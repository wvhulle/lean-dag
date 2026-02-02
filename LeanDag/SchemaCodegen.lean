import Lean
import Lean.Data.Json

open Lean Elab Command Meta

namespace LeanDag.SchemaCodegen

/-! # JSON Schema to Lean Type Code Generation

This module provides a custom command elaborator `gen_types_from_schema` that reads
a JSON schema file and generates Lean 4 types with ToJson/FromJson instances.
-/

/-! ## Schema Representation Types -/

/-- Represents a property within a JSON schema object definition. -/
structure SchemaProperty where
  name : String
  schemaType : Json  -- Full JSON schema for this property
  description : Option String
  isRequired : Bool
  hasDefault : Bool
  defaultValue : Option Json
  deriving Inhabited

/-- The kind of schema definition. -/
inductive SchemaKind where
  | object       -- Regular object with properties
  | stringEnum   -- String enum type
  | taggedUnion  -- oneOf with discriminator (like AnnotatedTextTree)
  deriving Inhabited, Repr, BEq

/-- Variant information for tagged unions. -/
structure TaggedVariant where
  discriminatorValue : String  -- e.g., "text", "append", "tag"
  properties : List SchemaProperty
  description : Option String
  deriving Inhabited

/-- Represents a complete type definition from the schema. -/
structure SchemaDefinition where
  name : String
  kind : SchemaKind
  description : Option String
  properties : List SchemaProperty  -- For object types
  enumValues : List String          -- For string enums
  variants : List TaggedVariant     -- For tagged unions
  discriminatorField : String       -- Field name for tagged union discriminator
  deriving Inhabited

/-! ## Schema Parsing -/

/-- Extract description from a JSON schema node. -/
def getDescription (j : Json) : Option String :=
  j.getObjValAs? String "description" |>.toOption

/-- Check if a field is required based on the "required" array. -/
def isFieldRequired (requiredFields : List String) (fieldName : String) : Bool :=
  requiredFields.contains fieldName

/-- Parse a single property from the schema. -/
def parseProperty (name : String) (propSchema : Json) (isRequired : Bool) : SchemaProperty :=
  let hasDefault := propSchema.getObjVal? "default" |>.isOk
  let defaultValue := propSchema.getObjVal? "default" |>.toOption
  {
    name
    schemaType := propSchema
    description := getDescription propSchema
    isRequired
    hasDefault
    defaultValue
  }

/-- Parse properties from an object schema. -/
def parseProperties (schema : Json) : List SchemaProperty := Id.run do
  let propsObj := schema.getObjVal? "properties" |>.toOption.getD (Json.mkObj [])
  let requiredArr := schema.getObjValAs? (Array String) "required" |>.toOption.getD #[]
  let requiredList := requiredArr.toList
  let mut result : List SchemaProperty := []
  match propsObj with
  | .obj kvs =>
    for ⟨name, propSchema⟩ in kvs.toList do
      let isReq := isFieldRequired requiredList name
      result := result ++ [parseProperty name propSchema isReq]
  | _ => pure ()
  result

/-- Parse enum values from a string enum schema. -/
def parseEnumValues (schema : Json) : List String :=
  match schema.getObjValAs? (Array String) "enum" with
  | .ok arr => arr.toList
  | .error _ => []

/-- Determine the discriminator field from a tagged union schema. -/
def findDiscriminatorField (variants : Array Json) : String := Id.run do
  -- Look for a field with "const" that's present in all variants
  for variant in variants do
    let propsObj := variant.getObjVal? "properties" |>.toOption.getD (Json.mkObj [])
    match propsObj with
    | .obj kvs =>
      for ⟨name, propSchema⟩ in kvs.toList do
        if propSchema.getObjVal? "const" |>.isOk then
          return name
    | _ => pure ()
  -- Default to "type" if nothing found
  "type"

/-- Parse a tagged union variant. -/
def parseVariant (variantSchema : Json) (discriminatorField : String) : Option TaggedVariant := do
  let propsObj ← variantSchema.getObjVal? "properties" |>.toOption
  let discriminatorProp ← match propsObj with
    | .obj kvs => kvs.toList.find? (·.1 == discriminatorField)
    | _ => none
  let constVal ← discriminatorProp.2.getObjVal? "const" |>.toOption
  let discriminatorValue ← constVal.getStr? |>.toOption
  let requiredArr := variantSchema.getObjValAs? (Array String) "required" |>.toOption.getD #[]
  let requiredList := requiredArr.toList
  let mut properties : List SchemaProperty := []
  match propsObj with
  | .obj kvs =>
    for ⟨name, propSchema⟩ in kvs.toList do
      if name != discriminatorField then
        let isReq := isFieldRequired requiredList name
        properties := properties ++ [parseProperty name propSchema isReq]
  | _ => pure ()
  some {
    discriminatorValue
    properties
    description := getDescription variantSchema
  }

/-- Determine the kind of a schema definition. -/
def determineSchemaKind (schema : Json) : SchemaKind :=
  if schema.getObjVal? "oneOf" |>.isOk then
    .taggedUnion
  else if schema.getObjVal? "enum" |>.isOk then
    .stringEnum
  else
    .object

/-- Parse a single definition from $defs. -/
def parseDefinition (name : String) (schema : Json) : SchemaDefinition := Id.run do
  let kind := determineSchemaKind schema
  let description := getDescription schema
  match kind with
  | .stringEnum =>
    pure {
      name
      kind
      description
      properties := []
      enumValues := parseEnumValues schema
      variants := []
      discriminatorField := ""
    }
  | .taggedUnion =>
    let oneOfArr := schema.getObjValAs? (Array Json) "oneOf" |>.toOption.getD #[]
    let discField := findDiscriminatorField oneOfArr
    let variants := oneOfArr.toList.filterMap (parseVariant · discField)
    pure {
      name
      kind
      description
      properties := []
      enumValues := []
      variants
      discriminatorField := discField
    }
  | .object =>
    pure {
      name
      kind
      description
      properties := parseProperties schema
      enumValues := []
      variants := []
      discriminatorField := ""
    }

/-- Parse all definitions from a JSON schema. -/
def parseSchema (json : Json) : Except String (List SchemaDefinition) := do
  let defs ← json.getObjVal? "$defs"
  match defs with
  | .obj kvs => return kvs.toList.map fun ⟨name, schema⟩ => parseDefinition name schema
  | _ => throw "Expected $defs to be an object"

/-! ## Type Mapping -/

/-- Convert snake_case to camelCase. -/
def snakeToCamel (s : String) : String := Id.run do
  let parts := s.splitOn "_"
  match parts with
  | [] => ""
  | [single] => single
  | first :: rest =>
    let capitalizedRest := rest.map fun part =>
      if part.isEmpty then ""
      else part.capitalize
    first ++ String.join capitalizedRest

/-- Resolve a $ref to a type name. -/
def resolveRef (ref : String) : String :=
  -- "#/$defs/LineCharacterPosition" -> "LineCharacterPosition"
  let parts := ref.splitOn "/"
  parts.getLast!

/-- Extract dependencies (referenced types) from a schema. -/
partial def extractDependencies (schema : Json) : List String := Id.run do
  let mut deps : List String := []
  -- Check for $ref
  if let some ref := schema.getObjValAs? String "$ref" |>.toOption then
    deps := deps ++ [resolveRef ref]
  -- Check properties
  if let .ok (.obj props) := schema.getObjVal? "properties" then
    for ⟨_, propSchema⟩ in props.toList do
      deps := deps ++ extractDependencies propSchema
  -- Check array items
  if let .ok items := schema.getObjVal? "items" then
    deps := deps ++ extractDependencies items
  -- Check oneOf variants
  if let .ok (.arr variants) := schema.getObjVal? "oneOf" then
    for v in variants do
      deps := deps ++ extractDependencies v
  deps

/-- Map a JSON schema type to a Lean type name. -/
partial def schemaTypeToLean (schema : Json) : String := Id.run do
  -- Check for $ref first
  if let some ref := schema.getObjValAs? String "$ref" |>.toOption then
    return resolveRef ref
  -- Check for const (used in discriminator fields)
  if schema.getObjVal? "const" |>.isOk then
    return "String"
  -- Check for type field
  let typeStr := schema.getObjValAs? String "type" |>.toOption.getD "any"
  match typeStr with
  | "string" =>
    if schema.getObjVal? "enum" |>.isOk then
      "String"  -- Inline enums become String for now
    else
      "String"
  | "integer" =>
    let min := schema.getObjValAs? Int "minimum" |>.toOption
    if min == some 0 then "Nat" else "Int"
  | "boolean" => "Bool"
  | "array" =>
    let items := schema.getObjVal? "items" |>.toOption.getD (Json.mkObj [])
    let itemType := schemaTypeToLean items
    s!"Array {itemType}"
  | "object" => "Json"  -- Fallback for inline objects
  | _ => "Json"

/-- Get the Lean type for a property, wrapping in Option if not required. -/
def propertyToLeanType (prop : SchemaProperty) : String :=
  let baseType := schemaTypeToLean prop.schemaType
  if prop.isRequired && !prop.hasDefault then
    baseType
  else
    -- Add parentheses around complex types (those with spaces like "List X")
    let parts := baseType.splitOn " "
    let needsParens := parts.length > 1
    if needsParens then
      s!"Option ({baseType})"
    else
      s!"Option {baseType}"

/-! ## Dependency Ordering -/

/-- Get all type names referenced by a definition. -/
def getDefinitionDependencies (def_ : SchemaDefinition) : List String := Id.run do
  let mut deps : List String := []
  let reservedWords := ["List", "Option", "Array", "String", "Int", "Nat", "Bool", "Json"]
  -- From properties
  for prop in def_.properties do
    let typeStr := schemaTypeToLean prop.schemaType
    -- Extract type name from "Array X" or "Option X" or just "X"
    let words := typeStr.splitOn " "
    for word in words do
      if !reservedWords.contains word then
        deps := deps ++ [word]
  -- From tagged union variants
  for variant in def_.variants do
    for prop in variant.properties do
      let typeStr := schemaTypeToLean prop.schemaType
      let words := typeStr.splitOn " "
      for word in words do
        if !reservedWords.contains word then
          deps := deps ++ [word]
  deps.eraseDups

/-- Simple topological sort for definitions. -/
def topologicalSort (defs : List SchemaDefinition) : List SchemaDefinition := Id.run do
  let names := defs.map (·.name)
  let mut sorted : List SchemaDefinition := []
  let mut remaining := defs
  let mut iterations := 0
  let maxIterations := defs.length * defs.length + 1
  while !remaining.isEmpty && iterations < maxIterations do
    iterations := iterations + 1
    let mut added := false
    for def_ in remaining do
      let deps := getDefinitionDependencies def_
      -- Filter to only deps that are in our schema (not external types)
      let schemaDeps := deps.filter (names.contains ·)
      -- Check if all schema deps are already sorted
      let sortedNames := sorted.map (·.name)
      let allDepsSorted := schemaDeps.all fun dep => sortedNames.contains dep || dep == def_.name
      if allDepsSorted then
        sorted := sorted ++ [def_]
        remaining := remaining.filter (·.name != def_.name)
        added := true
        break
    if !added then
      -- No progress, just add the first remaining (cycle or external dep)
      match remaining.head? with
      | some def_ =>
        sorted := sorted ++ [def_]
        remaining := remaining.drop 1
      | none => break
  sorted

/-! ## Code Generation -/

/-- Generate a structure field. -/
def genStructField (prop : SchemaProperty) : String := Id.run do
  let fieldName := prop.name  -- Keep snake_case to match JSON
  let fieldType := propertyToLeanType prop
  let isOptional := !prop.isRequired || prop.hasDefault
  let defaultPart :=
    if prop.hasDefault && prop.isRequired then
      -- Required field with default - use the default value directly
      match prop.defaultValue with
      | some (.bool b) => s!" := {if b then "true" else "false"}"
      | some (.num n) =>
        if n.mantissa < 0 then s!" := {n.mantissa}"
        else s!" := {n.mantissa}"
      | some (.str strVal) => s!" := \"{strVal}\""
      | some (.arr arr) => if arr.isEmpty then " := []" else ""
      | _ => ""
    else if isOptional then
      -- Optional field - default to none
      " := none"
    else
      ""
  s!"  {fieldName} : {fieldType}{defaultPart}"

/-- Generate a structure definition as a string. -/
def genStructureString (def_ : SchemaDefinition) : String := Id.run do
  let fields := def_.properties.map genStructField
  let fieldsStr := String.intercalate "\n" fields
  let docComment := match def_.description with
    | some desc => s!"/-- {desc} -/\n"
    | none => ""
  s!"{docComment}structure {def_.name} where\n{fieldsStr}\n  deriving Inhabited, ToJson, FromJson, BEq, Repr"

/-- Generate an enum definition as a string. -/
def genEnumString (def_ : SchemaDefinition) : String := Id.run do
  let typeName := def_.name
  let docComment := match def_.description with
    | some desc => s!"/-- {desc} -/\n"
    | none => ""
  let variants := def_.enumValues.map fun v =>
    let leanName := snakeToCamel v
    s!"  | {leanName}"
  let variantsStr := String.intercalate "\n" variants
  let toJsonCases := def_.enumValues.map fun v =>
    let leanName := snakeToCamel v
    s!"    | .{leanName} => \"{v}\""
  let toJsonStr := String.intercalate "\n" toJsonCases
  let fromJsonCases := def_.enumValues.map fun v =>
    let leanName := snakeToCamel v
    s!"    | \"{v}\" => .ok {typeName}.{leanName}"
  let fromJsonStr := String.intercalate "\n" fromJsonCases
  s!"{docComment}inductive {typeName} where
{variantsStr}
  deriving Inhabited, BEq, Repr

instance : ToJson {typeName} where
  toJson
{toJsonStr}

instance : FromJson {typeName} where
  fromJson? j := do
    let str ← j.getStr?
    match str with
{fromJsonStr}
    | x => .error (\"invalid {typeName}: \" ++ x)"

/-- Check if a type references the given type name (for detecting self-recursion). -/
def typeReferencesName (typeStr : String) (name : String) : Bool :=
  typeStr.splitOn " " |>.any (· == name)

/-- Generate a tagged union inductive as a string. -/
def genTaggedUnionString (def_ : SchemaDefinition) : String := Id.run do
  let docComment := match def_.description with
    | some desc => s!"/-- {desc} -/\n"
    | none => ""
  let typeName := def_.name
  let discField := def_.discriminatorField
  -- Check if this type is self-recursive
  let isSelfRecursive := def_.variants.any fun v =>
    v.properties.any fun p =>
      typeReferencesName (propertyToLeanType p) typeName
  -- Generate inductive variants
  let variants := def_.variants.map fun v =>
    let variantName := snakeToCamel v.discriminatorValue
    let params := v.properties.map fun p =>
      let pType := propertyToLeanType p
      s!"({p.name} : {pType})"
    let paramsStr := String.intercalate " " params
    if paramsStr.isEmpty then
      s!"  | {variantName}"
    else
      s!"  | {variantName} {paramsStr}"
  let variantsStr := String.intercalate "\n" variants
  -- Generate toJson implementation
  -- Use prefixed parameter names to avoid conflicts with constructor names
  let toJsonCases := def_.variants.map fun v =>
    let variantName := snakeToCamel v.discriminatorValue
    let paramNames := v.properties.map fun p => s!"p_{p.name}"
    let paramsPattern := String.intercalate " " paramNames
    let fieldsList := v.properties.map fun p =>
      let paramVar := s!"p_{p.name}"
      -- For self-recursive types, use explicit toJson call
      if isSelfRecursive && typeReferencesName (propertyToLeanType p) typeName then
        let baseType := schemaTypeToLean p.schemaType
        if baseType.startsWith "Array " then
          s!"(\"{p.name}\", Json.arr ({paramVar}.map {typeName}.toJson))"
        else
          s!"(\"{p.name}\", {typeName}.toJson {paramVar})"
      else
        s!"(\"{p.name}\", Lean.toJson {paramVar})"
    let fieldsStr := String.intercalate ", " fieldsList
    let discriminatorPair := s!"(\"{discField}\", \"{v.discriminatorValue}\")"
    if paramsPattern.isEmpty then
      s!"  | {typeName}.{variantName} => Json.mkObj [{discriminatorPair}]"
    else
      s!"  | {typeName}.{variantName} {paramsPattern} => Json.mkObj [{discriminatorPair}, {fieldsStr}]"
  let toJsonStr := String.intercalate "\n" toJsonCases
  -- Generate fromJson implementation with explicit type annotation
  let fromJsonCases := def_.variants.map fun v =>
    let variantName := snakeToCamel v.discriminatorValue
    let bindings := v.properties.map fun p =>
      let pType := propertyToLeanType p
      let baseType := schemaTypeToLean p.schemaType
      -- For self-recursive types, use explicit fromJson? call
      if isSelfRecursive && typeReferencesName pType typeName then
        if baseType.startsWith "Array " then
          s!"    let {p.name}Json ← j.getObjValAs? (Array Json) \"{p.name}\"\n    let {p.name}List ← {p.name}Json.toList.mapM {typeName}.fromJson?\n    let {p.name} : {pType} := {p.name}List.toArray"
        else if pType.startsWith "Option " then
          s!"    let {p.name}Json := j.getObjVal? \"{p.name}\" |>.toOption\n    let {p.name} : {pType} ← match {p.name}Json with | some jv => {typeName}.fromJson? jv |>.map some | none => .ok none"
        else
          s!"    let {p.name}Json ← j.getObjVal? \"{p.name}\"\n    let {p.name} : {pType} ← {typeName}.fromJson? {p.name}Json"
      else
        s!"    let {p.name} : {pType} ← j.getObjValAs? _ \"{p.name}\""
    let bindingsStr := String.intercalate "\n" bindings
    let paramNames := v.properties.map (·.name)
    let paramsCall := String.intercalate " " paramNames
    let returnExpr := if paramsCall.isEmpty
      then s!"{typeName}.{variantName}"
      else s!"{typeName}.{variantName} {paramsCall}"
    if bindingsStr.isEmpty then
      s!"  | \"{v.discriminatorValue}\" => .ok ({returnExpr})"
    else
      s!"  | \"{v.discriminatorValue}\" => do\n{bindingsStr}\n    .ok ({returnExpr})"
  let fromJsonStr := String.intercalate "\n" fromJsonCases
  s!"{docComment}inductive {typeName} where
{variantsStr}
  deriving Inhabited, BEq, Repr

partial def {typeName}.toJson : {typeName} → Json
{toJsonStr}

instance : ToJson {typeName} := ⟨{typeName}.toJson⟩

partial def {typeName}.fromJson? (j : Json) : Except String {typeName} := do
  let discVal ← j.getObjValAs? String \"{discField}\"
  match discVal with
{fromJsonStr}
  | x => .error (\"invalid {typeName} {discField}: \" ++ x)

instance : FromJson {typeName} := ⟨{typeName}.fromJson?⟩"

/-! ## Command Elaborator -/

/-- Generate Lean code for a single schema definition. -/
def genDefinitionCode (def_ : SchemaDefinition) : String :=
  match def_.kind with
  | .object => genStructureString def_
  | .stringEnum => genEnumString def_
  | .taggedUnion => genTaggedUnionString def_

/-- The main code generation function. Returns list of code blocks, one per type definition. -/
def generateLeanCode (defs : List SchemaDefinition) : List String := Id.run do
  -- Sort definitions by dependencies
  let sortedDefs := topologicalSort defs
  sortedDefs.map genDefinitionCode

/-- Parse and elaborate a single command string. -/
def parseAndElabCommand (code : String) : CommandElabM Unit := do
  let env ← getEnv
  -- Parse the code as a command
  match Parser.runParserCategory env `command code with
  | .error e => throwError "Failed to parse generated code: {e}\n\nCode:\n{code}"
  | .ok stx => elabCommand stx

/-- Parse and elaborate multiple commands from a list of code strings.
    Each string in the list is elaborated together as a unit. -/
def parseAndElabMultipleCommands (codes : List String) : CommandElabM Unit := do
  for code in codes do
    if !code.trimAsciiStart.toString.isEmpty then
      -- Split the code into individual commands (separated by double newlines within)
      let parts := code.splitOn "\n\n"
      for part in parts do
        if !part.trimAsciiStart.toString.isEmpty then
          parseAndElabCommand part

/-- Syntax for the gen_types_from_schema command. -/
syntax (name := genTypesFromSchema) "gen_types_from_schema" str : command

/-- Elaborate the gen_types_from_schema command. -/
@[command_elab genTypesFromSchema]
def elabGenTypesFromSchema : CommandElab := fun stx => do
  match stx with
  | `(command| gen_types_from_schema $path:str) =>
    let schemaPath := path.getString
    -- Resolve relative path from the file containing this command
    let srcDir := (← IO.currentDir)
    let fullPath := if schemaPath.startsWith "/" then
      System.FilePath.mk schemaPath
    else
      srcDir / schemaPath
    let jsonStr ← IO.FS.readFile fullPath
    let json ← match Json.parse jsonStr with
      | .ok j => pure j
      | .error e => throwError "JSON parse error: {e}"
    let defs ← match parseSchema json with
      | .ok d => pure d
      | .error e => throwError "Schema parse error: {e}"
    -- Generate the code as a list of definition blocks
    let codes := generateLeanCode defs
    -- Log the generated code for debugging
    logInfo m!"Generated {defs.length} type definitions from schema"
    -- Parse and elaborate each definition
    parseAndElabMultipleCommands codes
  | _ => throwUnsupportedSyntax

end LeanDag.SchemaCodegen
