import Lean
import Lean.Data.Json

open Lean Elab Command Meta

namespace LeanDag.SchemaCodegen

/-! # JSON Schema to Lean Type Code Generation

This module provides a custom command elaborator `gen_types_from_schema` that reads
a JSON schema file and generates Lean 4 types with ToJson/FromJson instances.

## Property Order

JSON objects in Lean.Json are stored as sorted RBNodes, losing insertion order.
To preserve property order for constructor parameters, we use the `"x-property-order"`
extension field in the schema. If not present, properties are sorted alphabetically.
-/

/-! ## Schema Representation -/

structure SchemaProperty where
  name : String
  schemaType : Json
  description : Option String
  isRequired : Bool
  hasDefault : Bool
  defaultValue : Option Json
  deriving Inhabited

inductive SchemaKind where
  | object | stringEnum | taggedUnion
  deriving Inhabited, BEq

structure TaggedVariant where
  discriminatorValue : String
  properties : List SchemaProperty
  description : Option String
  deriving Inhabited

structure SchemaDefinition where
  name : String
  kind : SchemaKind
  description : Option String
  properties : List SchemaProperty
  enumValues : List String
  variants : List TaggedVariant
  discriminatorField : String
  deriving Inhabited

/-! ## Utilities -/

def getDescription (j : Json) : Option String :=
  j.getObjValAs? String "description" |>.toOption

def snakeToCamel (s : String) : String :=
  match s.splitOn "_" with
  | [] => ""
  | [x] => x
  | first :: rest => first ++ String.join (rest.map String.capitalize)

def lowercaseFirst (s : String) : String :=
  if s.isEmpty then s else s.take 1 |>.toString |>.toLower ++ (s.drop 1).toString

def toCamelCase (s : String) : String :=
  if s.contains '_' then snakeToCamel s else lowercaseFirst s

def resolveRef (ref : String) : String :=
  ref.splitOn "/" |>.getLast!

/-! ## Type Mapping -/

partial def schemaTypeToLean (schema : Json) : String :=
  if let some ref := schema.getObjValAs? String "$ref" |>.toOption then
    resolveRef ref
  else if schema.getObjVal? "const" |>.isOk then
    "String"
  else
    match schema.getObjValAs? String "type" |>.toOption.getD "any" with
    | "string" => "String"
    | "integer" =>
      let min := schema.getObjValAs? Int "minimum" |>.toOption
      if min == some 0 then "Nat" else "Int"
    | "boolean" => "Bool"
    | "array" =>
      let items := schema.getObjVal? "items" |>.toOption.getD (Json.mkObj [])
      s!"Array {schemaTypeToLean items}"
    | "object" => "Json"
    | _ => "Json"

def propertyToLeanType (prop : SchemaProperty) : String :=
  let baseType := schemaTypeToLean prop.schemaType
  if prop.isRequired || prop.hasDefault then baseType
  else if baseType.contains ' ' then s!"Option ({baseType})" else s!"Option {baseType}"

/-! ## Schema Parsing -/

def parseProperty (name : String) (propSchema : Json) (isRequired : Bool) : SchemaProperty :=
  { name
    schemaType := propSchema
    description := getDescription propSchema
    isRequired
    hasDefault := propSchema.getObjVal? "default" |>.isOk
    defaultValue := propSchema.getObjVal? "default" |>.toOption }

/-- Get property order as sorted keys. -/
def getPropertyOrder (schema : Json) : List String :=
  match schema.getObjVal? "properties" with
  | .ok (.obj kvs) => kvs.toList.map (·.1) |>.mergeSort (· < ·)
  | _ => []

def parseProperties (schema : Json) : List SchemaProperty :=
  let propsObj := schema.getObjVal? "properties" |>.toOption.getD (Json.mkObj [])
  let required := schema.getObjValAs? (Array String) "required" |>.toOption.getD #[] |>.toList
  let order := getPropertyOrder schema
  match propsObj with
  | .obj kvs =>
    let kvsList := kvs.toList
    order.filterMap fun name =>
      kvsList.find? (·.1 == name) |>.map fun (_, propSchema) =>
        parseProperty name propSchema (required.contains name)
  | _ => []

def findDiscriminatorField (variants : Array Json) : String := Id.run do
  for variant in variants do
    if let .ok (.obj kvs) := variant.getObjVal? "properties" then
      for ⟨name, propSchema⟩ in kvs.toList do
        if propSchema.getObjVal? "const" |>.isOk then
          return name
  return "type"

def parseVariant (variantSchema : Json) (discriminatorField : String) : Option TaggedVariant := do
  let propsObj ← variantSchema.getObjVal? "properties" |>.toOption
  let kvs ← match propsObj with | .obj kvs => some kvs.toList | _ => none
  let (_, discProp) ← kvs.find? (·.1 == discriminatorField)
  let constVal ← discProp.getObjVal? "const" |>.toOption
  let discriminatorValue ← constVal.getStr? |>.toOption
  let required := variantSchema.getObjValAs? (Array String) "required" |>.toOption.getD #[] |>.toList
  let order := getPropertyOrder variantSchema
  let properties := order.filterMap fun name =>
    if name == discriminatorField then none
    else kvs.find? (·.1 == name) |>.map fun (_, propSchema) =>
      parseProperty name propSchema (required.contains name)
  some { discriminatorValue, properties, description := getDescription variantSchema }

def determineSchemaKind (schema : Json) : SchemaKind :=
  if schema.getObjVal? "oneOf" |>.isOk then .taggedUnion
  else if schema.getObjVal? "enum" |>.isOk then .stringEnum
  else .object

def parseDefinition (name : String) (schema : Json) : SchemaDefinition :=
  let kind := determineSchemaKind schema
  let description := getDescription schema
  match kind with
  | .stringEnum =>
    let enumValues := schema.getObjValAs? (Array String) "enum" |>.toOption.getD #[] |>.toList
    { name, kind, description, properties := [], enumValues, variants := [], discriminatorField := "" }
  | .taggedUnion =>
    let oneOfArr := schema.getObjValAs? (Array Json) "oneOf" |>.toOption.getD #[]
    let discField := findDiscriminatorField oneOfArr
    let variants := oneOfArr.toList.filterMap (parseVariant · discField)
    { name, kind, description, properties := [], enumValues := [], variants, discriminatorField := discField }
  | .object =>
    { name, kind, description, properties := parseProperties schema, enumValues := [], variants := [], discriminatorField := "" }

def parseSchema (json : Json) : Except String (List SchemaDefinition) := do
  let defs ← json.getObjVal? "$defs"
  match defs with
  | .obj kvs => return kvs.toList.map fun (name, schema) => parseDefinition name schema
  | _ => throw "Expected $defs to be an object"

/-! ## Dependency Ordering -/

def getDefinitionDependencies (def_ : SchemaDefinition) : List String :=
  let reserved := ["List", "Option", "Array", "String", "Int", "Nat", "Bool", "Json"]
  let fromProps := def_.properties.map (schemaTypeToLean ·.schemaType)
  let fromVariants := def_.variants.flatMap (·.properties.map (schemaTypeToLean ·.schemaType))
  (fromProps ++ fromVariants).flatMap (·.splitOn " ") |>.filter (!reserved.contains ·) |>.eraseDups

partial def topologicalSort (defs : List SchemaDefinition) : List SchemaDefinition := Id.run do
  let names := defs.map (·.name)
  let mut sorted : List SchemaDefinition := []
  let mut remaining := defs
  let mut fuel := defs.length * defs.length + 1
  while fuel > 0 && !remaining.isEmpty do
    fuel := fuel - 1
    let sortedNames := sorted.map (·.name)
    match remaining.find? fun d =>
      let deps := getDefinitionDependencies d |>.filter names.contains
      deps.all fun dep => sortedNames.contains dep || dep == d.name
    with
    | some d =>
      sorted := sorted ++ [d]
      remaining := remaining.filter (·.name != d.name)
    | none =>
      sorted := sorted ++ remaining.take 1
      remaining := remaining.drop 1
  return sorted ++ remaining

/-! ## Code Generation -/

def genStructField (prop : SchemaProperty) : String :=
  let fieldName := toCamelCase prop.name
  let fieldType := propertyToLeanType prop
  let defaultPart :=
    if prop.hasDefault then
      match prop.defaultValue with
      | some (.bool b) => s!" := {b}"
      | some (.num n) => s!" := {n.mantissa}"
      | some (.str s) => s!" := \"{s}\""
      | some (.arr a) => if a.isEmpty then " := #[]" else ""
      | _ => ""
    else if !prop.isRequired then " := none"
    else ""
  s!"  {fieldName} : {fieldType}{defaultPart}"

def genStructureString (def_ : SchemaDefinition) : String :=
  let docComment := def_.description.map (s!"/-- {·} -/\n") |>.getD ""
  let fields := def_.properties.map genStructField |> String.intercalate "\n"
  -- Generate custom ToJson that maps camelCase fields to snake_case JSON keys
  let toJsonFields := def_.properties.map fun p =>
    let fieldName := toCamelCase p.name
    s!"(\"{p.name}\", Lean.toJson s.{fieldName})"
  let toJsonBody := s!"Json.mkObj [{String.intercalate ", " toJsonFields}]"
  -- Generate custom FromJson that maps snake_case JSON keys to camelCase fields
  let fromJsonBindings := def_.properties.map fun p =>
    let fieldName := toCamelCase p.name
    let fieldType := propertyToLeanType p
    s!"    let {fieldName} : {fieldType} ← j.getObjValAs? _ \"{p.name}\""
  let fieldNames := def_.properties.map (toCamelCase ·.name)
  let fromJsonReturn := ".ok { " ++ String.intercalate ", " fieldNames ++ " }"
  s!"{docComment}structure {def_.name} where
{fields}
  deriving Inhabited, BEq, Repr

instance : ToJson {def_.name} where
  toJson s := {toJsonBody}

instance : FromJson {def_.name} where
  fromJson? j := do
{String.intercalate "\n" fromJsonBindings}
    {fromJsonReturn}"

def genEnumString (def_ : SchemaDefinition) : String :=
  let typeName := def_.name
  let docComment := def_.description.map (s!"/-- {·} -/\n") |>.getD ""
  let variants := def_.enumValues.map (s!"  | {toCamelCase ·}") |> String.intercalate "\n"
  let toJsonCases := def_.enumValues.map fun v => s!"    | .{toCamelCase v} => \"{v}\""
  let fromJsonCases := def_.enumValues.map fun v => s!"    | \"{v}\" => .ok {typeName}.{toCamelCase v}"
  s!"{docComment}inductive {typeName} where
{variants}
  deriving Inhabited, BEq, Repr

instance : ToJson {typeName} where
  toJson
{String.intercalate "\n" toJsonCases}

instance : FromJson {typeName} where
  fromJson? j := do
    let str ← j.getStr?
    match str with
{String.intercalate "\n" fromJsonCases}
    | x => .error (\"invalid {typeName}: \" ++ x)"

def typeReferencesName (typeStr name : String) : Bool :=
  typeStr.splitOn " " |>.any (· == name)

def genTaggedUnionString (def_ : SchemaDefinition) : String :=
  let typeName := def_.name
  let discField := def_.discriminatorField
  let docComment := def_.description.map (s!"/-- {·} -/\n") |>.getD ""
  let isSelfRecursive := def_.variants.any fun v =>
    v.properties.any fun p => typeReferencesName (propertyToLeanType p) typeName

  -- Generate inductive variants (use camelCase for Lean field names)
  let variants := def_.variants.map fun v =>
    let variantName := toCamelCase v.discriminatorValue
    let params := v.properties.map fun p =>
      let fieldName := toCamelCase p.name
      s!"({fieldName} : {propertyToLeanType p})"
    if params.isEmpty then s!"  | {variantName}" else s!"  | {variantName} {String.intercalate " " params}"

  -- Generate toJson (map camelCase params to snake_case JSON keys)
  let toJsonCases := def_.variants.map fun v =>
    let variantName := toCamelCase v.discriminatorValue
    let paramNames := v.properties.map fun p => s!"p_{toCamelCase p.name}"
    let fieldsList := v.properties.map fun p =>
      let paramVar := s!"p_{toCamelCase p.name}"
      if isSelfRecursive && typeReferencesName (propertyToLeanType p) typeName then
        let baseType := schemaTypeToLean p.schemaType
        if baseType.startsWith "Array " then s!"(\"{p.name}\", Json.arr ({paramVar}.map {typeName}.toJson))"
        else s!"(\"{p.name}\", {typeName}.toJson {paramVar})"
      else s!"(\"{p.name}\", Lean.toJson {paramVar})"
    let discPair := s!"(\"{discField}\", \"{v.discriminatorValue}\")"
    if paramNames.isEmpty then s!"  | {typeName}.{variantName} => Json.mkObj [{discPair}]"
    else s!"  | {typeName}.{variantName} {String.intercalate " " paramNames} => Json.mkObj [{discPair}, {String.intercalate ", " fieldsList}]"

  -- Generate fromJson (map snake_case JSON keys to camelCase params)
  let fromJsonCases := def_.variants.map fun v =>
    let variantName := toCamelCase v.discriminatorValue
    let bindings := v.properties.map fun p =>
      let fieldName := toCamelCase p.name
      let pType := propertyToLeanType p
      let baseType := schemaTypeToLean p.schemaType
      if isSelfRecursive && typeReferencesName pType typeName then
        if baseType.startsWith "Array " then
          s!"    let {fieldName}Json ← j.getObjValAs? (Array Json) \"{p.name}\"\n    let {fieldName}List ← {fieldName}Json.toList.mapM {typeName}.fromJson?\n    let {fieldName} : {pType} := {fieldName}List.toArray"
        else if pType.startsWith "Option " then
          s!"    let {fieldName}Json := j.getObjVal? \"{p.name}\" |>.toOption\n    let {fieldName} : {pType} ← match {fieldName}Json with | some jv => {typeName}.fromJson? jv |>.map some | none => .ok none"
        else s!"    let {fieldName}Json ← j.getObjVal? \"{p.name}\"\n    let {fieldName} : {pType} ← {typeName}.fromJson? {fieldName}Json"
      else s!"    let {fieldName} : {pType} ← j.getObjValAs? _ \"{p.name}\""
    let paramNames := v.properties.map fun p => toCamelCase p.name
    let returnExpr := if paramNames.isEmpty then s!"{typeName}.{variantName}"
      else s!"{typeName}.{variantName} {String.intercalate " " paramNames}"
    if bindings.isEmpty then s!"  | \"{v.discriminatorValue}\" => .ok ({returnExpr})"
    else s!"  | \"{v.discriminatorValue}\" => do\n{String.intercalate "\n" bindings}\n    .ok ({returnExpr})"

  s!"{docComment}inductive {typeName} where
{String.intercalate "\n" variants}
  deriving Inhabited, BEq, Repr

partial def {typeName}.toJson : {typeName} → Json
{String.intercalate "\n" toJsonCases}

instance : ToJson {typeName} := ⟨{typeName}.toJson⟩

partial def {typeName}.fromJson? (j : Json) : Except String {typeName} := do
  let discVal ← j.getObjValAs? String \"{discField}\"
  match discVal with
{String.intercalate "\n" fromJsonCases}
  | x => .error (\"invalid {typeName} {discField}: \" ++ x)

instance : FromJson {typeName} := ⟨{typeName}.fromJson?⟩"

def genDefinitionCode (def_ : SchemaDefinition) : String :=
  match def_.kind with
  | .object => genStructureString def_
  | .stringEnum => genEnumString def_
  | .taggedUnion => genTaggedUnionString def_

def generateLeanCode (defs : List SchemaDefinition) : List String :=
  (topologicalSort defs).map genDefinitionCode

/-! ## Command Elaborator -/

def parseAndElabCommand (code : String) : CommandElabM Unit := do
  let env ← getEnv
  match Parser.runParserCategory env `command code with
  | .error e => throwError "Failed to parse generated code: {e}\n\nCode:\n{code}"
  | .ok stx => elabCommand stx

def parseAndElabMultipleCommands (codes : List String) : CommandElabM Unit := do
  for code in codes do
    for part in code.splitOn "\n\n" do
      if !part.trimAsciiStart.toString.isEmpty then
        parseAndElabCommand part

syntax (name := genTypesFromSchema) "gen_types_from_schema" str : command

@[command_elab genTypesFromSchema]
def elabGenTypesFromSchema : CommandElab := fun stx => do
  match stx with
  | `(command| gen_types_from_schema $path:str) =>
    let schemaPath := path.getString
    let srcFile := (← getFileName)
    let srcDir := System.FilePath.mk srcFile |>.parent.getD "."
    let fullPath := if schemaPath.startsWith "/" then System.FilePath.mk schemaPath else srcDir / schemaPath
    let jsonStr ← IO.FS.readFile fullPath
    let json ← match Json.parse jsonStr with
      | .ok j => pure j
      | .error e => throwError "JSON parse error: {e}"
    let defs ← match parseSchema json with
      | .ok d => pure d
      | .error e => throwError "Schema parse error: {e}"
    let codes := generateLeanCode defs
    logInfo m!"Generated {defs.length} type definitions from schema"
    parseAndElabMultipleCommands codes
  | _ => throwUnsupportedSyntax

end LeanDag.SchemaCodegen
