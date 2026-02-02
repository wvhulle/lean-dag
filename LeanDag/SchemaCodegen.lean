import Lean
import Lean.Data.Json

open Lean Elab Command Meta Parser Term

namespace LeanDag.SchemaCodegen

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

def toCamelCase (s : String) : String :=
  match s.splitOn "_" with
  | [] => ""
  | first :: rest => first.decapitalize ++ String.join (rest.map String.capitalize)

def resolveRef (ref : String) : String :=
  ref.splitOn "/" |>.getLast!

/-! ## Type Shape ADT -/

/-- Captures the structure of a type from JSON Schema, eliminating dual string/syntax mapping. -/
inductive TypeShape where
  | primitive : String → TypeShape  -- "String", "Nat", "Int", "Bool", "Json"
  | array : TypeShape → TypeShape
  | option : TypeShape → TypeShape
  | ref : String → TypeShape        -- Reference to another type
  deriving Inhabited, BEq, Repr

/-- Parse a JSON schema into a TypeShape. -/
partial def parseTypeShape (schema : Json) : TypeShape :=
  if let some r := schema.getObjValAs? String "$ref" |>.toOption then
    .ref (resolveRef r)
  else if schema.getObjVal? "const" |>.isOk then
    .primitive "String"
  else
    match schema.getObjValAs? String "type" |>.toOption.getD "any" with
    | "string" => .primitive "String"
    | "integer" =>
      let min := schema.getObjValAs? Int "minimum" |>.toOption
      if min == some 0 then .primitive "Nat" else .primitive "Int"
    | "boolean" => .primitive "Bool"
    | "array" =>
      let items := schema.getObjVal? "items" |>.toOption.getD (Json.mkObj [])
      .array (parseTypeShape items)
    | "object" => .primitive "Json"
    | _ => .primitive "Json"

/-- Convert TypeShape to a string representation (for dependency analysis). -/
def TypeShape.toString : TypeShape → String
  | .primitive s => s
  | .array inner => s!"Array {inner.toString}"
  | .option inner => s!"Option {inner.toString}"
  | .ref name => name

/-- Get the referenced type names from a TypeShape (for dependency analysis). -/
def TypeShape.getRefs : TypeShape → List String
  | .primitive _ => []
  | .array inner => inner.getRefs
  | .option inner => inner.getRefs
  | .ref name => [name]

/-- Check if a TypeShape contains a reference to the given type name. -/
def TypeShape.containsRef (shape : TypeShape) (typeName : String) : Bool :=
  shape.getRefs.contains typeName

/-- Convert TypeShape to syntax (TSyntax `term). -/
partial def TypeShape.toTermStx : TypeShape → CommandElabM (TSyntax `term)
  | .primitive "String" => `(String)
  | .primitive "Nat" => `(Nat)
  | .primitive "Int" => `(Int)
  | .primitive "Bool" => `(Bool)
  | .primitive "Json" => `(Json)
  | .primitive s => `($(mkIdent (Name.mkSimple s)))
  | .array inner => do let innerStx ← inner.toTermStx; `(Array $innerStx)
  | .option inner => do let innerStx ← inner.toTermStx; `(Option $innerStx)
  | .ref name => `($(mkIdent (Name.mkSimple name)))

/-- Get the TypeShape for a property, wrapping in Option if not required. -/
def propertyTypeShape (prop : SchemaProperty) : TypeShape :=
  let baseShape := parseTypeShape prop.schemaType
  if prop.isRequired || prop.hasDefault then baseShape
  else .option baseShape

/-! ## Schema Parsing -/

def parseProperty (name : String) (propSchema : Json) (isRequired : Bool) : SchemaProperty :=
  { name
    schemaType := propSchema
    description := getDescription propSchema
    isRequired
    hasDefault := propSchema.getObjVal? "default" |>.isOk
    defaultValue := propSchema.getObjVal? "default" |>.toOption }

/-- Parse properties from a JSON schema, optionally excluding certain fields. -/
def parsePropertiesFrom (schema : Json) (exclude : List String := []) : List SchemaProperty :=
  match schema.getObjVal? "properties" with
  | .ok (.obj kvs) =>
    let kvsList := kvs.toList
    let order := kvsList.map (·.1) |>.mergeSort (· < ·)
    let required := schema.getObjValAs? (Array String) "required" |>.toOption.getD #[] |>.toList
    order.filterMap fun name =>
      if exclude.contains name then none
      else kvsList.find? (·.1 == name) |>.map fun (_, propSchema) =>
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
  let properties := parsePropertiesFrom variantSchema [discriminatorField]
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
    { name, kind, description, properties := parsePropertiesFrom schema, enumValues := [], variants := [], discriminatorField := "" }

def parseSchema (json : Json) : Except String (List SchemaDefinition) := do
  let defs ← json.getObjVal? "$defs"
  match defs with
  | .obj kvs => return kvs.toList.map fun (name, schema) => parseDefinition name schema
  | _ => throw "Expected $defs to be an object"

/-! ## Dependency Ordering -/

def getDefinitionDependencies (def_ : SchemaDefinition) : List String :=
  let fromProps := def_.properties.flatMap fun p => (parseTypeShape p.schemaType).getRefs
  let fromVariants := def_.variants.flatMap fun v =>
    v.properties.flatMap fun p => (parseTypeShape p.schemaType).getRefs
  (fromProps ++ fromVariants).eraseDups

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

/-! ## Syntax Construction Helpers -/

/-- Convert JSON property name to Lean field identifier -/
def mkFieldIdent (jsonName : String) : Ident :=
  mkIdent (Name.mkSimple (toCamelCase jsonName))

/-- Create a type identifier from a type name -/
def mkTypeIdent (typeName : String) : Ident :=
  mkIdent (Name.mkSimple typeName)

/-- Create a qualified identifier (e.g., TypeName.ctorName or TypeName.toJson) -/
def mkQualIdent (typeName memberName : String) : Ident :=
  mkIdent (Name.mkStr (Name.mkSimple typeName) memberName)

/-- Build full property type with Option wrapper if needed -/
def propertyToTypeStx (prop : SchemaProperty) : CommandElabM (TSyntax `term) :=
  (propertyTypeShape prop).toTermStx

/-- Build default value syntax for a property -/
def mkDefaultValueStx (prop : SchemaProperty) : CommandElabM (Option (TSyntax `term)) := do
  if prop.hasDefault then
    match prop.defaultValue with
    | some (.bool b) => return some (← `($(quote b)))
    | some (.num n) =>
      let intVal := n.mantissa
      if intVal ≥ 0 then
        return some (← `($(quote intVal.toNat)))
      else
        -- For negative integers, construct the literal directly
        let lit := Syntax.mkNumLit (toString intVal)
        return some (← `(($lit : Int)))
    | some (.str s) => return some (← `($(quote s)))
    | some (.arr a) =>
      if a.isEmpty then return some (← `(#[]))
      else return none
    | _ => return none
  else if !prop.isRequired then
    return some (← `(none))
  else
    return none

/-- Build structure field declaration -/
def mkStructFieldStx (prop : SchemaProperty) : CommandElabM (TSyntax `Lean.Parser.Command.structExplicitBinder) := do
  let fieldName := mkFieldIdent prop.name
  let fieldType ← propertyToTypeStx prop
  match ← mkDefaultValueStx prop with
  | some defaultVal =>
    `(Lean.Parser.Command.structExplicitBinder| ($fieldName : $fieldType := $defaultVal))
  | none =>
    `(Lean.Parser.Command.structExplicitBinder| ($fieldName : $fieldType))

/-- Build a ToJson pair for a field -/
def mkToJsonFieldPair (prop : SchemaProperty) : CommandElabM (TSyntax `term) := do
  let jsonKey := prop.name
  let fieldName := mkFieldIdent prop.name
  `(($(quote jsonKey), Lean.toJson s.$fieldName))

/-- Build FromJson field extraction as a do-sequence item -/
def mkFromJsonFieldBinding (prop : SchemaProperty) : CommandElabM (TSyntax ``Parser.Term.doSeqItem) := do
  let fieldName := mkFieldIdent prop.name
  let jsonKey := prop.name
  let fieldType ← propertyToTypeStx prop
  `(Parser.Term.doSeqItem| let $fieldName : $fieldType ← j.getObjValAs? _ $(quote jsonKey))

/-! ## Structure Generation -/

def genStructure (def_ : SchemaDefinition) : CommandElabM Unit := do
  let typeName := mkTypeIdent def_.name

  -- Build structure fields
  let fields ← def_.properties.toArray.mapM mkStructFieldStx

  -- Generate the structure definition
  let structCmd ← `(command|
    structure $typeName where
      $[$fields]*
      deriving Inhabited, BEq, Repr
  )
  elabCommand structCmd

  -- Generate ToJson instance
  let toJsonPairs ← def_.properties.toArray.mapM mkToJsonFieldPair
  let toJsonInst ← `(command|
    instance : ToJson $typeName where
      toJson s := Json.mkObj [$[$toJsonPairs],*]
  )
  elabCommand toJsonInst

  -- Generate FromJson instance
  let fromJsonBindings ← def_.properties.toArray.mapM mkFromJsonFieldBinding
  let fieldNames := def_.properties.toArray.map (mkFieldIdent ·.name)
  let fieldAssignments ← fieldNames.mapM fun fn => `(Parser.Term.structInstLVal| $fn:ident)
  let fromJsonInst ← `(command|
    instance : FromJson $typeName where
      fromJson? j := do
        $[$fromJsonBindings]*
        .ok { $[$fieldAssignments := $fieldNames],* }
  )
  elabCommand fromJsonInst

/-! ## Enum Generation -/

def genEnum (def_ : SchemaDefinition) : CommandElabM Unit := do
  let typeName := mkTypeIdent def_.name

  -- Build constructors
  let ctorStxs ← def_.enumValues.toArray.mapM fun v => do
    let ctorName := mkIdent (Name.mkSimple (toCamelCase v))
    `(Lean.Parser.Command.ctor| | $ctorName:ident)

  -- Generate the inductive definition
  let inductiveCmd ← `(command|
    inductive $typeName:ident where
      $[$ctorStxs]*
      deriving Inhabited, BEq, Repr
  )
  elabCommand inductiveCmd

  -- Generate ToJson match arms
  let toJsonMatchArms ← def_.enumValues.toArray.mapM fun v => do
    let ctorIdent := mkIdent (Name.mkSimple (toCamelCase v))
    `(Term.matchAltExpr| | .$ctorIdent:ident => $(quote v))

  -- Build the match expression as a term
  let toJsonMatch ← `(match x with $toJsonMatchArms:matchAlt*)
  let toJsonInst ← `(command|
    instance : ToJson $typeName where
      toJson x := $toJsonMatch
  )
  elabCommand toJsonInst

  -- Generate FromJson instance
  let fromJsonMatchArms ← def_.enumValues.toArray.mapM fun v => do
    -- Build qualified constructor name as TypeName.CtorName
    let qualCtorName := mkQualIdent def_.name (toCamelCase v)
    let result ← `(.ok $qualCtorName)
    `(Term.matchAltExpr| | $(quote v) => $result)

  let typeNameStr := def_.name
  let errorArm ← `(Term.matchAltExpr| | x => .error (s!"invalid {$(quote typeNameStr)}: " ++ x))
  let allFromJsonArms := fromJsonMatchArms.push errorArm

  -- Build the complete body with bind for string extraction
  let fromJsonBody ← `(j.getStr? >>= fun str => match str with $allFromJsonArms:matchAlt*)
  let fromJsonInst ← `(command|
    instance : FromJson $typeName where
      fromJson? j := $fromJsonBody
  )
  elabCommand fromJsonInst

/-! ## Tagged Union Generation -/

/-- Detect if a tagged union is self-recursive -/
def detectSelfRecursion (def_ : SchemaDefinition) : Bool :=
  def_.variants.any fun v =>
    v.properties.any fun p => (propertyTypeShape p).containsRef def_.name

def genTaggedUnion (def_ : SchemaDefinition) : CommandElabM Unit := do
  let typeName := mkTypeIdent def_.name
  let typeNameStr := def_.name
  let discField := def_.discriminatorField
  let isSelfRecursive := detectSelfRecursion def_

  -- Build variant constructors
  let ctorStxs ← def_.variants.toArray.mapM fun v => do
    let ctorName := mkIdent (Name.mkSimple (toCamelCase v.discriminatorValue))
    if v.properties.isEmpty then
      `(Lean.Parser.Command.ctor| | $ctorName:ident)
    else
      let paramBinders ← v.properties.toArray.mapM fun p => do
        let paramName := mkFieldIdent p.name
        let paramType ← propertyToTypeStx p
        `(bracketedBinder| ($paramName : $paramType))
      `(Lean.Parser.Command.ctor| | $ctorName:ident $[$paramBinders]*)

  -- Generate the inductive definition
  let inductiveCmd ← `(command|
    inductive $typeName:ident where
      $[$ctorStxs]*
      deriving Inhabited, BEq, Repr
  )
  elabCommand inductiveCmd

  -- Generate partial toJson function
  let toJsonArms ← def_.variants.toArray.mapM fun v => do
    -- Build qualified constructor pattern as TypeName.CtorName
    let qualCtorName := mkQualIdent typeNameStr (toCamelCase v.discriminatorValue)
    let discPair ← `(($(quote discField), $(quote v.discriminatorValue)))

    if v.properties.isEmpty then
      let result ← `(Json.mkObj [$discPair])
      `(Term.matchAltExpr| | $qualCtorName => $result)
    else
      let paramNames := v.properties.toArray.map fun p =>
        mkIdent (Name.mkSimple ("p_" ++ toCamelCase p.name))

      let fieldPairs ← (v.properties.toArray.zip paramNames).mapM fun (p, paramVar) => do
        let shape := propertyTypeShape p
        let toJsonFnIdent := mkQualIdent typeNameStr "toJson"
        if isSelfRecursive && shape.containsRef typeNameStr then
          match shape with
          | .array _ => `(($(quote p.name), Json.arr (($paramVar).map $toJsonFnIdent)))
          | _ => `(($(quote p.name), $toJsonFnIdent $paramVar))
        else
          `(($(quote p.name), Lean.toJson $paramVar))

      -- Build the pattern with parameters - use direct splicing without brackets
      let result ← `(Json.mkObj [$discPair, $[$fieldPairs],*])
      `(Term.matchAltExpr| | $qualCtorName $paramNames* => $result)

  let toJsonFnName := mkQualIdent typeNameStr "toJson"
  -- Build match expression as body
  let toJsonMatch ← `(match x with $toJsonArms:matchAlt*)
  let toJsonDef ← `(command|
    partial def $toJsonFnName (x : $typeName) : Json := $toJsonMatch
  )
  elabCommand toJsonDef

  let toJsonInst ← `(command|
    instance : ToJson $typeName := ⟨$toJsonFnName⟩
  )
  elabCommand toJsonInst

  -- Generate partial fromJson? function
  let fromJsonArms ← def_.variants.toArray.mapM fun v => do
    let qualCtorName := mkQualIdent typeNameStr (toCamelCase v.discriminatorValue)

    if v.properties.isEmpty then
      let result ← `(.ok $qualCtorName)
      `(Term.matchAltExpr| | $(quote v.discriminatorValue) => $result)
    else
      let bindings ← v.properties.toArray.mapM fun p => do
        let fieldName := mkFieldIdent p.name
        let shape := propertyTypeShape p
        let fieldType ← propertyToTypeStx p
        let fromJsonFnIdent := mkQualIdent typeNameStr "fromJson?"

        if isSelfRecursive && shape.containsRef typeNameStr then
          match shape with
          | .array _ =>
            let jsonVarName := mkIdent (Name.mkSimple (toCamelCase p.name ++ "Json"))
            let listVarName := mkIdent (Name.mkSimple (toCamelCase p.name ++ "List"))
            return #[
              ← `(Parser.Term.doSeqItem| let $jsonVarName ← j.getObjValAs? (Array Json) $(quote p.name)),
              ← `(Parser.Term.doSeqItem| let $listVarName ← ($jsonVarName).toList.mapM $fromJsonFnIdent),
              ← `(Parser.Term.doSeqItem| let $fieldName : $fieldType := ($listVarName).toArray)
            ]
          | .option _ =>
            let jsonVarName := mkIdent (Name.mkSimple (toCamelCase p.name ++ "Json"))
            let someArm ← `(Term.matchAltExpr| | some jv => ($fromJsonFnIdent jv).map some)
            let noneArm ← `(Term.matchAltExpr| | none => .ok none)
            let arms := #[someArm, noneArm]
            let matchExpr ← `(match $jsonVarName:ident with $arms:matchAlt*)
            return #[
              ← `(Parser.Term.doSeqItem| let $jsonVarName := j.getObjVal? $(quote p.name) |>.toOption),
              ← `(Parser.Term.doSeqItem| let $fieldName : $fieldType ← ($matchExpr))
            ]
          | _ =>
            let jsonVarName := mkIdent (Name.mkSimple (toCamelCase p.name ++ "Json"))
            return #[
              ← `(Parser.Term.doSeqItem| let $jsonVarName ← j.getObjVal? $(quote p.name)),
              ← `(Parser.Term.doSeqItem| let $fieldName : $fieldType ← ($fromJsonFnIdent $jsonVarName))
            ]
        else
          return #[← `(Parser.Term.doSeqItem| let $fieldName : $fieldType ← j.getObjValAs? _ $(quote p.name))]

      let allBindings := bindings.flatMap id
      let paramNames := v.properties.toArray.map (mkFieldIdent ·.name)
      let returnExpr ← `($qualCtorName $paramNames*)

      let body ← `(do
          $[$allBindings]*
          .ok $returnExpr)
      `(Term.matchAltExpr| | $(quote v.discriminatorValue) => $body)

  let errorArm ← `(Term.matchAltExpr| | x => .error (s!"invalid {$(quote typeNameStr)} {$(quote discField)}: " ++ x))
  let allFromJsonArms := fromJsonArms.push errorArm

  let fromJsonFnName := mkQualIdent typeNameStr "fromJson?"
  -- Build match expression for discriminator
  let fromJsonMatch ← `(match discVal with $allFromJsonArms:matchAlt*)
  -- Build the body expression without explicit type annotation
  let fromJsonBody ← `(j.getObjValAs? String $(quote discField) >>= fun discVal => $fromJsonMatch)
  -- Build return type for function signature
  let returnType ← `(Except String $typeName)
  -- Build partial def with explicit return type in signature
  let fromJsonDef ← liftTermElabM <| `(partial def $fromJsonFnName:ident (j : Json) : $returnType := $fromJsonBody)
  elabCommand fromJsonDef

  -- Build the instance type separately
  let fromJsonType ← `(FromJson $typeName)
  -- Build instance using liftTermElabM
  let fromJsonInst ← liftTermElabM <| `(instance : $fromJsonType := ⟨$fromJsonFnName⟩)
  elabCommand fromJsonInst

/-! ## Code Generation Dispatch -/

def genDefinition (def_ : SchemaDefinition) : CommandElabM Unit := do
  match def_.kind with
  | .object => genStructure def_
  | .stringEnum => genEnum def_
  | .taggedUnion => genTaggedUnion def_

/-! ## Command Elaborator -/

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
    logInfo m!"Generated {defs.length} type definitions from schema"
    for def_ in topologicalSort defs do
      genDefinition def_
  | _ => throwUnsupportedSyntax

end LeanDag.SchemaCodegen
