import Lean
import LeanDag.SchemaCodegen

open Lean

namespace LeanDag.Generated

-- Generate all types from the JSON schema
gen_types_from_schema "protocol-schema.json"

end LeanDag.Generated
