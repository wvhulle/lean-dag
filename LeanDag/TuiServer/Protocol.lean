/-
Copyright (c) 2025 Willem Van Hulle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import LeanDag.Types

open Lean

namespace LeanDag.TuiServer

/-! ## Server Mode -/

/-- Server mode for RPC communication. -/
inductive ServerMode where
  | library    -- Library mode: uses `lake serve`, requires `import LeanDag`
  | standalone -- Standalone mode: uses lean-dag binary, no import required
  deriving Inhabited, BEq, Repr

instance : ToJson ServerMode where
  toJson
    | .library => "Library"
    | .standalone => "Standalone"

instance : FromJson ServerMode where
  fromJson? j := do
    let s ← j.getStr?
    match s with
    | "Library" => pure .library
    | "Standalone" => pure .standalone
    | _ => throw s!"invalid ServerMode: {s}"

/-! ## Cursor Info -/

/-- Cursor location with document URI and trigger method. -/
structure CursorInfo where
  uri : String
  position : Lsp.Position
  method : String
  deriving Inhabited, BEq, Repr, ToJson, FromJson

/-! ## Messages (Server → TUI) -/

/-- Messages sent from server to TUI over the TCP socket. -/
inductive Message where
  | connected (serverMode : Option ServerMode)
  | cursor (info : CursorInfo)
  | proofDag (uri : String) (position : Lsp.Position) (proofDag : Option ProofDag)
  | error (error : String)
  deriving Inhabited, Repr

/-- Convert Message to JSON with tagged format matching Rust serde. -/
def Message.toJson : Message → Json
  | .connected serverMode =>
    Json.mkObj [("type", "Connected"), ("server_mode", Lean.toJson serverMode)]
  | .cursor info =>
    Json.mkObj [("type", "Cursor"), ("uri", info.uri), ("position", Lean.toJson info.position), ("method", info.method)]
  | .proofDag uri pos dag =>
    Json.mkObj [("type", "ProofDag"), ("uri", uri), ("position", Lean.toJson pos), ("proof_dag", Lean.toJson dag)]
  | .error err =>
    Json.mkObj [("type", "Error"), ("error", err)]

instance : ToJson Message := ⟨Message.toJson⟩

/-- Parse Message from JSON. -/
def Message.fromJson? (j : Json) : Except String Message := do
  let type ← j.getObjValAs? String "type"
  match type with
  | "Connected" =>
    let serverMode ← j.getObjValAs? (Option ServerMode) "server_mode"
    return .connected serverMode
  | "Cursor" =>
    let uri ← j.getObjValAs? String "uri"
    let position ← j.getObjValAs? Lsp.Position "position"
    let method ← j.getObjValAs? String "method"
    return .cursor { uri, position, method }
  | "ProofDag" =>
    let uri ← j.getObjValAs? String "uri"
    let position ← j.getObjValAs? Lsp.Position "position"
    let proofDag ← j.getObjValAs? (Option ProofDag) "proof_dag"
    return .proofDag uri position proofDag
  | "Error" =>
    let error ← j.getObjValAs? String "error"
    return .error error
  | _ => throw s!"invalid Message type: {type}"

instance : FromJson Message := ⟨Message.fromJson?⟩

/-! ## Commands (TUI → Server) -/

/-- Commands sent from TUI to server. -/
inductive Command where
  | navigate (uri : String) (position : Lsp.Position)
  | getProofDag (uri : String) (position : Lsp.Position) (mode : String)
  deriving Inhabited, BEq, Repr

/-- Convert Command to JSON with tagged format matching Rust serde. -/
def Command.toJson : Command → Json
  | .navigate uri position =>
    Json.mkObj [("type", "Navigate"), ("uri", uri), ("position", Lean.toJson position)]
  | .getProofDag uri position mode =>
    Json.mkObj [("type", "GetProofDag"), ("uri", uri), ("position", Lean.toJson position), ("mode", mode)]

instance : ToJson Command := ⟨Command.toJson⟩

/-- Parse Command from JSON. -/
def Command.fromJson? (j : Json) : Except String Command := do
  let type ← j.getObjValAs? String "type"
  match type with
  | "Navigate" =>
    let uri ← j.getObjValAs? String "uri"
    let position ← j.getObjValAs? Lsp.Position "position"
    return .navigate uri position
  | "GetProofDag" =>
    let uri ← j.getObjValAs? String "uri"
    let position ← j.getObjValAs? Lsp.Position "position"
    let mode ← j.getObjValAs? String "mode" <|> pure "tree"
    return .getProofDag uri position mode
  | _ => throw s!"invalid Command type: {type}"

instance : FromJson Command := ⟨Command.fromJson?⟩

end LeanDag.TuiServer
