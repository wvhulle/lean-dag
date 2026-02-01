/-
Copyright (c) 2025 Willem Van Hulle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Std.Internal.Async
import LeanDag.TuiServer.Protocol

open Lean
open Std.Net
open Std.Internal.IO.Async

namespace LeanDag.TuiServer

/-! ## Client Connection -/

/-- A connected TUI client. -/
structure ClientConnection where
  socket : TCP.Socket.Client
  id : Nat

/-! ## TCP Server -/

/-- TCP server that broadcasts messages to TUI clients. -/
structure TcpServer where
  /-- The underlying TCP server socket. -/
  server : TCP.Socket.Server
  /-- Connected clients. -/
  clients : IO.Ref (Array ClientConnection)
  /-- Next client ID counter. -/
  nextId : IO.Ref Nat
  /-- Server mode for RPC communication. -/
  serverMode : ServerMode
  /-- Port the server is listening on. -/
  port : UInt16

namespace TcpServer

/-- Create a new TCP server bound to the specified port. -/
def create (port : UInt16) (serverMode : ServerMode := .standalone) : IO TcpServer := do
  let server ← TCP.Socket.Server.mk
  let addr := SocketAddressV4.mk (IPv4Addr.ofParts 127 0 0 1) port
  server.bind addr
  server.listen 16
  let clients ← IO.mkRef #[]
  let nextId ← IO.mkRef 0
  IO.eprintln s!"[TcpServer] Listening on 127.0.0.1:{port}"
  return { server, clients, nextId, serverMode, port }

/-- Send a message to a single client. Returns false if send failed. -/
def sendToClient (client : ClientConnection) (msg : Message) : IO Bool := do
  let json := Lean.toJson msg
  let line := json.compress ++ "\n"
  let bytes := line.toUTF8
  try
    (client.socket.send bytes).block
    return true
  catch _ =>
    return false

/-- Broadcast a message to all connected clients. -/
def broadcast (srv : TcpServer) (msg : Message) : IO Unit := do
  let clients ← srv.clients.get
  let mut activeClients := #[]
  for client in clients do
    if ← sendToClient client msg then
      activeClients := activeClients.push client
  -- Update clients list, removing disconnected ones
  srv.clients.set activeClients

/-- Broadcast proof DAG to all connected clients. -/
def broadcastProofDag (srv : TcpServer) (uri : String) (position : Lsp.Position) (proofDag : Option ProofDag) : IO Unit :=
  srv.broadcast (.proofDag uri position proofDag)

/-- Broadcast cursor info to all connected clients. -/
def broadcastCursor (srv : TcpServer) (info : CursorInfo) : IO Unit :=
  srv.broadcast (.cursor info)

/-- Broadcast error to all connected clients. -/
def broadcastError (srv : TcpServer) (error : String) : IO Unit :=
  srv.broadcast (.error error)

/-- Find index of first newline in string, returns none if not found. -/
def findNewlineIdx (s : String) : Option Nat := Id.run do
  let mut idx := 0
  for c in s.toList do
    if c == '\n' then
      return some idx
    idx := idx + 1
  return none

/-- Read a line from the client socket. Returns none on EOF or error. -/
partial def readLine (client : TCP.Socket.Client) (buffer : String := "") : Async (Option String) := do
  let chunk? ← client.recv? 1024
  match chunk? with
  | none => return none  -- EOF
  | some chunk =>
    let newData := String.fromUTF8! chunk
    let combined := buffer ++ newData
    -- Look for newline
    match findNewlineIdx combined with
    | some idx =>
      -- Found newline, extract line before it (convert Slice to String)
      let line := (combined.take idx).toString
      return some line
    | none =>
      -- No newline found, keep reading
      readLine client combined

/-- Handle a single client connection. -/
def handleClient (srv : TcpServer) (client : ClientConnection) : Async Unit := do
  IO.eprintln s!"[TcpServer] Client {client.id} connected"

  -- Send Connected message immediately
  let _ ← IO.asTask do
    let _ ← sendToClient client (.connected (some srv.serverMode))

  -- Read loop for commands from client
  for _ in Lean.Loop.mk do
    let line? ← readLine client.socket
    match line? with
    | none =>
      IO.eprintln s!"[TcpServer] Client {client.id} disconnected"
      break
    | some line =>
      if !line.isEmpty then
        match Lean.Json.parse line >>= Command.fromJson? with
        | .ok cmd =>
          match cmd with
          | .navigate uri pos =>
            IO.eprintln s!"[TcpServer] Received navigate command from client {client.id}: {uri}:{pos.line}:{pos.character}"
            -- TODO: Handle navigate via LSP showDocument
          | .getProofDag uri pos mode =>
            IO.eprintln s!"[TcpServer] Received getProofDag command from client {client.id}: {uri}:{pos.line}:{pos.character} mode={mode}"
            -- Note: In library mode, this command cannot be directly handled here
            -- because we don't have access to the document context.
            -- The lean-tui client should use its own RPC client instead.
        | .error e =>
          IO.eprintln s!"[TcpServer] Failed to parse command: {e}"

  -- Remove client from list
  let clients ← srv.clients.get
  srv.clients.set (clients.filter (·.id != client.id))

/-- Accept loop - accepts new connections and spawns handlers. -/
partial def acceptLoop (srv : TcpServer) : Async Unit := do
  for _ in Lean.Loop.mk do
    let client ← srv.server.accept
    let id ← srv.nextId.modifyGet fun n => (n, n + 1)
    let conn : ClientConnection := { socket := client, id }

    -- Add to clients list
    srv.clients.modify (·.push conn)

    -- Spawn client handler in background
    background (handleClient srv conn)

/-- Start the server accept loop in the background. -/
def start (srv : TcpServer) : IO Unit := do
  let _ ← IO.asTask do
    (acceptLoop srv).block

end TcpServer

end LeanDag.TuiServer
