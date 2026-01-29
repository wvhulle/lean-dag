# LeanAnalyzer

An LSP server extension for Lean 4 that exposes proof structure via RPC.

## Build

```bash
lake build lean-analyzer
```

## Test

```bash
lake test
```

## Usage

The `lean-analyzer` binary is an LSP server with an additional RPC endpoint:

```
LeanAnalyzer.getProofDag
```

**Parameters:**
- `textDocument`: Document identifier
- `position`: Cursor position (line/character)
- `mode`: `"tree"` (full proof) or `"single_tactic"` (current tactic only)

**Returns:** `ProofDag` with:
- `nodes`: Array of proof steps with tactic text, goals before/after, parent/children
- `root`: Index of root node
- `currentNode`: Index of node at cursor position
- `initialState`: Starting proof state

## Project Structure

```
LeanAnalyzer/       # Library source
  Types.lean        # ProofDag, GoalInfo, etc.
  InfoTreeParser.lean  # Extract proof steps from Lean's InfoTree
  LspServer.lean    # RPC handler

Tests/              # Test suite
  Unit*.lean        # Unit tests (mock data)
  Rpc*.lean         # Integration tests (live server)

Demos/              # Test fixtures
  test-project/     # Sample Lean files for testing
```
