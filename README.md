# LeanDag

An LSP server extension for Lean 4 that exposes proof structure via RPC.

## Build

```bash
lake build lean-dag
```

## Test

```bash
lake test
```

## How It Works

```mermaid
flowchart TB
    Editor[Editor / TUI]

    subgraph LeanDag[lean-dag Worker]
        direction TB
        Router{Request?}
        LeanLSP[Lean LSP internals]
        ProofDag[getProofDag RPC]
    end

    subgraph Pipeline[Proof Extraction]
        direction LR
        InfoTree --> Parser[InfoTreeParser]
        Parser --> Builder[DagBuilder]
        Builder --> JSON[ProofDag JSON]
    end

    Editor <-->|LSP| Router
    Router -->|hover, completion, etc.| LeanLSP
    Router -->|getProofDag| ProofDag
    ProofDag --> Pipeline
```

How it works:

- `lean-dag` is a full Lean LSP server (watchdog + workers)
- Standard LSP requests (hover, completion, diagnostics) are handled by Lean's built-in LSP
- The custom `getProofDag` RPC extracts proof structure from Lean's InfoTree
