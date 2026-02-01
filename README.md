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
    subgraph Clients
        Editor[Editor]
        TUI[lean-tui]
    end

    subgraph Worker[lean-dag Worker]
        direction TB
        Router{LSP Request}
        LeanLSP[Lean LSP]
        RPC[getProofDag RPC]
        Broadcast[TCP Broadcast]
    end

    subgraph Pipeline[Proof Extraction]
        direction LR
        InfoTree[InfoTree]
        Parser[InfoTreeParser]
        Builder[DagBuilder]
        JSON[ProofDag]
    end

    Editor <-->|LSP| Router
    Router -->|hover, completion| LeanLSP
    Router -->|getProofDag| RPC
    Router -->|hover, plainGoal| Broadcast
    RPC --> Pipeline
    Broadcast --> Pipeline
    Pipeline --> JSON
    Broadcast <-->|TCP| TUI
    TUI -.->|Navigate| Editor
```

How it works:

- `lean-dag` is a full Lean LSP server (watchdog + workers)
- Standard LSP requests (hover, completion, diagnostics) are handled by Lean's built-in LSP
- The custom `getProofDag` RPC extracts proof structure from Lean's InfoTree
