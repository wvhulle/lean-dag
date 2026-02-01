# Lean DAG

An RPC method extension for the built-in [Lean](https://lean-lang.org/) RPC server. You are supposed to import `LeanDag` in you `lakefile.toml` like this:

```toml
[[require]]
name = "LeanDag"
git = "https://github.com/wvhulle/lean-dag.git"
rev = "main"
```

In combination with another front-end like [`lean-tui`](https://codeberg.org/wvhulle/lean-tui) you can use it to have a custom view on your proof state as a [directed acyclic graph (DAG)](https://en.wikipedia.org/wiki/Directed_acyclic_graph).

The format of the RPC-JSON sent out by this RPC server method is documented in [./protocol-schema.json](./protocol-schema.json). It can be used for automatic code-generation of safe APIs (in Rust, JavaScript or other languages that support this).

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
