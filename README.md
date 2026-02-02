# Lean DAG

Enables [Lean](https://lean-lang.org/) users to wire up a separate info view along diagnostics in their IDE if their IDE does not support an info view. An info view is a [proof assistant](https://en.wikipedia.org/wiki/Proof_assistant)-specific user interface that helps mathematicians / developers while writing proofs.

See also, the official [Lean Info-View source](https://github.com/leanprover/vscode-lean4/tree/master/lean4-infoview).

Current features:

- Showing simple open goals and hypotheses
- Showing [directed acyclic graph (DAG)](https://en.wikipedia.org/wiki/Directed_acyclic_graph) of your proof / program
- Using several Lean file buffers simultaneously


Types of programming supported:

- Tactic-mode proof construction view
- Term-mode proof construction view (under construction)

Not supported: HTML and JS-based widgets.

## Installation

You are supposed to import `LeanDag` in your user project's `lakefile.toml` like this:

```toml
[[require]]
name = "LeanDag"
git = "https://github.com/wvhulle/lean-dag.git"
rev = "main"
```

## Usage (for normal users)

See the documentation on [`lean-tui`](https://codeberg.org/wvhulle/lean-tui) for an example on how to use this library.


## Usage (for developers)

To be able to build a front-end on top of library, you need to connect with the TCP port used use the RPC-JSON protocol to speak with it.

The format of the RPC-JSON sent out by this RPC server method is documented in [`protocol-schema.json`](./protocol-schema.json).


Tip: It can be used for automatic code-generation of safe APIs (in Rust, JavaScript or other languages that support this). See for example [`typify`](https://docs.rs/typify/latest/typify/).

## How Does It Work?

All the logic is build around a custom RPC server method. Lean allows users to specify user-space RPC server methods with an attribute.

The TCP server is initialized lazily upon the first user interaction with the Lean LSP.
