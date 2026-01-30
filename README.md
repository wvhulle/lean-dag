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

## Usage

The `lean-dag` binary is an LSP server with an additional RPC endpoint:

```
LeanDag.getProofDag
```
