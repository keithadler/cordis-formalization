# Cordis Lean 4 Formalization

Lean 4 formalization of *A Programming Paradigm for Spatiotemporal Composability* (`arXiv:2608.25512v1`), including machine-checked counterexamples and corrigenda (`Cordis/Results/`, `Cordis/Repairs/`).

## Layout

- `Cordis.lean` — Root library module and axiom audit (`Cordis.AxiomAudit.check`).
- `Cordis/` — Core calculus, paper-indexed results (`Cordis/Results/`), and scoped repairs (`Cordis/Repairs/`).
- `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` — Lake package configuration (Lean `v4.24.0`, zero external dependencies).

## Building

With `elan` / Lean 4 installed:

```sh
lake build
```
