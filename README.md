# Autumn

A weekend project: a small **BEAM-lite** virtual machine, written in **Lean 4**, plus an Elixir Mix compiler that lowers a teaching subset of Elixir to JSON IR.

The goal is to get hands-on with Lean (executable specs, proofs, a real stepper) while peeling back a few layers of how BEAM-style runtimes work — processes, scheduling, messages, OTP-ish patterns — without trying to reimplement OTP.

## Pipeline

```text
Elixir subset  →  Mix lowerer  →  IR JSON (format: 1)  →  Lean VM (`autumn`)
```

Thin stdlib modules (`GenServer`, `Supervisor`, `ETS`, `Agent`, …) live under `stdlib/` and compile alongside app code. Semantics for the IR and builtins are documented in [`vm/IR.md`](vm/IR.md); repo layout and agent/build policy live in [`AGENTS.md`](AGENTS.md).

## Quick start

Tooling: Elixir/Erlang via [`mise.toml`](mise.toml); Lean 4.35 via Lake in `vm/`.

```bash
# VM
cd vm && lake build

# Compiler
cd compiler
mix deps.get
mix autumn.compile ../tests/fixtures/add_main.ex /tmp/add.bc.json

# Run
cd ../vm && lake exe autumn /tmp/add.bc.json
```

Useful Mix tasks (from `compiler/`, after `lake build`):

```bash
mix autumn.smoke          # fixtures with .expect → Lean VM
mix autumn.repl           # interactive EVAL/LOAD loop
mix autumn.bench          # time tests/bench/*.ex
mix autumn.bench_compare  # Autumn vs host BEAM
```

REPL sketch:

```text
autumn(1)> .load ../tests/fixtures/add_main.ex
autumn(2)> Main.add(10, 20)
30
```

## What’s in the box

| Path | Role |
| --- | --- |
| `compiler/` | Mix app: lower `.ex` → IR JSON |
| `vm/` | Lean 4 library + `autumn` executable |
| `stdlib/` | Thin OTP-flavored library modules |
| `tests/fixtures/` | Sample programs + `.expect` (no committed `.bc.json`) |
| `tests/bench/` | Small workloads for timing |

This is intentionally incomplete: a teaching subset, not a drop-in BEAM. Fun over fidelity.
