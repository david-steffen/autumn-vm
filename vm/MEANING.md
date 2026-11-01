# Verified compiler sketch (Autumn-authored)

Lynx-inspired layering only — no Lynx text. This note sketches **how compiled
programs are meant**, not Mix soundness. Opcode/JSON details stay in [`IR.md`](IR.md).

## Purity layers

| Layer | Carrier | Intended laws |
| --- | --- | --- |
| Pure term | `Except StepError Term` helpers / builtins without `State` | Deterministic; errors are catchable `:badarg`-class or structural |
| One-step dispatcher | `step` / `stepInstr` / `stepScheduled` | `*_preserves`, `*_progress` (public surface in `Step/Lemmas`) |
| Concurrent machine | `State` + reduction clock + choice tape | `run` / `runScheduled` multi-step; empty tape ≡ `run` |
| Observational | Smoke expects / `Obs.Schedule` | Same `toTerm` result under covering tapes |

Law levels climb **pure → sequential → concurrent**. Do not unfold private stepper
bodies in external proofs — use the named lemma API (`AGENTS.md`).

## Mix lowerer ↔ IR WF

- Mix emits `format: 1` JSON; Lean `Json.Decode` + `Module.checkWF` gate load /
  `load_file` install.
- Lowerer sugar (e.g. `hd`/`tl`/`++`, bitstring match chunking, `if`/`cond`) must
  preserve the teaching subset documented in `IR.md`; no second encyclopedia here.
- Stdlib OTP (`GenServer`, `Agent`, `Task`, `Registry`, …) is **Elixir on existing
  opcodes** — meaning flows through the same step/run lemmas, not separate IR.

## OTP lemma namespaces

`Autumn.OTP.GenServer` / `Supervisor` hold observational call/EXIT laws
(`counterCall_observes_seven`, `trap_exit_delivers_mailbox`) next to stdlib.
Full GenServer refinement stays out of scope.

## IR induction

`Meaning.instr_induction` (Prop case split on every opcode) plus
`wf_instr_regsOk` / `wf_instr_jumpOk` / `wf_code_terminal` lift `Function.WF`
to per-opcode facts. Program-level example: `Meaning.addMain_observes_three`.
