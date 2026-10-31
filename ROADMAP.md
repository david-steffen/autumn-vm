# Autumn roadmap

Ordered backlog for the Elixir subset → IR JSON → Lean 4 VM. Check items off in the same PR that finishes them. Bump [`vm/IR.md`](vm/IR.md) before Lean/Mix when adding opcodes.

## Working rules

- Prefer one phase theme per PR.
- Prefer fixtures + Mix test + `lake exe autumn` before deep new lemmas.
- Catchable language exceptions (`raise`) stay distinct from uncatchable stepper `typeError`.

## Done (through IR v14)

- [x] Register IR v1–13: literals/calls through monitors, floats/strings, closures, multi-module, `load_file`
- [x] Generational heap + GC lemmas; reduction-preemptive scheduler (logical clock for timeouts)
- [x] Mix lowerer for the teaching subset + golden fixtures (`try_rescue`, `counter_server`, `link_exit`, guards/maps/dyn cons-tuple, …)
- [x] Exceptions path: nested try, `try/after`, match miss → `raise` `:match_error`, named `rescue e in […]`
- [x] Selective `receive` / `after`; OTP-style sequenced counter server
- [x] Fold `handlersWF` into `Process.WF`; document catchable exceptions vs `typeError` in `vm/IR.md`
- [x] Step/state WF lemmas closed (no `sorry` in `vm/Autumn/*.lean`); `stepInstr_preserves` + `finishLoadFile_preserves` / `Module.checkWF` gate

## Phase 5 — Monitors + refs (IR v9)

Teaching subset, not full BEAM:

1. [x] Unique refs as a first-class term (JSON/lit + VM tag); builtin `make_ref/0`
2. [x] `monitor` / `demonitor` opcodes (or equivalent); on monitored exit, deliver `{:DOWN, ref, :process, pid, reason}` to the mailbox (unidirectional; no auto-exit)
3. [x] Document in `vm/IR.md` before Lean/Mix; golden fixture e.g. `monitor_exit.ex`
4. [x] WF/preserve lemmas for the new ops (same PR as runtime if small; else follow-up)

## Phase 6 — Monitored call / reply

Build on v9 + existing selective receive (mostly fixtures + lowerer; avoid new IR if possible):

1. [x] Rewrite or add a counter/server fixture using tagged messages (`{from, :add, n}`, …) instead of sequenced bare values (`counter_server.ex`)
2. [x] Client “call” pattern: `monitor` + selective `receive` for reply or `DOWN`; timeout via existing `wait` / `after`
3. [x] `#guard` / Mix golden for the happy path and a crash / `DOWN` path

## Phase 7 — Small language surface (lowerer-first)

No big new term kinds:

1. [x] `if` / `unless` / `cond` → existing jumps / `jump_if_eq` (`if_else.ex`, `cond_main.ex`)
2. [x] List helpers (`hd` / `tl` / `++`) deferred — fixtures use patterns / comparisons instead

## Phase 8 — Floats + strings (IR v10)

1. [x] Float and string immediates (JSON lit + `is_tag`; not heap nodes)
2. [x] Homogeneous float arith / compare; string `<>/2`; `is_float` / `is_binary` as expr or guard
3. [x] Fixture `float_string.ex` + Mix golden; document in `vm/IR.md`

## Phase 9 — Closures (IR v11)

1. [x] Heap `Node.closure` + `make_fun` / `apply`; tag `fun` / `is_function`
2. [x] Mix: lift single-clause `fn` to synthetic MFA (captures first); lower `f.(…)`
3. [x] Fixture `closure_capture.ex` + Mix golden; document in `vm/IR.md`
4. [x] WF/preserve lemmas for the new ops

## Phase 10 — Match `=` + pin `^` (lowerer-only)

1. [x] `pat = expr` via existing pattern emitters; miss → `raise :match_error`
2. [x] Pin `^var` in patterns (`==/2` + `jump_if_eq`); nested compounds/lists/maps
3. [x] Fixture `match_pin.ex` + Mix golden; document in `vm/IR.md`

## Phase 11 — Multi-module (IR v12)

1. [x] Lean `CodeModule` + `Module.modules`; decode/encode/WF; `findFunction` flattens
2. [x] Mix: lower per `defmodule`, `assemble` / multi-file compile; single-module still flat
3. [x] Fixture `multi_mod.ex` + Mix golden; document in `vm/IR.md`

## Phase 12 — Preemptive scheduling

1. [x] Document reduction-budget preemption in `vm/IR.md` / State comments (no algorithm change)
2. [x] Fixture `preempt_fair.ex`: infinite hog cannot starve helper reply; Mix golden + VM smoke → `1`

## Phase 13 — Dynamic `Code.load_file` (IR v13)

1. [x] `load_file` opcode + `Module.installModules`; IO runner; catchable `:enoent` / `:badarg` / `:bad_bytecode`
2. [x] Mix `Code.load_file/1`; fixtures `hot_load/` + `hot_load.ex`; VM smoke → `11`
3. [x] Document in `vm/IR.md`
4. [x] Gate successful install on `Module.checkWF` + live `processesModuleOkB`; `finishLoadFile_preserves` / `raiseLoadAtCurrent_preserves`

## Phase 14 — Usable alpha runtime (IR v14)

No stdlib / ETS / binaries:

1. [x] Durable drain: entry exit does not halt; machine result when idle
2. [x] OTP-shaped `trap_exit` (default false); `Process.flag/2` / `Process.exit/2`
3. [x] Language-shaped builtin mismatches → catchable `:badarg`
4. [x] Fixtures: `drain_siblings`, `link_exit` (trap), `link_kill`, `process_exit_down`, `badarg_rescue`
5. [x] Document in `vm/IR.md`; WF/preserve for drain + kill path + flag/exit

## Phase 15 — Durable REPL

1. [x] Lean `autumn --repl`: `EVAL` / `LOAD` / `QUIT`; modules persist, processes reset per eval
2. [x] Mix `autumn.repl` + `AutumnCompiler.eval_expr/1` (wrap expression as `Repl.main/0`)
3. [x] Document in `AGENTS.md`

## Phase 16 — VM proof depth

One-step `step_progress` / `step_preserves` are closed. Push past single-step WF into multi-step, semantics, and maintainability (no new IR unless a proof forces a tiny helper).

1. [x] `State.initial_WF` + multi-step `run_progress` / `runModule_progress` (`runModule` path)
2. [x] Durable-drain semantics: `scheduleNext_result_is_toTerm` (idle publish ⇒ `Heap.toTerm`)
3. [x] Factor `stepInstr_preserves` / `stepInstr_error_not_structural` case towers (per-opcode helpers)
4. [x] Encode ↔ Decode tag roundtrip (`decodeTag_encodeTag`); Instr/Module roundtrip → Phase 17.1
5. [x] `afterInstr_preserves` (clock / reductions / `scheduleNext`); `runIOState` → Phase 17.1 pure FS
6. [x] `versionOkB_complete` + `FunName.resolvableB_complete`; `regsOk` / `moduleOkB` → Phase 17.1
7. [x] Observational OTP: `signalLink_trapExit_eq_mailbox` (`trap_exit` ⇒ mailbox EXIT, not kill)

## Phase 17 — Proof tails, REPL, lowerer, CI

Demo + trust. One theme per PR. Float JSON / live-`IO` tails → Phase 18.

### 17.1 — Close Phase 16 proof tails

1. [x] `decodeLit_encodeLit` (non-float) → `decodeInstr_encodeInstr` → `decodeModule_encodeModule` (`modules[]` image); move `resolvableB_complete` into `WellFormed`
   - Done: structural `Term.FloatFree`; `decodeLitWithFuel_encodeLit` / `decodeLit_encodeLit` (all non-float terms); `decodeInstr_encodeInstr`; `decodeModule_encodeModule` (`modules[]`); `resolvableB_complete` in `WellFormed`.
2. [x] `peekLoadFile_spec` + pure `runIOStatePure` + `runIOStatePure_preserves` / `_progress`
3. [x] `instrOkB_complete` → uniqueness/`checkWF` completeness → `moduleOkB_complete` / `processesModuleOkB_complete`

### 17.2 — REPL as the demo

1. [x] Mix `.help` / `.bindings`; unknown `.foo` → Mix error (not lowerer)
2. [x] AGENTS “First 5 minutes” REPL walkthrough

### 17.3 — Lowerer ergonomics

1. [x] Multi-clause `fn` (reuse multi-clause `def` → `case`); fixture + golden
2. [x] `hd` / `tl` / `++` lowerer-only onto existing list IR; fixture + golden; IR.md sugar note
3. [x] Clearer diagnostics for bad `fn` / `pat =` (context prefix)

### 17.4 — Fixture gallery + CI smoke

1. [x] Wire `list_lit` Mix golden assert
2. [x] `mix autumn.smoke` allowlist → `lake exe autumn` / `AUTUMN_VM`
3. [x] GitHub Actions: `mix test` + `lake build` + smoke; document in AGENTS

## Phase 18 — Deferred Phase 17 tails

1. [x] Float JSON encode/decode roundtrip under `JsonNumber.fromFloat? = .inr _` (`.inl` → `⟨0,0⟩`); see `decodeLit_encodeLit_float_*`
2. [x] Live `load_file` IO bridge: `interpretLoadFile` shared by `runIOState` / `runIOStatePure`; `interpretLoadFile_preserves`

## Phase 19 — GenServer patterns + smoke gallery

No new IR (teaching GenServer as lowerer patterns on monitors / selective receive / refs).

1. [x] `genserver_counter.ex`: `{:call, from, ref, req}` / `{:reply, ref, _}` + `make_ref` + monitor; Mix golden; VM → `7`
2. [x] `genserver_call_down.ex`: pinned `^mref` DOWN on crash; Mix golden; VM → `1`
3. [x] Expand `mix autumn.smoke` allowlist (`fn_multi`, `list_helpers`, genserver_*, `counter_server`, `list_lit`, …)

## Phase 20 — Multi-step preservation + idle-drain observational

Dual of `run_progress`; lift `scheduleNext_result_is_toTerm` through the runner.

1. [x] `run_preserves` / `runModule_preserves` — successful `run` witnesses WF state with that machine result
2. [x] `afterInstr_result_is_toTerm` / `stepInstr_result_is_toTerm` / `step_result_is_toTerm`
3. [x] `run_result_is_toTerm` / `runModule_result_is_toTerm` — idle-drain value is `Heap.toTerm`

## Later (deprioritized)

- ETS
- Stdlib (`GenServer` / `Supervisor` as real modules, not fixtures)
- Verified compiler
- Bit-identical float identity (`n.toFloat = f`) when `fromFloat?` succeeds
