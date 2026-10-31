# Autumn roadmap

Ordered backlog for the Elixir subset → IR JSON → Lean 4 VM. Check items off in the same PR that finishes them. Bump [`vm/IR.md`](vm/IR.md) before Lean/Mix when adding opcodes.

## Working rules

- Prefer one phase theme per PR.
- Prefer fixtures + Mix test + `lake exe autumn` before deep new lemmas.
- Catchable language exceptions (`raise`) stay distinct from uncatchable stepper `typeError`.

## Done (through IR v8)

- [x] Register IR v1–8: literals/calls through selective receive + process links (`link` / EXIT signals)
- [x] Generational heap + GC lemmas; reduction-preemptive scheduler (logical clock for timeouts)
- [x] Mix lowerer for the teaching subset + golden fixtures (`try_rescue`, `counter_server`, `link_exit`, guards/maps/dyn cons-tuple, …)
- [x] Exceptions path: nested try, `try/after`, match miss → `raise` `:match_error`, named `rescue e in […]`
- [x] Selective `receive` / `after`; OTP-style sequenced counter server
- [x] Fold `handlersWF` into `Process.WF`; document catchable exceptions vs `typeError` in `vm/IR.md`
- [x] Step/state WF lemmas closed (no `sorry` in `vm/Autumn/*.lean`); `stepInstr_preserves` covers ops through v8

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

## Later (deprioritized)

- ETS
- Verified compiler
