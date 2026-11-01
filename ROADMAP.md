# Autumn roadmap

Ordered backlog for the Elixir subset → IR JSON → Lean 4 VM. Check items off in the same PR that finishes them. Bump [`vm/IR.md`](vm/IR.md) before Lean/Mix when adding opcodes.

## Working rules

- Prefer one phase theme per PR.
- Prefer fixtures + Mix test + `lake exe autumn` before deep new lemmas.
- Catchable language exceptions (`raise`) stay distinct from uncatchable stepper `typeError`.

## Done (through IR v15)

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

## Phase 21 — Thin `GenServer` stdlib

Client helpers only (no behaviour / `init` / Supervisor). Servers still hand-write the receive loop.

1. [x] `stdlib/genserver.ex`: `call/2`, `cast/2`, `reply/3` (monitor + selective receive; DOWN/after → `0`)
2. [x] Fixtures `genserver_stdlib` / `genserver_stdlib_down` via `compile_files`; Mix golden + smoke → `7` / `0`
3. [x] Document in `AGENTS.md`; smoke allowlist accepts stdlib companion sources

## Phase 22 — Dynamic MFA, GenServer behaviour, Supervisor (IR v15)

OTP-shaped runtime dispatch: module is a runtime atom; callbacks look up `"#{mod}.#{fun}/#{arity}"`.

1. [x] IR v15 `apply_mfa` — Instr/Step/Json/WF + preserve/progress; catchable `:undef` / `:badarg`
2. [x] Mix: bare alias → atom; `apply/3` with literal arg list → `apply_mfa`; `spawn(Mod, :fun, […])`
3. [x] `stdlib/genserver.ex`: `start` / `start_link` / `server` + `init` / `handle_call` / `handle_cast` via `apply_mfa`
4. [x] `stdlib/supervisor.ex`: thin `one_for_one` (`start_link` / monitor / restart)
5. [x] Fixtures `genserver_behaviour` → `8`, `supervisor_one_for_one` → `6`; Mix goldens + smoke
6. [x] `GenServer.call` `after` budget 50→500 (client timeout under supervisor restart load) + demonitor on timeout

## Phase 23 — `handle_info` + supervisor intensity

Stdlib-first (no new IR). `receive after` timeouts stay literal (period fixed at 100 ticks).

1. [x] `GenServer`: optional `handle_info/2` via `apply_mfa`; missing MFA → rescue `:undef` as `{:noreply, state}`
2. [x] Non-`{:call,:cast}` mailbox messages → `handle_info` catch-all in `loop/2`
3. [x] Supervisor intensity: `start_link(children, max_restarts)` (default 3); period = 100 ticks quiet reset; exceed → exit `:shutdown`
4. [x] Fixtures `genserver_info` → `3`, `supervisor_intensity` → `1`; Mix goldens + smoke
5. [x] Out of scope (Phase 23): `rest_for_one` / `one_for_all`, `continue`, child_spec maps, `use GenServer`, variable `after` timeout

## Phase 24 — Supervisor strategies + demonitor flush + thin ETS

1. [x] `Supervisor`: `rest_for_one` / `one_for_all` (`start_link(children, strategy, max_restarts)`); fixtures → `8` / `5`
2. [x] `demonitor` always flushes pending `{:DOWN, ref, …}` (OTP `[:flush]`); IR.md + Lean preserve/progress
3. [x] Thin ETS: `ets_new/0` `ets_insert/3` `ets_lookup/2` `ets_delete/2` (State tables; lookup → value or `nil`); `stdlib/ets.ex`; fixture/smoke → `42`

## Lynx-inspired work (license)

Intended project license: **MIT** (simple VM). [Lynx](https://github.com/josevalim/lynx) is **Apache-2.0** — adapted Lynx source cannot be re-licensed as MIT; it would stay Apache-2.0 with NOTICE/headers inside an otherwise MIT tree.

Default for FiniteFloat / Bitstring: **clean-room** from IEEE / Erlang semantics (same shape, no Lynx text) so the tree stays MIT-only. Phases 26–27 and Later are design inspiration only.

## Phase 25 — FiniteFloat (IR unchanged)

Finite IEEE binary64 so float proofs no longer dodge Lean `Float` / `JsonNumber.fromFloat?`. Clean-room (MIT); do not copy Lynx Lean.

1. [x] Add root MIT `LICENSE` if not already present
2. [x] `Autumn.Term.FiniteFloat` (`sign` / `exp < 2047` / `frac`) + `add`/`sub`/`mul`/`div`/`ofScientific`/`toRat` (fail on inf/NaN)
3. [x] `Term.float` / heap immediates use `FiniteFloat`; Step arith/compare via FiniteFloat (mixed int/float still `:badarg`)
4. [x] JSON lit encode/decode via exact fields or scientific mantissa/exp; `Term.FloatFree` now allows floats
5. [x] Bit-identical float encode/decode (`decodeLit_encodeLit_float`); fixture + Mix golden + smoke

## Phase 26 — Public proof surface

Make opcode/builtin lemmas the stable API (Lynx-style expose / public-lemma discipline). No new IR; Autumn-authored.

1. [x] Document “proofs use Preserve/Progress helpers, not private `stepInstr` unfolds” in `AGENTS.md` / lemma module headers
2. [x] Audit `Step/PreserveInstr` + `ProgressInstr` + key State/Heap lemmas — every `Instr` has preserve + progress; call-specials + `builtin_error_not_structural` documented in `PreserveInstr` header
3. [ ] Optional (deferred): Lean test snapshot of exported proof names once the surface stabilizes further

## Phase 27 — Schedule-quantified observational specs

Dual of today’s deterministic `scheduleNext`: quantify over fair scheduler choices. Prefer a thin choice list over baking nondeterminism into `State`. Autumn-authored; Lynx is the prior art for the idea.

1. [x] Define `ScheduleChoice` / `scheduleNextWith` / `popChoice` on `State`; `Step.Schedule` runners (`stepScheduled` / `runScheduled` / `afterInstrWith`) consume a choice tape at top-level schedule points (park paths inside `stepInstr` stay deterministic)
2. [x] Observational lemmas: `exists_schedule_prefer`, `forall_includes_roundRobin`, `covers`, `scheduleNextWith_prefer_runnable` (+ WF preserve); OTP-fixture schedule laws can grow on this API
3. [x] Default `run` / smoke path unchanged (deterministic `scheduleNext`)

## Phase 28 — Binaries / bitstrings

Teaching subset grows past UTF-8 `string`-as-binary. Clean-room from Erlang binary semantics (MIT); no Lynx Bitstring text. Bump IR when terms/opcodes land.

1. [x] Aligned binaries: `Term.Bitstring` / `Term.bitstring` immediate; Mix `<<…>>` → `{"binary":[…]}`; `<>/2` aligned append; `is_binary` / `is_bitstring`; UTF-8 `string` stays separate (documented in `IR.md` v16)
2. [x] Partial bitstrings + `Valid` (`trailingBits` 1…7, unused low bits cleared via `ofBytesTrailing?`); JSON `bitstring` lit; Mix segment construct for partial sizes deferred (aligned-only `<<…>>`)
3. [x] WF/preserve/progress + fixture/smoke `binary_basic`; string remains separate immediate

## Phase 29 — Richer ETS (IR v17)

Teaching subset (not full OTP). Objects are `{key, val}`.

1. [x] `EtsKind` + named tables; `Autumn/Ets.lean` (resolve, kind insert, match/select)
2. [x] Builtins: `ets_new/2`, list `ets_lookup/2`, `ets_match_object/2`, `ets_select/2` (empty guards; `:_` / `:"$N"` / `:'$_'` / `:'$$'`); tab = tid or name atom
3. [x] Preserve/progress (+ `result_is_toTerm`); IR.md v17; Mix `needs_v17?`
4. [x] `stdlib/ets.ex`; fixtures `ets_basic` (list lookup) / `ets_bag` → `2` / `ets_named` → `7` / `ets_select` → `5`; Mix goldens + smoke
5. [x] Out of scope: `ordered_set`, non-empty guards, continuations, `delete_object`, ownership/heir

## Phase 30 — Mix partial bitstring construct

Close the Phase 28 Mix gap: Lean/JSON already accept partial `bitstring` lits; lowerer still emits aligned-only `<<…>>`.

No new IR version if only Mix → existing `{"bitstring":{"bytes":[…],"trailing_bits":k}}` (v16).

1. [x] Mix: integer segments with explicit `::size` / `::size(N)` for **N ∈ 1…7** on a trailing partial (and full bytes with `::8` / default); combine into one lit via Lean’s `Valid` / cleared unused low bits
2. [x] Reject unsupported forms clearly (`::binary`, dynamic size, non-int value, mid-construct partial that isn’t last, size > 8 except via multi-byte — teaching: keep small)
3. [x] Fixture `bitstring_partial.ex` + Mix golden + smoke (e.g. `is_bitstring` / `not is_binary` / equality against a known shape → small int)
4. [x] Document Mix construct in `vm/IR.md` v16 section; AGENTS one-liner
5. [x] Out of scope: binary **matching** / comprehensions, `::utf8` construct beyond today’s string chunks, non-literal sizes, `<>/2` of partials (still `:badarg`)

## Phase 31 — Thin `use GenServer` + child_spec

Demo surface on existing IR (no new opcodes). Teaching subset — not full OTP behaviours.

1. [x] `GenServer.child_spec({mod, arg})` (and/or `child_spec(arg)` when used via `use`) → map `%{id: mod, start: {mod, arg}}` (Autumn-shaped; not full OTP `:start` MFA)
2. [x] `Supervisor`: accept child_spec **maps** beside `{Mod, arg}` tuples; start via `GenServer.start` / `start_link` as today
3. [x] Mix: expand bare `use GenServer` in a `defmodule` into an injected `def child_spec(arg)` (AST rewrite before lower — no general macro engine); unknown `use X` → clear error
4. [x] Fixture: callback module with `use GenServer` + supervisor started from `[Counter.child_spec(0)]` (or map lit) → smoke int; Mix golden
5. [x] Document in `AGENTS.md` / stdlib comments; smoke allowlist
6. [x] Out of scope: `@behaviour` checking, `handle_continue` / `{:continue, _}`, full OTP child_spec keys (`:restart`, `:shutdown`, `:type`), `use GenServer, …` options, `def call` macro sugar

## Phase 32 — ETS tails (IR v18)

Teaching subset: select guards, `delete_object`, `ordered_set`, ownership/heir. Not full OTP.

1. [x] IR.md v18 + Mix `needs_v18?` + Lean `versionOk*` / Decode
2. [x] `EtsTable` owner/heir/alive; `:ordered_set` insert order; `deleteObject`; teaching `evalGuard`; `resolveTab` skips dead
3. [x] Builtins `ets_delete_object/2` / `ets_heir/2`; owner on `ets_new`; `propagateExit` → heir transfer or kill; preserve/progress/`result_is_toTerm`
4. [x] `stdlib/ets.ex`; fixtures `ets_guards` → `2` / `ets_delete_object` → `3` / `ets_ordered` → `1` / `ets_heir` → `42`; Mix goldens + smoke
5. [x] Out of scope: `give_away`, private tables, rich match-spec BIFs, `first`/`next`/`slot`

## Phase 33 — GenServer extras (teaching)

No new IR version. Stdlib + Mix expand.

1. [x] Mix: `@behaviour` / `@impl` strip; `use GenServer` options `restart:` / `shutdown:` / `significant:`; require `init/1` `handle_call/3` `handle_cast/2` `handle_continue/2`
2. [x] GenServer: `{:continue, _}` / `:hibernate` (noop) return tails; `handle_continue` chain; stop returns reason
3. [x] Supervisor: `:restart` permanent/temporary/transient; `:shutdown` brutal_kill vs exit; `:significant` drop ⇒ supervisor `:shutdown`; extended child records
4. [x] Fixtures `genserver_continue` → `2` / `supervisor_temporary` → `1` / `supervisor_significant` → `1`; Mix tests; smoke
5. [x] Out of scope: start MFA, `:type`, real hibernate, `@impl` name check, receive-after sleep on shutdown ms

## Phase 34 — Pattern/receive polish + OTP gaps

1. [x] Mix: tuple pattern arity via `tuple_size/1`; fixture `tuple_pattern_arity` → `3`; GenServer case simplified
2. [x] IR v19 `WaitTimeout` lit|reg|infinity; after-only receive; variable after timeout; Supervisor shutdown wait
3. [x] OTP gaps: start MFA (`{Mod,Fun,[arg]}`), `:type` carry, `Process.hibernate/0` + GenServer `:hibernate` tails
4. [x] Fixtures `receive_after_var` → `1` / `genserver_hibernate` → `4` / `supervisor_shutdown_wait` → `4` / `supervisor_start_mfa` → `9`; ROADMAP/AGENTS/IR.md
5. [x] Out of scope: true BEAM hibernate, nested supervisor `:type` ordering, dynamic MFA spawn from non-literal Mix args, rewriting historical v7 wait JSON

## Later (deprioritized)

- Verified compiler — when started, design purity layers (`Except` / dispatcher / effectful result + law levels pure→concurrent) for compiled-program meaning; OTP-shaped Lean namespaces (`GenServer` / `Supervisor` lemmas) alongside stdlib (inspiration only)
- Induction principles over IR functions if program-level laws appear
