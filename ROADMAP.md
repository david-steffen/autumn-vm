# Autumn roadmap

Ordered backlog for the Elixir subset → IR JSON → Lean 4 VM. Check items off in the same PR that finishes them. Bump [`vm/IR.md`](vm/IR.md) before Lean/Mix when adding opcodes.

## Working rules

- Prefer one phase theme per PR.
- Prefer fixtures + Mix test + `lake exe autumn` before deep new lemmas.
- Catchable language exceptions (`raise`) stay distinct from uncatchable stepper `typeError`.

## Done (through IR v8)

- [x] Register IR v1–8: … + selective receive + process links (`link` / EXIT signals)
- [x] Generational heap + GC lemmas; cooperative scheduler (logical clock for timeouts)
- [x] Mix lowerer for the teaching subset + golden fixtures (`try_rescue`, `counter_server`, `link_exit`, …)
- [x] `stepInstr_preserves` covers ops through v6; v7–8 scheduler/link/exit WF proofs still deferred (`sorry`)

## Phase 1 — Close open loops (no new IR if possible)

1. [x] **Process Elixir path** — `tests/fixtures/ping_pong.ex` + Mix golden; `self/0` builtin for current pid
2. [x] **Exception fixtures** — nested try, unmatched rescue re-raise, no-handler exit; Lean `#guard` for `try_rescue`
3. [x] **`try/after` without rescue** — run `after` on uncaught raise (handler + re-raise after `after`)
4. [x] **Match miss → `raise`** — `case` / multi-clause fallthrough raises `:match_error` instead of returning `nil`

## Phase 2 — Receive like BEAM (IR v7)

1. [x] Selective `receive` with patterns (`recv_peek` / `recv_drop` / scan loop; park via `wait`)
2. [x] `receive … after` timeout (logical-clock `wait` + scheduler deadline wake)
3. [x] OTP-style counter server fixture (`counter_server.ex`; sequenced messages, no dynamic tuples yet)

## Phase 3 — Language surface (mostly lowerer + small builtins)

1. [x] Guards on `def`/`case` (reuse `jump_if_eq` / `is_tag` / comparison builtins) — `guards.ex`
2. [x] Dynamic `cons` / list build (`cons/2`) + `make_tuple/N` — `dyn_list.ex` / `dyn_tuple.ex`
3. [x] Map patterns in `case` / heads via `map_get` — `map_pat.ex`
4. [x] Fold `handlersWF` into `Process.WF` + notes in `vm/IR.md` (some preserve lemmas still `sorry`)

## Phase 4 — Process failure model (IR bump)

1. [x] Links + exit signal propagation (teaching unit, not full BEAM) — `link` / `spawn_link`; `link_exit.ex`
2. [x] Named exception tags / `rescue e in […]` while still value-based — `rescue_in.ex`
3. [x] Document catchable language exceptions vs uncatchable `typeError` in `vm/IR.md`

## Later (deprioritized)

- Floats, binaries/strings as first-class terms
- `fn` / closures
- ETS
- Multi-module loading
- Preemptive scheduling
- Verified compiler
