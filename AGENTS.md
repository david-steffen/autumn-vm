# Autumn

Elixir subset → versioned IR JSON → Lean 4 VM. The Mix lowerer emits bytecode; the Lean executable decodes and runs it.

## Layout

| Path | Role |
| --- | --- |
| `compiler/` | Mix app: lower `.ex` fixtures to IR JSON |
| `vm/` | Lean 4 library + `autumn` exe |
| `vm/Autumn/State/Types.lean` | Frame / Process / State / StepError types |
| `vm/Autumn/Process.lean` | Process GC + alloc runtime |
| `vm/Autumn/State.lean` | State scheduler / links / EXIT |
| `vm/Autumn/{Heap,Process,State,Step}/` | Nested lemmas/satellites (Mathlib-style); barrels `State/Lemmas`, `Step/Lemmas` |
| `vm/Autumn/Json/` | Encode / Decode / Lemmas (JSON ↔ IR) |
| `vm/IR.md` | **IR source of truth** (opcodes, literals, versions) |
| `vm/Autumn/Repl.lean` | Durable `autumn --repl` line protocol |
| `ROADMAP.md` | Ordered backlog (“what’s next”) |
| `tests/fixtures/` | Sample Elixir programs for lowering |
| `stdlib/` | Thin library modules (`genserver.ex`, `supervisor.ex`, `ets.ex`); compile with `AutumnCompiler.compile_files/1` alongside app code |
| `vm/Autumn/Ets.lean` | ETS table ops + match/select/guards/heir (IR v17–v18) |

**Module atoms + `apply_mfa` (IR v15):** a bare alias like `Counter` lowers to atom `"Counter"` (no `Elixir.` prefix). `apply(mod, :init, [arg])` with a literal arg list emits `apply_mfa`, which looks up `"#{mod}.#{fun}/#{arity}"` in the loaded image. Stdlib `GenServer` dispatches `init` / `handle_call` / `handle_cast` / `handle_continue` / optional `handle_info` this way; missing `handle_info/2` → catchable `:undef` rescued as `{:noreply, state}`; `continue` / `:hibernate` (`Process.hibernate/0` GC then loop) return tails supported. Other missing MFA → catchable `:undef`. `Supervisor.start_link(children)` / `start_link(children, max_restarts)` strategies with intensity window (period 100 ticks); child_spec maps may set `:restart` / `:shutdown` / `:significant` / `:type` (carried) and `:start` as `{Mod, arg}` or `{Mod, Fun, [arg]}` MFA; nest via `{Supervisor, :child_main, [children]}` (`spawn_link`). Mix: `use GenServer` (+ `restart:`/`shutdown:`/`significant:`/`type:`), `@behaviour GenServer`, `@impl` strip; requires `init/1` `handle_call/3` `handle_cast/2` `handle_continue/2`. Tuple patterns enforce arity via `tuple_size/1`. IR v19: `wait` timeout `{"reg":R}`; after-only `receive`; `Process.hibernate/0`.

**Binaries (IR v16 / v20):** `Term.bitstring` immediate (`bytes` + `trailingBits`; `0` ⇒ aligned binary). Mix `<<1, 2, "ab">>` → `{"binary":[…]}`; `<<n::k>>` / `::size(k)` for **k ∈ 1…8** (trailing partial → `bitstring` lit). UTF-8 `string` stays separate; `is_binary/1` matches string **or** aligned bitstring; `is_bitstring/1` matches string or any bitstring; `<>/2` appends aligned bitstrings. **v20 matching:** builtins `bit_size/1` / `bs_get_integer/2` / `bs_drop/2`; Mix patterns `<<x::N, rest::binary>>` (literal N) miss → `:match_error`. See `vm/IR.md` v16 / v20.

**ETS (IR v17–v21):** kinds `:set` / `:bag` / `:duplicate_bag` / `:ordered_set`; `ets_new/2` named or anonymous (`nil`); tab id is tid **or** name atom; `lookup` → list of values; `match_object` / `select` with `:_` / `:"$N"`; v18 teaching select guards, `delete_object/2`, owner/heir (`ets_heir/2`, `{:ETS-TRANSFER, tid, from, data}` on owner exit); v21 `ets_first/1` / `ets_next/2` / `ets_give_away/3`. See `vm/IR.md` v17–v21; `stdlib/ets.ex`.

## Build & run

**Compiler** (from `compiler/`, Elixir via `mise.toml`):

```bash
mix deps.get
mix test
mix autumn.compile ../tests/fixtures/add_main.ex /tmp/add.bc.json
# multi-file (stdlib + app):
#   iex> AutumnCompiler.compile_files!(["../stdlib/genserver.ex", "../tests/fixtures/genserver_stdlib.ex"], "/tmp/gs.bc.json")
mix autumn.smoke   # allowlisted fixtures on the Lean VM (build VM first)
```

**VM** (from `vm/`, Lean 4.35):

```bash
lake build
lake exe autumn /tmp/add.bc.json
lake exe autumn --roundtrip /tmp/add.bc.json
lake exe autumn --lean-demo
lake exe autumn --repl   # EVAL/LOAD/QUIT line protocol (usually via Mix)
```

**CI:** `.github/workflows/ci.yml` — Mix test via mise; Lake build + `mix autumn.smoke`.

**REPL** (build the VM first, then from `compiler/`):

```bash
mix autumn.repl
```

### First 5 minutes

```text
autumn(1)> .help
autumn(2)> .load ../tests/fixtures/add_main.ex
autumn(3)> Main.add(10, 20)
30
autumn(4)> x = Main.add(1, 2)
3
autumn(5)> x + 10
13
autumn(6)> .bindings
autumn(7)> .quit
```

Expressions lower as `Repl.main/0` so a loaded `Main` is not overwritten. Mix replays simple `var = …` bindings across lines (RHS re-runs on later lines); Lean keeps modules and resets processes each `EVAL`. Dot commands: `.help`, `.bindings`, `.load`, `.clear`, `.quit`. Protocol: `EVAL`/`LOAD` JSON lines, `QUIT`.
## Coding defaults

- Prefer **type-centered modules** (type + its operations colocated). Cross-type pipelines (`Json.Decode`, `Json.Encode`, `Step`) stay separate. See [`.agents/skills/type-centered-modules/SKILL.md`](.agents/skills/type-centered-modules/SKILL.md).
- Lean modules past ~1k lines or mixed ownership → split per that skill (runtime ↔ nested `*/Lemmas`, barrels, `State.Types` → `Process` → `State`).
- Treat `vm/IR.md` as authoritative when changing opcodes, JSON shapes, or IR versions; keep Lean and Mix in sync.
- Keep changes scoped: no drive-by refactors or unrelated file churn.
- Proof-only material for a type goes in `*Lemmas` next to that type, not in grab-bag utils.
- For Lean: before writing a helper function, check `List`, `Array`, and `String` namespaces. Functions like `filterMap`, `find?`, `any`, and `all` are often built-in.

## Public proof surface (Phase 26)

External / multi-step proofs should use the **named lemma API**, not unfold private stepper bodies:

| Concern | Prefer | Avoid unfolding |
| --- | --- | --- |
| One-step WF | `step_preserves` / `stepInstr_preserves` / per-opcode `*_preserves` in `Step/PreserveInstr` (+ helpers in `Step/Preserve`) | `stepInstr` / `afterInstr` case towers |
| One-step progress | `step_progress` / `stepInstr_error_not_structural` / per-opcode `*_error_not_structural` in `Step/ProgressInstr` | `builtin` / `raiseValue` internals (use `builtin_error_not_structural`, `floatBinop_ne_error`, …) |
| Heap / GC | `Heap/Lemmas` | ad-hoc `Heap` field surgery |
| Scheduler / links / EXIT | `State/Lemmas` barrel (`ProcessLemmas`, `SchedLemmas`, `LinkLemmas`) | raw `scheduleNext` / `signalLink` unfolds |
| JSON ↔ IR | `Json/Lemmas` (`decode*_encode*`) | `JsonNumber.fromFloat?` / hand-rolled lit parsers |

**Rule:** when adding an opcode or call-special builtin, land a matching preserve + progress lemma in the same PR (or a follow-up that blocks merge). The `stepInstr_*` dispatchers must case on every `Instr` constructor. Call-specials (`map_put/3`, `cons/2`, `Process.*`, `ets_*` including v17–v18 `ets_new/2` / `ets_match_object/2` / `ets_select/2` / `ets_delete_object/2` / `ets_heir/2`, `make_ref/0`) keep helpers in `Step/Preserve` and are reached via `call_preserves` / `call_error_not_structural`.

Curated public names are frozen in [`vm/tests/proof_surface.names`](vm/tests/proof_surface.names); CI runs [`vm/scripts/check_proof_surface.sh`](vm/scripts/check_proof_surface.sh) after `lake build`. Rename/add surface lemmas → update the golden in the same PR.

## Skills

Agent skills live under [`.agents/skills/`](.agents/skills/). Read and follow the matching skill when the task fits:

| Skill | When |
| --- | --- |
| [type-centered-modules](.agents/skills/type-centered-modules/SKILL.md) | Module layout / “where does this go?” |
| [lean-proof](.agents/skills/lean-proof/SKILL.md) | Writing or repairing Lean proofs |
| [lean-mwe](.agents/skills/lean-mwe/SKILL.md) | Minimizing Lean errors / bug-report MWEs |
| [lean-bisect](.agents/skills/lean-bisect/SKILL.md) | Finding which Lean commit changed behavior |
| [lean-setup](.agents/skills/lean-setup/SKILL.md) | First-time lean4 clone / toolchain setup |
| [lean-pr](.agents/skills/lean-pr/SKILL.md) | PRs / commits against leanprover/lean4 |
| [mathlib-build](.agents/skills/mathlib-build/SKILL.md) | Building Mathlib (cache, quiet builds) |
| [mathlib-pr](.agents/skills/mathlib-pr/SKILL.md) | PRs / commits against mathlib4 |
| [mathlib-review](.agents/skills/mathlib-review/SKILL.md) | Reviewing Mathlib PRs |
| [nightly-testing](.agents/skills/nightly-testing/SKILL.md) | Nightly CI, toolchain bumps, adaptation PRs |
