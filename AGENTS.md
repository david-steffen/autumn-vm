# Autumn

Elixir subset → IR JSON (`format: 1`) → Lean 4 VM. The Mix lowerer emits bytecode; the Lean executable decodes and runs it.

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
| `vm/IR.md` | **IR source of truth** (opcodes, literals, builtins, scheduling) |
| `vm/builtins.mfa` | Canonical builtin MFA inventory (Mix ↔ Lean sync) |
| `vm/Autumn/Repl.lean` | Durable `autumn --repl` line protocol |
| `ROADMAP.md` | Short backlog (“what’s next”); history is git |
| `vm/MEANING.md` | Verified-compiler sketch (purity layers); not a second IR encyclopedia |
| `tests/fixtures/` | Sample `.ex` programs + `.expect` / optional `.smoke.json` (no committed `.bc.json`) |
| `stdlib/` | Thin library modules (`genserver`, `supervisor`, `ets`, `agent`, `task`, `registry`, `enum`); compile with `AutumnCompiler.compile_files/1` alongside app code |
| `vm/Autumn/Ets.lean` | ETS table ops + match/select/guards/heir |
| `vm/Autumn/{Meaning,Obs,OTP,Meta}/` | Meaning layers, observational schedule laws, OTP stubs, `#eval` exploration |

Feature semantics (GenServer, binaries, ETS, …): see [`vm/IR.md`](vm/IR.md) and stdlib module headers — not duplicated here.

## Build & run

**Compiler** (from `compiler/`, Elixir via `mise.toml`):

```bash
mix deps.get
mix test
mix autumn.compile ../tests/fixtures/add_main.ex /tmp/add.bc.json
# multi-file (stdlib + app):
#   iex> AutumnCompiler.compile_files!(["../stdlib/genserver.ex", "../tests/fixtures/genserver_stdlib.ex"], "/tmp/gs.bc.json")
mix autumn.smoke   # fresh-compile fixtures with .expect; run Lean VM (build VM first)
```

**VM** (from `vm/`, Lean 4.35):

```bash
lake build
lake exe autumn /tmp/add.bc.json
lake exe autumn --roundtrip /tmp/add.bc.json
lake exe autumn --lean-demo
lake exe autumn --repl   # EVAL/LOAD/QUIT line protocol (usually via Mix)
```

**CI:** `.github/workflows/ci.yml` — Mix test via mise; Lake build; proof-surface rename tripwire; builtins sync; `mix autumn.smoke`.

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

Agent vignette (stdlib via multi-file load — compile Agent with GenServer first, or use a fixture smoke path). From Mix after `lake build`:

```text
autumn(1)> .load ../stdlib/genserver.ex
autumn(2)> .load ../stdlib/agent.ex
autumn(3)> .load ../tests/fixtures/agent_basic.ex
autumn(4)> Main.main()
50
```

Expressions lower as `Repl.main/0` so a loaded `Main` is not overwritten. Mix replays simple `var = …` bindings across lines (RHS re-runs on later lines); Lean keeps modules and resets processes each `EVAL`. Dot commands: `.help`, `.bindings`, `.load`, `.clear`, `.quit`. Protocol: `EVAL`/`LOAD` JSON lines, `QUIT`.

## Coding defaults

- Prefer **type-centered modules** (type + its operations colocated). Cross-type pipelines (`Json.Decode`, `Json.Encode`, `Step`) stay separate. See [`.agents/skills/type-centered-modules/SKILL.md`](.agents/skills/type-centered-modules/SKILL.md).
- Lean modules past ~1k lines or mixed ownership → split per that skill (runtime ↔ nested `*/Lemmas`, barrels, `State.Types` → `Process` → `State`).
- Treat `vm/IR.md` as authoritative for opcodes/JSON; `vm/builtins.mfa` for builtin MFA names. Do not add per-construct wire version ladders — bump `format` only on breaking shape changes. Do not commit fixture `.bc.json`.
- Keep changes scoped: no drive-by refactors or unrelated file churn.
- Proof-only material for a type goes in `*Lemmas` next to that type, not in grab-bag utils.
- For Lean: before writing a helper function, check `List`, `Array`, and `String` namespaces. Functions like `filterMap`, `find?`, `any`, and `all` are often built-in.

## Public proof surface

External / multi-step proofs should use the **named lemma API**, not unfold private stepper bodies:

| Concern | Prefer | Avoid unfolding |
| --- | --- | --- |
| One-step WF | `step_preserves` / `stepInstr_preserves` / per-opcode `*_preserves` in `Step/PreserveInstr` (+ helpers in `Step/Preserve`) | `stepInstr` / `afterInstr` case towers |
| One-step progress | `step_progress` / `stepInstr_error_not_structural` / per-opcode `*_error_not_structural` in `Step/ProgressInstr` | `builtin` / `raiseValue` internals (use `builtin_error_not_structural`, `floatBinop_ne_error`, …) |
| Heap / GC | `Heap/Lemmas` | ad-hoc `Heap` field surgery |
| Scheduler / links / EXIT | `State/Lemmas` barrel (`ProcessLemmas`, `SchedLemmas`, `LinkLemmas`) | raw `scheduleNext` / `signalLink` unfolds |
| JSON ↔ IR | `Json/Lemmas` (`decode*_encode*`) | `JsonNumber.fromFloat?` / hand-rolled lit parsers |

**Rule:** when adding an opcode or call-special builtin, land a matching preserve + progress lemma in the same PR (or a follow-up that blocks merge). Update [`vm/builtins.mfa`](vm/builtins.mfa) when adding an MFA. The `stepInstr_*` dispatchers must case on every `Instr` constructor. Call-specials keep helpers in `Step/Preserve` and are reached via `call_preserves` / `call_error_not_structural`.

[`vm/tests/proof_surface.names`](vm/tests/proof_surface.names) + [`vm/scripts/check_proof_surface.sh`](vm/scripts/check_proof_surface.sh) are a **rename tripwire only** — they do not certify exhaustiveness or semantic stability. Builtin MFA sync: [`vm/scripts/check_builtins.sh`](vm/scripts/check_builtins.sh).

## Skills

Agent skills live under [`.agents/skills/`](.agents/skills/). Read and follow the matching skill when the task fits:

| Skill | When |
| --- | --- |
| [type-centered-modules](.agents/skills/type-centered-modules/SKILL.md) | Module layout / “where does this go?” |
| [avoid-wire-version-ladders](.agents/skills/avoid-wire-version-ladders/SKILL.md) | IR/schema version ladders in lockstep codebases |
| [avoid-committed-wire-goldens](.agents/skills/avoid-committed-wire-goldens/SKILL.md) | Committing derived `.bc.json` / wire snapshots |
| [avoid-multi-site-allowlists](.agents/skills/avoid-multi-site-allowlists/SKILL.md) | Hand-copied MFA/builtin string lists |
| [avoid-doc-dual-sot](.agents/skills/avoid-doc-dual-sot/SKILL.md) | Duplicating IR encyclopedias / Phase tags in docs |
| [avoid-ceremonial-name-goldens](.agents/skills/avoid-ceremonial-name-goldens/SKILL.md) | Text-presence “API” goldens that don’t enforce meaning |
| [lean-proof](.agents/skills/lean-proof/SKILL.md) | Writing or repairing Lean proofs |
| [lean-mwe](.agents/skills/lean-mwe/SKILL.md) | Minimizing Lean errors / bug-report MWEs |
| [lean-bisect](.agents/skills/lean-bisect/SKILL.md) | Finding which Lean commit changed behavior |
| [lean-setup](.agents/skills/lean-setup/SKILL.md) | First-time lean4 clone / toolchain setup |
| [lean-pr](.agents/skills/lean-pr/SKILL.md) | PRs / commits against leanprover/lean4 |
| [mathlib-build](.agents/skills/mathlib-build/SKILL.md) | Building Mathlib (cache, quiet builds) |
| [mathlib-pr](.agents/skills/mathlib-pr/SKILL.md) | PRs / commits against mathlib4 |
| [mathlib-review](.agents/skills/mathlib-review/SKILL.md) | Reviewing Mathlib PRs |
| [nightly-testing](.agents/skills/nightly-testing/SKILL.md) | Nightly CI, toolchain bumps, adaptation PRs |
