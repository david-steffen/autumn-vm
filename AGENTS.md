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

## Build & run

**Compiler** (from `compiler/`, Elixir via `mise.toml`):

```bash
mix deps.get
mix test
mix autumn.compile ../tests/fixtures/add_main.ex /tmp/add.bc.json
```

**VM** (from `vm/`, Lean 4.35):

```bash
lake build
lake exe autumn /tmp/add.bc.json
lake exe autumn --roundtrip /tmp/add.bc.json
lake exe autumn --lean-demo
lake exe autumn --repl   # EVAL/LOAD/QUIT line protocol (usually via Mix)
```

**REPL** (build the VM first, then from `compiler/`):

```bash
mix autumn.repl
# autumn(1)> 1 + 2
# autumn(2)> .load ../tests/fixtures/add_main.ex
# autumn(3)> Main.add(10, 20)
# autumn(4)> .quit
```

Expressions lower as `Repl.main/0` so a loaded `Main` is not overwritten. Mix replays simple `var = …` bindings across lines; Lean keeps modules and resets processes each `EVAL`. Protocol: `EVAL`/`LOAD` JSON lines, `QUIT`.

## Coding defaults

- Prefer **type-centered modules** (type + its operations colocated). Cross-type pipelines (`Json.Decode`, `Json.Encode`, `Step`) stay separate. See [`.agents/skills/type-centered-modules/SKILL.md`](.agents/skills/type-centered-modules/SKILL.md).
- Lean modules past ~1k lines or mixed ownership → split per that skill (runtime ↔ nested `*/Lemmas`, barrels, `State.Types` → `Process` → `State`).
- Treat `vm/IR.md` as authoritative when changing opcodes, JSON shapes, or IR versions; keep Lean and Mix in sync.
- Keep changes scoped: no drive-by refactors or unrelated file churn.
- Proof-only material for a type goes in `*Lemmas` next to that type, not in grab-bag utils.
- For Lean: before writing a helper function, check `List`, `Array`, and `String` namespaces. Functions like `filterMap`, `find?`, `any`, and `all` are often built-in.

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
