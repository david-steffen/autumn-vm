# Autumn

Elixir subset → versioned IR JSON → Lean 4 VM. The Mix lowerer emits bytecode; the Lean executable decodes and runs it.

## Layout

| Path | Role |
| --- | --- |
| `compiler/` | Mix app: lower `.ex` fixtures to IR JSON |
| `vm/` | Lean 4 library + `autumn` exe |
| `vm/Autumn/StateTypes.lean` | Frame / Process / State / StepError types |
| `vm/Autumn/Process.lean` | Process GC + alloc runtime |
| `vm/Autumn/State.lean` | State scheduler / links / EXIT |
| `vm/Autumn/*Lemmas.lean` | Proofs: `HeapLemmas`, `ProcessLemmas`, `State*Lemmas` barrel, `StepProgress` / `StepPreserve` / `StepLemmas` |
| `vm/IR.md` | **IR source of truth** (opcodes, literals, versions) |
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
```

## Coding defaults

- Prefer **type-centered modules** (type + its operations colocated). Cross-type pipelines (`Decode`, `Encode`, `Step`) stay separate. See [`.agents/skills/type-centered-modules/SKILL.md`](.agents/skills/type-centered-modules/SKILL.md).
- Lean modules past ~1k lines or mixed ownership → split per that skill (runtime ↔ `*Lemmas` pairing, lemma barrels, `StateTypes` → `Process` → `State`).
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
