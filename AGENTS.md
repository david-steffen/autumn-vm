# Autumn

Elixir subset → versioned IR JSON → Lean 4 VM. The Mix lowerer emits bytecode; the Lean executable decodes and runs it.

## Layout

| Path | Role |
| --- | --- |
| `compiler/` | Mix app: lower `.ex` fixtures to IR JSON |
| `vm/` | Lean 4 library + `autumn` exe |
| `vm/IR.md` | **IR source of truth** (opcodes, literals, versions) |
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

- Prefer **type-centered modules** (type + its operations colocated). Cross-type pipelines (`Decode`, `Encode`, `Step`) stay separate. See [`.cursor/skills/type-centered-modules/SKILL.md`](.cursor/skills/type-centered-modules/SKILL.md).
- Treat `vm/IR.md` as authoritative when changing opcodes, JSON shapes, or IR versions; keep Lean and Mix in sync.
- Keep changes scoped: no drive-by refactors or unrelated file churn.
- Proof-only material for a type goes in `*Lemmas` next to that type, not in grab-bag utils.
