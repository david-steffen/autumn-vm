---
name: type-centered-modules
description: >-
  Organize Lean and Elixir modules around a primary type (or small type cluster),
  with a carve-out for cross-type pipelines. Use when creating, splitting, or
  refactoring modules; deciding where a function belongs; or when the user asks
  about module organization, file layout, or “where should this go.”
---

# Type-centered modules

## Rules

1. **One primary type (or tightly coupled cluster) per module.** Put constructors, accessors, pretty-printing, equality, and type-local well-formedness helpers with that type.
2. **Cross-type transformations get their own module**, named for the relation or process (`Decode`, `Encode`, `Step`), not stuffed into one operand type.
3. **No Utils / Helpers grab-bags.** If a function has a clear primary type, put it there. Proof-only material goes in `TypeLemmas` (e.g. `HeapLemmas`, `StepLemmas`).

## Good (type-owned)

`Term` lives with its operations in `vm/Autumn/Term.lean`:

```lean
inductive Term where
  | nil | bool (b : Bool) | int (n : Int) | ...

namespace Term
def toString : Term → String := ...
partial def beq : Term → Term → Bool := ...
end Term
```

Same idea: `Heap` + heap ops in `Heap.lean`; `Process` GC/alloc in `Process.lean`; `Instr` / `Function` / `Module` as one IR cluster in `Instr.lean`; Elixir `AutumnCompiler.Lower` owns lowering state and emit helpers.

## Good (pipeline-owned)

Keep separate when the work crosses types:

| Module | Why |
| --- | --- |
| `Decode` / `Encode` | JSON ↔ `Module` / `Term` |
| `Step` | execute `Instr` against `State` / `Heap` / `Term` |
| `*Lemmas` | proofs about a type or relation, not runtime API |

Do **not** move `step` into `Instr.lean` or JSON parsing into `Term.lean`.

## Bad

```lean
-- Utils.lean — unclear owner, grows forever
def termToString ...
def decodeInstr ...
def heapAlloc ...
```

Instead: `Term.toString`, `Decode.*`, `Heap.alloc` (or equivalent names in the owning module).

## When to split

Soft thresholds (Autumn Lean; same spirit for Elixir):

- **~800–1000 lines** → consider a split.
- **Sooner** if the file mixes ownership (e.g. `Process` proofs living in `HeapLemmas`).
- Split on **type / pipeline seams**, not arbitrary line chunks. Prefer several focused modules over one mega-file with section comments only.

### Runtime ↔ lemmas pairing

| Runtime | Proofs |
| --- | --- |
| `Heap.lean` | `HeapLemmas.lean` |
| `Process.lean` | `ProcessLemmas.lean` |
| `State.lean` (scheduler / links) | `StateProcessLemmas` / `StateSchedLemmas` / `StateLinkLemmas` |
| `Step.lean` | `StepProgress` / `StepPreserve` / thin `StepLemmas` barrel |

Do not park Process GC lemmas in `HeapLemmas` or Step preservation in a grab-bag utils file.

### Barrel re-exports

When a concern splits into satellites, keep a **thin barrel** so existing imports stay stable:

- `StateLemmas.lean` imports `StateProcessLemmas`, `StateSchedLemmas`, `StateLinkLemmas`
- `StepLemmas.lean` imports `StepProgress`, `StepPreserve` (+ fixture theorems)

Downstream (`Main`, other lemmas) should prefer the barrel unless they need only one satellite.

### Import DAG (State / Process)

Avoid `State` ↔ `Process` cycles:

```
StateTypes  →  Process  →  State (ops)
```

- `StateTypes.lean` — `Frame` / `Handler` / `Process` / `State` / `StepError`
- `Process.lean` — Process GC + alloc (imports `StateTypes`)
- `State.lean` — scheduler / links / EXIT (imports `StateTypes` + `Process`)

Lake auto-discovers new files under `vm/Autumn/`; no `lakefile.lean` edits for new modules.

## Checklist when adding code

- [ ] Does this function have a primary type? → that type’s module / namespace
- [ ] Does it transform between representations or drive a machine? → pipeline module
- [ ] Would it only exist for proofs? → matching `*Lemmas` (paired with runtime owner)
- [ ] Would a new “utils” file be the only home? → stop; pick an owner above
- [ ] Is the module past ~1k lines or mixing types? → split on an ownership seam; use a barrel if imports must stay stable
