# Autumn IR

Versioned bytecode exchanged as JSON between the Mix lowerer and the Lean VM.

Supported `version` values: `1` (literals/calls) and `2` (lists, case ops, processes).

## Module

```json
{
  "version": 2,
  "entry": "Main.main/0",
  "functions": [ /* Function */ ]
}
```

## Function

```json
{
  "name": "Main.add/2",
  "arity": 2,
  "locals": 3,
  "code": [ /* Instr */ ]
}
```

Registers: dense `r0 .. r(locals-1)`. Params occupy `r0 .. r(arity-1)`.

## Literals

| JSON | Term |
| --- | --- |
| `null` | `nil` |
| `{"bool": true}` | boolean |
| `{"int": 42}` | integer |
| `{"atom": "ok"}` | atom |
| `{"tuple": [lit, ...]}` | tuple |
| `{"list": [lit, ...]}` | list (v2) |
| `{"pid": 0}` | process id (v2, usually runtime-only) |

## Instructions

### v1

- `{"op":"load_lit","reg":0,"lit":...}`
- `{"op":"move","dest":1,"src":0}`
- `{"op":"call","dest":2,"fun":"Main.add/2","args":[0,1]}`
- `{"op":"return","reg":2}`
- `{"op":"halt","reg":0}`

### v2 sequential

- `{"op":"jump","target":12}` — absolute instruction index
- `{"op":"jump_if_eq","target":12,"reg":0,"lit":...}` — jump if reg equals lit
- `{"op":"get_tuple_elem","dest":1,"tuple":0,"index":0}`
- `{"op":"is_tag","dest":1,"reg":0,"tag":"tuple"}` — tag ∈ nil\|bool\|int\|atom\|tuple\|list\|pid

### v2 processes

- `{"op":"spawn","dest":0,"fun":"Main.worker/1","args":[1]}` — dest ← pid
- `{"op":"send","pid":0,"msg":1}`
- `{"op":"recv","dest":0}` — pop mailbox or park until message

## Builtins

| MFA | Meaning |
| --- | --- |
| `+/2` `-/2` `*/2` | integer arithmetic |
| `==/2` | structural equality → bool |
| `tuple_size/1` | tuple length → int |
| `elem/2` | `(tuple, index)` → element (0-based) |

## Scheduling

Cooperative: each process runs a small reduction budget then yields. `recv` on an empty mailbox parks the process (`waiting`); `send` wakes a waiting target. Machine result is the **entry process** return/halt value.

## Runtime heap (Lean VM)

Compound terms (`tuple` / `list`) are **heap-allocated** at runtime; immediates (`nil` / `bool` / `int` / `atom` / `pid`) stay unboxed in registers.

- Each process owns a **generational heap**: a single `nodes` array laid out `old ++ young`. Refs `< oldSize` are old; the rest are the young **nursery**. Allocation bump-fills young only, up to `youngCapacity` (and total `capacity`).
- **Minor GC** (nursery full): evacuate only young objects reachable from the process roots (stack registers, mailbox, result) and **promote every survivor into old** (no aging; one minor survived ⇒ old). Old refs are leaves and the old prefix is kept verbatim, so old refs stay valid. Young is empty afterwards (`minorCount += 1`).
- **Major GC** (after a minor, if old can no longer hold a full nursery — `nodes.size + youngCapacity > capacity` — or young is still full): full-heap **Cheney** copy over old+young; the result is entirely old (`gcCount += 1`) and `capacity` is grown for headroom.
- **No remembered set**: heap nodes are immutable and children are always allocated before parents, so an old object can never point at a young one; roots plus tracing through young are sufficient.
- Allocation failure path (`allocNode` / `allocCompound`): `alloc?` → `gc` (minor, then major if needed) → `alloc?` → `growAlloc` (grow capacity/nursery, force-alloc).
- Registers, mailboxes, and process results hold `Value`s (immediate or `Ref`).
- **Nested compound allocation is GC-safe**: while building a `tuple`/`list` literal, already-built children are parked on the process mailbox (a GC root), and the parent node is rebuilt from the live (post-GC) mailbox suffix. A GC triggered mid-term therefore never leaves stale refs. `installHeap` never inflates `capacity`/`youngCapacity`, so a full nursery still triggers GC. `GCDemo` forces minor and major collections on tiny heaps (including retained roots filling old) and checks `toTerm` round-trips.
- Both collections share one root-rewriting pass (`collectWith`) and satisfy `GcRel` (`minorGc_rel`, `majorGc_rel`, `gc_rel`): they preserve immediates in registers/mailbox/result exactly (`{minor_gc,majorGc,gc}_frame_reg_immediate`, `*_mailbox_immediate`, `*_result_immediate`), process well-formedness (`minor_gc_preserves_process_WF`, `majorGc_preserves_process_WF`, `gc_preserves_process_WF`), and keep all root refs well-formed (`*_rootsWF` / `*_preserves_obs`). `toTerm` is `partial`, so full compound preservation is checked by `GCDemo` rather than proved.
- **`send` / `spawn` copy** values into the target process heap (no cross-heap refs).
- IR JSON is unchanged: the Mix lowerer still emits term trees; the VM allocates them on `load_lit` / spawn args.
