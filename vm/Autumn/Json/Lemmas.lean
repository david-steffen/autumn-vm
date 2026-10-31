import Autumn.Json.Encode
import Autumn.Json.Decode
import Autumn.WellFormed
import Std.Data.TreeMap.Raw.Lemmas
import Std.Data.TreeMap.Raw.WF
import Init.Data.Order.LemmasExtra

/-!
# Encode ↔ Decode roundtrip

JSON is the Mix ↔ Lean contract. Tags are unconditional; literals exclude `.float`
anywhere in the term tree (`Term.FloatFree`). Compound lits, instructions, and the
`modules[]` module image all roundtrip under the stated hypotheses.
-/

open Lean Std

namespace Autumn

theorem decodeTag_encodeTag (t : Tag) :
    Json.Decode.decodeTag (Json.Encode.encodeTag t) = .ok t := by
  cases t <;> rfl

/-- No `.float` anywhere in the term tree (avoids `JsonNumber.fromFloat?` collapse). -/
def Term.FloatFree : Term → Prop
  | .float _ => False
  | .nil | .bool _ | .int _ | .atom _ | .string _ | .pid _ | .reference _ => True
  | .tuple es | .list es => ∀ e ∈ es, Term.FloatFree e
  | .map es => ∀ kv ∈ es, Term.FloatFree kv.1 ∧ Term.FloatFree kv.2
  | .closure _ env => ∀ e ∈ env, Term.FloatFree e
termination_by t => sizeOf t
decreasing_by
  all_goals (
    simp_wf
    have hmem := Array.sizeOf_lt_of_mem ‹_›
    first
    | omega
    | (have hsize : sizeOf (‹Term × Term› : Term × Term) =
          1 + sizeOf (‹Term × Term›).1 + sizeOf (‹Term × Term›).2 := rfl
       omega)
  )

def Instr.FloatFree : Instr → Prop
  | .loadLit _ lit | .jumpIfEq _ _ lit => Term.FloatFree lit
  | _ => True

def Function.FloatFree (f : Function) : Prop :=
  ∀ i, (hi : i < f.code.size) → Instr.FloatFree (f.code[i]'hi)

def CodeModule.FloatFree (cm : CodeModule) : Prop :=
  ∀ i, (hi : i < cm.functions.size) → Function.FloatFree (cm.functions[i]'hi)

/-- Modules whose encoded `modules[]` image has float-free literals. -/
def Module.FloatFree (m : Module) : Prop :=
  ∀ i, (hi : i < m.modules.size) → CodeModule.FloatFree (m.modules[i]'hi)

/-- Nesting depth used as a lower bound on decode fuel. -/
def Term.depth : Term → Nat
  | .nil | .bool _ | .int _ | .float _ | .atom _ | .string _ | .pid _ | .reference _ => 1
  | .tuple es | .list es =>
    1 + es.attach.foldl (fun n ⟨e, _⟩ => Nat.max n (Term.depth e)) 0
  | .map es =>
    1 + es.attach.foldl (fun n ⟨⟨k, v⟩, _⟩ => Nat.max n (Nat.max (Term.depth k) (Term.depth v))) 0
  | .closure _ env =>
    1 + env.attach.foldl (fun n ⟨e, _⟩ => Nat.max n (Term.depth e)) 0
termination_by t => sizeOf t
decreasing_by
  all_goals (
    simp_wf
    have hmem := Array.sizeOf_lt_of_mem ‹_›
    · first | omega |
        (have hkv : sizeOf (k, v) = 1 + sizeOf k + sizeOf v := rfl; omega)
  )

/-- Embedded literal nesting fits the public `decodeLit` fuel budget. -/
def Instr.LitFuelOk : Instr → Prop
  | .loadLit _ lit | .jumpIfEq _ _ lit => Term.depth lit ≤ 100000
  | _ => True

def Function.LitFuelOk (f : Function) : Prop :=
  ∀ i, (hi : i < f.code.size) → Instr.LitFuelOk (f.code[i]'hi)

def CodeModule.LitFuelOk (cm : CodeModule) : Prop :=
  ∀ i, (hi : i < cm.functions.size) → Function.LitFuelOk (cm.functions[i]'hi)

def Module.LitFuelOk (m : Module) : Prop :=
  ∀ i, (hi : i < m.modules.size) → CodeModule.LitFuelOk (m.modules[i]'hi)

/-- Encode→decode requires `locals ≥ arity` (decode rejects otherwise). -/
def Function.LocalsOk (f : Function) : Prop :=
  f.arity ≤ f.locals

def CodeModule.LocalsOk (cm : CodeModule) : Prop :=
  ∀ i, (hi : i < cm.functions.size) → Function.LocalsOk (cm.functions[i]'hi)

def Module.LocalsOk (m : Module) : Prop :=
  ∀ i, (hi : i < m.modules.size) → CodeModule.LocalsOk (m.modules[i]'hi)

namespace Json

theorem isNull_mkObj (fields : List (String × Json)) :
    Json.isNull (Json.mkObj fields) = false := rfl

theorem getObjVal?_singleton (k : String) (v : Json) :
    (Json.mkObj [(k, v)]).getObjVal? k = .ok v := by
  simp only [Json.mkObj, Json.getObjVal?, Std.TreeMap.Raw.ofList_singleton]
  have hget : ((∅ : Std.TreeMap.Raw String Json compare).insert k v).get? k = some v :=
    Std.TreeMap.Raw.getElem?_insert_self Std.TreeMap.Raw.WF.emptyc (k := k) (v := v)
  change (match ((∅ : Std.TreeMap.Raw String Json compare).insert k v).get? k with
    | some val => Except.ok (ε := String) val
    | none => Except.error _) = Except.ok (ε := String) v
  rw [hget]

theorem getObjVal?_singleton_ne (k k' : String) (v : Json) (hne : k ≠ k') :
    (Json.mkObj [(k, v)]).getObjVal? k' =
      .error s!"property not found: {k'}" := by
  simp only [Json.mkObj, Json.getObjVal?]
  have hlist : ([(k, v)].map Prod.fst).contains k' = false := by
    simpa [List.contains_cons, List.contains_nil] using Ne.symm hne
  have hget :
      (Std.TreeMap.Raw.ofList [(k, v)] compare)[k']? = none :=
    Std.TreeMap.Raw.getElem?_ofList_of_contains_eq_false hlist
  change (match (Std.TreeMap.Raw.ofList [(k, v)] compare).get? k' with
    | some val => Except.ok (ε := String) val
    | none => Except.error _) = Except.error _
  rw [show (Std.TreeMap.Raw.ofList [(k, v)] compare).get? k' =
      (Std.TreeMap.Raw.ofList [(k, v)] compare)[k']? from rfl, hget]

/-- Lookup succeeds for a distinct-key `mkObj` field list. -/
theorem getObjVal?_of_mem (fields : List (String × Json)) (k : String) (v : Json)
    (hmem : (k, v) ∈ fields)
    (hdistinct : fields.Pairwise (fun a b => a.1 ≠ b.1)) :
    (Json.mkObj fields).getObjVal? k = .ok v := by
  simp only [Json.mkObj, Json.getObjVal?]
  have hget : (Std.TreeMap.Raw.ofList fields compare)[k]? = some v :=
    Std.TreeMap.Raw.getElem?_ofList_of_mem
      (k := k) (k' := k) (v := v)
      (k_eq := (compare_eq_iff_eq (a := k) (b := k)).mpr rfl)
      (distinct := by
        refine List.Pairwise.imp ?_ hdistinct
        intro a b hne hcmp
        exact hne (compare_eq_iff_eq.mp hcmp))
      hmem
  change (match (Std.TreeMap.Raw.ofList fields compare).get? k with
    | some val => Except.ok (ε := String) val
    | none => Except.error _) = Except.ok (ε := String) v
  rw [show (Std.TreeMap.Raw.ofList fields compare).get? k =
      (Std.TreeMap.Raw.ofList fields compare)[k]? from rfl, hget]

theorem getObjVal?_of_not_mem (fields : List (String × Json)) (k : String)
    (h : (fields.map Prod.fst).contains k = false) :
    (Json.mkObj fields).getObjVal? k = .error s!"property not found: {k}" := by
  simp only [Json.mkObj, Json.getObjVal?]
  have hget : (Std.TreeMap.Raw.ofList fields compare)[k]? = none :=
    Std.TreeMap.Raw.getElem?_ofList_of_contains_eq_false h
  change (match (Std.TreeMap.Raw.ofList fields compare).get? k with
    | some val => Except.ok (ε := String) val
    | none => Except.error _) = Except.error _
  rw [show (Std.TreeMap.Raw.ofList fields compare).get? k =
      (Std.TreeMap.Raw.ofList fields compare)[k]? from rfl, hget]

theorem asBool_coe (b : Bool) : Decode.asBool (b : Json) = .ok b := rfl
theorem asInt_num (n : Int) : Decode.asInt (Json.num n) = .ok n := rfl
theorem asNat_coe (n : Nat) : Decode.asNat (n : Json) = .ok n := rfl
theorem asString_coe (s : String) : Decode.asString (s : Json) = .ok s := rfl
theorem asArray_arr (a : Array Json) : Decode.asArray (Json.arr a) = .ok a := rfl

theorem field_eq_ok (j : Json) (k : String) (v : Json)
    (h : j.getObjVal? k = .ok v) :
    Decode.field j k = .ok v := by
  simp only [Decode.field]
  rw [h]
  rfl

theorem List.mapM_ok_of_forall_mem {ε α} (f : α → Except ε α) (l : List α)
    (h : ∀ x ∈ l, f x = .ok x) : l.mapM f = .ok l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [h x (List.mem_cons_self), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem Array.mapM_ok_of_forall_mem {ε α} (f : α → Except ε α) (xs : Array α)
    (h : ∀ x ∈ xs, f x = .ok x) : xs.mapM f = .ok xs := by
  rw [Array.mapM_eq_mapM_toList]
  have : xs.toList.mapM f = .ok xs.toList :=
    List.mapM_ok_of_forall_mem f xs.toList (fun x hx => h x (Array.mem_toList_iff.mp hx))
  simp [this, Functor.map, Except.map]

theorem List.le_foldl_max_of_mem (l : List Nat) (n : Nat) (hn : n ∈ l) :
    n ≤ l.foldl Nat.max 0 := by
  match l, hn with
  | [], h => cases h
  | x :: xs, h =>
    have hl : x :: xs ≠ [] := by simp
    have hfoldl : (x :: xs).foldl Nat.max 0 = (x :: xs).max hl := by
      simp only [List.foldl_cons, Nat.zero_max]
      rfl
    rw [hfoldl]
    exact List.le_max_of_mem h

theorem depth_le_of_mem_elems (es : Array Term) (e : Term) (he : e ∈ es) :
    Term.depth e ≤ es.attach.foldl (fun n ⟨x, _⟩ => Nat.max n (Term.depth x)) 0 := by
  have hmem : (⟨e, he⟩ : { x // x ∈ es }) ∈ es.attach := Array.mem_attach es ⟨e, he⟩
  have heq :
      es.attach.foldl (fun n ⟨x, _⟩ => Nat.max n (Term.depth x)) 0 =
        (es.attach.toList.map fun ⟨x, _⟩ => Term.depth x).foldl Nat.max 0 := by
    rw [← Array.foldl_toList, List.foldl_map]
  rw [heq]
  have : Term.depth e ∈ es.attach.toList.map fun ⟨x, _⟩ => Term.depth x := by
    refine List.mem_map.mpr ?_
    exact ⟨⟨e, he⟩, Array.mem_toList_iff.mpr hmem, rfl⟩
  exact List.le_foldl_max_of_mem _ _ this

theorem depth_tuple_eq (es : Array Term) :
    Term.depth (.tuple es) =
      1 + es.attach.foldl (fun n ⟨e, _⟩ => Nat.max n (Term.depth e)) 0 := by
  simp [Term.depth]

theorem depth_list_eq (es : Array Term) :
    Term.depth (.list es) =
      1 + es.attach.foldl (fun n ⟨e, _⟩ => Nat.max n (Term.depth e)) 0 := by
  simp [Term.depth]

theorem depth_map_eq (es : Array (Term × Term)) :
    Term.depth (.map es) =
      1 + es.attach.foldl (fun n ⟨⟨k, v⟩, _⟩ => Nat.max n (Nat.max (Term.depth k) (Term.depth v))) 0 := by
  simp [Term.depth]

theorem depth_closure_eq (funName : String) (env : Array Term) :
    Term.depth (.closure funName env) =
      1 + env.attach.foldl (fun n ⟨e, _⟩ => Nat.max n (Term.depth e)) 0 := by
  simp [Term.depth]

theorem depth_le_of_mem_map_key (es : Array (Term × Term)) (k v : Term)
    (he : (k, v) ∈ es) :
    Term.depth k ≤
      es.attach.foldl (fun n ⟨⟨k', v'⟩, _⟩ => Nat.max n (Nat.max (Term.depth k') (Term.depth v'))) 0 := by
  have hmem : (⟨(k, v), he⟩ : { x // x ∈ es }) ∈ es.attach := Array.mem_attach es _
  have heq :
      es.attach.foldl (fun n ⟨⟨k', v'⟩, _⟩ => Nat.max n (Nat.max (Term.depth k') (Term.depth v'))) 0 =
        (es.attach.toList.map fun ⟨⟨k', v'⟩, _⟩ => Nat.max (Term.depth k') (Term.depth v')).foldl Nat.max 0 := by
    rw [← Array.foldl_toList, List.foldl_map]
  rw [heq]
  have hkv : Nat.max (Term.depth k) (Term.depth v) ∈
      es.attach.toList.map fun ⟨⟨k', v'⟩, _⟩ => Nat.max (Term.depth k') (Term.depth v') := by
    refine List.mem_map.mpr ?_
    exact ⟨⟨(k, v), he⟩, Array.mem_toList_iff.mpr hmem, rfl⟩
  exact Nat.le_trans (Nat.le_max_left _ _) (List.le_foldl_max_of_mem _ _ hkv)

theorem depth_le_of_mem_map_val (es : Array (Term × Term)) (k v : Term)
    (he : (k, v) ∈ es) :
    Term.depth v ≤
      es.attach.foldl (fun n ⟨⟨k', v'⟩, _⟩ => Nat.max n (Nat.max (Term.depth k') (Term.depth v'))) 0 := by
  have hmem : (⟨(k, v), he⟩ : { x // x ∈ es }) ∈ es.attach := Array.mem_attach es _
  have heq :
      es.attach.foldl (fun n ⟨⟨k', v'⟩, _⟩ => Nat.max n (Nat.max (Term.depth k') (Term.depth v'))) 0 =
        (es.attach.toList.map fun ⟨⟨k', v'⟩, _⟩ => Nat.max (Term.depth k') (Term.depth v')).foldl Nat.max 0 := by
    rw [← Array.foldl_toList, List.foldl_map]
  rw [heq]
  have hkv : Nat.max (Term.depth k) (Term.depth v) ∈
      es.attach.toList.map fun ⟨⟨k', v'⟩, _⟩ => Nat.max (Term.depth k') (Term.depth v') := by
    refine List.mem_map.mpr ?_
    exact ⟨⟨(k, v), he⟩, Array.mem_toList_iff.mpr hmem, rfl⟩
  exact Nat.le_trans (Nat.le_max_right _ _) (List.le_foldl_max_of_mem _ _ hkv)

/-- If every element roundtrips under `fuel`, so does `mapM decode ∘ map encode`. -/
theorem mapM_decodeLitWithFuel_encodeLit (fuel : Nat) (es : Array Term)
    (hround : ∀ e ∈ es, Decode.decodeLitWithFuel fuel (Encode.encodeLit e) = .ok e) :
    (es.map Encode.encodeLit).mapM (Decode.decodeLitWithFuel fuel) = .ok es := by
  rw [Array.mapM_map]
  exact Array.mapM_ok_of_forall_mem _ _ hround

theorem attach_map_encodeLit (es : Array Term) :
    (es.attach.map fun ⟨e, _⟩ => Encode.encodeLit e) = es.map Encode.encodeLit :=
  Array.attach_map_val es Encode.encodeLit

theorem attach_map_encodeMapEntry (entries : Array (Term × Term)) :
    (entries.attach.map fun ⟨⟨k, v⟩, _⟩ =>
        Json.mkObj [("key", Encode.encodeLit k), ("value", Encode.encodeLit v)]) =
      entries.map fun (p : Term × Term) =>
        Json.mkObj [("key", Encode.encodeLit p.1), ("value", Encode.encodeLit p.2)] :=
  Array.attach_map_val entries fun (p : Term × Term) =>
    Json.mkObj [("key", Encode.encodeLit p.1), ("value", Encode.encodeLit p.2)]

/-- Decode of an encoded map entry object recovers the pair when keys/values roundtrip. -/
theorem decodeMapEntry_encode (fuel : Nat) (k v : Term)
    (hk : Decode.decodeLitWithFuel fuel (Encode.encodeLit k) = .ok k)
    (hv : Decode.decodeLitWithFuel fuel (Encode.encodeLit v) = .ok v) :
    (do
      let e := Json.mkObj [("key", Encode.encodeLit k), ("value", Encode.encodeLit v)]
      let k' ← Decode.decodeLitWithFuel fuel (← Decode.field e "key")
      let val ← Decode.decodeLitWithFuel fuel (← Decode.field e "value")
      pure (k', val)) = Except.ok (k, v) := by
  have hkey := getObjVal?_of_mem [("key", Encode.encodeLit k), ("value", Encode.encodeLit v)]
    "key" (Encode.encodeLit k) (by simp) (by simp [List.pairwise_cons])
  have hval := getObjVal?_of_mem [("key", Encode.encodeLit k), ("value", Encode.encodeLit v)]
    "value" (Encode.encodeLit v) (by simp) (by simp [List.pairwise_cons])
  simp [Decode.field, hkey, hval, hk, hv, Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem decodeLitWithFuel_singleton_bool (fuel : Nat) (b : Bool) (hfuel : 1 ≤ fuel) :
    Decode.decodeLitWithFuel fuel (Encode.encodeLit (.bool b)) = .ok (.bool b) := by
  match fuel with
  | 0 => omega
  | fuel + 1 =>
    rw [Encode.encodeLit]
    unfold Decode.decodeLitWithFuel
    rw [getObjVal?_singleton]
    simp [isNull_mkObj, asBool_coe, Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem decodeLitWithFuel_singleton_nil (fuel : Nat) (hfuel : 1 ≤ fuel) :
    Decode.decodeLitWithFuel fuel (Encode.encodeLit .nil) = .ok .nil := by
  match fuel with
  | 0 => omega
  | fuel + 1 =>
    rw [Encode.encodeLit]
    unfold Decode.decodeLitWithFuel
    rfl

theorem decodeLitWithFuel_singleton_int (fuel : Nat) (n : Int) (hfuel : 1 ≤ fuel) :
    Decode.decodeLitWithFuel fuel (Encode.encodeLit (.int n)) = .ok (.int n) := by
  match fuel with
  | 0 => omega
  | fuel + 1 =>
    rw [Encode.encodeLit]
    unfold Decode.decodeLitWithFuel
    have hbool := getObjVal?_singleton_ne "int" "bool" (Json.num n) (by decide)
    have hint := getObjVal?_singleton "int" (Json.num n)
    simp [isNull_mkObj, hbool, hint, asInt_num, Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem decodeLitWithFuel_singleton_atom (fuel : Nat) (s : String) (hfuel : 1 ≤ fuel) :
    Decode.decodeLitWithFuel fuel (Encode.encodeLit (.atom s)) = .ok (.atom s) := by
  match fuel with
  | 0 => omega
  | fuel + 1 =>
    rw [Encode.encodeLit]
    unfold Decode.decodeLitWithFuel
    have hbool := getObjVal?_singleton_ne "atom" "bool" (s : Json) (by decide)
    have hint := getObjVal?_singleton_ne "atom" "int" (s : Json) (by decide)
    have hatom := getObjVal?_singleton "atom" (s : Json)
    simp [isNull_mkObj, hbool, hint, hatom, asString_coe, Bind.bind, Pure.pure,
      Except.bind, Except.pure]

theorem decodeLitWithFuel_singleton_string (fuel : Nat) (s : String) (hfuel : 1 ≤ fuel) :
    Decode.decodeLitWithFuel fuel (Encode.encodeLit (.string s)) = .ok (.string s) := by
  match fuel with
  | 0 => omega
  | fuel + 1 =>
    rw [Encode.encodeLit]
    unfold Decode.decodeLitWithFuel
    have hbool := getObjVal?_singleton_ne "string" "bool" (s : Json) (by decide)
    have hint := getObjVal?_singleton_ne "string" "int" (s : Json) (by decide)
    have hatom := getObjVal?_singleton_ne "string" "atom" (s : Json) (by decide)
    have htuple := getObjVal?_singleton_ne "string" "tuple" (s : Json) (by decide)
    have hlist := getObjVal?_singleton_ne "string" "list" (s : Json) (by decide)
    have hmap := getObjVal?_singleton_ne "string" "map" (s : Json) (by decide)
    have hpid := getObjVal?_singleton_ne "string" "pid" (s : Json) (by decide)
    have href := getObjVal?_singleton_ne "string" "ref" (s : Json) (by decide)
    have hfloat := getObjVal?_singleton_ne "string" "float" (s : Json) (by decide)
    have hstr := getObjVal?_singleton "string" (s : Json)
    simp [isNull_mkObj, hbool, hint, hatom, htuple, hlist, hmap, hpid, href, hfloat, hstr,
      asString_coe, Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem decodeLitWithFuel_singleton_pid (fuel : Nat) (id : Nat) (hfuel : 1 ≤ fuel) :
    Decode.decodeLitWithFuel fuel (Encode.encodeLit (.pid id)) = .ok (.pid id) := by
  match fuel with
  | 0 => omega
  | fuel + 1 =>
    rw [Encode.encodeLit]
    unfold Decode.decodeLitWithFuel
    have hbool := getObjVal?_singleton_ne "pid" "bool" (id : Json) (by decide)
    have hint := getObjVal?_singleton_ne "pid" "int" (id : Json) (by decide)
    have hatom := getObjVal?_singleton_ne "pid" "atom" (id : Json) (by decide)
    have htuple := getObjVal?_singleton_ne "pid" "tuple" (id : Json) (by decide)
    have hlist := getObjVal?_singleton_ne "pid" "list" (id : Json) (by decide)
    have hmap := getObjVal?_singleton_ne "pid" "map" (id : Json) (by decide)
    have hpid := getObjVal?_singleton "pid" (id : Json)
    simp [isNull_mkObj, hbool, hint, hatom, htuple, hlist, hmap, hpid,
      asNat_coe, Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem decodeLitWithFuel_singleton_ref (fuel : Nat) (id : Nat) (hfuel : 1 ≤ fuel) :
    Decode.decodeLitWithFuel fuel (Encode.encodeLit (.reference id)) = .ok (.reference id) := by
  match fuel with
  | 0 => omega
  | fuel + 1 =>
    rw [Encode.encodeLit]
    unfold Decode.decodeLitWithFuel
    have hbool := getObjVal?_singleton_ne "ref" "bool" (id : Json) (by decide)
    have hint := getObjVal?_singleton_ne "ref" "int" (id : Json) (by decide)
    have hatom := getObjVal?_singleton_ne "ref" "atom" (id : Json) (by decide)
    have htuple := getObjVal?_singleton_ne "ref" "tuple" (id : Json) (by decide)
    have hlist := getObjVal?_singleton_ne "ref" "list" (id : Json) (by decide)
    have hmap := getObjVal?_singleton_ne "ref" "map" (id : Json) (by decide)
    have hpid := getObjVal?_singleton_ne "ref" "pid" (id : Json) (by decide)
    have href := getObjVal?_singleton "ref" (id : Json)
    simp [isNull_mkObj, hbool, hint, hatom, htuple, hlist, hmap, hpid, href,
      asNat_coe, Bind.bind, Pure.pure, Except.bind, Except.pure]

/-- Fuel-aware roundtrip for float-free literals. -/
theorem decodeLitWithFuel_encodeLit (fuel : Nat) (t : Term) (ht : Term.FloatFree t)
    (hfuel : Term.depth t ≤ fuel) :
    Decode.decodeLitWithFuel fuel (Encode.encodeLit t) = .ok t := by
  revert fuel ht hfuel
  refine WellFounded.fix
    (C := fun t => ∀ (fuel : Nat) (ht : Term.FloatFree t) (hfuel : Term.depth t ≤ fuel),
      Decode.decodeLitWithFuel fuel (Encode.encodeLit t) = .ok t)
    (measure (α := Term) sizeOf |>.wf) (fun t ih fuel ht hfuel => ?_) t
  match t with
  | .nil =>
    have : 1 ≤ fuel := by simpa [Term.depth] using hfuel
    exact decodeLitWithFuel_singleton_nil fuel this
  | .bool b =>
    have : 1 ≤ fuel := by simpa [Term.depth] using hfuel
    exact decodeLitWithFuel_singleton_bool fuel b this
  | .int n =>
    have : 1 ≤ fuel := by simpa [Term.depth] using hfuel
    exact decodeLitWithFuel_singleton_int fuel n this
  | .float _ =>
    simp [Term.FloatFree] at ht
  | .atom s =>
    have : 1 ≤ fuel := by simpa [Term.depth] using hfuel
    exact decodeLitWithFuel_singleton_atom fuel s this
  | .string s =>
    have : 1 ≤ fuel := by simpa [Term.depth] using hfuel
    exact decodeLitWithFuel_singleton_string fuel s this
  | .pid id =>
    have : 1 ≤ fuel := by simpa [Term.depth] using hfuel
    exact decodeLitWithFuel_singleton_pid fuel id this
  | .reference id =>
    have : 1 ≤ fuel := by simpa [Term.depth] using hfuel
    exact decodeLitWithFuel_singleton_ref fuel id this
  | .tuple elems =>
    match fuel with
    | 0 =>
      have hge : 1 ≤ Term.depth (.tuple elems) := by simp [depth_tuple_eq]
      omega
    | fuel + 1 =>
      simp only [Term.FloatFree] at ht
      have hsub : ∀ e ∈ elems, Term.depth e ≤ fuel := by
        intro e he
        have hle := depth_le_of_mem_elems elems e he
        have heq := depth_tuple_eq elems
        omega
      have hround : ∀ e ∈ elems,
          Decode.decodeLitWithFuel fuel (Encode.encodeLit e) = .ok e := by
        intro e he
        refine ih e ?_ fuel (ht e he) (hsub e he)
        change sizeOf e < sizeOf (Term.tuple elems)
        have hmem := Array.sizeOf_lt_of_mem he
        rw [Term.tuple.sizeOf_spec]
        omega
      rw [Encode.encodeLit, attach_map_encodeLit]
      unfold Decode.decodeLitWithFuel
      have hbool := getObjVal?_singleton_ne "tuple" "bool"
        (Json.arr (elems.map Encode.encodeLit)) (by decide)
      have hint := getObjVal?_singleton_ne "tuple" "int"
        (Json.arr (elems.map Encode.encodeLit)) (by decide)
      have hatom := getObjVal?_singleton_ne "tuple" "atom"
        (Json.arr (elems.map Encode.encodeLit)) (by decide)
      have htuple := getObjVal?_singleton "tuple" (Json.arr (elems.map Encode.encodeLit))
      have hdone := mapM_decodeLitWithFuel_encodeLit fuel elems hround
      simp [isNull_mkObj, hbool, hint, hatom, htuple, asArray_arr,
        Bind.bind, Pure.pure, Except.bind, Except.pure, hdone]
  | .list elems =>
    match fuel with
    | 0 =>
      have hge : 1 ≤ Term.depth (.list elems) := by simp [depth_list_eq]
      omega
    | fuel + 1 =>
      simp only [Term.FloatFree] at ht
      have hsub : ∀ e ∈ elems, Term.depth e ≤ fuel := by
        intro e he
        have hle := depth_le_of_mem_elems elems e he
        have heq := depth_list_eq elems
        omega
      have hround : ∀ e ∈ elems,
          Decode.decodeLitWithFuel fuel (Encode.encodeLit e) = .ok e := by
        intro e he
        refine ih e ?_ fuel (ht e he) (hsub e he)
        change sizeOf e < sizeOf (Term.list elems)
        have hmem := Array.sizeOf_lt_of_mem he
        rw [Term.list.sizeOf_spec]
        omega
      rw [Encode.encodeLit, attach_map_encodeLit]
      unfold Decode.decodeLitWithFuel
      have hbool := getObjVal?_singleton_ne "list" "bool"
        (Json.arr (elems.map Encode.encodeLit)) (by decide)
      have hint := getObjVal?_singleton_ne "list" "int"
        (Json.arr (elems.map Encode.encodeLit)) (by decide)
      have hatom := getObjVal?_singleton_ne "list" "atom"
        (Json.arr (elems.map Encode.encodeLit)) (by decide)
      have htuple := getObjVal?_singleton_ne "list" "tuple"
        (Json.arr (elems.map Encode.encodeLit)) (by decide)
      have hlist := getObjVal?_singleton "list" (Json.arr (elems.map Encode.encodeLit))
      have hdone := mapM_decodeLitWithFuel_encodeLit fuel elems hround
      simp [isNull_mkObj, hbool, hint, hatom, htuple, hlist, asArray_arr,
        Bind.bind, Pure.pure, Except.bind, Except.pure, hdone]
  | .map entries =>
    match fuel with
    | 0 =>
      have hge : 1 ≤ Term.depth (.map entries) := by simp [depth_map_eq]
      omega
    | fuel + 1 =>
      simp only [Term.FloatFree] at ht
      have hsubk : ∀ kv ∈ entries, Term.depth kv.1 ≤ fuel := by
        intro kv he
        have hle := depth_le_of_mem_map_key entries kv.1 kv.2 he
        have heq := depth_map_eq entries
        omega
      have hsubv : ∀ kv ∈ entries, Term.depth kv.2 ≤ fuel := by
        intro kv he
        have hle := depth_le_of_mem_map_val entries kv.1 kv.2 he
        have heq := depth_map_eq entries
        omega
      have hsize_key (kv : Term × Term) (he : kv ∈ entries) :
          sizeOf kv.1 < sizeOf (Term.map entries) := by
        have hmem := Array.sizeOf_lt_of_mem he
        have hkv : sizeOf kv = 1 + sizeOf kv.1 + sizeOf kv.2 := rfl
        rw [Term.map.sizeOf_spec]; omega
      have hsize_val (kv : Term × Term) (he : kv ∈ entries) :
          sizeOf kv.2 < sizeOf (Term.map entries) := by
        have hmem := Array.sizeOf_lt_of_mem he
        have hkv : sizeOf kv = 1 + sizeOf kv.1 + sizeOf kv.2 := rfl
        rw [Term.map.sizeOf_spec]; omega
      have hentry : ∀ kv ∈ entries,
          (do
            let e := Json.mkObj [("key", Encode.encodeLit kv.1), ("value", Encode.encodeLit kv.2)]
            let k' ← Decode.decodeLitWithFuel fuel (← Decode.field e "key")
            let val ← Decode.decodeLitWithFuel fuel (← Decode.field e "value")
            pure (k', val)) = Except.ok kv := by
        intro kv he
        cases kv with
        | mk k v =>
          exact decodeMapEntry_encode fuel k v
            (ih k (hsize_key (k, v) he) fuel (ht (k, v) he).1 (hsubk (k, v) he))
            (ih v (hsize_val (k, v) he) fuel (ht (k, v) he).2 (hsubv (k, v) he))
      rw [Encode.encodeLit, attach_map_encodeMapEntry]
      unfold Decode.decodeLitWithFuel
      let encEntry := fun (x : Term × Term) =>
        Json.mkObj [("key", Encode.encodeLit x.1), ("value", Encode.encodeLit x.2)]
      have hbool := getObjVal?_singleton_ne "map" "bool"
        (Json.arr (entries.map encEntry)) (by decide)
      have hint := getObjVal?_singleton_ne "map" "int"
        (Json.arr (entries.map encEntry)) (by decide)
      have hatom := getObjVal?_singleton_ne "map" "atom"
        (Json.arr (entries.map encEntry)) (by decide)
      have htuple := getObjVal?_singleton_ne "map" "tuple"
        (Json.arr (entries.map encEntry)) (by decide)
      have hlist := getObjVal?_singleton_ne "map" "list"
        (Json.arr (entries.map encEntry)) (by decide)
      have hmap := getObjVal?_singleton "map" (Json.arr (entries.map encEntry))
      simp [isNull_mkObj, encEntry, hbool, hint, hatom, htuple, hlist, hmap, asArray_arr,
        Bind.bind, Pure.pure, Except.bind, Except.pure, Array.mapM_map]
      have hdone :
          entries.mapM
            ((fun e => do
                let k ← Decode.decodeLitWithFuel fuel (← Decode.field e "key")
                let val ← Decode.decodeLitWithFuel fuel (← Decode.field e "value")
                pure (k, val)) ∘
              fun p => Json.mkObj [("key", Encode.encodeLit p.1), ("value", Encode.encodeLit p.2)]) =
            Except.ok entries := by
        refine Array.mapM_ok_of_forall_mem _ _ ?_
        intro kv he
        simpa [Function.comp, Bind.bind, Pure.pure, Except.bind, Except.pure] using hentry kv he
      -- Expand `do` binds so the goal's `match` form matches.
      simp only [Bind.bind, Pure.pure, Except.bind, Except.pure] at hdone
      rw [hdone]
  | .closure funName env =>
    match fuel with
    | 0 =>
      have hge : 1 ≤ Term.depth (.closure funName env) := by simp [depth_closure_eq]
      omega
    | fuel + 1 =>
      simp only [Term.FloatFree] at ht
      have hsub : ∀ e ∈ env, Term.depth e ≤ fuel := by
        intro e he
        have hle := depth_le_of_mem_elems env e he
        have heq := depth_closure_eq funName env
        omega
      have hround : ∀ e ∈ env,
          Decode.decodeLitWithFuel fuel (Encode.encodeLit e) = .ok e := by
        intro e he
        refine ih e ?_ fuel (ht e he) (hsub e he)
        change sizeOf e < sizeOf (Term.closure funName env)
        have hmem := Array.sizeOf_lt_of_mem he
        rw [Term.closure.sizeOf_spec]
        omega
      rw [Encode.encodeLit, attach_map_encodeLit]
      unfold Decode.decodeLitWithFuel
      have hbool := getObjVal?_singleton_ne "closure" "bool"
        (Json.mkObj [("fun", (funName : Json)), ("env", Json.arr (env.map Encode.encodeLit))])
        (by decide)
      have hint := getObjVal?_singleton_ne "closure" "int"
        (Json.mkObj [("fun", (funName : Json)), ("env", Json.arr (env.map Encode.encodeLit))])
        (by decide)
      have hatom := getObjVal?_singleton_ne "closure" "atom"
        (Json.mkObj [("fun", (funName : Json)), ("env", Json.arr (env.map Encode.encodeLit))])
        (by decide)
      have htuple := getObjVal?_singleton_ne "closure" "tuple"
        (Json.mkObj [("fun", (funName : Json)), ("env", Json.arr (env.map Encode.encodeLit))])
        (by decide)
      have hlist := getObjVal?_singleton_ne "closure" "list"
        (Json.mkObj [("fun", (funName : Json)), ("env", Json.arr (env.map Encode.encodeLit))])
        (by decide)
      have hmap := getObjVal?_singleton_ne "closure" "map"
        (Json.mkObj [("fun", (funName : Json)), ("env", Json.arr (env.map Encode.encodeLit))])
        (by decide)
      have hpid := getObjVal?_singleton_ne "closure" "pid"
        (Json.mkObj [("fun", (funName : Json)), ("env", Json.arr (env.map Encode.encodeLit))])
        (by decide)
      have href := getObjVal?_singleton_ne "closure" "ref"
        (Json.mkObj [("fun", (funName : Json)), ("env", Json.arr (env.map Encode.encodeLit))])
        (by decide)
      have hfloat := getObjVal?_singleton_ne "closure" "float"
        (Json.mkObj [("fun", (funName : Json)), ("env", Json.arr (env.map Encode.encodeLit))])
        (by decide)
      have hstr := getObjVal?_singleton_ne "closure" "string"
        (Json.mkObj [("fun", (funName : Json)), ("env", Json.arr (env.map Encode.encodeLit))])
        (by decide)
      have hclos := getObjVal?_singleton "closure"
        (Json.mkObj [("fun", (funName : Json)), ("env", Json.arr (env.map Encode.encodeLit))])
      have hfun := getObjVal?_of_mem
        [("fun", (funName : Json)), ("env", Json.arr (env.map Encode.encodeLit))]
        "fun" (funName : Json) (by simp) (by simp [List.pairwise_cons])
      have henv := getObjVal?_of_mem
        [("fun", (funName : Json)), ("env", Json.arr (env.map Encode.encodeLit))]
        "env" (Json.arr (env.map Encode.encodeLit)) (by simp) (by simp [List.pairwise_cons])
      have hdone := mapM_decodeLitWithFuel_encodeLit fuel env hround
      simp [isNull_mkObj, hbool, hint, hatom, htuple, hlist, hmap, hpid, href, hfloat, hstr,
        hclos, Decode.field, hfun, henv, asString_coe, asArray_arr,
        Bind.bind, Pure.pure, Except.bind, Except.pure, hdone]


theorem mapM_asNat_toJson (args : Array Nat) :
    (args.map (fun a => toJson a)).mapM Decode.asNat = .ok args := by
  rw [Array.mapM_map]
  exact Array.mapM_ok_of_forall_mem _ _ (fun a _ => by
    change Decode.asNat (toJson a) = .ok a
    simp [toJson, asNat_coe])

theorem decodeInstr_encodeInstr (i : Instr) (hi : Instr.FloatFree i)
    (hfuel : Instr.LitFuelOk i) :
    Json.Decode.decodeInstr (Json.Encode.encodeInstr i) = .ok i := by
  cases i with
  | leaveTry =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hop := getObjVal?_singleton "op" ("leave_try" : Json)
    simp [Decode.field, hop, asString_coe, Bind.bind, Pure.pure, Except.bind, Except.pure]
  | return_ r =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("return" : Json)), ("reg", (r : Json))].Pairwise
        (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("return" : Json)), ("reg", (r : Json))]
      "op" ("return" : Json) (by simp) hdist
    have hreg := getObjVal?_of_mem [("op", ("return" : Json)), ("reg", (r : Json))]
      "reg" (r : Json) (by simp) hdist
    simp [Decode.field, hop, hreg, asString_coe, asNat_coe,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | halt r =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("halt" : Json)), ("reg", (r : Json))].Pairwise
        (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("halt" : Json)), ("reg", (r : Json))]
      "op" ("halt" : Json) (by simp) hdist
    have hreg := getObjVal?_of_mem [("op", ("halt" : Json)), ("reg", (r : Json))]
      "reg" (r : Json) (by simp) hdist
    simp [Decode.field, hop, hreg, asString_coe, asNat_coe,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | jump t =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("jump" : Json)), ("target", (t : Json))].Pairwise
        (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("jump" : Json)), ("target", (t : Json))]
      "op" ("jump" : Json) (by simp) hdist
    have htgt := getObjVal?_of_mem [("op", ("jump" : Json)), ("target", (t : Json))]
      "target" (t : Json) (by simp) hdist
    simp [Decode.field, hop, htgt, asString_coe, asNat_coe,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | recv d =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("recv" : Json)), ("dest", (d : Json))].Pairwise
        (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("recv" : Json)), ("dest", (d : Json))]
      "op" ("recv" : Json) (by simp) hdist
    have hdest := getObjVal?_of_mem [("op", ("recv" : Json)), ("dest", (d : Json))]
      "dest" (d : Json) (by simp) hdist
    simp [Decode.field, hop, hdest, asString_coe, asNat_coe,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | recvDrop i =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("recv_drop" : Json)), ("index", (i : Json))].Pairwise
        (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("recv_drop" : Json)), ("index", (i : Json))]
      "op" ("recv_drop" : Json) (by simp) hdist
    have hidx := getObjVal?_of_mem [("op", ("recv_drop" : Json)), ("index", (i : Json))]
      "index" (i : Json) (by simp) hdist
    simp [Decode.field, hop, hidx, asString_coe, asNat_coe,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | raise r =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("raise" : Json)), ("reg", (r : Json))].Pairwise
        (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("raise" : Json)), ("reg", (r : Json))]
      "op" ("raise" : Json) (by simp) hdist
    have hreg := getObjVal?_of_mem [("op", ("raise" : Json)), ("reg", (r : Json))]
      "reg" (r : Json) (by simp) hdist
    simp [Decode.field, hop, hreg, asString_coe, asNat_coe,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | link p =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("link" : Json)), ("pid", (p : Json))].Pairwise
        (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("link" : Json)), ("pid", (p : Json))]
      "op" ("link" : Json) (by simp) hdist
    have hpid := getObjVal?_of_mem [("op", ("link" : Json)), ("pid", (p : Json))]
      "pid" (p : Json) (by simp) hdist
    simp [Decode.field, hop, hpid, asString_coe, asNat_coe,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | demonitor r =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("demonitor" : Json)), ("ref", (r : Json))].Pairwise
        (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("demonitor" : Json)), ("ref", (r : Json))]
      "op" ("demonitor" : Json) (by simp) hdist
    have href := getObjVal?_of_mem [("op", ("demonitor" : Json)), ("ref", (r : Json))]
      "ref" (r : Json) (by simp) hdist
    simp [Decode.field, hop, href, asString_coe, asNat_coe,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | move d s =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("move" : Json)), ("dest", (d : Json)), ("src", (s : Json))].Pairwise
        (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("move" : Json)), ("dest", (d : Json)), ("src", (s : Json))]
      "op" ("move" : Json) (by simp) hdist
    have hdest := getObjVal?_of_mem [("op", ("move" : Json)), ("dest", (d : Json)), ("src", (s : Json))]
      "dest" (d : Json) (by simp) hdist
    have hsrc := getObjVal?_of_mem [("op", ("move" : Json)), ("dest", (d : Json)), ("src", (s : Json))]
      "src" (s : Json) (by simp) hdist
    simp [Decode.field, hop, hdest, hsrc, asString_coe, asNat_coe,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | send p m =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("send" : Json)), ("pid", (p : Json)), ("msg", (m : Json))].Pairwise
        (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("send" : Json)), ("pid", (p : Json)), ("msg", (m : Json))]
      "op" ("send" : Json) (by simp) hdist
    have hpid := getObjVal?_of_mem [("op", ("send" : Json)), ("pid", (p : Json)), ("msg", (m : Json))]
      "pid" (p : Json) (by simp) hdist
    have hmsg := getObjVal?_of_mem [("op", ("send" : Json)), ("pid", (p : Json)), ("msg", (m : Json))]
      "msg" (m : Json) (by simp) hdist
    simp [Decode.field, hop, hpid, hmsg, asString_coe, asNat_coe,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | enterTry rescueIp exc =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("enter_try" : Json)), ("rescue", (rescueIp : Json)), ("exc", (exc : Json))].Pairwise
        (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("enter_try" : Json)), ("rescue", (rescueIp : Json)), ("exc", (exc : Json))]
      "op" ("enter_try" : Json) (by simp) hdist
    have hres := getObjVal?_of_mem [("op", ("enter_try" : Json)), ("rescue", (rescueIp : Json)), ("exc", (exc : Json))]
      "rescue" (rescueIp : Json) (by simp) hdist
    have hexc := getObjVal?_of_mem [("op", ("enter_try" : Json)), ("rescue", (rescueIp : Json)), ("exc", (exc : Json))]
      "exc" (exc : Json) (by simp) hdist
    simp [Decode.field, hop, hres, hexc, asString_coe, asNat_coe,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | monitor d p =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("monitor" : Json)), ("dest", (d : Json)), ("pid", (p : Json))].Pairwise
        (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("monitor" : Json)), ("dest", (d : Json)), ("pid", (p : Json))]
      "op" ("monitor" : Json) (by simp) hdist
    have hdest := getObjVal?_of_mem [("op", ("monitor" : Json)), ("dest", (d : Json)), ("pid", (p : Json))]
      "dest" (d : Json) (by simp) hdist
    have hpid := getObjVal?_of_mem [("op", ("monitor" : Json)), ("dest", (d : Json)), ("pid", (p : Json))]
      "pid" (p : Json) (by simp) hdist
    simp [Decode.field, hop, hdest, hpid, asString_coe, asNat_coe,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | loadFile d p =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("load_file" : Json)), ("dest", (d : Json)), ("path", (p : Json))].Pairwise
        (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("load_file" : Json)), ("dest", (d : Json)), ("path", (p : Json))]
      "op" ("load_file" : Json) (by simp) hdist
    have hdest := getObjVal?_of_mem [("op", ("load_file" : Json)), ("dest", (d : Json)), ("path", (p : Json))]
      "dest" (d : Json) (by simp) hdist
    have hpath := getObjVal?_of_mem [("op", ("load_file" : Json)), ("dest", (d : Json)), ("path", (p : Json))]
      "path" (p : Json) (by simp) hdist
    simp [Decode.field, hop, hdest, hpath, asString_coe, asNat_coe,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | getTupleElem d t i =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("get_tuple_elem" : Json)), ("dest", (d : Json)), ("tuple", (t : Json)),
        ("index", (i : Json))].Pairwise (fun a b : String × Json => a.1 ≠ b.1) := by
      simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("get_tuple_elem" : Json)), ("dest", (d : Json)),
        ("tuple", (t : Json)), ("index", (i : Json))]
      "op" ("get_tuple_elem" : Json) (by simp) hdist
    have hdest := getObjVal?_of_mem [("op", ("get_tuple_elem" : Json)), ("dest", (d : Json)),
        ("tuple", (t : Json)), ("index", (i : Json))]
      "dest" (d : Json) (by simp) hdist
    have htu := getObjVal?_of_mem [("op", ("get_tuple_elem" : Json)), ("dest", (d : Json)),
        ("tuple", (t : Json)), ("index", (i : Json))]
      "tuple" (t : Json) (by simp) hdist
    have hidx := getObjVal?_of_mem [("op", ("get_tuple_elem" : Json)), ("dest", (d : Json)),
        ("tuple", (t : Json)), ("index", (i : Json))]
      "index" (i : Json) (by simp) hdist
    simp [Decode.field, hop, hdest, htu, hidx, asString_coe, asNat_coe,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | getListElem d t i =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("get_list_elem" : Json)), ("dest", (d : Json)), ("list", (t : Json)),
        ("index", (i : Json))].Pairwise (fun a b : String × Json => a.1 ≠ b.1) := by
      simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("get_list_elem" : Json)), ("dest", (d : Json)),
        ("list", (t : Json)), ("index", (i : Json))]
      "op" ("get_list_elem" : Json) (by simp) hdist
    have hdest := getObjVal?_of_mem [("op", ("get_list_elem" : Json)), ("dest", (d : Json)),
        ("list", (t : Json)), ("index", (i : Json))]
      "dest" (d : Json) (by simp) hdist
    have hl := getObjVal?_of_mem [("op", ("get_list_elem" : Json)), ("dest", (d : Json)),
        ("list", (t : Json)), ("index", (i : Json))]
      "list" (t : Json) (by simp) hdist
    have hidx := getObjVal?_of_mem [("op", ("get_list_elem" : Json)), ("dest", (d : Json)),
        ("list", (t : Json)), ("index", (i : Json))]
      "index" (i : Json) (by simp) hdist
    simp [Decode.field, hop, hdest, hl, hidx, asString_coe, asNat_coe,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | getListRest d t i =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("get_list_rest" : Json)), ("dest", (d : Json)), ("list", (t : Json)),
        ("index", (i : Json))].Pairwise (fun a b : String × Json => a.1 ≠ b.1) := by
      simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("get_list_rest" : Json)), ("dest", (d : Json)),
        ("list", (t : Json)), ("index", (i : Json))]
      "op" ("get_list_rest" : Json) (by simp) hdist
    have hdest := getObjVal?_of_mem [("op", ("get_list_rest" : Json)), ("dest", (d : Json)),
        ("list", (t : Json)), ("index", (i : Json))]
      "dest" (d : Json) (by simp) hdist
    have hl := getObjVal?_of_mem [("op", ("get_list_rest" : Json)), ("dest", (d : Json)),
        ("list", (t : Json)), ("index", (i : Json))]
      "list" (t : Json) (by simp) hdist
    have hidx := getObjVal?_of_mem [("op", ("get_list_rest" : Json)), ("dest", (d : Json)),
        ("list", (t : Json)), ("index", (i : Json))]
      "index" (i : Json) (by simp) hdist
    simp [Decode.field, hop, hdest, hl, hidx, asString_coe, asNat_coe,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | recvPeek d i empty =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("recv_peek" : Json)), ("dest", (d : Json)), ("index", (i : Json)),
        ("empty", (empty : Json))].Pairwise (fun a b : String × Json => a.1 ≠ b.1) := by
      simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("recv_peek" : Json)), ("dest", (d : Json)),
        ("index", (i : Json)), ("empty", (empty : Json))]
      "op" ("recv_peek" : Json) (by simp) hdist
    have hdest := getObjVal?_of_mem [("op", ("recv_peek" : Json)), ("dest", (d : Json)),
        ("index", (i : Json)), ("empty", (empty : Json))]
      "dest" (d : Json) (by simp) hdist
    have hidx := getObjVal?_of_mem [("op", ("recv_peek" : Json)), ("dest", (d : Json)),
        ("index", (i : Json)), ("empty", (empty : Json))]
      "index" (i : Json) (by simp) hdist
    have hemp := getObjVal?_of_mem [("op", ("recv_peek" : Json)), ("dest", (d : Json)),
        ("index", (i : Json)), ("empty", (empty : Json))]
      "empty" (empty : Json) (by simp) hdist
    simp [Decode.field, hop, hdest, hidx, hemp, asString_coe, asNat_coe,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | isTag d r tag =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("is_tag" : Json)), ("dest", (d : Json)), ("reg", (r : Json)),
        ("tag", Encode.encodeTag tag)].Pairwise (fun a b : String × Json => a.1 ≠ b.1) := by
      simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("is_tag" : Json)), ("dest", (d : Json)),
        ("reg", (r : Json)), ("tag", Encode.encodeTag tag)]
      "op" ("is_tag" : Json) (by simp) hdist
    have hdest := getObjVal?_of_mem [("op", ("is_tag" : Json)), ("dest", (d : Json)),
        ("reg", (r : Json)), ("tag", Encode.encodeTag tag)]
      "dest" (d : Json) (by simp) hdist
    have hreg := getObjVal?_of_mem [("op", ("is_tag" : Json)), ("dest", (d : Json)),
        ("reg", (r : Json)), ("tag", Encode.encodeTag tag)]
      "reg" (r : Json) (by simp) hdist
    have htag := getObjVal?_of_mem [("op", ("is_tag" : Json)), ("dest", (d : Json)),
        ("reg", (r : Json)), ("tag", Encode.encodeTag tag)]
      "tag" (Encode.encodeTag tag) (by simp) hdist
    have htd := decodeTag_encodeTag tag
    simp [Decode.field, hop, hdest, hreg, htag, htd, asString_coe, asNat_coe,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | loadLit r lit =>
    simp only [Instr.FloatFree, Instr.LitFuelOk] at hi hfuel
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("load_lit" : Json)), ("reg", (r : Json)), ("lit", Encode.encodeLit lit)].Pairwise
        (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("load_lit" : Json)), ("reg", (r : Json)), ("lit", Encode.encodeLit lit)]
      "op" ("load_lit" : Json) (by simp) hdist
    have hreg := getObjVal?_of_mem [("op", ("load_lit" : Json)), ("reg", (r : Json)), ("lit", Encode.encodeLit lit)]
      "reg" (r : Json) (by simp) hdist
    have hlitf := getObjVal?_of_mem [("op", ("load_lit" : Json)), ("reg", (r : Json)), ("lit", Encode.encodeLit lit)]
      "lit" (Encode.encodeLit lit) (by simp) hdist
    have hlit : Decode.decodeLit (Encode.encodeLit lit) = .ok lit := by
      simpa [Decode.decodeLit] using decodeLitWithFuel_encodeLit 100000 lit hi hfuel
    simp [Decode.field, hop, hreg, hlitf, hlit, asString_coe, asNat_coe,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | jumpIfEq t r lit =>
    simp only [Instr.FloatFree, Instr.LitFuelOk] at hi hfuel
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("jump_if_eq" : Json)), ("target", (t : Json)), ("reg", (r : Json)),
        ("lit", Encode.encodeLit lit)].Pairwise (fun a b : String × Json => a.1 ≠ b.1) := by
      simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("jump_if_eq" : Json)), ("target", (t : Json)),
        ("reg", (r : Json)), ("lit", Encode.encodeLit lit)]
      "op" ("jump_if_eq" : Json) (by simp) hdist
    have htgt := getObjVal?_of_mem [("op", ("jump_if_eq" : Json)), ("target", (t : Json)),
        ("reg", (r : Json)), ("lit", Encode.encodeLit lit)]
      "target" (t : Json) (by simp) hdist
    have hreg := getObjVal?_of_mem [("op", ("jump_if_eq" : Json)), ("target", (t : Json)),
        ("reg", (r : Json)), ("lit", Encode.encodeLit lit)]
      "reg" (r : Json) (by simp) hdist
    have hlitf := getObjVal?_of_mem [("op", ("jump_if_eq" : Json)), ("target", (t : Json)),
        ("reg", (r : Json)), ("lit", Encode.encodeLit lit)]
      "lit" (Encode.encodeLit lit) (by simp) hdist
    have hlit : Decode.decodeLit (Encode.encodeLit lit) = .ok lit := by
      simpa [Decode.decodeLit] using decodeLitWithFuel_encodeLit 100000 lit hi hfuel
    simp [Decode.field, hop, htgt, hreg, hlitf, hlit, asString_coe, asNat_coe,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | call d f args =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("call" : Json)), ("dest", (d : Json)), ("fun", (f : Json)),
        ("args", Json.arr (args.map fun a => toJson a))].Pairwise
        (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("call" : Json)), ("dest", (d : Json)), ("fun", (f : Json)),
        ("args", Json.arr (args.map fun a => toJson a))]
      "op" ("call" : Json) (by simp) hdist
    have hdest := getObjVal?_of_mem [("op", ("call" : Json)), ("dest", (d : Json)), ("fun", (f : Json)),
        ("args", Json.arr (args.map fun a => toJson a))]
      "dest" (d : Json) (by simp) hdist
    have hfun := getObjVal?_of_mem [("op", ("call" : Json)), ("dest", (d : Json)), ("fun", (f : Json)),
        ("args", Json.arr (args.map fun a => toJson a))]
      "fun" (f : Json) (by simp) hdist
    have hargs := getObjVal?_of_mem [("op", ("call" : Json)), ("dest", (d : Json)), ("fun", (f : Json)),
        ("args", Json.arr (args.map fun a => toJson a))]
      "args" (Json.arr (args.map fun a => toJson a)) (by simp) hdist
    have hmap := mapM_asNat_toJson args
    simp [Decode.field, hop, hdest, hfun, hargs, hmap, asString_coe, asNat_coe, asArray_arr,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | spawn d f args =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("spawn" : Json)), ("dest", (d : Json)), ("fun", (f : Json)),
        ("args", Json.arr (args.map fun a => toJson a))].Pairwise
        (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("spawn" : Json)), ("dest", (d : Json)), ("fun", (f : Json)),
        ("args", Json.arr (args.map fun a => toJson a))]
      "op" ("spawn" : Json) (by simp) hdist
    have hdest := getObjVal?_of_mem [("op", ("spawn" : Json)), ("dest", (d : Json)), ("fun", (f : Json)),
        ("args", Json.arr (args.map fun a => toJson a))]
      "dest" (d : Json) (by simp) hdist
    have hfun := getObjVal?_of_mem [("op", ("spawn" : Json)), ("dest", (d : Json)), ("fun", (f : Json)),
        ("args", Json.arr (args.map fun a => toJson a))]
      "fun" (f : Json) (by simp) hdist
    have hargs := getObjVal?_of_mem [("op", ("spawn" : Json)), ("dest", (d : Json)), ("fun", (f : Json)),
        ("args", Json.arr (args.map fun a => toJson a))]
      "args" (Json.arr (args.map fun a => toJson a)) (by simp) hdist
    have hmap := mapM_asNat_toJson args
    simp [Decode.field, hop, hdest, hfun, hargs, hmap, asString_coe, asNat_coe, asArray_arr,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | makeFun d f caps =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("make_fun" : Json)), ("dest", (d : Json)), ("fun", (f : Json)),
        ("captures", Json.arr (caps.map fun a => toJson a))].Pairwise
        (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("make_fun" : Json)), ("dest", (d : Json)), ("fun", (f : Json)),
        ("captures", Json.arr (caps.map fun a => toJson a))]
      "op" ("make_fun" : Json) (by simp) hdist
    have hdest := getObjVal?_of_mem [("op", ("make_fun" : Json)), ("dest", (d : Json)), ("fun", (f : Json)),
        ("captures", Json.arr (caps.map fun a => toJson a))]
      "dest" (d : Json) (by simp) hdist
    have hfun := getObjVal?_of_mem [("op", ("make_fun" : Json)), ("dest", (d : Json)), ("fun", (f : Json)),
        ("captures", Json.arr (caps.map fun a => toJson a))]
      "fun" (f : Json) (by simp) hdist
    have hargs := getObjVal?_of_mem [("op", ("make_fun" : Json)), ("dest", (d : Json)), ("fun", (f : Json)),
        ("captures", Json.arr (caps.map fun a => toJson a))]
      "captures" (Json.arr (caps.map fun a => toJson a)) (by simp) hdist
    have hmap := mapM_asNat_toJson caps
    simp [Decode.field, hop, hdest, hfun, hargs, hmap, asString_coe, asNat_coe, asArray_arr,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | apply d f args =>
    simp only [Encode.encodeInstr, Decode.decodeInstr]
    have hdist : [("op", ("apply" : Json)), ("dest", (d : Json)), ("fun", (f : Json)),
        ("args", Json.arr (args.map fun a => toJson a))].Pairwise
        (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
    have hop := getObjVal?_of_mem [("op", ("apply" : Json)), ("dest", (d : Json)), ("fun", (f : Json)),
        ("args", Json.arr (args.map fun a => toJson a))]
      "op" ("apply" : Json) (by simp) hdist
    have hdest := getObjVal?_of_mem [("op", ("apply" : Json)), ("dest", (d : Json)), ("fun", (f : Json)),
        ("args", Json.arr (args.map fun a => toJson a))]
      "dest" (d : Json) (by simp) hdist
    have hfun := getObjVal?_of_mem [("op", ("apply" : Json)), ("dest", (d : Json)), ("fun", (f : Json)),
        ("args", Json.arr (args.map fun a => toJson a))]
      "fun" (f : Json) (by simp) hdist
    have hargs := getObjVal?_of_mem [("op", ("apply" : Json)), ("dest", (d : Json)), ("fun", (f : Json)),
        ("args", Json.arr (args.map fun a => toJson a))]
      "args" (Json.arr (args.map fun a => toJson a)) (by simp) hdist
    have hmap := mapM_asNat_toJson args
    simp [Decode.field, hop, hdest, hfun, hargs, hmap, asString_coe, asNat_coe, asArray_arr,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | wait retry after timeout =>
    match timeout with
    | none =>
      simp only [Encode.encodeInstr, toJson, List.cons_append, List.nil_append, Decode.decodeInstr]
      have hdist : [("op", Json.str "wait"), ("retry", (retry : Json)), ("after", (after : Json)),
          ("timeout", Json.null)].Pairwise (fun a b : String × Json => a.1 ≠ b.1) := by
        simp [List.pairwise_cons]
      have hop := getObjVal?_of_mem [("op", Json.str "wait"), ("retry", (retry : Json)),
          ("after", (after : Json)), ("timeout", Json.null)]
        "op" (Json.str "wait") (by simp) hdist
      have hretry := getObjVal?_of_mem [("op", Json.str "wait"), ("retry", (retry : Json)),
          ("after", (after : Json)), ("timeout", Json.null)]
        "retry" (retry : Json) (by simp) hdist
      have hafter := getObjVal?_of_mem [("op", Json.str "wait"), ("retry", (retry : Json)),
          ("after", (after : Json)), ("timeout", Json.null)]
        "after" (after : Json) (by simp) hdist
      have hto := getObjVal?_of_mem [("op", Json.str "wait"), ("retry", (retry : Json)),
          ("after", (after : Json)), ("timeout", Json.null)]
        "timeout" Json.null (by simp) hdist
      simp [Decode.field, hop, hretry, hafter, hto, asString_coe, asNat_coe,
        Bind.bind, Pure.pure, Except.bind, Except.pure]
    | some n =>
      simp only [Encode.encodeInstr, toJson, List.cons_append, List.nil_append, Decode.decodeInstr]
      have hdist : [("op", Json.str "wait"), ("retry", (retry : Json)), ("after", (after : Json)),
          ("timeout", (n : Json))].Pairwise (fun a b : String × Json => a.1 ≠ b.1) := by
        simp [List.pairwise_cons]
      have hop := getObjVal?_of_mem [("op", Json.str "wait"), ("retry", (retry : Json)),
          ("after", (after : Json)), ("timeout", (n : Json))]
        "op" (Json.str "wait") (by simp) hdist
      have hretry := getObjVal?_of_mem [("op", Json.str "wait"), ("retry", (retry : Json)),
          ("after", (after : Json)), ("timeout", (n : Json))]
        "retry" (retry : Json) (by simp) hdist
      have hafter := getObjVal?_of_mem [("op", Json.str "wait"), ("retry", (retry : Json)),
          ("after", (after : Json)), ("timeout", (n : Json))]
        "after" (after : Json) (by simp) hdist
      have hto := getObjVal?_of_mem [("op", Json.str "wait"), ("retry", (retry : Json)),
          ("after", (after : Json)), ("timeout", (n : Json))]
        "timeout" (n : Json) (by simp) hdist
      simp [Decode.field, hop, hretry, hafter, hto, asString_coe, asNat_coe,
        Bind.bind, Pure.pure, Except.bind, Except.pure]



theorem versionOk_not_rejected (v : Nat) (h : Module.versionOk v) :
    (v != 1 && v != 2 && v != 3 && v != 4 && v != 5 && v != 6 && v != 7 && v != 8 &&
      v != 9 && v != 10 && v != 11 && v != 12 && v != 13 && v != 14) = false := by
  simp only [Module.versionOk] at h
  rcases h with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]

theorem decodeFunction_encodeFunction (f : Function)
    (hf : Function.FloatFree f) (hfuel : Function.LitFuelOk f)
    (hloc : Function.LocalsOk f) :
    Decode.decodeFunction (Encode.encodeFunction f) = Except.ok f := by
  simp only [Encode.encodeFunction, Decode.decodeFunction]
  have hdist : [("name", (f.name : Json)), ("arity", (f.arity : Json)),
      ("locals", (f.locals : Json)), ("code", Json.arr (f.code.map Encode.encodeInstr))].Pairwise
      (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
  have hname := getObjVal?_of_mem [("name", (f.name : Json)), ("arity", (f.arity : Json)),
      ("locals", (f.locals : Json)), ("code", Json.arr (f.code.map Encode.encodeInstr))]
    "name" (f.name : Json) (by simp) hdist
  have harity := getObjVal?_of_mem [("name", (f.name : Json)), ("arity", (f.arity : Json)),
      ("locals", (f.locals : Json)), ("code", Json.arr (f.code.map Encode.encodeInstr))]
    "arity" (f.arity : Json) (by simp) hdist
  have hlocals := getObjVal?_of_mem [("name", (f.name : Json)), ("arity", (f.arity : Json)),
      ("locals", (f.locals : Json)), ("code", Json.arr (f.code.map Encode.encodeInstr))]
    "locals" (f.locals : Json) (by simp) hdist
  have hcode := getObjVal?_of_mem [("name", (f.name : Json)), ("arity", (f.arity : Json)),
      ("locals", (f.locals : Json)), ("code", Json.arr (f.code.map Encode.encodeInstr))]
    "code" (Json.arr (f.code.map Encode.encodeInstr)) (by simp) hdist
  have hmap : (f.code.map Encode.encodeInstr).mapM Decode.decodeInstr = Except.ok f.code := by
    rw [Array.mapM_map]
    refine Array.mapM_ok_of_forall_mem _ _ ?_
    intro inst hi
    obtain ⟨idx, hidx, rfl⟩ := Array.getElem_of_mem hi
    exact decodeInstr_encodeInstr _ (hf idx hidx) (hfuel idx hidx)
  have hlt : ¬(f.locals < f.arity) := Nat.not_lt.mpr hloc
  simp [Decode.field, Decode.resolveLabels, hname, harity, hlocals, hcode, hmap,
    asString_coe, asNat_coe, asArray_arr, Bind.bind, Pure.pure, Except.bind, Except.pure, hlt]

theorem decodeCodeModule_encodeCodeModule (cm : CodeModule)
    (hm : CodeModule.FloatFree cm) (hfuel : CodeModule.LitFuelOk cm)
    (hloc : CodeModule.LocalsOk cm) :
    Decode.decodeCodeModule (Encode.encodeCodeModule cm) = Except.ok cm := by
  simp only [Encode.encodeCodeModule, Decode.decodeCodeModule]
  have hdist : [("name", (cm.name : Json)),
      ("functions", Json.arr (cm.functions.map Encode.encodeFunction))].Pairwise
      (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
  have hname := getObjVal?_of_mem [("name", (cm.name : Json)),
      ("functions", Json.arr (cm.functions.map Encode.encodeFunction))]
    "name" (cm.name : Json) (by simp) hdist
  have hfuns := getObjVal?_of_mem [("name", (cm.name : Json)),
      ("functions", Json.arr (cm.functions.map Encode.encodeFunction))]
    "functions" (Json.arr (cm.functions.map Encode.encodeFunction)) (by simp) hdist
  have hmap : (cm.functions.map Encode.encodeFunction).mapM Decode.decodeFunction =
      Except.ok cm.functions := by
    rw [Array.mapM_map]
    refine Array.mapM_ok_of_forall_mem _ _ ?_
    intro f hfmem
    obtain ⟨idx, hidx, rfl⟩ := Array.getElem_of_mem hfmem
    exact decodeFunction_encodeFunction _ (hm idx hidx) (hfuel idx hidx) (hloc idx hidx)
  simp [Decode.field, hname, hfuns, hmap, asString_coe, asArray_arr,
    Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem decodeModule_encodeModule (m : Module) (hm : Module.FloatFree m)
    (hfuel : Module.LitFuelOk m) (hloc : Module.LocalsOk m)
    (hv : Module.versionOk m.version) (hne : 0 < m.modules.size) :
    Decode.decodeModule (Encode.encodeModule m) = Except.ok m := by
  simp only [Encode.encodeModule, Decode.decodeModule]
  have hdist : [("version", (m.version : Json)), ("entry", (m.entry : Json)),
      ("modules", Json.arr (m.modules.map Encode.encodeCodeModule))].Pairwise
      (fun a b : String × Json => a.1 ≠ b.1) := by simp [List.pairwise_cons]
  have hvis := getObjVal?_of_mem [("version", (m.version : Json)), ("entry", (m.entry : Json)),
      ("modules", Json.arr (m.modules.map Encode.encodeCodeModule))]
    "version" (m.version : Json) (by simp) hdist
  have hentry := getObjVal?_of_mem [("version", (m.version : Json)), ("entry", (m.entry : Json)),
      ("modules", Json.arr (m.modules.map Encode.encodeCodeModule))]
    "entry" (m.entry : Json) (by simp) hdist
  have hmods := getObjVal?_of_mem [("version", (m.version : Json)), ("entry", (m.entry : Json)),
      ("modules", Json.arr (m.modules.map Encode.encodeCodeModule))]
    "modules" (Json.arr (m.modules.map Encode.encodeCodeModule)) (by simp) hdist
  have hvok := versionOk_not_rejected m.version hv
  have hmap : (m.modules.map Encode.encodeCodeModule).mapM Decode.decodeCodeModule =
      Except.ok m.modules := by
    rw [Array.mapM_map]
    refine Array.mapM_ok_of_forall_mem _ _ ?_
    intro cm hcmem
    obtain ⟨idx, hidx, rfl⟩ := Array.getElem_of_mem hcmem
    exact decodeCodeModule_encodeCodeModule _
      (hm idx hidx) (hfuel idx hidx) (hloc idx hidx)
  have hempty : m.modules.isEmpty = false := by
    simp [Array.isEmpty]
    intro heq
    rw [heq] at hne
    simp at hne
  simp [Decode.field, hvis, hentry, hmods, asString_coe, asNat_coe, asArray_arr,
    Bind.bind, Pure.pure, Except.bind, Except.pure, hvok, hmap, hempty]


end Json

/-- Decode ∘ encode for float-free literals under the public fuel budget. -/
theorem decodeLit_encodeLit (t : Term) (ht : Term.FloatFree t)
    (hbound : Term.depth t ≤ 100000) :
    Json.Decode.decodeLit (Json.Encode.encodeLit t) = .ok t := by
  simpa [Json.Decode.decodeLit] using Json.decodeLitWithFuel_encodeLit 100000 t ht hbound

/-- Decode ∘ encode for instructions with float-free embedded lits. -/
theorem decodeInstr_encodeInstr (i : Instr) (hi : Instr.FloatFree i)
    (hfuel : Instr.LitFuelOk i) :
    Json.Decode.decodeInstr (Json.Encode.encodeInstr i) = .ok i :=
  Json.decodeInstr_encodeInstr i hi hfuel

/-- Decode ∘ encode for the `modules[]` image `encodeModule` emits (float-free lits). -/
theorem decodeModule_encodeModule (m : Module) (hm : Module.FloatFree m)
    (hfuel : Module.LitFuelOk m) (hloc : Module.LocalsOk m)
    (hv : Module.versionOk m.version) (hne : 0 < m.modules.size) :
    Json.Decode.decodeModule (Json.Encode.encodeModule m) = .ok m :=
  Json.decodeModule_encodeModule m hm hfuel hloc hv hne

/-! ## Float literals (Phase 18)

`encodeLit (.float f)` goes through `JsonNumber.fromFloat?`. Finite floats recover
`n.toFloat` (not necessarily bit-identical to `f`). Non-finite floats collapse to `0.0`.
-/

namespace Json

theorem decodeLitWithFuel_encodeLit_float_inr (fuel : Nat) (f : Float) (n : JsonNumber)
    (hfuel : 1 ≤ fuel) (hn : JsonNumber.fromFloat? f = .inr n) :
    Decode.decodeLitWithFuel fuel (Encode.encodeLit (.float f)) =
      .ok (.float n.toFloat) := by
  match fuel with
  | 0 => omega
  | fuel + 1 =>
    rw [Encode.encodeLit, hn]
    unfold Decode.decodeLitWithFuel
    have hbool := getObjVal?_singleton_ne "float" "bool" (Json.num n) (by decide)
    have hint := getObjVal?_singleton_ne "float" "int" (Json.num n) (by decide)
    have hatom := getObjVal?_singleton_ne "float" "atom" (Json.num n) (by decide)
    have htuple := getObjVal?_singleton_ne "float" "tuple" (Json.num n) (by decide)
    have hlist := getObjVal?_singleton_ne "float" "list" (Json.num n) (by decide)
    have hmap := getObjVal?_singleton_ne "float" "map" (Json.num n) (by decide)
    have hpid := getObjVal?_singleton_ne "float" "pid" (Json.num n) (by decide)
    have href := getObjVal?_singleton_ne "float" "ref" (Json.num n) (by decide)
    have hfloat := getObjVal?_singleton "float" (Json.num n)
    simp [isNull_mkObj, hbool, hint, hatom, htuple, hlist, hmap, hpid, href, hfloat,
      Json.getNum?, Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem decodeLitWithFuel_encodeLit_float_inl (fuel : Nat) (f : Float) (msg : String)
    (hfuel : 1 ≤ fuel) (hn : JsonNumber.fromFloat? f = .inl msg) :
    Decode.decodeLitWithFuel fuel (Encode.encodeLit (.float f)) =
      .ok (.float (JsonNumber.toFloat ⟨0, 0⟩)) := by
  match fuel with
  | 0 => omega
  | fuel + 1 =>
    rw [Encode.encodeLit, hn]
    unfold Decode.decodeLitWithFuel
    have hbool := getObjVal?_singleton_ne "float" "bool" (Json.num ⟨0, 0⟩) (by decide)
    have hint := getObjVal?_singleton_ne "float" "int" (Json.num ⟨0, 0⟩) (by decide)
    have hatom := getObjVal?_singleton_ne "float" "atom" (Json.num ⟨0, 0⟩) (by decide)
    have htuple := getObjVal?_singleton_ne "float" "tuple" (Json.num ⟨0, 0⟩) (by decide)
    have hlist := getObjVal?_singleton_ne "float" "list" (Json.num ⟨0, 0⟩) (by decide)
    have hmap := getObjVal?_singleton_ne "float" "map" (Json.num ⟨0, 0⟩) (by decide)
    have hpid := getObjVal?_singleton_ne "float" "pid" (Json.num ⟨0, 0⟩) (by decide)
    have href := getObjVal?_singleton_ne "float" "ref" (Json.num ⟨0, 0⟩) (by decide)
    have hfloat := getObjVal?_singleton "float" (Json.num ⟨0, 0⟩)
    simp [isNull_mkObj, hbool, hint, hatom, htuple, hlist, hmap, hpid, href, hfloat,
      Json.getNum?, Bind.bind, Pure.pure, Except.bind, Except.pure]

/-- Public-fuel form: finite float → decode recovers `n.toFloat`. -/
theorem decodeLit_encodeLit_float_inr (f : Float) (n : JsonNumber)
    (hn : JsonNumber.fromFloat? f = .inr n) :
    Decode.decodeLit (Encode.encodeLit (.float f)) = .ok (.float n.toFloat) := by
  simpa [Decode.decodeLit] using
    decodeLitWithFuel_encodeLit_float_inr 100000 f n (by decide) hn

/-- Public-fuel form: non-finite float collapses to encode/decode of `⟨0,0⟩`. -/
theorem decodeLit_encodeLit_float_inl (f : Float) (msg : String)
    (hn : JsonNumber.fromFloat? f = .inl msg) :
    Decode.decodeLit (Encode.encodeLit (.float f)) =
      .ok (.float (JsonNumber.toFloat ⟨0, 0⟩)) := by
  simpa [Decode.decodeLit] using
    decodeLitWithFuel_encodeLit_float_inl 100000 f msg (by decide) hn

end Json

end Autumn
