import Mettapedia.Machines.NamedShapeCursor

/-!
# Shared names versus unfolded constructor size

An instrumented expansion records each dereference occurrence. Its value
projection agrees with the uninstrumented expansion. If every stored body
contains a constructor, the number of dereference occurrences, and hence
the number of distinct visited names, is bounded by unfolded constructor
size. Successful traces contain the root and are reference-closed, so this
also bounds every finite set of reachable names.

The constructor condition matters: a chain of alias-only entries can have
more names than its expanded one-atom term. The bound counts logical names,
not skeleton tables, allocator bytes, caches, or unreachable allocated data.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NamedDAGSize

open ShapeStore NamedShapeGraph
open Mettapedia.GSLT.Dynamics.StoreReachability

variable {α Name : Type}

abbrev Trace (α Name : Type) := Tm α × List Name

def localNodes : Expr α Name → Nat
  | .atom _ => 1
  | .node l r => 1 + localNodes l + localNodes r
  | .ref _ => 0

def evalTrace (read : Name → Option (Trace α Name)) : Expr α Name → Option (Trace α Name)
  | .atom a => some (.atom a, [])
  | .node l r => (evalTrace read l).bind fun left =>
      (evalTrace read r).map fun right => (.node left.1 right.1, left.2 ++ right.2)
  | .ref n => read n

def expand (heap : Heap α Name) : Nat → Name → Option (Trace α Name)
  | 0, _ => none
  | depth + 1, n => (heap n).bind fun e =>
      (evalTrace (expand heap depth) e).map fun result => (result.1, n :: result.2)

theorem evalTrace_value (read : Name → Option (Trace α Name)) (e : Expr α Name) :
    (evalTrace read e).map Prod.fst = e.eval (fun n => (read n).map Prod.fst) := by
  induction e with
  | atom a => rfl
  | ref n => rfl
  | node l r ihl ihr =>
      simp only [evalTrace, Expr.eval]
      rw [← ihl, ← ihr]
      cases evalTrace read l <;> cases evalTrace read r <;> rfl

theorem expand_value (heap : Heap α Name) (depth : Nat) (n : Name) :
    (expand heap depth n).map Prod.fst = unfoldName heap depth n := by
  induction depth generalizing n with
  | zero => rfl
  | succ depth ih =>
      cases found : heap n with
      | none => simp [expand, unfoldName, found]
      | some body =>
          simp only [expand, unfoldName, found, Option.bind_some, Option.map_map]
          change (evalTrace (expand heap depth) body).map Prod.fst = _
          rw [evalTrace_value]
          exact eval_congr body _ _ (fun child _ => ih child)

theorem evalTrace_bound (read : Name → Option (Trace α Name))
    (bounded : ∀ n result, read n = some result → result.2.length ≤ termSize result.1)
    (e : Expr α Name) (result : Trace α Name) (success : evalTrace read e = some result) :
    result.2.length + localNodes e ≤ termSize result.1 := by
  induction e generalizing result with
  | atom a =>
      have equal : (.atom a, []) = result := Option.some.inj success
      subst result
      simp [localNodes, termSize]
  | ref n => simpa [localNodes] using bounded n result success
  | node l r ihl ihr =>
      obtain ⟨left, hl, tail⟩ := Option.bind_eq_some_iff.mp success
      obtain ⟨right, hr, equal⟩ := Option.map_eq_some_iff.mp tail
      subst result
      have bl := ihl left hl
      have br := ihr right hr
      simp only [List.length_append, localNodes, termSize]
      omega

/-- Count repeated read occurrences before counting distinct shared names. -/
theorem expand_bound (heap : Heap α Name)
    (constructors : ∀ n e, heap n = some e → 0 < localNodes e)
    (depth : Nat) (n : Name) (result : Trace α Name)
    (success : expand heap depth n = some result) : result.2.length ≤ termSize result.1 := by
  induction depth generalizing n result with
  | zero => simp [expand] at success
  | succ depth ih =>
      obtain ⟨e, found, tail⟩ := Option.bind_eq_some_iff.mp success
      obtain ⟨expanded, he, equal⟩ := Option.map_eq_some_iff.mp tail
      subst result
      have bound := evalTrace_bound _ ih e expanded he
      have positive := constructors n e found
      simp only [List.length_cons]
      omega

theorem expand_has_root (heap : Heap α Name) (depth : Nat) (n : Name)
    (result : Trace α Name) (success : expand heap depth n = some result) : n ∈ result.2 := by
  cases depth with
  | zero => simp [expand] at success
  | succ depth =>
      obtain ⟨e, _, tail⟩ := Option.bind_eq_some_iff.mp success
      obtain ⟨expanded, _, equal⟩ := Option.map_eq_some_iff.mp tail
      subst result
      exact List.mem_cons_self

theorem evalTrace_contains_refs (read : Name → Option (Trace α Name))
    (rooted : ∀ n result, read n = some result → n ∈ result.2)
    (e : Expr α Name) (result : Trace α Name) (success : evalTrace read e = some result) :
    ∀ n ∈ e.refs, n ∈ result.2 := by
  induction e generalizing result with
  | atom a => simp [Expr.refs]
  | ref n =>
      intro child member
      have equal : child = n := by simpa [Expr.refs] using member
      subst child
      exact rooted n result success
  | node l r ihl ihr =>
      obtain ⟨left, hl, tail⟩ := Option.bind_eq_some_iff.mp success
      obtain ⟨right, hr, equal⟩ := Option.map_eq_some_iff.mp tail
      subst result
      intro n member
      rcases List.mem_append.mp member with hleft | hright
      · exact List.mem_append_left _ (ihl left hl n hleft)
      · exact List.mem_append_right _ (ihr right hr n hright)

abbrev Closed (heap : Heap α Name) (seen : List Name) : Prop :=
  ∀ n ∈ seen, ∀ e, heap n = some e → ∀ child ∈ e.refs, child ∈ seen

theorem evalTrace_closed (heap : Heap α Name) (read : Name → Option (Trace α Name))
    (closed : ∀ n result, read n = some result → Closed heap result.2)
    (e : Expr α Name) (result : Trace α Name) (success : evalTrace read e = some result) :
    Closed heap result.2 := by
  induction e generalizing result with
  | atom a =>
      have equal : (.atom a, []) = result := Option.some.inj success
      subst result
      intro n absent
      exact False.elim (List.not_mem_nil absent)
  | ref n => exact closed n result success
  | node l r ihl ihr =>
      obtain ⟨left, hl, tail⟩ := Option.bind_eq_some_iff.mp success
      obtain ⟨right, hr, equal⟩ := Option.map_eq_some_iff.mp tail
      subst result
      intro n member body found child occurs
      rcases List.mem_append.mp member with hleft | hright
      · exact List.mem_append_left _ (ihl left hl n hleft body found child occurs)
      · exact List.mem_append_right _ (ihr right hr n hright body found child occurs)

theorem expand_closed (heap : Heap α Name) (depth : Nat) (n : Name)
    (result : Trace α Name) (success : expand heap depth n = some result) : Closed heap result.2 := by
  induction depth generalizing n result with
  | zero => simp [expand] at success
  | succ depth ih =>
      obtain ⟨e, found, tail⟩ := Option.bind_eq_some_iff.mp success
      obtain ⟨expanded, he, equal⟩ := Option.map_eq_some_iff.mp tail
      subst result
      intro parent member body hbody child occurs
      rcases List.mem_cons.mp member with same | later
      · subst parent
        have sameBody : body = e := Option.some.inj (hbody.symm.trans found)
        subst body
        exact List.mem_cons_of_mem _
          (evalTrace_contains_refs _ (expand_has_root heap depth) e expanded he child occurs)
      · exact List.mem_cons_of_mem _ (evalTrace_closed heap _ ih e expanded he
          parent later body hbody child occurs)

def graph (heap : Heap α Name) (root : Name) : Store Name where
  root n := n = root
  pointsTo p c := ∃ e, heap p = some e ∧ c ∈ e.refs

theorem reachable_in_trace (heap : Heap α Name) (depth : Nat) (root : Name)
    (result : Trace α Name) (success : expand heap depth root = some result)
    (n : Name) (live : Reach (graph heap root) n) : n ∈ result.2 := by
  induction live with
  | root same => exact same ▸ expand_has_root heap depth root result success
  | @step p c _ edge ih =>
      obtain ⟨body, found, occurs⟩ := edge
      exact expand_closed heap depth root result success p ih body found c occurs

theorem reachable_size_bound [DecidableEq Name] (heap : Heap α Name)
    (constructors : ∀ n e, heap n = some e → 0 < localNodes e)
    (depth : Nat) (root : Name) (result : Trace α Name)
    (success : expand heap depth root = some result)
    (reachable : Finset Name) (allLive : ∀ n ∈ reachable, Reach (graph heap root) n) :
    reachable.card ≤ termSize result.1 := by
  have included : reachable ⊆ result.2.toFinset := by
    intro n member
    exact List.mem_toFinset.mpr (reachable_in_trace heap depth root result success n (allLive n member))
  exact (Finset.card_le_card included).trans
    ((List.toFinset_card_le _).trans (expand_bound heap constructors depth root result success))

theorem constructed_bodies_have_constructors (read : Name → Option (Tm α))
    (name : Tm α → Name) (policy : Policy α) (n : Name) (e : Expr α Name)
    (found : NamedStoreModel.bodies read name policy n = some e) : 0 < localNodes e := by
  obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp found
  cases t <;> simp [quoteBody, localNodes]

/-- The constructed recursive store supplies both successful expansion and
the constructor condition, rather than asking the client to assume either. -/
theorem constructed_reachable_bound [DecidableEq Name]
    (read : Name → Option (Tm α)) (name : Tm α → Name)
    (roundtrip : ∀ t, read (name t) = some t) (policy : Policy α)
    (root : Name) (t : Tm α) (found : read root = some t)
    (reachable : Finset Name)
    (allLive : ∀ n ∈ reachable, Reach (graph (NamedStoreModel.bodies read name policy) root) n) :
    reachable.card ≤ termSize t := by
  have success := (expand_value (NamedStoreModel.bodies read name policy) (termSize t + 1) root).trans
    (NamedStoreModel.bodies_complete read name roundtrip policy root t found)
  obtain ⟨result, expanded, value⟩ := Option.map_eq_some_iff.mp success
  have bound := reachable_size_bound _ (constructed_bodies_have_constructors read name policy)
    _ root result expanded reachable allLive
  simpa only [value] using bound

namespace Controls

def shared : Heap Unit Nat
  | 0 => some (.atom ())
  | 1 => some (.node (.ref 0) (.ref 0))
  | _ => none

example : expand shared 2 1 = some (.node (.atom ()) (.atom ()), [1, 0, 0]) := by decide
example : ([1, 0, 0] : List Nat).toFinset.card = 2 := by decide

def aliases : Heap Unit Nat
  | 0 => some (.atom ())
  | 1 => some (.ref 0)
  | _ => none

theorem aliases_need_the_constructor_condition :
    expand aliases 2 1 = some (.atom (), [1, 0]) ∧
    ([1, 0] : List Nat).toFinset.card > termSize (Tm.atom ()) := by decide

end Controls

#print axioms expand_value
#print axioms expand_bound
#print axioms expand_closed
#print axioms reachable_size_bound

end Mettapedia.Machines.NamedDAGSize
