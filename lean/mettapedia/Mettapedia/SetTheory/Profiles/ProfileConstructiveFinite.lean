import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma

/-!
# Explicit constructive finite enumeration

Finite algorithms receive an authored list of all candidates. Completeness
and absence of duplicates are proved for that list. Decisions and witness
extraction search the list rather than selecting from propositional
existence. No quotient-to-list choice is used.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ConstructiveFinite

universe u v

class Enumeration (α : Type u) where
  elements : List α
  nodup : elements.Nodup
  complete : ∀ value, value ∈ elements

variable {α : Type u} {β : Type v}

def elements [Enumeration α] : List α := Enumeration.elements
def size [Enumeration α] : Nat := (elements (α := α)).length

theorem complete [Enumeration α] (value : α) : value ∈ elements :=
  Enumeration.complete value

theorem nodup [Enumeration α] : (elements (α := α)).Nodup :=
  Enumeration.nodup

instance finEnumeration (bound : Nat) : Enumeration (Fin bound) where
  elements := List.finRange bound
  nodup := List.nodup_finRange bound
  complete := List.mem_finRange

@[simp] theorem size_fin (bound : Nat) : size (α := Fin bound) = bound :=
  List.length_finRange

instance forallDecidable [Enumeration α] (predicate : α → Prop) [DecidablePred predicate] :
    Decidable (∀ value, predicate value) :=
  decidable_of_iff ((elements (α := α)).all (fun value => decide (predicate value)) = true) (by
    simp only [List.all_eq_true, decide_eq_true_eq]
    exact ⟨fun available value => available value (complete value),
      fun available value _ => available value⟩)

instance existsDecidable [Enumeration α] (predicate : α → Prop) [DecidablePred predicate] :
    Decidable (∃ value, predicate value) :=
  decidable_of_iff ((elements (α := α)).any (fun value => decide (predicate value)) = true) (by
    simp only [List.any_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨value, _, available⟩ => ⟨value, available⟩,
      fun ⟨value, available⟩ => ⟨value, complete value, available⟩⟩)

def pairElements [Enumeration α] [Enumeration β] : List (α × β) :=
  List.product (elements (α := α)) (elements (α := β))

theorem pair_complete [Enumeration α] [Enumeration β] (first : α) (second : β) :
    (first, second) ∈ pairElements :=
  List.mem_product.mpr ⟨complete first, complete second⟩

theorem pair_length [Enumeration α] [Enumeration β] :
    (pairElements (α := α) (β := β)).length = size (α := α) * size (α := β) :=
  List.length_product _ _

instance productEnumeration [Enumeration α] [Enumeration β] : Enumeration (α × β) where
  elements := pairElements
  nodup := (nodup (α := α)).product (nodup (α := β))
  complete := fun pair => pair_complete pair.1 pair.2

@[simp] theorem size_product [Enumeration α] [Enumeration β] :
    size (α := α × β) = size (α := α) * size (α := β) := pair_length

def subtypeElements [Enumeration α] (predicate : α → Prop) [DecidablePred predicate] :
    List {value : α // predicate value} :=
  ((elements (α := α)).filter (fun value => decide (predicate value))).attach.map
    (fun value => ⟨value.val, by
      have available : value.val ∈ (elements (α := α)).filter (fun value => decide (predicate value)) :=
        value.property
      exact of_decide_eq_true (List.mem_filter.mp available).2⟩)

theorem subtype_complete [Enumeration α] (predicate : α → Prop) [DecidablePred predicate]
    (value : {value : α // predicate value}) : value ∈ subtypeElements predicate := by
  unfold subtypeElements
  apply List.mem_map.mpr
  have available : value.val ∈ (elements (α := α)).filter (fun value => decide (predicate value)) :=
    List.mem_filter.mpr ⟨complete value.val, decide_eq_true value.property⟩
  exact ⟨⟨value.val, available⟩, List.mem_attach _ _, Subtype.ext rfl⟩

theorem subtype_nodup [Enumeration α] (predicate : α → Prop) [DecidablePred predicate] :
    (subtypeElements predicate).Nodup := by
  unfold subtypeElements
  apply ((nodup (α := α)).filter _).attach.map
  intro first second same
  apply Subtype.ext
  exact congrArg (fun value : {value : α // predicate value} => value.val) same

instance subtypeEnumeration [Enumeration α] (predicate : α → Prop) [DecidablePred predicate] :
    Enumeration {value : α // predicate value} where
  elements := subtypeElements predicate
  nodup := subtype_nodup predicate
  complete := subtype_complete predicate

theorem subtype_size [Enumeration α] (predicate : α → Prop) [DecidablePred predicate] :
    @size {value : α // predicate value} (subtypeEnumeration predicate) =
      ((elements (α := α)).filter (fun value => decide (predicate value))).length := by
  change (subtypeElements predicate).length = _
  simp only [subtypeElements, List.length_map, List.length_attach]

theorem filter_sublist_of_imp (pool : List α) (first second : α → Bool)
    (implication : ∀ value, first value = true → second value = true) :
    List.Sublist (pool.filter first) (pool.filter second) := by
  induction pool with
  | nil => exact List.Sublist.refl []
  | cons value pool previous =>
    cases before : first value <;> cases after : second value
    · simpa only [List.filter_cons, before, after, Bool.false_eq_true, if_false] using previous
    · simpa only [List.filter_cons, before, after, Bool.false_eq_true, if_false, if_true] using previous.cons value
    · exact False.elim (Bool.false_ne_true (after.symm.trans (implication value before)))
    · simpa only [List.filter_cons, before, after, if_true] using previous.cons_cons value

theorem length_lt_of_sublist_ne {first second : List α}
    (contained : List.Sublist first second) (distinct : first ≠ second) : first.length < second.length :=
  Nat.lt_of_not_ge (fun bound => distinct (contained.eq_of_length_le bound))

def witnessFromList (pool : List α) (predicate : α → Prop) [DecidablePred predicate]
    (available : ∃ value ∈ pool, predicate value) : {value : α // predicate value} :=
  match pool with
  | [] => False.elim (by simp at available)
  | first :: rest =>
      if good : predicate first then ⟨first, good⟩
      else witnessFromList rest predicate (by
        obtain ⟨value, member, proof⟩ := available
        rcases List.mem_cons.mp member with same | member
        · exact False.elim (good (same ▸ proof))
        · exact ⟨value, member, proof⟩)

def witness [Enumeration α] (predicate : α → Prop) [DecidablePred predicate]
    (available : ∃ value, predicate value) : {value : α // predicate value} :=
  witnessFromList elements predicate (by
    obtain ⟨value, proof⟩ := available
    exact ⟨value, complete value, proof⟩)

end Mettapedia.SetTheory.Profiles.ConstructiveFinite
