import Mettapedia.SetTheory.Profiles.ProfileConstructiveFinite
import Mathlib.Data.List.Nodup

/-!
# Constructed finite function search

An explicit enumeration provides rank and unrank. Function candidates are
then built recursively from the finite domain's positions. In particular,
searching for two mutually inverse child maps does not invoke propositional
choice or a quotient's chosen representative.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ConstructiveFinite

universe u v

variable {α : Type u} {β : Type v}

/-- Locate a member by scanning the authored list, carrying its get equation. -/
def positionIn [DecidableEq α] (pool : List α) (value : α) (member : value ∈ pool) :
    {index : Fin pool.length // pool.get index = value} :=
  match pool with
  | [] => False.elim (by simp at member)
  | head :: tail =>
      if same : value = head then ⟨0, same.symm⟩
      else
        let earlier := positionIn tail value (by
          rcases List.mem_cons.mp member with equal | inTail
          · exact False.elim (same equal)
          · exact inTail)
        ⟨earlier.val.succ, earlier.property⟩

/-- Rank and unrank use the authored list's own position order. -/
def positionEquiv [Enumeration α] [DecidableEq α] : Fin (size (α := α)) ≃ α where
  toFun index := (elements (α := α)).get index
  invFun value := (positionIn elements value (complete value)).val
  left_inv index := (nodup (α := α)).get_inj_iff.mp
    (positionIn elements ((elements (α := α)).get index) (complete _)).property
  right_inv value := (positionIn elements value (complete value)).property

def finFunctions (values : List β) : (count : Nat) → List (Fin count → β)
  | 0 => [Fin.elim0]
  | count + 1 => (values.product (finFunctions values count)).map
      (fun pair => Fin.cases pair.1 pair.2)

theorem finFunctions_complete (values : List β) (all : ∀ value, value ∈ values)
    (count : Nat) (function : Fin count → β) : function ∈ finFunctions values count := by
  induction count with
  | zero =>
    have same : function = Fin.elim0 := funext (fun index => Fin.elim0 index)
    simp only [finFunctions, List.mem_singleton]
    exact same
  | succ count previous =>
    apply List.mem_map.mpr
    refine ⟨⟨function 0, fun index => function index.succ⟩,
      List.mem_product.mpr ⟨all _, previous _⟩, ?_⟩
    funext index
    refine Fin.cases ?_ (fun index => ?_) index <;> rfl

def functionElements [Enumeration α] [Enumeration β] [DecidableEq α] : List (α → β) :=
  (finFunctions (elements (α := β)) (size (α := α))).map
    (fun function value => function (positionEquiv.symm value))

theorem function_complete [Enumeration α] [Enumeration β] [DecidableEq α]
    (function : α → β) : function ∈ functionElements := by
  apply List.mem_map.mpr
  refine ⟨fun index => function (positionEquiv index),
    finFunctions_complete _ complete _ _, ?_⟩
  funext value
  exact congrArg function (positionEquiv.apply_symm_apply value)

/-- Deciding existence searches actual constructed finite function tables. -/
def functionExistsDecidable [Enumeration α] [Enumeration β] [DecidableEq α]
    (predicate : (α → β) → Prop) [DecidablePred predicate] :
    Decidable (∃ function, predicate function) :=
  decidable_of_iff ((functionElements (α := α) (β := β)).any
    (fun function => decide (predicate function)) = true) (by
      simp only [List.any_eq_true, decide_eq_true_eq]
      exact ⟨fun ⟨function, _, available⟩ => ⟨function, available⟩,
        fun ⟨function, available⟩ => ⟨function, function_complete function, available⟩⟩)

/-- Both function directions are searched before the inverse laws are checked. -/
def inverseCandidates [Enumeration α] [Enumeration β] [DecidableEq α] [DecidableEq β] :
    List ((α → β) × (β → α)) :=
  (functionElements (α := α) (β := β)).product (functionElements (α := β) (β := α))

theorem inverseCandidates_complete
    [Enumeration α] [Enumeration β] [DecidableEq α] [DecidableEq β]
    (maps : (α → β) × (β → α)) : maps ∈ inverseCandidates :=
  List.mem_product.mpr ⟨function_complete maps.1, function_complete maps.2⟩

def inverseExistsDecidable
    [Enumeration α] [Enumeration β] [DecidableEq α] [DecidableEq β]
    (predicate : ((α → β) × (β → α)) → Prop) [DecidablePred predicate] :
    Decidable (∃ maps, predicate maps) :=
  decidable_of_iff ((inverseCandidates (α := α) (β := β)).any
    (fun maps => decide (predicate maps)) = true) (by
      simp only [List.any_eq_true, decide_eq_true_eq]
      exact ⟨fun ⟨maps, _, available⟩ => ⟨maps, available⟩,
        fun ⟨maps, available⟩ => ⟨maps, inverseCandidates_complete maps, available⟩⟩)

def inverseWitness
    [Enumeration α] [Enumeration β] [DecidableEq α] [DecidableEq β]
    (predicate : ((α → β) × (β → α)) → Prop) [DecidablePred predicate]
    (available : ∃ maps, predicate maps) : {maps // predicate maps} :=
  witnessFromList inverseCandidates predicate (by
    obtain ⟨maps, property⟩ := available
    exact ⟨maps, inverseCandidates_complete maps, property⟩)

end Mettapedia.SetTheory.Profiles.ConstructiveFinite

namespace Mettapedia.SetTheory.Profiles.ConstructiveFinite

universe u v
variable {α : Type u} {β : Type v}

/-- A constructive cardinal bound; it splits a known list member and never
converts a finite quotient into a chosen enumeration. -/
theorem nodup_length_le_of_subset (first second : List α) (unique : first.Nodup)
    (contained : ∀ value, value ∈ first → value ∈ second) : first.length ≤ second.length := by
  induction first generalizing second with
  | nil => exact Nat.zero_le _
  | cons head tail previous =>
    obtain ⟨before, after, same⟩ := List.mem_iff_append.mp (contained head (List.mem_cons_self))
    subst second
    have remainder : ∀ value, value ∈ tail → value ∈ before ++ after := by
      intro value member
      have located := contained value (List.mem_cons_of_mem head member)
      simp only [List.mem_append, List.mem_cons] at located ⊢
      rcases located with inBefore | equal | inAfter
      · exact Or.inl inBefore
      · exact False.elim ((List.nodup_cons.mp unique).1 (equal ▸ member))
      · exact Or.inr inAfter
    have bound := previous (before ++ after) unique.of_cons remainder
    simp only [List.length_cons, List.length_append] at bound ⊢
    omega

theorem size_le_of_injective [Enumeration α] [Enumeration β]
    (function : α → β) (injective : Function.Injective function) :
    size (α := α) ≤ size (α := β) := by
  have unique := (nodup (α := α)).map injective
  have contained : ∀ value, value ∈ (elements (α := α)).map function →
      value ∈ elements (α := β) := fun value _ => complete value
  have bound := nodup_length_le_of_subset _ _ unique contained
  simpa only [size, List.length_map] using bound

theorem size_eq_of_equiv [Enumeration α] [Enumeration β] (equivalence : α ≃ β) :
    size (α := α) = size (α := β) :=
  Nat.le_antisymm (size_le_of_injective equivalence equivalence.injective)
    (size_le_of_injective equivalence.symm equivalence.symm.injective)

end Mettapedia.SetTheory.Profiles.ConstructiveFinite
