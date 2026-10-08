import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedSetTheory
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedDeductionControls

/-!
# Future union, retained occurrences and unbounded infinity controls

Current double members do not suffice to construct a future union. The
counterexample has a node carrier growing at every stage and edges that
appear later. Distinct pair occurrences remain literal receipts even
when their material values agree. The ordinal arguments are unbounded:
matching distinguishes every two different finite ordinals, and the
constructed infinity matches none of them.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedSetControls

open CategoryTheory ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphRealizedSetConstructors
open ContextualGraphRealizedDeductionControls (growing root lateMember)

universe u
variable {D : Type u} [Category.{u} D]

/-- This candidate deliberately keeps only the double members visible
at construction. The theorem below separates it from the actual union. -/
def presentOnlyUnion {point : D} (parent : Value D point) : Value D point :=
  enumeration (fun receipt : Σ first : Child D parent, Child D (childValue D parent first) =>
    childValue D (childValue D parent receipt.1) receipt.2)

theorem current_union_has_no_member (value : Value Nat 0) :
    ¬ Nonempty (Member value (union (root 0))) := by
  rintro ⟨proof⟩
  let moved := Member.transportParent (Equal.ofEq (move_identity Nat 0 (union (root 0))).symm) proof
  let decoded := unionEliminate (root 0) (𝟙 0) moved
  exact Nat.not_lt_zero 0 decoded.2.1.1.property

theorem present_only_union_never_gains_members {target : Nat} (path : 0 ⟶ target)
    (value : Value Nat target) :
    ¬ Nonempty (Member value (move Nat path (presentOnlyUnion (root 0)))) := by
  rintro ⟨proof⟩
  let decoded := enumerationEliminate _ path proof
  exact Nat.not_lt_zero 0 decoded.1.1.property

def futureUnionMember :
    Member (root 1) (move Nat (homOfLE (by decide : 0 ≤ 1)) (union (root 0))) :=
  unionIntro (root 0) (homOfLE (by decide : 0 ≤ 1))
    (lateMember 1 (by decide)) (lateMember 1 (by decide))

theorem future_union_is_not_present_only :
    ¬ Nonempty (Equal (union (root 0)) (presentOnlyUnion (root 0))) := by
  rintro ⟨same⟩
  let arrival : 0 ⟶ 1 := homOfLE (by decide)
  exact present_only_union_never_gains_members arrival (root 1)
    ⟨Member.transportParent (same.restrict arrival) futureUnionMember⟩

theorem same_current_members_do_not_determine_future_set :
    (∀ value : Value Nat 0, ¬ Nonempty (Member value (union (root 0)))) ∧
    (∀ value : Value Nat 0, ¬ Nonempty (Member value (presentOnlyUnion (root 0)))) ∧
    ¬ Nonempty (Equal (union (root 0)) (presentOnlyUnion (root 0))) := by
  refine ⟨current_union_has_no_member, ?_, future_union_is_not_present_only⟩
  intro value member
  exact present_only_union_never_gains_members (𝟙 0) value
    (member.map (Member.transportParent (Equal.ofEq (move_identity Nat 0 (presentOnlyUnion (root 0))).symm)))

theorem duplicate_pair_occurrences_remain_distinct :
    (pairFirst (𝟙 1) (root 1) (root 1)).1 ≠ (pairSecond (𝟙 1) (root 1) (root 1)).1 := by
  intro same
  have labels := congrArg (fun receipt => match receipt.val with
    | .inl _ => none
    | .inr node => some node.1.down) same
  change some false = some true at labels
  cases labels

theorem every_finite_ordinal_is_distinguished (point : D) (first second : Nat) :
    Nonempty (Equal (ordinal point first) (ordinal point second)) ↔ first = second :=
  ordinal_matching_iff point first second

theorem infinity_is_not_finite (point : D) (bound : Nat) :
    ¬ Nonempty (Equal (infinity point) (ordinal point bound)) := by
  rintro ⟨same⟩
  exact ordinal_irreflexive point bound
    (Member.transportParent same (infinityIntro bound (Equal.refl (ordinal point bound))))

theorem infinity_has_arbitrarily_many_distinct_members (point : D) (bound : Nat) :
    (∀ index : Fin bound, Nonempty (Member (ordinal point index.val) (infinity point))) ∧
    (∀ first second : Fin bound,
      Nonempty (Equal (ordinal point first.val) (ordinal point second.val)) → first = second) := by
  constructor
  · intro index
    exact ⟨infinityIntro index.val (Equal.refl _)⟩
  · intro first second same
    exact Fin.ext ((ordinal_matching_iff point first.val second.val).mp same)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedSetControls
