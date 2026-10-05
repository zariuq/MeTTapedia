import Mettapedia.GSLT.Logic.RhoBagReactiveSystem
import Mettapedia.OSLF.StructuralModal.SeparatingConjunction

/-!
# Rho's equation-relative cut and its resource algebra

The existing canonical component map identifies pure rho's structural classes
with bags of reactive components. The equation-relative OSLF cut is exactly the
separating conjunction of these bags, including atom-sensitive predicates.
Every resource partition used by the backward direction is realized by actual
parallel terms. No exclusive ownership or transition locality is inferred from
this spatial comparison.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Bridges.GSLT.RhoSeparation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.GSLT.RhoBagReactiveSystem
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.OSLF.StructuralModal.SeparatingConjunction

theorem components_parallel_append (left right : List Pattern) :
    components (.collection .hashBag (left ++ right) none) =
      components (.collection .hashBag left none) +
        components (.collection .hashBag right none) := by
  simp only [components_parallel, List.map_append, List.sum_append]

/-- A selected part of the canonical resource bag is itself realized by a
parallel process, with precisely those occurrences. -/
theorem components_rebuild_subbag {process : Pattern} {part : Multiset Pattern}
    (contained : part ≤ components process) :
    components (.collection .hashBag part.toList none) = part := by
  rw [components_parallel, sum_map_components_of_le]
  · exact Multiset.coe_toList part
  · simpa only [Multiset.coe_toList] using contained

/-- Every resource decomposition is an actual equation-relative process cut. -/
theorem split_realized {process : Pattern} {left right : Multiset Pattern}
    (split : components process = left + right) :
    StructuralCongruence process
      (.collection .hashBag (left.toList ++ right.toList) none) ∧
      components (.collection .hashBag left.toList none) = left ∧
      components (.collection .hashBag right.toList none) = right := by
  have leftContained : left ≤ components process := by
    rw [split]
    exact Multiset.le_add_right _ _
  have rightContained : right ≤ components process := by
    rw [split]
    exact Multiset.le_add_left _ _
  have first := components_rebuild_subbag leftContained
  have second := components_rebuild_subbag rightContained
  refine ⟨structuralCongruence_of_components_eq ?_, first, second⟩
  rw [components_parallel_append, first, second, split]

/-- The existing OSLF cut, read modulo rho's equations, is precisely the
existing bag separation algebra's connective. -/
theorem sepConj_iff_components (P Q : Multiset Pattern → Prop)
    {process : Pattern} (pure : HashSetFree process) :
    SepConj StructuralCongruence .hashBag (fun term => P (components term))
      (fun term => Q (components term)) process ↔
        sepConj P Q (components process) := by
  constructor
  · rintro ⟨left, right, related, first, second⟩
    have pureTarget := (hashSetFree_iff_of_structuralCongruence related).mp pure
    have decomposition := components_eq_of_structuralCongruence pure pureTarget related
    rw [components_parallel_append] at decomposition
    exact ⟨components (.collection .hashBag left none),
      components (.collection .hashBag right none), trivial, decomposition, first, second⟩
  · rintro ⟨left, right, _, split, first, second⟩
    obtain ⟨related, leftImage, rightImage⟩ := split_realized split
    exact ⟨left.toList, right.toList, related,
      by simpa only [leftImage] using first,
      by simpa only [rightImage] using second⟩

/-- Component predicates are legitimate observations of the pure structural
class rather than of a chosen ordering of its parallel presentation. -/
theorem componentPredicate_invariant (P : Multiset Pattern → Prop)
    {first second : Pattern} (firstPure : HashSetFree first) (secondPure : HashSetFree second)
    (related : StructuralCongruence first second) :
    P (components first) ↔ P (components second) := by
  rw [components_eq_of_structuralCongruence firstPure secondPure related]

/-- The spatial cut is symmetric even for predicates that inspect the
particular communicating atoms. -/
theorem sepConj_comm (P Q : Multiset Pattern → Prop)
    {process : Pattern} (pure : HashSetFree process) :
    SepConj StructuralCongruence .hashBag (fun term => P (components term))
      (fun term => Q (components term)) process ↔
    SepConj StructuralCongruence .hashBag (fun term => Q (components term))
      (fun term => P (components term)) process := by
  rw [sepConj_iff_components P Q pure, sepConj_iff_components Q P pure,
    Mettapedia.GSLT.SeparationAlgebra.sepConj_comm]

end Mettapedia.OSLF.Bridges.GSLT.RhoSeparation
