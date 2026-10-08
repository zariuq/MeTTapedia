import Mettapedia.TypeTheory.DisplayedPresheafTheoryTransformationCoherence
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Witness-sensitive controls for theory transformations

Two parallel theory changes have identical base-value maps, but one
increments the supplied witness and the other resets it. A nonidentity
postcomposition exchanges those arrows. The canonical horizontal action
therefore computes a different result while retaining its composition law.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafTheoryTransformationCoherenceControls

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.Limits
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafTheoryRestriction DisplayedPresheafTheoryTransformation
open DisplayedPresheafTheoryRestrictionAction DisplayedPresheafTheoryTransformationCoherence

abbrev Callers := Discrete Unit
abbrev Worlds := WalkingParallelPair

def before : Callers ⥤ Worlds := (Functor.const Callers).obj .zero
def after : Callers ⥤ Worlds := (Functor.const Callers).obj .one

def increment : before ⟶ after := (Functor.const Callers).map WalkingParallelPairHom.left
def reset : before ⟶ after := (Functor.const Callers).map WalkingParallelPairHom.right

def base : Worldsᵒᵖ ⥤ Type := (Functor.const _).obj PUnit

/-- This diagram is not constant: its parallel witness maps are successor
and reset, although its two object carriers coincide. -/
def witnessDiagram : Worlds ⥤ Type :=
  parallelPair (TypeCat.ofHom Nat.succ) (TypeCat.ofHom (fun (_ : Nat) => 1))

def witnesses : DisplayedFamily base :=
  CategoryOfElements.π base ⋙ walkingParallelPairOpEquiv.inverse ⋙ witnessDiagram

def supplied (value : Nat) :
    (totalSpace (restrictFamily after base witnesses)).obj (Opposite.op (Discrete.mk ())) :=
  ⟨PUnit.unit, value⟩

theorem increment_computes (value : Nat) :
    (totalEvidenceMap increment base witnesses).app (Opposite.op (Discrete.mk ()))
      (supplied value) = ⟨PUnit.unit, Nat.succ value⟩ := rfl

theorem reset_computes (value : Nat) :
    (totalEvidenceMap reset base witnesses).app (Opposite.op (Discrete.mk ()))
      (supplied value) = ⟨PUnit.unit, (1 : Nat)⟩ := rfl

theorem base_maps_agree : baseMap increment base = baseMap reset base := by
  ext world value
  rfl

theorem witness_maps_differ :
    totalEvidenceMap increment base witnesses ≠ totalEvidenceMap reset base witnesses := by
  intro same
  have values := congrArg (fun map =>
    (map.app (Opposite.op (Discrete.mk ())) (supplied 1)).2) same
  exact Nat.succ_ne_self 1 values

/-- Equality of the base action does not identify the displayed witness
action or turn a theory transformation into an invertible comparison. -/
theorem base_equality_does_not_determine_evidence :
    baseMap increment base = baseMap reset base ∧
      totalEvidenceMap increment base witnesses ≠ totalEvidenceMap reset base witnesses :=
  ⟨base_maps_agree, witness_maps_differ⟩

theorem reset_is_not_injective :
    ¬ Function.Injective
      ((totalEvidenceMap reset base witnesses).app (Opposite.op (Discrete.mk ()))) := by
  intro injective
  have equal : supplied 0 = supplied 1 := injective (by
    rw [reset_computes, reset_computes])
  have numbers := congrArg (fun receipt => receipt.2) equal
  exact Nat.zero_ne_one numbers

/-- An actual nonidentity functor exchanges the two authored arrows. -/
def exchange : Worlds ⥤ Worlds where
  obj := id
  map arrow := by
    cases arrow
    · exact WalkingParallelPairHom.right
    · exact WalkingParallelPairHom.left
    · exact WalkingParallelPairHom.id _
  map_id world := by cases world <;> rfl
  map_comp first second := by cases first <;> cases second <;> rfl

theorem exchanges_the_change : whiskerRight increment exchange = reset := by
  ext caller
  rfl

/-- Postcomposition really changes the computed witness, and agrees with
the independent staged displayed action. -/
theorem horizontal_action_computes (value : Nat) :
    ((totalTransformation (whiskerRight increment exchange) base).app witnesses).app
      (Opposite.op (Discrete.mk ())) (supplied value) = ⟨PUnit.unit, (1 : Nat)⟩ := by
  rw [exchanges_the_change]
  exact reset_computes value

theorem horizontal_and_staged_agree :
    totalTransformation (whiskerRight increment exchange) base =
      whiskerLeft (restrictionFunctor exchange base)
        (totalTransformation increment (exchange.op ⋙ base)) :=
  totalTransformation_whiskerRight increment exchange base

/-- A nonconstant contextual term supplies zero at the upper world and
one at the lower world; both authored routes preserve its coherence. -/
def contextualTerm : witnesses.sections where
  val point := by
    rcases point with ⟨⟨world⟩, value⟩
    cases world
    · exact (1 : Nat)
    · exact (0 : Nat)
  property := by
    rintro ⟨⟨first⟩, x⟩ ⟨⟨second⟩, y⟩ ⟨⟨route⟩, follows⟩
    change PUnit at x y
    cases x
    cases y
    cases first <;> cases second <;> cases route <;> rfl

theorem actual_term_transport :
    sectionLift (restrictFamily after base witnesses)
        (restrictTerm after base witnesses contextualTerm) ≫
        totalEvidenceMap increment base witnesses =
      baseMap increment base ≫
        sectionLift (restrictFamily before base witnesses)
          (restrictTerm before base witnesses contextualTerm) :=
  totalEvidenceMap_term increment base witnesses contextualTerm

end Mettapedia.TypeTheory.DisplayedPresheafTheoryTransformationCoherenceControls
