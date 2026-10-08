import Mettapedia.TypeTheory.PresheafNativeRefinementCells
import Mettapedia.TypeTheory.PresheafNativePropositionRestriction
import Mettapedia.TypeTheory.PresheafNativePredicateLogicalRestriction
import Mettapedia.TypeTheory.NativeLocalTheoryRestrictionControls
import Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfTransformationControls
import Mettapedia.TypeTheory.DisplayedPresheafClassifierCoherenceControls

/-!
# Witness and world controls for native predicate theory action

A world exchange changes a varying finite native fibre and transports a
proper selected inhabitant through the new native refinement comparison.
Actual nonidentity theory cells increment or reset a retained witness.
A proper future sieve distinguishes the two paths of the new ordinary
native proposition comparison, so the general cell square is genuinely lax.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.PresheafNativePredicateLogicalRestrictionControls

open _root_.CategoryTheory
open Mettapedia.GSLT.Topos
open DisplayedPresheafTransport DisplayedPresheafComprehension
open ContextualLocalUniverses NativeLocalTypeFormers NativeLocalTheoryRestriction
open PresheafNativePropositionReadout PresheafNativeStableRefinement

namespace Worlds

open NativeLocalTheoryRestrictionControls

def selected : Subfunctor (totalSpace domain.decoded) where
  obj _ := {receipt | receipt.2.val = 1}
  map _ _ holds := holds

noncomputable def incomingDecoder :=
  (DisplayedPresheafTheoryRestrictionAction.restrictionFunctor exchange.functor base).mapIso
    (decodeIso domain selected)

def supplied : (PresheafNativePredicateRefinement.displayed domain.decoded selected).obj
    ⟨trueWorld, PUnit.unit⟩ := ⟨(⟨1, by decide⟩ : Fin 2), rfl⟩

noncomputable def nativeSource := incomingDecoder.inv.app ⟨falseWorld, PUnit.unit⟩ supplied

noncomputable def decoded :
    (PresheafNativePredicateRefinement.displayed (restrict exchange.functor domain).decoded
      (PresheafNativeRefinementRestriction.predicate exchange.functor domain selected)).obj
        ⟨falseWorld, PUnit.unit⟩ :=
  (decodeIso (restrict exchange.functor domain)
    (PresheafNativeRefinementRestriction.predicate exchange.functor domain selected)).hom.app
      ⟨falseWorld, PUnit.unit⟩
      ((PresheafNativeRefinementRestriction.comparison exchange.functor domain selected).hom.app
        ⟨falseWorld, PUnit.unit⟩ nativeSource)

/-- The actual native comparison recovers the supplied dependent
inhabitant from the changed world, rather than validating its own definition. -/
theorem actual_world_refinement_readout : decoded.val = (⟨1, by decide⟩ : Fin 2) := by
  have square := ConcreteCategory.congr_hom (NatTrans.congr_app
    (PresheafNativeRefinementRestriction.decoder_square exchange.functor domain selected)
    ⟨falseWorld, PUnit.unit⟩) nativeSource
  have cancel := ConcreteCategory.congr_hom
    (incomingDecoder.inv_hom_id_app ⟨falseWorld, PUnit.unit⟩) supplied
  change incomingDecoder.hom.app ⟨falseWorld, PUnit.unit⟩ nativeSource = supplied at cancel
  change decoded = (PresheafNativeRefinementRestriction.subtypeIso
    exchange.functor domain selected).hom.app ⟨falseWorld, PUnit.unit⟩
      (incomingDecoder.hom.app ⟨falseWorld, PUnit.unit⟩ nativeSource) at square
  rw [cancel] at square
  exact congrArg Subtype.val square

theorem target_membership_retained : decoded.val.val = 1 := decoded.property

theorem original_world_has_no_selected_inhabitant :
    ¬ Nonempty ((PresheafNativePredicateRefinement.displayed domain.decoded selected).obj
      ⟨falseWorld, PUnit.unit⟩) := by
  rintro ⟨value⟩
  have bound : value.val.val < 1 := value.val.isLt
  have chosen : value.val.val = 1 := value.property
  rw [chosen] at bound
  exact Nat.lt_irrefl 1 bound

theorem omitted_world_has_the_wrong_fibre :
    (restrict exchange.functor domain).decoded.obj ⟨falseWorld, PUnit.unit⟩ ≠
      domain.decoded.obj ⟨falseWorld, PUnit.unit⟩ :=
  omitting_the_world_change_changes_the_type

theorem exchange_supplies_future_coverage :
    LogicalTransport.LiftsRestrictions exchange.functor :=
  PresheafNativePredicateLogicalRestriction.equivalence_lifts exchange.functor

end Worlds

namespace Evidence

open DisplayedPresheafTheoryCwfControls
open DisplayedPresheafTheoryCwfTransformationControls (increment reset)

abbrev argument : NativeType base := LocalType.present witnesses
def world : Callersᵒᵖ := Opposite.op (Discrete.mk ())

noncomputable def supplied (number : Nat) :=
  (completeIso (restrict selectOne argument)
    (PresheafNativeRefinementRestriction.predicate selectOne argument ⊤)).inv.app world
      ⟨⟨PUnit.unit, number⟩, trivial⟩

noncomputable def readout (change : selectZero ⟶ selectOne) (number : Nat) :=
  (forgetComplete (restrict selectZero argument)
    (PresheafNativeRefinementRestriction.predicate selectZero argument ⊤)).app world
      ((PresheafNativeRefinementCells.cell change argument ⊤).app world (supplied number))

theorem whole_cell_readout (change : selectZero ⟶ selectOne) (number : Nat) :
    readout change number =
      (PresheafNativeLogicalCells.completeCell change base argument).app world
        (⟨PUnit.unit, number⟩ : (totalSpace (restrict selectOne argument).decoded).obj world) := by
  have square := ConcreteCategory.congr_hom (NatTrans.congr_app
    (PresheafNativeRefinementCells.cell_forget change argument ⊤) world) (supplied number)
  have cancellation := ConcreteCategory.congr_hom
    ((completeIso (restrict selectOne argument)
      (PresheafNativeRefinementRestriction.predicate selectOne argument ⊤)).inv_hom_id_app world)
        ⟨⟨PUnit.unit, number⟩, trivial⟩
  change (completeIso (restrict selectOne argument)
    (PresheafNativeRefinementRestriction.predicate selectOne argument ⊤)).hom.app world
      (supplied number) = ⟨⟨PUnit.unit, number⟩, trivial⟩ at cancellation
  change readout change number =
    (PresheafNativeLogicalCells.completeCell change base argument).app world
      ((completeIso (restrict selectOne argument)
        (PresheafNativeRefinementRestriction.predicate selectOne argument ⊤)).hom.app
          world (supplied number)).val at square
  rw [cancellation] at square
  exact square

theorem increment_retains_changed_witness (number : Nat) :
    (readout increment number).2 = Nat.succ number := by
  rw [whole_cell_readout]
  rfl

theorem reset_retains_actual_witness (number : Nat) :
    (show Nat from (readout reset number).2) = 1 := by
  rw [whole_cell_readout]
  rw [PresheafNativeLogicalCells.completeCell_decodes]
  rfl

theorem equal_programs_do_not_determine_selected_evidence :
    (readout increment 1).1 = (readout reset 1).1 ∧
      (readout increment 1).2 ≠ (readout reset 1).2 := by
  constructor
  · change PUnit.unit = PUnit.unit
    rfl
  · intro same
    have contradiction : Nat.succ 1 = 1 :=
      (increment_retains_changed_witness 1).symm.trans
        (same.trans (reset_retains_actual_witness 1))
    exact Nat.succ_ne_self 1 contradiction

end Evidence

namespace Truth

open DisplayedPresheafClassifierCoherenceControls
open DependentProductRestrictionControls (properFuture)

def world := point.1
def receipt : (totalSpace (restrict later (nativeOmega base)).decoded).obj world :=
  ⟨PUnit.unit, properFuture⟩

def direct : Sieve world.unop :=
  ((PresheafNativePropositionRestriction.displayComparison later base).substitution.app world receipt).2
def throughCell : Sieve world.unop :=
  ((PresheafNativePropositionRestriction.displayComparison earlier base).substitution.app world
    ((PresheafNativeLogicalCells.completeCell advance base (nativeOmega base)).app world receipt)).2

theorem native_ordinary_inclusion : direct ≤ throughCell :=
  PresheafNativePropositionRestriction.cell_lax advance base world receipt

theorem native_ordinary_square_is_proper : direct ≠ throughCell := by
  change DisplayedPresheafClassifierCoherenceControls.direct ≠
    DisplayedPresheafClassifierCoherenceControls.throughChange
  exact comparison_square_not_equal

end Truth

end Mettapedia.TypeTheory.PresheafNativePredicateLogicalRestrictionControls
