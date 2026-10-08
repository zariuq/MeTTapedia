import Mettapedia.TypeTheory.PresheafNativeLogicalCells
import Mettapedia.TypeTheory.PresheafNativeClosedSubstitution
import Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfTransformationControls
import Mettapedia.TypeTheory.DisplayedPresheafClassifierCoherenceControls
import Mettapedia.TypeTheory.NativeLocalTheoryRestrictionControls

/-!
# Complete native logical-action controls

A genuine theory arrow changes both supplied witnesses of a native sum.
A second coherent arrow resets both witnesses, so coherence does not entail
injectivity. The native sieve cell gives a proper inclusion, and a world
exchange changes the fibre of a varying finite native family. Every display
arrow still retains its full contextual substitution in the slice.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativeLogicalActionControls

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice
open DisplayedPresheafSliceSubstitution DisplayedPresheafTheoryRestriction
open ContextualLocalUniverses NativeLocalTypeFormers NativeLocalTheoryRestriction
open NativeLocalTheoryTransformation NativeLocalDisplayComparisons
open PresheafNativeLogicalAction PresheafNativeLogicalCells
open DisplayedPresheafTheoryCwfControls
open DisplayedPresheafTheoryCwfTransformationControls (increment reset)

local instance nativeDisplayCategory {K : Type} [Category K] (P : Kᵒᵖ ⥤ Type) :
    Category.{0} (TypeOver (localCwf (DisplayedPresheafCwf.presheafCwf.{0, 0, 0} K)) P) :=
  TypeOver.instCategory (C := localCwf (DisplayedPresheafCwf.presheafCwf.{0, 0, 0} K)) (Γ := P)

abbrev argument : NativeType base := LocalType.present witnesses
abbrev evidence : NativeType (totalSpace argument.decoded) :=
  LocalType.present (reindexDisplayed (totalProjection witnesses) witnesses)

def callerWorld : Callersᵒᵖ := Opposite.op (Discrete.mk ())

noncomputable def incomingDecoder :=
  sumDecoderTotal (selectOne.op ⋙ base) (restrict selectOne argument)
    (body selectOne argument evidence)

noncomputable def outgoingDecoder :=
  sumDecoderTotal (selectZero.op ⋙ base) (restrict selectZero argument)
    (body selectZero argument evidence)

def suppliedPair (first second : Nat) :
    (totalSpace (DisplayedPresheafSigma.sigmaDisplayed
      (restrictFamily selectOne base argument.decoded)
      ((DisplayedPresheafTheoryRestrictionAction.codomainFunctor selectOne base
        argument.decoded).obj evidence.decoded))).obj callerWorld :=
  ⟨PUnit.unit, ⟨first, second⟩⟩

noncomputable def suppliedNativePair (first second : Nat) :=
  incomingDecoder.inv.app callerWorld (suppliedPair first second)

noncomputable def nativePairReadout (change : selectZero ⟶ selectOne)
    (first second : Nat) :=
  outgoingDecoder.hom.app callerWorld
    ((sumCell change base argument evidence).app callerWorld
      (suppliedNativePair first second))

theorem readout_is_actual_pair_transport (change : selectZero ⟶ selectOne)
    (first second : Nat) :
    nativePairReadout change first second =
      (DisplayedPresheafSumTransformationCoherence.sumTotalMap change base
        argument.decoded evidence.decoded).app callerWorld (suppliedPair first second) := by
  have square := ConcreteCategory.congr_hom
    (NatTrans.congr_app (sum_cell_decoder change base argument evidence) callerWorld)
      (suppliedNativePair first second)
  have cancellation := ConcreteCategory.congr_hom
    (incomingDecoder.inv_hom_id_app callerWorld) (suppliedPair first second)
  change incomingDecoder.hom.app callerWorld (suppliedNativePair first second) =
    suppliedPair first second at cancellation
  exact square.trans (congrArg
    ((DisplayedPresheafSumTransformationCoherence.sumTotalMap change base
      argument.decoded evidence.decoded).app callerWorld) cancellation)

/-- Both witnesses follow the supplied nonidentity theory arrow. -/
theorem increment_reads_both_witnesses (first second : Nat) :
    nativePairReadout increment first second =
      (⟨PUnit.unit, ⟨Nat.succ first, Nat.succ second⟩⟩ :
        (totalSpace (DisplayedPresheafSigma.sigmaDisplayed
          (restrictFamily selectZero base argument.decoded)
          ((DisplayedPresheafTheoryRestrictionAction.codomainFunctor selectZero base
            argument.decoded).obj evidence.decoded))).obj callerWorld) := by
  rw [readout_is_actual_pair_transport]
  rfl

theorem reset_reads_both_witnesses (first second : Nat) :
    nativePairReadout reset first second =
      (⟨PUnit.unit, ⟨(1 : Nat), (1 : Nat)⟩⟩ :
        (totalSpace (DisplayedPresheafSigma.sigmaDisplayed
          (restrictFamily selectZero base argument.decoded)
          ((DisplayedPresheafTheoryRestrictionAction.codomainFunctor selectZero base
            argument.decoded).obj evidence.decoded))).obj callerWorld) := by
  rw [readout_is_actual_pair_transport]
  rfl

theorem equal_programs_do_not_determine_evidence :
    (nativePairReadout increment 1 3).1 = (nativePairReadout reset 1 3).1 ∧
      (nativePairReadout increment 1 3).2.2 ≠ (nativePairReadout reset 1 3).2.2 := by
  rw [increment_reads_both_witnesses, reset_reads_both_witnesses]
  constructor
  · rfl
  · change (4 : Nat) ≠ 1
    decide

theorem coherent_reset_forgets_distinct_pairs :
    nativePairReadout reset 0 3 = nativePairReadout reset 1 4 := by
  rw [reset_reads_both_witnesses, reset_reads_both_witnesses]

namespace Truth

open DisplayedPresheafClassifierCoherenceControls
open DependentProductRestrictionControls (properFuture)

abbrev propositionBase := DisplayedPresheafClassifierCoherenceControls.base

def receipt : (totalSpace (restrict later (nativeTruth propositionBase)).decoded).obj callerWorld :=
  ⟨PUnit.unit, properFuture⟩

def direct : Sieve (Discrete.mk ()) :=
  ((truthDisplay later propositionBase).substitution.app callerWorld receipt).2
def viaCell : Sieve (Discrete.mk ()) :=
  ((truthDisplay earlier propositionBase).substitution.app callerWorld
  ((completeCell advance propositionBase (nativeTruth propositionBase)).app callerWorld receipt)).2

theorem direct_bottom : direct = ⊥ :=
  DisplayedPresheafClassifierCoherenceControls.direct_bottom

theorem viaCell_top : viaCell = ⊤ :=
  DisplayedPresheafClassifierCoherenceControls.throughChange_top

theorem actual_native_inclusion : direct ≤ viaCell :=
  truth_cell_lax advance propositionBase callerWorld receipt

/-- The actual native complete cell does not turn the classifier's
noninvertible comparison into an equality. -/
theorem native_square_is_proper : direct ≠ viaCell := by
  rw [direct_bottom, viaCell_top]
  intro same
  have member : (⊤ : Sieve (Discrete.mk ())).arrows (𝟙 (Discrete.mk ())) := trivial
  have bottomMember : (⊥ : Sieve (Discrete.mk ())).arrows (𝟙 (Discrete.mk ())) :=
    same.symm ▸ member
  exact bottomMember

end Truth

namespace WorldChange

open NativeLocalTheoryRestrictionControls

def actualMappedDomain : NativeType (exchange.functor.op ⋙ NativeLocalTheoryRestrictionControls.base) :=
  (localMorphism exchange.functor).mapType domain

/-- The actual structured native action changes a varying fibre. -/
theorem action_reads_exchanged_fibre :
    actualMappedDomain.decoded.obj
      ⟨falseWorld, PUnit.unit⟩ = Fin 2 := rfl

theorem world_change_cannot_be_omitted :
    actualMappedDomain.decoded.obj
      ⟨falseWorld, PUnit.unit⟩ ≠ domain.decoded.obj ⟨falseWorld, PUnit.unit⟩ :=
  omitting_the_world_change_changes_the_type

/-- The canonical native display map and its slice image preserve
the same complete contextual substitution. -/
theorem exchanged_sum_slice_map :
    ((PresheafNativeClosedSubstitution.toSlice (exchange.functor.op ⋙ base)).map
      (sumDisplayIso exchange.functor domain codomain).hom).left =
        totalHom (sumIso exchange.functor domain codomain).hom := rfl

theorem omitted_future_arrows_can_identify_functions :
    ¬ Function.Injective
      (DependentProductRestriction.restrictSection
        DependentProductRestrictionControls.initialWorld
        DependentProductRestrictionControls.argumentFamily
        DependentProductRestrictionControls.evidenceFamily
        (X := Discrete.mk ())) :=
  unrestricted_future_restriction_is_not_injective

end WorldChange

end Mettapedia.TypeTheory.PresheafNativeLogicalActionControls
