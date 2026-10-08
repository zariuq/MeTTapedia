import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.ExecutableWrittenCheckingControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.ExecutableTowerNumbersWeakHead

/-!
# Inspection, budget and checking controls

Weak-head reduction is separated from full reduction by retained redexes under
constructors and binders. A recursor forces its scrutinee but does not force an
unused method. The successful dependent judgments are reconstructed using the
weak-head procedure itself.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ExecutableWeakHeadControls

open TypedEquality.Normalization
open ExecutableCheckingControls (level rules num zero numeral copiedByRecursor)

def whnf (term : Tm Tower.Head 0) : Option (Tm Tower.Head 0) :=
  ExecutableWeakHead.value rules (ExecutableTowerNumbers.root level)
    ExecutableTowerNumbersWeakHead.plan 100 term

def test {n : Nat} (context : Ctx Tower.Head n) (term type : Tm Tower.Head n) : Bool :=
  ExecutableTowerNumbersWeakHead.accepts level 100 context term type

def sourceTest {n : Nat} (context : ExecutableWrittenChecking.SourceContext Tower.Head n)
    (term type : ATm Tower.Head n) : Bool :=
  ExecutableTowerNumbersWeakHead.acceptsSource level 100 context term type

def identityRedex {n : Nat} : Tm Tower.Head n := .app (.lam (.var 0)) zero

theorem beta_reduces : whnf identityRedex = some zero := by decide +kernel

theorem pair_fields_are_not_forced :
    whnf (.pair identityRedex identityRedex) = some (.pair identityRedex identityRedex) := by
  decide +kernel

theorem lambda_body_is_not_forced :
    whnf (.lam (identityRedex : Tm Tower.Head 1)) = some (.lam identityRedex) := by decide +kernel

theorem neutral_argument_is_not_forced :
    whnf (.app (.const `missing) identityRedex) = some (.app (.const `missing) identityRedex) := by
  decide +kernel

theorem projection_forces_its_returned_field :
    whnf (.fst (.pair identityRedex (.const `missing))) = some zero := by decide +kernel

theorem zero_case_does_not_force_unused_method :
    whnf (recApp TowerNumbersModel.numRec
      [.lam num, zero, .app (.const `missing) identityRedex] zero) = some zero := by decide +kernel

theorem recursor_forces_scrutinee :
    whnf (recApp TowerNumbersModel.numRec
      [.lam num, zero, .lam (.lam (.var 0))] identityRedex) = some zero := by decide +kernel

theorem returning_constructor_stops_reduction :
    whnf (copiedByRecursor 3) = some (ExecutableCheckingControls.succ (copiedByRecursor 2)) := by
  decide +kernel

theorem shared_budget_exhausts :
    ExecutableWeakHead.runValue rules (ExecutableTowerNumbers.root level)
      ExecutableTowerNumbersWeakHead.plan 2 (identityRedex : Tm Tower.Head 0) = none := by
  decide +kernel

theorem shared_budget_records_consumption :
    ExecutableWeakHead.runValue rules (ExecutableTowerNumbers.root level)
      ExecutableTowerNumbersWeakHead.plan 5 (identityRedex : Tm Tower.Head 0) = some (zero, 2) := by
  decide +kernel

theorem dependent_pack_accepted :
    test .nil ExecutableCheckingControls.pack ExecutableCheckingControls.packType = true := by
  decide +kernel

theorem wrong_endpoint_rejected :
    test .nil ExecutableCheckingControls.wrongPack ExecutableCheckingControls.packType = false := by
  decide +kernel

theorem polymorphic_identity_accepted :
    test .nil ExecutableCheckingControls.polymorphicId ExecutableCheckingControls.polymorphicIdType =
      true := by decide +kernel

theorem written_identity_accepted :
    sourceTest .nil ExecutableWrittenCheckingControls.writtenId
      ExecutableWrittenCheckingControls.idType = true := by decide +kernel

theorem written_domain_mismatch_rejected :
    sourceTest .nil ExecutableWrittenCheckingControls.wrongDomainId
      ExecutableWrittenCheckingControls.idType = false := by decide +kernel

theorem annotated_context_rejected :
    sourceTest ExecutableWrittenCheckingControls.invalidContext (.var 0)
      (ExecutableWrittenCheckingControls.sortA 0) = false := by decide +kernel

theorem recursor_accepted : test .nil (copiedByRecursor 3) num = true := by decide +kernel

theorem recursor_identity_checked :
    test .nil (.refl (copiedByRecursor 3)) (.id num (numeral 3) (numeral 3)) = true := by
  decide +kernel

/-- Source acceptance cannot be recovered from the erased term, even at one
fixed, formed expected type in this constructed model. -/
theorem source_checking_does_not_descend_through_erasure :
    ¬ ∃ readout : Tm Tower.Head 0 → Bool, ∀ source : ATm Tower.Head 0,
      readout source.erase = sourceTest .nil source ExecutableWrittenCheckingControls.idType := by
  rintro ⟨readout, agrees⟩
  have first := agrees ExecutableWrittenCheckingControls.writtenId
  have second := agrees ExecutableWrittenCheckingControls.wrongDomainId
  rw [written_identity_accepted] at first
  rw [written_domain_mismatch_rejected] at second
  rw [← ExecutableWrittenCheckingControls.erased_identities_agree, first] at second
  cases second

theorem accepted_dependent_source_has_annotated_typing :
    TypedEquality.ATyped rules .nil ExecutableWrittenCheckingControls.writtenId
      ExecutableWrittenCheckingControls.idType.erase :=
  ExecutableTowerNumbersWeakHead.acceptsSource_sound level written_identity_accepted

theorem written_identity_synthesis :
    ExecutableTowerNumbersWeakHead.inferSource level 100 .nil
      ExecutableWrittenCheckingControls.writtenId =
      some ExecutableWrittenCheckingControls.idType.erase := by decide +kernel

theorem malformed_domain_has_no_synthesized_type :
    ExecutableTowerNumbersWeakHead.inferSource level 100 .nil
      ExecutableWrittenCheckingControls.missingDomain = none := by decide +kernel

theorem synthesized_source_retains_context_formation :
    ExecutableWrittenChecking.SourceContext.Formed rules
      (.nil : ExecutableWrittenChecking.SourceContext Tower.Head 0) ∧
    TypedEquality.ATyped rules .nil ExecutableWrittenCheckingControls.writtenId
      ExecutableWrittenCheckingControls.idType.erase :=
  ExecutableTowerNumbersWeakHead.inferSource_sound level written_identity_synthesis

end ExecutableWeakHeadControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
