import Mettapedia.Logic.TierZero.Adequacy.HOLLightChronologyObservation
import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextInstallationControls

/-!
# Logical licensing is strictly weaker than exact-cache history licensing

An actual type command can be justified by its one selected existence proof
while an unused public cache entry is fabricated falsity. That public cache
cannot be the cache of any licensed semantic frame. Requiring a full-state
snapshot for the logical observation would therefore reject a harmless input.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightChronologyControls

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.TypeFamilySemantics
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open ProofExecution.Registered.Controls
open DefinitionAdapters.ContextControls
open HOLLightContextLicensing
open HOLLightContextControls.TypeDefinition

local instance : DecidablePred emptyAxiomPolicy := fun _ => .isFalse id

theorem actual_type_history_licenses_context : Licensed coreContext emptyAxiomPolicy definedType.context :=
  HOLLightChronologyObservation.reachable_licensed coreContext emptyAxiomPolicy definition_history_reachable

theorem unused_false_row_does_not_block_logical_admission :
    Admitted emptyAxiomPolicy coreContext definedType.context := by
  refine ⟨typeCommand, #[identityExistence, falseExistence], output,
    HOLLightContextInstallationControls.unused_public_false_row_changes_no_local_check.trans command_checked, rfl, ?_⟩
  intro index cited fact found
  have indexSame : index = 0 := by simpa [Command.parents, typeCommand] using cited
  subst index
  have same : identityExistence = fact := Option.some.inj found
  subst fact
  exact withExistence_valid identityExistence (by simp [withExistence])

universe w

theorem unused_false_cache_has_no_licensed_frame (initial context : TheoryContext) (policy : AxiomPolicy) :
    ¬Nonempty (RegisteredReplayModels.Frame.{w} initial policy context #[identityExistence, falseExistence]) := by
  rintro ⟨frame⟩
  apply frame.cached_falsity_refused (fun _ _ => proposition) (fun _ => proposition) falseExistence rfl
    PrimitiveSentences.falsityDB_translates
  simp

theorem logical_admission_does_not_imply_full_cache_license :
    Admitted emptyAxiomPolicy coreContext definedType.context ∧
      ¬Nonempty (RegisteredReplayModels.Frame.{0} coreContext emptyAxiomPolicy coreContext
        #[identityExistence, falseExistence]) :=
  ⟨unused_false_row_does_not_block_logical_admission, unused_false_cache_has_no_licensed_frame _ _ _⟩

end Mettapedia.Logic.TierZero.Adequacy.HOLLightChronologyControls
