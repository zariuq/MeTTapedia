import Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedPublication

/-! # Initialization from one explicit root context and public request data -/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedGenesis

open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open InferenceSchemaActivation (Tm action)
open HOLLightContextLicensing
open HOLLightLicensedActivation
open HOLLightLicensedValues

universe uO
variable {O : Type uO}

/-- Initial rows consist of public data and the explicitly authorized single
context token. No theorem or unrelated context is a trusted initial fact. -/
def Genesis (root : Nat) (location : O → Location) (payload : O → Tm)
    (state : Configuration Value O) : Prop :=
  ∀ occurrence ∈ state.present, location occurrence = requests ∨
    location occurrence = licenses ∧ payload occurrence = available root

theorem genesis_valid (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (contexts : Nat → TheoryContext) (root : Nat) (rootContext : contexts root = initial)
    (location : O → Location) (payload : O → Tm) (state : Configuration Value O)
    (genesis : Genesis root location payload state) :
    HOLLightLicensedPublication.Valid initial policy contexts location payload state := by
  intro assignment _ occurrence present
  rcases genesis occurrence present with publicHere | ⟨privateHere, rootHere⟩
  · rw [publicHere]
    exact meaning_request initial policy contexts _
  · rw [privateHere, rootHere, available_fixed]
    apply meaning_available
    rw [rootContext]
    exact initial_licensed initial policy

theorem genesis_has_no_theorems (root : Nat) (location : O → Location) (payload : O → Tm)
    (state : Configuration Value O) (genesis : Genesis root location payload state)
    (occurrence : O) (present : occurrence ∈ state.present) : location occurrence ≠ judgments := by
  rcases genesis occurrence present with publicHere | ⟨privateHere, _⟩
  · simp [publicHere, requests, judgments]
  · simp [privateHere, licenses, judgments]

theorem genesis_has_only_root_context (root : Nat) (location : O → Location) (payload : O → Tm)
    (state : Configuration Value O) (genesis : Genesis root location payload state)
    (occurrence : O) (present : occurrence ∈ state.present)
    (privateHere : location occurrence = licenses) (context : Nat)
    (atContext : payload occurrence = available context) : context = root := by
  rcases genesis occurrence present with publicHere | ⟨_, rootHere⟩
  · rw [privateHere] at publicHere
    cases publicHere
  · exact available_injective (atContext.symm.trans rootHere)

end Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedGenesis
