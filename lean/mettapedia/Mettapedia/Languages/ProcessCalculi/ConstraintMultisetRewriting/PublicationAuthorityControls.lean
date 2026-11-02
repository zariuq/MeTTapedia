import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PublicationAuthority
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-!
# A public copy of a theorem value does not grant publication rights

The client may publish the same value at a public location, but its ordinary
valid producer cannot publish at the protected occurrence. A two-actor run
interleaves that public write with the installed kernel rule. Every protected
value then has provenance from the original hypotheses and kernel rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PublicationAuthority.Controls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes (Rights)
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel (Derivable)
open ConstraintMultisetRewriting.Controls
  (signature A f zero initial callRule callSelection call_valid)

def label : Nat → Term signature
  | 3 => .const 1
  | occurrence => ConstraintMultisetRewriting.Controls.label occurrence

def location (occurrence : Nat) : Bool := occurrence = 0 ∨ occurrence = 2
def protectedOccurrence (occurrence : Nat) : Prop := location occurrence = true
instance : DecidablePred protectedOccurrence := fun occurrence => inferInstanceAs (Decidable (location occurrence = true))

def allRights : Rights Bool := fun _ _ => true
def clientRights : Rights Bool := fun space _ => !space
def producer : RuleInstance (Term signature) := ⟨[], [], [], [], [.const 1]⟩
def publicSelection : Selection Nat := ⟨[], [], [3]⟩
def forgedSelection : Selection Nat := ⟨[], [], [2]⟩

def kernel : Process (Term signature) Bool := ⟨allRights, [callRule]⟩
def client : Process (Term signature) Bool := ⟨clientRights, [producer]⟩

def system : System (Term signature) Bool Bool Nat location protectedOccurrence where
  process actor := if actor then client else kernel
  kernel := false
  soleWriter := by
    intro actor different occurrence isProtected
    cases actor with
    | false => exact False.elim (different rfl)
    | true =>
        change (!location occurrence) = false
        rw [isProtected]
        rfl

theorem equal_values_have_distinct_publication_locations :
    label 2 = label 3 ∧ location 2 ≠ location 3 := by
  exact ⟨rfl, by decide⟩

theorem the_client_can_form_the_public_output : Formed clientRights location publicSelection := by
  intro occurrence member
  have same : occurrence = 3 := by simpa [publicSelection] using member
  subst occurrence
  rfl

theorem the_client_cannot_form_the_protected_output : ¬ Formed clientRights location forgedSelection := by
  intro formed
  have forbidden := formed 2 (by simp [forgedSelection])
  cases forbidden

theorem the_forged_producer_is_an_ordinary_valid_firing :
    forgedSelection.Valid A label producer initial := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨A.identity, A.models_nil _⟩, ?_⟩
  intro check member
  cases member

theorem the_same_producer_can_publish_publicly : publicSelection.Valid A label producer initial := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨A.identity, A.models_nil _⟩, ?_⟩
  intro check member
  cases member

def publicState := publicSelection.result label producer initial
def forgedState := forgedSelection.result label producer initial
def finalState := callSelection.result label callRule publicState

theorem public_step : system.Step A label true initial publicState :=
  ⟨producer, by simp [system, client], publicSelection,
    the_same_producer_can_publish_publicly, the_client_can_form_the_public_output, rfl⟩

theorem the_client_cannot_publish_the_protected_copy : ¬ system.Step A label true initial forgedState := by
  intro step
  have old := system.nonwriter_creates_no_protected_occurrence A label
    (by decide : true ≠ system.kernel) step (occurrence := 2) (by decide) (by decide)
  have missing : 2 ∉ initial.present := by decide
  exact missing old

theorem the_kernel_rule_is_valid_after_the_public_write : callSelection.Valid A label callRule publicState := by
  refine ⟨call_valid.take_distinct, call_valid.output_distinct, rfl, rfl, rfl, by decide,
    call_valid.consistent, ?_⟩
  intro check member
  cases member

theorem kernel_step : system.Step A label false publicState finalState := by
  refine ⟨callRule, by simp [system, kernel], callSelection,
    the_kernel_rule_is_valid_after_the_public_write, ?_, rfl⟩
  intro occurrence member
  rfl

theorem interleaved_run : system.Run A label initial [true, false] finalState :=
  .cons public_step (.cons kernel_step (.nil finalState))

def hypotheses (judgment : Term signature) : Prop := ∃ argument, judgment = f argument

theorem initial_provenance :
    Provenance.AllDerivable A label protectedOccurrence kernel.rules hypotheses initial := by
  intro assignment _ occurrence member isProtected
  have choices : occurrence = 0 ∨ occurrence = 1 := by simpa [initial] using member
  rcases choices with rfl | rfl
  · exact Derivable.initial ⟨assignment 0, rfl⟩
  · cases isProtected

theorem every_protected_output_in_the_run_has_installed_provenance :
    Provenance.AllDerivable A label protectedOccurrence kernel.rules hypotheses finalState :=
  system.run_allDerivable A label hypotheses interleaved_run initial_provenance

theorem the_published_theorem_has_a_derivation_from_the_original_hypotheses :
    Derivable hypotheses (Provenance.Infers A label protectedOccurrence kernel.rules) (Term.const 1) := by
  have solved : A.Models zero finalState.equations := by
    intro equation member
    have same : equation = (f (.const 0), f (.var 0)) := by
      simpa [finalState, publicState, Selection.result, Selection.problem, Selection.equations,
        callSelection, callRule, publicSelection, producer, initial, label, ConstraintMultisetRewriting.Controls.label] using member
    subst equation
    rfl
  exact every_protected_output_in_the_run_has_installed_provenance zero solved 2 (by decide) (by decide)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PublicationAuthority.Controls
