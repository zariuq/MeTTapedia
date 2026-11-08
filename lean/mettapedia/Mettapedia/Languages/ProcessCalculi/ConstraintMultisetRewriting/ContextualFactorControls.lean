import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFactorization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedStepControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrincipalAskControls

/-!
# Each interaction obligation can fail with the other two satisfied

All examples use actual contextual terms, preparation, finite occurrence
worlds and universal asks. The guards can fail in a consistent store.
The controls do not infer that the three indexed layers vary independently
under every change of signature, authority or scope.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFactorControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualActivatedStep ContextualInteractionFactors
open ContextualSelectionViews.Controls (base locals captures raw active RawTerm ActiveTerm atom p rawA)
open ContextualGuardedStep.Controls (occupied selection bare outputs trueRule equalityRule activeA)

def rows (_ : Nat) : ContextualStoredRows.Row locals captures [] () := .shared (atom captures)
def extraRead : Selection Nat := ⟨[], [7], [99]⟩
def doubleTake : Selection Nat := ⟨[7, 7], [], [99]⟩
def doubleTakeRule : RuleInstance RawTerm := ⟨[rawA, rawA], [], [], [], [rawA]⟩

theorem malformed_ports_still_have_resources : Resources extraRead bare.present := by
  apply (resources_iff outputs _ _).mpr
  decide

theorem malformed_ports_still_have_information : Information locals captures occupied extraRead trueRule rows bare := by
  refine ⟨ContextualFrameUnifier.solvable_of_consistent ⟨generator active, ?_⟩, ?_⟩
  · change (ContextualFamilies.action active [] ()).Models (generator active) []
    exact SubstitutionAction.models_nil _ _
  · intro check member
    have only : check = .equal (atom active) (atom active) := List.mem_singleton.mp member
    subst check
    exact ContextualGuardSemantics.Ask.equal_refl locals _ _ _ _

theorem malformed_ports_fail_formation : ¬ Formation locals captures occupied extraRead trueRule rows outputs := by
  intro formed
  have impossible := formed.read_length
  cases impossible

theorem doubled_take_has_formation : Formation locals captures occupied doubleTake doubleTakeRule rows outputs := by
  exact ⟨rfl, rfl, rfl⟩

theorem doubled_take_has_information : Information locals captures occupied doubleTake doubleTakeRule rows bare := by
  refine ⟨ContextualFrameUnifier.solvable_of_consistent ⟨generator active, ?_⟩, ?_⟩
  · intro equation member
    change equation ∈ [(atom active, atom active), (atom active, atom active)] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    subst equation
    rfl
  · intro check member
    cases member

theorem doubled_take_fails_resources : ¬ Resources doubleTake bare.present := by
  intro resource
  have distinct := ((resources_iff outputs _ _).mp resource).1
  exact (by decide : ¬ ([7, 7] : List Nat).Nodup) distinct

theorem unresolved_guard_has_formation : Formation locals captures occupied selection equalityRule rows outputs :=
  ⟨rfl, rfl, rfl⟩

theorem unresolved_guard_has_resources : Resources selection bare.present := by
  apply (resources_iff outputs _ _).mpr
  decide

theorem unresolved_guard_has_consistent_equations :
    (ContextualFamilies.action active [] ()).Consistent
      (problem locals captures occupied selection equalityRule rows bare) :=
  ⟨generator active, SubstitutionAction.models_nil _ _⟩

theorem unresolved_guard_fails_information : ¬ Information locals captures occupied selection equalityRule rows bare := by
  intro information
  have ask := information.checks (.equal (generator active (.inr 0)) (atom active))
    (List.mem_singleton_self _)
  have same := ask (Mettapedia.Logic.LP.ScopedVar Nat ⊕ Nat) active (generator active)
    (fun _ member => False.elim (List.not_mem_nil member))
  change generator active (.inr 0) = atom active at same
  cases (Term.op.inj same).1

theorem true_guard_forms_an_actual_step :
    ContextualGuardedStep.Valid locals captures occupied selection trueRule rows bare outputs := by
  apply (ContextualGuardedStep.valid_iff_factors locals captures occupied selection trueRule rows bare outputs).mpr
  refine ⟨⟨rfl, rfl, rfl⟩, unresolved_guard_has_resources, ?_⟩
  exact malformed_ports_still_have_information

open ContextualPrefixModelControls (emptySignature noDeclarations callers oldCallerProblem aliasCallers)

theorem learning_an_alias_refines_but_does_not_preserve_solutions :
    ContextualInformation.Refines oldCallerProblem [] ∧
      ¬ ContextualInformation.Equivalent oldCallerProblem [] := by
  constructor
  · intro Future future candidate _model equation member
    cases member
  · intro same
    have model := same.2 Bool callers (generator callers) (by intro equation member; cases member)
    have equal := model (generator callers false, generator callers true) (List.mem_singleton_self _)
    rw [instantiate_generator, instantiate_generator] at equal
    have names := congrArg Operator.key (Sum.inr.inj (Term.op.inj equal).1)
    cases names

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFactorControls
