import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedPromotion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFactorControls

/-!
# Reused contextual interfaces keep their guards at every instance

One capture assignment satisfies a retained guard; another refutes it, while
both keep the same resource selection and consistent equation problem. The
uninstantiated source guard is unresolved. An additional shared row can also
invalidate an absence guard without changing the original binding problem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedPromotionControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualActivatedStep ContextualInteractionFactors ContextualViewNaturality
open ContextualSelectionViews.Controls (base locals captures raw active RawTerm atom pair rawA)
open ContextualGuardedStep.Controls (occupied selection bare outputs equalityRule)
open ContextualFactorControls (rows)

def pinA : Assignment captures captures := fun _ => atom captures
def pinB : Assignment captures captures := fun _ => pair (atom captures) (atom captures)
def mappedRule (change : Assignment captures captures) :=
  equalityRule.map (instantiate (ContextualStoredRows.liftCaptures locals change))
def mappedRows (change : Assignment captures captures) := fun occurrence => (rows occurrence).map locals change
def mappedBefore (change : Assignment captures captures) :=
  ContextualTransportedActivation.configurationMap change bare
def mappedOutputs (change : Assignment captures captures) :=
  fun occurrence => instantiate (activeLift locals change) (outputs occurrence)

theorem first_instance_information :
    Information locals captures occupied selection (mappedRule pinA) (mappedRows pinA) (mappedBefore pinA) := by
  refine ⟨ContextualFrameUnifier.solvable_of_consistent ⟨generator active, ?_⟩, ?_⟩
  · exact SubstitutionAction.models_nil _ _
  · intro check member
    have only : check = .equal (atom active) (atom active) := List.mem_singleton.mp member
    subst check
    exact ContextualGuardSemantics.Ask.equal_refl locals _ _ _ _

theorem first_instance_fires :
    ContextualGuardedStep.Valid locals captures occupied selection (mappedRule pinA)
      (mappedRows pinA) (mappedBefore pinA) (mappedOutputs pinA) :=
  (ContextualGuardedPromotion.instance_valid_iff_information locals pinA occupied selection
    equalityRule rows bare outputs ContextualFactorControls.unresolved_guard_has_formation
    ContextualFactorControls.unresolved_guard_has_resources).mpr first_instance_information

theorem second_instance_is_consistent :
    (ContextualFamilies.action active [] ()).Consistent
      (problem locals captures occupied selection (mappedRule pinB) (mappedRows pinB) (mappedBefore pinB)) :=
  ⟨generator active, SubstitutionAction.models_nil _ _⟩

theorem second_instance_refuses :
    ¬ ContextualGuardedStep.Valid locals captures occupied selection (mappedRule pinB)
      (mappedRows pinB) (mappedBefore pinB) (mappedOutputs pinB) := by
  intro valid
  have asked := valid.checks (.equal (pair (atom active) (atom active)) (atom active))
    (List.mem_singleton_self _)
  have same := asked (Mettapedia.Logic.LP.ScopedVar Nat ⊕ Nat) active (generator active)
    (fun _ member => False.elim (List.not_mem_nil member))
  change pair (atom active) (atom active) = atom active at same
  cases (Term.op.inj same).1

theorem the_successful_instance_does_not_license_its_unresolved_source :
    ¬ ContextualGuardedStep.Valid locals captures occupied selection equalityRule rows bare outputs := by
  intro valid
  exact ContextualFactorControls.unresolved_guard_fails_information
    ((ContextualGuardedStep.valid_iff_factors locals captures _ _ _ _ _ _).mp valid).information

theorem both_instances_keep_one_guard :
    (prepared locals captures occupied selection (mappedRule pinA) (mappedRows pinA)).rule.checks.length = 1 ∧
    (prepared locals captures occupied selection (mappedRule pinB) (mappedRows pinB)).rule.checks.length = 1 :=
  ⟨rfl, rfl⟩

def absentRule : RuleInstance RawTerm := ⟨[], [], [], [.absent rawA], [rawA]⟩
def emptyWorld : Configuration (Term (signature base captures) [] ()) Nat := ⟨[], ∅⟩

theorem absence_in_the_empty_world : Information locals captures occupied selection absentRule rows emptyWorld := by
  refine ⟨ContextualFrameUnifier.solvable_of_consistent ⟨generator active, SubstitutionAction.models_nil _ _⟩, ?_⟩
  intro check member
  have only : check = .absent (atom active) := List.mem_singleton.mp member
  subst check
  intro Future future candidate _model occurrence impossible
  exact False.elim (Finset.notMem_empty occurrence impossible)

theorem the_same_absence_guard_refuses_after_a_row_arrives :
    ¬ Information locals captures occupied selection absentRule rows bare := by
  intro information
  have asked := information.checks (.absent (atom active)) (List.mem_singleton_self _)
  exact asked (Mettapedia.Logic.LP.ScopedVar Nat ⊕ Nat) active (generator active)
    (fun _ member => False.elim (List.not_mem_nil member)) 7 (by decide) rfl

theorem arrival_preserves_the_equation_problem :
    problem locals captures occupied selection absentRule rows emptyWorld =
      problem locals captures occupied selection absentRule rows bare := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedPromotionControls
