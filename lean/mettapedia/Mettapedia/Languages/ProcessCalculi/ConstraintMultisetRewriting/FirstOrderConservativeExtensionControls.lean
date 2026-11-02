import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderConservativeExtension
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-!
# Redundant tells, independent tells and genuine new bindings

The incoming equation x = B already determines the protected value. Repeating
it preserves every old solution even though a normalized substitution replaces
the raw generator. Starting from an empty store, the same actual tell removes
the old possibility x = A. An unrelated fresh tell preserves x through the
closed-component gluing construction.

These are original occurrence steps over existing LP terms. They neither
replace a caller's identity policy nor establish native enforcement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderConservativeExtension.Controls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A zero one)
open FirstOrderAskLocality

def component : Set Nat := {0}
def label (_ : Nat) : Term signature := .var 0
def known : EquationStore (Term signature) := [(.var 0, .const 1)]
def unrelated : EquationStore (Term signature) := [(.var 1, .const 2)]
def picked : Selection Nat := ⟨[], [], []⟩
def tellKnown : RuleInstance (Term signature) := ⟨[], [], known, [], []⟩
def tellUnrelated : RuleInstance (Term signature) := ⟨[], [], unrelated, [], []⟩
def beforeKnown : Configuration (Term signature) Nat := ⟨known, {0}⟩
def beforeOpen : Configuration (Term signature) Nat := ⟨[], {0}⟩
def afterRedundant : Configuration (Term signature) Nat := picked.result label tellKnown beforeKnown
def afterBinding : Configuration (Term signature) Nat := picked.result label tellKnown beforeOpen
def afterUnrelated : Configuration (Term signature) Nat := picked.result label tellUnrelated beforeOpen

theorem one_models_known : A.Models one known := by
  intro equation member
  have same : equation = (Term.var (σ := signature) 0, .const 1) := by simpa [known] using member
  subst equation
  rfl

private theorem tell_valid (old extra : EquationStore (Term signature))
    (consistent : A.Consistent (old ++ extra)) :
    picked.Valid A label ⟨[], [], extra, [], []⟩ ⟨old, {0}⟩ := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · change MeTTaCalculus.OccurrenceCommits.Enabled label ({0} : Finset Nat) picked.commit
    decide
  · simpa [Selection.problem, Selection.equations, picked] using consistent
  · intro check member
    cases member

theorem redundant_tell_valid : picked.Valid A label tellKnown beforeKnown :=
  tell_valid known known ⟨one, (A.models_append one known known).mpr ⟨one_models_known, one_models_known⟩⟩

theorem actual_redundant_step : Step A label tellKnown beforeKnown afterRedundant :=
  ⟨picked, redundant_tell_valid, rfl⟩

theorem redundant_tell_is_conservative :
    ConservativeOn component beforeKnown.equations afterRedundant.equations := by
  apply selected_conservative_of_entailed component label tellKnown picked beforeKnown
  simpa [GuardFreeProcessOrders.added, Selection.equations, picked, tellKnown, beforeKnown] using
    A.refines_refl known

/-- Raw identity may reject an already correct normalized value. -/
theorem normalization_is_not_new_information :
    A.Models one beforeKnown.equations ∧ one 0 ≠ (Subst.id signature) 0 ∧
      ConservativeOn component beforeKnown.equations afterRedundant.equations := by
  refine ⟨one_models_known, ?_, redundant_tell_is_conservative⟩
  intro same
  cases same

theorem redundant_tell_preserves_possible_values (term value : Term signature)
    (supported : ∀ name ∈ term.freeVars, name ∈ component) :
    (∃ assignment, A.Models assignment afterRedundant.equations ∧ assignment.applyTerm term = value) ↔
      ∃ assignment, A.Models assignment beforeKnown.equations ∧ assignment.applyTerm term = value :=
  possible_value_iff redundant_tell_is_conservative actual_redundant_step.refines term value supported

theorem unrelated_tell_valid : picked.Valid A label tellUnrelated beforeOpen := by
  apply tell_valid [] unrelated
  refine ⟨Subst.single 1 (.const 2), ?_⟩
  intro equation member
  have same : equation = (Term.var (σ := signature) 1, .const 2) := by simpa [unrelated] using member
  subst equation
  rfl

theorem actual_unrelated_step : Step A label tellUnrelated beforeOpen afterUnrelated :=
  ⟨picked, unrelated_tell_valid, rfl⟩

theorem unrelated_tell_is_conservative :
    ConservativeOn component beforeOpen.equations afterUnrelated.equations := by
  apply selected_conservative_of_closed_avoiding component label tellUnrelated picked beforeOpen
    unrelated_tell_valid
  · intro equation member
    cases member
  · intro equation member name inSupport
    have same : equation = (Term.var (σ := signature) 1, .const 2) := by
      simpa [GuardFreeProcessOrders.added, Selection.equations, picked, tellUnrelated, unrelated] using member
    subst equation
    have atOne : name = 1 := by simpa [equationSupport, Term.freeVars] using inSupport
    subst name
    simp [component]

/-- The new solution can change fresh y while retaining any old x value. -/
theorem unrelated_tell_extends_every_old_value (old : Subst signature) :
    ∃ extended, A.Models extended afterUnrelated.equations ∧
      extended 0 = old 0 ∧ extended 1 = Term.const (σ := signature) 2 := by
  obtain ⟨extended, model, agree⟩ := unrelated_tell_is_conservative old (A.models_nil old)
  refine ⟨extended, model, agree 0 (by simp [component]), ?_⟩
  exact model (.var 1, .const 2) (by
    simp [afterUnrelated, Selection.result, Selection.problem, Selection.equations,
      beforeOpen, picked, tellUnrelated, unrelated])

theorem binding_tell_valid : picked.Valid A label tellKnown beforeOpen :=
  tell_valid [] known ⟨one, by simpa using one_models_known⟩

theorem actual_new_binding_step : Step A label tellKnown beforeOpen afterBinding :=
  ⟨picked, binding_tell_valid, rfl⟩

theorem protected_old_zero_is_possible :
    ∃ assignment, A.Models assignment beforeOpen.equations ∧ assignment 0 = Term.const (σ := signature) 0 :=
  ⟨zero, A.models_nil zero, rfl⟩

theorem new_binding_fixes_one (assignment : Subst signature)
    (model : A.Models assignment afterBinding.equations) : assignment 0 = Term.const (σ := signature) 1 :=
  model (.var 0, .const 1) (by
    simp [afterBinding, Selection.result, Selection.problem, Selection.equations,
      beforeOpen, picked, tellKnown, known])

theorem protected_old_zero_cannot_extend :
    ¬ ∃ assignment, A.Models assignment afterBinding.equations ∧ assignment 0 = Term.const (σ := signature) 0 := by
  rintro ⟨assignment, model, sameZero⟩
  have impossible := sameZero.symm.trans (new_binding_fixes_one assignment model)
  cases impossible

theorem genuine_binding_is_not_conservative :
    ¬ ConservativeOn component beforeOpen.equations afterBinding.equations := by
  intro preserves
  obtain ⟨extended, model, agree⟩ := preserves zero (A.models_nil zero)
  exact protected_old_zero_cannot_extend ⟨extended, model, agree 0 (by simp [component])⟩

theorem a_valid_step_can_restrict_protected_possibilities :
    Step A label tellKnown beforeOpen afterBinding ∧
      beforeOpen.present = afterBinding.present ∧
      ¬ ConservativeOn component beforeOpen.equations afterBinding.equations :=
  ⟨actual_new_binding_step, by decide, genuine_binding_is_not_conservative⟩

theorem new_binding_changes_both_verdicts :
    ¬ A.Entails beforeOpen.equations (fun assignment => assignment 0 = Term.const (σ := signature) 1) ∧
    A.Entails afterBinding.equations (fun assignment => assignment 0 = Term.const (σ := signature) 1) ∧
    ¬ A.Entails beforeOpen.equations (fun assignment => assignment 0 ≠ Term.const (σ := signature) 0) ∧
    A.Entails afterBinding.equations (fun assignment => assignment 0 ≠ Term.const (σ := signature) 0) := by
  refine ⟨?_, new_binding_fixes_one, ?_, ?_⟩
  · intro entailed
    have impossible := entailed zero (A.models_nil zero)
    cases impossible
  · intro refuted
    exact refuted zero (A.models_nil zero) rfl
  · intro assignment model sameZero
    have impossible := sameZero.symm.trans (new_binding_fixes_one assignment model)
    cases impossible

theorem unrelated_tell_preserves_both_local_verdicts
    (observation : Subst signature → Prop) (reads : ReadsOnly component observation) :
    (A.Entails afterUnrelated.equations observation ↔ A.Entails beforeOpen.equations observation) ∧
      (A.Entails afterUnrelated.equations (fun assignment => ¬ observation assignment) ↔
        A.Entails beforeOpen.equations (fun assignment => ¬ observation assignment)) :=
  step_verdicts_iff actual_unrelated_step unrelated_tell_is_conservative observation reads

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderConservativeExtension.Controls
