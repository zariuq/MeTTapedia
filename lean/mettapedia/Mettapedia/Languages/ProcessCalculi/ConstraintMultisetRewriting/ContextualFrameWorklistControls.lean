import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameWorklist
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameControls

/-!
# Executed fresh-frame worklist controls

A swapped same-hole equation introduces a helper with no ambient parameters.
Equal maps discharge their equation without an interface decrease. A later
ground constraint binds the actual helper, and unrelated declarations retain
their parameter interfaces. Identical compound applications discharge by
reflexivity; nonidentical compound constraints stay explicit residuals.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameWorklist.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual

abbrev base := ContextualFrame.Controls.signature
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

def declaration (identity : Bool) : MetaArity base := if identity then ([()], ()) else ([(), ()], ())
abbrev extended := signature base declaration
def call {Γ : Ctx base} (first second : Term extended Γ ()) : Term extended Γ () :=
  .op (.inr (.mk false)) (.cons first (.cons second .nil))
def constant {Γ : Ctx base} : Term extended Γ () := .op (.inl .constant) .nil

def formal : Term extended [(), ()] () := call (.var .zero) (.var (.succ .zero))
def swapped : Term extended [(), ()] () := call (.var (.succ .zero)) (.var .zero)
def swapProblem : Problem declaration := [(observe formal, observe swapped)]
def sameProblem : Problem declaration := [(observe formal, observe formal)]
def constrained : Problem declaration :=
  [(observe formal, observe swapped), (observe formal, observe (constant (Γ := [(), ()])))]
def compoundProblem : Problem declaration :=
  [(observe (call (constant (Γ := [])) constant), observe (call (constant (Γ := [])) constant))]
def nonidenticalCompoundProblem : Problem declaration :=
  [(observe (call (constant (Γ := [])) constant), observe (constant (Γ := [])))]

def constantModel : Assignment declaration declaration
  | false => constant
  | true => constant

theorem constant_models_swap : Models constantModel swapProblem := by
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

theorem constant_models_same : Models constantModel sameProblem := by
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

theorem constant_models_constrained : Models constantModel constrained := by
  intro equation member
  simp only [constrained, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

def pendingCount {problem : Problem declaration} : Result problem → Option Nat
  | .refuted _ => none
  | .residual update => some update.remaining.length

def rootArity {Next : Type} (next : Next → MetaArity base) :
    {Γ : Ctx base} → {sort : base.Srt} → Term (signature base next) Γ sort → Option Nat
  | _, _, .var _ => none
  | _, _, .op (.inl _) _ => none
  | _, _, .op (.inr (.mk identity)) _ => some (next identity).1.length

def originalImageArity {problem : Problem declaration} (result : Result problem) (identity : Bool) : Option Nat :=
  match result with
  | .refuted _ => none
  | .residual update => rootArity update.declaration (update.answer identity)

theorem the_swapped_equation_discharges_in_one_step : pendingCount (run 1 declaration swapProblem) = some 0 := by
  rw [run_eq_local_on_model 1 swapProblem declaration constantModel constant_models_swap]
  decide +kernel

theorem equal_maps_do_not_repeat_the_same_equation : pendingCount (run 1 declaration sameProblem) = some 0 := by
  rw [run_eq_local_on_model 1 sameProblem declaration constantModel constant_models_same]
  decide +kernel

theorem the_actual_fresh_helper_has_no_ambient_parameters :
    originalImageArity (run 1 declaration swapProblem) false = some 0 := by
  rw [run_eq_local_on_model 1 swapProblem declaration constantModel constant_models_swap]
  decide +kernel

theorem the_unselected_declaration_keeps_its_own_parameter :
    originalImageArity (run 1 declaration swapProblem) true = some 1 := by
  rw [run_eq_local_on_model 1 swapProblem declaration constantModel constant_models_swap]
  decide +kernel

theorem a_later_ground_equation_binds_the_computed_helper :
    pendingCount (run 3 declaration constrained) = some 0 := by
  rw [run_eq_local_on_model 3 constrained declaration constantModel constant_models_constrained]
  decide +kernel

theorem identical_compound_applications_discharge_by_reflexivity :
    pendingCount (run 1 declaration compoundProblem) = some 0 := by
  decide +kernel

theorem reflexivity_does_not_constrain_the_compound_hole_image :
    originalImageArity (run 1 declaration compoundProblem) false = some 2 := by
  decide +kernel

theorem nonidentical_compound_applications_are_not_falsely_refuted :
    pendingCount (run 3 declaration nonidenticalCompoundProblem) = some 1 := by
  decide +kernel

theorem zero_fuel_keeps_both_original_constraints : pendingCount (run 0 declaration constrained) = some 2 := rfl

theorem the_computed_fresh_frame_answer_solves_the_whole_original_queue :
    ∃ update, run 3 declaration constrained = .residual update ∧
      update.remaining = [] ∧ Models update.answer constrained := by
  have count := a_later_ground_equation_binds_the_computed_helper
  generalize computed : run 3 declaration constrained = result at count
  cases result with
  | refuted proof => cases count
  | residual update =>
      have empty : update.remaining = [] := by simpa using (Option.some.inj count)
      exact ⟨update, rfl, empty, update.completed empty⟩

def reversed : Problem declaration := constrained.reverse

theorem constant_models_reversed : Models constantModel reversed := by
  intro equation member
  exact constant_models_constrained equation (List.mem_reverse.mp member)

theorem the_reverse_order_also_completes : pendingCount (run 3 declaration reversed) = some 0 := by
  rw [run_eq_local_on_model 3 reversed declaration constantModel constant_models_reversed]
  decide +kernel

/-- The two witnesses are actual worklist outputs. Their comparison preserves
every original term, including terms in surrounding binding contexts. -/
theorem the_actual_two_orders_preserve_original_instances :
    ∃ first : ContextualFrameUpdate.Update constrained,
      ∃ second : ContextualFrameUpdate.Update reversed,
        run 3 declaration constrained = .residual first ∧
        run 3 declaration reversed = .residual second ∧
        first.remaining = [] ∧ second.remaining = [] ∧
        ∃ toSecond : Assignment first.declaration second.declaration,
          ∃ toFirst : Assignment second.declaration first.declaration,
            (∀ {Γ : Ctx base} (term : Term extended Γ ()),
              instantiate toSecond (instantiate first.answer term) = instantiate second.answer term) ∧
            (∀ {Γ : Ctx base} (term : Term extended Γ ()),
              instantiate toFirst (instantiate second.answer term) = instantiate first.answer term) := by
  obtain ⟨first, computedFirst, firstEmpty, _⟩ :=
    the_computed_fresh_frame_answer_solves_the_whole_original_queue
  have count := the_reverse_order_also_completes
  generalize computedSecond : run 3 declaration reversed = result at count
  cases result with
  | refuted proof => cases count
  | residual second =>
      have secondEmpty : second.remaining = [] := by simpa using (Option.some.inj count)
      obtain ⟨toSecond, toFirst, forward, backward⟩ := first.completed_orders second
        firstEmpty secondEmpty (List.reverse_perm constrained).symm
      exact ⟨first, second, computedFirst, rfl, firstEmpty, secondEmpty,
        toSecond, toFirst, fun term => forward term, fun term => backward term⟩

/-- A lambda has its own bound variable even after the outer hole's two
formal parameters have been eliminated by the swapped-spine equation. -/
def localLambda {Γ : Ctx base} : Term extended Γ () :=
  .op (.inl .lam) (.cons (.var .zero) .nil)

def binderProblem : Problem declaration :=
  [(observe formal, observe swapped), (observe formal, observe (localLambda (Γ := [(), ()])))]

def binderModel : Assignment declaration declaration
  | false => localLambda
  | true => generator declaration true

theorem binder_models_problem : Models binderModel binderProblem := by
  intro equation member
  simp only [binderProblem, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem the_worklist_solves_the_binding_example : pendingCount (run 3 declaration binderProblem) = some 0 := by
  rw [run_eq_local_on_model 3 binderProblem declaration binderModel binder_models_problem]
  decide +kernel

theorem the_completed_binding_answer_has_the_declared_body :
    ∃ update : ContextualFrameUpdate.Update binderProblem,
      run 3 declaration binderProblem = .residual update ∧ update.remaining = [] ∧
      instantiate update.answer formal =
        (.op (.inl .lam) (.cons (.var .zero) .nil) : Term (signature base update.declaration) [(), ()] ()) := by
  have count := the_worklist_solves_the_binding_example
  generalize computed : run 3 declaration binderProblem = result at count
  cases result with
  | refuted proof => cases count
  | residual update =>
      have empty : update.remaining = [] := by simpa using (Option.some.inj count)
      have solved := update.completed empty
      have body := solved (observe formal, observe (localLambda (Γ := [(), ()]))) (by simp [binderProblem])
      exact ⟨update, rfl, empty, observe_injective body⟩

namespace Incremental

def declaration (name : Bool) : MetaArity base := if name then ([], ()) else ([()], ())
abbrev terms := signature base declaration

def atom {Γ : Ctx base} : Term terms Γ () := .op (.inl .constant) .nil
def pair {Γ : Ctx base} (first second : Term terms Γ ()) : Term terms Γ () :=
  .op (.inl .pair) (.cons first (.cons second .nil))
def lam {Γ : Ctx base} (body : Term terms (() :: Γ) ()) : Term terms Γ () :=
  .op (.inl .lam) (.cons body .nil)
def function {Γ : Ctx base} (argument : Term terms Γ ()) : Term terms Γ () :=
  .op (.inr (.mk false)) (.cons argument .nil)
def unknown {Γ : Ctx base} : Term terms Γ () := .op (.inr (.mk true)) .nil

def past : Problem declaration :=
  [(observe (lam (Γ := []) (function (.var .zero))), observe (lam (Γ := []) (.var .zero)))]
def extra : Problem declaration :=
  [(observe (function (Γ := []) (pair unknown atom)), observe (pair (Γ := []) atom atom))]
def incompatible : Problem declaration :=
  [(observe (function (Γ := []) (pair unknown atom)), observe (atom (Γ := [])))]

def model : Assignment declaration declaration
  | false => .var .zero
  | true => atom

theorem prefix_model : Models model past := by
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

theorem joint_model : Models model (past ++ extra) := by
  apply (models_append _ _ _).mpr
  refine ⟨prefix_model, ?_⟩
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

def pending {problem : Problem declaration} : Result problem → Option Nat
  | .refuted _ => none
  | .residual update => some update.remaining.length

def variableIsConstant {problem : Problem declaration} : Result problem → Bool
  | .refuted _ => false
  | .residual update => match update.answer true with
    | .op (.inl .constant) .nil => true
    | _ => false

def nextIsPattern : Result past → Bool
  | .refuted _ => false
  | .residual update =>
      ContextualPatternFragment.checkProblem (update.remaining ++ mapProblem update.answer extra)

theorem raw_later_application_is_not_a_structural_pattern :
    ContextualPatternFragment.check (function (Γ := []) (pair unknown atom)) = false := by
  decide +kernel

theorem the_actual_prefix_solves_under_a_binder : pending (run 1 declaration past) = some 0 := by
  rw [run_eq_local_on_model 1 past declaration model prefix_model]
  decide +kernel

theorem the_completed_prefix_exposes_a_pattern_problem : nextIsPattern (run 1 declaration past) = true := by
  rw [run_eq_local_on_model 1 past declaration model prefix_model]
  decide +kernel

theorem the_incremental_run_solves_the_original_compound_problem :
    pending (runIncremental 1 1 past extra) = some 0 := by
  rw [runIncremental_eq_local_on_model 1 1 past extra declaration model joint_model]
  decide +kernel

theorem the_later_equation_binds_the_shared_variable :
    variableIsConstant (runIncremental 1 1 past extra) = true := by
  rw [runIncremental_eq_local_on_model 1 1 past extra declaration model joint_model]
  decide +kernel

theorem incompatible_later_equation_is_refuted :
    pending (runIncremental 1 1 past incompatible) = none := by
  unfold runIncremental
  rw [run_eq_local_on_model 1 past declaration model prefix_model]
  decide +kernel

theorem uncompleted_prefix_is_not_discarded :
    pending (runIncremental 0 0 past extra) = some 2 := rfl

def forgetfulModel : Assignment declaration declaration := fun _ => atom

theorem dropping_the_prefix_would_admit_the_incompatible_equation : Models forgetfulModel incompatible := by
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

theorem the_same_model_violates_the_retained_prefix : ¬ Models forgetfulModel past := by
  intro model
  have equation := model _ (List.mem_singleton_self _)
  have terms := observe_injective equation
  have bodies := (Args.cons.inj (eq_of_heq (Term.op.inj terms).2)).1
  cases bodies

theorem the_successful_computed_update_keeps_both_original_equations :
    ∃ update : ContextualFrameUpdate.Update (past ++ extra),
      runIncremental 1 1 past extra = .residual update ∧ update.remaining = [] ∧
        Models update.answer (past ++ extra) := by
  have count := the_incremental_run_solves_the_original_compound_problem
  cases computed : runIncremental 1 1 past extra with
  | refuted proof => simp only [computed, pending, reduceCtorEq] at count
  | residual update =>
      have empty : update.remaining = [] := by
        simpa only [computed, pending, Option.some.injEq, List.length_eq_zero_iff] using count
      exact ⟨update, rfl, empty, update.completed empty⟩

end Incremental

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameWorklist.Controls
