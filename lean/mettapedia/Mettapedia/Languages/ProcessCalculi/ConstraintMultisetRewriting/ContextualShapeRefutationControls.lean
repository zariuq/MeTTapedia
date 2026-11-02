import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeRefutation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnrefutedPatternControls

/-!
# Shape refusal detects a global cycle and respects the general language

The total first-order owner detects a cycle spread over two equations. A
scope-inconsistent equation still has a shape model, so shape success does
not assert higher-order solvability. Conversely, a legal projecting model
of repeated and compound applications can have inconsistent erased shapes;
the checked pattern guard therefore leaves that queue unrefuted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeRefutationControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment
open ContextualShapeErasure

abbrev base := ContextualFrame.Controls.signature
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

theorem the_cycle_has_no_shape_model {Next : Type} (images : ShapeAssignment base Bool Next) :
    ¬ ShapeModels images ContextualUnrefutedPatternControls.cycle := by
  intro models
  have first := models _ List.mem_cons_self
  have second := models _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  change images false = images true at first
  let leaf : ShapeTerm base Next := .app ⟨(), .constant⟩ (fun position => Fin.elim0 position)
  let children : Fin 2 → ShapeTerm base Next := Fin.cases (images false) (fun position =>
    Fin.cases leaf (fun impossible => Fin.elim0 impossible) position)
  have same : images true = Mettapedia.Logic.LP.Term.app (σ := shapeSignature base Next) ⟨(), .pair⟩ children := by
    dsimp only [observe, ContextualUnrefutedPatternControls.call, ContextualUnrefutedPatternControls.pair,
      ContextualUnrefutedPatternControls.constant, evaluate, evaluateArgs] at second
    refine second.trans ?_
    apply congrArg (Mettapedia.Logic.LP.Term.app (σ := shapeSignature base Next) ⟨(), .pair⟩)
    funext position
    fin_cases position <;> rfl
  have smaller := Mettapedia.Logic.LP.Term.size_subterm (σ := shapeSignature base Next)
    (f := ⟨(), .pair⟩) (ts := children) ⟨0, Nat.zero_lt_succ 1⟩
  change (images false).size < (Mettapedia.Logic.LP.Term.app (σ := shapeSignature base Next) ⟨(), .pair⟩ children).size at smaller
  rw [← same, first] at smaller
  exact Nat.lt_irrefl _ smaller

theorem the_total_shape_owner_detects_the_two_equation_cycle :
    ContextualShapeRefutation.solve ContextualUnrefutedPatternControls.cycle = none := by
  apply (ContextualShapeRefutation.solve_none_iff_no_shape_model _).mpr
  rintro ⟨images, models⟩
  exact the_cycle_has_no_shape_model images models

theorem the_pattern_guard_allows_the_certified_cycle_refutation :
    (ContextualShapeRefutation.choose ContextualUnrefutedPatternControls.cycle).isSome = true := by
  cases selected : ContextualShapeRefutation.choose ContextualUnrefutedPatternControls.cycle with
  | some proof => rfl
  | none =>
      obtain ⟨images, _, models⟩ := ContextualShapeRefutation.choose_none_has_model _
        ContextualUnrefutedPatternControls.cycle_is_patterned selected
      exact False.elim (the_cycle_has_no_shape_model images models)

theorem a_scope_inconsistency_can_still_have_a_shape_model :
    (ContextualShapeRefutation.solve ContextualUnrefutedPatternControls.missingVariable).isSome = true ∧
      (ContextualEquationRefutation.choose ContextualUnrefutedPatternControls.missingVariable).isSome = true := by
  constructor
  · apply (ContextualShapeRefutation.solve_isSome_iff_shape_model _).mpr
    refine ⟨(fun _ => .const ()), ?_⟩
    intro equation member
    have only := List.mem_singleton.mp member
    subst equation
    rfl
  · decide +kernel

theorem the_projecting_general_problem_has_no_shape_model {Next : Type} (images : ShapeAssignment base Bool Next) :
    ¬ ShapeModels images ContextualFrameSaturationControls.generalProblem := by
  intro models
  have first := models _ List.mem_cons_self
  have second := models _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  change images false = (.const () : ShapeTerm base Next) at first
  change images false = Mettapedia.Logic.LP.Term.app (σ := shapeSignature base Next) ⟨(), .constant⟩
    (fun position => Fin.elim0 position) at second
  cases first.symm.trans second

theorem erasure_alone_would_refuse_a_legal_projecting_application :
    Models ContextualFrameSaturationControls.generalModel ContextualFrameSaturationControls.generalProblem ∧
      (ContextualShapeRefutation.solve ContextualFrameSaturationControls.generalProblem).isNone = true := by
  refine ⟨ContextualFrameSaturationControls.the_repeated_and_compound_equations_have_a_model, ?_⟩
  have none : ContextualShapeRefutation.solve ContextualFrameSaturationControls.generalProblem = none := by
    apply (ContextualShapeRefutation.solve_none_iff_no_shape_model _).mpr
    rintro ⟨images, models⟩
    exact the_projecting_general_problem_has_no_shape_model images models
  rw [none]
  rfl

theorem the_actual_shape_guard_retains_that_general_application :
    ContextualShapeRefutation.choose ContextualFrameSaturationControls.generalProblem = none := by
  apply ContextualShapeRefutation.choose_nonpattern
  rw [← checkProblem_iff]
  decide +kernel

theorem the_infinite_family_has_an_executable_shape_model :
    (ContextualShapeRefutation.solve ContextualActiveSupportControls.problem).isSome = true := by
  obtain ⟨images, unifies⟩ := necessary_model ContextualActiveSupportControls.image ContextualActiveSupportControls.problem
    ContextualSolverPatternControls.the_infinite_roster_problem_is_structural
    ContextualActiveSupportControls.the_original_equations_have_an_actual_model
  exact (ContextualShapeRefutation.solve_isSome_iff_shape_model _).mpr
    ⟨images, (unifies_equations_iff images _).mp unifies⟩

theorem the_shape_refusal_excludes_models_in_every_later_frame {Next : Type} (next : Next → MetaArity base)
    (candidate : Assignment ContextualUnrefutedPatternControls.source next) :
    ¬ Models candidate ContextualUnrefutedPatternControls.cycle := by
  have refused := the_pattern_guard_allows_the_certified_cycle_refutation
  cases computed : ContextualShapeRefutation.choose ContextualUnrefutedPatternControls.cycle with
  | none => simp only [computed, Option.isSome_none, Bool.false_eq_true] at refused
  | some proof => exact proof.noModel next candidate

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeRefutationControls
