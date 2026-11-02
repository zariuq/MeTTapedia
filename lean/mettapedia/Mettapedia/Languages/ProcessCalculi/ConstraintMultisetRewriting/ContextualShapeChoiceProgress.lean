import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeNamedProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeBindingProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverChoiceProgress

/-!
# Every actual pattern choice decreases finite shape work

The proof follows each concrete root constructor and the retained prefix
and suffix. It requires a first-order shape model, with no higher-order
solvability premise. Reversing an equation preserves the same measure.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeChoiceProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment
open ContextualSolverCases
open ContextualShapeErasure
open ContextualShapePotential (measure)
open ContextualSolverMeasure (Smaller of_image_lt of_interface_lt of_equation_lt)

variable {S : Signature} {V Next : Type} [DecidableEq V] {source : V → MetaArity S}

theorem imitation (identity : V) {Γ : Ctx S} (rho : Ren S (source identity).1 Γ)
    (operator : S.Op (source identity).2) (fields : Args (signature S source) (S.arity operator) Γ)
    (before after : Problem source) (images : ShapeAssignment S V Next)
    (patterned : ProblemPattern (before ++ (observe (rename (S := signature S source) rho (generator source identity)),
      observe (Term.op (.inl operator) fields)) :: after))
    (models : ShapeModels images (before ++ (observe (rename (S := signature S source) rho (generator source identity)),
      observe (Term.op (.inl operator) fields)) :: after)) :
    let update := (ContextualSolverImitationProgress.choice identity rho operator fields before after).perform
    letI := update.equality
    ∃ remaining : ShapeAssignment S update.Variables Next, ShapeModels remaining update.remaining ∧
      (∀ name, images name = evaluate remaining (update.answer name)) ∧
      Smaller (measure remaining update.remaining) (measure images (before ++
        (observe (rename (S := signature S source) rho (generator source identity)), observe (Term.op (.inl operator) fields)) :: after)) := by
  let equation := (observe (rename (S := signature S source) rho (generator source identity)), observe (Term.op (.inl operator) fields))
  have moved := ContextualProblemPermutation.selected_to_head equation before after
  have patternedHead := (ContextualProblemPermutation.patterns_permutation moved).mp patterned
  have modeledHead := (ContextualShapeTransport.models_permutation images moved).mp models
  let named := ContextualNamedImitation.apply source identity rho operator fields (before ++ after)
  let _ := named.equality
  obtain ⟨remaining, modeled, components, decrease⟩ :=
    ContextualShapeNamedProgress.imitation identity rho operator fields (before ++ after) images patternedHead modeledHead
  have tails := ContextualSolverImitationProgress.queue_permutation identity rho operator fields before after
  have samePotential := ContextualShapePotential.permutation remaining tails
  have sameSource := ContextualShapePotential.permutation images moved
  refine ⟨remaining, (ContextualShapeTransport.models_permutation remaining tails).mpr modeled, components, of_image_lt ?_⟩
  exact lt_of_eq_of_lt samePotential (decrease.trans_eq sameSource.symm)

theorem self (identity : V) {Γ : Ctx S} (left right : Ren S (source identity).1 Γ) (different : left ≠ right)
    (before after : Problem source) (images : ShapeAssignment S V Next)
    (patterned : ProblemPattern (before ++ (observe (rename (S := signature S source) left (generator source identity)),
      observe (rename (S := signature S source) right (generator source identity))) :: after))
    (models : ShapeModels images (before ++ (observe (rename (S := signature S source) left (generator source identity)),
      observe (rename (S := signature S source) right (generator source identity))) :: after)) :
    let update := (ContextualSolverSelfProgress.choice identity left right different before after).perform
    letI := update.equality
    ∃ remaining : ShapeAssignment S update.Variables Next, ShapeModels remaining update.remaining ∧
      (∀ name, images name = evaluate remaining (update.answer name)) ∧
      Smaller (measure remaining update.remaining) (measure images (before ++
        (observe (rename (S := signature S source) left (generator source identity)),
          observe (rename (S := signature S source) right (generator source identity))) :: after)) := by
  let equation := (observe (rename (S := signature S source) left (generator source identity)),
    observe (rename (S := signature S source) right (generator source identity)))
  have moved := ContextualProblemPermutation.selected_to_head equation before after
  have patternedHead := (ContextualProblemPermutation.patterns_permutation moved).mp patterned
  have modeledHead := (ContextualShapeTransport.models_permutation images moved).mp models
  let named := ContextualNamedSelfPair.apply source identity left right (before ++ after)
  let _ := named.equality
  obtain ⟨remaining, modeled, components, imagesBound, parameters⟩ :=
    ContextualShapeNamedProgress.self identity left right different (before ++ after) images patternedHead modeledHead
  have tail := ContextualSolverSelfProgress.same_remaining identity left right different before after
  have sameImages := ContextualShapePotential.permutation images moved
  have sameParameters := ContextualProblemPermutation.interface_permutation moved
  refine ⟨remaining, ?_, components, of_interface_lt ?_ ?_⟩
  · rw [tail]
    exact modeled
  · dsimp only [ContextualShapePotential.measure]
    rw [tail]
    exact imagesBound.trans_eq sameImages.symm
  · dsimp only [ContextualShapePotential.measure]
    rw [tail]
    exact parameters.trans_eq sameParameters.symm

theorem flex (first second : V) (different : first ≠ second) (sorts : (source first).2 = (source second).2)
    {Γ : Ctx S} (left : Ren S (source first).1 Γ) (right : Ren S (source second).1 Γ)
    (before after : Problem source) (images : ShapeAssignment S V Next)
    (patterned : ProblemPattern (before ++ (observe (rename (S := signature S source) left (generator source first)),
      observe (rename (S := signature S source) right (generator source second))) :: after))
    (models : ShapeModels images (before ++ (observe (rename (S := signature S source) left (generator source first)),
      observe (rename (S := signature S source) right (generator source second))) :: after)) :
    let update := (ContextualSolverFlexProgress.choice first second different sorts left right before after).perform
    letI := update.equality
    ∃ remaining : ShapeAssignment S update.Variables Next, ShapeModels remaining update.remaining ∧
      (∀ name, images name = evaluate remaining (update.answer name)) ∧
      Smaller (measure remaining update.remaining) (measure images (before ++
        (observe (rename (S := signature S source) left (generator source first)),
          observe (rename (S := signature S source) right (generator source second))) :: after)) := by
  let equation := (observe (rename (S := signature S source) left (generator source first)),
    observe (rename (S := signature S source) right (generator source second)))
  have moved := ContextualProblemPermutation.selected_to_head equation before after
  have patternedHead := (ContextualProblemPermutation.patterns_permutation moved).mp patterned
  have modeledHead := (ContextualShapeTransport.models_permutation images moved).mp models
  let named := ContextualNamedFlexPair.apply source first second different sorts left right (before ++ after)
  let _ := named.equality
  obtain ⟨remaining, modeled, components, decrease⟩ :=
    ContextualShapeNamedProgress.flex first second different sorts left right (before ++ after) images patternedHead modeledHead
  have tail := ContextualSolverFlexProgress.same_remaining first second different sorts left right before after
  have sameSource := ContextualShapePotential.permutation images moved
  refine ⟨remaining, ?_, components, of_image_lt ?_⟩
  · rw [tail]
    exact modeled
  · dsimp only [ContextualShapePotential.measure]
    rw [tail]
    exact decrease.trans_eq sameSource.symm

theorem reflexive {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort)
    (before after : Problem source) (images : ShapeAssignment S V Next)
    (models : ShapeModels images (before ++ (observe term, observe term) :: after)) :
    let update := (ContextualSolverReflexiveProgress.choice term before after).perform
    ShapeModels images update.remaining ∧ (∀ name, images name = evaluate images (update.answer name)) ∧
      Smaller (measure images update.remaining) (measure images (before ++ (observe term, observe term) :: after)) := by
  have included := ContextualSolverReflexiveProgress.active_subset term before after
  refine ⟨?_, fun _ => rfl, of_equation_lt ?_ ?_ ?_⟩
  · rw [ContextualSolverReflexiveProgress.same_remaining]
    intro equation member
    apply models equation
    rcases List.mem_append.mp member with first | second
    · exact List.mem_append_left _ first
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ second)
  · dsimp only [ContextualShapePotential.measure]
    rw [ContextualSolverReflexiveProgress.same_remaining]
    exact ContextualShapePotential.monotone images included
  · dsimp only [ContextualShapePotential.measure]
    rw [ContextualSolverReflexiveProgress.same_remaining]
    exact ContextualInterfacePotential.monotone source included
  · dsimp only [ContextualShapePotential.measure]
    rw [ContextualSolverReflexiveProgress.same_remaining]
    change ContextualEquationWeight.weight (source := source) (before ++ after) <
      ContextualEquationWeight.weight (source := source) (before ++ (observe term, observe term) :: after)
    rw [ContextualEquationWeight.weight_append,
      ContextualEquationWeight.weight_append, ContextualEquationWeight.weight_cons]
    change ContextualEquationWeight.weight before + ContextualEquationWeight.weight after <
      ContextualEquationWeight.weight before + (termSize term + termSize term + ContextualEquationWeight.weight after)
    have positive := termSize_pos term
    omega

omit [DecidableEq V] in
theorem models_at (images : ShapeAssignment S V Next) (equation : Equation (Observation S source))
    (before after : Problem source) :
    ShapeModels images (before ++ equation :: after) ↔ ShapeModels images (before ++ (equation.2, equation.1) :: after) := by
  simp only [ShapeModels, List.forall_mem_append, List.forall_mem_cons]
  exact and_congr Iff.rfl (and_congr eq_comm Iff.rfl)

theorem measure_at (images : ShapeAssignment S V Next) (equation : Equation (Observation S source))
    (before after : Problem source) :
    measure images (before ++ equation :: after) = measure images (before ++ (equation.2, equation.1) :: after) := by
  dsimp only [ContextualShapePotential.measure]
  rw [ContextualProblemOrientation.active_at equation before after, ContextualProblemOrientation.weight_at equation before after]
  rfl

theorem root_progress {equation : Equation (Observation S source)} (selected : RootCase S source equation) :
    ∀ (before after : Problem source) (images : ShapeAssignment S V Next), ProblemPattern (before ++ equation :: after) →
      ShapeModels images (before ++ equation :: after) →
      let update := (selected.locate before after).perform
      letI := update.equality
      ∃ remaining : ShapeAssignment S update.Variables Next, ShapeModels remaining update.remaining ∧
        (∀ name, images name = evaluate remaining (update.answer name)) ∧
        Smaller (measure remaining update.remaining) (measure images (before ++ equation :: after)) := by
  induction selected with
  | reflexive term =>
      intro before after images _ models
      exact ⟨images, reflexive term before after images models⟩
  | binding recovered =>
      intro before after images patterned models
      exact ⟨images, ContextualShapeBindingProgress.located_progress recovered before after images patterned models⟩
  | imitation identity rho operator fields => exact imitation identity rho operator fields
  | selfPair identity left right different => exact self identity left right different
  | flexPair first second different sorts left right => exact flex first second different sorts left right
  | @reverse equation original smaller =>
      intro before after images patterned models
      have flippedPattern := (ContextualProblemOrientation.patterns_at equation before after).mp patterned
      have flippedModels := (models_at images equation before after).mp models
      let _ := (original.locate before after).perform.equality
      obtain ⟨remaining, modeled, components, decrease⟩ := smaller before after images flippedPattern flippedModels
      refine ⟨remaining, modeled, components, ?_⟩
      exact Eq.mpr (congrArg (fun bound => Smaller (measure remaining
        (original.locate before after).perform.remaining) bound) (measure_at images equation before after)) decrease

theorem choice_progress {problem : Problem source} (selected : Choice problem)
    (images : ShapeAssignment S V Next) (patterned : ProblemPattern problem) (models : ShapeModels images problem) :
    let update := selected.perform
    letI := update.equality
    ∃ remaining : ShapeAssignment S update.Variables Next, ShapeModels remaining update.remaining ∧
      (∀ name, images name = evaluate remaining (update.answer name)) ∧
      Smaller (measure remaining update.remaining) (measure images problem) := by
  rcases selected with ⟨before, equation, root, after, split⟩
  subst problem
  exact root_progress root before after images patterned models

theorem computed_progress [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    {problem : Problem source} {update : ContextualFrameUpdate.Update problem}
    (computed : ContextualFrameWorklist.choose problem = some update)
    (images : ShapeAssignment S V Next) (patterned : ProblemPattern problem) (models : ShapeModels images problem) :
    letI := update.equality
    ∃ remaining : ShapeAssignment S update.Variables Next, ShapeModels remaining update.remaining ∧
      (∀ name, images name = evaluate remaining (update.answer name)) ∧
      Smaller (measure remaining update.remaining) (measure images problem) := by
  unfold ContextualFrameWorklist.choose at computed
  obtain ⟨selected, _, rfl⟩ := Option.map_eq_some_iff.mp computed
  exact choice_progress selected images patterned models

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeChoiceProgress
