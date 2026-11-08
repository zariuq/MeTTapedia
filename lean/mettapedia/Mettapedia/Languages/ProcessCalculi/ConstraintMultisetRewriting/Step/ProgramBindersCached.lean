import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersPrincipal
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixPrincipals

/-!
# Principal answers along runs, with the actual incremental solver

The principal theorem of `ProgramBindersPrincipal` needs every retained equation to be a Miller
pattern. A right-hand side such as β's `$B[$A]` is not, so after one firing the store leaves the
fragment. This file follows the actual solver instead, as retained λ execution does: the completed
answer of the previous firing is a cache, and only the new equation `lhs ≐ call` is solved.

- **Fixed calls** (`Fixes`): every solution of the store reads the current call as one source term.
  The initial state of a call fixes it.
- **Determinate equations** (`Determinate`): two solutions that match the same call agree on the
  right-hand side. A firing of a determinate equation at a fixed call fixes its answer
  (`fixes_destination`).
- `cached_principal`: at a fixed call with a completed cache, the actual incremental run for a
  Miller-pattern equation completes, and its answer is principal for the whole firing problem.
- `execution_with_solvers_iff`: for a program of determinate Miller-pattern equations, source runs
  are exactly the runs of the step with an actual completed solver result at every firing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualPatternFragment (Pattern ProblemPattern generator_pattern instantiate_preserves)

variable {S : Signature} {Γ : Ctx S} {sort : S.Srt} {ι : Type} {program : ι → Equation S Γ sort}

/-! ## Fixed calls and determinate equations -/

variable (program) in
/-- Every solution of the store, in every frame, reads the call as `call`; and one exists. -/
def Fixes (state : State program) (call : Term S Γ sort) : Prop :=
  ∃ value, Holds program state value ∧ ContextualFrameUnifier.Solvable state.1.inventory.configuration.equations ∧
    ∀ {Future : Type} (future : Future → MetaArity S) (solution : Assignment state.1.declarations future),
      ContextualFrameUnifier.Models solution state.1.inventory.configuration.equations →
        instantiate solution value = Rigid.includeTerm future call

/-- Two solutions matching the same call agree on the right-hand side. -/
def Determinate {Δ : Ctx S} (e : Equation S Δ sort) : Prop :=
  ∀ {W : Type} (target : W → MetaArity S) (first second : Assignment e.arity target) (call : Term S Δ sort),
    instantiate first e.lhs = Rigid.includeTerm target call →
      instantiate second e.lhs = Rigid.includeTerm target call →
        instantiate first e.rhs = instantiate second e.rhs

theorem Fixes.determines {state : State program} {call : Term S Γ sort} (fixes : Fixes program state call) :
    Determines program state call := by
  obtain ⟨value, holds, ⟨Future, future, solution, solved⟩, reads⟩ := fixes
  refine ⟨⟨Future, future, solution, value, holds, solved, reads future solution solved⟩, ?_⟩
  intro Later later other otherCall readsOther
  obtain ⟨value', ⟨_, isShared⟩, otherSolved, observed⟩ := readsOther
  have same : value' = value := ContextualStoredRows.Row.shared.inj (isShared.symm.trans holds.2)
  subst same
  exact Rigid.include_injective later otherCall call (observed.symm.trans (reads later other otherSolved))

theorem initial_fixes (call : Term S Γ sort) : Fixes program (initial call) call := by
  refine ⟨_, initial_holds call, ⟨_, _, generator (ground S), fun equation member => by cases member⟩, ?_⟩
  intro Future future solution _
  exact Rigid.instantiate_include (source := ground S) solution call

/-- Two ground solutions of a determinate equation at one call give one answer. -/
theorem Determinate.answer_unique {Δ : Ctx S} {e : Equation S Δ sort} (determinate : Determinate e)
    {call first second : Term S Δ sort} (left : Answers e call first) (right : Answers e call second) :
    first = second := by
  obtain ⟨θ, matched, answered⟩ := left
  obtain ⟨θ', matched', answered'⟩ := right
  exact Rigid.include_injective _ _ _ (answered.symm.trans
    ((determinate (ground S) _ _ call matched matched').trans answered'))

variable [DecidableEq ι] [ClosedTerms S]

/-- **A firing of a determinate equation at a fixed call fixes its answer.** -/
theorem fixes_destination (state : State program) (call : Term S Γ sort) (fixes : Fixes program state call)
    (index : ι) (valid : Admitted program state index) (determinate : Determinate (program index)) :
    ∃ answer, Answers (program index) call answer ∧
      Fixes program (destination program state index valid) answer := by
  obtain ⟨θ, matched⟩ := (valid_iff state call fixes.determines index).mp valid
  obtain ⟨answer, read⟩ := holeFree (instantiate ((program index).assign θ (ground S)) (program index).rhs)
  refine ⟨answer, ⟨θ, matched, read⟩, ?_⟩
  obtain ⟨value, holds, _, reads⟩ := fixes
  refine ⟨_, destination_holds state index valid holds.1, valid.solvable, ?_⟩
  intro Future future solution solved
  change ContextualFrameUnifier.Models solution (ContextualActivatedStep.problem (locals program)
    state.1.declarations state.1.occupied (selection state.2) (rule program state.1.declarations index)
    state.1.inventory.rows state.1.inventory.configuration) at solved
  rw [actual_problem program state index value holds.2] at solved
  obtain ⟨oldPart, newPart⟩ := (ContextualFrameUnifier.models_append _ _ _).mp solved
  have oldRead := reads future _ ((ContextualFrameUnifier.models_mapProblem _ _ _).mp oldPart)
  have newEquation := newPart _ (List.mem_singleton_self _)
  dsimp only [Prod.fst, Prod.snd] at newEquation
  rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose] at newEquation
  have firingMatch := newEquation.trans oldRead
  have groundMatch := ((program index).reads_in_frame θ (program index).lhs call future).mp matched
  have agree := determinate future _ _ call firingMatch groundMatch
  unfold output
  rw [← Assignment.instantiate_compose, agree]
  exact ((program index).reads_in_frame θ (program index).rhs answer future).mp read

/-! ## The cache and the incremental run -/

variable (program) in
abbrev scopedLocals (key : ScopedVar (Local program)) : MetaArity S := locals program key.name

/-- A completed or residual solver result for the retained store. -/
abbrev Cache (state : State program) :=
  ContextualFrameUpdate.Update (ContextualResidual.observeProblem state.1.inventory.configuration.equations)

def extendedCache (state : State program) (cache : Cache state) (complete : cache.remaining = []) :=
  ContextualPrefixModels.completedUpdateWithUnused (scopedLocals program) state.1.inventory.configuration.equations
    cache complete

/-- The equations the firing adds to the store. -/
def addedProblem (state : State program) (index : ι) :=
  ContextualResidual.observeProblem (ContextualActivatedStep.addedEquations (locals program) state.1.declarations
    state.1.occupied (selection state.2) (rule program state.1.declarations index) state.1.inventory.rows)

omit [DecidableEq ι] [ClosedTerms S] in
theorem observed_problem_split (state : State program) (index : ι) :
    firingProblem state index =
      ContextualResidual.observeProblem (ContextualFrameUnifier.mapProblem
        (ContextualPrefixModels.inclusion (scopedLocals program) state.1.declarations)
          state.1.inventory.configuration.equations) ++ addedProblem state index := by
  unfold firingProblem
  rw [ContextualActivatedStep.problem_eq_frame_append]
  exact List.map_append

omit [DecidableEq ι] [ClosedTerms S] in
theorem added_problem_of_shared (state : State program) (index : ι)
    (value : Term (signature S state.1.declarations) Γ sort)
    (isShared : state.1.inventory.rows state.2 = .shared value) :
    addedProblem state index =
      [(observe (instantiate (schemaAt program state.1.declarations index (ruleScope state.1.occupied state.2))
          (program index).lhs),
        observe (instantiate (ContextualSelectionViews.capturedTarget (locals program) state.1.declarations) value))] := by
  have equations := actual_problem program state index value isShared
  rw [ContextualActivatedStep.problem_eq_frame_append] at equations
  have suffix := List.append_cancel_left equations
  exact congrArg ContextualResidual.observeProblem suffix

omit [DecidableEq ι] [ClosedTerms S] in
theorem lifted_schema {V W : Type} {captures : V → MetaArity S} {next : W → MetaArity S} (index : ι) (scope : Nat)
    (change : Assignment captures next) {Δ : Ctx S} {result : S.Srt}
    (value : Term (signature S (program index).arity) Δ result) :
    instantiate (ContextualStoredRows.liftCaptures (scopedLocals program) change)
      (instantiate (schemaAt program captures index scope) value) =
        instantiate (schemaAt program next index scope) value := by
  rw [instantiate_comp]
  congr 1
  funext hole
  exact instantiate_generator _ _

omit [ClosedTerms S] in
/-- The new equation, read through the cache, is a Miller-pattern problem. -/
theorem cached_problem_is_pattern (state : State program) (call : Term S Γ sort) (fixes : Fixes program state call)
    (cache : Cache state) (complete : cache.remaining = []) (index : ι)
    (lhsPattern : Pattern S (program index).arity (program index).lhs) :
    ProblemPattern ((extendedCache state cache complete).remaining ++
      ContextualResidual.mapProblem (extendedCache state cache complete).answer (addedProblem state index)) := by
  obtain ⟨value, holds, _, reads⟩ := fixes
  have valueRead := reads cache.declaration cache.answer
    ((ContextualResidual.models_observeProblem _ _).mp (cache.completed complete))
  change ProblemPattern (ContextualResidual.mapProblem
    (ContextualStoredRows.liftCaptures (scopedLocals program) cache.answer) (addedProblem state index))
  rw [added_problem_of_shared state index value holds.2]
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  constructor
  · change Pattern S _ (instantiate (ContextualStoredRows.liftCaptures (scopedLocals program) cache.answer)
      (instantiate (schemaAt program state.1.declarations index (ruleScope state.1.occupied state.2))
        (program index).lhs))
    rw [lifted_schema]
    exact instantiate_preserves _ (fun _ => generator_pattern _) _ lhsPattern
  · change Pattern S _ (instantiate (ContextualStoredRows.liftCaptures (scopedLocals program) cache.answer)
      (instantiate (ContextualSelectionViews.capturedSource (scopedLocals program) state.1.declarations) value))
    rw [ContextualStoredRows.liftCaptures_on_shared_value, valueRead, Rigid.instantiate_include]
    exact ContextualPatternFragment.rigid_inclusion_pattern _ call

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- The actual incremental run: the cached prefix is transported across the fresh holes, and only
the new equation is solved. -/
def solveCached (state : State program) (index : ι) (cache : Cache state) (complete : cache.remaining = [])
    (fuel : Nat) : ContextualFrameWorklist.Result (firingProblem state index) :=
  ((ContextualFrameWorklist.Result.residual (extendedCache state cache complete)).resume fuel
    (addedProblem state index)).cast (observed_problem_split state index).symm

omit [ClosedTerms S] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- The readings of a firing are exactly the instances of a completed answer of its problem. -/
theorem completed_readings (state : State program) (index : ι) (valid : Admitted program state index)
    (present : state.1.inventory.configuration.present = {state.2})
    (result : ContextualFrameUpdate.Update (firingProblem state index)) (finished : result.remaining = []) :
    ∀ answer, Reads program (destination program state index valid) answer ↔
      ∃ (Future : Type) (future : Future → MetaArity S) (factor : Assignment result.declaration future),
        instantiate factor (instantiate result.answer
          (output program state.1.declarations index state.1.occupied state.2)) = Rigid.includeTerm future answer := by
  have answerSolves := result.completed finished
  intro answer
  constructor
  · rintro ⟨Future, future, solution, made, ⟨_, madeShared⟩, solutionSolves, observed⟩
    have same : made = output program state.1.declarations index state.1.occupied state.2 :=
      ContextualStoredRows.Row.shared.inj (madeShared.symm.trans (destination_holds state index valid present).2)
    subst same
    obtain ⟨factor, components⟩ := (result.completed_models_iff finished future solution).mp
      ((ContextualResidual.models_observeProblem _ _).mpr solutionSolves)
    exact ⟨Future, future, factor,
      (ContextualFrameUnifier.factor_terms _ _ factor components _).symm.trans observed⟩
  · rintro ⟨Future, future, factor, read⟩
    refine ⟨Future, future, Assignment.compose factor result.answer, _,
      destination_holds state index valid present, ?_, ?_⟩
    · exact (ContextualResidual.models_observeProblem _ _).mp
        (ContextualResidual.models_compose answerSolves factor)
    · rw [Assignment.instantiate_compose]
      exact read

omit [ClosedTerms S] in
/-- **Principal answers with the actual incremental solver.** At a fixed call with a completed
cache, the incremental run of an admitted Miller-pattern equation completes, and the readings of the
firing are exactly the instances of its answer. -/
theorem cached_principal (state : State program) (call : Term S Γ sort) (fixes : Fixes program state call)
    (cache : Cache state) (complete : cache.remaining = []) (index : ι)
    (lhsPattern : Pattern S (program index).arity (program index).lhs) (valid : Admitted program state index) :
    ∃ (fuel : Nat) (result : ContextualFrameUpdate.Update (firingProblem state index)),
      solveCached state index cache complete fuel = .residual result ∧ result.remaining = [] ∧
        ∀ answer, Reads program (destination program state index valid) answer ↔
          ∃ (Future : Type) (future : Future → MetaArity S) (factor : Assignment result.declaration future),
            instantiate factor (instantiate result.answer
              (output program state.1.declarations index state.1.occupied state.2)) =
                Rigid.includeTerm future answer := by
  obtain ⟨fuel, finished⟩ := ContextualPatternTermination.finishes_resuming (extendedCache state cache complete)
    (addedProblem state index) (cached_problem_is_pattern state call fixes cache complete index lhsPattern)
  have castFinished := finished.cast (observed_problem_split state index).symm
  change ContextualPatternTermination.Finished (solveCached state index cache complete fuel) at castFinished
  generalize computed : solveCached state index cache complete fuel = outcome at castFinished
  cases castFinished with
  | solved result empty =>
      obtain ⟨_, holds, _, _⟩ := fixes
      exact ⟨fuel, result, computed, empty, completed_readings state index valid holds.1 result empty⟩
  | refuted proof =>
      obtain ⟨Later, later, candidate, solved⟩ := valid.solvable
      exact False.elim (proof later candidate ((ContextualResidual.models_observeProblem _ _).mpr solved))

/-! ## Runs with the actual solver at every firing -/

omit [ClosedTerms S] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
variable (program) in
/-- The empty store's solver result: the actual zero-fuel run. -/
def initialCache (call : Term S Γ sort) : Cache (initial (program := program) call) :=
  @ContextualFrameWorklist.identity S Empty inferInstance (ground S) []

/-- A run of the step together with the actual completed incremental solver result at every
firing. Neither the constructors nor the caches mention a source rewrite. -/
inductive SolverPath (call : Term S Γ sort) : (state : State program) → Cache state → Prop
  | initial : SolverPath call (initial call) (initialCache program call)
  | step {state : State program} {cache : Cache state} (prior : SolverPath call state cache)
      (complete : cache.remaining = []) (index : ι) (valid : Admitted program state index) (fuel : Nat)
      (next : Cache (destination program state index valid))
      (computed : solveCached state index cache complete fuel = .residual next) (finished : next.remaining = []) :
      SolverPath call (destination program state index valid) next

omit [ClosedTerms S] in
theorem SolverPath.complete {call : Term S Γ sort} {state : State program} {cache : Cache state}
    (path : SolverPath call state cache) : cache.remaining = [] := by
  cases path with
  | initial => rfl
  | step _ _ _ _ _ _ _ finished => exact finished

omit [ClosedTerms S] in
theorem SolverPath.semantic {call : Term S Γ sort} {state : State program} {cache : Cache state}
    (path : SolverPath call state cache) :
    Relation.ReflTransGen (Transition program) (ProgramBinders.initial call) state := by
  induction path with
  | initial => exact .refl
  | step _ _ index valid _ _ _ _ ih => exact ih.tail ⟨index, valid, rfl⟩

/-- **Source runs come with actual solver results.** For a program of determinate Miller-pattern
equations, every source run is a run of the step whose every firing has a completed incremental
solver result, and its last state fixes the answer. -/
theorem runs_with_solvers (determinate : ∀ index, Determinate (program index))
    (patterns : ∀ index, Pattern S (program index).arity (program index).lhs)
    {call answer : Term S Γ sort} (runs : Relation.ReflTransGen (Rewrites program) call answer) :
    ∃ (state : State program) (cache : Cache state), SolverPath call state cache ∧ Fixes program state answer := by
  induction runs with
  | refl => exact ⟨initial call, initialCache program call, .initial, initial_fixes call⟩
  | tail _ rewriting ih =>
      obtain ⟨state, cache, path, fixes⟩ := ih
      obtain ⟨index, answered⟩ := rewriting
      obtain ⟨θ, matched, _⟩ := answered
      have valid := (valid_iff state _ fixes.determines index).mpr ⟨θ, matched⟩
      obtain ⟨answer', answered', fixesNext⟩ := fixes_destination state _ fixes index valid (determinate index)
      have same := Determinate.answer_unique (determinate index) answered' ⟨θ, matched, by assumption⟩
      subst same
      obtain ⟨fuel, result, computed, empty, _⟩ :=
        cached_principal state _ fixes cache path.complete index (patterns index) valid
      exact ⟨destination program state index valid, result,
        .step path path.complete index valid fuel result computed empty, fixesNext⟩

/-- **Adequacy with the actual solver.** For a program of determinate Miller-pattern equations,
source runs reach exactly the readings of the step's runs with actual completed solver results. -/
theorem execution_with_solvers_iff (determinate : ∀ index, Determinate (program index))
    (patterns : ∀ index, Pattern S (program index).arity (program index).lhs) (call answer : Term S Γ sort) :
    Relation.ReflTransGen (Rewrites program) call answer ↔
      ∃ (state : State program) (cache : Cache state), SolverPath call state cache ∧ Reads program state answer := by
  constructor
  · intro runs
    obtain ⟨state, cache, path, fixes⟩ := runs_with_solvers determinate patterns runs
    exact ⟨state, cache, path, fixes.determines.1⟩
  · rintro ⟨state, cache, path, reads⟩
    exact (execution_iff call answer).mpr ⟨state, path.semantic, reads⟩

#print axioms Fixes.determines
#print axioms initial_fixes
#print axioms Determinate.answer_unique
#print axioms fixes_destination
#print axioms cached_problem_is_pattern
#print axioms completed_readings
#print axioms cached_principal
#print axioms SolverPath.semantic
#print axioms runs_with_solvers
#print axioms execution_with_solvers_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders
