import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseStateRefinement
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseBinderControls

/-!
# A queried function computes the key of a subsequent source join

The function is lambda z. pair(z,2). Applying its captured body to 1 gives
the key pair(1,2), whose answer is 7. The whole source firing also takes a
permit and publishes the answer. The competing key pair(2,2), with answer
9, cannot be selected by the same computation.

Function opening, contextual application, the dependent lookup and the
effect use the ordinary clause compiler and actual worklist. No evaluator
callback supplies the computed key or the answer.
The controls use the solver specification and preserve pending equations;
they assert neither a numerical completing budget nor an empty residual.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedJoinControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualClauseFrames ContextualConditionalRows
open ContextualClausePublication.BinderControls (DataOperator dataSignature base locals captures queries actor origin
  symbol pair lam located function callBody sourceCall)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (result : base.Srt) : DecidableEq (base.Op result) := by
  change DecidableEq (DataOperator ⊕ Operator (SchematicReach.spaceDeclaration dataSignature () (Name := Nat)) result)
  infer_instance

def answer : SchematicReach.Closed actor := generator actor (.inl true)
def sourceAnswer : SchematicReach.Closed origin := generator origin (.inl true)
def edge {V : Type} {decl : V → MetaArity base}
    (key value : SchematicReach.Closed decl) := located 2 (pair key value)

def store (occurrence : Nat) : Row locals captures [] () :=
  ofStored locals captures (.shared
    (if occurrence = 0 then located 1 (function captures)
     else if occurrence = 1 then edge (pair (symbol 1) (symbol 2)) (symbol 7)
     else if occurrence = 2 then edge (pair (symbol 2) (symbol 2)) (symbol 9)
     else located 5 (symbol 99)))

def world : ContextualClauseSourceState.World locals Nat [] () :=
  ⟨Empty, inferInstance, captures, [], {0, 1, 2, 3}, store⟩
def code : RuleInstance (SchematicReach.Closed actor) :=
  ⟨[located 5 (symbol 99)],
    [located 1 (lam (generator actor (.inl false))), edge (callBody 1) answer],
    [], [], [located 9 answer]⟩
def plan : ContextualPublication.Plan (SchematicReach.Closed actor) := ⟨code, [true], rfl⟩
def picked : Selection Nat := ⟨[3], [0, 1], [4]⟩
def problem := ContextualClauseSourceState.information queries locals world plan picked

theorem problem_explicit : problem =
    [(observe (located 5 (symbol 99)), observe (located 5 (symbol 99))),
     (observe (located 1 (lam (generator origin (.inl false)))), observe (located 1 (function origin))),
     (observe (edge (sourceCall 1) sourceAnswer),
      observe (edge (pair (symbol 1) (symbol 2)) (symbol 7)))] := by
  with_unfolding_all rfl

def model {V : Type} (decl : V → MetaArity base) : Assignment origin decl
  | .inl false => pair (.var .zero) (symbol 2)
  | .inl true => symbol 7
  | .inr (.inl ⟨_, impossible⟩) => nomatch impossible
  | .inr (.inr impossible) => nomatch impossible

theorem source_model {V : Type} (decl : V → MetaArity base) : ContextualResidual.Models (model decl) problem := by
  rw [problem_explicit]
  intro equation member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

private theorem pair_injective {V : Type} {decl : V → MetaArity base}
    {first second third fourth : SchematicReach.Closed decl}
    (same : pair first second = pair third fourth) : first = third ∧ second = fourth := by
  have fields := Args.cons.inj (eq_of_heq (Term.op.inj same).2)
  exact ⟨fields.1, (Args.cons.inj fields.2).1⟩

private theorem function_computes {V : Type} (decl : V → MetaArity base) (candidate : Assignment origin decl)
    (functionEq : instantiate candidate (located 1 (lam (generator origin (.inl false)))) =
      instantiate candidate (located 1 (function origin))) :
    instantiate candidate (sourceCall 1) = pair (symbol 1) (symbol 2) := by
  apply ContextualClausePublication.BinderControls.source_body_applies_its_argument decl candidate ?_ 1
  rw [ContextualClausePublication.BinderControls.source_problem_explicit]
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  exact functionEq

theorem every_source_model_has_the_computed_key {V : Type} (decl : V → MetaArity base)
    (candidate : Assignment origin decl) (solved : ContextualResidual.Models candidate problem) :
    instantiate candidate (sourceCall 1) = pair (symbol 1) (symbol 2) := by
  apply function_computes decl candidate
  have equation := solved
    (observe (located 1 (lam (generator origin (.inl false)))), observe (located 1 (function origin)))
    (by rw [problem_explicit]; simp)
  exact observe_injective equation

theorem every_source_model_answers_seven {V : Type} (decl : V → MetaArity base)
    (candidate : Assignment origin decl) (solved : ContextualResidual.Models candidate problem) :
    instantiate candidate sourceAnswer = symbol 7 := by
  have equation := solved
    (observe (edge (sourceCall 1) sourceAnswer), observe (edge (pair (symbol 1) (symbol 2)) (symbol 7)))
    (by rw [problem_explicit]; simp)
  change observe (instantiate candidate (edge (sourceCall 1) sourceAnswer)) =
    observe (instantiate candidate (edge (pair (symbol 1) (symbol 2)) (symbol 7))) at equation
  have terms := observe_injective equation
  change located 2 (pair (instantiate candidate (sourceCall 1)) (instantiate candidate sourceAnswer)) =
    located 2 (pair (pair (symbol 1) (symbol 2)) (symbol 7)) at terms
  have values := (SchematicReach.place_injective terms).2
  change pair (instantiate candidate (sourceCall 1)) (instantiate candidate sourceAnswer) =
    pair (pair (symbol 1) (symbol 2)) (symbol 7) at values
  exact (pair_injective values).2

theorem source_admitted : ContextualClauseSourceState.Admitted queries locals world plan picked := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨Empty, captures, model captures, source_model captures⟩, ?_⟩
  intro check member
  cases member

abbrev before := world.native ∅

theorem the_published_schema_has_exactly_the_source_answer
    (compiled : ContextualConditionalClauses.Compiled queries locals (before := before) plan picked)
    {Next : Type} (next : Next → MetaArity base)
    (candidate : Assignment compiled.firing.target.declarations next) (pattern : SchematicReach.Closed next) :
    Matches (ContextualPublication.privateFamily (bank queries locals) compiled.firing.update.declaration)
      compiled.firing.target.declarations candidate pattern (compiled.firing.target.rows 4) ↔
        pattern = located 9 (symbol 7) := by
  have kinds := compiled.intents
  change [compiled.firing.reusable 4] = [true] at kinds
  have ordinary := (List.cons.inj kinds).1
  apply (compiled.ordinary_body_instances ⟨0, by decide +kernel⟩ ordinary next candidate pattern).trans
  change ContextualPublication.SourceInstances problem (located 9 sourceAnswer) next pattern ↔ _
  constructor
  · rintro ⟨extension, images, solved, same⟩
    have answer := every_source_model_answers_seven extension.declarations images solved
    have exactValue : instantiate images (located 9 sourceAnswer) = located 9 (symbol 7) := by
      change located 9 (instantiate images sourceAnswer) = _
      erw [answer]
    apply extension.instantiate_injective
    exact same.symm.trans exactValue
  · intro same
    subst pattern
    exact ⟨ContextualGuardMatching.Extension.identity next, model next, source_model next, rfl⟩

theorem a_real_firing_preserves_the_dependent_join (fuel : Nat) :
    ∃ compiled : ContextualConditionalClauses.Compiled queries locals (before := before) plan picked,
      compiled.firing.fuel = fuel ∧ compiled.firing.target.present = {0, 1, 2, 4} := by
  obtain ⟨compiled, budget⟩ := ContextualConditionalClauses.realize queries locals
    (before := before) plan picked source_admitted fuel
  refine ⟨compiled, budget, ?_⟩
  rw [compiled.physical_result]
  decide +kernel

theorem the_independent_source_result_agrees_with_the_actual_target
    (compiled : ContextualConditionalClauses.Compiled queries locals (before := before) plan picked)
    {Next : Type} (next : Next → MetaArity base)
    (candidate : Assignment compiled.firing.target.declarations next) (pattern : SchematicReach.Closed next) :
    Matches (ContextualClauseSourceState.resultLocals queries locals world)
      (ContextualClauseSourceState.resultFamily queries locals world)
      (Assignment.compose candidate compiled.sourceFrame.assignment) pattern
      ((ContextualClauseSourceState.target queries locals world plan picked).rows 4) ↔
        pattern = located 9 (symbol 7) :=
  (ContextualClauseStateRefinement.produced_matches (before := world) (occupied := ∅)
    (plan := plan) (picked := picked) compiled ⟨0, by decide +kernel⟩ next candidate pattern).trans
    (the_published_schema_has_exactly_the_source_answer compiled next candidate pattern)

def sharedPlan : ContextualPublication.Plan (SchematicReach.Closed actor) := ⟨code, [false], rfl⟩

theorem the_shared_case_has_an_actual_refinement (fuel : Nat) :
    ∃ compiled : ContextualConditionalClauses.Compiled queries locals (before := before) sharedPlan picked,
      compiled.firing.fuel = fuel ∧
      ∀ (Next : Type) (next : Next → MetaArity base)
        (candidate : Assignment compiled.firing.target.declarations next) (pattern : SchematicReach.Closed next),
        Matches (ContextualClauseSourceState.resultLocals queries locals world)
          (ContextualClauseSourceState.resultFamily queries locals world)
          (Assignment.compose candidate compiled.sourceFrame.assignment) pattern
          ((ContextualClauseSourceState.target queries locals world sharedPlan picked).rows 4) ↔
        Matches (ContextualPublication.privateFamily (bank queries locals) compiled.firing.update.declaration)
          compiled.firing.target.declarations candidate pattern (compiled.firing.target.rows 4) := by
  obtain ⟨compiled, budget⟩ := ContextualConditionalClauses.realize queries locals
    (before := before) sharedPlan picked source_admitted fuel
  refine ⟨compiled, budget, ?_⟩
  intro Next next candidate pattern
  exact ContextualClauseStateRefinement.produced_matches (before := world) (occupied := ∅)
    (plan := sharedPlan) (picked := picked) compiled ⟨0, by decide +kernel⟩ next candidate pattern

def wrongPicked : Selection Nat := ⟨[3], [0, 2], [4]⟩
def wrongProblem := ContextualClauseSourceState.information queries locals world plan wrongPicked

theorem wrong_problem_explicit : wrongProblem =
    [(observe (located 5 (symbol 99)), observe (located 5 (symbol 99))),
     (observe (located 1 (lam (generator origin (.inl false)))), observe (located 1 (function origin))),
     (observe (edge (sourceCall 1) sourceAnswer),
      observe (edge (pair (symbol 2) (symbol 2)) (symbol 9)))] := by
  with_unfolding_all rfl

theorem the_competing_key_has_no_source_firing :
    ¬ ContextualClauseSourceState.Admitted queries locals world plan wrongPicked := by
  intro admitted
  obtain ⟨Future, future, candidate, solved⟩ := admitted.solvable
  change ContextualResidual.Models candidate wrongProblem at solved
  erw [wrong_problem_explicit] at solved
  have functionEq := solved
    (observe (located 1 (lam (generator origin (.inl false)))), observe (located 1 (function origin)))
    (List.mem_cons_of_mem _ (List.mem_cons_self))
  have computed := function_computes future candidate (observe_injective functionEq)
  have equation := solved
    (observe (edge (sourceCall 1) sourceAnswer), observe (edge (pair (symbol 2) (symbol 2)) (symbol 9)))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  change observe (instantiate candidate (edge (sourceCall 1) sourceAnswer)) =
    observe (instantiate candidate (edge (pair (symbol 2) (symbol 2)) (symbol 9))) at equation
  have values := (SchematicReach.place_injective (observe_injective equation)).2
  change pair (instantiate candidate (sourceCall 1)) (instantiate candidate sourceAnswer) =
    pair (pair (symbol 2) (symbol 2)) (symbol 9) at values
  have keys := (pair_injective values).1
  have numbers := (pair_injective (computed.symm.trans keys)).1
  have impossible : (1 : Nat) = 2 := DataOperator.symbol.inj
    (Sum.inl.inj (Sum.inl.inj (Term.op.inj numbers).1))
  omega

theorem the_competing_key_has_no_compiled_firing :
    ¬ Nonempty (ContextualConditionalClauses.Compiled queries locals (before := before) plan wrongPicked) := by
  rintro ⟨compiled⟩
  exact the_competing_key_has_no_source_firing compiled.source_admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedJoinControls
