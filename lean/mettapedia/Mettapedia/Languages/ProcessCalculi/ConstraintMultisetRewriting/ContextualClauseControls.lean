import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClausePublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReachControls

/-!
# Two stored-definition calls bind the body of one atomic clause

One schema describes f(x) = b(x,2). The clause calls it with 1 and 2 through
two reads of the same physical row, binds their pair in a body equation,
consumes a token and publishes the pair. Its second output deliberately
retains a shared caller reference. A contradictory body guard rejects the
whole compiled clause despite all its input occurrences being available.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClausePublication.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open SchematicReach.Controls (spaceSignature DataOperator symbol pair)
open ContextualConjunctiveQueries ContextualClauseFrames ContextualClauseProblem ContextualClauseAdmission
open ContextualWorldScopeLedger ContextualScopeSupport

abbrev base := spaceSignature
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := by
  change DecidableEq (DataOperator ⊕ Operator (SchematicReach.spaceDeclaration
    SchematicReach.Controls.dataSignature () (Name := Nat)) sort)
  infer_instance

abbrev queries (_ : Nat) : MetaArity base := ([], ())
abbrev locals (_ : Nat) : MetaArity base := ([], ())
abbrev captures (_ : Nat) : MetaArity base := ([], ())
abbrev actor := queryFamily queries captures
abbrev origin := family queries locals captures

def call {V : Type} {decl : V → MetaArity base} (argument : SchematicReach.Closed decl) := pair (symbol 10) argument
def body {V : Type} {decl : V → MetaArity base} (argument : SchematicReach.Closed decl) :=
  pair (symbol 20) (pair argument (symbol 2))
def placed {V : Type} {decl : V → MetaArity base} (space : Nat) (value : SchematicReach.Closed decl) :=
  SchematicReach.place (SchematicReach.name space) value

def queryVar (identity : Nat) : SchematicReach.Closed actor := generator actor (.inl identity)
def captureVar (identity : Nat) : SchematicReach.Closed actor := generator actor (.inr identity)
def privateVar : SchematicReach.Closed (ContextualSelectionViews.source locals captures) := generator (ContextualSelectionViews.source locals captures) (Sum.inl 0)
def definitionBody := placed 1 (pair (call privateVar) (body privateVar))
def rows (occurrence : Nat) : ContextualStoredRows.Row locals captures [] () :=
  if occurrence = 7 then .schema definitionBody else .shared (placed 3 (symbol 0))
def initial : Configuration (SchematicReach.Closed captures) Nat := ⟨[], {0, 7}⟩
def scopes (_ : Nat) : Finset Nat := ∅
def inventory : Inventory locals captures (O := Nat) [] () := ⟨initial, rows, [], []⟩
def before : ContextualExecution.Endpoint locals Nat [] () where
  Names := Nat
  equality := inferInstance
  declarations := captures
  scopes := scopes
  occupied := ∅
  inventory := inventory
  covered := (coveredWorld_iff locals captures scopes ∅ inventory).mpr (by decide +kernel)

def code : RuleInstance (SchematicReach.Closed actor) :=
  ⟨[placed 3 (symbol 0)],
    [placed 1 (pair (call (symbol 1)) (queryVar 0)), placed 1 (pair (call (symbol 2)) (queryVar 1))],
    [(queryVar 2, pair (queryVar 0) (queryVar 1))],
    [.equal (queryVar 2) (pair (queryVar 0) (queryVar 1))],
    [placed 9 (queryVar 2), placed 9 (pair (queryVar 0) (captureVar 0))]⟩
def plan : ContextualPublication.Plan (SchematicReach.Closed actor) := ⟨code, [true, false], rfl⟩
def selected : Selection Nat := ⟨[0], [7, 7], [90, 91]⟩
def sourceProblem := problem queries locals captures selected code rows initial
def q (identity : Nat) : SchematicReach.Closed origin := generator origin (.inl identity)
def r (scope : Nat) : SchematicReach.Closed origin := generator origin (.inr (.inl (ScopedVar.at scope 0)))

theorem source_problem_explicit :
    sourceProblem =
      [(placed 3 (symbol 0), placed 3 (symbol 0)),
       (placed 1 (pair (call (symbol 1)) (q 0)), placed 1 (pair (call (r 3)) (body (r 3)))),
       (placed 1 (pair (call (symbol 2)) (q 1)), placed 1 (pair (call (r 4)) (body (r 4)))),
       (q 2, pair (q 0) (q 1))] := by
  with_unfolding_all rfl

def model {Next : Type} (next : Next → MetaArity base) (caller : Assignment captures next) : Assignment origin next
  | .inl identity =>
      if identity = 0 then body (symbol 1)
      else if identity = 1 then body (symbol 2)
      else if identity = 2 then pair (body (symbol 1)) (body (symbol 2))
      else symbol 77
  | .inr (.inl name) => symbol (if name.scope = 3 then 1 else 2)
  | .inr (.inr identity) => caller identity

theorem source_model {Next : Type} (next : Next → MetaArity base) (caller : Assignment captures next) :
    ContextualFrameUnifier.Models (model next caller) sourceProblem := by
  rw [source_problem_explicit]
  intro equation member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> with_unfolding_all rfl

theorem source_admitted : Admitted queries locals captures selected code rows initial := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨Nat, captures, model captures (generator captures), source_model captures (generator captures)⟩, ?_⟩
  intro check member Next next candidate solved
  have only : check = .equal (queryVar 2) (pair (queryVar 0) (queryVar 1)) := List.mem_singleton.mp member
  subst check
  change instantiate candidate (q 2) = instantiate candidate (pair (q 0) (q 1))
  exact solved (q 2, pair (q 0) (q 1)) (by change (q 2, pair (q 0) (q 1)) ∈ sourceProblem; rw [source_problem_explicit]; simp)

theorem covered : RuleCovered (privateScopes scopes) ∅ code := by
  apply (ruleRoots_covered_iff (privateScopes scopes) ∅ code).mp
  decide +kernel

theorem patterned : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem sourceProblem) := by
  apply (ContextualPatternFragment.checkProblem_iff _).mp
  decide +kernel

/-- The generic compiler builds its actual solver-backed publication. The
two reads retain their common physical identity and separate schema scopes. -/
theorem actual_compiled_clause : Nonempty (Compiled queries locals (before := before) plan selected) :=
  realize queries locals (before := before) plan selected covered source_admitted patterned

theorem token_and_both_outputs_change_together :
    ∃ compiled : Compiled queries locals (before := before) plan selected,
      compiled.firing.target.inventory.configuration.present = {7, 90, 91} := by
  obtain ⟨compiled⟩ := actual_compiled_clause
  refine ⟨compiled, ?_⟩
  rw [compiled.physical_result]
  decide +kernel

theorem first_output_is_reusable (compiled : Compiled queries locals (before := before) plan selected) :
    compiled.firing.reusable 90 = true := by
  have intents := compiled.intents
  change [compiled.firing.reusable 90, compiled.firing.reusable 91] = [true, false] at intents
  exact (List.cons.inj intents).1

theorem second_output_is_shared (compiled : Compiled queries locals (before := before) plan selected) :
    compiled.firing.reusable 91 = false := by
  have intents := compiled.intents
  change [compiled.firing.reusable 90, compiled.firing.reusable 91] = [true, false] at intents
  exact (List.cons.inj (List.cons.inj intents).2).1

private theorem instantiate_symbol {V Next : Type} {decl : V → MetaArity base} {next : Next → MetaArity base}
    (assignment : Assignment decl next) (number : Nat) : instantiate assignment (symbol number) = symbol number := rfl
private theorem instantiate_pair {V Next : Type} {decl : V → MetaArity base} {next : Next → MetaArity base}
    (assignment : Assignment decl next) (first second : SchematicReach.Closed decl) :
    instantiate assignment (pair first second) = pair (instantiate assignment first) (instantiate assignment second) := rfl
private theorem instantiate_call {V Next : Type} {decl : V → MetaArity base} {next : Next → MetaArity base}
    (assignment : Assignment decl next) (argument : SchematicReach.Closed decl) :
    instantiate assignment (call argument) = call (instantiate assignment argument) := rfl
private theorem instantiate_body {V Next : Type} {decl : V → MetaArity base} {next : Next → MetaArity base}
    (assignment : Assignment decl next) (argument : SchematicReach.Closed decl) :
    instantiate assignment (body argument) = body (instantiate assignment argument) := rfl
private theorem instantiate_placed {V Next : Type} {decl : V → MetaArity base} {next : Next → MetaArity base}
    (assignment : Assignment decl next) (space : Nat) (argument : SchematicReach.Closed decl) :
    instantiate assignment (placed space argument) = placed space (instantiate assignment argument) := rfl

private theorem pair_injective {Next : Type} {next : Next → MetaArity base}
    {first second otherFirst otherSecond : SchematicReach.Closed next}
    (same : pair first second = pair otherFirst otherSecond) : first = otherFirst ∧ second = otherSecond := by
  have arguments := eq_of_heq (Term.op.inj same).2
  have first := Args.cons.inj arguments
  have second := Args.cons.inj first.2
  exact ⟨first.1, second.1⟩

/-- Every original solution returns the two different call results. This
does not select one ground model as the meaning of the clause. -/
theorem all_source_models_compute_the_pair {Next : Type} (next : Next → MetaArity base)
    (candidate : Assignment origin next) (solved : ContextualFrameUnifier.Models candidate sourceProblem) :
    instantiate candidate (q 2) = pair (body (symbol 1)) (body (symbol 2)) := by
  have first := solved (placed 1 (pair (call (symbol 1)) (q 0)), placed 1 (pair (call (r 3)) (body (r 3))))
    (by rw [source_problem_explicit]; simp)
  have second := solved (placed 1 (pair (call (symbol 2)) (q 1)), placed 1 (pair (call (r 4)) (body (r 4))))
    (by rw [source_problem_explicit]; simp)
  have result := solved (q 2, pair (q 0) (q 1)) (by rw [source_problem_explicit]; simp)
  simp only [instantiate_placed, instantiate_pair, instantiate_call, instantiate_body, instantiate_symbol] at first second
  have firstParts := pair_injective (SchematicReach.place_injective first).2
  have secondParts := pair_injective (SchematicReach.place_injective second).2
  have firstArgument := (pair_injective firstParts.1).2
  have secondArgument := (pair_injective secondParts.1).2
  have firstValue := firstParts.2
  have secondValue := secondParts.2
  rw [← firstArgument] at firstValue
  rw [← secondArgument] at secondValue
  simp only [instantiate_pair] at result
  exact result.trans (congrArg₂ pair firstValue secondValue)

/-- The result is compared with the actual stored row, after the actual
solver substitution, rather than only with a source-side prediction. -/
theorem actual_published_pair (compiled : Compiled queries locals (before := before) plan selected) :
    compiled.firing.target.inventory.rows 90 =
      ContextualPublication.ordinary (bank queries locals) compiled.firing.update.declaration
        (placed 9 (pair (body (symbol 1)) (body (symbol 2)))) := by
  have made : 90 ∈ compiled.firing.selection.made := by rw [compiled.selected]; decide +kernel
  rw [compiled.firing.ordinary_row made (first_output_is_reusable compiled)]
  apply congrArg (ContextualPublication.ordinary (bank queries locals) compiled.firing.update.declaration)
  have sourceSolved : ContextualFrameUnifier.Models
      (Assignment.compose compiled.firing.update.answer (frame queries locals captures ∅).assignment) sourceProblem :=
    compiled.solved_source_model
  have bodyValue := all_source_models_compute_the_pair compiled.firing.update.declaration _ sourceSolved
  have atPort := output_at_port queries locals captures ∅ selected code rows
    (by decide +kernel) rfl ⟨0, by decide +kernel⟩
  have sourceValue : queryView queries locals captures
      (code.produce.get ⟨0, by decide +kernel⟩) = placed 9 (q 2) := by with_unfolding_all rfl
  have outputValue : outputs queries locals captures ∅ selected code rows 90 =
      instantiate (frame queries locals captures ∅).assignment (placed 9 (q 2)) :=
    atPort.trans (congrArg (instantiate (frame queries locals captures ∅).assignment) sourceValue)
  rw [compiled.values]
  change instantiate compiled.firing.update.answer (outputs queries locals captures ∅ selected code rows 90) = _
  rw [outputValue]
  exact (Assignment.instantiate_compose compiled.firing.update.answer (frame queries locals captures ∅).assignment
    (placed 9 (q 2))).symm.trans
      ((instantiate_placed (Assignment.compose compiled.firing.update.answer (frame queries locals captures ∅).assignment)
        9 (q 2)).trans (congrArg (placed (decl := compiled.firing.update.declaration) 9) bodyValue))

theorem the_actual_output_refuses_an_aliased_call_result
    (compiled : Compiled queries locals (before := before) plan selected)
    {Next : Type} (next : Next → MetaArity base)
    (candidate : Assignment compiled.firing.target.declarations next) :
    ¬ ContextualGuardMatching.Matches
      (ContextualPublication.privateFamily (bank queries locals) compiled.firing.update.declaration)
      candidate (placed 9 (pair (body (symbol 1)) (body (symbol 1))))
      (compiled.firing.target.inventory.rows 90) := by
  intro matched
  rw [actual_published_pair] at matched
  obtain ⟨extension, images, same⟩ :=
    (ContextualPublication.ordinary_matches_iff (bank queries locals) compiled.firing.update.declaration candidate _ _).mp matched
  simp only [instantiate_placed, instantiate_pair, instantiate_body, instantiate_symbol] at same
  have second := (pair_injective (SchematicReach.place_injective same).2).2
  have argument := (pair_injective (pair_injective second).2).1
  have impossible : (2 : Nat) = 1 := SchematicReach.Controls.symbol_injective argument
  omega

theorem the_shared_output_uses_the_returned_source_environment
    (compiled : Compiled queries locals (before := before) plan selected) :
    compiled.firing.target.inventory.rows 91 = ContextualStoredRows.Row.shared
      (instantiate compiled.continuationEnv (placed 9 (pair (queryVar 0) (captureVar 0)))) :=
  compiled.shared_body_value ⟨1, by decide +kernel⟩ (second_output_is_shared compiled)

def refusedCode : RuleInstance (SchematicReach.Closed actor) :=
  { code with checks := [.equal (queryVar 2) (symbol 999)] }
def refusedPlan : ContextualPublication.Plan (SchematicReach.Closed actor) := ⟨refusedCode, [true, false], rfl⟩

theorem a_contradictory_body_guard_is_refused : ¬ Admitted queries locals captures selected refusedCode rows initial := by
  intro admitted
  have asked := admitted.checks (.equal (queryVar 2) (symbol 999)) (by simp [refusedCode])
  have same := asked Nat captures (model captures (generator captures)) (source_model captures (generator captures))
  change pair (body (symbol 1)) (body (symbol 2)) = (symbol 999 : SchematicReach.Closed captures) at same
  have operators := (Term.op.inj same).1
  cases operators

theorem refusal_cannot_publish_a_partial_body :
    ¬ Nonempty (Compiled queries locals (before := before) refusedPlan selected) := by
  rintro ⟨compiled⟩
  exact a_contradictory_body_guard_is_refused compiled.source_admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClausePublication.Controls
