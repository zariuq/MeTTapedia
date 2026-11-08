import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReachPublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReachControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTransportedActivationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublicationPlan

/-!
# Solved data is preserved while reusable variables remain independent

The program constrains its first local to 10 and stores a term whose second
local occurs twice. Later reusable reads may choose different values for
that second local; one read must keep its two occurrences equal. The
publication is built from the actual completed worklist return.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublication.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualWorldScopeLedger ContextualScopeSupport
open SchematicReach.Controls (dataSignature spaceSignature locals captures symbol pair)

abbrev base := spaceSignature
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := by
  change DecidableEq (SchematicReach.Controls.DataOperator ⊕
    Operator (SchematicReach.spaceDeclaration dataSignature () (Name := Nat)) sort)
  infer_instance

abbrev raw := ContextualSelectionViews.source locals captures
abbrev active := ContextualSelectionViews.target locals captures

def rawVariable (identity : Nat) : SchematicReach.Closed raw := generator raw (.inl identity)
def localVariable (identity : Nat) : SchematicReach.Closed active :=
  generator active (.inl (ScopedVar.at 1 identity))
def template : SchematicReach.Closed active := pair (localVariable 0) (pair (localVariable 1) (localVariable 1))
def rawTemplate : SchematicReach.Closed raw := pair (rawVariable 0) (pair (rawVariable 1) (rawVariable 1))
def outputs (_ : Nat) : SchematicReach.Closed active := SchematicReach.place (SchematicReach.name 1) template
def selected : Selection Nat := ⟨[],[],[99]⟩

def rawRule : NamedSpaces.LocatedRule (SchematicReach.Closed raw) :=
  ⟨[],[],[(rawVariable 0,symbol 10)],[],[(SchematicReach.name 1,rawTemplate)]⟩
def rule := rawRule.toRule (SchematicReach.spaceTerms raw)
def addresses (_ : Nat) : SchematicReach.Closed captures := SchematicReach.name 2
def payloads (_ : Nat) : ContextualStoredRows.Row locals captures [] () := .shared (generator captures 0)
def rows := SchematicReach.placedRows locals captures addresses payloads
def initial : Configuration (SchematicReach.Closed captures) Nat := ⟨[],{7}⟩
def inventory : Inventory locals captures (O := Nat) [] () := ⟨initial,rows,[],[]⟩
def scopes (_ : Nat) : Finset Nat := ∅
def start : ContextualExecution.Endpoint locals Nat [] () where
  Names := Nat
  equality := inferInstance
  declarations := captures
  scopes := scopes
  occupied := ∅
  inventory := inventory
  covered := (coveredWorld_iff locals captures scopes ∅ inventory).mpr (by decide +kernel)

def problem := ContextualActivatedStep.problem locals captures ∅ selected rule rows initial
def observed := ContextualResidual.observeProblem problem

theorem problem_explicit : problem = [(localVariable 0,symbol 10)] := by with_unfolding_all rfl

def sourceModel {Next : Type} (next : Next → MetaArity base) (value : Nat) : Assignment active next
  | .inl ⟨_,identity⟩ => if identity = 0 then symbol 10 else symbol value
  | .inr _ => symbol 0

theorem source_model (value : Nat) : ContextualResidual.Models (sourceModel captures value) observed := by
  apply (ContextualResidual.models_observeProblem _ _).mpr
  rw [problem_explicit]
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  with_unfolding_all rfl

def localResult := ContextualFrameWorklist.runWithRefuter
  (fun declaration problem => ContextualEquationRefutation.choose (S := base) (source := declaration) problem)
  1 active observed

def updateOption {Variables : Type} {declaration : Variables → MetaArity base}
    {problem : ContextualResidual.Problem declaration} :
    ContextualFrameWorklist.Result problem → Option (ContextualFrameUpdate.Update problem)
  | .residual update => some update
  | .refuted _ => none

theorem actual_return_is_residual : (updateOption localResult).isSome = true := by decide +kernel
def update : ContextualFrameUpdate.Update observed := (updateOption localResult).get actual_return_is_residual

theorem extracted_return {Variables : Type} {declaration : Variables → MetaArity base}
    {problem : ContextualResidual.Problem declaration} (result : ContextualFrameWorklist.Result problem)
    (present : (updateOption result).isSome = true) :
    result = .residual ((updateOption result).get present) := by
  cases result with
  | residual update => rfl
  | refuted _ => cases present

theorem actual_run : ContextualFrameWorklist.run 1 active observed = .residual update := by
  rw [ContextualFrameWorklist.run_eq_local_on_model 1 observed captures (sourceModel captures 20) (source_model 20)]
  exact extracted_return localResult actual_return_is_residual

theorem finished : update.remaining = [] := by decide +kernel

theorem covered_rule : RuleCovered (privateScopes scopes) ∅ rule := by
  apply (ruleRoots_covered_iff (privateScopes scopes) ∅ rule).mp
  decide +kernel

theorem admission : ContextualGuardedStep.Requirements locals captures ∅ selected rule rows initial outputs := by
  refine ⟨by decide,by decide,rfl,rfl,?_,by decide,?_⟩
  · with_unfolding_all rfl
  · intro check member
    cases member

def sharedTarget := ContextualExecution.computedTarget locals start rule selected outputs covered_rule admission update

def execution : ContextualExecution.Firing locals start sharedTarget where
  rule := rule
  ruleCovered := covered_rule
  selection := selected
  outputs := outputs
  fuel := 1
  update := update
  admitted := admission
  computed := actual_run
  empty := finished
  destination := rfl

def firing (reusable : Bool) : ContextualPublication.Firing (before := start) :=
  ⟨sharedTarget,execution,fun _ => reusable⟩

def answer (value : Nat) {Next : Type} (next : Next → MetaArity base) : SchematicReach.Closed next :=
  SchematicReach.place (SchematicReach.name 1) (pair (symbol 10) (pair (symbol value) (symbol value)))

theorem source_instances_of_answer {Next : Type} (next : Next → MetaArity base) (value : Nat) :
    SourceInstances observed (outputs 99) next (answer value next) := by
  refine ⟨ContextualGuardMatching.Extension.identity next,sourceModel next value,?_,?_⟩
  · apply (ContextualResidual.models_observeProblem _ _).mpr
    rw [problem_explicit]
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    with_unfolding_all rfl
  · with_unfolding_all rfl

theorem the_reusable_output_has_both_independent_readings {Next : Type}
    (next : Next → MetaArity base) (candidate : Assignment (firing true).target.declarations next) :
    ContextualGuardMatching.Matches (privateFamily locals update.declaration) candidate (answer 20 next)
        ((firing true).target.inventory.rows 99) ∧
      ContextualGuardMatching.Matches (privateFamily locals update.declaration) candidate (answer 30 next)
        ((firing true).target.inventory.rows 99) := by
  constructor
  · exact ((firing true).ordinary_matches_source (by decide) rfl next candidate _).mpr
      (source_instances_of_answer next 20)
  · exact ((firing true).ordinary_matches_source (by decide) rfl next candidate _).mpr
      (source_instances_of_answer next 30)

theorem physical_result_is_one_committed_output :
    (firing true).target.inventory.configuration.present = {7,99} := by decide +kernel

theorem query_rows_do_not_rewrite_the_retained_owner :
    (firing true).target.inventory.rows 7 = .shared
      (instantiate (ContextualComputedFreshFrame.includeSource update)
        (SchematicReach.place (SchematicReach.name 2)
          (instantiate (ContextualSelectionViews.capturedTarget locals captures) (generator captures 0)))) := by
  with_unfolding_all rfl

def residualIdentity : update.Variables := by
  with_unfolding_all exact Sum.inl (ScopedVar.at 1 1)

def residualTerm : SchematicReach.Closed update.declaration := by
  with_unfolding_all exact generator update.declaration residualIdentity

theorem normalized_output_keeps_the_binding :
    instantiate update.answer (outputs 99) = SchematicReach.place (SchematicReach.name 1)
      (pair (symbol 10) (pair residualTerm residualTerm)) := by
  with_unfolding_all rfl

private theorem pair_injective {Next : Type} {next : Next → MetaArity base}
    {first second otherFirst otherSecond : SchematicReach.Closed next}
    (same : pair first second = pair otherFirst otherSecond) : first = otherFirst ∧ second = otherSecond := by
  have arguments := eq_of_heq (Term.op.inj same).2
  have first := Args.cons.inj arguments
  have second := Args.cons.inj first.2
  exact ⟨first.1,second.1⟩

theorem a_single_read_keeps_the_repeated_variable_equal {Next : Type}
    (next : Next → MetaArity base) (candidate : Assignment (firing true).target.declarations next) :
    ¬ ContextualGuardMatching.Matches (privateFamily locals update.declaration) candidate
      (SchematicReach.place (SchematicReach.name 1) (pair (symbol 10) (pair (symbol 20) (symbol 30))))
      ((firing true).target.inventory.rows 99) := by
  intro matched
  have source := ((firing true).ordinary_matches_source (by decide) rfl next candidate _).mp matched
  obtain ⟨extension,model,_,same⟩ := source
  change SchematicReach.place (SchematicReach.name 1)
    (pair (instantiate model (localVariable 0))
      (pair (instantiate model (localVariable 1)) (instantiate model (localVariable 1)))) =
    SchematicReach.place (SchematicReach.name 1) (pair (symbol 10) (pair (symbol 20) (symbol 30))) at same
  have repeated := pair_injective (pair_injective (SchematicReach.place_injective same).2).2
  have impossible : (20 : Nat) = 30 := SchematicReach.Controls.symbol_injective (repeated.1.symm.trans repeated.2)
  omega

theorem shared_publication_keeps_one_shared_reading {Next : Type}
    (next : Next → MetaArity base) (candidate : Assignment (firing false).target.declarations next) :
    ¬ (ContextualGuardMatching.Matches (privateFamily locals update.declaration) candidate (answer 20 next)
        ((firing false).target.inventory.rows 99) ∧
      ContextualGuardMatching.Matches (privateFamily locals update.declaration) candidate (answer 30 next)
        ((firing false).target.inventory.rows 99)) := by
  rintro ⟨first,second⟩
  rw [(firing false).shared_row (by decide) rfl] at first second
  change answer 20 next = _ at first
  change answer 30 next = _ at second
  have same := first.trans second.symm
  have components := pair_injective (pair_injective (SchematicReach.place_injective same).2).2
  have impossible : (20 : Nat) = 30 := SchematicReach.Controls.symbol_injective components.1
  omega

def wrongAnswer {Next : Type} (next : Next → MetaArity base) : SchematicReach.Closed next :=
  SchematicReach.place (SchematicReach.name 1) (pair (symbol 11) (pair (symbol 20) (symbol 20)))

def wrongImages {Next : Type} (next : Next → MetaArity base) : Assignment active next
  | .inl ⟨_,identity⟩ => if identity = 0 then symbol 11 else symbol 20
  | .inr _ => symbol 0

theorem zero_fuel_has_not_solved_the_binding :
    (ContextualFrameWorklist.identity observed).remaining ≠ [] := by decide +kernel

theorem discarding_the_residual_queue_admits_a_wrong_result {Next : Type}
    (next : Next → MetaArity base) (candidate : Assignment (firing true).target.declarations next) :
    ContextualGuardMatching.Matches (privateFamily locals active) candidate (wrongAnswer next)
      (ordinary locals active
        (instantiate (ContextualFrameWorklist.identity observed).answer (outputs 99))) := by
  apply (ordinary_matches_iff locals active candidate _ _).mpr
  refine ⟨ContextualGuardMatching.Extension.identity next,wrongImages next,?_⟩
  change instantiate (wrongImages next) (instantiate (generator active) (outputs 99)) = _
  rw [instantiate_identity]
  with_unfolding_all rfl

theorem the_original_source_refuses_that_wrong_result {Next : Type} (next : Next → MetaArity base) :
    ¬ SourceInstances observed (outputs 99) next (wrongAnswer next) := by
  rintro ⟨extension,candidate,model,same⟩
  have equations := (ContextualResidual.models_observeProblem candidate problem).mp model
  rw [problem_explicit] at equations
  have bound := equations _ List.mem_cons_self
  change instantiate candidate (localVariable 0) = symbol 10 at bound
  change SchematicReach.place (SchematicReach.name 1)
    (pair (instantiate candidate (localVariable 0))
      (pair (instantiate candidate (localVariable 1)) (instantiate candidate (localVariable 1)))) =
    SchematicReach.place (SchematicReach.name 1) (pair (symbol 11) (pair (symbol 20) (symbol 20))) at same
  have first := (pair_injective (SchematicReach.place_injective same).2).1
  have impossible : (10 : Nat) = 11 := SchematicReach.Controls.symbol_injective (bound.symm.trans first)
  omega

def mixedRule : RuleInstance (SchematicReach.Closed raw) :=
  { rule with produce := [SchematicReach.place (SchematicReach.name 1) rawTemplate,
    SchematicReach.place (SchematicReach.name 1) rawTemplate] }
def mixedSelection : Selection Nat := ⟨[],[],[99,100]⟩
def mixedPlan : Plan (SchematicReach.Closed raw) := ⟨mixedRule,[true,false],rfl⟩

theorem mixed_problem_unchanged :
    ContextualActivatedStep.problem locals captures ∅ mixedSelection mixedRule rows initial = problem := by
  with_unfolding_all rfl

theorem mixed_covered : RuleCovered (privateScopes scopes) ∅ mixedRule := by
  apply (ruleRoots_covered_iff (privateScopes scopes) ∅ mixedRule).mp
  decide +kernel

theorem mixed_admitted : ContextualGuardedStep.Valid locals captures ∅ mixedSelection
    mixedRule rows initial outputs := by
  refine ⟨⟨by decide,by decide,rfl,rfl,?_,by decide,?_⟩,?_⟩
  · with_unfolding_all rfl
  · intro check member
    cases member
  · rw [mixed_problem_unchanged]
    exact ContextualFrameUnifier.solvable_of_model
      ((ContextualResidual.models_observeProblem _ _).mp (source_model 20))

theorem mixed_patterned : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
    (ContextualActivatedStep.problem locals captures ∅ mixedSelection mixedRule rows initial)) := by
  apply (ContextualPatternFragment.checkProblem_iff _).mp
  decide +kernel

theorem one_atomic_firing_publishes_both_storage_kinds :
    ∃ firing : ContextualPublication.Firing (before := start), firing.rule = mixedRule ∧
      firing.selection = mixedSelection ∧ firing.outputs = outputs ∧
      firing.reusable 99 = true ∧ firing.reusable 100 = false ∧
      firing.target.inventory.configuration.present = {7,99,100} := by
  obtain ⟨firing,ruleEq,selectionEq,outputsEq,kinds⟩ :=
    realize_planned_publication locals start mixedPlan mixedSelection outputs mixed_covered mixed_admitted mixed_patterned
  have shape : [firing.reusable 99,firing.reusable 100] = [true,false] := kinds
  have first := (List.cons.inj shape).1
  have second := (List.cons.inj (List.cons.inj shape).2).1
  refine ⟨firing,ruleEq,selectionEq,outputsEq,first,second,?_⟩
  rw [firing.physical_result,selectionEq]
  change MeTTaCalculus.OccurrenceCommits.fire initial.present (mixedSelection.commit (T := Unit)) = {7,99,100}
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublication.Controls
