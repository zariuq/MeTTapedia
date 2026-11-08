import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRuleCode
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalClauses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingEntry

/-!
# Two operative uses of one stored rule body

The stored syntax takes request(x) and produces (x, lambda z. z). A source
clause reads that same physical code occurrence twice, obtaining the body
ports through unification. It consumes requests 1 and 2 and produces both
correlated results in one actual firing. The code remains stored.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRuleCode.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualConjunctiveQueries ContextualClauseFrames ContextualConditionalRows
open ContextualConditionalSourceProblem ContextualConditionalSourceAdmission

inductive DataOp where
  | symbol : Nat → DataOp
  | pair
  | request
  | lam
  deriving DecidableEq

abbrev dataSignature : Signature where
  Srt := Unit
  Op _ := DataOp
  arity
    | .symbol _ => []
    | .pair => [([], ()), ([], ())]
    | .request => [([], ())]
    | .lam => [([()], ())]

abbrev base := codeSignature dataSignature ()
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (dataSignature.Op sort) := inferInstanceAs (DecidableEq DataOp)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstance

abbrev locals (_ : Nat) : MetaArity base := ([], ())
abbrev captures (_ : Nat) : MetaArity base := ([], ())
abbrev queries (_ : Nat) : MetaArity base := ([], ())
abbrev actor := queryFamily queries captures
abbrev raw := ContextualSelectionViews.source locals captures
abbrev origin := family queries locals captures
abbrev Tm {V : Type} (decl : V → MetaArity base) := Term (signature base decl) [] ()

def symbol {V : Type} {decl : V → MetaArity base} (number : Nat) : Tm decl :=
  .op (.inl (.original (.symbol number))) .nil
def pair {V : Type} {decl : V → MetaArity base} (first second : Tm decl) : Tm decl :=
  .op (.inl (.original .pair)) (.cons first (.cons second .nil))
def request {V : Type} {decl : V → MetaArity base} (value : Tm decl) : Tm decl :=
  .op (.inl (.original .request)) (.cons value .nil)
def identity {V : Type} (decl : V → MetaArity base) : Tm decl :=
  .op (.inl (.original .lam)) (.cons (.var .zero) .nil)
def result {V : Type} {decl : V → MetaArity base} (value : Tm decl) : Tm decl := pair value (identity decl)

theorem request_injective {V : Type} {decl : V → MetaArity base} {first second : Tm decl}
    (same : request first = request second) : first = second :=
  (Args.cons.inj (eq_of_heq (Term.op.inj same).2)).1

theorem pair_injective {V : Type} {decl : V → MetaArity base} {a b c d : Tm decl}
    (same : pair a b = pair c d) : a = c ∧ b = d := by
  have parts := Args.cons.inj (eq_of_heq (Term.op.inj same).2)
  exact ⟨parts.1, (Args.cons.inj parts.2).1⟩

theorem symbol_injective {V : Type} {decl : V → MetaArity base} {first second : Nat}
    (same : (symbol first : Tm decl) = symbol second) : first = second :=
  DataOp.symbol.inj (CodeOp.original.inj (Sum.inl.inj (Term.op.inj same).1))

def q (number : Nat) : Tm actor := generator actor (.inl number)
def privateValue : Tm raw := generator raw (.inl 0)
def storedBody : RuleInstance (Tm raw) := ⟨[request privateValue], [], [], [], [result privateValue]⟩
def queryBody (left right : Nat) : RuleInstance (Tm actor) := ⟨[q left], [], [], [], [q right]⟩
def plainRows (occurrence : Nat) : ContextualStoredRows.Row locals captures [] () :=
  if occurrence = 7 then .schema (encode storedBody)
  else .shared (request (symbol (if occurrence = 0 then 1 else 2)))
def rows (occurrence : Nat) : Row locals captures [] () := ofStored locals captures (plainRows occurrence)
def before : ContextualConditionalExecution.State locals Nat [] () where
  Names := Nat
  equality := inferInstance
  declarations := captures
  occupied := ∅
  equations := []
  present := {0, 1, 7}
  rows := rows

def code : RuleInstance (Tm actor) :=
  ⟨[q 0, q 2], [encode (queryBody 0 1), encode (queryBody 2 3)], [], [], [pair (q 1) (q 3)]⟩
def plan : ContextualPublication.Plan (Tm actor) := ⟨code, [true], rfl⟩
def selected : Selection Nat := ⟨[0, 1], [7, 7], [90]⟩
def sourceProblem := problem queries locals captures selected code rows before.equations
def queryValue (number : Nat) : Tm origin := generator origin (.inl number)
def rowValue (scope : Nat) : Tm origin := generator origin (.inr (.inl (ScopedVar.at scope 0)))
def sourceBody (scope : Nat) : RuleInstance (Tm origin) :=
  ⟨[request (rowValue scope)], [], [], [], [result (rowValue scope)]⟩
def sourceQueryBody (left right : Nat) : RuleInstance (Tm origin) :=
  ⟨[queryValue left], [], [], [], [queryValue right]⟩

theorem source_problem_explicit : sourceProblem =
    [(observe (queryValue 0), observe (request (symbol 1))),
     (observe (queryValue 2), observe (request (symbol 2))),
     (observe (encode (sourceQueryBody 0 1)), observe (encode (sourceBody 4))),
     (observe (encode (sourceQueryBody 2 3)), observe (encode (sourceBody 5)))] := by
  with_unfolding_all rfl

def model {Next : Type} (next : Next → MetaArity base) : Assignment origin next
  | .inl 0 => request (symbol 1)
  | .inl 1 => result (symbol 1)
  | .inl 2 => request (symbol 2)
  | .inl 3 => result (symbol 2)
  | .inl _ => symbol 0
  | .inr (.inl name) => symbol (if name.scope = 4 then 1 else 2)
  | .inr (.inr _) => symbol 0

theorem source_model {Next : Type} (next : Next → MetaArity base) : ContextualResidual.Models (model next) sourceProblem := by
  rw [source_problem_explicit]
  intro equation member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

private theorem one_use_computes_its_body {Next : Type} {next : Next → MetaArity base}
    (candidate : Assignment origin next) (left right scope number : Nat)
    (input : instantiate candidate (queryValue left) = request (symbol number))
    (code : instantiate candidate (encode (sourceQueryBody left right)) = instantiate candidate (encode (sourceBody scope))) :
    instantiate candidate (queryValue right) = result (symbol number) := by
  have bodies := (instantiated_codes_iff candidate (sourceQueryBody left right) (sourceBody scope)).mp code
  have first : instantiate candidate (queryValue left) = request (instantiate candidate (rowValue scope)) :=
    (List.cons.inj (congrArg (fun body => body.take) bodies)).1
  have pinned := request_injective (first.symm.trans input)
  have output : instantiate candidate (queryValue right) = result (instantiate candidate (rowValue scope)) :=
    (List.cons.inj (congrArg (fun body => body.produce) bodies)).1
  exact output.trans (congrArg result pinned)

theorem every_source_model_preserves_both_results {Next : Type} {next : Next → MetaArity base}
    (candidate : Assignment origin next) (solved : ContextualResidual.Models candidate sourceProblem) :
    instantiate candidate (pair (queryValue 1) (queryValue 3)) = pair (result (symbol 1)) (result (symbol 2)) := by
  rw [source_problem_explicit] at solved
  let equations : EquationStore (Tm origin) :=
    [(queryValue 0, request (symbol 1)), (queryValue 2, request (symbol 2)),
     (encode (sourceQueryBody 0 1), encode (sourceBody 4)), (encode (sourceQueryBody 2 3), encode (sourceBody 5))]
  have ordinary := (ContextualResidual.models_observeProblem candidate equations).mp solved
  have firstInput := ordinary (queryValue 0, request (symbol 1)) (by simp [equations])
  have secondInput := ordinary (queryValue 2, request (symbol 2)) (by simp [equations])
  have firstCode := ordinary (encode (sourceQueryBody 0 1), encode (sourceBody 4)) (by simp [equations])
  have secondCode := ordinary (encode (sourceQueryBody 2 3), encode (sourceBody 5)) (by simp [equations])
  have first := one_use_computes_its_body candidate 0 1 4 1 firstInput firstCode
  have second := one_use_computes_its_body candidate 2 3 5 2 secondInput secondCode
  change pair (instantiate candidate (queryValue 1)) (instantiate candidate (queryValue 3)) = _
  rw [first, second]

theorem source_admitted : Admitted queries locals captures selected code rows before.equations before.present := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨Nat, captures, model captures, source_model captures⟩, ?_⟩
  intro check member
  cases member

def scopes (_ : Nat) : Finset Nat := ∅
def inventory : ContextualWorldScopeLedger.Inventory locals captures (O := Nat) [] () :=
  ⟨⟨[], {0, 1, 7}⟩, plainRows, [], []⟩
def endpoint : ContextualExecution.Endpoint locals Nat [] () where
  Names := Nat
  equality := inferInstance
  declarations := captures
  scopes := scopes
  occupied := ∅
  inventory := inventory
  covered := (ContextualWorldScopeLedger.coveredWorld_iff locals captures scopes ∅ inventory).mpr (by decide +kernel)

def ordinaryProblem := ContextualClauseProblem.problem queries locals captures selected code plainRows inventory.configuration

theorem ordinary_problem_agrees : sourceProblem = ContextualResidual.observeProblem ordinaryProblem :=
  ContextualConditionalSourceProblem.problem_ofStored queries locals captures selected code plainRows inventory.configuration

theorem original_source_admitted : ContextualClauseAdmission.Admitted queries locals captures selected code plainRows inventory.configuration :=
  (ContextualConditionalSourceAdmission.admitted_ofEndpoint_iff queries locals endpoint selected code).mp source_admitted

theorem rule_covered : ContextualWorldScopeLedger.RuleCovered (ContextualScopeSupport.privateScopes scopes) ∅ code := by
  apply (ContextualWorldScopeLedger.ruleRoots_covered_iff (ContextualScopeSupport.privateScopes scopes) ∅ code).mp
  decide +kernel

theorem source_patterned : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem ordinaryProblem) := by
  apply (ContextualPatternFragment.checkProblem_iff _).mp
  decide +kernel

theorem an_actual_completed_code_firing_exists :
    Nonempty (ContextualClausePublication.Compiled queries locals (before := endpoint) plan selected) :=
  ContextualClausePublication.realize queries locals (before := endpoint) plan selected rule_covered original_source_admitted source_patterned

theorem the_completed_firing_stores_both_computed_bodies
    (compiled : ContextualClausePublication.Compiled queries locals (before := endpoint) plan selected) :
    compiled.firing.target.inventory.rows 90 = ContextualPublication.ordinary (bank queries locals)
      compiled.firing.update.declaration (pair (result (symbol 1)) (result (symbol 2))) := by
  have made : 90 ∈ compiled.firing.selection.made := by rw [compiled.selected]; decide +kernel
  have reusable : compiled.firing.reusable 90 = true := by
    have kinds := compiled.intents
    exact (List.cons.inj kinds).1
  rw [compiled.firing.ordinary_row made reusable]
  apply congrArg (ContextualPublication.ordinary (bank queries locals) compiled.firing.update.declaration)
  have actualModel : ContextualResidual.Models
      (Assignment.compose compiled.firing.update.answer (frame queries locals captures ∅).assignment) sourceProblem := by
    rw [ordinary_problem_agrees]
    exact (ContextualResidual.models_observeProblem _ _).mpr compiled.solved_source_model
  have sourceValue := every_source_model_preserves_both_results _ actualModel
  have outputValue : ContextualClauseAdmission.outputs queries locals captures ∅ selected code plainRows 90 =
      instantiate (frame queries locals captures ∅).assignment (pair (queryValue 1) (queryValue 3)) := by
    exact (ContextualClausePublication.output_at_port queries locals captures ∅ selected code plainRows
      (by decide +kernel) rfl ⟨0, by decide +kernel⟩).trans (by with_unfolding_all rfl)
  rw [compiled.values]
  change instantiate compiled.firing.update.answer (ContextualClauseAdmission.outputs queries locals captures ∅ selected code plainRows 90) = _
  rw [outputValue]
  exact (Assignment.instantiate_compose compiled.firing.update.answer (frame queries locals captures ∅).assignment _).symm.trans sourceValue

theorem actual_compiled_code_uses :
    ∃ compiled : ContextualConditionalClauses.Compiled queries locals (before := before) plan selected,
      compiled.firing.fuel = 0 ∧ compiled.firing.target.present = {7, 90} := by
  obtain ⟨compiled, budget⟩ := ContextualConditionalClauses.realize queries locals (before := before) plan selected source_admitted 0
  refine ⟨compiled, budget, ?_⟩
  rw [compiled.physical_result]
  decide +kernel

theorem the_code_stays_stored (compiled : ContextualConditionalClauses.Compiled queries locals (before := before) plan selected) :
    7 ∈ compiled.firing.target.present := by
  rw [compiled.physical_result]
  decide +kernel

theorem stored_body_decodes_exactly :
    decode (encode storedBody) = some storedBody := decode_encode storedBody

theorem code_reads_have_no_single_shared_view :
    ¬ ∃ value, value = ContextualStoredRows.viewAt locals captures 4 (.schema (encode storedBody)) ∧
      value = ContextualStoredRows.viewAt locals captures 5 (.schema (encode storedBody)) := by
  rintro ⟨value, first, second⟩
  exact schema_views_ne (S := dataSignature) (atom := ()) locals captures storedBody (by decide +kernel) 0
    (by
      change (Sum.inl 0 : Nat ⊕ Nat) ∈ [Sum.inl 0, Sum.inl 0]
      simp) (first.symm.trans second)

def sharedValue : Tm captures := generator captures 0
def sharedBody : RuleInstance (Tm captures) := ⟨[request sharedValue], [], [], [], [result sharedValue]⟩
def sharedRows (occurrence : Nat) : Row locals captures [] () :=
  if occurrence = 7 then ofStored locals captures (.shared (encode sharedBody)) else rows occurrence
def sharedProblem := problem queries locals captures selected code sharedRows before.equations
def capturedValue : Tm origin := generator origin (.inr (.inr 0))
def sourceSharedBody : RuleInstance (Tm origin) := ⟨[request capturedValue], [], [], [], [result capturedValue]⟩

theorem shared_problem_explicit : sharedProblem =
    [(observe (queryValue 0), observe (request (symbol 1))),
     (observe (queryValue 2), observe (request (symbol 2))),
     (observe (encode (sourceQueryBody 0 1)), observe (encode sourceSharedBody)),
     (observe (encode (sourceQueryBody 2 3)), observe (encode sourceSharedBody))] := by
  with_unfolding_all rfl

theorem explicitly_shared_code_cannot_serve_the_two_incompatible_requests
    {Next : Type} {next : Next → MetaArity base} (candidate : Assignment origin next) :
    ¬ ContextualResidual.Models candidate sharedProblem := by
  intro solved
  rw [shared_problem_explicit] at solved
  let equations : EquationStore (Tm origin) :=
    [(queryValue 0, request (symbol 1)), (queryValue 2, request (symbol 2)),
     (encode (sourceQueryBody 0 1), encode sourceSharedBody), (encode (sourceQueryBody 2 3), encode sourceSharedBody)]
  have ordinary := (ContextualResidual.models_observeProblem candidate equations).mp solved
  have firstInput := ordinary (queryValue 0, request (symbol 1)) (by simp [equations])
  have secondInput := ordinary (queryValue 2, request (symbol 2)) (by simp [equations])
  have firstCode := (instantiated_codes_iff candidate (sourceQueryBody 0 1) sourceSharedBody).mp
    (ordinary (encode (sourceQueryBody 0 1), encode sourceSharedBody) (by simp [equations]))
  have secondCode := (instantiated_codes_iff candidate (sourceQueryBody 2 3) sourceSharedBody).mp
    (ordinary (encode (sourceQueryBody 2 3), encode sourceSharedBody) (by simp [equations]))
  have firstUse := (List.cons.inj (congrArg (fun body => body.take) firstCode)).1
  have secondUse := (List.cons.inj (congrArg (fun body => body.take) secondCode)).1
  have wrong : request (symbol 1) = request (symbol 2) :=
    firstInput.symm.trans (firstUse.trans (secondUse.symm.trans secondInput))
  have impossible : (1 : Nat) = 2 := symbol_injective (request_injective wrong)
  omega

theorem the_shared_version_has_no_source_firing :
    ¬ Admitted queries locals captures selected code sharedRows before.equations before.present := by
  intro admitted
  obtain ⟨Future, future, candidate, solved⟩ := admitted.solvable
  exact explicitly_shared_code_cannot_serve_the_two_incompatible_requests candidate solved

def declaration : Declaration (Tm raw) := ⟨.perSelection, ⟨storedBody, [true], rfl⟩⟩
def declarationRows (occurrence : Nat) : Row locals captures [] () :=
  if occurrence = 7 then ofStored locals captures (.schema (encodeDeclaration declaration)) else rows occurrence
def declarationWorld : ContextualConditionalExecution.State locals Nat [] () := {before with rows := declarationRows}
def picked : Selection Nat := ⟨[0], [], [90]⟩
def entryProblem := problem locals locals captures (ContextualStandingEntry.selected 7 picked)
  (ContextualStandingEntry.activation locals captures declaration).rule declarationRows declarationWorld.equations
def sourceDeclaration (value : Tm origin) : Declaration (Tm origin) :=
  ⟨.perSelection, ⟨⟨[request value], [], [], [], [result value]⟩, [true], rfl⟩⟩

theorem entry_problem_explicit : entryProblem =
    [(observe (request (queryValue 0)), observe (request (symbol 1))),
     (observe (encodeDeclaration (sourceDeclaration (queryValue 0))),
      observe (encodeDeclaration (sourceDeclaration (rowValue 3))))] := by
  with_unfolding_all rfl

def entryModel : Assignment origin captures
  | .inl _ => symbol 1
  | .inr (.inl _) => symbol 1
  | .inr (.inr _) => symbol 0

theorem entry_source_admitted : ContextualStandingEntry.Admitted locals declarationWorld 7 declaration picked := by
  refine ⟨rfl, ?_⟩
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨Nat, captures, entryModel, ?_⟩, ?_⟩
  · change ContextualResidual.Models entryModel entryProblem
    rw [entry_problem_explicit]
    intro equation member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro check member
    cases member

theorem declaration_is_readable_as_data :
    decodeDeclaration (ContextualStoredRows.asTemplate locals captures (declarationRows 7).value) = some declaration :=
  ContextualStandingEntry.admitted_decodes locals declarationWorld 7 declaration picked entry_source_admitted

theorem the_generic_standing_entry_constructs_an_actual_firing :
    ∃ compiled : ContextualStandingEntry.Compiled locals declarationWorld 7 declaration picked,
      compiled.actual.firing.fuel = 0 ∧ compiled.actual.firing.target.present = {1, 7, 90} := by
  obtain ⟨compiled, budget⟩ := ContextualStandingEntry.realize locals declarationWorld 7 declaration picked entry_source_admitted 0
  refine ⟨compiled, budget, ?_⟩
  rw [compiled.actual.physical_result]
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRuleCode.Controls
