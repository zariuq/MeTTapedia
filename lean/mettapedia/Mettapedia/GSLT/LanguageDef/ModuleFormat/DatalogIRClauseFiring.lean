import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClausePremises
import Mettapedia.OSLF.MeTTaIL.GeneralVectorInstantiation

/-! A successful source-clause join and its guards construct a complete
typed root firing, from the actual request to the encoded conclusion.
Elaborated rule metadata may extend the context; authored endpoints and
premises are preserved explicitly. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClauseFiring

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding ScopedRuleMatching
open GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem request_binderFree (pools : Join.Pools) : binderFree (RequestInstances.schema pools) = true := by
  have names (inputs : List String) : binderFreeList (inputs.map Pattern.fvar) = true := by
    induction inputs with
    | nil => rfl
    | cons _ _ ih => simpa only [List.map_cons,binderFreeList,binderFree,Bool.true_and] using ih
  simp only [RequestInstances.schema,Join.poolPattern,Join.vector,binderFree,binderFreeList,names,Bool.true_and]

theorem joined_firing (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (ordinal : Nat) (clause : Clause) (source : ProgramGrounding.ClauseAt program ordinal clause)
    (authored : RewriteRule) (compiled : Query.compileClause? prepared.vocabulary ordinal clause = some authored)
    (facts : List GroundFact) (codes : List Pattern)
    (encoded : List.Forall₂ (fun fact code => Executable.fact? prepared.vocabulary fact = some code) facts codes)
    (row : Mettapedia.Languages.Datalog.Join.Row)
    (joined : row ∈ Mettapedia.Languages.Datalog.Join.join clause.positiveAtoms facts [])
    (holds : ∀ comparison ∈ Comparisons.guards clause,
      Comparisons.Holds Executable.policy (Mettapedia.Languages.Datalog.Join.assignment row.environment) comparison)
    (conclusion : GroundFact) (headRead : Grounding.head? row.environment clause.head = some conclusion)
    (environment : GeneralPremise.Environment)
    (provider : environment.provider = (Executable.snapshot prepared codes).provider)
    (terms : environment.language.terms = Query.baseLanguage.terms)
    (free : environment.free = FreeTypeContext.ofList (Executable.freeTypes prepared.vocabulary))
    (index : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
    (fields : rule.left = authored.left ∧ rule.right = authored.right ∧ rule.premises = authored.premises)
    (extra : List (String × TypeExpr))
    (ctx : rule.typeContext = BindingContext.context prepared.vocabulary clause ++ extra)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index = some spec)
    (admitted : admittedFor rule spec = true) (zero : GeneralPremise.checkZeroDependencies spec = true) :
    ∃ target trace captured completed history,
      Executable.fact? prepared.vocabulary conclusion = some target ∧
      GeneralPremise.RootFiring environment [] (.base "DlStatement") (Executable.request prepared.vocabulary)
        index trace captured completed history target := by
  let fixed := BindingTyping.ofClause prepared.vocabulary clause row.environment row.facts
  have fieldsCompiled := FiringReading.compiled_fields prepared.vocabulary ordinal clause authored compiled
  have left : rule.left = RequestInstances.schema prepared.vocabulary := fields.1.trans fieldsCompiled.1
  have restricted := (BodyCompilation.compiled_body prepared.vocabulary ordinal clause authored compiled).1
  have poolReads := BindingTyping.clause_pools prepared.vocabulary clause row.environment row.facts
  have requestTyped := PhysicalTyping.request_open environment.language terms prepared.vocabulary
  have leftShape : VectorFirstOrder rule.left := by rw [left]; exact RequestInstances.request_shape _
  have leftFree : binderFree rule.left = true := by rw [left]; exact request_binderFree _
  have leftDefined : Defined fixed rule.left.freeFvarNames := by
    rw [left]
    exact RequestInstances.request_defined _ _ poolReads
  have leftInstance : applyBindings fixed rule.left = Executable.request prepared.vocabulary := by
    rw [left]
    exact RequestInstances.request_instance _ _ poolReads
  obtain ⟨captured,matching,compatible,capturedTyped,capturedObjects⟩ := ScopedInstances.typed_match environment.language
    prepared.vocabulary clause row.environment row.facts rule spec extra ctx admitted zero .left [] rule.left
    (Executable.request prepared.vocabulary) leftShape leftFree (.left rule) leftDefined leftInstance
    (.base "DlStatement") requestTyped [] (by intro entry member; cases member)
  have capturedPools : CompilationFlow.PoolsBound prepared.vocabulary captured := by
    apply CompilationFlow.request_pools
    rw [← left]
    exact GeneralPremise.matching_bound_names matching
  obtain ⟨completed,history,premises,after,variablesBound,poolsBound⟩ := ClausePremises.all_body program seeds prepared accepted ordinal clause source
    authored compiled facts codes encoded row joined holds environment ⟨index,rule,spec,[],0,0⟩ provider terms free fields.2.2 extra ctx
    rfl rfl rfl admitted zero captured compatible capturedPools
  have headCompiled : Join.atom? prepared.vocabulary clause.body.length clause.head = some rule.right := by
    rw [fields.2.1]
    exact fieldsCompiled.2
  have headBound := CompilationFlow.head_bound prepared.vocabulary clause restricted rule.right headCompiled completed poolsBound variablesBound
  have canonical : ∀ fact ∈ facts, ∃ code, Executable.fact? prepared.vocabulary fact = some code := by
    intro fact member
    obtain ⟨code,_,formed⟩ := SourceQueries.encoded_member prepared.vocabulary facts codes encoded fact member
    exact ⟨code,formed⟩
  have variablesRead := BindingTyping.clause_variables prepared.vocabulary clause row.environment row.facts
    (JoinInstances.environment_values prepared.vocabulary clause.positiveAtoms facts row canonical joined)
    (Mettapedia.Languages.Datalog.Join.clause_join_names clause facts row joined)
  have headEncoded := PhysicalInstances.atom_instance prepared.vocabulary fixed poolReads _ variablesRead clause.body.length clause.head conclusion
    rule.right headCompiled (Grounding.head?_sound headRead) (by
      intro argument value atArgument _
      exact (restricted.1 .anonymous (List.mem_append_left _ (List.mem_of_getElem? atArgument)) rfl).elim)
  have fixedTyped : CapturesTyped environment.language (FreeTypeContext.ofList (Executable.freeTypes prepared.vocabulary)) [] rule.typeContext fixed := by
    rw [ctx]
    exact BindingTyping.clause_typed_extended environment.language prepared.vocabulary clause row.environment row.facts extra
  have finalTyped := ScopedCompatible.typed_admitted (bound := []) after fixedTyped admitted zero
  have roots := ScopedCompatible.rootValues (bound := []) after fixedTyped
  have dependencies : ∀ name ∈ rule.right.freeFvarNames, dependencies? spec name = some [] := by
    intro name member
    obtain ⟨value,found⟩ := headBound name member
    have included := ConditionalEquationExecution.lookup_assignment_member completed name value found
    obtain ⟨_,type,_,typeDeclared,_,_,_⟩ := finalTyped.1 name value included
    exact dependencies_empty_of_admitted admitted zero typeDeclared
  have reduct := vector_instantiation_exact (operation := ScopedReflectiveExecution.binderOperation environment.reflection rule)
    admitted (InstanceMatching.atom_shape _ _ _ _ headCompiled) (NameCoherent.right rule) headBound roots after dependencies
  have capturedSorted : GeneralPremise.TypedAssignment environment ⟨index,rule,spec,[],0,0⟩ captured := by
    simpa only [GeneralPremise.TypedAssignment,free] using And.intro capturedTyped capturedObjects
  have sourceTyped : OpenPatternWellSorted environment.language environment.free [] (.base "DlStatement")
      (Executable.request prepared.vocabulary) := by rw [free]; exact requestTyped
  have targetTyped : OpenPatternWellSorted environment.language environment.free [] (.base "DlStatement")
      (applyBindings fixed rule.right) := by
    rw [free]
    exact PhysicalTyping.fact_open environment.language terms prepared.vocabulary conclusion _ headEncoded
  obtain ⟨trace,traced⟩ := GeneralScopedMatchMachine.matches_trace matching
  exact ⟨_,trace,captured,completed,history,headEncoded,
    .fire declared specified admitted sourceTyped traced capturedSorted premises reduct targetTyped⟩

theorem authorized_firing (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (ordinal : Nat) (clause : Clause) (source : ProgramGrounding.ClauseAt program ordinal clause)
    (authored : RewriteRule) (compiled : Query.compileClause? prepared.vocabulary ordinal clause = some authored)
    (facts : List GroundFact) (codes : List Pattern)
    (encoded : List.Forall₂ (fun fact code => Executable.fact? prepared.vocabulary fact = some code) facts codes)
    (wanted : GroundInstances.Instance) (authorized : GroundInstances.Authorized Executable.policy ordinal clause facts wanted)
    (environment : GeneralPremise.Environment)
    (provider : environment.provider = (Executable.snapshot prepared codes).provider)
    (terms : environment.language.terms = Query.baseLanguage.terms)
    (free : environment.free = FreeTypeContext.ofList (Executable.freeTypes prepared.vocabulary))
    (index : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
    (fields : rule.left = authored.left ∧ rule.right = authored.right ∧ rule.premises = authored.premises)
    (extra : List (String × TypeExpr))
    (ctx : rule.typeContext = BindingContext.context prepared.vocabulary clause ++ extra)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index = some spec)
    (admitted : admittedFor rule spec = true) (zero : GeneralPremise.checkZeroDependencies spec = true) :
    ∃ target trace captured completed history,
      Executable.fact? prepared.vocabulary wanted.conclusion = some target ∧
      GeneralPremise.RootFiring environment [] (.base "DlStatement") (Executable.request prepared.vocabulary)
        index trace captured completed history target := by
  obtain ⟨row,joined,emitted,formed,_,conclusion⟩ := GroundInstances.source_join_witness Executable.policy ordinal clause facts wanted authorized
  have rowFields := GroundInstances.fromRow?_fields formed
  have holds : ∀ comparison ∈ Comparisons.guards clause,
      Comparisons.Holds Executable.policy (Mettapedia.Languages.Datalog.Join.assignment row.environment) comparison := by
    apply (Comparisons.all?_eq_some_true_iff Executable.policy row.environment (Comparisons.guards clause) ?_).mp rowFields.1
    intro comparison inside
    exact ⟨authorized.1.1 comparison.left (Comparisons.guard_arguments_required inside (by simp [Comparison.arguments])),
      authorized.1.1 comparison.right (Comparisons.guard_arguments_required inside (by simp [Comparison.arguments]))⟩
  have headRead : Grounding.head? row.environment clause.head = some wanted.conclusion :=
    rowFields.2.1.trans (congrArg some conclusion)
  exact joined_firing program seeds prepared accepted ordinal clause source authored compiled facts codes encoded row joined holds wanted.conclusion headRead
    environment provider terms free index rule spec fields extra ctx declared specified admitted zero

#print axioms joined_firing
#print axioms authorized_firing

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClauseFiring
