import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRQueryInstances
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRPhysicalTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRJoinInstances
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSnapshotReading
import Mettapedia.Languages.Datalog.JoinNameDomain

/-! Source joins and satisfied guards supply actual typed provider queries.
Selected rows, the shared substitution, anonymous occurrence positions and
retained matcher traces are constructed together. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.SourceQueries

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding
open GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem encoded_member (pools : Join.Pools) (facts : List GroundFact) (codes : List Pattern)
    (encoded : List.Forall₂ (fun fact code => Executable.fact? pools fact = some code) facts codes)
    (fact : GroundFact) (member : fact ∈ facts) :
    ∃ code ∈ codes, Executable.fact? pools fact = some code := by
  induction encoded with
  | nil => cases member
  | @cons head code facts codes first rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨code,List.mem_cons_self,first⟩
    · obtain ⟨other,present,formed⟩ := ih member
      exact ⟨other,List.mem_cons_of_mem _ present,formed⟩

private theorem query_coherent (context : GeneralPremise.Context) (relation : String)
    (arguments : List Pattern)
    (selected : context.rule.premises[context.premiseIndex]? = some (.relationQuery relation arguments))
    (depth : context.quantifierDepth = 0) (index : Nat) (code : Pattern)
    (atCode : arguments[index]? = some code) : NameCoherent context.rule (context.site index) [] code := by
  intro suffix
  simp only [GeneralPremise.Context.site,sitePattern?,selected,depth,quantifiedBody?,
    Option.bind_eq_bind,Option.bind_some,atCode,List.nil_append]

theorem positive_query (prepared : Executable.Prepared) (clause : Clause)
    (facts : List GroundFact) (codes : List Pattern)
    (encoded : List.Forall₂ (fun fact code => Executable.fact? prepared.vocabulary fact = some code) facts codes)
    (row : Mettapedia.Languages.Datalog.Join.Row)
    (joined : row ∈ Mettapedia.Languages.Datalog.Join.join clause.positiveAtoms facts [])
    (position : Nat) (source : Mettapedia.Languages.Datalog.Atom) (fact : GroundFact) (code : Pattern)
    (atSource : clause.positiveAtoms[position]? = some source) (atFact : row.facts[position]? = some fact)
    (compiled : Join.atom? prepared.vocabulary position source = some code)
    (environment : GeneralPremise.Environment) (context : GeneralPremise.Context)
    (provider : environment.provider = (Executable.snapshot prepared codes).provider)
    (terms : environment.language.terms = Query.baseLanguage.terms)
    (free : environment.free = FreeTypeContext.ofList (Executable.freeTypes prepared.vocabulary))
    (bound : context.bound = []) (depth : context.quantifierDepth = 0)
    (selected : context.rule.premises[context.premiseIndex]? = some (.relationQuery Query.factRelation [code]))
    (extra : List (String × TypeExpr))
    (ctx : context.rule.typeContext = BindingContext.context prepared.vocabulary clause ++ extra)
    (admitted : admittedFor context.rule context.spec = true)
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (initial : ScopedRuleMatching.Assignment)
    (before : ScopedCompatible 0 (BindingTyping.ofClause prepared.vocabulary clause row.environment row.facts) initial) :
    ∃ index final trace,
      GeneralPremise.TracedQuery environment context Query.factRelation [code] initial index final [(0,trace)] ∧
      ScopedCompatible 0 (BindingTyping.ofClause prepared.vocabulary clause row.environment row.facts) final ∧
      GeneralPremise.BoundNames final code.freeFvarNames := by
  have canonical : ∀ fact ∈ facts, ∃ code, Executable.fact? prepared.vocabulary fact = some code := by
    intro fact member
    obtain ⟨code,_,formed⟩ := encoded_member prepared.vocabulary facts codes encoded fact member
    exact ⟨code,formed⟩
  have evidence := Mettapedia.Languages.Datalog.Join.join_sound clause.positiveAtoms facts [] joined
  have sourceBound := (List.getElem?_eq_some_iff.mp atSource).1
  have factBound := (List.getElem?_eq_some_iff.mp atFact).1
  have matched : source.Matches (Mettapedia.Languages.Datalog.Join.assignment row.environment) fact := by
    have actual := evidence.2.1.get sourceBound factBound
    simpa only [List.get_eq_getElem,(List.getElem?_eq_some_iff.mp atSource).2,
      (List.getElem?_eq_some_iff.mp atFact).2] using actual
  have member : fact ∈ facts := by
    have actual := evidence.2.2.get factBound (by simpa only [← evidence.2.2.length_eq] using factBound)
    exact List.mem_of_getElem? (by simpa only [List.get_eq_getElem,(List.getElem?_eq_some_iff.mp atFact).2] using actual)
  obtain ⟨target,targetMember,targetEncoded⟩ := encoded_member prepared.vocabulary facts codes encoded fact member
  have atOrdered : (Join.orderedBody clause)[position]? = some (.atom source) := by
    rw [BodyCompilation.ordered_body,List.getElem?_append_left (by simpa using sourceBound)]
    simp only [List.getElem?_map,atSource,Option.map_some]
  have pools := BindingTyping.clause_pools prepared.vocabulary clause row.environment row.facts
  have variablesRead := BindingTyping.clause_variables prepared.vocabulary clause row.environment row.facts
    (JoinInstances.environment_values prepared.vocabulary clause.positiveAtoms facts row canonical joined)
    (Mettapedia.Languages.Datalog.Join.clause_join_names clause facts row joined)
  have anonymous : ∀ index value, source.arguments[index]? = some .anonymous → fact.values[index]? = some value →
      ∃ physical, PhysicalInstances.value? prepared.vocabulary value = some physical ∧
        (BindingTyping.ofClause prepared.vocabulary clause row.environment row.facts).lookup (Join.anonymousVariable position index) = some physical := by
    intro index value atArgument atValue
    exact BindingTyping.clause_anonymous prepared.vocabulary clause row.environment row.facts position index source fact value
      atOrdered atArgument atFact atValue (JoinInstances.fact_values_in_pool prepared.vocabulary fact target targetEncoded value
        (List.mem_of_getElem? atValue))
  have defined := PhysicalInstances.atom_defined prepared.vocabulary _ pools _ variablesRead position source fact code compiled matched anonymous
  have instantiated : applyBindings (BindingTyping.ofClause prepared.vocabulary clause row.environment row.facts) code = target := by
    have actual := PhysicalInstances.atom_instance prepared.vocabulary _ pools _ variablesRead position source fact code compiled matched anonymous
    exact Option.some.inj (actual.symm.trans targetEncoded)
  obtain ⟨index,atTarget⟩ := List.mem_iff_getElem?.mp targetMember
  have present : environment.provider.rows[index]? = some ⟨Query.factRelation,[target]⟩ := by
    rw [provider]
    change (((Query.provider codes).rows ++ prepared.staticRows)[index]?) = _
    rw [List.getElem?_append_left (by simpa [Query.provider] using (List.getElem?_eq_some_iff.mp atTarget).1)]
    simp only [Query.provider,List.getElem?_map,atTarget,Option.map_some]
  have signature := SnapshotReading.fact_signature prepared codes
  rw [← provider] at signature
  obtain ⟨final,trace,held,compatible⟩ := QueryInstances.output_query prepared.vocabulary clause row.environment row.facts
    environment context extra ctx bound free admitted zero code target (InstanceMatching.atom_shape _ _ _ _ compiled)
    (ClauseDictionary.atom_binderFree _ _ _ _ compiled)
    (query_coherent context Query.factRelation [code] selected depth 0 code rfl) defined instantiated
    (PhysicalTyping.fact_open environment.language terms prepared.vocabulary fact target targetEncoded) index present signature initial before
  refine ⟨index,final,trace,held,compatible,?_⟩
  simpa [GeneralPremise.queryOutputNames] using held.readout.produces _ signature

theorem comparison_query (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (ordinal : Nat) (clause : Clause) (source : ProgramGrounding.ClauseAt program ordinal clause) (restricted : clause.RangeRestricted)
    (facts : List GroundFact) (codes : List Pattern)
    (encoded : List.Forall₂ (fun fact code => Executable.fact? prepared.vocabulary fact = some code) facts codes)
    (row : Mettapedia.Languages.Datalog.Join.Row)
    (joined : row ∈ Mettapedia.Languages.Datalog.Join.join clause.positiveAtoms facts [])
    (comparison : Comparison) (inClause : comparison ∈ Comparisons.guards clause)
    (holds : Comparisons.Holds Executable.policy (Mettapedia.Languages.Datalog.Join.assignment row.environment) comparison)
    (position : Nat) (leftCode rightCode : Pattern)
    (leftCompiled : Join.argument? prepared.vocabulary position 0 comparison.left = some leftCode)
    (rightCompiled : Join.argument? prepared.vocabulary position 1 comparison.right = some rightCode)
    (environment : GeneralPremise.Environment) (context : GeneralPremise.Context)
    (provider : environment.provider = (Executable.snapshot prepared codes).provider)
    (free : environment.free = FreeTypeContext.ofList (Executable.freeTypes prepared.vocabulary))
    (bound : context.bound = []) (depth : context.quantifierDepth = 0)
    (selected : context.rule.premises[context.premiseIndex]? =
      some (.relationQuery (Join.comparisonName comparison.operator) [leftCode,rightCode]))
    (extra : List (String × TypeExpr))
    (ctx : context.rule.typeContext = BindingContext.context prepared.vocabulary clause ++ extra)
    (admitted : admittedFor context.rule context.spec = true)
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (initial : ScopedRuleMatching.Assignment)
    (before : ScopedCompatible 0 (BindingTyping.ofClause prepared.vocabulary clause row.environment row.facts) initial)
    (leftDefined : GeneralPremise.BoundNames initial leftCode.freeFvarNames)
    (rightDefined : GeneralPremise.BoundNames initial rightCode.freeFvarNames) :
    ∃ index, GeneralPremise.TracedQuery environment context (Join.comparisonName comparison.operator)
      [leftCode,rightCode] initial index initial [(0,[]),(1,[])] := by
  have canonical : ∀ fact ∈ facts, ∃ code, Executable.fact? prepared.vocabulary fact = some code := by
    intro fact member
    obtain ⟨code,_,formed⟩ := encoded_member prepared.vocabulary facts codes encoded fact member
    exact ⟨code,formed⟩
  have pools := BindingTyping.clause_pools prepared.vocabulary clause row.environment row.facts
  have variablesRead := BindingTyping.clause_variables prepared.vocabulary clause row.environment row.facts
    (JoinInstances.environment_values prepared.vocabulary clause.positiveAtoms facts row canonical joined)
    (Mettapedia.Languages.Datalog.Join.clause_join_names clause facts row joined)
  have leftNamed : comparison.left ≠ .anonymous := restricted.1 comparison.left
    (Comparisons.guard_arguments_required inClause (by simp [Comparison.arguments]))
  have rightNamed : comparison.right ≠ .anonymous := restricted.1 comparison.right
    (Comparisons.guard_arguments_required inClause (by simp [Comparison.arguments]))
  have usedOriginal : comparison.operator ∈ Executable.operators program := by
    rcases source with atRule | ⟨fact,_,rfl⟩
    · exact Executable.source_guard_operator (List.mem_of_getElem? atRule) inClause
    · simp [LPBridge.groundClause,Comparisons.guards] at inClause
  obtain ⟨left,right,leftMatched,rightMatched,compared⟩ := holds
  obtain ⟨leftValue,leftEncoded,leftRead⟩ := PhysicalInstances.argument_instance prepared.vocabulary _ pools _ variablesRead
    position 0 comparison.left leftCode left leftCompiled leftMatched (fun same => (leftNamed same).elim)
  obtain ⟨rightValue,rightEncoded,rightRead⟩ := PhysicalInstances.argument_instance prepared.vocabulary _ pools _ variablesRead
    position 1 comparison.right rightCode right rightCompiled rightMatched (fun same => (rightNamed same).elim)
  have leftTyped := PhysicalTyping.value_encoded_open environment.language prepared.vocabulary left leftValue leftEncoded
  have rightTyped := PhysicalTyping.value_encoded_open environment.language prepared.vocabulary right rightValue rightEncoded
  obtain ⟨leftIndex,leftAt,rfl⟩ := Option.map_eq_some_iff.mp leftEncoded
  obtain ⟨rightIndex,rightAt,rfl⟩ := Option.map_eq_some_iff.mp rightEncoded
  have present : (⟨Join.comparisonName comparison.operator,
      [Executable.valueRef leftIndex,Executable.valueRef rightIndex]⟩ : GeneralPremise.ProviderRow)
      ∈ (Executable.snapshot prepared codes).provider.rows := by
    apply (Executable.snapshot_comparison_row_iff program seeds prepared accepted codes comparison.operator leftIndex rightIndex).mpr
    exact ⟨usedOriginal,left,right,
      by obtain ⟨inside,same,_⟩ := List.idxOf?_eq_some_iff.mp leftAt; simp [inside,same],
      by obtain ⟨inside,same,_⟩ := List.idxOf?_eq_some_iff.mp rightAt; simp [inside,same],compared⟩
  obtain ⟨index,atRow⟩ := List.mem_iff_getElem?.mp present
  have used : comparison.operator ∈ Executable.operators prepared.source := by
    rw [(Executable.prepare_typed program seeds prepared accepted).1]
    exact usedOriginal
  have signature := SnapshotReading.comparison_signature prepared codes comparison.operator used
  rw [← provider] at atRow signature
  have rowTyped : GeneralPremise.RowTyped environment.language environment.free context.bound
      ⟨Join.comparisonName comparison.operator,[.base "DlValue",.base "DlValue"],[.input,.input]⟩
      ⟨Join.comparisonName comparison.operator,[Executable.valueRef leftIndex,Executable.valueRef rightIndex]⟩ := by
    constructor
    · rfl
    · rw [free,bound]
      exact .cons leftTyped (.cons rightTyped .nil)
  exact ⟨index,QueryInstances.input_query prepared.vocabulary clause row.environment row.facts environment context extra ctx bound free
    admitted zero (Join.comparisonName comparison.operator) leftCode rightCode _ _
    (ClauseDictionary.argument_variable _ _ _ _ _ leftCompiled) (ClauseDictionary.argument_variable _ _ _ _ _ rightCompiled)
    (query_coherent context _ [leftCode,rightCode] selected depth 0 leftCode rfl)
    (query_coherent context _ [leftCode,rightCode] selected depth 1 rightCode rfl)
    initial before leftDefined rightDefined leftRead rightRead index atRow signature rowTyped⟩

#print axioms positive_query
#print axioms comparison_query

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.SourceQueries
