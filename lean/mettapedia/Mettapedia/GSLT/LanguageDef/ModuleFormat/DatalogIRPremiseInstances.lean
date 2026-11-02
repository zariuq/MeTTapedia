import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRCompilationFlow

/-! The source body's typed queries compose in their actual rule order.
Positive outputs retain all source-variable bindings needed by subsequent
guards. Comparison queries preserve the completed assignment. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.PremiseInstances

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding
open GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

def AtRulePositions (context : GeneralPremise.Context) (premises : List Syntax.Premise) : Prop :=
  ∀ offset premise, premises[offset]? = some premise →
    context.rule.premises[context.premiseIndex + offset]? = some premise

private theorem positions_head {context : GeneralPremise.Context} {premise : Syntax.Premise} {premises : List Syntax.Premise}
    (actual : AtRulePositions context (premise :: premises)) :
    context.rule.premises[context.premiseIndex]? = some premise := by
  simpa only [Nat.add_zero] using actual 0 premise rfl

private theorem positions_tail {context : GeneralPremise.Context} {premise : Syntax.Premise} {premises : List Syntax.Premise}
    (actual : AtRulePositions context (premise :: premises)) : AtRulePositions context.next premises := by
  intro offset item present
  have tail := actual (offset + 1) item (by simpa only [List.getElem?_cons_succ] using present)
  simpa only [GeneralPremise.Context.next,Nat.add_assoc,Nat.add_comm 1 offset] using tail

theorem positive_sequence (prepared : Executable.Prepared) (clause : Clause)
    (facts : List GroundFact) (codes : List Pattern)
    (encoded : List.Forall₂ (fun fact code => Executable.fact? prepared.vocabulary fact = some code) facts codes)
    (row : Mettapedia.Languages.Datalog.Join.Row)
    (joined : row ∈ Mettapedia.Languages.Datalog.Join.join clause.positiveAtoms facts [])
    (environment : GeneralPremise.Environment)
    (provider : environment.provider = (Executable.snapshot prepared codes).provider)
    (terms : environment.language.terms = Query.baseLanguage.terms)
    (free : environment.free = FreeTypeContext.ofList (Executable.freeTypes prepared.vocabulary))
    (entries : List (Mettapedia.Languages.Datalog.Atom × Nat)) (native : List Syntax.Premise)
    (compiled : List.Forall₂ (fun entry premise => ∃ code,
      Join.atom? prepared.vocabulary entry.2 entry.1 = some code ∧ premise = .relationQuery Query.factRelation [code]) entries native)
    (sources : ∀ entry ∈ entries, clause.positiveAtoms[entry.2]? = some entry.1)
    (context : GeneralPremise.Context) (extra : List (String × TypeExpr))
    (ctx : context.rule.typeContext = BindingContext.context prepared.vocabulary clause ++ extra)
    (bound : context.bound = []) (depth : context.quantifierDepth = 0)
    (actual : AtRulePositions context native)
    (admitted : admittedFor context.rule context.spec = true)
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (initial : ScopedRuleMatching.Assignment)
    (before : ScopedCompatible 0 (BindingTyping.ofClause prepared.vocabulary clause row.environment row.facts) initial) :
    ∃ final history, GeneralPremise.PremisesHold environment context native initial final history ∧
      ScopedCompatible 0 (BindingTyping.ofClause prepared.vocabulary clause row.environment row.facts) final ∧
      CompilationFlow.VariablesBound (entries.flatMap (fun entry => entry.1.variables)) final := by
  cases entries with
  | nil =>
    cases compiled
    exact ⟨initial,[],.nil,before,by intro name member; cases member⟩
  | cons entry entries =>
    cases compiled with
    | @cons _ premise _ native first rest =>
      obtain ⟨code,codeCompiled,rfl⟩ := first
      have atSource := sources entry List.mem_cons_self
      have evidence := Mettapedia.Languages.Datalog.Join.join_sound clause.positiveAtoms facts [] joined
      have sourceBound := (List.getElem?_eq_some_iff.mp atSource).1
      have factBound : entry.2 < row.facts.length := by rw [← evidence.2.1.length_eq]; exact sourceBound
      let fact := row.facts[entry.2]
      have atFact : row.facts[entry.2]? = some fact := by simp [fact,factBound]
      obtain ⟨index,middle,trace,query,compatible,produced⟩ := SourceQueries.positive_query prepared clause facts codes encoded row joined
        entry.2 entry.1 fact code atSource atFact codeCompiled environment context provider terms free bound depth
        (positions_head actual) extra ctx admitted zero initial before
      obtain ⟨final,history,held,after,variablesBound⟩ := positive_sequence prepared clause facts codes encoded row joined environment provider terms free
        entries native rest (fun other member => sources other (List.mem_cons_of_mem _ member)) context.next extra ctx bound rfl
        (positions_tail actual) admitted zero middle compatible
      refine ⟨final,_,.cons (.query query) held,after,?_⟩
      have firstBound := (CompilationFlow.output_variables prepared.vocabulary entry.2 entry.1 code codeCompiled middle produced)
      have preserved := GeneralPremise.BoundNames.extension firstBound held.extension
      simpa only [CompilationFlow.VariablesBound,List.flatMap_cons,List.map_append] using preserved.append variablesBound
termination_by entries.length

theorem comparison_sequence (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (ordinal : Nat) (clause : Clause) (source : ProgramGrounding.ClauseAt program ordinal clause) (restricted : clause.RangeRestricted)
    (facts : List GroundFact) (codes : List Pattern)
    (encoded : List.Forall₂ (fun fact code => Executable.fact? prepared.vocabulary fact = some code) facts codes)
    (row : Mettapedia.Languages.Datalog.Join.Row)
    (joined : row ∈ Mettapedia.Languages.Datalog.Join.join clause.positiveAtoms facts [])
    (environment : GeneralPremise.Environment)
    (provider : environment.provider = (Executable.snapshot prepared codes).provider)
    (free : environment.free = FreeTypeContext.ofList (Executable.freeTypes prepared.vocabulary))
    (entries : List (Comparison × Nat)) (native : List Syntax.Premise)
    (compiled : List.Forall₂ (fun entry premise => ∃ left right,
      Join.argument? prepared.vocabulary entry.2 0 entry.1.left = some left ∧
      Join.argument? prepared.vocabulary entry.2 1 entry.1.right = some right ∧
      premise = .relationQuery (Join.comparisonName entry.1.operator) [left,right]) entries native)
    (sources : ∀ entry ∈ entries, entry.1 ∈ Comparisons.guards clause ∧
      Comparisons.Holds Executable.policy (Mettapedia.Languages.Datalog.Join.assignment row.environment) entry.1)
    (context : GeneralPremise.Context) (extra : List (String × TypeExpr))
    (ctx : context.rule.typeContext = BindingContext.context prepared.vocabulary clause ++ extra)
    (bound : context.bound = []) (depth : context.quantifierDepth = 0)
    (actual : AtRulePositions context native)
    (admitted : admittedFor context.rule context.spec = true)
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (initial : ScopedRuleMatching.Assignment)
    (before : ScopedCompatible 0 (BindingTyping.ofClause prepared.vocabulary clause row.environment row.facts) initial)
    (poolsBound : CompilationFlow.PoolsBound prepared.vocabulary initial)
    (variablesBound : CompilationFlow.VariablesBound clause.providedVariables initial) :
    ∃ history, GeneralPremise.PremisesHold environment context native initial initial history := by
  cases entries with
  | nil => cases compiled; exact ⟨[],.nil⟩
  | cons entry entries =>
    cases compiled with
    | @cons _ premise _ native first rest =>
      obtain ⟨left,right,leftCompiled,rightCompiled,rfl⟩ := first
      have authored := sources entry List.mem_cons_self
      have leftBound := CompilationFlow.guard_bound prepared.vocabulary clause restricted entry.1 authored.1 entry.2 0
        entry.1.left (by simp [Comparison.arguments]) left leftCompiled initial poolsBound variablesBound
      have rightBound := CompilationFlow.guard_bound prepared.vocabulary clause restricted entry.1 authored.1 entry.2 1
        entry.1.right (by simp [Comparison.arguments]) right rightCompiled initial poolsBound variablesBound
      obtain ⟨index,query⟩ := SourceQueries.comparison_query program seeds prepared accepted ordinal clause source restricted facts codes encoded row joined
        entry.1 authored.1 authored.2 entry.2 left right leftCompiled rightCompiled environment context provider free bound depth
        (positions_head actual) extra ctx admitted zero initial before leftBound rightBound
      obtain ⟨history,held⟩ := comparison_sequence program seeds prepared accepted ordinal clause source restricted facts codes encoded row joined
        environment provider free entries native rest (fun other member => sources other (List.mem_cons_of_mem _ member)) context.next extra
        ctx bound rfl (positions_tail actual) admitted zero initial before poolsBound variablesBound
      exact ⟨_,.cons (.query query) held⟩
termination_by entries.length

#print axioms positive_sequence
#print axioms comparison_sequence

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.PremiseInstances
