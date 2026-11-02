import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRPremiseInstances
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSequence

/-! The actual compiled clause body realizes its successful source join
and guards. All premises share the restricted source substitution, retain
their authored indices and produce one complete event history. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClausePremises

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding
open GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem compiled_split (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? pools ordinal clause = some rule) :
    clause.RangeRestricted ∧ ∃ positive guards : List Syntax.Premise,
      List.Forall₂ (fun entry premise => ∃ code, Join.atom? pools entry.2 entry.1 = some code ∧
        premise = .relationQuery Query.factRelation [code]) clause.positiveAtoms.zipIdx positive ∧
      List.Forall₂ (fun entry premise => ∃ left right,
        Join.argument? pools entry.2 0 entry.1.left = some left ∧
        Join.argument? pools entry.2 1 entry.1.right = some right ∧
        premise = .relationQuery (Join.comparisonName entry.1.operator) [left,right])
        ((Comparisons.guards clause).zipIdx clause.positiveAtoms.length) guards ∧
      rule.premises = positive ++ guards := by
  obtain ⟨restricted,native,body,actual⟩ := BodyCompilation.compiled_body pools ordinal clause rule compiled
  have entries : (Join.orderedBody clause).zipIdx =
      clause.positiveAtoms.zipIdx.map (fun entry => (Mettapedia.Languages.Datalog.Premise.atom entry.1,entry.2)) ++
      ((Comparisons.guards clause).zipIdx clause.positiveAtoms.length).map
        (fun entry => (Mettapedia.Languages.Datalog.Premise.comparison entry.1,entry.2)) := by
    rw [BodyCompilation.ordered_body,List.zipIdx_append]
    simp only [List.zipIdx_map,List.length_map,Nat.zero_add]
    rfl
  rw [entries,List.mapM_append] at body
  simp only [List.mapM_map,Function.comp_def] at body
  change (((clause.positiveAtoms.zipIdx.mapM fun entry => Join.bodyPremise? pools entry.2 (.atom entry.1))).bind fun positive =>
    (((Comparisons.guards clause).zipIdx clause.positiveAtoms.length).mapM fun entry => Join.bodyPremise? pools entry.2 (.comparison entry.1)).bind
      fun guards => some (positive ++ guards)) = some native at body
  simp only [Option.bind_eq_some_iff,Option.some.injEq] at body
  obtain ⟨positive,positiveCompiled,guards,guardsCompiled,rfl⟩ := body
  refine ⟨restricted,positive.map Query.lowerPremise,guards.map Query.lowerPremise,?_,?_,?_⟩
  · apply List.forall₂_map_right_iff.mpr
    exact (CompilationFlow.mapM_relation _ _ _ positiveCompiled).imp (fun entry premise formed =>
      BodyCompilation.atom_premise pools entry.2 entry.1 premise formed)
  · apply List.forall₂_map_right_iff.mpr
    exact (CompilationFlow.mapM_relation _ _ _ guardsCompiled).imp (fun entry premise formed =>
      BodyCompilation.guard_premise pools entry.2 entry.1 premise formed)
  · simpa only [List.map_append] using actual

theorem all_body (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (ordinal : Nat) (clause : Clause) (source : ProgramGrounding.ClauseAt program ordinal clause)
    (rule : RewriteRule) (compiled : Query.compileClause? prepared.vocabulary ordinal clause = some rule)
    (facts : List GroundFact) (codes : List Pattern)
    (encoded : List.Forall₂ (fun fact code => Executable.fact? prepared.vocabulary fact = some code) facts codes)
    (row : Mettapedia.Languages.Datalog.Join.Row)
    (joined : row ∈ Mettapedia.Languages.Datalog.Join.join clause.positiveAtoms facts [])
    (holds : ∀ comparison ∈ Comparisons.guards clause,
      Comparisons.Holds Executable.policy (Mettapedia.Languages.Datalog.Join.assignment row.environment) comparison)
    (environment : GeneralPremise.Environment) (context : GeneralPremise.Context)
    (provider : environment.provider = (Executable.snapshot prepared codes).provider)
    (terms : environment.language.terms = Query.baseLanguage.terms)
    (free : environment.free = FreeTypeContext.ofList (Executable.freeTypes prepared.vocabulary))
    (body : context.rule.premises = rule.premises)
    (extra : List (String × TypeExpr))
    (ctx : context.rule.typeContext = BindingContext.context prepared.vocabulary clause ++ extra)
    (bound : context.bound = []) (depth : context.quantifierDepth = 0) (start : context.premiseIndex = 0)
    (admitted : admittedFor context.rule context.spec = true)
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (initial : ScopedRuleMatching.Assignment)
    (before : ScopedCompatible 0 (BindingTyping.ofClause prepared.vocabulary clause row.environment row.facts) initial)
    (poolsBound : CompilationFlow.PoolsBound prepared.vocabulary initial) :
    ∃ final history, GeneralPremise.PremisesHold environment context context.rule.premises initial final history ∧
      ScopedCompatible 0 (BindingTyping.ofClause prepared.vocabulary clause row.environment row.facts) final ∧
      CompilationFlow.VariablesBound clause.providedVariables final ∧
      CompilationFlow.PoolsBound prepared.vocabulary final := by
  obtain ⟨restricted,positive,guards,positiveCompiled,guardsCompiled,same⟩ := compiled_split prepared.vocabulary ordinal clause rule compiled
  have actualBody : context.rule.premises = positive ++ guards := body.trans same
  have positivePositions : PremiseInstances.AtRulePositions context positive := by
    intro offset premise present
    rw [actualBody,start,Nat.zero_add,List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1]
    exact present
  obtain ⟨middle,positiveHistory,positiveHeld,compatible,providedBound⟩ := PremiseInstances.positive_sequence prepared clause facts codes encoded row joined
    environment provider terms free clause.positiveAtoms.zipIdx positive positiveCompiled
    (fun entry member => List.mk_mem_zipIdx_iff_getElem?.mp member) context extra ctx bound depth positivePositions admitted zero initial before
  have names : (clause.positiveAtoms.zipIdx.flatMap fun entry => entry.1.variables) = clause.providedVariables := by
    have mapped := congrArg (fun atoms : List Mettapedia.Languages.Datalog.Atom => atoms.flatMap (·.variables))
      (List.zipIdx_map_fst 0 clause.positiveAtoms)
    simpa only [List.flatMap_map,Function.comp_def,Clause.providedVariables] using mapped
  rw [names] at providedBound
  have retainedPools := GeneralPremise.BoundNames.extension poolsBound positiveHeld.extension
  have guardPositions : PremiseInstances.AtRulePositions (context.after positive.length) guards := by
    intro offset premise present
    simp only [GeneralPremise.Context.after_rule,GeneralPremise.Context.after_index,start,Nat.zero_add]
    rw [actualBody,List.getElem?_append_right (Nat.le_add_right _ _)]
    simpa only [Nat.add_sub_cancel_left] using present
  obtain ⟨guardHistory,guardHeld⟩ := PremiseInstances.comparison_sequence program seeds prepared accepted ordinal clause source restricted
    facts codes encoded row joined environment provider free ((Comparisons.guards clause).zipIdx clause.positiveAtoms.length) guards guardsCompiled
    (fun entry member => ⟨List.fst_mem_of_mem_zipIdx member,holds entry.1 (List.fst_mem_of_mem_zipIdx member)⟩)
    (context.after positive.length) extra (by simpa using ctx) (by simpa using bound) (GeneralPremise.Context.after_depth depth _)
    guardPositions (by simpa using admitted) (by simpa using zero) middle compatible retainedPools providedBound
  exact ⟨middle,positiveHistory ++ guardHistory,actualBody ▸ positiveHeld.append guardHeld,compatible,providedBound,retainedPools⟩

#print axioms compiled_split
#print axioms all_body

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClausePremises
