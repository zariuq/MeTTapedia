import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRPremiseReading
import Mettapedia.Languages.Datalog.ClauseInference

/-! A compiled root firing satisfies its source clause, including the
positive body and primitive guards under the very same variable assignment. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClauseSoundness

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralScopedMatch
open GeneralFirstOrderProjection

private theorem guard_used (program : Program) (ordinal : Nat) (clause : Clause)
    (source : ProgramGrounding.ClauseAt program ordinal clause)
    (comparison : Comparison) (guard : comparison ∈ Comparisons.guards clause) :
    comparison.operator ∈ Executable.operators program := by
  rcases source with atRule | ⟨fact,_,rfl⟩
  · exact Executable.source_guard_operator (List.mem_of_getElem? atRule) guard
  · simp [LPBridge.groundClause,Comparisons.guards] at guard

theorem root_body_readout (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern) (facts : List GroundFact)
    (represented : ∀ value ∈ known, ∃ fact ∈ facts, Executable.decodeFact? prepared value = some fact)
    (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (source : ProgramGrounding.ClauseAt program ordinal clause)
    (compiled : Query.compileClause? prepared.vocabulary ordinal clause = some rule)
    (executionRule : RewriteRule) (spec : RuleBindingSpec)
    (shape : executionRule.left = rule.left ∧ executionRule.right = rule.right ∧ executionRule.premises = rule.premises)
    (zero : GeneralPremise.checkZeroDependencies spec = true)
    {environment : GeneralPremise.Environment} {index : Nat}
    (provider : environment.provider = (Executable.snapshot prepared known).provider)
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} {target : Pattern}
    (declared : environment.language.rewrites[index]? = some executionRule)
    (specified : GeneralPremise.specification? environment index = some spec)
    (firing : GeneralPremise.RootFiring environment [] (.base "DlStatement") (Executable.request prepared.vocabulary)
      index trace captured completed history target)
    : clause.RangeRestricted ∧
      ClauseReading.PoolsRead prepared.vocabulary (ClauseDictionary.expand prepared.vocabulary (ordinary completed)) ∧
      (∀ atom ∈ clause.positiveAtoms, ∃ premise ∈ facts,
        atom.Matches (FiringReading.sourceAssignment prepared.vocabulary completed) premise) ∧
      (∀ comparison ∈ Comparisons.guards clause,
        Comparisons.Holds Executable.policy (FiringReading.sourceAssignment prepared.vocabulary completed) comparison) := by
  obtain ⟨compiledLeft,_⟩ := FiringReading.compiled_fields prepared.vocabulary ordinal clause rule compiled
  have left := shape.1.trans compiledLeft
  obtain ⟨restricted,native,bodyCompiled,bodyShape⟩ := BodyCompilation.compiled_body prepared.vocabulary ordinal clause rule compiled
  cases firing with
  | @fire _ _ _ _ _ actualRule actualSpec _ _ _ _ actualDeclared actualSpecified _ _ matching capturedTyped premises _ _ =>
    have sameRule : actualRule = executionRule := Option.some.inj (actualDeclared.symm.trans declared)
    subst actualRule
    have sameSpec : actualSpec = spec := Option.some.inj (actualSpecified.symm.trans specified)
    subst actualSpec
    have roots := (premises.typed capturedTyped).rootValues zero
    have requestMatch : Matches executionRule spec 0 .left [] 0 []
        (.apply "InferSnapshot" [Join.poolPattern (Join.relationSlots prepared.vocabulary),Join.poolPattern (Join.literalSlots prepared.vocabulary)])
        (Executable.request prepared.vocabulary) captured := by
      simpa only [left,List.length_nil] using matching.matching
    have poolsRead := RequestReading.request_pools prepared.vocabulary requestMatch premises.extension roots
    rw [shape.2.2,bodyShape] at premises
    have used : ∀ entry ∈ (Join.orderedBody clause).zipIdx, ∀ comparison,
        entry.1 = .comparison comparison → comparison.operator ∈ Executable.operators prepared.source := by
      intro entry member comparison same
      have atBody := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp member)
      rw [same] at atBody
      rw [(Executable.prepare_typed program seeds prepared accepted).1]
      exact guard_used program ordinal clause source comparison ((BodyCompilation.ordered_guard clause comparison).mp atBody)
    have allHeld := PremiseReading.all_sound program seeds prepared accepted known facts represented provider
      (Join.orderedBody clause).zipIdx native bodyCompiled used premises (GeneralScopedMatch.Extends.refl _) roots poolsRead
    refine ⟨restricted,poolsRead,?_,?_⟩
    · intro atom member
      have inBody := (BodyCompilation.ordered_atom clause atom).mpr member
      obtain ⟨position,atBody⟩ := List.mem_iff_getElem?.mp inBody
      exact allHeld (.atom atom,position) (List.mk_mem_zipIdx_iff_getElem?.mpr atBody)
    · intro comparison member
      have inBody := (BodyCompilation.ordered_guard clause comparison).mpr member
      obtain ⟨position,atBody⟩ := List.mem_iff_getElem?.mp inBody
      exact allHeld (.comparison comparison,position) (List.mk_mem_zipIdx_iff_getElem?.mpr atBody)

theorem root_clause_readout (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern) (facts : List GroundFact)
    (represented : ∀ value ∈ known, ∃ fact ∈ facts, Executable.decodeFact? prepared value = some fact)
    (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (source : ProgramGrounding.ClauseAt program ordinal clause)
    (compiled : Query.compileClause? prepared.vocabulary ordinal clause = some rule)
    (executionRule : RewriteRule) (spec : RuleBindingSpec)
    (shape : executionRule.left = rule.left ∧ executionRule.right = rule.right ∧ executionRule.premises = rule.premises)
    (zero : GeneralPremise.checkZeroDependencies spec = true)
    {environment : GeneralPremise.Environment} {index : Nat}
    (provider : environment.provider = (Executable.snapshot prepared known).provider)
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} {target : Pattern}
    (declared : environment.language.rewrites[index]? = some executionRule)
    (specified : GeneralPremise.specification? environment index = some spec)
    (firing : GeneralPremise.RootFiring environment [] (.base "DlStatement") (Executable.request prepared.vocabulary)
      index trace captured completed history target)
    (fact : GroundFact) (decoded : Executable.decodeFact? prepared target = some fact) :
    clause.RangeRestricted ∧ clause.head.Matches (FiringReading.sourceAssignment prepared.vocabulary completed) fact ∧
      (∀ atom ∈ clause.positiveAtoms, ∃ premise ∈ facts,
        atom.Matches (FiringReading.sourceAssignment prepared.vocabulary completed) premise) ∧
      (∀ comparison ∈ Comparisons.guards clause,
        Comparisons.Holds Executable.policy (FiringReading.sourceAssignment prepared.vocabulary completed) comparison) := by
  obtain ⟨restricted,_,body,guards⟩ := root_body_readout program seeds prepared accepted known facts represented
    ordinal clause rule source compiled executionRule spec shape zero provider declared specified firing
  obtain ⟨compiledLeft,compiledRight⟩ := FiringReading.compiled_fields prepared.vocabulary ordinal clause rule compiled
  have right : Join.atom? prepared.vocabulary clause.body.length clause.head = some executionRule.right := by
    rw [shape.2.1]
    exact compiledRight
  have head := FiringReading.root_conclusion_readout prepared.vocabulary clause executionRule spec
    (shape.1.trans compiledLeft) right zero declared specified firing fact decoded
  exact ⟨restricted,head,body,guards⟩

theorem root_clause_sound (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern) (facts : List GroundFact)
    (represented : ∀ value ∈ known, ∃ fact ∈ facts, Executable.decodeFact? prepared value = some fact)
    (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (source : ProgramGrounding.ClauseAt program ordinal clause)
    (compiled : Query.compileClause? prepared.vocabulary ordinal clause = some rule)
    {environment : GeneralPremise.Environment} {index : Nat}
    (provider : environment.provider = (Executable.snapshot prepared known).provider)
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} {target : Pattern}
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index = some (GeneralRuleBindingInference.inferredSpec rule))
    (firing : GeneralPremise.RootFiring environment [] (.base "DlStatement") (Executable.request prepared.vocabulary)
      index trace captured completed history target)
    (fact : GroundFact) (decoded : Executable.decodeFact? prepared target = some fact) :
    clause.RangeRestricted ∧ clause.head.Matches (FiringReading.sourceAssignment prepared.vocabulary completed) fact ∧
      (∀ atom ∈ clause.positiveAtoms, ∃ premise ∈ facts,
        atom.Matches (FiringReading.sourceAssignment prepared.vocabulary completed) premise) ∧
      (∀ comparison ∈ Comparisons.guards clause,
        Comparisons.Holds Executable.policy (FiringReading.sourceAssignment prepared.vocabulary completed) comparison) := by
  exact root_clause_readout program seeds prepared accepted known facts represented ordinal clause rule source compiled
    rule (GeneralRuleBindingInference.inferredSpec rule) ⟨rfl,rfl,rfl⟩ (inferred_zero rule)
    provider declared specified firing fact decoded

theorem root_fact_derives (program : Program) (seeds input : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program input = .ok prepared) (known : List Pattern) (facts : List GroundFact)
    (represented : ∀ value ∈ known, ∃ fact ∈ facts, Executable.decodeFact? prepared value = some fact)
    (derived : ∀ fact ∈ facts, Closure.Derives Executable.policy program seeds fact)
    (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (source : ProgramGrounding.ClauseAt program ordinal clause)
    (compiled : Query.compileClause? prepared.vocabulary ordinal clause = some rule)
    {environment : GeneralPremise.Environment} {index : Nat}
    (provider : environment.provider = (Executable.snapshot prepared known).provider)
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} {target : Pattern}
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index = some (GeneralRuleBindingInference.inferredSpec rule))
    (firing : GeneralPremise.RootFiring environment [] (.base "DlStatement") (Executable.request prepared.vocabulary)
      index trace captured completed history target)
    (fact : GroundFact) (decoded : Executable.decodeFact? prepared target = some fact) :
    Closure.Derives Executable.policy program seeds fact := by
  obtain ⟨restricted,head,body,guards⟩ := root_clause_sound program input prepared accepted known facts represented
    ordinal clause rule source compiled provider declared specified firing fact decoded
  exact Closure.Derives.of_clause Executable.policy program seeds facts ordinal clause source restricted
    (FiringReading.sourceAssignment prepared.vocabulary completed) fact head body guards derived

#print axioms root_body_readout
#print axioms root_clause_readout
#print axioms root_clause_sound
#print axioms root_fact_derives

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClauseSoundness
