import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClauseSoundness

/-! Source range restriction and actual positive query matches make every
compiled conclusion decodable. Head well-formedness is derived from the body,
not assumed of the result. The resulting source witness observes facts. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.RootTotality

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralScopedMatch Match
open GeneralFirstOrderProjection

theorem source_authorized (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
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
      index trace captured completed history target) :
    ∃ row : GroundInstances.Instance, Executable.decodeFact? prepared target = some row.conclusion ∧
      ProgramGrounding.SourceAuthorized Executable.policy program facts row := by
  obtain ⟨restricted,poolsRead,body,guards⟩ := ClauseSoundness.root_body_readout program seeds prepared accepted known facts represented
    ordinal clause rule source compiled executionRule spec shape zero provider declared specified firing
  obtain ⟨fact,head⟩ := Clause.head_has_matching_fact clause restricted
    (FiringReading.sourceAssignment prepared.vocabulary completed) facts body
  obtain ⟨_,rightCompiled⟩ := FiringReading.compiled_fields prepared.vocabulary ordinal clause rule compiled
  have right : Join.atom? prepared.vocabulary clause.body.length clause.head = some executionRule.right := by
    rw [shape.2.1]
    exact rightCompiled
  have decoded := ClauseReading.atom_decoding_complete prepared.vocabulary _ poolsRead clause.body.length clause.head
    executionRule.right right (fun argument member => restricted.1 argument (List.mem_append_left _ member)) fact head
  rw [ClauseDictionary.atom_expands prepared.vocabulary (ordinary completed) clause.body.length clause.head executionRule.right right] at decoded
  have targetRead := FiringReading.root_target_readout executionRule spec
    (ClauseDictionary.atom_binderFree prepared.vocabulary clause.body.length clause.head executionRule.right right) zero declared specified firing
  rw [targetRead] at decoded
  obtain ⟨row,same,authorized⟩ := clause_instance Executable.policy program facts ordinal clause source restricted
    (FiringReading.sourceAssignment prepared.vocabulary completed) fact head body guards
  exact ⟨row,by simpa only [same,Executable.decodeFact?] using decoded,authorized⟩

#print axioms source_authorized

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.RootTotality
