import Mettapedia.Languages.MeTTa.MeTTaZeroLanguageAdequacy
import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment

/-!
# PeTTa interprets and extends the query-first MeTTa Zero kernel

PeTTa's existing atomspace semantics supplies an exact occurrence-bag model of
the query-first kernel:

* the reflective medium is `PeTTaSpace.storedAtoms`;
* public query is the multiset quotient of `PeTTaSpace.spaceMatch`;
* the matcher is the existing `matchPattern`;
* the grounding portal remains a parameter, because PeTTa grounding is a
  larger library boundary than the pure space semantics in this module.

The query correspondence is exact modulo enumeration order.  For evaluation we
prove the direction justified by the current PeTTa specification: every
premise-free `PeTTaEval.ruleApp` result is produced by the Zero evaluator after
the corresponding equation atom has been obtained through public query.
PeTTa adds `superpose`, `collapse`, effects, typing, and further evaluation
cases, so no converse for the whole dialect is asserted.

The existing MORK/MM2 theorem then receives the same arbitrary-atom query
fragment.  Its workspace is set-valued, so that bridge preserves query
support, not occurrence multiplicity.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.MeTTaZeroExtension

open Mettapedia.GSLT
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-! ## Exact PeTTa model -/

/-- PeTTa's real stored-atom list and matcher instantiate the kernel. -/
def model (groundApply : Pattern → Multiset Pattern := fun _ => 0) :
    MeTTaZero.Model where
  Space := PeTTaSpace
  contents := fun space => space.storedAtoms
  matchAtoms := fun pattern atom => matchPattern pattern atom
  groundApply := groundApply

theorem model_lawful (groundApply : Pattern → Multiset Pattern) :
    MeTTaZero.Lawful (model groundApply) := by
  constructor
  intro name atom
  simp [model, matchPattern]

/-- **Exact occurrence-bag query interpretation.**  The only quotient forgets
PeTTa's enumeration order; it preserves every occurrence and uses the same
matcher. -/
@[simp] theorem query_eq_spaceMatch (groundApply : Pattern → Multiset Pattern)
    (space : PeTTaSpace) (pattern template : Pattern) :
    MeTTaZero.query (model groundApply) space pattern template =
      (space.spaceMatch pattern template : Multiset Pattern) := by
  simp [MeTTaZero.query, model, PeTTaSpace.spaceMatch]

/-- Enumerating the public query recovers exactly PeTTa's reflective medium,
including ordinary facts and premise-free equations. -/
@[simp] theorem queryAll_eq_storedAtoms
    (groundApply : Pattern → Multiset Pattern) (space : PeTTaSpace) :
    MeTTaZero.queryAll (model groundApply) space =
      (space.storedAtoms : Multiset Pattern) :=
  MeTTaZero.queryAll_eq_contents _ (model_lawful groundApply) space

/-- PeTTa's declarative `match &self` case computes a list whose occurrence
bag is exactly the Zero query result. -/
theorem petta_spaceQuery_realizes_zero_query
    (groundApply : Pattern → Multiset Pattern) (space : PeTTaSpace)
    (pattern template : Pattern) :
    PeTTaEval space
      (.apply "match" [.apply "&self" [], pattern, template])
      (space.spaceMatch pattern template) ∧
        (space.spaceMatch pattern template : Multiset Pattern) =
          MeTTaZero.query (model groundApply) space pattern template := by
  exact ⟨petta_eval_spaceQuery_correct space pattern template,
    (query_eq_spaceMatch groundApply space pattern template).symm⟩

/-! ## PeTTa query as a certified realization

The theorem above is packaged here in the generic realization class.  The
request indexes both the executable artifact and its observation, so the
artifact carries an actual `PeTTaEval` derivation rather than merely the list
that PeTTa happens to compute. -/

/-- One public query request interpreted by PeTTa. -/
structure QueryRequest where
  space : PeTTaSpace
  /-- The authored term naming this concrete space for relation dispatch. -/
  spaceTerm : Pattern
  pattern : Pattern
  template : Pattern

/-- The executable PeTTa result together with its declarative evaluation
witness. -/
structure QueryArtifact (request : QueryRequest) where
  results : List Pattern
  evaluated : PeTTaEval request.space
    (.apply "match" [.apply "&self" [], request.pattern, request.template])
    results

/-- **PeTTa is a certified realization of Zero's public query operation.**
The named observation forgets only answer enumeration order; coercion to a
multiset retains every occurrence. -/
def queryRealization (groundApply : Pattern → Multiset Pattern := fun _ => 0) :
    Realization (fun _ : QueryRequest => Unit) QueryArtifact
      (fun _ => Multiset Pattern) where
  compile := fun request _ =>
    { results := request.space.spaceMatch request.pattern request.template
      evaluated := petta_eval_spaceQuery_correct request.space
        request.pattern request.template }
  observeSource := fun request _ =>
    MeTTaZero.query (model groundApply) request.space
      request.pattern request.template
  observeArtifact := fun _ artifact => artifact.results
  adequate := by
    intro request _
    exact (query_eq_spaceMatch groundApply request.space
      request.pattern request.template).symm

@[simp] theorem queryRealization_observation
    (groundApply : Pattern → Multiset Pattern) (request : QueryRequest) :
    (queryRealization groundApply).observeArtifact request
        ((queryRealization groundApply).compile request ()) =
      MeTTaZero.query (model groundApply) request.space
        request.pattern request.template :=
  (queryRealization groundApply).observe_compile request ()

/-- In particular, PeTTa realizes the complete occurrence count, not merely
the support of the Zero query. -/
theorem queryRealization_preserves_count
    (groundApply : Pattern → Multiset Pattern) (request : QueryRequest)
    (answer : Pattern) :
    Multiset.count answer
        ((queryRealization groundApply).observeArtifact request
          ((queryRealization groundApply).compile request ())) =
      Multiset.count answer
        (MeTTaZero.query (model groundApply) request.space
          request.pattern request.template) := by
  rw [queryRealization_observation]

/-! ## Certified backend choice -/

/-- Remove the public query-result constructor emitted by the authored
five-field executor.  The fallback branch makes this an observation on every
artifact, while the adequacy theorem below uses only constructor-shaped
artifacts produced by that executor. -/
def unwrapQueryAnswer : Pattern → Pattern
  | .apply "zero-query-answer" [answer] => answer
  | artifact => artifact

@[simp] theorem unwrapQueryAnswer_queryAnswerPattern (answer : Pattern) :
    unwrapQueryAnswer (queryAnswerPattern answer) = answer :=
  rfl

/-- The generic premise-aware interpreter over Zero's five-field root,
restricted to PeTTa query requests. -/
noncomputable def authoredQueryRealization
    (groundApply : Pattern → Multiset Pattern := fun _ => 0) :
    Realization (fun _ : QueryRequest => Unit)
      (fun _ => Multiset Pattern) (fun _ => Multiset Pattern) where
  compile := fun request _ =>
    (MeTTaZeroLanguageAdequacy.authoredRealization (model groundApply)).compile ()
      (.query request.space request.spaceTerm request.pattern request.template)
  observeSource := fun request _ =>
    MeTTaZero.query (model groundApply) request.space
      request.pattern request.template
  observeArtifact := fun _ answers => answers.map unwrapQueryAnswer
  adequate := by
    intro request _
    rw [MeTTaZeroLanguageAdequacy.authoredRealization_query,
      Multiset.map_map]
    simp

/-- Select the generic authored executor or PeTTa's native query evaluator per
request.  The selector is deliberately unconstrained: correctness follows
from the two realization certificates, not from the plan heuristic. -/
noncomputable def hybridQueryRealization
    (groundApply : Pattern → Multiset Pattern := fun _ => 0)
    (useAuthoredExecutor : QueryRequest → Bool) :
    Realization (fun _ : QueryRequest => Unit)
      (fun request => Multiset Pattern ⊕ QueryArtifact request)
      (fun _ => Multiset Pattern) :=
  (authoredQueryRealization groundApply).select
    (queryRealization groundApply)
    (by intro request _; rfl)
    (fun request _ => useAuthoredExecutor request)

theorem hybridQueryRealization_observation
    (groundApply : Pattern → Multiset Pattern)
    (useAuthoredExecutor : QueryRequest → Bool) (request : QueryRequest) :
    (hybridQueryRealization groundApply useAuthoredExecutor).observeArtifact
        request
        ((hybridQueryRealization groundApply useAuthoredExecutor).compile
          request ()) =
      MeTTaZero.query (model groundApply) request.space
        request.pattern request.template :=
  (hybridQueryRealization groundApply useAuthoredExecutor).observe_compile
    request ()

/-- Positive selection canary: a true plan selects the generic authored
executor artifact. -/
theorem hybridQueryRealization_selects_authored
    (groundApply : Pattern → Multiset Pattern)
    (useAuthoredExecutor : QueryRequest → Bool) (request : QueryRequest)
    (selected : useAuthoredExecutor request = true) :
    (hybridQueryRealization groundApply useAuthoredExecutor).compile request () =
      .inl ((authoredQueryRealization groundApply).compile request ()) := by
  exact Realization.select_compile_left
    (authoredQueryRealization groundApply) (queryRealization groundApply)
    (by intro indexed _; rfl) (fun indexed _ => useAuthoredExecutor indexed)
    request () selected

/-- Symmetric selection canary for PeTTa's native artifact, which retains its
declarative `PeTTaEval` witness. -/
theorem hybridQueryRealization_selects_petta
    (groundApply : Pattern → Multiset Pattern)
    (useAuthoredExecutor : QueryRequest → Bool) (request : QueryRequest)
    (selected : useAuthoredExecutor request = false) :
    (hybridQueryRealization groundApply useAuthoredExecutor).compile request () =
      .inr ((queryRealization groundApply).compile request ()) := by
  exact Realization.select_compile_right
    (authoredQueryRealization groundApply) (queryRealization groundApply)
    (by intro indexed _; rfl) (fun indexed _ => useAuthoredExecutor indexed)
    request () selected

/-- Every occurrence returned by PeTTa's query is exactly one rewrite of the
Zero query GSLT. -/
theorem petta_query_member_iff_zero_step
    (groundApply : Pattern → Multiset Pattern) (space : PeTTaSpace)
    (pattern template result : Pattern) :
    result ∈ (space.spaceMatch pattern template : Multiset Pattern) ↔
      ∃ occurrence,
        (MeTTaZero.queryGSLT (model groundApply)).Step
          (.request space pattern template)
          (.answer space pattern template occurrence result) := by
  rw [← query_eq_spaceMatch]
  exact MeTTaZero.mem_query_iff_exists_step _ _ _ _ _

/-! ## PeTTa rule application is derived from reflective query -/

/-- A premise-free PeTTa rule is publicly visible as an equation atom. -/
theorem rule_atom_mem_queryAll
    (groundApply : Pattern → Multiset Pattern) {space : PeTTaSpace}
    {rule : RewriteRule} (ruleMember : rule ∈ space.rules)
    (premiseFree : rule.premises = []) :
    .apply "=" [rule.left, rule.right] ∈
      MeTTaZero.queryAll (model groundApply) space := by
  rw [queryAll_eq_storedAtoms]
  exact PeTTaSpace.mem_storedAtoms_of_premiseFreeRule ruleMember premiseFree

/-- The result of every premise-free PeTTa rule application occurs in the
query-derived equation results.  This is the load-bearing fact: evaluation
does not consult a hidden rule table. -/
theorem ruleApplication_mem_equationResults
    (groundApply : Pattern → Multiset Pattern) {space : PeTTaSpace}
    {rule : RewriteRule} {bindings : Bindings} {subject result : Pattern}
    (ruleMember : rule ∈ space.rules)
    (premiseFree : rule.premises = [])
    (matchMember : bindings ∈ matchPattern rule.left subject)
    (instantiates : applyBindings bindings rule.right = result) :
    result ∈
      MeTTaZero.equationResults (model groundApply) space subject := by
  rw [MeTTaZero.mem_equationResults_iff]
  exact
    ⟨.apply "=" [rule.left, rule.right],
      rule_atom_mem_queryAll groundApply ruleMember premiseFree,
      rule.left, rule.right, rfl,
      bindings, matchMember, instantiates⟩

/-- Every PeTTa rule-application result is therefore an answer of the complete
Zero one-step evaluator (with the same optional grounding portal). -/
theorem ruleApplication_mem_evaluateOne
    (groundApply : Pattern → Multiset Pattern) {space : PeTTaSpace}
    {rule : RewriteRule} {bindings : Bindings} {subject result : Pattern}
    (ruleMember : rule ∈ space.rules)
    (premiseFree : rule.premises = [])
    (matchMember : bindings ∈ matchPattern rule.left subject)
    (instantiates : applyBindings bindings rule.right = result) :
    result ∈ MeTTaZero.evaluateOne (model groundApply) space subject := by
  have equationMember := ruleApplication_mem_equationResults groundApply
    ruleMember premiseFree matchMember instantiates
  have interpretedMember :
      result ∈ MeTTaZero.interpretedResults (model groundApply) space subject :=
    Multiset.mem_add.mpr (Or.inl equationMember)
  have interpretedNonempty :
      MeTTaZero.interpretedResults (model groundApply) space subject ≠ 0 :=
    by
      intro empty
      simp [empty] at interpretedMember
  rw [MeTTaZero.evaluateOne_of_interpreted _ _ _ interpretedNonempty]
  exact interpretedMember

/-- The same result is an actual rewrite occurrence in the composed Zero
evaluation GSLT. -/
theorem ruleApplication_has_zero_evaluation_step
    (groundApply : Pattern → Multiset Pattern) {space : PeTTaSpace}
    {rule : RewriteRule} {bindings : Bindings} {subject result : Pattern}
    (ruleMember : rule ∈ space.rules)
    (premiseFree : rule.premises = [])
    (matchMember : bindings ∈ matchPattern rule.left subject)
    (instantiates : applyBindings bindings rule.right = result) :
    ∃ occurrence,
      (MeTTaZero.evaluationGSLT (model groundApply)).Step
        (.request space subject) (.answer space subject occurrence result) := by
  exact (MeTTaZero.mem_evaluateOne_iff_exists_step _ _ _ _).1
    (ruleApplication_mem_evaluateOne groundApply ruleMember premiseFree
      matchMember instantiates)

/-- Bundled bridge from the actual PeTTa `ruleApp` constructor to the Zero
evaluation GSLT. -/
theorem petta_ruleApp_has_zero_step
    (groundApply : Pattern → Multiset Pattern) {space : PeTTaSpace}
    {rule : RewriteRule} {bindings : Bindings} {subject result : Pattern}
    (ruleMember : rule ∈ space.rules)
    (premiseFree : rule.premises = [])
    (matchMember : bindings ∈ matchPattern rule.left subject)
    (instantiates : applyBindings bindings rule.right = result) :
    PeTTaEval space subject [result] ∧
      ∃ occurrence,
        (MeTTaZero.evaluationGSLT (model groundApply)).Step
          (.request space subject) (.answer space subject occurrence result) := by
  exact
    ⟨PeTTaEval.ruleApp rule bindings subject result ruleMember premiseFree
        matchMember instantiates,
      ruleApplication_has_zero_evaluation_step groundApply ruleMember premiseFree
        matchMember instantiates⟩

/-! ## Reflection changes what is observable -/

/-- An ordinary fact remains observable through the same query used by
evaluation. -/
theorem fact_mem_public_query
    (groundApply : Pattern → Multiset Pattern) {space : PeTTaSpace}
    {fact : Pattern} (factMember : fact ∈ space.facts) :
    fact ∈ MeTTaZero.queryAll (model groundApply) space := by
  rw [queryAll_eq_storedAtoms]
  exact PeTTaSpace.mem_storedAtoms_of_fact factMember

/-- Positive reflection canary: a stored rule can be returned as data, not
merely fired privately. -/
theorem rule_mem_public_query
    (groundApply : Pattern → Multiset Pattern) {space : PeTTaSpace}
    {rule : RewriteRule} (ruleMember : rule ∈ space.rules)
    (premiseFree : rule.premises = []) :
    .apply "=" [rule.left, rule.right] ∈
      MeTTaZero.queryAll (model groundApply) space :=
  rule_atom_mem_queryAll groundApply ruleMember premiseFree

/-! ## The existing support-valued MM2 seam -/

/-- The already-proved PeTTa core-fragment theorem sends every arbitrary-atom
query witness into the MORK/MM2 source-query interface.  This corollary makes
the route from the Zero public query explicit while retaining its honest
scope: single-variable matching and support membership. -/
theorem zero_any_atom_query_to_mm2_support
    {space : PeTTaSpace} {name : String} {template atom result : Pattern}
    (atomMember : atom ∈ MeTTaZero.queryAll (model fun _ => 0) space)
    (templateTranslatable :
      Mettapedia.Languages.ProcessCalculi.MORK.morkTranslatable template = true)
    (instantiates : applyBindings [(name, atom)] template = result)
    {workspace :
      Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable.CSpace}
    (workspaceMember :
      Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom atom ∈ workspace) :
    let source :=
      Mettapedia.Languages.MeTTa.RuntimeExec.morkRuntimeQueryExec0.baseSourceFactor
        (.fvar name)
    ∃ substitution translated,
      (substitution, translated) ∈
          Mettapedia.Languages.MeTTa.RuntimeExec.morkRuntimeQueryExec0.computableSourceFactorMatch
            [] workspace source ∧
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst substitution
            (Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom template) =
          Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom result := by
  have storedMember : atom ∈ space.storedAtoms := by
    simpa using atomMember
  exact
    Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment.anyFactMatch_toComputableSourceQuery
      storedMember templateTranslatable instantiates workspaceMember

end Mettapedia.Languages.MeTTa.PeTTa.MeTTaZeroExtension
