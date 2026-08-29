import Mettapedia.GSLT.LanguageDef.CertificateGSLTWireFormat

/-!
# Article identity: local rule agreement and rootedness

Two properties of chronological articles that the acceptance theorems of
`CertificateGSLTWireFormat` do not by themselves settle, both raised by external
review of that module.

**Local rule agreement.**  `checkWireArticle_true_of_ruleLookupRefines`
transports an article along *whole-table* rule retention.  That is far more
than an article needs and far more than a large library can offer: an
article cites a handful of rules out of a table that may hold tens of
thousands.  `checkWireArticle_iff_articleRuleAgreement` replaces it with the
exact hypothesis — agreement on the cited identifiers only — and gets a
biconditional instead of an implication.  This is what makes
content-addressed article reuse across large, independently growing
definitions possible.

**Rootedness.**  The version-1 checker validates every node and then requires
only that the root carry the target; it never requires nodes to be reachable
from the root.  Acceptance is therefore not affected by unreachable nodes.
This is not unsoundness — the root still reconstructs an exact derivation —
but it means the submitted-node count and any content hash of an article are
not functions of the proof, which the compact-cost ledger depends on.  The
reachability predicate, its executable check, and the strengthened checker
are given here, with soundness inherited unchanged.  The remaining
obligation before rootedness can be *required* by the ABI is stated
explicitly at the end of this file: that linearised articles are always
rooted, which is what would keep the completeness half of
`wireArticle_correspondence` intact.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-! ## Local rule agreement -/

/-- The rule identifiers an article actually cites. -/
def WireArticle.citedRuleIds (article : WireArticle) : List RuleId :=
  article.nodes.map fun node => node.ruleInstance.ruleId

/-- Two definitions agree on everything this article cites. -/
def ArticleRuleAgreement (source target : ValidatedCalculusLanguageDef)
    (article : WireArticle) : Prop :=
  ∀ id ∈ article.citedRuleIds,
    source.1.lookupRule? id = target.1.lookupRule? id

/-- Instantiation depends on the definition only through the looked-up
schema. -/
theorem instantiateRule?_congr {source target : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance}
    (agree : source.1.lookupRule? ruleInstance.ruleId =
      target.1.lookupRule? ruleInstance.ruleId) :
    instantiateRule? source ruleInstance = instantiateRule? target
      ruleInstance := by
  simp only [instantiateRule?, agree]

/-- Checking one node depends only on the schema its instance names. -/
theorem checkOpenDAGNode?_congr {source target : ValidatedCalculusLanguageDef}
    {context : List Pattern} {entries : List OpenDAGEntry}
    {node : OpenDAGNode}
    (agree : source.1.lookupRule? node.ruleInstance.ruleId =
      target.1.lookupRule? node.ruleInstance.ruleId) :
    checkOpenDAGNode? source context entries node =
      checkOpenDAGNode? target context entries node := by
  unfold checkOpenDAGNode?
  rw [instantiateRule?_congr agree]

theorem checkOpenDAGNodes?_congr {source target : ValidatedCalculusLanguageDef}
    {context : List Pattern} :
    ∀ (nodes : List OpenDAGNode) (entries : List OpenDAGEntry),
      (∀ node ∈ nodes, source.1.lookupRule? node.ruleInstance.ruleId =
        target.1.lookupRule? node.ruleInstance.ruleId) →
      checkOpenDAGNodes? source context entries nodes =
        checkOpenDAGNodes? target context entries nodes := by
  intro nodes
  induction nodes with
  | nil => intro entries _; rfl
  | cons node rest inductionHypothesis =>
      intro entries agree
      simp only [checkOpenDAGNodes?]
      rw [checkOpenDAGNode?_congr (agree node (List.mem_cons_self ..))]
      cases headCheck : checkOpenDAGNode? target context entries node with
      | none => rfl
      | some middle =>
          exact inductionHypothesis middle
            (fun n member => agree n (List.mem_cons_of_mem _ member))

theorem checkOpenDAGBlocks?_congr {source target : ValidatedCalculusLanguageDef}
    {context : List Pattern} :
    ∀ (blocks : List (List OpenDAGNode)) (entries : List OpenDAGEntry),
      (∀ block ∈ blocks, ∀ node ∈ block,
        source.1.lookupRule? node.ruleInstance.ruleId =
          target.1.lookupRule? node.ruleInstance.ruleId) →
      checkOpenDAGBlocks? source context entries blocks =
        checkOpenDAGBlocks? target context entries blocks := by
  intro blocks
  induction blocks with
  | nil => intro entries _; rfl
  | cons block rest inductionHypothesis =>
      intro entries agree
      simp only [checkOpenDAGBlocks?]
      rw [checkOpenDAGNodes?_congr block entries
        (agree block (List.mem_cons_self ..))]
      cases blockCheck : checkOpenDAGNodes? target context entries block with
      | none => rfl
      | some middle =>
          exact inductionHypothesis middle
            (fun b member => agree b (List.mem_cons_of_mem _ member))

/-- **Local rule agreement suffices.**  Two definitions that resolve every
identifier the article cites to the same schema accept exactly the same
article.  Unlike whole-table refinement this is a biconditional, and it is
insensitive to everything the article does not mention — which is what makes
it usable against a large, independently growing library. -/
theorem checkWireArticle_iff_articleRuleAgreement
    {source target : ValidatedCalculusLanguageDef} {article : WireArticle}
    (agree : ArticleRuleAgreement source target article) :
    checkWireArticle source article = true ↔
      checkWireArticle target article = true := by
  have nodesAgree : ∀ block ∈ [article.nodes], ∀ node ∈ block,
      source.1.lookupRule? node.ruleInstance.ruleId =
        target.1.lookupRule? node.ruleInstance.ruleId := by
    intro block blockMember node member
    have blockEq : block = article.nodes := by simpa using blockMember
    subst blockEq
    exact agree node.ruleInstance.ruleId (List.mem_map_of_mem member)
  have blocksEq : checkOpenDAGBlocks source [] article.target article.rootId
      [article.nodes] =
      checkOpenDAGBlocks target [] article.target article.rootId
        [article.nodes] := by
    unfold checkOpenDAGBlocks expandOpenDAGBlocks?
    rw [checkOpenDAGBlocks?_congr [article.nodes] [] nodesAgree]
  simp only [checkWireArticle, blocksEq]

/-- Whole-table retention is the special case in which every identifier
agrees, so the earlier transport theorem factors through this one. -/
theorem articleRuleAgreement_of_lookup_eq
    {source target : ValidatedCalculusLanguageDef} (article : WireArticle)
    (agree : ∀ id, source.1.lookupRule? id = target.1.lookupRule? id) :
    ArticleRuleAgreement source target article :=
  fun id _ => agree id

/-! ## Rootedness -/

/-- The node identifiers a node cites directly.  Premise references are not
node references and are dropped. -/
def OpenDAGNode.citedNodes (node : OpenDAGNode) : List Nat :=
  node.children.filterMap fun reference =>
    match reference with
    | .node id => some id
    | .premise _ => none

/-- Reachability of a node identifier from the article's root, along
citation edges. -/
inductive ReachableNode (nodes : List OpenDAGNode) (rootId : Nat) :
    Nat → Prop where
  | root : ReachableNode nodes rootId rootId
  | cited {node : OpenDAGNode} {id : Nat} (member : node ∈ nodes)
      (fromRoot : ReachableNode nodes rootId node.id)
      (cites : id ∈ node.citedNodes) : ReachableNode nodes rootId id

/-- Reachability only grows when the node list grows. -/
theorem ReachableNode.mono {nodes nodes' : List OpenDAGNode} {rootId id : Nat}
    (subset : ∀ node ∈ nodes, node ∈ nodes')
    (reachable : ReachableNode nodes rootId id) :
    ReachableNode nodes' rootId id := by
  induction reachable with
  | root => exact .root
  | cited member _ cites inductionHypothesis =>
      exact .cited (subset _ member) inductionHypothesis cites

/-- Every node of the article is used by the proof the root denotes. -/
def WireArticle.Rooted (article : WireArticle) : Prop :=
  ∀ node ∈ article.nodes,
    ReachableNode article.nodes article.rootId node.id

/-- Executable rootedness check: mark the root, then sweep the node list
right to left, adding the citations of every marked node.  Chronology — a
node cites only strictly earlier nodes — is what makes a single reverse pass
sufficient. -/
def neededNodes (nodes : List OpenDAGNode) (rootId : Nat) : List Nat :=
  nodes.foldr
    (fun node needed =>
      if needed.contains node.id then needed ++ node.citedNodes else needed)
    [rootId]

def WireArticle.rootedCheck (article : WireArticle) : Bool :=
  article.nodes.all fun node =>
    (neededNodes article.nodes article.rootId).contains node.id

/-- The rooted article checker: version-1 acceptance plus the requirement
that no node rides along unused. -/
def checkRootedArticle (definition : ValidatedCalculusLanguageDef)
    (article : WireArticle) : Bool :=
  checkWireArticle definition article && article.rootedCheck

/-- Rooted acceptance is a strengthening: it still yields a derivation of the
stored target.  Soundness is inherited unchanged, so adopting rootedness
cannot admit anything new. -/
theorem checkRootedArticle_sound {definition : ValidatedCalculusLanguageDef}
    {article : WireArticle}
    (accepted : checkRootedArticle definition article = true) :
    Nonempty (Derivation definition article.target) := by
  simp only [checkRootedArticle, Bool.and_eq_true] at accepted
  exact checkWireArticle_sound accepted.1

/-- Rooted acceptance implies plain acceptance. -/
theorem checkWireArticle_of_checkRootedArticle
    {definition : ValidatedCalculusLanguageDef} {article : WireArticle}
    (accepted : checkRootedArticle definition article = true) :
    checkWireArticle definition article = true := by
  simp only [checkRootedArticle, Bool.and_eq_true] at accepted
  exact accepted.1

/-- Local rule agreement transports rooted acceptance too: rootedness is a
property of the article alone and does not mention the definition. -/
theorem checkRootedArticle_iff_articleRuleAgreement
    {source target : ValidatedCalculusLanguageDef} {article : WireArticle}
    (agree : ArticleRuleAgreement source target article) :
    checkRootedArticle source article = true ↔
      checkRootedArticle target article = true := by
  simp only [checkRootedArticle, Bool.and_eq_true,
    checkWireArticle_iff_articleRuleAgreement agree]

/-! ## The remaining obligation before rootedness can be required

`checkRootedArticle` is sound by inheritance, so adopting it can never admit
anything new.  What is *not* yet proved is that it admits everything the
version-1 checker admits from a real derivation, namely:

    ∀ (derivation : Derivation definition goal),
      (articleOfDerivation derivation).rootedCheck = true

`Derivation.linearize` emits exactly the nodes of the derivation tree and
makes each node cite the roots of its children, so the statement is expected
to hold; the proof is a mutual induction over `Derivation`/`DerivationList`
with the node-list append reasoning that `linearize_checks` already carries.
Until it is proved, `checkWireArticle` remains the ABI and
`checkRootedArticle` is an available strengthening, not a requirement — the
completeness half of `wireArticle_correspondence` is stated for the former
and is not inherited by the latter. -/

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
