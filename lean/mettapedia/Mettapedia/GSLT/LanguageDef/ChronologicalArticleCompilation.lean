import Mettapedia.GSLT.LanguageDef.ExactRuleSelectorCompilation
import Mettapedia.GSLT.LanguageDef.ProofGSLTWireFormat

/-!
# Chronological article compilation

The generic exact selector chooses a rule instance; successful local node
construction extends a chronological environment.  This module packages the
environment invariant so finalization needs only to select the root and check
its target.  It does not replay the accumulated article.

The result is the formal boundary needed by a generated rule machine: every
node is admitted when it is constructed, and the final wire article is
accepted by the ordinary ProofGSLT checker.
-/

namespace Mettapedia.GSLT.LanguageDef.ChronologicalArticleCompilation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.ProofGSLT

universe uKey

variable {Key : Type uKey}

/-- A chronological builder whose native environment is exactly the result of
checking the nodes already emitted against its append-only premise context.
The invariant is established once per node, not by replaying the full list at
finalization. -/
structure Builder (presentation : ValidatedPresentation) where
  context : List Pattern
  nodes : List OpenDAGNode
  entries : List OpenDAGEntry
  checked :
    checkOpenDAGNodes? presentation context [] nodes = some entries

/-- The empty chronological environment. -/
def Builder.empty (presentation : ValidatedPresentation)
    (context : List Pattern := []) :
    Builder presentation where
  context := context
  nodes := []
  entries := []
  checked := rfl

/-- Sequential checking composes over list append. -/
theorem checkOpenDAGNodes?_append
    (presentation : ValidatedPresentation) (context : List Pattern) :
    ∀ (first second : List OpenDAGNode) (entries : List OpenDAGEntry),
      checkOpenDAGNodes? presentation context entries (first ++ second) =
        (checkOpenDAGNodes? presentation context entries first).bind
          (fun middle =>
            checkOpenDAGNodes? presentation context middle second) := by
  intro first
  induction first with
  | nil =>
      intro second entries
      rfl
  | cons node nodes inductionHypothesis =>
      intro second entries
      simp only [List.cons_append, checkOpenDAGNodes?]
      cases checked : checkOpenDAGNode? presentation context entries node with
      | none => simp
      | some middle =>
          exact inductionHypothesis second middle

/-- A successful premise reference remains the same reference when new
premises are appended.  Existing premise coordinates are stable because the
context grows only at its right boundary. -/
theorem resolveOpenDAGReference?_context_append_of_some
    (context suffix : List Pattern) (entries : List OpenDAGEntry)
    (expected : Pattern) (reference : OpenDAGReference)
    (proof : RawOpenProof)
    (resolved :
      resolveOpenDAGReference? context entries expected reference =
        some proof) :
    resolveOpenDAGReference? (context ++ suffix) entries expected reference =
      some proof := by
  cases reference with
  | premise index =>
      simp only [resolveOpenDAGReference?] at resolved ⊢
      cases found : context[index]? with
      | none => simp [found] at resolved
      | some actual =>
          have inBounds : index < context.length :=
            (List.getElem?_eq_some_iff.mp found).choose
          rw [List.getElem?_append_left inBounds]
          exact resolved
  | node id =>
      exact resolved

/-- Ordered child resolution is stable under append-only premise extension. -/
theorem resolveOpenDAGChildren?_context_append_of_some
    (context suffix : List Pattern) (entries : List OpenDAGEntry) :
    ∀ (premises : List Pattern) (references : List OpenDAGReference)
      (proofs : List RawOpenProof),
      resolveOpenDAGChildren? context entries premises references =
          some proofs →
        resolveOpenDAGChildren? (context ++ suffix) entries
            premises references = some proofs := by
  intro premises
  induction premises with
  | nil =>
      intro references proofs resolved
      cases references <;> simp_all [resolveOpenDAGChildren?]
  | cons premise premises inductionHypothesis =>
      intro references proofs resolved
      cases references with
      | nil => simp [resolveOpenDAGChildren?] at resolved
      | cons reference references =>
          simp only [resolveOpenDAGChildren?] at resolved ⊢
          cases headResolved :
              resolveOpenDAGReference? context entries premise reference with
          | none => simp [headResolved] at resolved
          | some proof =>
              cases tailResolved :
                  resolveOpenDAGChildren? context entries premises references with
              | none => simp [headResolved, tailResolved] at resolved
              | some tailProofs =>
                  simp [headResolved, tailResolved] at resolved
                  cases resolved
                  rw [resolveOpenDAGReference?_context_append_of_some
                    context suffix entries premise reference proof headResolved]
                  rw [inductionHypothesis references tailProofs tailResolved]
                  rfl

/-- One accepted chronological node remains accepted after appending premises.
The returned entry environment is byte-for-byte the same logical value. -/
theorem checkOpenDAGNode?_context_append_of_some
    (presentation : ValidatedPresentation)
    (context suffix : List Pattern) (entries next : List OpenDAGEntry)
    (node : OpenDAGNode)
    (checked : checkOpenDAGNode? presentation context entries node =
      some next) :
    checkOpenDAGNode? presentation (context ++ suffix) entries node =
      some next := by
  unfold checkOpenDAGNode? at checked ⊢
  cases duplicate : findOpenDAGEntry? entries node.id with
  | some entry => simp [duplicate] at checked
  | none =>
      simp only [duplicate] at checked ⊢
      cases instantiated :
          instantiateRule? presentation node.ruleInstance with
      | none => simp [instantiated] at checked
      | some result =>
          rcases result with ⟨premises, conclusion⟩
          simp only [instantiated] at checked ⊢
          cases childrenChecked :
              resolveOpenDAGChildren? context entries premises node.children with
          | none => simp [childrenChecked] at checked
          | some children =>
              simp [childrenChecked] at checked
              cases checked
              rw [resolveOpenDAGChildren?_context_append_of_some
                context suffix entries premises node.children children
                childrenChecked]

/-- A completely checked chronological prefix remains checked after an
append-only premise extension. -/
theorem checkOpenDAGNodes?_context_append_of_some
    (presentation : ValidatedPresentation) (context suffix : List Pattern) :
    ∀ (entries : List OpenDAGEntry) (nodes : List OpenDAGNode)
      (next : List OpenDAGEntry),
      checkOpenDAGNodes? presentation context entries nodes = some next →
        checkOpenDAGNodes? presentation (context ++ suffix) entries nodes =
          some next := by
  intro entries nodes
  induction nodes generalizing entries with
  | nil =>
      intro next checked
      simpa [checkOpenDAGNodes?] using checked
  | cons node nodes inductionHypothesis =>
      intro next checked
      simp only [checkOpenDAGNodes?] at checked ⊢
      cases headChecked :
          checkOpenDAGNode? presentation context entries node with
      | none => simp [headChecked] at checked
      | some middle =>
          simp only [headChecked] at checked
          rw [checkOpenDAGNode?_context_append_of_some
            presentation context suffix entries middle node headChecked]
          exact inductionHypothesis middle next checked

/-- Append one new premise while retaining every previously checked node.
No node is replayed; the proof is the append-only context-stability theorem. -/
def Builder.appendPremise {presentation : ValidatedPresentation}
    (builder : Builder presentation) (premise : Pattern) :
    Builder presentation where
  context := builder.context ++ [premise]
  nodes := builder.nodes
  entries := builder.entries
  checked := checkOpenDAGNodes?_context_append_of_some
    presentation builder.context [premise] [] builder.nodes builder.entries
    builder.checked

/-- Append one locally accepted node.  Failure is transactional: no builder is
returned unless the extended chronological invariant can be constructed. -/
def Builder.append? {presentation : ValidatedPresentation}
    (builder : Builder presentation) (node : OpenDAGNode) :
    Option (Builder presentation) :=
  match checkedNode :
      checkOpenDAGNode? presentation builder.context builder.entries node with
  | none => none
  | some next =>
      some
        { context := builder.context
          nodes := builder.nodes ++ [node]
          entries := next
          checked := by
            rw [checkOpenDAGNodes?_append]
            simp [builder.checked, checkedNode, checkOpenDAGNodes?] }

/-- One exact-selector action that emits a ProofGSLT node. -/
def selectedNode? [DecidableEq Key]
    (index : ExactRuleSelectorCompilation.ExactIndex Key RuleInstance)
    (query : Key)
    (id : Nat) (children : List OpenDAGReference) :
    Option OpenDAGNode :=
  match ExactRuleSelectorCompilation.lookup query index with
  | none => none
  | some ruleInstance => some ⟨id, ruleInstance, children⟩

/-- The source relational observation of the same node-producing action. -/
def sourceSelectedNodes [DecidableEq Key]
    (keyOf? : RuleInstance → Option Key) (rules : List RuleInstance)
    (query : Key) (id : Nat) (children : List OpenDAGReference) :
    List OpenDAGNode :=
  (FiniteRuleIndexCompilation.sourceCandidates keyOf? rules query).map
    fun ruleInstance => ⟨id, ruleInstance, children⟩

/-- Exact-selector compilation preserves the complete source bag of
node-producing actions. -/
theorem sourceSelectedNodes_eq_selectedNode?_toList_of_compile?
    [DecidableEq Key]
    (keyOf? : RuleInstance → Option Key) (rules : List RuleInstance)
    (index : ExactRuleSelectorCompilation.ExactIndex Key RuleInstance)
    (accepted :
      ExactRuleSelectorCompilation.compile? keyOf? rules = some index)
    (query : Key) (id : Nat) (children : List OpenDAGReference) :
    sourceSelectedNodes keyOf? rules query id children =
      (selectedNode? index query id children).toList := by
  unfold sourceSelectedNodes selectedNode?
  rw [ExactRuleSelectorCompilation.sourceCandidates_eq_lookup_toList_of_compile?
    keyOf? rules index accepted query]
  cases ExactRuleSelectorCompilation.lookup query index <;> rfl

/-- Select and append one rule action through the same transactional builder.
The selector and chronological-node admission are independent fail-closed
stages. -/
def Builder.appendSelected? {presentation : ValidatedPresentation}
    [DecidableEq Key] (builder : Builder presentation)
    (index : ExactRuleSelectorCompilation.ExactIndex Key RuleInstance)
    (query : Key)
    (id : Nat) (children : List OpenDAGReference) :
    Option (Builder presentation) := do
  let node ← selectedNode? index query id children
  builder.append? node

/-- Finalize a builder only when the requested root exists and has the claimed
target.  No accumulated node is replayed here. -/
def Builder.finish? {presentation : ValidatedPresentation}
    (builder : Builder presentation) (rootId : Nat) (target : Pattern) :
    Option WireArticle :=
  match findOpenDAGEntry? builder.entries rootId with
  | none => none
  | some root =>
      if root.goal = target then
        some
          { version := wireArticleVersion
            nodes := builder.nodes
            rootId := rootId
            target := target }
      else none

/-- Finalization of an incrementally admitted builder produces an open article
accepted against the builder's append-only premise context. -/
theorem Builder.finish?_open_sound {presentation : ValidatedPresentation}
    (builder : Builder presentation) (rootId : Nat) (target : Pattern)
    (article : WireArticle)
    (finished : builder.finish? rootId target = some article) :
    article.version = wireArticleVersion ∧
      checkOpenDAGBlocks presentation builder.context article.target
        article.rootId [article.nodes] = true := by
  simp only [Builder.finish?] at finished
  split at finished
  · contradiction
  · rename_i root found
    split at finished
    · rename_i same
      cases finished
      unfold checkOpenDAGBlocks expandOpenDAGBlocks?
      simp [checkOpenDAGBlocks?, builder.checked, found, same]
    · contradiction

/-- The closed specialization recovers ordinary wire-article acceptance. -/
theorem Builder.finish?_closed_sound
    {presentation : ValidatedPresentation}
    (builder : Builder presentation) (closed : builder.context = [])
    (rootId : Nat) (target : Pattern) (article : WireArticle)
    (finished : builder.finish? rootId target = some article) :
    checkWireArticle presentation article = true := by
  unfold checkWireArticle
  have openAccepted :=
    Builder.finish?_open_sound builder rootId target article finished
  rw [closed] at openAccepted
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using openAccepted

/-! ## Positive and fail-closed witnesses -/

private def sampleRuleInstance : RuleInstance :=
  ⟨⟨"sample-rule"⟩, []⟩

/-- A present exact key produces precisely one chronological node action. -/
example :
    selectedNode? [(3, sampleRuleInstance)] 3 7 [] =
      some ⟨7, sampleRuleInstance, []⟩ := by
  rfl

/-- An empty builder cannot be finalized with a nonexistent root. -/
example (presentation : ValidatedPresentation) :
    (Builder.empty presentation).finish? 0 (.apply "missing" []) = none :=
  rfl

/-- A missing exact selector never mutates the chronological builder. -/
example (presentation : ValidatedPresentation) :
    (Builder.empty presentation).appendSelected?
      (Key := Nat) [] 7 0 [] = none :=
  rfl

/-- Appending a premise exposes exactly its new stable coordinate. -/
example (premise : Pattern) :
    resolveOpenDAGReference? [premise] [] premise (.premise 0) =
      some (.premise 0) := by
  simp [resolveOpenDAGReference?]

/-- A future premise coordinate is rejected before that premise is appended. -/
example (premise : Pattern) :
    resolveOpenDAGReference? [] [] premise (.premise 0) = none :=
  rfl

end Mettapedia.GSLT.LanguageDef.ChronologicalArticleCompilation
