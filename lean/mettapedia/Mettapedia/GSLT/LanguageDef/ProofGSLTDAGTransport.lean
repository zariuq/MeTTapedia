import Mettapedia.GSLT.LanguageDef.ProofGSLTOpenDAG

/-!
# Exact transport of open DAG evidence

Rule-retaining presentation refinement preserves not only the meaning of an
open DAG but the very same chronological artifact.  The proof is executable:
each successful source rule instantiation is the same successful target
instantiation, so node, block, and root computations replay unchanged.

General derivation-valued interpretations deliberately do not satisfy this
theorem.  Compiling a primitive source node to a multi-node target template
requires a separate graph-substitution construction.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

private theorem instantiateRule?_eq_some_of_refines
    {source target : ValidatedPresentation}
    (refines : RuleLookupRefines source target)
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (instantiated :
      instantiateRule? source ruleInstance = some (premises, conclusion)) :
    instantiateRule? target ruleInstance = some (premises, conclusion) :=
  instantiateRule?_eq_some_iff_application.mpr
    ((instantiateRule?_eq_some_iff_application.mp instantiated).transport
      refines)

private theorem checkOpenDAGNode?_eq_some_of_refines
    {source target : ValidatedPresentation}
    (refines : RuleLookupRefines source target)
    {context : List Pattern} {entries next : List OpenDAGEntry}
    {node : OpenDAGNode}
    (checked : checkOpenDAGNode? source context entries node = some next) :
    checkOpenDAGNode? target context entries node = some next := by
  unfold checkOpenDAGNode? at checked ⊢
  cases duplicate : findOpenDAGEntry? entries node.id with
  | some entry => simp [duplicate] at checked
  | none =>
      simp only [duplicate] at checked ⊢
      cases instantiated : instantiateRule? source node.ruleInstance with
      | none => simp [instantiated] at checked
      | some result =>
          rcases result with ⟨premises, conclusion⟩
          simp only [instantiated] at checked
          have targetInstantiated :=
            instantiateRule?_eq_some_of_refines refines instantiated
          rw [targetInstantiated]
          cases resolved :
              resolveOpenDAGChildren? context entries premises node.children with
          | none => simp [resolved] at checked
          | some proofs =>
              simp only [resolved, Option.some.injEq] at checked ⊢
              exact checked

private theorem checkOpenDAGNodes?_eq_some_of_refines
    {source target : ValidatedPresentation}
    (refines : RuleLookupRefines source target) {context : List Pattern} :
    ∀ {entries : List OpenDAGEntry} {nodes : List OpenDAGNode}
      {next : List OpenDAGEntry},
      checkOpenDAGNodes? source context entries nodes = some next →
        checkOpenDAGNodes? target context entries nodes = some next := by
  intro entries nodes
  induction nodes generalizing entries with
  | nil =>
      intro next checked
      simpa [checkOpenDAGNodes?] using checked
  | cons node nodes inductionHypothesis =>
      intro next checked
      simp only [checkOpenDAGNodes?] at checked ⊢
      cases first : checkOpenDAGNode? source context entries node with
      | none => simp [first] at checked
      | some middle =>
          simp only [first] at checked
          have targetFirst :=
            checkOpenDAGNode?_eq_some_of_refines refines first
          rw [targetFirst]
          exact inductionHypothesis checked

private theorem checkOpenDAGBlocks?_eq_some_of_refines
    {source target : ValidatedPresentation}
    (refines : RuleLookupRefines source target) {context : List Pattern} :
    ∀ {entries : List OpenDAGEntry} {blocks : List (List OpenDAGNode)}
      {next : List OpenDAGEntry},
      checkOpenDAGBlocks? source context entries blocks = some next →
        checkOpenDAGBlocks? target context entries blocks = some next := by
  intro entries blocks
  induction blocks generalizing entries with
  | nil =>
      intro next checked
      simpa [checkOpenDAGBlocks?] using checked
  | cons block blocks inductionHypothesis =>
      intro next checked
      simp only [checkOpenDAGBlocks?] at checked ⊢
      cases first : checkOpenDAGNodes? source context entries block with
      | none => simp [first] at checked
      | some middle =>
          simp only [first] at checked
          have targetFirst :=
            checkOpenDAGNodes?_eq_some_of_refines refines first
          rw [targetFirst]
          exact inductionHypothesis checked

theorem expandOpenDAGBlocks?_eq_some_of_ruleLookupRefines
    {source target : ValidatedPresentation}
    (refines : RuleLookupRefines source target)
    {context : List Pattern} {goal : Pattern} {rootId : Nat}
    {blocks : List (List OpenDAGNode)} {proof : RawOpenProof}
    (expanded :
      expandOpenDAGBlocks? source context goal rootId blocks = some proof) :
    expandOpenDAGBlocks? target context goal rootId blocks = some proof := by
  unfold expandOpenDAGBlocks? at expanded ⊢
  cases checked : checkOpenDAGBlocks? source context [] blocks with
  | none => simp [checked] at expanded
  | some entries =>
      simp only [checked] at expanded
      have targetChecked :=
        checkOpenDAGBlocks?_eq_some_of_refines refines checked
      rw [targetChecked]
      exact expanded

/-- Exact refinement preserves acceptance of the same open-DAG artifact. -/
theorem checkOpenDAGBlocks_true_of_ruleLookupRefines
    {source target : ValidatedPresentation}
    (refines : RuleLookupRefines source target)
    {context : List Pattern} {goal : Pattern} {rootId : Nat}
    {blocks : List (List OpenDAGNode)}
    (checked :
      checkOpenDAGBlocks source context goal rootId blocks = true) :
    checkOpenDAGBlocks target context goal rootId blocks = true := by
  unfold checkOpenDAGBlocks at checked ⊢
  cases expanded :
      expandOpenDAGBlocks? source context goal rootId blocks with
  | none => simp [expanded] at checked
  | some proof =>
      have targetExpanded :=
        expandOpenDAGBlocks?_eq_some_of_ruleLookupRefines refines expanded
      simp [targetExpanded]

namespace CheckedOpenDAG

/-- Transport a checked DAG without changing identifiers, blocks, or sharing. -/
def transport {source target : Object}
    (refines : RuleLookupRefines source.presentation target.presentation)
    {context : List Pattern} {goal : Pattern}
    (dag : CheckedOpenDAG source context goal) :
    CheckedOpenDAG target context goal :=
  { rootId := dag.rootId
    blocks := dag.blocks
    accepted :=
      checkOpenDAGBlocks_true_of_ruleLookupRefines refines dag.accepted }

@[simp] theorem transport_rootId {source target : Object}
    (refines : RuleLookupRefines source.presentation target.presentation)
    {context : List Pattern} {goal : Pattern}
    (dag : CheckedOpenDAG source context goal) :
    (dag.transport refines).rootId = dag.rootId := rfl

@[simp] theorem transport_blocks {source target : Object}
    (refines : RuleLookupRefines source.presentation target.presentation)
    {context : List Pattern} {goal : Pattern}
    (dag : CheckedOpenDAG source context goal) :
    (dag.transport refines).blocks = dag.blocks := rfl

end CheckedOpenDAG

end Mettapedia.GSLT.LanguageDef.ProofGSLT
