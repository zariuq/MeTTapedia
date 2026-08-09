import Mettapedia.GSLT.LanguageDef.ProofGSLTOpenChecker

/-!
# Chronological DAG templates with premise holes

This is the compact evidence layer for general proof-GSLT interpretations.
References distinguish premise occurrences from previously checked rule nodes.
Rule-node identifiers must be unique and every node reference must point
backward into the chronological environment.  Premise references remain
positions in the ordered open context.

The checker reconstructs an exact `RawOpenProof` tree as ghost evidence.
Successful DAG checking therefore yields a typed `OpenDerivation`, while the
submitted DAG remains available for cost, provenance, and sharing-sensitive
consumers.  The theorem does not identify DAG-node cost with expanded-tree
cost.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- One child edge either cites an authored premise occurrence or an earlier
derived node. -/
inductive OpenDAGReference where
  | premise (index : Nat)
  | node (id : Nat)
deriving Repr

/-- One chronological derived node in an open proof DAG. -/
structure OpenDAGNode where
  id : Nat
  ruleInstance : RuleInstance
  children : List OpenDAGReference
deriving Repr

/-- Logical checker state.  The proof tree is ghost evidence reconstructed
from sharing references. -/
structure OpenDAGEntry where
  id : Nat
  goal : Pattern
  proof : RawOpenProof
deriving Repr

def findOpenDAGEntry? : List OpenDAGEntry → Nat → Option OpenDAGEntry
  | [], _ => none
  | entry :: entries, id =>
      if entry.id = id then some entry else findOpenDAGEntry? entries id

private theorem findOpenDAGEntry?_eq_some_mem
    {entries : List OpenDAGEntry} {id : Nat} {entry : OpenDAGEntry}
    (found : findOpenDAGEntry? entries id = some entry) :
    entry ∈ entries := by
  induction entries with
  | nil => simp [findOpenDAGEntry?] at found
  | cons head tail inductionHypothesis =>
      by_cases same : head.id = id
      · simp [findOpenDAGEntry?, same] at found
        subst entry
        simp
      · simp [findOpenDAGEntry?, same] at found
        exact List.mem_cons_of_mem head (inductionHypothesis found)

/-- Resolve one typed child edge to its expanded open proof. -/
def resolveOpenDAGReference? (context : List Pattern)
    (entries : List OpenDAGEntry) (expected : Pattern) :
    OpenDAGReference → Option RawOpenProof
  | .premise index =>
      match context[index]? with
      | some actual =>
          if actual = expected then some (.premise index) else none
      | none => none
  | .node id =>
      match findOpenDAGEntry? entries id with
      | some entry => if entry.goal = expected then some entry.proof else none
      | none => none

/-- Resolve an ordered premise vector. -/
def resolveOpenDAGChildren? (context : List Pattern)
    (entries : List OpenDAGEntry) :
    List Pattern → List OpenDAGReference → Option (List RawOpenProof)
  | [], [] => some []
  | premise :: premises, child :: children => do
      let proof ← resolveOpenDAGReference? context entries premise child
      let proofs ← resolveOpenDAGChildren? context entries premises children
      some (proof :: proofs)
  | _, _ => none

/-- Check and append one chronological open-DAG node. -/
def checkOpenDAGNode? (presentation : ValidatedPresentation)
    (context : List Pattern) (entries : List OpenDAGEntry)
    (node : OpenDAGNode) : Option (List OpenDAGEntry) :=
  match findOpenDAGEntry? entries node.id with
  | some _ => none
  | none =>
      match instantiateRule? presentation node.ruleInstance with
      | none => none
      | some (premises, conclusion) =>
          match resolveOpenDAGChildren? context entries premises node.children with
          | none => none
          | some children =>
              some
                ({ id := node.id
                   goal := conclusion
                   proof := .node node.ruleInstance children } :: entries)

/-- Check a chronological node list. -/
def checkOpenDAGNodes? (presentation : ValidatedPresentation)
    (context : List Pattern) :
    List OpenDAGEntry → List OpenDAGNode → Option (List OpenDAGEntry)
  | entries, [] => some entries
  | entries, node :: nodes => do
      let next ← checkOpenDAGNode? presentation context entries node
      checkOpenDAGNodes? presentation context next nodes

/-- Check bounded transport blocks while retaining one chronological
environment. -/
def checkOpenDAGBlocks? (presentation : ValidatedPresentation)
    (context : List Pattern) :
    List OpenDAGEntry → List (List OpenDAGNode) → Option (List OpenDAGEntry)
  | entries, [] => some entries
  | entries, block :: blocks => do
      let next ← checkOpenDAGNodes? presentation context entries block
      checkOpenDAGBlocks? presentation context next blocks

/-- Reconstruct the selected root after checking every chronological block. -/
def expandOpenDAGBlocks? (presentation : ValidatedPresentation)
    (context : List Pattern) (goal : Pattern) (rootId : Nat)
    (blocks : List (List OpenDAGNode)) : Option RawOpenProof := do
  let entries ← checkOpenDAGBlocks? presentation context [] blocks
  let root ← findOpenDAGEntry? entries rootId
  if root.goal = goal then some root.proof else none

/-- Boolean executable boundary for open proof DAGs. -/
def checkOpenDAGBlocks (presentation : ValidatedPresentation)
    (context : List Pattern) (goal : Pattern) (rootId : Nat)
    (blocks : List (List OpenDAGNode)) : Bool :=
  (expandOpenDAGBlocks? presentation context goal rootId blocks).isSome

private def OpenDAGEnvironmentSound (presentation : ValidatedPresentation)
    (context : List Pattern) (entries : List OpenDAGEntry) : Prop :=
  ∀ entry ∈ entries,
    checkOpenRaw presentation context entry.goal entry.proof = true

private theorem emptyOpenDAGEnvironmentSound
    (presentation : ValidatedPresentation) (context : List Pattern) :
    OpenDAGEnvironmentSound presentation context [] := by
  intro entry membership
  simp at membership

private theorem resolveOpenDAGReference?_sound
    {presentation : ValidatedPresentation} {context : List Pattern}
    {entries : List OpenDAGEntry}
    (sound : OpenDAGEnvironmentSound presentation context entries)
    {expected : Pattern} {reference : OpenDAGReference}
    {proof : RawOpenProof}
    (resolved :
      resolveOpenDAGReference? context entries expected reference =
        some proof) :
    checkOpenRaw presentation context expected proof = true := by
  cases reference with
  | premise index =>
      simp only [resolveOpenDAGReference?] at resolved
      cases lookup : context[index]? with
      | none => simp [lookup] at resolved
      | some actual =>
          by_cases same : actual = expected
          · simp [lookup, same] at resolved
            subst proof
            simp [checkOpenRaw, lookup, same]
          · simp [lookup, same] at resolved
  | node id =>
      simp only [resolveOpenDAGReference?] at resolved
      cases found : findOpenDAGEntry? entries id with
      | none => simp [found] at resolved
      | some entry =>
          by_cases same : entry.goal = expected
          · simp [found, same] at resolved
            subst proof
            rw [← same]
            exact sound entry (findOpenDAGEntry?_eq_some_mem found)
          · simp [found, same] at resolved

private theorem resolveOpenDAGChildren?_sound
    {presentation : ValidatedPresentation} {context : List Pattern}
    {entries : List OpenDAGEntry}
    (sound : OpenDAGEnvironmentSound presentation context entries) :
    ∀ {premises : List Pattern} {references : List OpenDAGReference}
      {proofs : List RawOpenProof},
      resolveOpenDAGChildren? context entries premises references =
          some proofs →
        checkOpenRawChildren presentation context premises proofs = true := by
  intro premises
  induction premises with
  | nil =>
      intro references proofs resolved
      cases references with
      | nil =>
          simp [resolveOpenDAGChildren?] at resolved
          subst proofs
          simp [checkOpenRawChildren]
      | cons reference references =>
          simp [resolveOpenDAGChildren?] at resolved
  | cons premise premises inductionHypothesis =>
      intro references proofs resolved
      cases references with
      | nil => simp [resolveOpenDAGChildren?] at resolved
      | cons reference references =>
          simp only [resolveOpenDAGChildren?] at resolved
          cases first :
              resolveOpenDAGReference? context entries premise reference with
          | none => simp [first] at resolved
          | some proof =>
              simp only [first] at resolved
              cases rest :
                  resolveOpenDAGChildren? context entries premises references with
              | none => simp [rest] at resolved
              | some tailProofs =>
                  simp [rest] at resolved
                  subst proofs
                  simp only [checkOpenRawChildren, Bool.and_eq_true]
                  exact
                    ⟨resolveOpenDAGReference?_sound sound first,
                      inductionHypothesis rest⟩

private theorem checkOpenDAGNode?_sound
    {presentation : ValidatedPresentation} {context : List Pattern}
    {entries next : List OpenDAGEntry} {node : OpenDAGNode}
    (sound : OpenDAGEnvironmentSound presentation context entries)
    (checked :
      checkOpenDAGNode? presentation context entries node = some next) :
    OpenDAGEnvironmentSound presentation context next := by
  unfold checkOpenDAGNode? at checked
  cases duplicate : findOpenDAGEntry? entries node.id with
  | some entry => simp [duplicate] at checked
  | none =>
      simp only [duplicate] at checked
      cases instantiated : instantiateRule? presentation node.ruleInstance with
      | none => simp [instantiated] at checked
      | some result =>
          rcases result with ⟨premises, conclusion⟩
          simp only [instantiated] at checked
          cases resolved :
              resolveOpenDAGChildren? context entries premises node.children with
          | none => simp [resolved] at checked
          | some children =>
              simp only [resolved, Option.some.injEq] at checked
              subst next
              intro entry membership
              simp only [List.mem_cons] at membership
              rcases membership with equality | membership
              · subst entry
                have childrenSound :=
                  resolveOpenDAGChildren?_sound sound resolved
                simp [checkOpenRaw, instantiated, childrenSound]
              · exact sound entry membership

private theorem checkOpenDAGNodes?_sound
    {presentation : ValidatedPresentation} {context : List Pattern} :
    ∀ {entries : List OpenDAGEntry} {nodes : List OpenDAGNode}
      {next : List OpenDAGEntry},
      OpenDAGEnvironmentSound presentation context entries →
      checkOpenDAGNodes? presentation context entries nodes = some next →
      OpenDAGEnvironmentSound presentation context next := by
  intro entries nodes
  induction nodes generalizing entries with
  | nil =>
      intro next sound checked
      simp [checkOpenDAGNodes?] at checked
      subst next
      exact sound
  | cons node nodes inductionHypothesis =>
      intro next sound checked
      simp only [checkOpenDAGNodes?] at checked
      cases first : checkOpenDAGNode? presentation context entries node with
      | none => simp [first] at checked
      | some middle =>
          simp only [first] at checked
          exact inductionHypothesis (checkOpenDAGNode?_sound sound first) checked

private theorem checkOpenDAGBlocks?_sound
    {presentation : ValidatedPresentation} {context : List Pattern} :
    ∀ {entries : List OpenDAGEntry} {blocks : List (List OpenDAGNode)}
      {next : List OpenDAGEntry},
      OpenDAGEnvironmentSound presentation context entries →
      checkOpenDAGBlocks? presentation context entries blocks = some next →
      OpenDAGEnvironmentSound presentation context next := by
  intro entries blocks
  induction blocks generalizing entries with
  | nil =>
      intro next sound checked
      simp [checkOpenDAGBlocks?] at checked
      subst next
      exact sound
  | cons block blocks inductionHypothesis =>
      intro next sound checked
      simp only [checkOpenDAGBlocks?] at checked
      cases first : checkOpenDAGNodes? presentation context entries block with
      | none => simp [first] at checked
      | some middle =>
          simp only [first] at checked
          exact inductionHypothesis
            (checkOpenDAGNodes?_sound sound first) checked

/-- Successful open-DAG expansion produces an accepted exact open proof tree. -/
theorem expandOpenDAGBlocks?_sound
    {presentation : ValidatedPresentation} {context : List Pattern}
    {goal : Pattern} {rootId : Nat} {blocks : List (List OpenDAGNode)}
    {proof : RawOpenProof}
    (expanded :
      expandOpenDAGBlocks? presentation context goal rootId blocks =
        some proof) :
    checkOpenRaw presentation context goal proof = true := by
  unfold expandOpenDAGBlocks? at expanded
  cases checked : checkOpenDAGBlocks? presentation context [] blocks with
  | none => simp [checked] at expanded
  | some entries =>
      simp only [checked] at expanded
      cases found : findOpenDAGEntry? entries rootId with
      | none => simp [found] at expanded
      | some root =>
          by_cases same : root.goal = goal
          · simp [found, same] at expanded
            subst proof
            rw [← same]
            exact checkOpenDAGBlocks?_sound
              (emptyOpenDAGEnvironmentSound presentation context) checked
              root (findOpenDAGEntry?_eq_some_mem found)
          · simp [found, same] at expanded

/-- A checked open DAG reconstructs an exact typed open derivation. -/
theorem checkOpenDAGBlocks_exact_derivation
    {presentation : ValidatedPresentation} {context : List Pattern}
    {goal : Pattern} {rootId : Nat} {blocks : List (List OpenDAGNode)}
    (checked :
      checkOpenDAGBlocks presentation context goal rootId blocks = true) :
    ∃ (proof : RawOpenProof)
      (derivation : OpenDerivation presentation context goal),
      expandOpenDAGBlocks? presentation context goal rootId blocks =
          some proof ∧
        derivation.eraseOpen = proof := by
  unfold checkOpenDAGBlocks at checked
  cases expanded :
      expandOpenDAGBlocks? presentation context goal rootId blocks with
  | none => simp [expanded] at checked
  | some proof =>
      have accepted := expandOpenDAGBlocks?_sound expanded
      rcases checkOpenRaw_exact_derivation accepted with
        ⟨derivation, erased⟩
      exact ⟨proof, derivation, rfl, erased⟩

/-- Accepted chronological open-DAG artifact. -/
structure CheckedOpenDAG (object : Object) (context : List Pattern)
    (goal : Pattern) where
  rootId : Nat
  blocks : List (List OpenDAGNode)
  accepted :
    checkOpenDAGBlocks object.presentation context goal rootId blocks = true

end Mettapedia.GSLT.LanguageDef.ProofGSLT
