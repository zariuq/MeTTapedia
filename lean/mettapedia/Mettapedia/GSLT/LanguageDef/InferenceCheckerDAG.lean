import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-!
# Chronological proof-DAG checking

This module gives the generic inference checker a compact proof representation.
Each node contains one ordinary rule instance and an ordered list of earlier
child identifiers.  Checking a node instantiates the same admitted rule schema
as `checkRaw`, requires its child conclusions to equal the ordered premises,
and records the resulting conclusion under a new identifier.

The logical environment below also retains the recursively reconstructed
`RawProof`.  Implementations need retain only the conclusion; the proof field
is ghost evidence used to establish that successful chronological checking
expands to a proof accepted by the ordinary tree checker.
-/

namespace Mettapedia.GSLT.LanguageDef.InferenceCheckerDAG

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- One chronological proof-DAG node.  Child order is premise order. -/
structure DAGNode where
  id : Nat
  ruleInstance : RuleInstance
  children : List Nat
deriving Repr

/-- Logical checker state for one accepted node. -/
structure DAGEntry where
  id : Nat
  goal : Pattern
  proof : RawProof
deriving Repr

def findEntry? : List DAGEntry → Nat → Option DAGEntry
  | [], _ => none
  | entry :: entries, id =>
      if entry.id = id then some entry else findEntry? entries id

private theorem findEntry?_eq_some_mem
    {entries : List DAGEntry} {id : Nat} {entry : DAGEntry}
    (found : findEntry? entries id = some entry) :
    entry ∈ entries := by
  induction entries with
  | nil => simp [findEntry?] at found
  | cons head tail inductionHypothesis =>
      by_cases same : head.id = id
      · simp [findEntry?, same] at found
        subst entry
        simp
      · simp [findEntry?, same] at found
        exact List.mem_cons_of_mem head (inductionHypothesis found)

/-- Resolve an ordered premise vector to the recursively reconstructed child
proofs already admitted in the chronological environment. -/
def resolveChildren? (entries : List DAGEntry) :
    List Pattern → List Nat → Option (List RawProof)
  | [], [] => some []
  | premise :: premises, childId :: childIds => do
      let child ← findEntry? entries childId
      if child.goal = premise then
        let children ← resolveChildren? entries premises childIds
        some (child.proof :: children)
      else
        none
  | _, _ => none

private def EnvironmentSound
    (presentation : ValidatedPresentation) (entries : List DAGEntry) : Prop :=
  ∀ entry ∈ entries,
    checkRaw presentation entry.goal entry.proof = true

private theorem empty_environment_sound
    (presentation : ValidatedPresentation) :
    EnvironmentSound presentation [] := by
  intro entry membership
  simp at membership

private theorem resolveChildren?_sound
    {presentation : ValidatedPresentation} {entries : List DAGEntry}
    (sound : EnvironmentSound presentation entries) :
    ∀ {premises : List Pattern} {childIds : List Nat}
      {proofs : List RawProof},
      resolveChildren? entries premises childIds = some proofs →
        checkRawChildren presentation premises proofs = true := by
  intro premises
  induction premises with
  | nil =>
      intro childIds proofs resolved
      cases childIds with
      | nil =>
          simp [resolveChildren?] at resolved
          subst proofs
          simp [checkRawChildren]
      | cons childId childIds => simp [resolveChildren?] at resolved
  | cons premise premises inductionHypothesis =>
      intro childIds proofs resolved
      cases childIds with
      | nil => simp [resolveChildren?] at resolved
      | cons childId childIds =>
          simp only [resolveChildren?] at resolved
          cases found : findEntry? entries childId with
          | none => simp [found] at resolved
          | some child =>
              by_cases same : child.goal = premise
              · simp only [found] at resolved
                cases tailResolved :
                    resolveChildren? entries premises childIds with
                | none => simp [tailResolved] at resolved
                | some tailProofs =>
                    simp [tailResolved] at resolved
                    rcases resolved with ⟨_, proofEquality⟩
                    subst proofs
                    simp only [checkRawChildren, Bool.and_eq_true]
                    have childSound :=
                      sound child (findEntry?_eq_some_mem found)
                    rw [same] at childSound
                    exact
                      ⟨childSound,
                        inductionHypothesis tailResolved⟩
              · simp [found, same] at resolved

/-- Check and extend the chronological environment by one node. -/
def checkNode? (presentation : ValidatedPresentation)
    (entries : List DAGEntry) (node : DAGNode) : Option (List DAGEntry) :=
  match findEntry? entries node.id with
  | some _ => none
  | none =>
      match instantiateRule? presentation node.ruleInstance with
      | none => none
      | some (premises, conclusion) =>
          match resolveChildren? entries premises node.children with
          | none => none
          | some childProofs =>
              some
                ({ id := node.id
                   goal := conclusion
                   proof := .node node.ruleInstance childProofs } :: entries)

private theorem checkNode?_sound
    {presentation : ValidatedPresentation} {entries next : List DAGEntry}
    {node : DAGNode}
    (sound : EnvironmentSound presentation entries)
    (checked : checkNode? presentation entries node = some next) :
    EnvironmentSound presentation next := by
  unfold checkNode? at checked
  cases duplicate : findEntry? entries node.id with
  | some entry => simp [duplicate] at checked
  | none =>
      simp only [duplicate] at checked
      cases instantiated : instantiateRule? presentation node.ruleInstance with
      | none => simp [instantiated] at checked
      | some result =>
          rcases result with ⟨premises, conclusion⟩
          simp only [instantiated] at checked
          cases resolved :
              resolveChildren? entries premises node.children with
          | none => simp [resolved] at checked
          | some childProofs =>
              simp only [resolved, Option.some.injEq] at checked
              subst next
              intro entry membership
              simp only [List.mem_cons] at membership
              rcases membership with equality | membership
              · subst entry
                have childrenSound := resolveChildren?_sound sound resolved
                simp [checkRaw, instantiated, childrenSound]
              · exact sound entry membership

/-- Check a chronological node list, threading one shared environment. -/
def checkNodes? (presentation : ValidatedPresentation) :
    List DAGEntry → List DAGNode → Option (List DAGEntry)
  | entries, [] => some entries
  | entries, node :: nodes => do
      let next ← checkNode? presentation entries node
      checkNodes? presentation next nodes

private theorem checkNodes?_sound
    {presentation : ValidatedPresentation} :
    ∀ {entries : List DAGEntry} {nodes : List DAGNode}
      {next : List DAGEntry},
      EnvironmentSound presentation entries →
      checkNodes? presentation entries nodes = some next →
      EnvironmentSound presentation next := by
  intro entries nodes
  induction nodes generalizing entries with
  | nil =>
      intro next sound checked
      simp [checkNodes?] at checked
      subst next
      exact sound
  | cons node nodes inductionHypothesis =>
      intro next sound checked
      simp only [checkNodes?] at checked
      cases first : checkNode? presentation entries node with
      | none => simp [first] at checked
      | some middle =>
          simp only [first] at checked
          exact inductionHypothesis (checkNode?_sound sound first) checked

/-- Check a list of bounded transport blocks.  Block boundaries do not alter
the environment or proof order. -/
def checkBlocks? (presentation : ValidatedPresentation) :
    List DAGEntry → List (List DAGNode) → Option (List DAGEntry)
  | entries, [] => some entries
  | entries, block :: blocks => do
      let next ← checkNodes? presentation entries block
      checkBlocks? presentation next blocks

private theorem checkBlocks?_sound
    {presentation : ValidatedPresentation} :
    ∀ {entries : List DAGEntry} {blocks : List (List DAGNode)}
      {next : List DAGEntry},
      EnvironmentSound presentation entries →
      checkBlocks? presentation entries blocks = some next →
      EnvironmentSound presentation next := by
  intro entries blocks
  induction blocks generalizing entries with
  | nil =>
      intro next sound checked
      simp [checkBlocks?] at checked
      subst next
      exact sound
  | cons block blocks inductionHypothesis =>
      intro next sound checked
      simp only [checkBlocks?] at checked
      cases first : checkNodes? presentation entries block with
      | none => simp [first] at checked
      | some middle =>
          simp only [first] at checked
          exact inductionHypothesis (checkNodes?_sound sound first) checked

/-- Reconstruct the selected root proof after checking all chronological
blocks and require its conclusion to equal the requested goal. -/
def expandDAGBlocks? (presentation : ValidatedPresentation)
    (goal : Pattern) (rootId : Nat) (blocks : List (List DAGNode)) :
    Option RawProof := do
  let entries ← checkBlocks? presentation [] blocks
  let root ← findEntry? entries rootId
  if root.goal = goal then some root.proof else none

theorem expandDAGBlocks?_sound
    {presentation : ValidatedPresentation} {goal : Pattern} {rootId : Nat}
    {blocks : List (List DAGNode)} {proof : RawProof}
    (expanded : expandDAGBlocks? presentation goal rootId blocks = some proof) :
    checkRaw presentation goal proof = true := by
  unfold expandDAGBlocks? at expanded
  cases checked : checkBlocks? presentation [] blocks with
  | none => simp [checked] at expanded
  | some entries =>
      simp only [checked] at expanded
      cases found : findEntry? entries rootId with
      | none => simp [found] at expanded
      | some root =>
          by_cases same : root.goal = goal
          · simp [found, same] at expanded
            subst proof
            rw [← same]
            exact checkBlocks?_sound (empty_environment_sound presentation)
              checked root (findEntry?_eq_some_mem found)
          · simp [found, same] at expanded

/-- Executable Boolean wrapper around compact proof-DAG expansion. -/
def checkDAGBlocks (presentation : ValidatedPresentation)
    (goal : Pattern) (rootId : Nat) (blocks : List (List DAGNode)) : Bool :=
  (expandDAGBlocks? presentation goal rootId blocks).isSome

/-- Successful chronological block checking produces an ordinary raw proof
accepted by the generic tree checker for the same goal. -/
theorem checkDAGBlocks_sound
    {presentation : ValidatedPresentation} {goal : Pattern} {rootId : Nat}
    {blocks : List (List DAGNode)}
    (checked : checkDAGBlocks presentation goal rootId blocks = true) :
    ∃ proof, checkRaw presentation goal proof = true := by
  unfold checkDAGBlocks at checked
  cases expanded : expandDAGBlocks? presentation goal rootId blocks with
  | none => simp [expanded] at checked
  | some proof => exact ⟨proof, expandDAGBlocks?_sound expanded⟩

/-- Successful compact checking exposes the exact reconstructed raw proof and
a typed derivation whose erasure is that same proof.  This is stronger than
mere inhabitation of the requested goal. -/
theorem checkDAGBlocks_exact_derivation
    {presentation : ValidatedPresentation} {goal : Pattern} {rootId : Nat}
    {blocks : List (List DAGNode)}
    (checked : checkDAGBlocks presentation goal rootId blocks = true) :
    ∃ (proof : RawProof) (derivation : Derivation presentation goal),
      expandDAGBlocks? presentation goal rootId blocks = some proof ∧
        derivation.erase = proof := by
  unfold checkDAGBlocks at checked
  cases expanded : expandDAGBlocks? presentation goal rootId blocks with
  | none => simp [expanded] at checked
  | some proof =>
      have accepted : checkRaw presentation goal proof = true :=
        expandDAGBlocks?_sound expanded
      rcases checkRaw_exists_derivation_with_exact_erasure accepted with
        ⟨derivation, erased⟩
      exact ⟨proof, derivation, rfl, erased⟩

/-! ## Executable boundary fixtures -/

private def fixtureA : Pattern := .apply "DAGA" []
private def fixtureB : Pattern := .apply "DAGB" []
private def fixtureC : Pattern := .apply "DAGC" []

private def fixtureAxA : RuleSchema :=
  { id := ⟨"dag-ax-a"⟩
    metavariables := []
    premises := []
    conclusion := fixtureA }

private def fixtureAxB : RuleSchema :=
  { id := ⟨"dag-ax-b"⟩
    metavariables := []
    premises := []
    conclusion := fixtureB }

private def fixtureCombine : RuleSchema :=
  { id := ⟨"dag-combine"⟩
    metavariables := []
    premises := [fixtureA, fixtureB]
    conclusion := fixtureC }

private def fixturePresentation : Presentation :=
  { language :=
      { LanguageDef.empty "inference-dag-fixture" with
        judgments :=
          [{ head := "DAGA", arity := 0 },
           { head := "DAGB", arity := 0 },
           { head := "DAGC", arity := 0 }]
        inferenceRules := [fixtureAxA, fixtureAxB, fixtureCombine] } }

private theorem fixture_emptyLanguage_validate :
    (LanguageDef.empty "inference-dag-fixture").validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [LanguageDef.empty, LanguageDef.typeNames]

private theorem fixturePresentation_valid :
    fixturePresentation.isValidV2 = true := by
  simp [fixturePresentation, Presentation.isValidV2,
    Presentation.judgmentSignatureValid, Presentation.judgmentHeads,
    Presentation.isValidV1, Presentation.ruleIds,
    fixture_emptyLanguage_validate, fixtureAxA, fixtureAxB, fixtureCombine,
    fixtureA, fixtureB, fixtureC, RuleSchema.isValidIn,
    Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
    fixedConstructorListsValid, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]
  decide

private def fixtureValidated : ValidatedPresentation :=
  ⟨fixturePresentation, fixturePresentation_valid⟩

private def fixtureNodeA : DAGNode :=
  { id := 0, ruleInstance := ⟨⟨"dag-ax-a"⟩, []⟩, children := [] }

private def fixtureNodeB : DAGNode :=
  { id := 1, ruleInstance := ⟨⟨"dag-ax-b"⟩, []⟩, children := [] }

private def fixtureNodeC : DAGNode :=
  { id := 2
    ruleInstance := ⟨⟨"dag-combine"⟩, []⟩
    children := [0, 1] }

private def fixtureBlocks : List (List DAGNode) :=
  [[fixtureNodeA, fixtureNodeB], [fixtureNodeC]]

private theorem fixtureNodeA_instantiates :
    instantiateRule? fixtureValidated
      { ruleId := ⟨"dag-ax-a"⟩, arguments := [] } =
      some ([], fixtureA) := by
  simp [instantiateRule?, fixtureValidated, fixturePresentation,
    fixtureAxA, fixtureAxB, fixtureCombine, fixtureA,
    Presentation.lookupRule?, argumentsValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

private theorem fixtureNodeB_instantiates :
    instantiateRule? fixtureValidated
      { ruleId := ⟨"dag-ax-b"⟩, arguments := [] } =
      some ([], fixtureB) := by
  simp [instantiateRule?, fixtureValidated, fixturePresentation,
    fixtureAxA, fixtureAxB, fixtureCombine, fixtureB,
    Presentation.lookupRule?, argumentsValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

private theorem fixtureNodeC_instantiates :
    instantiateRule? fixtureValidated
      { ruleId := ⟨"dag-combine"⟩, arguments := [] } =
      some ([fixtureA, fixtureB], fixtureC) := by
  simp [instantiateRule?, fixtureValidated, fixturePresentation,
    fixtureAxA, fixtureAxB, fixtureCombine, fixtureA, fixtureB, fixtureC,
    Presentation.lookupRule?, argumentsValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

theorem fixture_blocks_accept :
    checkDAGBlocks fixtureValidated fixtureC 2 fixtureBlocks = true := by
  simp [checkDAGBlocks, expandDAGBlocks?, checkBlocks?, checkNodes?, checkNode?,
    resolveChildren?, findEntry?, fixtureBlocks, fixtureNodeA, fixtureNodeB,
    fixtureNodeC, fixtureNodeA_instantiates, fixtureNodeB_instantiates,
    fixtureNodeC_instantiates]

theorem fixture_swapped_children_reject :
    checkDAGBlocks fixtureValidated fixtureC 2
      [[fixtureNodeA, fixtureNodeB],
       [{ fixtureNodeC with children := [1, 0] }]] = false := by
  simp [checkDAGBlocks, expandDAGBlocks?, checkBlocks?, checkNodes?, checkNode?,
    resolveChildren?, findEntry?, fixtureNodeA, fixtureNodeB, fixtureNodeC,
    fixtureA, fixtureB,
    fixtureNodeA_instantiates, fixtureNodeB_instantiates,
    fixtureNodeC_instantiates]

theorem fixture_forward_child_reject :
    checkDAGBlocks fixtureValidated fixtureC 2
      [[fixtureNodeC], [fixtureNodeA, fixtureNodeB]] = false := by
  simp [checkDAGBlocks, expandDAGBlocks?, checkBlocks?, checkNodes?, checkNode?,
    resolveChildren?, findEntry?, fixtureNodeA, fixtureNodeB, fixtureNodeC,
    fixtureNodeC_instantiates]

theorem fixture_duplicate_id_reject :
    checkDAGBlocks fixtureValidated fixtureC 2
      [[fixtureNodeA, { fixtureNodeB with id := 0 }], [fixtureNodeC]] = false := by
  simp [checkDAGBlocks, expandDAGBlocks?, checkBlocks?, checkNodes?, checkNode?,
    resolveChildren?, findEntry?, fixtureNodeA, fixtureNodeB, fixtureNodeC,
    fixtureNodeA_instantiates, fixtureNodeB_instantiates]

end Mettapedia.GSLT.LanguageDef.InferenceCheckerDAG
