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

/-! ## Streaming chronological checking

The block checker above bounds transport depth, but retains every admitted
node.  A streaming certificate additionally names entries whose final use has
just occurred.  Releases are checked: an unknown or repeated identifier
rejects.  Node identifiers must be the consecutive chronological sequence
starting at zero, so releasing an entry cannot make its identifier reusable.

The release schedule is untrusted.  Releasing a needed entry makes a later
premise lookup fail; retaining an entry only consumes more memory.  Thus a
producer may compute liveness aggressively without entering the trusted
boundary.
-/

/-- One chronological node together with entries to release after the node
has been admitted. -/
structure StreamingDAGNode where
  node : DAGNode
  releases : List Nat
deriving Repr

/-- Live state of the streaming checker.  `nextId` enforces global freshness
without retaining a set of all earlier identifiers. -/
structure StreamingDAGState where
  nextId : Nat
  entries : List DAGEntry
deriving Repr

/-- Remove one live entry after its existence has been checked. -/
def eraseEntry (entries : List DAGEntry) (id : Nat) : List DAGEntry :=
  entries.filter fun entry => entry.id != id

/-- Release an exact list of live identifiers.  Missing or repeated releases
reject rather than silently changing the certificate. -/
def releaseEntries? : List DAGEntry → List Nat → Option (List DAGEntry)
  | entries, [] => some entries
  | entries, id :: ids =>
      match findEntry? entries id with
      | none => none
      | some _ => releaseEntries? (eraseEntry entries id) ids

private theorem eraseEntry_sound
    {presentation : ValidatedPresentation} {entries : List DAGEntry}
    (sound : EnvironmentSound presentation entries) (id : Nat) :
    EnvironmentSound presentation (eraseEntry entries id) := by
  intro entry membership
  exact sound entry (List.mem_filter.mp membership).1

private theorem releaseEntries?_sound
    {presentation : ValidatedPresentation} :
    ∀ {entries next : List DAGEntry} {ids : List Nat},
      EnvironmentSound presentation entries →
      releaseEntries? entries ids = some next →
      EnvironmentSound presentation next := by
  intro entries next ids
  induction ids generalizing entries with
  | nil =>
      intro sound released
      simp [releaseEntries?] at released
      subst next
      exact sound
  | cons id ids inductionHypothesis =>
      intro sound released
      simp only [releaseEntries?] at released
      cases found : findEntry? entries id with
      | none => simp [found] at released
      | some entry =>
          simp only [found] at released
          exact inductionHypothesis (eraseEntry_sound sound id) released

/-- Check one node, enforce its consecutive identifier, then apply its checked
release list. -/
def checkStreamingNode? (presentation : ValidatedPresentation)
    (state : StreamingDAGState) (action : StreamingDAGNode) :
    Option StreamingDAGState :=
  if action.node.id = state.nextId then do
    let admitted ← checkNode? presentation state.entries action.node
    let live ← releaseEntries? admitted action.releases
    some { nextId := state.nextId + 1, entries := live }
  else
    none

private theorem checkStreamingNode?_sound
    {presentation : ValidatedPresentation}
    {state next : StreamingDAGState} {action : StreamingDAGNode}
    (sound : EnvironmentSound presentation state.entries)
    (checked : checkStreamingNode? presentation state action = some next) :
    EnvironmentSound presentation next.entries := by
  unfold checkStreamingNode? at checked
  by_cases consecutive : action.node.id = state.nextId
  · simp only [consecutive, ↓reduceIte] at checked
    cases admitted :
        checkNode? presentation state.entries action.node with
    | none => simp [admitted] at checked
    | some entries =>
        simp only [admitted] at checked
        cases released : releaseEntries? entries action.releases with
        | none => simp [released] at checked
        | some live =>
            simp [released] at checked
            subst next
            exact releaseEntries?_sound
              (checkNode?_sound sound admitted) released
  · simp [consecutive] at checked

/-- Check a bounded sequence of streaming actions. -/
def checkStreamingNodes? (presentation : ValidatedPresentation) :
    StreamingDAGState → List StreamingDAGNode → Option StreamingDAGState
  | state, [] => some state
  | state, action :: actions => do
      let next ← checkStreamingNode? presentation state action
      checkStreamingNodes? presentation next actions

private theorem checkStreamingNodes?_sound
    {presentation : ValidatedPresentation} :
    ∀ {state next : StreamingDAGState} {actions : List StreamingDAGNode},
      EnvironmentSound presentation state.entries →
      checkStreamingNodes? presentation state actions = some next →
      EnvironmentSound presentation next.entries := by
  intro state next actions
  induction actions generalizing state with
  | nil =>
      intro sound checked
      simp [checkStreamingNodes?] at checked
      subst next
      exact sound
  | cons action actions inductionHypothesis =>
      intro sound checked
      simp only [checkStreamingNodes?] at checked
      cases first : checkStreamingNode? presentation state action with
      | none => simp [first] at checked
      | some middle =>
          simp only [first] at checked
          exact inductionHypothesis
            (checkStreamingNode?_sound sound first) checked

/-- Check independently bounded streaming blocks while retaining only the live
frontier between blocks. -/
def checkStreamingBlocks? (presentation : ValidatedPresentation) :
    StreamingDAGState → List (List StreamingDAGNode) →
      Option StreamingDAGState
  | state, [] => some state
  | state, block :: blocks => do
      let next ← checkStreamingNodes? presentation state block
      checkStreamingBlocks? presentation next blocks

private theorem checkStreamingBlocks?_sound
    {presentation : ValidatedPresentation} :
    ∀ {state next : StreamingDAGState}
      {blocks : List (List StreamingDAGNode)},
      EnvironmentSound presentation state.entries →
      checkStreamingBlocks? presentation state blocks = some next →
      EnvironmentSound presentation next.entries := by
  intro state next blocks
  induction blocks generalizing state with
  | nil =>
      intro sound checked
      simp [checkStreamingBlocks?] at checked
      subst next
      exact sound
  | cons block blocks inductionHypothesis =>
      intro sound checked
      simp only [checkStreamingBlocks?] at checked
      cases first : checkStreamingNodes? presentation state block with
      | none => simp [first] at checked
      | some middle =>
          simp only [first] at checked
          exact inductionHypothesis
            (checkStreamingNodes?_sound sound first) checked

/-- Check all streaming blocks and reconstruct the surviving root proof. -/
def expandStreamingDAGBlocks? (presentation : ValidatedPresentation)
    (goal : Pattern) (rootId : Nat)
    (blocks : List (List StreamingDAGNode)) : Option RawProof := do
  let final ←
    checkStreamingBlocks? presentation
      { nextId := 0, entries := [] } blocks
  let root ← findEntry? final.entries rootId
  if root.goal = goal then some root.proof else none

theorem expandStreamingDAGBlocks?_sound
    {presentation : ValidatedPresentation} {goal : Pattern} {rootId : Nat}
    {blocks : List (List StreamingDAGNode)} {proof : RawProof}
    (expanded :
      expandStreamingDAGBlocks? presentation goal rootId blocks =
        some proof) :
    checkRaw presentation goal proof = true := by
  unfold expandStreamingDAGBlocks? at expanded
  cases checked :
      checkStreamingBlocks? presentation
        { nextId := 0, entries := [] } blocks with
  | none => simp [checked] at expanded
  | some final =>
      simp only [checked] at expanded
      cases found : findEntry? final.entries rootId with
      | none => simp [found] at expanded
      | some root =>
          by_cases same : root.goal = goal
          · simp [found, same] at expanded
            subst proof
            rw [← same]
            exact
              checkStreamingBlocks?_sound
                (empty_environment_sound presentation) checked
                root (findEntry?_eq_some_mem found)
          · simp [found, same] at expanded

/-- Executable Boolean streaming checker. -/
def checkStreamingDAGBlocks (presentation : ValidatedPresentation)
    (goal : Pattern) (rootId : Nat)
    (blocks : List (List StreamingDAGNode)) : Bool :=
  (expandStreamingDAGBlocks? presentation goal rootId blocks).isSome

/-- Acceptance by the bounded-live-frontier checker yields an ordinary proof
accepted by the generic tree checker. -/
theorem checkStreamingDAGBlocks_sound
    {presentation : ValidatedPresentation} {goal : Pattern} {rootId : Nat}
    {blocks : List (List StreamingDAGNode)}
    (checked :
      checkStreamingDAGBlocks presentation goal rootId blocks = true) :
    ∃ proof, checkRaw presentation goal proof = true := by
  unfold checkStreamingDAGBlocks at checked
  cases expanded :
      expandStreamingDAGBlocks? presentation goal rootId blocks with
  | none => simp [expanded] at checked
  | some proof =>
      exact ⟨proof, expandStreamingDAGBlocks?_sound expanded⟩

/-- Streaming acceptance exposes a typed derivation whose erasure is the exact
reconstructed root proof. -/
theorem checkStreamingDAGBlocks_exact_derivation
    {presentation : ValidatedPresentation} {goal : Pattern} {rootId : Nat}
    {blocks : List (List StreamingDAGNode)}
    (checked :
      checkStreamingDAGBlocks presentation goal rootId blocks = true) :
    ∃ (proof : RawProof) (derivation : Derivation presentation goal),
      expandStreamingDAGBlocks? presentation goal rootId blocks =
          some proof ∧
        derivation.erase = proof := by
  unfold checkStreamingDAGBlocks at checked
  cases expanded :
      expandStreamingDAGBlocks? presentation goal rootId blocks with
  | none => simp [expanded] at checked
  | some proof =>
      have accepted : checkRaw presentation goal proof = true :=
        expandStreamingDAGBlocks?_sound expanded
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
  { language := LanguageDef.empty "inference-dag-fixture"
    calculus :=
      { judgments :=
          [{ head := "DAGA", arity := 0 },
           { head := "DAGB", arity := 0 },
           { head := "DAGC", arity := 0 }]
        rules := [fixtureAxA, fixtureAxB, fixtureCombine] } }

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

private def fixtureStreamingBlocks : List (List StreamingDAGNode) :=
  [[{ node := fixtureNodeA, releases := [] },
    { node := fixtureNodeB, releases := [] }],
   [{ node := fixtureNodeC, releases := [0, 1] }]]

/-- Positive boundary: both premises may be released immediately after their
last use while the root remains available. -/
theorem fixture_streaming_blocks_accept :
    checkStreamingDAGBlocks fixtureValidated fixtureC 2
      fixtureStreamingBlocks = true := by
  simp [checkStreamingDAGBlocks, expandStreamingDAGBlocks?,
    checkStreamingBlocks?, checkStreamingNodes?, checkStreamingNode?,
    releaseEntries?, eraseEntry, checkNode?, resolveChildren?, findEntry?,
    fixtureStreamingBlocks, fixtureNodeA, fixtureNodeB, fixtureNodeC,
    fixtureNodeA_instantiates, fixtureNodeB_instantiates,
    fixtureNodeC_instantiates]

/-- Negative boundary: releasing a premise before its final use makes the
later rule application fail. -/
theorem fixture_premature_release_reject :
    checkStreamingDAGBlocks fixtureValidated fixtureC 2
      [[{ node := fixtureNodeA, releases := [0] },
        { node := fixtureNodeB, releases := [] }],
       [{ node := fixtureNodeC, releases := [1] }]] = false := by
  simp [checkStreamingDAGBlocks, expandStreamingDAGBlocks?,
    checkStreamingBlocks?, checkStreamingNodes?, checkStreamingNode?,
    releaseEntries?, eraseEntry, checkNode?, resolveChildren?, findEntry?,
    fixtureNodeA, fixtureNodeB, fixtureNodeC, fixtureA,
    fixtureNodeA_instantiates, fixtureNodeB_instantiates,
    fixtureNodeC_instantiates]

/-- Negative boundary: after release, a past identifier still cannot be
reused because the consecutive counter is independent of the live entries. -/
theorem fixture_released_id_reuse_reject :
    checkStreamingDAGBlocks fixtureValidated fixtureC 2
      [[{ node := fixtureNodeA, releases := [0] },
        { node := { fixtureNodeB with id := 0 }, releases := [] }],
       [{ node := fixtureNodeC, releases := [] }]] = false := by
  simp [checkStreamingDAGBlocks, expandStreamingDAGBlocks?,
    checkStreamingBlocks?, checkStreamingNodes?, checkStreamingNode?,
    releaseEntries?, eraseEntry, checkNode?, resolveChildren?, findEntry?,
    fixtureNodeA, fixtureNodeB, fixtureNodeC,
    fixtureNodeA_instantiates]

end Mettapedia.GSLT.LanguageDef.InferenceCheckerDAG
