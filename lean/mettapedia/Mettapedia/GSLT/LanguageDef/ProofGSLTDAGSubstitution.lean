import Mettapedia.GSLT.LanguageDef.ProofGSLTRawSubstitution
import Mettapedia.GSLT.LanguageDef.ProofGSLTOpenDAG

/-!
# Sharing-preserving substitution of chronological proof DAGs

Open derivations compose by `bind`; this module composes their compact
evidence.  Given a checked DAG for `Γ ⊢ A` and one checked DAG per premise
position of `Γ` (all over a common ambient context `Δ`), the composite DAG
lists every environment segment once, then the outer DAG with each premise
citation rewired to the root of its segment.

Identifier discipline is by disjoint shifting: segment `i` is shifted past
every earlier segment's identifier bound, and the outer DAG past all of
them.  Rewiring touches only the outer DAG: environment segments keep their
premise citations (they already cite the ambient context `Δ`), while outer
premise citations become node references.  Sharing inside every constituent
is preserved verbatim — a segment cited many times by the outer proof still
contributes its nodes exactly once — so composite node count is exactly
additive while the expanded tree multiplies cited subtrees.

The identifier-collision refuter and the sharing arithmetic live in
`ProofGSLTDAGSubstitutionCanary`; the exact expansion and acceptance
theorems below make the composite a checked artifact whose ghost expansion
is raw substitution of the constituent expansions.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- Rewire one child edge: a premise citation covered by `holeRoots` becomes
a reference to that root node; uncovered premise citations survive; node
references shift past the base segments. -/
def OpenDAGReference.wire (holeRoots : List Nat) (offset : Nat) :
    OpenDAGReference → OpenDAGReference
  | .premise index =>
      match holeRoots[index]? with
      | some root => .node root
      | none => .premise index
  | .node id => .node (id + offset)

@[simp] theorem OpenDAGReference.wire_premise (holeRoots : List Nat)
    (offset index : Nat) :
    OpenDAGReference.wire holeRoots offset (.premise index) =
      match holeRoots[index]? with
      | some root => .node root
      | none => .premise index := rfl

@[simp] theorem OpenDAGReference.wire_node (holeRoots : List Nat)
    (offset id : Nat) :
    OpenDAGReference.wire holeRoots offset (.node id) =
      .node (id + offset) := rfl

/-- Rewire one chronological node: shift its identifier and wire its
children. -/
def OpenDAGNode.wire (holeRoots : List Nat) (offset : Nat)
    (node : OpenDAGNode) : OpenDAGNode :=
  { id := node.id + offset
    ruleInstance := node.ruleInstance
    children := node.children.map (OpenDAGReference.wire holeRoots offset) }

/-- Rewire every node of every chronological block. -/
def wireDAGBlocks (holeRoots : List Nat) (offset : Nat)
    (blocks : List (List OpenDAGNode)) : List (List OpenDAGNode) :=
  blocks.map (fun block => block.map (OpenDAGNode.wire holeRoots offset))

/-- Strict upper bound on the node identifiers of a block list. -/
def dagNodesIdBound (nodes : List OpenDAGNode) : Nat :=
  nodes.foldr (fun node bound => max (node.id + 1) bound) 0

/-- Strict upper bound on the node identifiers of chronological blocks. -/
def dagBlocksIdBound (blocks : List (List OpenDAGNode)) : Nat :=
  blocks.foldr (fun block bound => max (dagNodesIdBound block) bound) 0

/-- Total submitted node count of chronological blocks. -/
def dagBlocksNodeCount (blocks : List (List OpenDAGNode)) : Nat :=
  blocks.flatten.length

/-- One checked environment DAG per ordered premise position, all over a
common ambient context. -/
inductive CheckedOpenDAGList (object : Object) (context : List Pattern) :
    List Pattern → Type where
  | nil : CheckedOpenDAGList object context []
  | cons {goal : Pattern} {goals : List Pattern}
      (head : CheckedOpenDAG object context goal)
      (tail : CheckedOpenDAGList object context goals) :
      CheckedOpenDAGList object context (goal :: goals)

namespace CheckedOpenDAGList

/-- Total submitted node count across an environment. -/
def nodeCount {object : Object} {context : List Pattern} :
    {goals : List Pattern} → CheckedOpenDAGList object context goals → Nat
  | _, .nil => 0
  | _, .cons head tail => dagBlocksNodeCount head.blocks + tail.nodeCount

/-- Lay the environment segments out chronologically from a starting
identifier offset.  Returns the shifted segment blocks, the shifted root of
each segment aligned with the premise positions, and the final offset past
every segment. -/
def layout {object : Object} {context : List Pattern} :
    {goals : List Pattern} → CheckedOpenDAGList object context goals →
      Nat → List (List OpenDAGNode) × List Nat × Nat
  | _, .nil, offset => ([], [], offset)
  | _, .cons head tail, offset =>
      let rest := tail.layout (offset + dagBlocksIdBound head.blocks)
      (wireDAGBlocks [] offset head.blocks ++ rest.1,
        (head.rootId + offset) :: rest.2.1, rest.2.2)

end CheckedOpenDAGList

/-- Composite chronological blocks and root: every environment segment laid
out once, then the outer DAG wired onto the segment roots. -/
def substituteDAGBlocks {object : Object} {outerContext : List Pattern}
    {goal : Pattern} {context : List Pattern}
    (dag : CheckedOpenDAG object outerContext goal)
    (environment : CheckedOpenDAGList object context outerContext) :
    List (List OpenDAGNode) × Nat :=
  let laid := environment.layout 0
  (laid.1 ++ wireDAGBlocks laid.2.1 laid.2.2 dag.blocks,
    dag.rootId + laid.2.2)

/-! ## Node-count accounting -/

theorem wireDAGBlocks_nodeCount (holeRoots : List Nat) (offset : Nat)
    (blocks : List (List OpenDAGNode)) :
    dagBlocksNodeCount (wireDAGBlocks holeRoots offset blocks) =
      dagBlocksNodeCount blocks := by
  unfold dagBlocksNodeCount wireDAGBlocks
  induction blocks with
  | nil => rfl
  | cons block blocks inductionHypothesis =>
      simp [inductionHypothesis]

theorem dagBlocksNodeCount_append (first second : List (List OpenDAGNode)) :
    dagBlocksNodeCount (first ++ second) =
      dagBlocksNodeCount first + dagBlocksNodeCount second := by
  simp [dagBlocksNodeCount]

theorem CheckedOpenDAGList.layout_nodeCount {object : Object}
    {context : List Pattern} :
    ∀ {goals : List Pattern}
      (environment : CheckedOpenDAGList object context goals) (offset : Nat),
      dagBlocksNodeCount (environment.layout offset).1 =
        environment.nodeCount := by
  intro goals environment
  induction environment with
  | nil => intro offset; rfl
  | cons head tail inductionHypothesis =>
      intro offset
      simp only [CheckedOpenDAGList.layout, CheckedOpenDAGList.nodeCount,
        dagBlocksNodeCount_append, wireDAGBlocks_nodeCount]
      rw [inductionHypothesis]

/-- Composite node count is exactly additive: sharing inside every
constituent is preserved, and no constituent is duplicated no matter how
often the outer proof cites its position. -/
theorem substituteDAGBlocks_nodeCount {object : Object}
    {outerContext : List Pattern} {goal : Pattern} {context : List Pattern}
    (dag : CheckedOpenDAG object outerContext goal)
    (environment : CheckedOpenDAGList object context outerContext) :
    dagBlocksNodeCount (substituteDAGBlocks dag environment).1 =
      dagBlocksNodeCount dag.blocks + environment.nodeCount := by
  unfold substituteDAGBlocks
  simp only [dagBlocksNodeCount_append, wireDAGBlocks_nodeCount,
    CheckedOpenDAGList.layout_nodeCount]
  omega

/-! ## Chronological-environment lookup lemmas -/

theorem findOpenDAGEntry?_id_mem {entries : List OpenDAGEntry} {id : Nat}
    {entry : OpenDAGEntry}
    (found : findOpenDAGEntry? entries id = some entry) :
    entry.id = id ∧ entry ∈ entries := by
  induction entries with
  | nil => simp [findOpenDAGEntry?] at found
  | cons head tail inductionHypothesis =>
      by_cases same : head.id = id
      · simp [findOpenDAGEntry?, same] at found
        subst entry
        exact ⟨same, List.mem_cons_self⟩
      · simp [findOpenDAGEntry?, same] at found
        rcases inductionHypothesis found with ⟨idEq, mem⟩
        exact ⟨idEq, List.mem_cons_of_mem head mem⟩

theorem findOpenDAGEntry?_append_left {entries rest : List OpenDAGEntry}
    {id : Nat} {entry : OpenDAGEntry}
    (found : findOpenDAGEntry? entries id = some entry) :
    findOpenDAGEntry? (entries ++ rest) id = some entry := by
  induction entries with
  | nil => simp [findOpenDAGEntry?] at found
  | cons head tail inductionHypothesis =>
      by_cases same : head.id = id
      · simp [findOpenDAGEntry?, same] at found ⊢
        exact found
      · simp only [List.cons_append, findOpenDAGEntry?, if_neg same] at found ⊢
        exact inductionHypothesis found

theorem findOpenDAGEntry?_append_none {entries rest : List OpenDAGEntry}
    {id : Nat}
    (leftNone : findOpenDAGEntry? entries id = none) :
    findOpenDAGEntry? (entries ++ rest) id =
      findOpenDAGEntry? rest id := by
  induction entries with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      by_cases same : head.id = id
      · simp [findOpenDAGEntry?, same] at leftNone
      · simp only [findOpenDAGEntry?, if_neg same] at leftNone
        simp only [List.cons_append, findOpenDAGEntry?, if_neg same]
        exact inductionHypothesis leftNone

theorem findOpenDAGEntry?_none_of_bounded {entries : List OpenDAGEntry}
    {id offset : Nat}
    (bounded : ∀ entry ∈ entries, entry.id < offset) (high : offset ≤ id) :
    findOpenDAGEntry? entries id = none := by
  induction entries with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have headLow : head.id < offset := bounded head List.mem_cons_self
      have notSame : ¬ head.id = id := by omega
      simp only [findOpenDAGEntry?, if_neg notSame]
      exact inductionHypothesis
        (fun entry mem => bounded entry (List.mem_cons_of_mem head mem))

theorem findOpenDAGEntry?_none_of_grounded {entries : List OpenDAGEntry}
    {id floor : Nat}
    (grounded : ∀ entry ∈ entries, floor ≤ entry.id) (low : id < floor) :
    findOpenDAGEntry? entries id = none := by
  induction entries with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have headHigh : floor ≤ head.id := grounded head List.mem_cons_self
      have notSame : ¬ head.id = id := by omega
      simp only [findOpenDAGEntry?, if_neg notSame]
      exact inductionHypothesis
        (fun entry mem => grounded entry (List.mem_cons_of_mem head mem))

private theorem option_some_bind {α β : Type _} (value : α)
    (continuation : α → Option β) :
    (some value >>= continuation) = continuation value := rfl

private theorem option_some_bindMethod {α β : Type _} (value : α)
    (continuation : α → Option β) :
    (some value).bind continuation = continuation value := rfl

/-! ## The composite view of one checked entry -/

/-- How one original checker entry appears inside the composite: identifier
shifted past the base, goal unchanged, ghost expansion substituted. -/
def OpenDAGEntry.transform (expansions : List RawOpenProof) (offset : Nat)
    (entry : OpenDAGEntry) : OpenDAGEntry :=
  { id := entry.id + offset
    goal := entry.goal
    proof := RawOpenProof.substitute expansions entry.proof }

theorem findOpenDAGEntry?_transform {entries : List OpenDAGEntry}
    (expansions : List RawOpenProof) (offset : Nat) (id : Nat) :
    findOpenDAGEntry?
        (entries.map (OpenDAGEntry.transform expansions offset))
        (id + offset) =
      (findOpenDAGEntry? entries id).map
        (OpenDAGEntry.transform expansions offset) := by
  induction entries with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      by_cases same : head.id = id
      · simp [findOpenDAGEntry?, OpenDAGEntry.transform, same]
      · have notSame : ¬ head.id + offset = id + offset := by omega
        simp only [List.map_cons, findOpenDAGEntry?,
          OpenDAGEntry.transform, if_neg notSame, if_neg same]
        exact inductionHypothesis

theorem findOpenDAGEntry?_transform_low {entries : List OpenDAGEntry}
    (expansions : List RawOpenProof) (offset : Nat) {id : Nat}
    (low : id < offset) :
    findOpenDAGEntry?
        (entries.map (OpenDAGEntry.transform expansions offset)) id =
      none := by
  induction entries with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have notSame : ¬ head.id + offset = id := by omega
      simp only [List.map_cons, findOpenDAGEntry?, OpenDAGEntry.transform,
        if_neg notSame]
      exact inductionHypothesis

/-! ## Identifier provenance and bounds -/

theorem dagNodesIdBound_lt {nodes : List OpenDAGNode} {node : OpenDAGNode}
    (mem : node ∈ nodes) : node.id < dagNodesIdBound nodes := by
  induction nodes with
  | nil => simp at mem
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp mem with equal | inTail
      · subst equal
        simp only [dagNodesIdBound, List.foldr_cons]
        omega
      · have tailBound := inductionHypothesis inTail
        simp only [dagNodesIdBound, List.foldr_cons]
        unfold dagNodesIdBound at tailBound
        omega

theorem dagBlocksIdBound_lt {blocks : List (List OpenDAGNode)}
    {node : OpenDAGNode} (mem : node ∈ blocks.flatten) :
    node.id < dagBlocksIdBound blocks := by
  induction blocks with
  | nil => simp at mem
  | cons block blocks inductionHypothesis =>
      simp only [List.flatten_cons, List.mem_append] at mem
      rcases mem with inBlock | inRest
      · have := dagNodesIdBound_lt inBlock
        simp only [dagBlocksIdBound, List.foldr_cons]
        omega
      · have := inductionHypothesis inRest
        simp only [dagBlocksIdBound, List.foldr_cons]
        unfold dagBlocksIdBound at this
        omega

theorem wireDAGBlocks_mem {holeRoots : List Nat} {offset : Nat}
    {blocks : List (List OpenDAGNode)} {node : OpenDAGNode}
    (mem : node ∈ (wireDAGBlocks holeRoots offset blocks).flatten) :
    ∃ original ∈ blocks.flatten, node.id = original.id + offset := by
  unfold wireDAGBlocks at mem
  rcases List.mem_flatten.mp mem with ⟨block, blockMem, nodeMem⟩
  rcases List.mem_map.mp blockMem with ⟨originalBlock, originalBlockMem, blockEq⟩
  subst blockEq
  rcases List.mem_map.mp nodeMem with ⟨original, originalMem, nodeEq⟩
  refine ⟨original, List.mem_flatten.mpr ⟨originalBlock, originalBlockMem,
    originalMem⟩, ?_⟩
  rw [← nodeEq]
  rfl

/-- Every entry produced by checking either was present initially or carries
the identifier of a submitted node. -/
theorem checkOpenDAGNodes?_entry_provenance
    {presentation : ValidatedPresentation} {context : List Pattern} :
    ∀ {entries : List OpenDAGEntry} {nodes : List OpenDAGNode}
      {next : List OpenDAGEntry},
      checkOpenDAGNodes? presentation context entries nodes = some next →
      ∀ entry ∈ next,
        entry ∈ entries ∨ ∃ node ∈ nodes, entry.id = node.id := by
  intro entries nodes
  induction nodes generalizing entries with
  | nil =>
      intro next checked entry mem
      simp [checkOpenDAGNodes?] at checked
      subst next
      exact Or.inl mem
  | cons node nodes inductionHypothesis =>
      intro next checked entry mem
      simp only [checkOpenDAGNodes?] at checked
      cases first : checkOpenDAGNode? presentation context entries node with
      | none => simp [first] at checked
      | some middle =>
          simp only [first] at checked
          rcases inductionHypothesis checked entry mem with inMiddle | fromRest
          · unfold checkOpenDAGNode? at first
            cases duplicate : findOpenDAGEntry? entries node.id with
            | some existing => simp [duplicate] at first
            | none =>
                simp only [duplicate] at first
                cases instantiated :
                    instantiateRule? presentation node.ruleInstance with
                | none => simp [instantiated] at first
                | some result =>
                    rcases result with ⟨premises, conclusion⟩
                    simp only [instantiated] at first
                    cases resolved : resolveOpenDAGChildren? context entries
                        premises node.children with
                    | none => simp [resolved] at first
                    | some children =>
                        simp only [resolved, Option.some.injEq] at first
                        subst middle
                        rcases List.mem_cons.mp inMiddle with equal | inEntries
                        · subst equal
                          exact Or.inr ⟨node, List.mem_cons_self, rfl⟩
                        · exact Or.inl inEntries
          · rcases fromRest with ⟨witness, witnessMem, idEq⟩
            exact Or.inr ⟨witness, List.mem_cons_of_mem node witnessMem, idEq⟩

theorem checkOpenDAGBlocks?_entry_provenance
    {presentation : ValidatedPresentation} {context : List Pattern} :
    ∀ {entries : List OpenDAGEntry} {blocks : List (List OpenDAGNode)}
      {next : List OpenDAGEntry},
      checkOpenDAGBlocks? presentation context entries blocks = some next →
      ∀ entry ∈ next,
        entry ∈ entries ∨ ∃ node ∈ blocks.flatten, entry.id = node.id := by
  intro entries blocks
  induction blocks generalizing entries with
  | nil =>
      intro next checked entry mem
      simp [checkOpenDAGBlocks?] at checked
      subst next
      exact Or.inl mem
  | cons block blocks inductionHypothesis =>
      intro next checked entry mem
      simp only [checkOpenDAGBlocks?] at checked
      cases first : checkOpenDAGNodes? presentation context entries block with
      | none => simp [first] at checked
      | some middle =>
          simp only [first] at checked
          rcases inductionHypothesis checked entry mem with inMiddle | fromRest
          · rcases checkOpenDAGNodes?_entry_provenance first entry inMiddle
              with inEntries | ⟨node, nodeMem, idEq⟩
            · exact Or.inl inEntries
            · exact Or.inr ⟨node, by
                simp only [List.flatten_cons, List.mem_append]
                exact Or.inl nodeMem, idEq⟩
          · rcases fromRest with ⟨node, nodeMem, idEq⟩
            exact Or.inr ⟨node, by
              simp only [List.flatten_cons, List.mem_append]
              exact Or.inr nodeMem, idEq⟩

/-! ## Extending the chronological base under fresh identifiers -/

theorem resolveOpenDAGReference?_extend
    {context : List Pattern} {entries base : List OpenDAGEntry}
    {expected : Pattern} {reference : OpenDAGReference}
    {proof : RawOpenProof}
    (resolved :
      resolveOpenDAGReference? context entries expected reference =
        some proof) :
    resolveOpenDAGReference? context (entries ++ base) expected reference =
      some proof := by
  cases reference with
  | premise index =>
      simpa [resolveOpenDAGReference?] using resolved
  | node id =>
      simp only [resolveOpenDAGReference?] at resolved ⊢
      cases found : findOpenDAGEntry? entries id with
      | none => simp [found] at resolved
      | some entry =>
          simp only [found] at resolved
          rw [findOpenDAGEntry?_append_left found]
          exact resolved

theorem resolveOpenDAGChildren?_extend
    {context : List Pattern} {entries base : List OpenDAGEntry} :
    ∀ {premises : List Pattern} {references : List OpenDAGReference}
      {proofs : List RawOpenProof},
      resolveOpenDAGChildren? context entries premises references =
          some proofs →
        resolveOpenDAGChildren? context (entries ++ base) premises
            references = some proofs := by
  intro premises
  induction premises with
  | nil =>
      intro references proofs resolved
      cases references with
      | nil => simpa [resolveOpenDAGChildren?] using resolved
      | cons reference references =>
          simp [resolveOpenDAGChildren?] at resolved
  | cons premise premises inductionHypothesis =>
      intro references proofs resolved
      cases references with
      | nil => simp [resolveOpenDAGChildren?] at resolved
      | cons reference references =>
          simp only [resolveOpenDAGChildren?] at resolved ⊢
          cases first : resolveOpenDAGReference? context entries premise
              reference with
          | none => simp [first] at resolved
          | some childProof =>
              simp only [first] at resolved
              cases rest : resolveOpenDAGChildren? context entries premises
                  references with
              | none => simp [rest] at resolved
              | some restProofs =>
                  simp only [rest] at resolved
                  rw [resolveOpenDAGReference?_extend first,
                    inductionHypothesis rest]
                  exact resolved

theorem checkOpenDAGNode?_extend_base
    {presentation : ValidatedPresentation} {context : List Pattern}
    {entries base : List OpenDAGEntry} {node : OpenDAGNode}
    {next : List OpenDAGEntry}
    (checked :
      checkOpenDAGNode? presentation context entries node = some next)
    (fresh : findOpenDAGEntry? base node.id = none) :
    checkOpenDAGNode? presentation context (entries ++ base) node =
      some (next ++ base) := by
  unfold checkOpenDAGNode? at checked ⊢
  cases duplicate : findOpenDAGEntry? entries node.id with
  | some existing => simp [duplicate] at checked
  | none =>
      simp only [duplicate] at checked
      rw [findOpenDAGEntry?_append_none duplicate, fresh]
      cases instantiated : instantiateRule? presentation node.ruleInstance with
      | none => simp [instantiated] at checked
      | some result =>
          rcases result with ⟨premises, conclusion⟩
          simp only [instantiated] at checked ⊢
          cases resolved : resolveOpenDAGChildren? context entries premises
              node.children with
          | none => simp [resolved] at checked
          | some children =>
              simp only [resolved, Option.some.injEq] at checked
              subst next
              rw [resolveOpenDAGChildren?_extend resolved]
              rfl

theorem checkOpenDAGNodes?_extend_base
    {presentation : ValidatedPresentation} {context : List Pattern}
    {base : List OpenDAGEntry} :
    ∀ {entries : List OpenDAGEntry} {nodes : List OpenDAGNode}
      {next : List OpenDAGEntry},
      checkOpenDAGNodes? presentation context entries nodes = some next →
      (∀ node ∈ nodes, findOpenDAGEntry? base node.id = none) →
      checkOpenDAGNodes? presentation context (entries ++ base) nodes =
        some (next ++ base) := by
  intro entries nodes
  induction nodes generalizing entries with
  | nil =>
      intro next checked _fresh
      simp [checkOpenDAGNodes?] at checked
      subst next
      rfl
  | cons node nodes inductionHypothesis =>
      intro next checked fresh
      simp only [checkOpenDAGNodes?] at checked ⊢
      cases first : checkOpenDAGNode? presentation context entries node with
      | none => simp [first] at checked
      | some middle =>
          simp only [first] at checked
          rw [checkOpenDAGNode?_extend_base first
            (fresh node List.mem_cons_self)]
          exact inductionHypothesis checked
            (fun witness mem => fresh witness (List.mem_cons_of_mem node mem))

theorem checkOpenDAGBlocks?_extend_base
    {presentation : ValidatedPresentation} {context : List Pattern}
    {base : List OpenDAGEntry} :
    ∀ {entries : List OpenDAGEntry} {blocks : List (List OpenDAGNode)}
      {next : List OpenDAGEntry},
      checkOpenDAGBlocks? presentation context entries blocks = some next →
      (∀ node ∈ blocks.flatten, findOpenDAGEntry? base node.id = none) →
      checkOpenDAGBlocks? presentation context (entries ++ base) blocks =
        some (next ++ base) := by
  intro entries blocks
  induction blocks generalizing entries with
  | nil =>
      intro next checked _fresh
      simp [checkOpenDAGBlocks?] at checked
      subst next
      rfl
  | cons block blocks inductionHypothesis =>
      intro next checked fresh
      simp only [checkOpenDAGBlocks?] at checked ⊢
      cases first : checkOpenDAGNodes? presentation context entries block with
      | none => simp [first] at checked
      | some middle =>
          simp only [first] at checked
          rw [checkOpenDAGNodes?_extend_base first
            (fun node mem => fresh node (by
              simp only [List.flatten_cons, List.mem_append]
              exact Or.inl mem))]
          exact inductionHypothesis checked
            (fun node mem => fresh node (by
              simp only [List.flatten_cons, List.mem_append]
              exact Or.inr mem))

/-! ## Replaying a checked DAG through wiring

The original DAG was checked in `originalContext`; the composite replays it
in `ambientContext` with premise citations wired onto base roots.  The four
hypotheses say exactly what the surrounding layout provides: covered
premise positions resolve in the base to the original judgment with the
substituted citation as ghost proof; uncovered positions agree between the
contexts; base identifiers sit strictly below the shift; and the expansion
environment covers exactly the wired positions. -/

section WireReplay

variable {presentation : ValidatedPresentation}
variable {originalContext ambientContext : List Pattern}
variable {holeRoots : List Nat} {expansions : List RawOpenProof}
variable {offset : Nat} {base : List OpenDAGEntry}

variable
  (rootsResolve : ∀ (index root : Nat) (goalPattern : Pattern),
    holeRoots[index]? = some root →
    originalContext[index]? = some goalPattern →
    findOpenDAGEntry? base root =
      some { id := root
             goal := goalPattern
             proof := expansions.getD index (.premise index) })
  (ambientAgrees : ∀ (index : Nat) (goalPattern : Pattern),
    holeRoots[index]? = none →
    originalContext[index]? = some goalPattern →
    ambientContext[index]? = some goalPattern)
  (baseBounded : ∀ entry ∈ base, entry.id < offset)
  (lengthsAligned : expansions.length = holeRoots.length)

include rootsResolve ambientAgrees baseBounded lengthsAligned

theorem resolveOpenDAGReference?_wire
    {entries : List OpenDAGEntry} {expected : Pattern}
    {reference : OpenDAGReference} {proof : RawOpenProof}
    (resolved :
      resolveOpenDAGReference? originalContext entries expected reference =
        some proof) :
    resolveOpenDAGReference? ambientContext
        (entries.map (OpenDAGEntry.transform expansions offset) ++ base)
        expected (reference.wire holeRoots offset) =
      some (RawOpenProof.substitute expansions proof) := by
  cases reference with
  | premise index =>
      simp only [resolveOpenDAGReference?] at resolved
      cases lookup : originalContext[index]? with
      | none => simp [lookup] at resolved
      | some actual =>
          simp only [lookup] at resolved
          by_cases same : actual = expected
          · simp only [same, if_true, Option.some.injEq] at resolved
            subst proof
            cases covered : holeRoots[index]? with
            | some root =>
                have found := rootsResolve index root actual covered lookup
                have rootLow : root < offset := by
                  rcases findOpenDAGEntry?_id_mem found with ⟨idEq, mem⟩
                  have := baseBounded _ mem
                  omega
                simp only [OpenDAGReference.wire, covered,
                  resolveOpenDAGReference?]
                rw [findOpenDAGEntry?_append_none
                  (findOpenDAGEntry?_transform_low expansions offset rootLow),
                  found]
                simp [same, RawOpenProof.substitute_premise]
            | none =>
                have outOfHoles : holeRoots.length ≤ index :=
                  List.getElem?_eq_none_iff.mp covered
                have outOfExpansions : expansions.length ≤ index := by
                  omega
                have expansionDefault :
                    expansions[index]?.getD (RawOpenProof.premise index) =
                      .premise index := by
                  rw [List.getElem?_eq_none outOfExpansions]
                  rfl
                simp only [OpenDAGReference.wire, covered,
                  resolveOpenDAGReference?]
                rw [ambientAgrees index actual covered lookup]
                simp [same, RawOpenProof.substitute_premise,
                  List.getD_eq_getElem?_getD, expansionDefault]
          · simp [same] at resolved
  | node id =>
      simp only [resolveOpenDAGReference?] at resolved
      cases found : findOpenDAGEntry? entries id with
      | none => simp [found] at resolved
      | some entry =>
          simp only [found] at resolved
          by_cases same : entry.goal = expected
          · simp only [same, if_true, Option.some.injEq] at resolved
            subst proof
            simp only [OpenDAGReference.wire, resolveOpenDAGReference?]
            rw [findOpenDAGEntry?_append_left (by
              rw [findOpenDAGEntry?_transform expansions offset id, found]
              rfl)]
            simp [OpenDAGEntry.transform, same]
          · simp [same] at resolved

theorem resolveOpenDAGChildren?_wire
    {entries : List OpenDAGEntry} :
    ∀ {premises : List Pattern} {references : List OpenDAGReference}
      {proofs : List RawOpenProof},
      resolveOpenDAGChildren? originalContext entries premises references =
          some proofs →
        resolveOpenDAGChildren? ambientContext
            (entries.map (OpenDAGEntry.transform expansions offset) ++ base)
            premises
            (references.map (OpenDAGReference.wire holeRoots offset)) =
          some (RawOpenProof.substituteList expansions proofs) := by
  intro premises
  induction premises with
  | nil =>
      intro references proofs resolved
      cases references with
      | nil =>
          simp [resolveOpenDAGChildren?] at resolved
          subst proofs
          simp [resolveOpenDAGChildren?]
      | cons reference references =>
          simp [resolveOpenDAGChildren?] at resolved
  | cons premise premises inductionHypothesis =>
      intro references proofs resolved
      cases references with
      | nil => simp [resolveOpenDAGChildren?] at resolved
      | cons reference references =>
          simp only [resolveOpenDAGChildren?] at resolved
          cases first : resolveOpenDAGReference? originalContext entries
              premise reference with
          | none => simp [first] at resolved
          | some childProof =>
              simp only [first] at resolved
              cases rest : resolveOpenDAGChildren? originalContext entries
                  premises references with
              | none => simp [rest] at resolved
              | some restProofs =>
                  simp only [rest] at resolved
                  simp at resolved
                  subst proofs
                  simp only [List.map_cons, resolveOpenDAGChildren?]
                  rw [resolveOpenDAGReference?_wire rootsResolve
                      ambientAgrees baseBounded lengthsAligned first,
                    inductionHypothesis rest]
                  rfl

theorem checkOpenDAGNode?_wire
    {entries next : List OpenDAGEntry} {node : OpenDAGNode}
    (checked :
      checkOpenDAGNode? presentation originalContext entries node =
        some next) :
    checkOpenDAGNode? presentation ambientContext
        (entries.map (OpenDAGEntry.transform expansions offset) ++ base)
        (node.wire holeRoots offset) =
      some (next.map (OpenDAGEntry.transform expansions offset) ++ base) := by
  unfold checkOpenDAGNode? at checked ⊢
  cases duplicate : findOpenDAGEntry? entries node.id with
  | some existing => simp [duplicate] at checked
  | none =>
      simp only [duplicate] at checked
      have wiredId : (node.wire holeRoots offset).id = node.id + offset := rfl
      rw [wiredId, findOpenDAGEntry?_append_none (by
          rw [findOpenDAGEntry?_transform expansions offset node.id,
            duplicate]
          rfl),
        findOpenDAGEntry?_none_of_bounded baseBounded (by omega)]
      have wiredInstance :
          (node.wire holeRoots offset).ruleInstance = node.ruleInstance := rfl
      rw [wiredInstance]
      cases instantiated : instantiateRule? presentation node.ruleInstance with
      | none => simp [instantiated] at checked
      | some result =>
          rcases result with ⟨premises, conclusion⟩
          simp only [instantiated] at checked ⊢
          cases resolved : resolveOpenDAGChildren? originalContext entries
              premises node.children with
          | none => simp [resolved] at checked
          | some children =>
              simp only [resolved, Option.some.injEq] at checked
              subst next
              have wiredChildren : (node.wire holeRoots offset).children =
                  node.children.map (OpenDAGReference.wire holeRoots offset) :=
                rfl
              rw [wiredChildren, resolveOpenDAGChildren?_wire rootsResolve
                ambientAgrees baseBounded lengthsAligned resolved]
              simp [OpenDAGEntry.transform, RawOpenProof.substitute_node]

theorem checkOpenDAGNodes?_wire :
    ∀ {entries : List OpenDAGEntry} {nodes : List OpenDAGNode}
      {next : List OpenDAGEntry},
      checkOpenDAGNodes? presentation originalContext entries nodes =
          some next →
        checkOpenDAGNodes? presentation ambientContext
            (entries.map (OpenDAGEntry.transform expansions offset) ++ base)
            (nodes.map (OpenDAGNode.wire holeRoots offset)) =
          some (next.map (OpenDAGEntry.transform expansions offset) ++
            base) := by
  intro entries nodes
  induction nodes generalizing entries with
  | nil =>
      intro next checked
      simp [checkOpenDAGNodes?] at checked
      subst next
      rfl
  | cons node nodes inductionHypothesis =>
      intro next checked
      simp only [checkOpenDAGNodes?] at checked
      cases first : checkOpenDAGNode? presentation originalContext entries
          node with
      | none => simp [first] at checked
      | some middle =>
          simp only [first] at checked
          simp only [List.map_cons, checkOpenDAGNodes?]
          rw [checkOpenDAGNode?_wire rootsResolve ambientAgrees baseBounded
            lengthsAligned first]
          exact inductionHypothesis checked

theorem checkOpenDAGBlocks?_wire :
    ∀ {entries : List OpenDAGEntry} {blocks : List (List OpenDAGNode)}
      {next : List OpenDAGEntry},
      checkOpenDAGBlocks? presentation originalContext entries blocks =
          some next →
        checkOpenDAGBlocks? presentation ambientContext
            (entries.map (OpenDAGEntry.transform expansions offset) ++ base)
            (wireDAGBlocks holeRoots offset blocks) =
          some (next.map (OpenDAGEntry.transform expansions offset) ++
            base) := by
  intro entries blocks
  induction blocks generalizing entries with
  | nil =>
      intro next checked
      simp [checkOpenDAGBlocks?] at checked
      subst next
      rfl
  | cons block blocks inductionHypothesis =>
      intro next checked
      simp only [checkOpenDAGBlocks?] at checked
      cases first : checkOpenDAGNodes? presentation originalContext entries
          block with
      | none => simp [first] at checked
      | some middle =>
          simp only [first] at checked
          simp only [wireDAGBlocks, List.map_cons, checkOpenDAGBlocks?]
          rw [show (block.map (OpenDAGNode.wire holeRoots offset)) =
              block.map (OpenDAGNode.wire holeRoots offset) from rfl,
            checkOpenDAGNodes?_wire rootsResolve ambientAgrees baseBounded
              lengthsAligned first]
          have folded : blocks.map
              (fun innerBlock =>
                innerBlock.map (OpenDAGNode.wire holeRoots offset)) =
              wireDAGBlocks holeRoots offset blocks := rfl
          rw [folded]
          exact inductionHypothesis checked

end WireReplay

/-- Chronological checking threads its entry state through appended block
lists. -/
theorem checkOpenDAGBlocks?_append
    {presentation : ValidatedPresentation} {context : List Pattern} :
    ∀ {first second : List (List OpenDAGNode)}
      {entries : List OpenDAGEntry},
      checkOpenDAGBlocks? presentation context entries (first ++ second) =
        (checkOpenDAGBlocks? presentation context entries first).bind
          (fun middle =>
            checkOpenDAGBlocks? presentation context middle second) := by
  intro first
  induction first with
  | nil => intro second entries; rfl
  | cons block blocks inductionHypothesis =>
      intro second entries
      simp only [List.cons_append, checkOpenDAGBlocks?]
      cases head : checkOpenDAGNodes? presentation context entries block with
      | none => rfl
      | some middle =>
          exact inductionHypothesis

/-! ## The ghost expansion of a checked artifact -/

namespace CheckedOpenDAG

/-- The unique raw open proof an accepted DAG expands to. -/
def expansion {object : Object} {context : List Pattern} {goal : Pattern}
    (dag : CheckedOpenDAG object context goal) : RawOpenProof :=
  (expandOpenDAGBlocks? object.presentation context goal dag.rootId
    dag.blocks).get (by simpa [checkOpenDAGBlocks] using dag.accepted)

theorem expand_eq {object : Object} {context : List Pattern} {goal : Pattern}
    (dag : CheckedOpenDAG object context goal) :
    expandOpenDAGBlocks? object.presentation context goal dag.rootId
        dag.blocks = some dag.expansion :=
  (Option.some_get _).symm

/-- Destructure acceptance into its chronological components: the checked
entry environment, and the root entry carrying the goal and the ghost
expansion. -/
theorem exists_check_root {object : Object} {context : List Pattern}
    {goal : Pattern} (dag : CheckedOpenDAG object context goal) :
    ∃ (entries : List OpenDAGEntry) (rootEntry : OpenDAGEntry),
      checkOpenDAGBlocks? object.presentation context [] dag.blocks =
        some entries ∧
      findOpenDAGEntry? entries dag.rootId = some rootEntry ∧
      rootEntry.id = dag.rootId ∧ rootEntry ∈ entries ∧
      rootEntry.goal = goal ∧ rootEntry.proof = dag.expansion := by
  have expandEq := dag.expand_eq
  unfold expandOpenDAGBlocks? at expandEq
  cases checked : checkOpenDAGBlocks? object.presentation context []
      dag.blocks with
  | none => simp [checked] at expandEq
  | some entries =>
      simp only [checked] at expandEq
      cases found : findOpenDAGEntry? entries dag.rootId with
      | none => simp [found] at expandEq
      | some rootEntry =>
          by_cases goalEq : rootEntry.goal = goal
          · simp [found, goalEq] at expandEq
            rcases findOpenDAGEntry?_id_mem found with ⟨idEq, memEq⟩
            exact ⟨entries, rootEntry, rfl, found, idEq, memEq, goalEq,
              expandEq⟩
          · simp [found, goalEq] at expandEq

end CheckedOpenDAG

namespace CheckedOpenDAGList

/-- The ordered ghost expansions of an environment. -/
def expansions {object : Object} {context : List Pattern} :
    {goals : List Pattern} → CheckedOpenDAGList object context goals →
      List RawOpenProof
  | _, .nil => []
  | _, .cons head tail => head.expansion :: tail.expansions

theorem expansions_length {object : Object} {context : List Pattern}
    {goals : List Pattern}
    (environment : CheckedOpenDAGList object context goals) :
    environment.expansions.length = goals.length := by
  induction environment with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [expansions, inductionHypothesis]

/-- The chronological layout of an environment checks from the empty state
and provides, for every premise position, a base entry at the shifted
segment root carrying the premise judgment and the segment's ghost
expansion.  All identifiers stay inside the layout's identifier window. -/
theorem layout_checks {object : Object} {ambient : List Pattern} :
    ∀ {goals : List Pattern}
      (environment : CheckedOpenDAGList object ambient goals) (offset : Nat),
      ∃ B : List OpenDAGEntry,
        checkOpenDAGBlocks? object.presentation ambient []
            (environment.layout offset).1 = some B ∧
        (∀ entry ∈ B,
          offset ≤ entry.id ∧ entry.id < (environment.layout offset).2.2) ∧
        (∀ node ∈ (environment.layout offset).1.flatten, offset ≤ node.id) ∧
        offset ≤ (environment.layout offset).2.2 ∧
        (environment.layout offset).2.1.length = goals.length ∧
        (∀ (index root : Nat),
          (environment.layout offset).2.1[index]? = some root →
          root < (environment.layout offset).2.2 ∧
          ∃ (goalPattern : Pattern) (expansionProof : RawOpenProof),
            goals[index]? = some goalPattern ∧
            environment.expansions[index]? = some expansionProof ∧
            findOpenDAGEntry? B root =
              some { id := root, goal := goalPattern,
                     proof := expansionProof }) := by
  intro goals environment
  induction environment with
  | nil =>
      intro offset
      refine ⟨[], rfl, by simp, by simp [CheckedOpenDAGList.layout],
        by simp [CheckedOpenDAGList.layout], rfl, ?_⟩
      intro index root found
      simp [CheckedOpenDAGList.layout] at found
  | @cons headGoal tailGoals head tail inductionHypothesis =>
      intro offset
      obtain ⟨entriesH, rootH, checkedH, foundH, idH, memH, goalH, proofH⟩ :=
        head.exists_check_root
      have headWired :=
        checkOpenDAGBlocks?_wire (holeRoots := ([] : List Nat))
          (expansions := ([] : List RawOpenProof)) (offset := offset)
          (base := ([] : List OpenDAGEntry))
          (ambientContext := ambient)
          (fun index root goalPattern covered _ => by simp at covered)
          (fun index goalPattern _ lookup => lookup)
          (fun entry mem => by simp at mem)
          rfl checkedH
      simp only [List.map_nil, List.append_nil] at headWired
      have headEntryBounds : ∀ entry ∈ entriesH.map
          (OpenDAGEntry.transform [] offset),
          offset ≤ entry.id ∧
            entry.id < offset + dagBlocksIdBound head.blocks := by
        intro entry mem
        rcases List.mem_map.mp mem with ⟨original, originalMem, entryEq⟩
        subst entryEq
        rcases checkOpenDAGBlocks?_entry_provenance checkedH original
            originalMem with inEmpty | ⟨node, nodeMem, idEq⟩
        · simp at inEmpty
        · have := dagBlocksIdBound_lt nodeMem
          simp only [OpenDAGEntry.transform]
          omega
      obtain ⟨Bt, checkedT, entryBoundsT, nodeBoundsT, offsetLeT, lengthT,
          rootsT⟩ :=
        inductionHypothesis (offset + dagBlocksIdBound head.blocks)
      have tailExtended := checkOpenDAGBlocks?_extend_base
        (base := entriesH.map (OpenDAGEntry.transform [] offset))
        checkedT
        (fun node mem =>
          findOpenDAGEntry?_none_of_bounded
            (fun entry entryMem => (headEntryBounds entry entryMem).2)
            (nodeBoundsT node mem))
      simp only [List.nil_append] at tailExtended
      refine ⟨Bt ++ entriesH.map (OpenDAGEntry.transform [] offset), ?_, ?_,
        ?_, ?_, ?_, ?_⟩
      · simp only [CheckedOpenDAGList.layout]
        rw [checkOpenDAGBlocks?_append, headWired]
        simpa using tailExtended
      · intro entry mem
        simp only [CheckedOpenDAGList.layout]
        rcases List.mem_append.mp mem with inTail | inHead
        · have := entryBoundsT entry inTail
          omega
        · have := headEntryBounds entry inHead
          have leT := offsetLeT
          omega
      · intro node mem
        simp only [CheckedOpenDAGList.layout] at mem ⊢
        rw [List.flatten_append] at mem
        rcases List.mem_append.mp mem with inHead | inTail
        · rcases wireDAGBlocks_mem inHead with ⟨original, _, idEq⟩
          omega
        · have := nodeBoundsT node inTail
          omega
      · simp only [CheckedOpenDAGList.layout]
        omega
      · simp only [CheckedOpenDAGList.layout, List.length_cons, lengthT]
      · intro index root found
        simp only [CheckedOpenDAGList.layout] at found ⊢
        cases index with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst found
            have rootIdBound : head.rootId < dagBlocksIdBound head.blocks := by
              rcases checkOpenDAGBlocks?_entry_provenance checkedH rootH memH
                  with inEmpty | ⟨node, nodeMem, idEq⟩
              · simp at inEmpty
              · have := dagBlocksIdBound_lt nodeMem
                omega
            have rootLt : head.rootId + offset <
                (tail.layout (offset + dagBlocksIdBound head.blocks)).2.2 := by
              omega
            refine ⟨rootLt, headGoal, head.expansion, rfl, rfl, ?_⟩
            have foundShifted := findOpenDAGEntry?_transform
              ([] : List RawOpenProof) offset head.rootId
              (entries := entriesH)
            rw [foundH] at foundShifted
            simp only [Option.map] at foundShifted
            rw [findOpenDAGEntry?_append_none
              (findOpenDAGEntry?_none_of_grounded
                (fun entry entryMem => (entryBoundsT entry entryMem).1)
                (by omega)),
              foundShifted]
            simp only [Option.some.injEq, OpenDAGEntry.transform]
            rw [idH, goalH, proofH, RawOpenProof.substitute_nil]
        | succ tailIndex =>
            simp only [List.getElem?_cons_succ] at found
            obtain ⟨rootBound, goalPattern, expansionProof, goalFound,
                expansionFound, entryFound⟩ := rootsT tailIndex root found
            refine ⟨rootBound, goalPattern, expansionProof, ?_, ?_, ?_⟩
            · simpa using goalFound
            · simp only [CheckedOpenDAGList.expansions,
                List.getElem?_cons_succ]
              exact expansionFound
            · exact findOpenDAGEntry?_append_left entryFound

end CheckedOpenDAGList

/-! ## The composite is a checked artifact with the substituted expansion -/

theorem substituteDAGBlocks_expands {object : Object}
    {outerContext : List Pattern} {goal : Pattern} {context : List Pattern}
    (dag : CheckedOpenDAG object outerContext goal)
    (environment : CheckedOpenDAGList object context outerContext) :
    expandOpenDAGBlocks? object.presentation context goal
        (substituteDAGBlocks dag environment).2
        (substituteDAGBlocks dag environment).1 =
      some (RawOpenProof.substitute environment.expansions dag.expansion) := by
  obtain ⟨entriesD, rootD, checkedD, foundD, idD, memD, goalD, proofD⟩ :=
    dag.exists_check_root
  obtain ⟨B, checkedB, entryBounds, _nodeBounds, _offsetLe, rootsLength,
      rootsFacts⟩ := environment.layout_checks 0
  have wired := checkOpenDAGBlocks?_wire
    (holeRoots := (environment.layout 0).2.1)
    (expansions := environment.expansions)
    (offset := (environment.layout 0).2.2)
    (base := B) (ambientContext := context)
    (fun index root goalPattern covered lookup => by
      obtain ⟨_rootBound, goalPattern', expansionProof, goalFound,
          expansionFound, entryFound⟩ := rootsFacts index root covered
      have goalSame : goalPattern' = goalPattern := by
        rw [lookup] at goalFound
        exact (Option.some.inj goalFound).symm
      have getDSame :
          environment.expansions.getD index (.premise index) =
            expansionProof := by
        rw [List.getD_eq_getElem?_getD, expansionFound]
        rfl
      rw [getDSame, ← goalSame]
      exact entryFound)
    (fun index goalPattern uncovered lookup => by
      have short : (environment.layout 0).2.1.length ≤ index :=
        List.getElem?_eq_none_iff.mp uncovered
      have inRange : index < outerContext.length :=
        (List.getElem?_eq_some_iff.mp lookup).1
      omega)
    (fun entry mem => (entryBounds entry mem).2)
    (by rw [environment.expansions_length, ← rootsLength])
    checkedD
  simp only [List.map_nil, List.nil_append] at wired
  have foundShifted := findOpenDAGEntry?_transform environment.expansions
    (environment.layout 0).2.2 dag.rootId (entries := entriesD)
  rw [foundD] at foundShifted
  simp only [Option.map] at foundShifted
  dsimp only [substituteDAGBlocks]
  unfold expandOpenDAGBlocks?
  rw [checkOpenDAGBlocks?_append, checkedB, option_some_bindMethod, wired,
    option_some_bind, findOpenDAGEntry?_append_left foundShifted,
    option_some_bind]
  simp only [OpenDAGEntry.transform, goalD, if_true, Option.some.injEq]
  rw [proofD]

/-- The composite artifact is accepted. -/
theorem substituteDAGBlocks_accepts {object : Object}
    {outerContext : List Pattern} {goal : Pattern} {context : List Pattern}
    (dag : CheckedOpenDAG object outerContext goal)
    (environment : CheckedOpenDAGList object context outerContext) :
    checkOpenDAGBlocks object.presentation context goal
        (substituteDAGBlocks dag environment).2
        (substituteDAGBlocks dag environment).1 = true := by
  unfold checkOpenDAGBlocks
  rw [substituteDAGBlocks_expands dag environment]
  rfl

/-- Sharing-preserving substitution of checked chronological artifacts. -/
def CheckedOpenDAG.substitute {object : Object}
    {outerContext : List Pattern} {goal : Pattern} {context : List Pattern}
    (dag : CheckedOpenDAG object outerContext goal)
    (environment : CheckedOpenDAGList object context outerContext) :
    CheckedOpenDAG object context goal :=
  { rootId := (substituteDAGBlocks dag environment).2
    blocks := (substituteDAGBlocks dag environment).1
    accepted := substituteDAGBlocks_accepts dag environment }

/-- Expansion is a homomorphism from artifact substitution to raw
substitution: composing compact evidence substitutes its ghost proofs. -/
@[simp] theorem CheckedOpenDAG.substitute_expansion {object : Object}
    {outerContext : List Pattern} {goal : Pattern} {context : List Pattern}
    (dag : CheckedOpenDAG object outerContext goal)
    (environment : CheckedOpenDAGList object context outerContext) :
    (dag.substitute environment).expansion =
      RawOpenProof.substitute environment.expansions dag.expansion := by
  have fromDef := (dag.substitute environment).expand_eq
  have fromTheorem := substituteDAGBlocks_expands dag environment
  have same : some (dag.substitute environment).expansion =
      some (RawOpenProof.substitute environment.expansions dag.expansion) := by
    rw [← fromDef]
    exact fromTheorem
  exact Option.some.injEq _ _ ▸ same

/-- Artifact substitution presents clone substitution: whenever the
constituents erase typed open derivations, the composite's expansion is the
erasure of the plugged derivation. -/
theorem CheckedOpenDAG.substitute_erases_bind {object : Object}
    {outerContext : List Pattern} {goal : Pattern} {context : List Pattern}
    (dag : CheckedOpenDAG object outerContext goal)
    (environment : CheckedOpenDAGList object context outerContext)
    {derivation : OpenDerivation object.presentation outerContext goal}
    (dagErases : derivation.eraseOpen = dag.expansion)
    {typedEnvironment :
      OpenDerivationList object.presentation context outerContext}
    (environmentErases :
      typedEnvironment.eraseOpen = environment.expansions) :
    (dag.substitute environment).expansion =
      (derivation.bind typedEnvironment).eraseOpen := by
  rw [CheckedOpenDAG.substitute_expansion,
    OpenDerivation.eraseOpen_bind, dagErases, environmentErases]

/-- Expanded-tree cost of a composite: the outer tree plus one copy of each
segment expansion per citation — while the submitted composite artifact
grows only additively (`substituteDAGBlocks_nodeCount`). -/
theorem CheckedOpenDAG.substitute_expansion_ruleCount {object : Object}
    {outerContext : List Pattern} {goal : Pattern} {context : List Pattern}
    (dag : CheckedOpenDAG object outerContext goal)
    (environment : CheckedOpenDAGList object context outerContext) :
    (dag.substitute environment).expansion.ruleCount =
      dag.expansion.ruleCount +
        RawOpenProof.citationWeight environment.expansions dag.expansion := by
  rw [CheckedOpenDAG.substitute_expansion,
    RawOpenProof.substitute_ruleCount]

end Mettapedia.GSLT.LanguageDef.ProofGSLT
