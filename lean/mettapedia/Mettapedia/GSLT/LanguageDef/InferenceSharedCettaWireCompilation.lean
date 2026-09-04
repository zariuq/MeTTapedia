import Mettapedia.GSLT.LanguageDef.InferenceSharedCettaWireFormat

/-!
# Verified structural compilation into the shared CeTTa wire carrier

The version-two physical article checker accepts chronological pattern tables
and proof nodes.  The hash-consing producers are useful untrusted optimizers,
but exact authority lowering also needs one total producer with a proved
materialization theorem.

This module begins with a deliberately simple structural compiler.  It emits
each pattern occurrence in postorder, so every child identifier is already in
scope when its parent is materialized.  It does not claim deduplication;
sharing is a subsequent optimization validated by the same consumer.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.InferenceSharedCettaWireCompilation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferencePatternSharing
open Mettapedia.GSLT.LanguageDef.InferenceSharedCettaWire

/-- Result of structurally appending one pattern tree to an existing table. -/
structure PatternBuild where
  nodes : List SharedPatternNode
  rootId : Nat
  nextId : Nat
  table : Array Pattern
deriving Repr

/-- Result of structurally appending an ordered vector of pattern trees. -/
structure PatternListBuild where
  nodes : List SharedPatternNode
  rootIds : List Nat
  nextId : Nat
  table : Array Pattern
deriving Repr

mutual

/-- Append one pattern in postorder, starting at `nextId`. -/
def buildPattern : Pattern → Nat → Array Pattern → PatternBuild
  | pattern@(.bvar index), nextId, table =>
      { nodes := [⟨nextId, .bvar index⟩]
        rootId := nextId
        nextId := nextId + 1
        table := table.push pattern }
  | pattern@(.fvar name), nextId, table =>
      { nodes := [⟨nextId, .fvar name⟩]
        rootId := nextId
        nextId := nextId + 1
        table := table.push pattern }
  | pattern@(.apply head arguments), nextId, table =>
      let children := buildPatterns arguments nextId table
      { nodes := children.nodes ++
          [⟨children.nextId, .apply head children.rootIds⟩]
        rootId := children.nextId
        nextId := children.nextId + 1
        table := children.table.push pattern }
  | pattern@(.lambda binder body), nextId, table =>
      let child := buildPattern body nextId table
      { nodes := child.nodes ++
          [⟨child.nextId, .lambda binder child.rootId⟩]
        rootId := child.nextId
        nextId := child.nextId + 1
        table := child.table.push pattern }
  | pattern@(.multiLambda arity binders body), nextId, table =>
      let child := buildPattern body nextId table
      { nodes := child.nodes ++
          [⟨child.nextId, .multiLambda arity binders child.rootId⟩]
        rootId := child.nextId
        nextId := child.nextId + 1
        table := child.table.push pattern }
  | pattern@(.subst body replacement), nextId, table =>
      let bodyBuild := buildPattern body nextId table
      let replacementBuild :=
        buildPattern replacement bodyBuild.nextId bodyBuild.table
      { nodes := bodyBuild.nodes ++ replacementBuild.nodes ++
          [⟨replacementBuild.nextId,
            .subst bodyBuild.rootId replacementBuild.rootId⟩]
        rootId := replacementBuild.nextId
        nextId := replacementBuild.nextId + 1
        table := replacementBuild.table.push pattern }
  | pattern@(.collection collectionType elements rest), nextId, table =>
      let children := buildPatterns elements nextId table
      { nodes := children.nodes ++
          [⟨children.nextId,
            .collection collectionType children.rootIds rest⟩]
        rootId := children.nextId
        nextId := children.nextId + 1
        table := children.table.push pattern }
termination_by pattern => 2 * sizeOf pattern
decreasing_by all_goals simp_wf <;> omega

/-- Append an ordered pattern vector from left to right. -/
def buildPatterns : List Pattern → Nat → Array Pattern → PatternListBuild
  | [], nextId, table =>
      { nodes := []
        rootIds := []
        nextId
        table }
  | pattern :: patterns, nextId, table =>
      let head := buildPattern pattern nextId table
      let tail := buildPatterns patterns head.nextId head.table
      { nodes := head.nodes ++ tail.nodes
        rootIds := head.rootId :: tail.rootIds
        nextId := tail.nextId
        table := tail.table }
termination_by patterns => 2 * sizeOf patterns + 1

end

/-- Materialization over concatenated node vectors is sequential
materialization. -/
theorem materializePatternNodesLoop_append
    (left right : List SharedPatternNode) (nextId : Nat)
    (table : Array Pattern) :
    materializePatternNodesLoop (left ++ right) nextId table =
      match materializePatternNodesLoop left nextId table with
      | none => none
      | some after =>
          materializePatternNodesLoop right (nextId + left.length) after := by
  induction left generalizing nextId table with
  | nil => simp [materializePatternNodesLoop]
  | cons node nodes inductionHypothesis =>
      by_cases idMatches : node.id = nextId
      · cases keyResult : materializePatternNodeKey? table node.key with
        | none =>
            simp [materializePatternNodesLoop, idMatches, keyResult]
        | some pattern =>
            have nextIndexEquality :
                nextId + 1 + nodes.length =
                  nextId + (node :: nodes).length := by
              simp only [List.length_cons]
              omega
            simp [materializePatternNodesLoop, idMatches, keyResult,
              inductionHypothesis, nextIndexEquality]
      · simp [materializePatternNodesLoop, idMatches]

/-! ## Structural compiler invariants -/

/-- Exact invariants retained by one compiled pattern tree. -/
structure PatternBuildCorrect (pattern : Pattern) (startId : Nat)
    (initialTable : Array Pattern) (result : PatternBuild) : Prop where
  materializes :
    materializePatternNodesLoop result.nodes startId initialTable =
      some result.table
  nextId_eq : result.nextId = startId + result.nodes.length
  table_size_eq : result.table.size = result.nextId
  preservesPrefix : ∀ id, id < initialTable.size →
    result.table[id]? = initialTable[id]?
  root_lt : result.rootId < result.table.size
  root_eq : result.table[result.rootId]? = some pattern

/-- Exact invariants retained by an ordered vector of compiled patterns. -/
structure PatternListBuildCorrect (patterns : List Pattern) (startId : Nat)
    (initialTable : Array Pattern) (result : PatternListBuild) : Prop where
  materializes :
    materializePatternNodesLoop result.nodes startId initialTable =
      some result.table
  nextId_eq : result.nextId = startId + result.nodes.length
  table_size_eq : result.table.size = result.nextId
  preservesPrefix : ∀ id, id < initialTable.size →
    result.table[id]? = initialTable[id]?
  roots_lt : ∀ id, id ∈ result.rootIds → id < result.table.size
  roots_eq : resolvePatternIds result.table result.rootIds = some patterns

private theorem buildPattern_bvar_correct (index startId : Nat)
    (initialTable : Array Pattern)
    (initialSize : initialTable.size = startId) :
    PatternBuildCorrect (.bvar index) startId initialTable
      (buildPattern (.bvar index) startId initialTable) := by
  refine
    { materializes := ?_
      nextId_eq := ?_
      table_size_eq := ?_
      preservesPrefix := ?_
      root_lt := ?_
      root_eq := ?_ }
  · simp [buildPattern, materializePatternNodesLoop,
      materializePatternNodeKey?]
  · simp [buildPattern]
  · simp [buildPattern, initialSize]
  · intro id idLt
    have idNe : id ≠ initialTable.size := Nat.ne_of_lt idLt
    simp [buildPattern, Array.getElem?_push, idNe]
  · simp [buildPattern, initialSize]
  · rw [← initialSize]
    simp [buildPattern]

private theorem buildPattern_fvar_correct (name : String) (startId : Nat)
    (initialTable : Array Pattern)
    (initialSize : initialTable.size = startId) :
    PatternBuildCorrect (.fvar name) startId initialTable
      (buildPattern (.fvar name) startId initialTable) := by
  refine
    { materializes := ?_
      nextId_eq := ?_
      table_size_eq := ?_
      preservesPrefix := ?_
      root_lt := ?_
      root_eq := ?_ }
  · simp [buildPattern, materializePatternNodesLoop,
      materializePatternNodeKey?]
  · simp [buildPattern]
  · simp [buildPattern, initialSize]
  · intro id idLt
    have idNe : id ≠ initialTable.size := Nat.ne_of_lt idLt
    simp [buildPattern, Array.getElem?_push, idNe]
  · simp [buildPattern, initialSize]
  · rw [← initialSize]
    simp [buildPattern]

/-- Appending a materializable node to a correct prefix preserves every
compiler invariant. -/
private theorem appendPatternNode_correct
    (pattern : Pattern) (key : PatternNodeKey)
    (startId nextId : Nat) (initialTable middleTable : Array Pattern)
    (prefixNodes : List SharedPatternNode)
    (initialSize : initialTable.size = startId)
    (prefixMaterializes :
      materializePatternNodesLoop prefixNodes startId initialTable =
        some middleTable)
    (prefixNext : nextId = startId + prefixNodes.length)
    (middleSize : middleTable.size = nextId)
    (prefixPreserves : ∀ id, id < initialTable.size →
      middleTable[id]? = initialTable[id]?)
    (keyMaterializes :
      materializePatternNodeKey? middleTable key = some pattern) :
    PatternBuildCorrect pattern startId initialTable
      { nodes := prefixNodes ++ [⟨nextId, key⟩]
        rootId := nextId
        nextId := nextId + 1
        table := middleTable.push pattern } := by
  refine
    { materializes := ?_
      nextId_eq := ?_
      table_size_eq := ?_
      preservesPrefix := ?_
      root_lt := ?_
      root_eq := ?_ }
  · rw [materializePatternNodesLoop_append, prefixMaterializes]
    rw [← prefixNext]
    simp [materializePatternNodesLoop, keyMaterializes]
  · simp only [List.length_append, List.length_singleton]
    omega
  · simp [middleSize]
  · intro id idLt
    have idLtMiddle : id < middleTable.size := by
      rw [middleSize, prefixNext, ← initialSize]
      omega
    have idNe : id ≠ middleTable.size := Nat.ne_of_lt idLtMiddle
    simpa [Array.getElem?_push, idNe] using prefixPreserves id idLt
  · simp [middleSize]
  · rw [← middleSize]
    simp

mutual

/-- Structural pattern compilation is an exact section of materialization. -/
theorem buildPattern_correct (pattern : Pattern) (startId : Nat)
    (initialTable : Array Pattern)
    (initialSize : initialTable.size = startId) :
    PatternBuildCorrect pattern startId initialTable
      (buildPattern pattern startId initialTable) := by
  cases pattern with
  | bvar index =>
      exact buildPattern_bvar_correct index startId initialTable initialSize
  | fvar name =>
      exact buildPattern_fvar_correct name startId initialTable initialSize
  | apply head arguments =>
      let children := buildPatterns arguments startId initialTable
      have childrenCorrect :
          PatternListBuildCorrect arguments startId initialTable children :=
        buildPatterns_correct arguments startId initialTable initialSize
      have keyMaterializes :
          materializePatternNodeKey? children.table
              (.apply head children.rootIds) =
            some (.apply head arguments) := by
        simp [materializePatternNodeKey?, childrenCorrect.roots_eq]
      simpa [buildPattern, children] using
        appendPatternNode_correct (.apply head arguments)
          (.apply head children.rootIds) startId children.nextId
          initialTable children.table children.nodes initialSize
          childrenCorrect.materializes childrenCorrect.nextId_eq
          childrenCorrect.table_size_eq childrenCorrect.preservesPrefix
          keyMaterializes
  | lambda binder body =>
      let child := buildPattern body startId initialTable
      have childCorrect :
          PatternBuildCorrect body startId initialTable child :=
        buildPattern_correct body startId initialTable initialSize
      have keyMaterializes :
          materializePatternNodeKey? child.table
              (.lambda binder child.rootId) =
            some (.lambda binder body) := by
        simp [materializePatternNodeKey?, childCorrect.root_eq]
      simpa [buildPattern, child] using
        appendPatternNode_correct (.lambda binder body)
          (.lambda binder child.rootId) startId child.nextId
          initialTable child.table child.nodes initialSize
          childCorrect.materializes childCorrect.nextId_eq
          childCorrect.table_size_eq childCorrect.preservesPrefix
          keyMaterializes
  | multiLambda arity binders body =>
      let child := buildPattern body startId initialTable
      have childCorrect :
          PatternBuildCorrect body startId initialTable child :=
        buildPattern_correct body startId initialTable initialSize
      have keyMaterializes :
          materializePatternNodeKey? child.table
              (.multiLambda arity binders child.rootId) =
            some (.multiLambda arity binders body) := by
        simp [materializePatternNodeKey?, childCorrect.root_eq]
      simpa [buildPattern, child] using
        appendPatternNode_correct (.multiLambda arity binders body)
          (.multiLambda arity binders child.rootId)
          startId child.nextId initialTable child.table child.nodes initialSize
          childCorrect.materializes childCorrect.nextId_eq
          childCorrect.table_size_eq childCorrect.preservesPrefix
          keyMaterializes
  | subst body replacement =>
      let bodyBuild := buildPattern body startId initialTable
      have bodyCorrect :
          PatternBuildCorrect body startId initialTable bodyBuild :=
        buildPattern_correct body startId initialTable initialSize
      let replacementBuild :=
        buildPattern replacement bodyBuild.nextId bodyBuild.table
      have replacementCorrect :
          PatternBuildCorrect replacement bodyBuild.nextId bodyBuild.table
            replacementBuild :=
        buildPattern_correct replacement bodyBuild.nextId bodyBuild.table
          bodyCorrect.table_size_eq
      have prefixMaterializes :
          materializePatternNodesLoop
              (bodyBuild.nodes ++ replacementBuild.nodes)
              startId initialTable =
            some replacementBuild.table := by
        rw [materializePatternNodesLoop_append, bodyCorrect.materializes]
        rw [← bodyCorrect.nextId_eq]
        exact replacementCorrect.materializes
      have prefixNext :
          replacementBuild.nextId =
            startId +
              (bodyBuild.nodes ++ replacementBuild.nodes).length := by
        rw [List.length_append, replacementCorrect.nextId_eq,
          bodyCorrect.nextId_eq]
        omega
      have prefixPreserves : ∀ id, id < initialTable.size →
          replacementBuild.table[id]? = initialTable[id]? := by
        intro id idLt
        rw [replacementCorrect.preservesPrefix id]
        · exact bodyCorrect.preservesPrefix id idLt
        · rw [bodyCorrect.table_size_eq, bodyCorrect.nextId_eq,
            ← initialSize]
          omega
      have bodyRootInReplacement :
          replacementBuild.table[bodyBuild.rootId]? = some body := by
        rw [replacementCorrect.preservesPrefix bodyBuild.rootId
          bodyCorrect.root_lt]
        exact bodyCorrect.root_eq
      have keyMaterializes :
          materializePatternNodeKey? replacementBuild.table
              (.subst bodyBuild.rootId replacementBuild.rootId) =
            some (.subst body replacement) := by
        simp [materializePatternNodeKey?, bodyRootInReplacement,
          replacementCorrect.root_eq]
      simpa [buildPattern, bodyBuild, replacementBuild] using
        appendPatternNode_correct (.subst body replacement)
          (.subst bodyBuild.rootId replacementBuild.rootId)
          startId replacementBuild.nextId initialTable
          replacementBuild.table
          (bodyBuild.nodes ++ replacementBuild.nodes) initialSize
          prefixMaterializes prefixNext replacementCorrect.table_size_eq
          prefixPreserves keyMaterializes
  | collection collectionType elements rest =>
      let children := buildPatterns elements startId initialTable
      have childrenCorrect :
          PatternListBuildCorrect elements startId initialTable children :=
        buildPatterns_correct elements startId initialTable initialSize
      have keyMaterializes :
          materializePatternNodeKey? children.table
              (.collection collectionType children.rootIds rest) =
            some (.collection collectionType elements rest) := by
        simp [materializePatternNodeKey?, childrenCorrect.roots_eq]
      simpa [buildPattern, children] using
        appendPatternNode_correct (.collection collectionType elements rest)
          (.collection collectionType children.rootIds rest)
          startId children.nextId initialTable children.table children.nodes
          initialSize childrenCorrect.materializes childrenCorrect.nextId_eq
          childrenCorrect.table_size_eq childrenCorrect.preservesPrefix
          keyMaterializes
termination_by 2 * sizeOf pattern
decreasing_by all_goals simp_wf <;> omega

/-- Ordered structural pattern compilation preserves order and exact lookup
of every emitted root. -/
theorem buildPatterns_correct (patterns : List Pattern) (startId : Nat)
    (initialTable : Array Pattern)
    (initialSize : initialTable.size = startId) :
    PatternListBuildCorrect patterns startId initialTable
      (buildPatterns patterns startId initialTable) := by
  cases patterns with
  | nil =>
      refine
        { materializes := ?_
          nextId_eq := ?_
          table_size_eq := ?_
          preservesPrefix := ?_
          roots_lt := ?_
          roots_eq := ?_ }
      · simp [buildPatterns, materializePatternNodesLoop]
      · simp [buildPatterns]
      · simpa [buildPatterns] using initialSize
      · intro id _idLt
        simp [buildPatterns]
      · simp [buildPatterns]
      · simp [buildPatterns, resolvePatternIds]
  | cons pattern patterns =>
      let head := buildPattern pattern startId initialTable
      have headCorrect :
          PatternBuildCorrect pattern startId initialTable head :=
        buildPattern_correct pattern startId initialTable initialSize
      let tail := buildPatterns patterns head.nextId head.table
      have tailCorrect :
          PatternListBuildCorrect patterns head.nextId head.table tail :=
        buildPatterns_correct patterns head.nextId head.table
          headCorrect.table_size_eq
      have materializes :
          materializePatternNodesLoop (head.nodes ++ tail.nodes)
              startId initialTable =
            some tail.table := by
        rw [materializePatternNodesLoop_append, headCorrect.materializes]
        rw [← headCorrect.nextId_eq]
        exact tailCorrect.materializes
      have nextIdEquality :
          tail.nextId = startId + (head.nodes ++ tail.nodes).length := by
        rw [List.length_append, tailCorrect.nextId_eq,
          headCorrect.nextId_eq]
        omega
      have preservesPrefix : ∀ id, id < initialTable.size →
          tail.table[id]? = initialTable[id]? := by
        intro id idLt
        rw [tailCorrect.preservesPrefix id]
        · exact headCorrect.preservesPrefix id idLt
        · rw [headCorrect.table_size_eq, headCorrect.nextId_eq,
            ← initialSize]
          omega
      have headRootInTail :
          tail.table[head.rootId]? = some pattern := by
        rw [tailCorrect.preservesPrefix head.rootId headCorrect.root_lt]
        exact headCorrect.root_eq
      refine
        { materializes := by
            simpa [buildPatterns, head, tail] using materializes
          nextId_eq := by
            simpa [buildPatterns, head, tail] using nextIdEquality
          table_size_eq := by
            simpa [buildPatterns, head, tail] using tailCorrect.table_size_eq
          preservesPrefix := by
            simpa [buildPatterns, head, tail] using preservesPrefix
          roots_lt := ?_
          roots_eq := ?_ }
      · have rootsBound : ∀ id, id ∈ head.rootId :: tail.rootIds →
            id < tail.table.size := by
          intro id member
          simp only [List.mem_cons] at member
          rcases member with rfl | tailMember
          · have rootBeforeNext : head.rootId < head.nextId := by
              rw [← headCorrect.table_size_eq]
              exact headCorrect.root_lt
            rw [tailCorrect.table_size_eq, tailCorrect.nextId_eq]
            omega
          · exact tailCorrect.roots_lt id tailMember
        simpa [buildPatterns, head, tail] using rootsBound
      simp [buildPatterns, head, tail, resolvePatternIds, headRootInTail,
        tailCorrect.roots_eq]
termination_by 2 * sizeOf patterns + 1

end

/-! ## Chronological proof-node compilation -/

/-- Resolving a fixed identifier vector depends only on the table entries at
those identifiers. -/
theorem resolvePatternIds_congr (left right : Array Pattern)
    (ids : List Nat)
    (agree : ∀ id, id ∈ ids → right[id]? = left[id]?) :
    resolvePatternIds right ids = resolvePatternIds left ids := by
  induction ids with
  | nil => rfl
  | cons id ids inductionHypothesis =>
      have headAgree : right[id]? = left[id]? := agree id (by simp)
      have tailAgree : ∀ tailId, tailId ∈ ids →
          right[tailId]? = left[tailId]? := by
        intro tailId member
        exact agree tailId (by simp [member])
      simp only [resolvePatternIds]
      rw [headAgree, inductionHypothesis tailAgree]

/-- The shared physical proof-node carrier has no premise-reference variant.
This total projection therefore normalizes every reference to a chronological
node reference. -/
def normalizeReference : OpenDAGReference → OpenDAGReference
  | .premise id => .node id
  | .node id => .node id

def referenceId : OpenDAGReference → Nat
  | .premise id => id
  | .node id => id

@[simp] theorem node_reference_of_referenceId (reference : OpenDAGReference) :
    OpenDAGReference.node (referenceId reference) =
      normalizeReference reference := by
  cases reference <;> rfl

/-- Normalization performed by the shared proof-node carrier.  Canonical
closed derivations are fixed points of this operation. -/
def normalizeOpenDAGNode (node : OpenDAGNode) : OpenDAGNode :=
  { node with children := node.children.map normalizeReference }

/-- Structural compilation result for an ordered chronological node vector. -/
structure DAGNodesBuild where
  patternNodes : List SharedPatternNode
  nodes : List ReferencedDAGNode
  nextPatternId : Nat
  table : Array Pattern
deriving Repr

/-- Compile rule arguments into the pattern table and replace their full
syntax by identifiers.  Proof-node identifiers and order are unchanged. -/
def buildDAGNodes :
    List OpenDAGNode → Nat → Array Pattern → DAGNodesBuild
  | [], nextPatternId, table =>
      { patternNodes := []
        nodes := []
        nextPatternId
        table }
  | node :: nodes, nextPatternId, table =>
      let arguments :=
        buildPatterns node.ruleInstance.arguments nextPatternId table
      let referenced : ReferencedDAGNode :=
        { id := node.id
          ruleId := node.ruleInstance.ruleId
          argumentIds := arguments.rootIds
          children := node.children.map referenceId }
      let tail := buildDAGNodes nodes arguments.nextId arguments.table
      { patternNodes := arguments.nodes ++ tail.patternNodes
        nodes := referenced :: tail.nodes
        nextPatternId := tail.nextPatternId
        table := tail.table }

/-- Exact invariants of structural chronological-node compilation. -/
structure DAGNodesBuildCorrect (source : List OpenDAGNode)
    (startId : Nat) (initialTable : Array Pattern)
    (result : DAGNodesBuild) : Prop where
  patternsMaterialize :
    materializePatternNodesLoop result.patternNodes startId initialTable =
      some result.table
  nextId_eq :
    result.nextPatternId = startId + result.patternNodes.length
  table_size_eq : result.table.size = result.nextPatternId
  preservesPrefix : ∀ id, id < initialTable.size →
    result.table[id]? = initialTable[id]?
  nodesMaterialize :
    materializeReferencedDAGNodes? result.table result.nodes =
      some (source.map normalizeOpenDAGNode)

/-- Structural chronological-node compilation is exact up to the explicit
premise-to-node normalization of the target carrier. -/
theorem buildDAGNodes_correct (source : List OpenDAGNode)
    (startId : Nat) (initialTable : Array Pattern)
    (initialSize : initialTable.size = startId) :
    DAGNodesBuildCorrect source startId initialTable
      (buildDAGNodes source startId initialTable) := by
  induction source generalizing startId initialTable with
  | nil =>
      refine
        { patternsMaterialize := ?_
          nextId_eq := ?_
          table_size_eq := ?_
          preservesPrefix := ?_
          nodesMaterialize := ?_ }
      · simp [buildDAGNodes, materializePatternNodesLoop]
      · simp [buildDAGNodes]
      · simpa [buildDAGNodes] using initialSize
      · intro id _idLt
        simp [buildDAGNodes]
      · simp [buildDAGNodes, materializeReferencedDAGNodes?]
  | cons node nodes inductionHypothesis =>
      let arguments :=
        buildPatterns node.ruleInstance.arguments startId initialTable
      have argumentsCorrect :
          PatternListBuildCorrect node.ruleInstance.arguments startId
            initialTable arguments :=
        buildPatterns_correct node.ruleInstance.arguments startId
          initialTable initialSize
      let referenced : ReferencedDAGNode :=
        { id := node.id
          ruleId := node.ruleInstance.ruleId
          argumentIds := arguments.rootIds
          children := node.children.map referenceId }
      let tail := buildDAGNodes nodes arguments.nextId arguments.table
      have tailCorrect :
          DAGNodesBuildCorrect nodes arguments.nextId arguments.table tail :=
        inductionHypothesis arguments.nextId arguments.table
          argumentsCorrect.table_size_eq
      have patternsMaterialize :
          materializePatternNodesLoop
              (arguments.nodes ++ tail.patternNodes)
              startId initialTable =
            some tail.table := by
        rw [materializePatternNodesLoop_append,
          argumentsCorrect.materializes]
        rw [← argumentsCorrect.nextId_eq]
        exact tailCorrect.patternsMaterialize
      have nextIdEquality :
          tail.nextPatternId =
            startId + (arguments.nodes ++ tail.patternNodes).length := by
        rw [List.length_append, tailCorrect.nextId_eq,
          argumentsCorrect.nextId_eq]
        omega
      have preservesPrefix : ∀ id, id < initialTable.size →
          tail.table[id]? = initialTable[id]? := by
        intro id idLt
        rw [tailCorrect.preservesPrefix id]
        · exact argumentsCorrect.preservesPrefix id idLt
        · rw [argumentsCorrect.table_size_eq,
            argumentsCorrect.nextId_eq, ← initialSize]
          omega
      have argumentResolution :
          resolvePatternIds tail.table arguments.rootIds =
            some node.ruleInstance.arguments := by
        rw [resolvePatternIds_congr arguments.table tail.table
          arguments.rootIds]
        · exact argumentsCorrect.roots_eq
        · intro id member
          exact tailCorrect.preservesPrefix id
            (argumentsCorrect.roots_lt id member)
      have headMaterializes :
          materializeReferencedDAGNode? tail.table referenced =
            some (normalizeOpenDAGNode node) := by
        cases node with
        | mk id ruleInstance children =>
          cases ruleInstance with
          | mk ruleId ruleArguments =>
            simp [referenced, materializeReferencedDAGNode?,
              argumentResolution, normalizeOpenDAGNode, List.map_map,
              Function.comp_def]
      refine
        { patternsMaterialize := by
            simpa [buildDAGNodes, arguments, referenced, tail] using
              patternsMaterialize
          nextId_eq := by
            simpa [buildDAGNodes, arguments, referenced, tail] using
              nextIdEquality
          table_size_eq := by
            simpa [buildDAGNodes, arguments, referenced, tail] using
              tailCorrect.table_size_eq
          preservesPrefix := by
            simpa [buildDAGNodes, arguments, referenced, tail] using
              preservesPrefix
          nodesMaterialize := ?_ }
      simp [buildDAGNodes, arguments, referenced, tail,
        materializeReferencedDAGNodes?, headMaterializes,
        tailCorrect.nodesMaterialize]

/-! ## Canonical closed articles -/

@[simp] theorem normalizeOpenDAGNode_of_node_children
    (id : Nat) (ruleInstance : RuleInstance) (children : List Nat) :
    normalizeOpenDAGNode
        { id
          ruleInstance
          children := children.map OpenDAGReference.node } =
      { id
        ruleInstance
        children := children.map OpenDAGReference.node } := by
  simp [normalizeOpenDAGNode, normalizeReference, List.map_map,
    Function.comp_def]

mutual

/-- Every node emitted by closed-derivation linearization already lies in the
node-reference-only image of the shared carrier. -/
theorem derivation_linearize_normalized
    {definition : ValidatedCalculusLanguageDef} {goal : Pattern}
    (derivation : Derivation definition goal) (nextId : Nat) :
    (Derivation.linearize derivation nextId).1.map normalizeOpenDAGNode =
      (Derivation.linearize derivation nextId).1 := by
  cases derivation with
  | byRule ruleInstance premises children =>
      simp [Derivation.linearize,
        derivationList_linearize_normalized children nextId]
termination_by sizeOf derivation
decreasing_by all_goals simp_wf

/-- Ordered vectors of closed derivations emit only node references. -/
theorem derivationList_linearize_normalized
    {definition : ValidatedCalculusLanguageDef} {goals : List Pattern}
    (derivations : DerivationList definition goals) (nextId : Nat) :
    (DerivationList.linearize derivations nextId).1.map
        normalizeOpenDAGNode =
      (DerivationList.linearize derivations nextId).1 := by
  cases derivations with
  | nil => simp [DerivationList.linearize]
  | cons head tail =>
      simp [DerivationList.linearize,
        derivation_linearize_normalized head nextId,
        derivationList_linearize_normalized tail
          (Derivation.linearize head nextId).2.2]
termination_by sizeOf derivations

end

/-! ## Exact shared article construction -/

/-- Total structural compiler into the version-two shared physical article.
The compiler preserves proof-node and root identifiers.  Its only
normalization is the shared carrier's explicit premise-to-node projection;
canonical closed derivations are fixed points by
`derivation_linearize_normalized`. -/
def buildSharedWireArticle (article : WireArticle) : SharedWireArticle :=
  let target := buildPattern article.target 0 #[]
  let proof :=
    buildDAGNodes article.nodes target.nextId target.table
  { version := sharedArticleVersion
    patterns := target.nodes ++ proof.patternNodes
    nodes := proof.nodes
    rootId := article.rootId
    targetId := target.rootId }

/-- A version-one logical article that is already in the node-reference-only
image is recovered exactly after structural shared compilation and
materialization. -/
theorem materialize_buildSharedWireArticle
    (article : WireArticle)
    (versionCorrect : article.version = wireArticleVersion)
    (nodeReferencesCanonical :
      article.nodes.map normalizeOpenDAGNode = article.nodes) :
    materializeSharedArticle? (buildSharedWireArticle article) =
      some article := by
  let target := buildPattern article.target 0 #[]
  have targetCorrect :
      PatternBuildCorrect article.target 0 #[] target :=
    buildPattern_correct article.target 0 #[] rfl
  let proof :=
    buildDAGNodes article.nodes target.nextId target.table
  have proofCorrect :
      DAGNodesBuildCorrect article.nodes target.nextId target.table proof :=
    buildDAGNodes_correct article.nodes target.nextId target.table
      targetCorrect.table_size_eq
  have patternsMaterialize :
      materializePatternNodesLoop
          (target.nodes ++ proof.patternNodes) 0 #[] =
        some proof.table := by
    rw [materializePatternNodesLoop_append,
      targetCorrect.materializes]
    rw [← targetCorrect.nextId_eq]
    exact proofCorrect.patternsMaterialize
  have targetRootInProof :
      proof.table[target.rootId]? = some article.target := by
    rw [proofCorrect.preservesPrefix target.rootId targetCorrect.root_lt]
    exact targetCorrect.root_eq
  simp [buildSharedWireArticle, proof, target, materializeSharedArticle?,
    materializePatternNodes, sharedArticleVersion, patternsMaterialize,
    targetRootInProof, proofCorrect.nodesMaterialize,
    nodeReferencesCanonical]
  cases article
  simp_all

/-- Canonical articles produced from typed closed derivations are exact fixed
points of shared compilation followed by materialization. -/
theorem materialize_buildSharedWireArticle_of_derivation
    {definition : ValidatedCalculusLanguageDef} {goal : Pattern}
    (derivation : Derivation definition goal) :
    materializeSharedArticle?
        (buildSharedWireArticle (articleOfDerivation derivation)) =
      some (articleOfDerivation derivation) := by
  apply materialize_buildSharedWireArticle
  · rfl
  · exact derivation_linearize_normalized derivation 0

#print axioms materializePatternNodesLoop_append
#print axioms buildPattern_correct
#print axioms buildPatterns_correct
#print axioms buildDAGNodes_correct
#print axioms derivation_linearize_normalized
#print axioms derivationList_linearize_normalized
#print axioms materialize_buildSharedWireArticle
#print axioms materialize_buildSharedWireArticle_of_derivation

end Mettapedia.GSLT.LanguageDef.InferenceSharedCettaWireCompilation
