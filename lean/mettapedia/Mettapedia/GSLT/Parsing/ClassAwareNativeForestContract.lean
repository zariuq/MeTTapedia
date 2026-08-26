import Mettapedia.GSLT.Parsing.ClassAwarePackedForest

/-!
# Contract for a native binary packed forest

Native generalized parsers commonly expose a binary shared packed parse
forest: symbol and intermediate nodes own choices, while every choice points
to an optional prefix and one child.  This module gives that public shape an
implementation-independent meaning and relates its finite evidence to the
flattened class-aware forest.

The view below is not a semantics for a parser backend.  A native backend must
separately show that its exported arrays satisfy `Represents`.  In particular,
matching summaries or digests do not establish this contract.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract

open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ClassAwarePackedForest
open Mettapedia.GSLT.Parsing.ParserProfileSemantics

/-- Terminal payload retained by a neutral native forest. -/
inductive TerminalValue where
  | scalar (codepoint : Nat)
  | eof
  | witness (identity : Nat)
  deriving DecidableEq, Repr

/-- The four node classes of a binary shared packed parse forest. -/
inductive NodeKind where
  | terminal (terminalId : Nat) (value : TerminalValue)
  | epsilon
  | symbol (symbolId : Nat)
  | intermediate (production : Nat) (dot : Nat)
  deriving DecidableEq, Repr

/-- One exported node.  Choice ranges use ordinary natural indices rather
than a distinguished machine-word sentinel. -/
structure Node where
  kind : NodeKind
  scalarStart : Nat
  scalarStop : Nat
  byteStart : Nat
  byteStop : Nat
  choiceBegin : Nat
  choiceCount : Nat
  deriving DecidableEq, Repr

/-- One binary packed choice. -/
structure Choice where
  parent : Nat
  prefixNode : Option Nat
  childNode : Nat
  productionIndex : Nat
  scalarPivot : Nat
  bytePivot : Nat
  deriving DecidableEq, Repr

/-- Finite public forest data relevant to semantic correspondence.  Runtime
work counters and failure diagnostics belong to a separate receipt. -/
structure ForestView where
  nodes : List Node
  choices : List Choice
  roots : List Nat
  codepoints : List Nat
  byteOffsets : List Nat
  deriving DecidableEq, Repr

/-- Semantic identity tables retained outside disposable dense native IDs. -/
structure IdentityTable where
  symbolSort? : Nat → Option String
  terminalMatcher? : Nat → Option TerminalMatcher
  productionRef? : Nat → Option ProductionRef

/-- Scalar and byte spans agree with the immutable source offset table. -/
def NodeSpanCoherent (view : ForestView) (node : Node) : Prop :=
  node.scalarStart ≤ node.scalarStop ∧
    view.byteOffsets[node.scalarStart]? = some node.byteStart ∧
    view.byteOffsets[node.scalarStop]? = some node.byteStop

/-- Lookup of one coherent node by its disposable native index. -/
def NodeAt (view : ForestView) (index : Nat) (node : Node) : Prop :=
  view.nodes[index]? = some node ∧ NodeSpanCoherent view node

/-- A choice is in the contiguous range owned by its declared parent. -/
def OwnedChoice (view : ForestView) (parentIndex : Nat)
    (choice : Choice) : Prop :=
  ∃ parent localIndex,
    view.nodes[parentIndex]? = some parent ∧
    localIndex < parent.choiceCount ∧
    view.choices[parent.choiceBegin + localIndex]? = some choice ∧
    choice.parent = parentIndex

/-- One choice-array occurrence is owned at that exact array position. -/
def ChoiceAtOwned (view : ForestView) (choiceIndex : Nat)
    (choice : Choice) : Prop :=
  ∃ parent localIndex,
    view.nodes[choice.parent]? = some parent ∧
    localIndex < parent.choiceCount ∧
    choiceIndex = parent.choiceBegin + localIndex ∧
    view.choices[choiceIndex]? = some choice

/-- Bounds and ownership of the finite public arrays, before semantic identity
tables are consulted. -/
structure ForestArraysCoherent (view : ForestView) : Prop where
  nodesCoherent : ∀ (index : Nat) (node : Node),
    view.nodes[index]? = some node →
      NodeSpanCoherent view node ∧
        node.choiceBegin + node.choiceCount ≤ view.choices.length
  choicesOwned : ∀ (index : Nat) (choice : Choice),
    view.choices[index]? = some choice → ChoiceAtOwned view index choice
  rootsValid : ∀ (index : Nat), index ∈ view.roots →
    ∃ node, NodeAt view index node

/-- The pivot stored in a binary choice is the left boundary of its child. -/
def PivotCoherent (view : ForestView) (choice : Choice) : Prop :=
  ∃ childNode,
    NodeAt view choice.childNode childNode ∧
    choice.scalarPivot = childNode.scalarStart ∧
    choice.bytePivot = childNode.byteStart

/-- Binary factorization covers the parent's whole span.  A missing prefix
starts at the parent boundary; a present prefix covers exactly the interval
from the parent boundary to the pivot; the child covers pivot to parent end. -/
def FactorizationCoherent (view : ForestView) (choice : Choice) : Prop :=
  ∃ parentNode childNode,
    NodeAt view choice.parent parentNode ∧
    NodeAt view choice.childNode childNode ∧
    choice.scalarPivot = childNode.scalarStart ∧
    choice.bytePivot = childNode.byteStart ∧
    childNode.scalarStop = parentNode.scalarStop ∧
    childNode.byteStop = parentNode.byteStop ∧
    match choice.prefixNode with
    | none =>
        choice.scalarPivot = parentNode.scalarStart ∧
          choice.bytePivot = parentNode.byteStart
    | some prefixIndex =>
        ∃ prefixNode,
          NodeAt view prefixIndex prefixNode ∧
          prefixNode.scalarStart = parentNode.scalarStart ∧
          prefixNode.byteStart = parentNode.byteStart ∧
          prefixNode.scalarStop = choice.scalarPivot ∧
          prefixNode.byteStop = choice.bytePivot

set_option autoImplicit true in
/-- A scalar or EOF terminal payload agrees with the immutable scalar input.
Opaque witness terminals deliberately have no constructor here: the current
class-aware ParserPack semantics has no external-witness judgment. -/
inductive TerminalValueAgrees (input : List Nat) :
    TerminalValue → Nat → Nat → Type where
  | scalar
      (lookup : input[start]? = some codepoint) :
      TerminalValueAgrees input (.scalar codepoint) start (start + 1)
  | eof
      (atEnd : cursor = input.length) :
      TerminalValueAgrees input .eof cursor cursor

set_option autoImplicit true in
/-- Decode one native child node to zero or one flattened family children.
Intermediate nodes are intentionally absent: they are decoded only as binary
prefixes by `PrefixDerivation`. -/
inductive ChildDerivation (view : ForestView) (table : IdentityTable)
    (profile : ParserProfileLayer) (input : List Nat) :
    Nat → List ChildRef → Type where
  | terminal
      (nodeAt : NodeAt view nodeIndex {
        kind := .terminal terminalId value
        scalarStart := start
        scalarStop := stop
        byteStart := byteStart
        byteStop := byteStop
        choiceBegin := choiceBegin
        choiceCount := 0 })
      (matcherAt : table.terminalMatcher? terminalId = some matcher)
      (valueAgrees : TerminalValueAgrees input value start stop)
      (terminalMatch : TerminalMatchesAt profile input matcher start stop) :
      ChildDerivation view table profile input nodeIndex
        [.terminal matcher start stop]
  | epsilon
      (nodeAt : NodeAt view nodeIndex {
        kind := .epsilon
        scalarStart := cursor
        scalarStop := cursor
        byteStart := byteCursor
        byteStop := byteCursor
        choiceBegin := choiceBegin
        choiceCount := 0 }) :
      ChildDerivation view table profile input nodeIndex []
  | symbol
      (nodeAt : NodeAt view nodeIndex {
        kind := .symbol symbolId
        scalarStart := start
        scalarStop := stop
        byteStart := byteStart
        byteStop := byteStop
        choiceBegin := choiceBegin
        choiceCount := choiceCount })
      (sortAt : table.symbolSort? symbolId = some resultSort) :
      ChildDerivation view table profile input nodeIndex
        [.node ⟨resultSort, start, stop⟩]

set_option autoImplicit true in
mutual
  /-- Decode an optional intermediate prefix for one physical production. -/
  inductive PrefixDerivation (view : ForestView) (table : IdentityTable)
      (profile : ParserProfileLayer) (input : List Nat) (production : Nat) :
      Option Nat → List ChildRef → Type where
    | empty : PrefixDerivation view table profile input production none []
    | intermediate
        (nodeAt : NodeAt view nodeIndex {
          kind := .intermediate production dot
          scalarStart := start
          scalarStop := stop
          byteStart := byteStart
          byteStop := byteStop
          choiceBegin := choiceBegin
          choiceCount := choiceCount })
        (owned : OwnedChoice view nodeIndex choice)
        (body : ChoiceChildren view table profile input production
          choice children) :
        PrefixDerivation view table profile input production
          (some nodeIndex) children

  /-- Decode one binary choice to the ordered flattened sequence obtained by
  decoding its prefix first and its child second. -/
  inductive ChoiceChildren (view : ForestView) (table : IdentityTable)
      (profile : ParserProfileLayer) (input : List Nat) (production : Nat) :
      Choice → List ChildRef → Type where
    | binary
        (productionExact : choice.productionIndex = production)
        (pivot : PivotCoherent view choice)
        (factorization : FactorizationCoherent view choice)
        (prefixResult : PrefixDerivation view table profile input production
          choice.prefixNode prefixChildren)
        (childResult : ChildDerivation view table profile input
          choice.childNode childChildren) :
        ChoiceChildren view table profile input production choice
          (prefixChildren ++ childChildren)
end

set_option autoImplicit true in
/-- One symbol-node choice decodes to one exact flattened family. -/
inductive FamilyDerivation (view : ForestView) (table : IdentityTable)
    (profile : ParserProfileLayer) (input : List Nat) :
    Nat → Choice → Family → Type where
  | symbol
      (parentAt : NodeAt view parentIndex {
        kind := .symbol symbolId
        scalarStart := start
        scalarStop := stop
        byteStart := byteStart
        byteStop := byteStop
        choiceBegin := choiceBegin
        choiceCount := choiceCount })
      (owned : OwnedChoice view parentIndex choice)
      (sortAt : table.symbolSort? symbolId = some resultSort)
      (productionAt : table.productionRef? choice.productionIndex =
        some productionRef)
      (body : ChoiceChildren view table profile input choice.productionIndex
        choice children) :
      FamilyDerivation view table profile input parentIndex choice {
        parent := ⟨resultSort, start, stop⟩
        production := productionRef
        children := children }

/-- One exported root maps to one exact shared symbol key. -/
def RootKeyAt (view : ForestView) (table : IdentityTable)
    (key : NodeKey) : Prop :=
  ∃ rootIndex symbolId byteStart byteStop choiceBegin choiceCount,
    rootIndex ∈ view.roots ∧
    NodeAt view rootIndex {
      kind := .symbol symbolId
      scalarStart := key.start
      scalarStop := key.stop
      byteStart := byteStart
      byteStop := byteStop
      choiceBegin := choiceBegin
      choiceCount := choiceCount } ∧
    table.symbolSort? symbolId = some key.resultSort

/-- Every owned choice must have a finite semantic decoding.  This condition
rejects choices on leaves, bad pivots and production identities, and cyclic
prefix choices that have no finite unfolding. -/
def ChoiceCovered (view : ForestView) (table : IdentityTable)
    (profile : ParserProfileLayer) (input : List Nat)
    (parentIndex : Nat) (parent : Node) (choice : Choice) : Prop :=
  match parent.kind with
  | .symbol _ =>
      ∃ family, Nonempty
        (FamilyDerivation view table profile input parentIndex choice family)
  | .intermediate production _ =>
      ∃ children, Nonempty
        (ChoiceChildren view table profile input production choice children)
  | .terminal _ _ | .epsilon => False

set_option autoImplicit true in
/-- Graph reachability from an exported root through owned prefix and child
references.  Cycles are permitted as graph structure; finite semantic
unfolding is enforced separately by `ChoiceCovered`. -/
inductive Reachable (view : ForestView) : Nat → Prop where
  | root (member : nodeIndex ∈ view.roots) : Reachable view nodeIndex
  | prefix
      (parent : Reachable view parentIndex)
      (owned : OwnedChoice view parentIndex choice)
      (prefixExact : choice.prefixNode = some prefixIndex) :
      Reachable view prefixIndex
  | child
      (parent : Reachable view parentIndex)
      (owned : OwnedChoice view parentIndex choice) :
      Reachable view choice.childNode

/-- Exact representation contract between a native binary forest view and a
flattened class-aware forest. -/
structure Represents (view : ForestView) (table : IdentityTable)
    (profile : ParserProfileLayer) (input : List Nat)
    (target : ClassAwarePackedForest.Forest) : Prop where
  arraysCoherent : ForestArraysCoherent view
  rootsExact : ∀ key,
    key ∈ target.roots ↔ RootKeyAt view table key
  rootsCovered : ∀ rootIndex, rootIndex ∈ view.roots →
    ∃ key, RootKeyAt view table key
  familiesExact : ∀ family,
    family ∈ target.families ↔
      ∃ parentIndex choice,
        Nonempty (FamilyDerivation view table profile input
          parentIndex choice family)
  choicesCovered : ∀ parentIndex parent choice,
    NodeAt view parentIndex parent →
    OwnedChoice view parentIndex choice →
    ChoiceCovered view table profile input parentIndex parent choice
  nodesReachable : ∀ index node,
    view.nodes[index]? = some node → Reachable view index

theorem Represents.root_iff
    {view : ForestView} {table : IdentityTable}
    {profile : ParserProfileLayer} {input : List Nat}
    {target : ClassAwarePackedForest.Forest}
    (represents : Represents view table profile input target)
    (key : NodeKey) :
    key ∈ target.roots ↔ RootKeyAt view table key :=
  represents.rootsExact key

theorem Represents.family_iff
    {view : ForestView} {table : IdentityTable}
    {profile : ParserProfileLayer} {input : List Nat}
    {target : ClassAwarePackedForest.Forest}
    (represents : Represents view table profile input target)
    (family : Family) :
    family ∈ target.families ↔
      ∃ parentIndex choice,
        Nonempty (FamilyDerivation view table profile input
          parentIndex choice family) :=
  represents.familiesExact family

/-- A certificate unfolds directly through the native binary representation:
its root has a native symbol node and every selected flattened family has a
finite binary derivation. -/
def NativeRootUnfolds (view : ForestView) (table : IdentityTable)
    (profile : ParserProfileLayer) (input : List Nat)
    (resultSort : String) (certificate :
      Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate.Certificate) :
    Prop :=
  RootKeyAt view table (certificateKey resultSort certificate) ∧
    ∀ family, family ∈ certificateFamilies resultSort certificate →
      ∃ parentIndex choice,
        Nonempty (FamilyDerivation view table profile input
          parentIndex choice family)

/-- An exact representation turns flattened forest unfolding into native
binary unfolding in both directions. -/
theorem Represents.rootUnfolds_iff_native
    {view : ForestView} {table : IdentityTable}
    {profile : ParserProfileLayer} {input : List Nat}
    {target : ClassAwarePackedForest.Forest}
    (represents : Represents view table profile input target)
    (resultSort : String)
    (certificate :
      Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate.Certificate) :
    RootUnfolds target resultSort certificate ↔
      NativeRootUnfolds view table profile input resultSort certificate := by
  constructor
  · rintro ⟨root, families⟩
    constructor
    · exact (represents.rootsExact _).mp root
    · intro family member
      exact (represents.familiesExact family).mp (families family member)
  · rintro ⟨root, families⟩
    constructor
    · exact (represents.rootsExact _).mpr root
    · intro family member
      exact (represents.familiesExact family).mpr (families family member)

/-- Native binary membership plus exact semantic certificate replay. -/
def NativePackedReplays (view : ForestView) (table : IdentityTable)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat)
    (certificate :
      Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate.Certificate)
    (resultSort : String) (start stop : Nat)
    (tree : Mettapedia.GSLT.Parsing.PresentationExprSemantics.CST) : Type :=
  PLift (NativeRootUnfolds view table profile input resultSort certificate) ×
    Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate.Replays
      profile plan input certificate resultSort start stop tree

instance NativePackedReplays.instSubsingleton
    {view : ForestView} {table : IdentityTable}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat}
    {certificate :
      Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate.Certificate}
    {resultSort : String} {start stop : Nat}
    {tree : Mettapedia.GSLT.Parsing.PresentationExprSemantics.CST} :
    Subsingleton (NativePackedReplays view table profile plan input
      certificate resultSort start stop tree) := by
  unfold NativePackedReplays
  infer_instance

/-- The exact proof fibre exposed by a native binary forest view. -/
abbrev NativePackedFibre (view : ForestView) (table : IdentityTable)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (resultSort : String) (start stop : Nat)
    (tree : Mettapedia.GSLT.Parsing.PresentationExprSemantics.CST) : Type :=
  Sigma fun certificate => NativePackedReplays view table profile plan input
    certificate resultSort start stop tree

/-- A complete exact forest represented by a native binary view has precisely
the operational ParserPack proof fibre.  This is the reusable preservation and
backward-lift theorem that a concrete GLL or GLR export must instantiate. -/
noncomputable def nativeDerivationEquiv
    {view : ForestView} {table : IdentityTable}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {target : ClassAwarePackedForest.Forest}
    {resultSort : String} {start stop : Nat}
    {tree : Mettapedia.GSLT.Parsing.PresentationExprSemantics.CST}
    (represents : Represents view table profile input target)
    (complete : Complete target profile plan input
      resultSort start stop tree) :
    ParserPackDerivesAt profile plan input resultSort start stop tree ≃
      NativePackedFibre view table profile plan input
        resultSort start stop tree where
  toFun derivation :=
    ⟨Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate.Certificate.ofDerivation
        derivation,
      ⟨⟨(represents.rootUnfolds_iff_native resultSort _).mp
          (complete derivation)⟩,
        Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate.Replays.ofDerivation
          derivation⟩⟩
  invFun nativeReplay := nativeReplay.2.2.derivation
  left_inv derivation :=
    Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate.Replays.derivation_ofDerivation
      derivation
  right_inv nativeReplay := by
    rcases nativeReplay with ⟨certificate, replay⟩
    have certificateEqual :=
      Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate.Replays.certificate_derivation
        replay.2
    apply Sigma.eq certificateEqual
    apply Subsingleton.elim

/-! ## Positive and negative controls -/

private def canaryProfile : ParserProfileLayer := {
  name := "NativeForestCanary"
  startSort := "Value"
  classes := []
  states := []
}

private def canarySymbolNode : Node := {
  kind := .symbol 3
  scalarStart := 0
  scalarStop := 1
  byteStart := 0
  byteStop := 1
  choiceBegin := 0
  choiceCount := 1
}

private def canaryTerminalNode : Node := {
  kind := .terminal 10 (.scalar 65)
  scalarStart := 0
  scalarStop := 1
  byteStart := 0
  byteStop := 1
  choiceBegin := 1
  choiceCount := 0
}

private def canaryChoice : Choice := {
  parent := 0
  prefixNode := none
  childNode := 1
  productionIndex := 7
  scalarPivot := 0
  bytePivot := 0
}

private def canaryView : ForestView := {
  nodes := [canarySymbolNode, canaryTerminalNode]
  choices := [canaryChoice]
  roots := [0]
  codepoints := [65]
  byteOffsets := [0, 1]
}

private def canaryTable : IdentityTable := {
  symbolSort? := fun symbolId => if symbolId = 3 then some "Value" else none
  terminalMatcher? := fun terminalId =>
    if terminalId = 10 then some (.char 65) else none
  productionRef? := fun production =>
    if production = 7 then some (.structural 2) else none
}

private def canaryFamily : Family := {
  parent := ⟨"Value", 0, 1⟩
  production := .structural 2
  children := [.terminal (.char 65) 0 1]
}

theorem canaryRootKeyAt :
    RootKeyAt canaryView canaryTable ⟨"Value", 0, 1⟩ := by
  refine ⟨0, 3, 0, 1, 0, 1, ?_⟩
  simp [NodeAt, NodeSpanCoherent, canaryView, canaryTable,
    canarySymbolNode]

/-- A nontrivial symbol/choice/terminal forest inhabits the contract's central
decoding judgment. -/
def canaryFamilyDerivation :
    FamilyDerivation canaryView canaryTable canaryProfile [65]
      0 canaryChoice canaryFamily := by
  refine FamilyDerivation.symbol
      (symbolId := 3) (start := 0) (stop := 1)
      (byteStart := 0) (byteStop := 1)
      (choiceBegin := 0) (choiceCount := 1)
      (resultSort := "Value") (productionRef := .structural 2)
      (children := [.terminal (.char 65) 0 1])
      (parentAt := ?_) (owned := ?_) (sortAt := ?_)
      (productionAt := ?_) ?_
  · simp [NodeAt, NodeSpanCoherent, canaryView, canarySymbolNode]
  · refine ⟨canarySymbolNode, 0, ?_⟩
    simp [canaryView, canarySymbolNode, canaryChoice]
  · simp [canaryTable]
  · simp [canaryTable, canaryChoice]
  · refine ChoiceChildren.binary
        (prefixChildren := [])
        (childChildren := [.terminal (.char 65) 0 1])
        (productionExact := rfl)
        (pivot := ?_)
        (factorization := ?_)
        (prefixResult := PrefixDerivation.empty) ?_
    · refine ⟨canaryTerminalNode, ?_⟩
      simp [NodeAt, NodeSpanCoherent, canaryView, canaryTerminalNode,
        canaryChoice]
    · refine ⟨canarySymbolNode, canaryTerminalNode, ?_⟩
      simp [NodeAt, NodeSpanCoherent, canaryView, canarySymbolNode,
        canaryTerminalNode, canaryChoice]
    · exact ChildDerivation.terminal
        (terminalId := 10) (value := .scalar 65)
        (matcher := .char 65) (start := 0) (stop := 1)
        (byteStart := 0) (byteStop := 1) (choiceBegin := 1)
        (nodeAt := by
          simp [NodeAt, NodeSpanCoherent, canaryView, canaryTerminalNode,
            canaryChoice])
        (matcherAt := by simp [canaryTable])
        (valueAgrees := TerminalValueAgrees.scalar rfl)
        (terminalMatch := TerminalMatchesAt.char rfl)

/-- Negative control: an opaque witness cannot be silently interpreted as a
class-aware scalar or EOF match. -/
theorem witness_value_has_no_classAware_agreement
    (input : List Nat) (identity start stop : Nat) :
    IsEmpty (TerminalValueAgrees input (.witness identity) start stop) :=
  ⟨fun agreement => by cases agreement⟩

/-- Negative control: unequal physical production references determine
unequal flattened families even when parent and children agree. -/
theorem production_mutation_changes_family
    {parent : NodeKey} {children : List ChildRef}
    {left right : ProductionRef} (different : left ≠ right) :
    ({ parent := parent, production := left, children := children } : Family) ≠
      { parent := parent, production := right, children := children } := by
  intro equal
  exact different (congrArg Family.production equal)

/-- Negative control: a pivot different from the child's left boundary cannot
satisfy the binary-choice contract. -/
theorem wrong_scalar_pivot_not_coherent
    {view : ForestView} {choice : Choice} {child : Node}
    (wrong : choice.scalarPivot ≠ child.scalarStart)
    (unique : ∀ candidate, NodeAt view choice.childNode candidate →
      candidate = child) :
    ¬ PivotCoherent view choice := by
  rintro ⟨candidate, candidateAt, scalarEqual, _⟩
  rw [unique candidate candidateAt] at scalarEqual
  exact wrong scalarEqual

/-- Negative control: a child ending before or after its parent cannot satisfy
the binary factorization contract. -/
theorem wrong_child_stop_not_factorized
    {view : ForestView} {choice : Choice} {parent child : Node}
    (wrong : child.scalarStop ≠ parent.scalarStop)
    (parentUnique : ∀ candidate, NodeAt view choice.parent candidate →
      candidate = parent)
    (childUnique : ∀ candidate, NodeAt view choice.childNode candidate →
      candidate = child) :
    ¬ FactorizationCoherent view choice := by
  rintro ⟨candidateParent, candidateChild, candidateParentAt,
    candidateChildAt, _, _, stopEqual, _, _⟩
  rw [parentUnique candidateParent candidateParentAt,
    childUnique candidateChild candidateChildAt] at stopEqual
  exact wrong stopEqual

end Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract
