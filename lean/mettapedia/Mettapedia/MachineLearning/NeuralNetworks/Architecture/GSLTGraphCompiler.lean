import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.TypedRelationGraph

/-!
# Compiling GSLT problem presentations to typed neural graphs

The compiler is indexed by the exact validated `LanguageDef` used by the
decoder.  A raw problem presentation is first canonicalized; only then is its
finite typed graph built.  This separates three boundaries that need not
coincide:

* presentation metadata versus canonical problem content;
* semantic feature position versus serialized rotary row; and
* neural graph construction versus checker-owned legality and acceptance.

The OEIS instance below models the path, first-difference,
second-difference, and global relations used by the executable encoder.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

open Mettapedia.GSLT.LanguageDef

universe uSource uCanonical uNode uNodeKind uFeature uRole

/-- A compiler from source presentations to one common typed neural interface,
indexed by the exact validated output language. -/
structure GSLTGraphCompiler
    (NodeKind : Type uNodeKind) (Feature : Type uFeature)
    (Role : Type uRole) where
  language : ValidatedLanguageDef
  Source : Type uSource
  CanonicalSource : Type uCanonical
  canonicalize : Source → CanonicalSource
  WellFormed : CanonicalSource → Prop
  Node : CanonicalSource → Type uNode
  compileCanonical : ∀ source : CanonicalSource,
    TypedRelationGraph (Node source) NodeKind Feature Role
  supportedRoles : List Role
  emittedRole_supported : ∀ source edge,
    edge ∈ (compileCanonical source).edges → edge.role ∈ supportedRoles
  relation_functional : ∀ source, WellFormed source →
    (compileCanonical source).relationFunctional

namespace GSLTGraphCompiler

variable {NodeKind : Type uNodeKind} {Feature : Type uFeature}
  {Role : Type uRole}

/-- Compile a raw presentation through its declared canonical form. -/
def compile
    (compiler : GSLTGraphCompiler NodeKind Feature Role)
    (source : compiler.Source) :
    TypedRelationGraph (compiler.Node (compiler.canonicalize source))
      NodeKind Feature Role :=
  compiler.compileCanonical (compiler.canonicalize source)

/-- Two raw presentations with the same canonical content produce the same
typed graph, even when their metadata differs. -/
theorem compile_heq_of_canonicalize_eq
    (compiler : GSLTGraphCompiler NodeKind Feature Role)
    (left right : compiler.Source)
    (sameCanonical : compiler.canonicalize left = compiler.canonicalize right) :
    HEq (compiler.compile left) (compiler.compile right) := by
  exact congr_arg_heq compiler.compileCanonical sameCanonical

/-- The compiler contract exposes the exact three code-facing obligations:
bijective row serialization, supported edge roles, and deterministic relation
assignment. -/
theorem compilation_contract
    (compiler : GSLTGraphCompiler NodeKind Feature Role)
    (source : compiler.CanonicalSource) (wellFormed : compiler.WellFormed source) :
    Function.Bijective (compiler.compileCanonical source).serialize ∧
      (∀ edge ∈ (compiler.compileCanonical source).edges,
        edge.role ∈ compiler.supportedRoles) ∧
      (compiler.compileCanonical source).relationFunctional := by
  exact ⟨(compiler.compileCanonical source).serialize_bijective,
    compiler.emittedRole_supported source,
    compiler.relation_functional source wellFormed⟩

end GSLTGraphCompiler

/-! ## The relation vocabulary used by the executable graph encoder -/

/-- The twelve relation indices of the current neural graph interface. -/
inductive GSLTRelationRole
  | next
  | next2
  | derivedOf
  | global
  | child0
  | child1
  | child2
  | child3
  | child4
  | binder
  | scope
  | sharing
deriving DecidableEq, Repr

/-- Vocabulary order agrees with the executable relation-index table. -/
def allGSLTRelationRoles : List GSLTRelationRole :=
  [.next, .next2, .derivedOf, .global,
    .child0, .child1, .child2, .child3, .child4,
    .binder, .scope, .sharing]

theorem mem_allGSLTRelationRoles (role : GSLTRelationRole) :
    role ∈ allGSLTRelationRoles := by
  cases role <;> simp [allGSLTRelationRoles]

/-! ## Exact OEIS path-source instance -/

/-- Metadata-bearing source presentation.  The identifier is provenance; the
integer prefix is the canonical neural input. -/
structure OEISSequenceSource where
  identifier : String
  values : List Int
deriving DecidableEq, Repr

/-- Nodes are terms, first differences, second differences, and one global
hub.  The nested sum fixes their serialization blocks in that order. -/
abbrev OEISNode (n : Nat) :=
  Fin n ⊕ (Fin (n - 1) ⊕ (Fin (n - 2) ⊕ Unit))

inductive OEISNodeKind
  | term
  | firstDifference
  | secondDifference
  | global
deriving DecidableEq, Repr

namespace OEISPath

/-- Number of rows produced from an `n`-term prefix. -/
def nodeCount (n : Nat) : Nat :=
  n + ((n - 1) + ((n - 2) + 1))

private def secondAndGlobalEquiv (n : Nat) :
    Fin (n - 2) ⊕ Unit ≃ Fin ((n - 2) + 1) :=
  (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans
    finSumFinEquiv

private def firstThroughGlobalEquiv (n : Nat) :
    Fin (n - 1) ⊕ (Fin (n - 2) ⊕ Unit) ≃
      Fin ((n - 1) + ((n - 2) + 1)) :=
  (Equiv.sumCongr (Equiv.refl _) (secondAndGlobalEquiv n)).trans
    finSumFinEquiv

/-- Canonical block serialization: terms, first differences, second
differences, then the global hub. -/
def serialization (n : Nat) : OEISNode n ≃ Fin (nodeCount n) :=
  (Equiv.sumCongr (Equiv.refl _) (firstThroughGlobalEquiv n)).trans
    finSumFinEquiv

/-- Every node exactly once, in canonical serialized row order. -/
def nodes (n : Nat) : List (OEISNode n) :=
  List.ofFn fun row => (serialization n).symm row

def nodeKind {n : Nat} : OEISNode n → OEISNodeKind
  | .inl _ => .term
  | .inr (.inl _) => .firstDifference
  | .inr (.inr (.inl _)) => .secondDifference
  | .inr (.inr (.inr _)) => .global

private def termAt (values : List Int) (index : Fin values.length) : Int :=
  values.get index

private def firstDifferenceAt (values : List Int)
    (index : Fin (values.length - 1)) : Int :=
  let left : Fin values.length := ⟨index.val, by omega⟩
  let right : Fin values.length := ⟨index.val + 1, by omega⟩
  termAt values right - termAt values left

private def secondDifferenceAt (values : List Int)
    (index : Fin (values.length - 2)) : Int :=
  let left : Fin values.length := ⟨index.val, by omega⟩
  let middle : Fin values.length := ⟨index.val + 1, by omega⟩
  let right : Fin values.length := ⟨index.val + 2, by omega⟩
  termAt values right - 2 * termAt values middle + termAt values left

/-- Exact integer feature before the shared integer featurizer. -/
def feature (values : List Int) : OEISNode values.length → Int
  | .inl index => termAt values index
  | .inr (.inl index) => firstDifferenceAt values index
  | .inr (.inr (.inl index)) => secondDifferenceAt values index
  | .inr (.inr (.inr _)) => 0

/-- Semantic feature positions are reused across derivative orders. -/
def featurePosition {n : Nat} : OEISNode n → Nat
  | .inl index => index.val
  | .inr (.inl index) => index.val
  | .inr (.inr (.inl index)) => index.val
  | .inr (.inr (.inr _)) => 0

private def adjacent (left right : Nat) : Bool :=
  left + 1 = right || right + 1 = left

private def twoApart (left right : Nat) : Bool :=
  left + 2 = right || right + 2 = left

/-- Deterministic relation assignment used by the OEIS input graph. -/
def roleAt {n : Nat} : OEISNode n → OEISNode n → Option GSLTRelationRole
  | .inr (.inr (.inr _)), .inr (.inr (.inr _)) => none
  | .inr (.inr (.inr _)), _ => some .global
  | _, .inr (.inr (.inr _)) => some .global
  | .inl left, .inl right =>
      if adjacent left.val right.val then some .next
      else if twoApart left.val right.val then some .next2
      else none
  | .inl term, .inr (.inl difference) =>
      if term.val = difference.val then some .derivedOf else none
  | .inr (.inl difference), .inl term =>
      if term.val = difference.val then some .derivedOf else none
  | .inl term, .inr (.inr (.inl difference)) =>
      if term.val = difference.val then some .derivedOf else none
  | .inr (.inr (.inl difference)), .inl term =>
      if term.val = difference.val then some .derivedOf else none
  | _, _ => none

/-- The exact finite typed graph for one canonical integer prefix. -/
def graph (values : List Int) :
    TypedRelationGraph (OEISNode values.length) OEISNodeKind Int
      GSLTRelationRole where
  nodeDecidableEq := inferInstance
  nodeCount := nodeCount values.length
  serialize := serialization values.length
  serialize_bijective := (serialization values.length).bijective
  nodeKind := nodeKind
  feature := feature values
  featurePosition := featurePosition
  active := fun _ => true
  edges := edgesFromRoleAt (nodes values.length) roleAt

theorem graph_relationFunctional (values : List Int) :
    (graph values).relationFunctional := by
  exact edgesFromRoleAt_relationFunctional (nodes values.length) roleAt

theorem graph_emittedRole_supported (values : List Int)
    (edge : EdgeOccurrence (OEISNode values.length) GSLTRelationRole)
    (_member : edge ∈ (graph values).edges) :
    edge.role ∈ allGSLTRelationRoles :=
  mem_allGSLTRelationRoles edge.role

/-- The graph compiler can be paired with any exact validated GSLT output
language; language-specific legality remains in the decoder/checker layer. -/
def compiler (language : ValidatedLanguageDef) (maxPositions : Nat) :
    GSLTGraphCompiler OEISNodeKind Int GSLTRelationRole where
  language := language
  Source := OEISSequenceSource
  CanonicalSource := List Int
  canonicalize := OEISSequenceSource.values
  WellFormed := fun values => values ≠ [] ∧ values.length ≤ maxPositions
  Node := fun values => OEISNode values.length
  compileCanonical := graph
  supportedRoles := allGSLTRelationRoles
  emittedRole_supported := graph_emittedRole_supported
  relation_functional := fun source _ => graph_relationFunctional source

/-- Provenance labels do not alter the graph when the canonical prefix is
identical. -/
theorem metadata_invariant (language : ValidatedLanguageDef) (maxPositions : Nat)
    (leftIdentifier rightIdentifier : String) (values : List Int) :
    HEq ((compiler language maxPositions).compile ⟨leftIdentifier, values⟩)
      ((compiler language maxPositions).compile ⟨rightIdentifier, values⟩) :=
  (compiler language maxPositions).compile_heq_of_canonicalize_eq
    ⟨leftIdentifier, values⟩ ⟨rightIdentifier, values⟩ rfl

/-- Positive executable fixture: the three node blocks share semantic
positions, while their serialized rotary rows remain distinct. -/
theorem three_term_position_boundary :
    let term0 : OEISNode 3 := .inl ⟨0, by decide⟩
    let first0 : OEISNode 3 := .inr (.inl ⟨0, by decide⟩)
    featurePosition term0 = featurePosition first0 ∧
      (serialization 3 term0).val ≠ (serialization 3 first0).val := by
  simp [featurePosition, serialization, firstThroughGlobalEquiv,
    secondAndGlobalEquiv]
  change (0 : Nat) ≠ 3
  omega

def threeTerm0 : OEISNode 3 := .inl ⟨0, by decide⟩
def threeTerm1 : OEISNode 3 := .inl ⟨1, by decide⟩
def threeTerm2 : OEISNode 3 := .inl ⟨2, by decide⟩
def threeFirstDifference0 : OEISNode 3 :=
  .inr (.inl ⟨0, by decide⟩)
def threeSecondDifference0 : OEISNode 3 :=
  .inr (.inr (.inl ⟨0, by decide⟩))
def threeGlobal : OEISNode 3 := .inr (.inr (.inr ()))

/-- The three-term fixture has the same 24 directed edges as the executable
adapter: four adjacent, two distance-two, six derived, and twelve global. -/
theorem three_term_edge_count :
    (graph [1, 2, 3]).edges.length = 24 := by
  decide

/-- Representative relation cells agree with the executable path adapter. -/
theorem three_term_relation_cells :
    (graph [1, 2, 3]).lastRole? threeTerm0 threeTerm1 = some .next ∧
      (graph [1, 2, 3]).lastRole? threeTerm0 threeTerm2 = some .next2 ∧
      (graph [1, 2, 3]).lastRole? threeFirstDifference0 threeTerm0 =
        some .derivedOf ∧
      (graph [1, 2, 3]).lastRole? threeGlobal threeTerm0 = some .global ∧
      (graph [1, 2, 3]).lastRole? threeFirstDifference0 threeTerm1 = none := by
  decide

/-- Negative fixture: changing canonical content changes a real node feature,
even when provenance metadata is held fixed. -/
theorem changed_prefix_changes_feature :
    let first : OEISSequenceSource := ⟨"same", [1, 2, 3]⟩
    let second : OEISSequenceSource := ⟨"same", [9, 2, 3]⟩
    (graph first.values).feature (Sum.inl ⟨0, by decide⟩) ≠
      (graph second.values).feature (Sum.inl ⟨0, by decide⟩) := by
  decide

end OEISPath

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
