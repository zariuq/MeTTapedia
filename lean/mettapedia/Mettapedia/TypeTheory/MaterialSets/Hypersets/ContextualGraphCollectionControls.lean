import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedCollection
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphNonThinControls

/-!
# Non-thin, growing controls for actual contextual Strong Collection

The source graph exposes successively larger ordinal member families.
The body says that the source member belongs to its witness, and the
constructed witness is the transported source set itself. Collection
therefore acts on genuine varying values and membership realizers.

Two factorizations of one history retain distinct source occurrences:
an early witness followed by a later event, and a witness first obtained
at the final context. Their material children match at every future,
while their literal collection receipts keep the provenance distinct.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphCollectionControls

open CategoryTheory ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphFormulaRealization
open LabelledContextPaths ContextualGraphNonThinControls

def body : Formula 2 := .member 1 0
def environment : Environment World 0 initial := Fin.elim0
def sourceSet : Value World initial := root 0

def premise : ContextualGraphRealizedCollection.Premise body environment sourceSet :=
  fun _ arrival _ member => ⟨move World arrival sourceSet, ⟨member⟩⟩

def collected : Value World initial := ContextualGraphRealizedCollection.collector body environment sourceSet premise

def bothClauses := ContextualGraphRealizedCollection.strongCollection body environment sourceSet premise

def forwardAt (count : Nat) :=
  ContextualGraphRealizedCollection.forward body environment sourceSet premise (stage count) (history 0 count)
    (ordinalValue 0 (stage count) count)
    (Member.atChild (arrived 0 (history 0 count)) (newest 0 count))

def arrivalAtTwo : initial ⟶ two := extension 0 ≫ laterExtension 1

def earlyOrigin : ContextualGraphRealizedCollection.Origin sourceSet := ⟨next, extension 0, firstChild 0⟩

def lateChild : Child World (move World arrivalAtTwo sourceSet) :=
  ⟨Sum.inr 0, ⟨Nat.zero_lt_succ 1, [1], rfl⟩⟩

def lateOrigin : ContextualGraphRealizedCollection.Origin sourceSet := ⟨two, arrivalAtTwo, lateChild⟩

def rootAtTwo : Value World two :=
  ContextualGraphRealizedCollection.root body environment sourceSet premise two arrivalAtTwo

def earlyReceipt : Child World rootAtTwo :=
  ContextualGraphGenerators.rootChild (ContextualGraphRealizedCollection.source sourceSet) (ContextualGraphRealizedCollection.arrival sourceSet)
    (ContextualGraphRealizedCollection.witnessValue body environment sourceSet premise) arrivalAtTwo
    earlyOrigin (laterExtension 1) rfl

def lateReceipt : Child World rootAtTwo :=
  ContextualGraphGenerators.rootChild (ContextualGraphRealizedCollection.source sourceSet) (ContextualGraphRealizedCollection.arrival sourceSet)
    (ContextualGraphRealizedCollection.witnessValue body environment sourceSet premise) arrivalAtTwo
    lateOrigin (𝟙 two) (Category.comp_id arrivalAtTwo)

theorem origins_distinct : earlyOrigin ≠ lateOrigin := by
  intro same
  have stages := congrArg (fun origin : ContextualGraphRealizedCollection.Origin sourceSet => origin.1.length) same
  change (1 : Nat) = 2 at stages
  exact Nat.zero_ne_one (Nat.succ.inj stages)

theorem factorization_receipts_distinct : earlyReceipt ≠ lateReceipt := by
  intro same
  have nodes := congrArg Subtype.val same
  have stages := congrArg (fun node : ContextualGraphGenerators.Node (initial := initial)
      (ContextualGraphRealizedCollection.source sourceSet) (ContextualGraphRealizedCollection.witnessValue body environment sourceSet premise) two =>
    match node with
    | .inl _ => 0
    | .inr receipt => (ContextualGraphRealizedCollection.source sourceSet receipt.1).length) nodes
  change (1 : Nat) = 2 at stages
  exact Nat.zero_ne_one (Nat.succ.inj stages)

def earlyMembership : Member (move World arrivalAtTwo sourceSet) rootAtTwo :=
  Member.transportChild
    (Equal.ofEq (ContextualGraphRealizedCollection.transportedSource sourceSet earlyOrigin (laterExtension 1) arrivalAtTwo rfl))
    (ContextualGraphGenerators.rootIntro (ContextualGraphRealizedCollection.source sourceSet) (ContextualGraphRealizedCollection.arrival sourceSet)
      (ContextualGraphRealizedCollection.witnessValue body environment sourceSet premise) arrivalAtTwo
      earlyOrigin (laterExtension 1) rfl)

def lateMembership : Member (move World arrivalAtTwo sourceSet) rootAtTwo :=
  Member.transportChild
    (Equal.ofEq (move_identity World two (move World arrivalAtTwo sourceSet)))
    (ContextualGraphGenerators.rootIntro (ContextualGraphRealizedCollection.source sourceSet) (ContextualGraphRealizedCollection.arrival sourceSet)
      (ContextualGraphRealizedCollection.witnessValue body environment sourceSet premise) arrivalAtTwo
      lateOrigin (𝟙 two) (Category.comp_id arrivalAtTwo))

def receipt_children_match :
    Equal (childValue World rootAtTwo earlyReceipt) (childValue World rootAtTwo lateReceipt) :=
  earlyMembership.2.symm.trans lateMembership.2

theorem material_matching_does_not_identify_literal_receipts :
    Nonempty (Equal (childValue World rootAtTwo earlyReceipt)
      (childValue World rootAtTwo lateReceipt)) ∧ earlyReceipt ≠ lateReceipt :=
  ⟨⟨receipt_children_match⟩, factorization_receipts_distinct⟩

def originDepth (receipt : Child World rootAtTwo) : Nat :=
  match receipt.val with
  | .inl _ => 0
  | .inr retained => (ContextualGraphRealizedCollection.source sourceSet retained.1).length

/-- A dependent consumer may ask for an index at the witness's origin. -/
def originIndices (receipt : Child World rootAtTwo) : Type := Fin (originDepth receipt)

theorem matching_does_not_supply_dependent_transport :
    Nonempty (Equal (childValue World rootAtTwo earlyReceipt)
      (childValue World rootAtTwo lateReceipt)) ∧
      ¬ Nonempty (originIndices earlyReceipt ≃ originIndices lateReceipt) := by
  refine ⟨⟨receipt_children_match⟩, ?_⟩
  rintro ⟨comparison⟩
  change Fin 1 ≃ Fin 2 at comparison
  have same : comparison.symm 0 = comparison.symm 1 := Subsingleton.elim _ _
  have impossible : (0 : Fin 2) = 1 := comparison.symm.injective same
  exact Nat.zero_ne_one (congrArg Fin.val impossible)

def backwardEarly :=
  ContextualGraphRealizedCollection.backwardRoot body environment sourceSet premise two arrivalAtTwo
    (move World arrivalAtTwo sourceSet) earlyMembership

def backwardLate :=
  ContextualGraphRealizedCollection.backwardRoot body environment sourceSet premise two arrivalAtTwo
    (move World arrivalAtTwo sourceSet) lateMembership

def earlyTransportedMembership :
    Member (move World arrivalAtTwo sourceSet) (move World arrivalAtTwo collected) :=
  Member.transportParent
    (Equal.ofEq (ContextualGraphRealizedCollection.collector_move body environment sourceSet premise two arrivalAtTwo).symm)
    earlyMembership

def actualBackward :=
  ContextualGraphRealizedCollection.backward body environment sourceSet premise two arrivalAtTwo
    (move World arrivalAtTwo sourceSet) earlyTransportedMembership

/-- A witness with no literal children cannot realize this body's
membership assertion, even though the initial source observation is empty. -/
theorem empty_witness_refused (point : World) (value : Value World point) :
    ¬ Nonempty (Member value (constantValue World AccessiblePointedGraph.empty point)) := by
  rintro ⟨member⟩
  exact AccessiblePointedGraph.not_edge_empty member.1.val member.1.property

theorem collection_contains_unbounded_source_stages :
    Function.Injective (fun count =>
      (⟨stage count, history 0 count, newest 0 count⟩ : ContextualGraphRealizedCollection.Origin sourceSet)) := by
  intro first second same
  apply infinitely_many_worlds
  exact congrArg Sigma.fst same

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphCollectionControls
