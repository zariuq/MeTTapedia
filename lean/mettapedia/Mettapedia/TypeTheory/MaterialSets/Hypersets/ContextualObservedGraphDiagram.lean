import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphReceiptFamilies
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerClassifier
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraBisimulation

/-!
# Authored observed coalgebras in the varying graph universe

An originally small contextual coalgebra supplies the actual node
functor and its stable successor relation. Pointing that diagram gives
a natural interpretation in the same varying graph universe used by
the realized set theory. Pullback of the literal child family agrees
with the independently formed native successor family, including its
context maps and complete compatible sections.

The source signature determines which observations survive. In particular,
a relation that has already forgotten event occurrences does not recover
them here. Retained future matching entails the source's propositional
bisimilarity; no selection of a matching strategy from that proposition
is made.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualObservedGraphDiagram

open CategoryTheory ContextualWitnessCover ContextualGraphDiagrams
open ContextualSmallFamilyUniverse

universe u
variable {D : Type u} [Category.{u} D] {A : D ⥤ Type u}
variable (source : NaturalHom A (CoveredFuturePowerFamilies.family A))

def edge (point : D) (parent child : A.obj point) : Prop :=
  (source.app point parent).val.holds (CoveredFuturePowerFamilies.current A point child)

theorem edge_transport {first second : D} (arrival : first ⟶ second)
    {parent child : A.obj first} (available : edge source first parent child) :
    edge source second (A.map arrival parent) (A.map arrival child) :=
  (CoveredFuturePowerClassifier.classifiedPredicate A A source).closed
    (CategoryOfElements.homMk (F := CoveredFuturePowerClassifier.product A A)
      ⟨first, (parent, child)⟩ ⟨second, (A.map arrival parent, A.map arrival child)⟩ arrival rfl)
    available

def diagram : Diagram D where
  nodes := A
  edge := edge source
  edge_transport := edge_transport source

def pointing : NaturalHom A (values D) where
  app _ node := ⟨diagram source, node⟩
  naturality _ _ := rfl

theorem pointing_injective (point : D) : Function.Injective ((pointing source).app point) := by
  intro first second same
  exact eq_of_heq (Sigma.mk.inj_iff.mp same).2

theorem literal_kernel (point : D) (first second : A.obj point) :
    (pointing source).app point first = (pointing source).app point second ↔ first = second :=
  ⟨fun same => pointing_injective source point same, congrArg ((pointing source).app point)⟩

/-- Full future truth is recovered at the identical future object and
actual arrow, not by a pointwise change of context. -/
theorem future_edge (point : D) (parent : A.obj point)
    (future : PowerClassPresheafBaseChange.Future.Objects point) (child : A.obj future.1) :
    (source.app point parent).val.holds ⟨future, child⟩ ↔
      (diagram source).edge future.1 (A.map future.2 parent) child :=
  CoveredFuturePowerClassifier.classified_future A A source point parent ⟨future, child⟩

def successorFamily : A.Elements ⥤ Type u where
  obj point := {child : A.obj point.1 // edge source point.1 point.2 child}
  map {first second} step := TypeCat.ofHom fun child =>
    ⟨A.map step.1 child.val, by
      have moved := edge_transport source step.1 child.property
      have parents : A.map step.1 first.2 = second.2 := step.2
      rw [parents] at moved
      exact moved⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro child
    exact Subtype.ext (A.map_id_apply point.1 child.val)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro child
    exact Subtype.ext (A.map_comp_apply earlier.1 later.1 child.val)

/-- The independently authored successor action agrees with pullback of
the actual native family on the untyped contextual value universe. -/
theorem successor_pullback :
    ContextualGraphReceiptFamilies.along (pointing source) = successorFamily source := by
  refine Functor.hext (fun _ => rfl) ?_
  intro first second step
  apply heq_of_eq
  apply ConcreteCategory.hom_ext
  intro child
  apply Subtype.ext
  have readings := ContextualGraphReceiptFamilies.childValue_map D
    ((elementMap (pointing source)).map step) child
  exact eq_of_heq (Sigma.mk.inj_iff.mp readings).2

def successorSections : (ContextualGraphReceiptFamilies.along (pointing source)).sections ≃
    (successorFamily source).sections :=
  typeEqualityEquiv (congrArg (fun family : A.Elements ⥤ Type u => ↥family.sections)
    (successor_pullback source))

def wholeSelections : (successorFamily source).sections ≃
    ContextualGraphReceiptFamilies.Selection (pointing source) :=
  (successorSections source).symm.trans (ContextualGraphReceiptFamilies.wholeSectionEquiv (pointing source))

def nativeClassifier : NaturalHom A (universeFamily (D := D)) :=
  classifier (successorFamily source)

theorem native_decoding : decodedFamily (nativeClassifier source) = successorFamily source :=
  decoded_classifier_eq _

def successorMembership (point : D) (parent : A.obj point)
    (child : (successorFamily source).obj ⟨point, parent⟩) :
    ContextualRealizedGraphs.Member ((pointing source).app point child.val)
      ((pointing source).app point parent) :=
  ContextualRealizedGraphs.Member.atChild ((pointing source).app point parent) child

def sectionReading (term : (successorFamily source).sections) : NaturalHom A (values D) :=
  ContextualGraphReceiptFamilies.sectionReading (pointing source) ((successorSections source).symm term)

def sectionMembership (term : (successorFamily source).sections) (point : D) (parent : A.obj point) :
    ContextualRealizedGraphs.Member ((sectionReading source term).app point parent)
      ((pointing source).app point parent) :=
  ContextualGraphReceiptFamilies.sectionMembership (pointing source)
    ((successorSections source).symm term) point parent

theorem matching_is_bisimulation :
    ContextualCoalgebraBisimulation.IsBisimulation source
      (fun point first second => Nonempty (ContextualRealizedGraphs.Equal
        ((pointing source).app point first) ((pointing source).app point second))) where
  stable {_ _} arrival {_ _} related := related.map (ContextualRealizedGraphs.Equal.restrict arrival)
  forth {point left right} related future {child} available := by
    obtain ⟨matching⟩ := related
    let response := ContextualGraphRealizers.Realizer.forth matching ⟨future.1, future.2⟩
      ⟨child, (future_edge source point left future child).mp available⟩
    exact ⟨response.1.val, (future_edge source point right future response.1.val).mpr response.1.property,
      ⟨response.2⟩⟩
  back {point left right} related future {child} available := by
    obtain ⟨matching⟩ := related
    let response := ContextualGraphRealizers.Realizer.back matching ⟨future.1, future.2⟩
      ⟨child, (future_edge source point right future child).mp available⟩
    exact ⟨response.1.val, (future_edge source point left future response.1.val).mpr response.1.property,
      ⟨response.2⟩⟩

theorem matching_implies_bisimilar (point : D) (first second : A.obj point)
    (matching : ContextualRealizedGraphs.Equal ((pointing source).app point first)
      ((pointing source).app point second)) :
    ContextualCoalgebraBisimulation.Bisimilar source point first second :=
  ContextualCoalgebraBisimulation.greatest source (matching_is_bisimulation source) ⟨matching⟩

section AuthoredDiagram

variable (graph : Diagram D)

def authoredRelation : CoveredFuturePowerClassifier.StablePredicate
    (CoveredFuturePowerClassifier.product graph.nodes graph.nodes) where
  holds point := graph.edge point.1 point.2.1 point.2.2
  closed {first second} step available := by
    have parents := congrArg Prod.fst step.2
    have children := congrArg Prod.snd step.2
    exact parents ▸ children ▸ graph.edge_transport step.1 available

/-- The truth subtype itself constructs the small cover; no supplied
enumeration or chosen inverse is required. -/
def authoredSource : NaturalHom graph.nodes (CoveredFuturePowerFamilies.family graph.nodes) :=
  CoveredFuturePowerClassifier.classifier graph.nodes graph.nodes
    (CoveredFuturePowerClassifier.smallRelation graph.nodes graph.nodes (authoredRelation graph))

theorem authored_edge (point : D) (parent child : graph.nodes.obj point) :
    (diagram (authoredSource graph)).edge point parent child ↔ graph.edge point parent child := by
  change graph.edge point (graph.nodes.map (𝟙 point) parent) child ↔ graph.edge point parent child
  rw [graph.nodes.map_id_apply]

theorem authored_future (point : D) (parent : graph.nodes.obj point)
    (future : PowerClassPresheafBaseChange.Future.Objects point) (child : graph.nodes.obj future.1) :
    ((authoredSource graph).app point parent).val.holds ⟨future, child⟩ ↔
      graph.edge future.1 (graph.nodes.map future.2 parent) child := Iff.rfl

end AuthoredDiagram

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualObservedGraphDiagram
