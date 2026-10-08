import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyNodes
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphReceiptFamilies

/-!
# Natural body embeddings with actual child recovery

A natural embedding of all declared body nodes, preserving edges and
recovering every target child, induces full-future material matching.
The coiteration retains the native body receipt and every internal node.
The lifting data concern a concrete graph embedding, not a supplied
material interpretation or a selected quotient representative.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphNaturalBodyEmbedding

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualGraphDiagrams ContextualRealizedGraphs
universe u
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type u}
variable (reading : NaturalHom base (values D))

def bodyNodes : base.Elements ⥤ Type u := restrict (elementMap reading) (ContextualGraphFamilyBodyNodes.family D)

def nodeReading : NaturalHom (total (bodyNodes reading)) (values D) where
  app point receipt := ContextualGraphFamilyBodyNodes.reroot D (reading.app point receipt.1) receipt.2
  naturality {first second} arrival receipt :=
    (ContextualGraphFamilyBodyNodes.reroot_map D ((elementMap reading).map
      (CategoryOfElements.homMk (F := base) ⟨first, receipt.1⟩
        ⟨second, base.map arrival receipt.1⟩ arrival rfl)) receipt.2).symm

variable (target : Diagram D)
variable (embed : NaturalHom (total (bodyNodes reading)) target.nodes)

abbrev Forth : Prop :=
  ∀ (point : D) (receipt : (total (bodyNodes reading)).obj point)
    (child : Child D ((nodeReading reading).app point receipt)),
    target.edge point (embed.app point receipt) (embed.app point ⟨receipt.1, child.val⟩)

abbrev Back : Type u :=
  ∀ (point : D) (receipt : (total (bodyNodes reading)).obj point)
    (child : Child D (⟨target, embed.app point receipt⟩ : Value D point)),
    Σ actual : Child D ((nodeReading reading).app point receipt),
      PLift (child.val = embed.app point ⟨receipt.1, actual.val⟩)

variable (forth : Forth reading target embed) (back : Back reading target embed)

abbrev Witness (source : Diagram D) (point : D)
    (first : source.nodes.obj point) (second : target.nodes.obj point) : Type u :=
  Σ receipt : (total (bodyNodes reading)).obj point,
    PLift ((nodeReading reading).app point receipt = (⟨source, first⟩ : Value D point)) ×
      PLift (second = embed.app point receipt)

def stepForth (source : Diagram D) (point : D)
    (first : source.nodes.obj point) (second : target.nodes.obj point)
    (proof : Witness reading target embed source point first second)
    (future : ContextualGraphRealizers.Future point)
    (child : ContextualGraphRealizers.Child source future.1 (source.nodes.map future.2 first)) :
    Σ matched : ContextualGraphRealizers.Child target future.1 (target.nodes.map future.2 second),
      Witness reading target embed source future.1 child.val matched.val := by
  rcases proof with ⟨receipt, ⟨same⟩, ⟨atNode⟩⟩
  subst second
  let next := (total (bodyNodes reading)).map future.2 receipt
  have readings : (nodeReading reading).app future.1 next =
      (⟨source, source.nodes.map future.2 first⟩ : Value D future.1) :=
    ((nodeReading reading).naturality future.2 receipt).symm.trans (congrArg (move D future.2) same)
  let actual := cast (congrArg (Child D) readings.symm) child
  have edge := forth future.1 next actual
  rw [← embed.naturality future.2 receipt] at edge
  exact ⟨⟨embed.app future.1 ⟨next.1, actual.val⟩, edge⟩,
    ⟨next.1, actual.val⟩, ⟨ContextualGraphReceiptFamilies.childValue_cast D readings.symm child⟩, ⟨rfl⟩⟩

def stepBack (source : Diagram D) (point : D)
    (first : source.nodes.obj point) (second : target.nodes.obj point)
    (proof : Witness reading target embed source point first second)
    (future : ContextualGraphRealizers.Future point)
    (child : ContextualGraphRealizers.Child target future.1 (target.nodes.map future.2 second)) :
    Σ matched : ContextualGraphRealizers.Child source future.1 (source.nodes.map future.2 first),
      Witness reading target embed source future.1 matched.val child.val := by
  rcases proof with ⟨receipt, ⟨same⟩, ⟨atNode⟩⟩
  subst second
  let next := (total (bodyNodes reading)).map future.2 receipt
  have readings : (nodeReading reading).app future.1 next =
      (⟨source, source.nodes.map future.2 first⟩ : Value D future.1) :=
    ((nodeReading reading).naturality future.2 receipt).symm.trans (congrArg (move D future.2) same)
  have edge : target.edge future.1 (embed.app future.1 next) child.val :=
    (embed.naturality future.2 receipt) ▸ child.property
  let recovered := back future.1 next ⟨child.val, edge⟩
  let actual := cast (congrArg (Child D) readings) recovered.1
  exact ⟨actual, ⟨next.1, recovered.1.val⟩,
    ⟨(ContextualGraphReceiptFamilies.childValue_cast D readings recovered.1).symm⟩, recovered.2⟩

def comparison (point : D) (receipt : (total (bodyNodes reading)).obj point) :
    Equal ((nodeReading reading).app point receipt) (⟨target, embed.app point receipt⟩ : Value D point) :=
  ContextualGraphRealizers.corec (reading.app point receipt.1).1 target
    (stepForth reading target embed forth (reading.app point receipt.1).1)
    (stepBack reading target embed back (reading.app point receipt.1).1)
    ⟨receipt, ⟨rfl⟩, ⟨rfl⟩⟩

def rootComparison (point : D) (receipt : base.obj point) :
    Equal (reading.app point receipt)
      (⟨target, embed.app point ⟨receipt, (reading.app point receipt).2⟩⟩ : Value D point) :=
  comparison reading target embed forth back point ⟨receipt, (reading.app point receipt).2⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphNaturalBodyEmbedding
