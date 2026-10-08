import Mettapedia.SetTheory.Profiles.ProfileGraphReadout
import Mettapedia.TypeTheory.ContextualSmallFamilyUniverse

/-!
# Context substitution for full-future graph readouts

A context functor pulls back the node functor and authored edges. Complete
matching data are restricted by sending each actual future arrow through
that functor. This constructs a material comparison and its commuting
transport square. It proves preservation; an arbitrary functor can remove
observable futures, so no general reflection is claimed.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileGraphReadout

open CategoryTheory
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualGraphDiagrams ContextualRealizedGraphs
open Mettapedia.TypeTheory.ContextualSmallFamilyUniverse
open PowerClassPresheafBaseChange

universe u
variable {D E F : Type u} [Category.{u} D] [Category.{u} E] [Category.{u} F]

/-- Identity with its functor laws supplied explicitly. -/
abbrev contextIdentity (D : Type u) [Category.{u} D] : D ⥤ D := Cat.identity D

/-- Composition with explicit proofs of its two functor laws. -/
abbrev contextCompose (earlier : E ⥤ D) (later : D ⥤ F) : E ⥤ F :=
  Cat.compose earlier later

def reindexDiagram (change : E ⥤ D) (diagram : Diagram D) : Diagram E where
  nodes := restrict change diagram.nodes
  edge point := diagram.edge (change.obj point)
  edge_transport := fun {_ _} arrival {_ _} available =>
    diagram.edge_transport (change.map arrival) available

def reindexValue (change : E ⥤ D) {point : E}
    (value : Value D (change.obj point)) : Value E point :=
  ⟨reindexDiagram change value.1, value.2⟩

def reindexMatching (change : E ⥤ D) (left right : Diagram D) {point : E}
    {first : left.nodes.obj (change.obj point)} {second : right.nodes.obj (change.obj point)}
    (proof : ContextualGraphRealizers.Realizer left right (change.obj point) first second) :
    ContextualGraphRealizers.Realizer (reindexDiagram change left) (reindexDiagram change right)
      point first second :=
  ContextualGraphRealizers.corec (reindexDiagram change left) (reindexDiagram change right)
    (witness := fun point first second =>
      ContextualGraphRealizers.Realizer left right (change.obj point) first second)
    (fun _ _ _ proof future child =>
      ContextualGraphRealizers.Realizer.forth proof
        ⟨change.obj future.1, change.map future.2⟩ child)
    (fun _ _ _ proof future child =>
      ContextualGraphRealizers.Realizer.back proof
        ⟨change.obj future.1, change.map future.2⟩ child) proof

def reindexEqual (change : E ⥤ D) {point : E}
    {first second : Value D (change.obj point)} (proof : Equal first second) :
    Equal (reindexValue change first) (reindexValue change second) :=
  reindexMatching change first.1 second.1 proof

def reindexMaterial (change : E ⥤ D) (point : E) :
    Material D (change.obj point) → Material E point :=
  Quotient.map (reindexValue change) (fun {_ _} ⟨proof⟩ => ⟨reindexEqual change proof⟩)

theorem reindexMaterial_readout (change : E ⥤ D) (point : E)
    (value : Value D (change.obj point)) :
    reindexMaterial change point (readout D value) = readout E (reindexValue change value) := rfl

theorem reindexValue_transport (change : E ⥤ D) {first second : E}
    (arrival : first ⟶ second) (value : Value D (change.obj first)) :
    move E arrival (reindexValue change value) =
      reindexValue change (move D (change.map arrival) value) := rfl

theorem reindexMaterial_transport (change : E ⥤ D) {first second : E}
    (arrival : first ⟶ second) (value : Material D (change.obj first)) :
    transport E arrival (reindexMaterial change first value) =
      reindexMaterial change second (transport D (change.map arrival) value) := by
  induction value using Quotient.inductionOn with
  | h value => rfl

theorem reindexDiagram_identity (diagram : Diagram D) :
    reindexDiagram (contextIdentity D) diagram = diagram := by
  cases diagram
  rfl

theorem reindexDiagram_composition (earlier : E ⥤ D) (later : F ⥤ E)
    (diagram : Diagram D) :
    reindexDiagram later (reindexDiagram earlier diagram) =
      reindexDiagram (contextCompose later earlier) diagram := rfl

theorem reindexValue_identity {point : D} (value : Value D point) :
    reindexValue (contextIdentity D) value = value := by
  cases value
  rfl

theorem reindexValue_composition (earlier : E ⥤ D) (later : F ⥤ E) {point : F}
    (value : Value D (earlier.obj (later.obj point))) :
    reindexValue later (reindexValue earlier value) =
      reindexValue (contextCompose later earlier) value := rfl

theorem reindexMaterial_identity (point : D) (value : Material D point) :
    reindexMaterial (contextIdentity D) point value = value := by
  induction value using Quotient.inductionOn with
  | h value => exact congrArg (readout D) (reindexValue_identity value)

theorem reindexMaterial_composition (earlier : E ⥤ D) (later : F ⥤ E) (point : F)
    (value : Material D (earlier.obj (later.obj point))) :
    reindexMaterial later point (reindexMaterial earlier (later.obj point) value) =
      reindexMaterial (contextCompose later earlier) point value := by
  induction value using Quotient.inductionOn with
  | h value => rfl

def reindexMember (change : E ⥤ D) {point : E}
    {child parent : Value D (change.obj point)} (proof : Member child parent) :
    Member (reindexValue change child) (reindexValue change parent) :=
  ⟨proof.1, reindexEqual change proof.2⟩

theorem reindexMaterial_member (change : E ⥤ D) (point : E)
    {child parent : Material D (change.obj point)} (available : member D child parent) :
    member E (reindexMaterial change point child) (reindexMaterial change point parent) := by
  induction child using Quotient.inductionOn with
  | h child =>
    induction parent using Quotient.inductionOn with
    | h parent =>
      obtain ⟨proof⟩ := available
      exact ⟨reindexMember change proof⟩

end Mettapedia.SetTheory.Profiles.ProfileGraphReadout
