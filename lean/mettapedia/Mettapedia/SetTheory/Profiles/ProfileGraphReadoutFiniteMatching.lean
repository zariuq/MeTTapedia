import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutFinite
import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutMaterial

/-!
# Constructed matching strategies for finite stationary presentations

Finite search turns a nonempty matching set into its first authored
candidate, without selecting from arbitrary propositional existence.
Applied to the greatest finite bisimulation table, it constructs both
responses of a matching strategy. Stationary finite presentations can
therefore be compared with full-future constructive material values.
This is an overlap theorem; current observations of varying diagrams
remain strictly weaker.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileGraphReadout.Finite

open CategoryTheory
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualGraphDiagrams ContextualRealizedGraphs
open ConstructiveFinite

universe u
variable {α β : Type u}

variable [Enumeration α] [Enumeration β] [DecidableEq α] [DecidableEq β]

def finiteWitness (predicate : α → Prop) [DecidablePred predicate]
    (available : ∃ value, predicate value) : {value : α // predicate value} :=
  witness predicate available

variable (D : Type u) [Category.{u} D]
variable (left : α → α → Prop) (right : β → β → Prop)
variable [leftDecidable : DecidableRel left] [rightDecidable : DecidableRel right]

def stationaryDiagram : Diagram D where
  nodes := {
    obj _ := α
    map _ := TypeCat.ofHom id
    map_id _ := rfl
    map_comp _ _ := rfl }
  edge _ := left
  edge_transport := fun {_ _} _ {_ _} available => available

def stationaryValue (point : D) (node : α) : Value D point :=
  ⟨stationaryDiagram D left, node⟩

def stationaryMatching {point : D} {first : α} {second : β}
    (related : (first, second) ∈ stable left right) :
    Equal (stationaryValue D left point first) (stationaryValue D right point second) :=
  ContextualGraphRealizers.corec (stationaryDiagram D left) (stationaryDiagram D right)
    (witness := fun _ first second => PLift ((first, second) ∈ stable left right))
    (fun _ _ second proof _ child =>
      let childNode : α := child.val
      let predicate : β → Prop := fun reply => right second reply ∧ (childNode, reply) ∈ stable left right
      letI : DecidablePred predicate := fun reply => @instDecidableAnd
        (right second reply) ((childNode, reply) ∈ stable left right)
        (rightDecidable second reply) (inferInstanceAs (Decidable ((childNode, reply) ∈ stable left right)))
      let reply := finiteWitness predicate
        ((stable_isBisimulation left right proof.down).1 child.val child.property)
      ⟨⟨reply.val, reply.property.1⟩, ⟨reply.property.2⟩⟩)
    (fun _ first _ proof _ child =>
      let childNode : β := child.val
      let predicate : α → Prop := fun reply => left first reply ∧ (reply, childNode) ∈ stable left right
      letI : DecidablePred predicate := fun reply => @instDecidableAnd
        (left first reply) ((reply, childNode) ∈ stable left right)
        (leftDecidable first reply) (inferInstanceAs (Decidable ((reply, childNode) ∈ stable left right)))
      let reply := finiteWitness predicate
        ((stable_isBisimulation left right proof.down).2 child.val child.property)
      ⟨⟨reply.val, reply.property.1⟩, ⟨reply.property.2⟩⟩) ⟨related⟩

theorem stationary_readout_kernel (point : D) (first : α) (second : β) :
    readout D (stationaryValue D left point first) =
      readout D (stationaryValue D right point second) ↔
        equivalent left right first second = true := by
  constructor
  · intro same
    obtain ⟨matching⟩ := (readout_kernel D _ _).mp same
    have bisimilar := ContextualGraphCurrentMaterial.material_equality matching
    exact (equivalent_material_kernel left right first second).mpr bisimilar
  · intro same
    have related : (first, second) ∈ stable left right := of_decide_eq_true same
    exact (readout_kernel D _ _).mpr ⟨stationaryMatching D left right related⟩

end Mettapedia.SetTheory.Profiles.ProfileGraphReadout.Finite
