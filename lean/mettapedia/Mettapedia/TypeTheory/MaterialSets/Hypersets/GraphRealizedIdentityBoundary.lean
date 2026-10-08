import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphSetRealization
import Mettapedia.TypeTheory.MaterialSets.Hypersets.Hyperset

/-!
# Matching evidence and material equality

Constructed graph equality has a sound material equality readout. Its
matching evidence retains choices of child receipts that material equality
forgets. This distinction is visible in actual parent-membership transport,
even when the material endpoints agree.

The control is a two-node cyclic graph. Reflexive matching returns the
requested child; a second coherent matching returns the opposite child.
Both are valid equality realizers, with different actions on membership
receipts. Neither a faithful material equality comparison nor recovery of
that receipt action from material equality exists.

These are properties of matching realizers. They do not identify that
relation with a native identity type or assert unrestricted dependent J.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedIdentityBoundary

open GraphBisimulationRealizers GraphSetRealization

universe u v

/-- A sound readout of constructed matching evidence. -/
theorem materialEquality {first second : Graph.{u}} (proof : Equal first second) :
    HSet.mk first = HSet.mk second := HSet.sound proof.forget

/-- Membership witnesses have a sound material reading without selection
of a graph presentation for an arbitrary quotient value. -/
theorem materialMembership {child parent : Graph.{u}} (proof : Member child parent) :
    HSet.mk child ∈ HSet.mk parent :=
  HSet.mk_mem_mk_iff.mpr ⟨proof.1.val, proof.1.property, proof.2.forget⟩

namespace Controls

/-- Both nodes have both children; all nodes are actually reachable. -/
def cyclic : Graph.{u} where
  Node := ULift.{u} Bool
  edge _ _ := True
  point := ⟨false⟩
  reachable _ := Relation.ReflTransGen.single True.intro

def requested : Child cyclic.{u}.edge cyclic.point := ⟨⟨false⟩, True.intro⟩

/-- Matching data for every pair of nodes, with the opposite child as
the response in both directions. -/
def oppositeStep (first second : cyclic.{u}.Node) (_ : PUnit.{u + 1}) :
    Layer cyclic.edge cyclic.edge (fun _ _ => PUnit.{u + 1}) first second :=
  ⟨fun child => ⟨⟨⟨!child.val.down⟩, True.intro⟩, PUnit.unit⟩,
    fun child => ⟨⟨⟨!child.val.down⟩, True.intro⟩, PUnit.unit⟩⟩

def opposite : Equal cyclic.{u} cyclic :=
  corec cyclic.edge cyclic.edge oppositeStep PUnit.unit

/-- A dependent consumer observes the selected literal child. -/
def response (proof : Equal cyclic.{u} cyclic) : Bool :=
  (proof.out.1 requested).1.val.down

theorem reflexive_response : response (Equal.refl cyclic.{u}) = false := rfl

theorem opposite_response : response opposite.{u} = true := rfl

theorem opposite_ne_reflexive : opposite.{u} ≠ Equal.refl cyclic := by
  intro same
  have readings := congrArg response same
  rw [opposite_response, reflexive_response] at readings
  exact Bool.noConfusion readings

theorem matching_evidence_not_thin : ¬ Subsingleton (Equal cyclic.{u} cyclic) := by
  intro thin
  exact opposite_ne_reflexive (thin.allEq opposite (Equal.refl cyclic))

/-- A material equality proof forgets the actual response. -/
theorem material_equality_agrees :
    materialEquality opposite.{u} = materialEquality (Equal.refl cyclic) :=
  Subsingleton.elim _ _

theorem materialEquality_not_injective :
    ¬ Function.Injective (@materialEquality cyclic.{u} cyclic) := by
  intro injective
  exact opposite_ne_reflexive (injective material_equality_agrees)

/-- The loss is visible in actual membership transport, rather than only
in the internal representation of a matching proof. -/
def initialMember : Member (cyclic.{u}.repoint requested.val) cyclic :=
  Member.atChild cyclic requested

theorem parent_transport_opposite :
    (Member.transportParent opposite.{u} initialMember).1.val.down = true := rfl

theorem parent_transport_reflexive :
    (Member.transportParent (Equal.refl cyclic.{u}) initialMember).1.val.down = false := rfl

theorem parent_transport_distinguished :
    Member.transportParent opposite.{u} initialMember ≠
      Member.transportParent (Equal.refl cyclic) initialMember := by
  intro same
  have readings := congrArg (fun proof : Member (cyclic.repoint requested.val) cyclic =>
    proof.1.val.down) same
  rw [parent_transport_opposite, parent_transport_reflexive] at readings
  exact Bool.noConfusion readings

/-- The selected-response consumer cannot descend through the material
equality readout, although both matching realizers are sound. -/
theorem response_no_material_descent :
    ¬ ∃ read : (HSet.mk cyclic.{u} = HSet.mk cyclic) → Bool,
      ∀ proof : Equal cyclic cyclic, read (materialEquality proof) = response proof := by
  rintro ⟨read, square⟩
  have readings := (square opposite).symm.trans
    ((congrArg read material_equality_agrees).trans (square (Equal.refl cyclic)))
  rw [opposite_response, reflexive_response] at readings
  exact Bool.noConfusion readings

/-- No subsingleton observation can retain all matching witnesses of this
constructed graph, irrespective of which equality proof it records. -/
theorem thin_readout_not_faithful {Target : Type v} [Subsingleton Target]
    (read : Equal cyclic.{u} cyclic → Target) : ¬ Function.Injective read := by
  intro injective
  exact opposite_ne_reflexive (injective (Subsingleton.elim _ _))

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedIdentityBoundary
