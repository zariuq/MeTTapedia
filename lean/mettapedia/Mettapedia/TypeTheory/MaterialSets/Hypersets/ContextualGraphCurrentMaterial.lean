import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualRealizedGraphs
import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedIdentityBoundary
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Current material observations of the actual contextual graph universe

Full future matching computes matching of each current graph picture.
Equality and membership therefore have ordinary material observations at
every declared future. These are stage-indexed observations; the current
material picture is not asserted to be a constant natural set model.

The infinite stage control below agrees with the empty picture initially
and acquires a member later. Its initial material agreement cannot recover
full future matching. No reflection of implication or arbitrary dependent
receipt families is inferred from the primitive observations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphCurrentMaterial

open CategoryTheory ContextualGraphDiagrams

universe u
variable {D : Type u} [Category.{u} D]

def currentStep (left right : Diagram D) (point : D)
    (first : left.nodes.obj point) (second : right.nodes.obj point)
    (proof : ContextualGraphRealizers.Realizer left right point first second) :
    GraphBisimulationRealizers.Layer (left.edge point) (right.edge point)
      (fun first second => ContextualGraphRealizers.Realizer left right point first second)
      first second :=
  ⟨fun child => ContextualGraphRealizers.Realizer.currentForth proof child,
    fun child => ContextualGraphRealizers.Realizer.currentBack proof child⟩

/-- Current matching is computed from the identity-future responses at
every continuation layer, rather than chosen from bisimilarity. -/
def currentMatching (left right : Diagram D) (point : D)
    {first : left.nodes.obj point} {second : right.nodes.obj point}
    (proof : ContextualGraphRealizers.Realizer left right point first second) :
    GraphBisimulationRealizers.Realizer (left.edge point) (right.edge point) first second :=
  GraphBisimulationRealizers.corec (left.edge point) (right.edge point)
    (currentStep left right point) proof

def pictureMatching {point : D} (first second : Value D point)
    (proof : GraphBisimulationRealizers.Realizer
      (first.1.edge point) (second.1.edge point) first.2 second.2) :
    GraphSetRealization.Equal (picture D first) (picture D second) :=
  (GraphBisimulationRealizers.generated (left := first.1.edge point) first.2
    (picture D first).point).trans
      (proof.trans
        (GraphBisimulationRealizers.generated (left := second.1.edge point) second.2
          (picture D second).point).symm)

def pictureEquality {point : D} {first second : Value D point}
    (proof : ContextualRealizedGraphs.Equal first second) :
    GraphSetRealization.Equal (picture D first) (picture D second) :=
  pictureMatching first second (currentMatching first.1 second.1 point proof)

theorem material_equality {point : D} {first second : Value D point}
    (proof : ContextualRealizedGraphs.Equal first second) :
    HSet.mk (picture D first) = HSet.mk (picture D second) :=
  GraphRealizedIdentityBoundary.materialEquality (pictureEquality proof)

theorem material_equality_at_future {point target : D} (arrival : point ⟶ target)
    {first second : Value D point} (proof : ContextualRealizedGraphs.Equal first second) :
    HSet.mk (picture D (move D arrival first)) =
      HSet.mk (picture D (move D arrival second)) :=
  material_equality (ContextualRealizedGraphs.Equal.restrict arrival proof)

/-- A literal current child is present in the generated graph without a
choice of a presentation representative. -/
def pictureChild {point : D} (parent : Value D point) (child : Child D parent) :
    GraphBisimulationRealizers.Child (picture D parent).edge (picture D parent).point :=
  ⟨⟨child.val, Relation.ReflTransGen.single child.property⟩, child.property⟩

def childPictureEquality {point : D} (parent : Value D point) (child : Child D parent) :
    GraphSetRealization.Equal (picture D (childValue D parent child))
      ((picture D parent).repoint (pictureChild parent child).val) :=
  (GraphBisimulationRealizers.generated (left := parent.1.edge point) child.val
      (picture D (childValue D parent child)).point).trans
    ((GraphSetRealization.repointInclusion (picture D parent) (pictureChild parent child).val).trans
      (GraphBisimulationRealizers.generated (left := parent.1.edge point) parent.2
        (pictureChild parent child).val)).symm

def pictureMembership {point : D} {child parent : Value D point}
    (proof : ContextualRealizedGraphs.Member child parent) :
    GraphSetRealization.Member (picture D child) (picture D parent) :=
  ⟨pictureChild parent proof.1,
    (pictureEquality proof.2).trans (childPictureEquality parent proof.1)⟩

theorem material_membership {point : D} {child parent : Value D point}
    (proof : ContextualRealizedGraphs.Member child parent) :
    HSet.mk (picture D child) ∈ HSet.mk (picture D parent) :=
  GraphRealizedIdentityBoundary.materialMembership (pictureMembership proof)

theorem material_membership_at_future {point target : D} (arrival : point ⟶ target)
    {child parent : Value D point} (proof : ContextualRealizedGraphs.Member child parent) :
    HSet.mk (picture D (move D arrival child)) ∈
      HSet.mk (picture D (move D arrival parent)) :=
  material_membership (ContextualRealizedGraphs.Member.restrict arrival proof)

namespace Controls

/-- A delayed edge is authored at every natural stage beyond its bound.
The bound is arbitrary; there is no last observation stage. -/
def delayed (bound : Nat) : Diagram Nat where
  nodes := {
    obj _ := Bool
    map _ := TypeCat.ofHom id
    map_id _ := rfl
    map_comp _ _ := rfl }
  edge stage parent child := parent = false ∧ child = true ∧ bound < stage
  edge_transport := fun {_ _} arrival {_ _} available =>
    ⟨available.1, available.2.1, Nat.lt_of_lt_of_le available.2.2 (leOfHom arrival)⟩

def delayedValue (bound stage : Nat) : Value Nat stage := ⟨delayed bound, false⟩

def emptyDiagram : Diagram Nat where
  nodes := {
    obj _ := PUnit
    map _ := TypeCat.ofHom id
    map_id _ := rfl
    map_comp _ _ := rfl }
  edge _ _ _ := False
  edge_transport := fun {_ _} _ {_ _} available => available

def emptyValue (stage : Nat) : Value Nat stage := ⟨emptyDiagram, PUnit.unit⟩

def initiallyEmpty (bound : Nat) :
    GraphBisimulationRealizers.Realizer ((delayed bound).edge 0)
      (emptyDiagram.edge 0) false PUnit.unit :=
  GraphBisimulationRealizers.corec ((delayed bound).edge 0) (emptyDiagram.edge 0)
    (witness := fun _ _ => PUnit.{1})
    (fun _ _ _ =>
      ⟨fun child => False.elim (Nat.not_lt_zero bound child.property.2.2),
        fun child => False.elim child.property⟩) PUnit.unit

theorem initial_material_agreement (bound : Nat) :
    HSet.mk (picture Nat (delayedValue bound 0)) =
      HSet.mk (picture Nat (emptyValue 0)) :=
  GraphRealizedIdentityBoundary.materialEquality
    (pictureMatching (delayedValue bound 0) (emptyValue 0) (initiallyEmpty bound))

theorem empty_material_has_no_members (stage : Nat) (value : HSet.{0}) :
    ¬ value ∈ HSet.mk (picture Nat (emptyValue stage)) := by
  rintro ⟨child, available, _⟩
  exact available

def laterChild (bound : Nat) : Child Nat (delayedValue bound (bound+1)) :=
  ⟨true, rfl, rfl, Nat.lt_succ_self bound⟩

theorem later_material_has_member (bound : Nat) :
    HSet.mk (picture Nat (childValue Nat (delayedValue bound (bound+1)) (laterChild bound))) ∈
      HSet.mk (picture Nat (delayedValue bound (bound+1))) :=
  material_membership (ContextualRealizedGraphs.Member.atChild
    (delayedValue bound (bound+1)) (laterChild bound))

theorem later_material_differs (bound : Nat) :
    HSet.mk (picture Nat (delayedValue bound (bound+1))) ≠
      HSet.mk (picture Nat (emptyValue (bound+1))) := by
  intro same
  have available := later_material_has_member bound
  rw [same] at available
  exact empty_material_has_no_members (bound+1) _ available

theorem initial_agreement_does_not_reflect_future_matching (bound : Nat) :
    ¬ Nonempty (ContextualRealizedGraphs.Equal (delayedValue bound 0) (emptyValue 0)) := by
  rintro ⟨proof⟩
  let response := ContextualGraphRealizers.Realizer.forth proof
    ⟨bound+1, homOfLE (Nat.zero_le (bound+1))⟩ (laterChild bound)
  exact response.1.property

theorem unbounded_readout_control (bound : Nat) :
    HSet.mk (picture Nat (delayedValue bound 0)) = HSet.mk (picture Nat (emptyValue 0)) ∧
      ¬ Nonempty (ContextualRealizedGraphs.Equal (delayedValue bound 0) (emptyValue 0)) ∧
      HSet.mk (picture Nat (delayedValue bound (bound+1))) ≠
        HSet.mk (picture Nat (emptyValue (bound+1))) :=
  ⟨initial_material_agreement bound,
    initial_agreement_does_not_reflect_future_matching bound, later_material_differs bound⟩

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphCurrentMaterial
