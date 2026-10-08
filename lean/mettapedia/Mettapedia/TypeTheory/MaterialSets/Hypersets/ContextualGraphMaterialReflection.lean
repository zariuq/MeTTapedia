import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphCurrentMaterial

/-!
# Pointwise material agreement does not supply future matching

Two graph diagrams have equal material pictures at every natural stage.
Initially one root has two childless occurrences and the other has one.
At later stages the second diagram acquires the missing occurrence and
one of those occurrences acquires a member. Each separate material
picture agrees, but the initially available matching response cannot
follow the occurrence whose future changes.

The counterexample concerns full future matching existence, not only
faithful recovery of proof receipts. The diagrams and all matching trees
are constructed without selection from propositional bisimilarity.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialReflection

open CategoryTheory ContextualGraphDiagrams ContextualGraphCurrentMaterial

inductive Node
  | root
  | old
  | late

inductive Edge (early : Bool) (stage : Nat) : Node → Node → Prop
  | old : Edge early stage .root .old
  | late (available : early = true ∨ 0 < stage) : Edge early stage .root .late
  | grows (positive : 0 < stage) : Edge early stage .late .old

def diagram (early : Bool) : Diagram Nat where
  nodes := {
    obj _ := Node
    map _ := TypeCat.ofHom id
    map_id _ := rfl
    map_comp _ _ := rfl }
  edge := Edge early
  edge_transport := by
    intro first second arrival parent child available
    cases available with
    | old => exact Edge.old
    | late ready => exact Edge.late (ready.elim Or.inl
        (fun positive => Or.inr (Nat.lt_of_lt_of_le positive (leOfHom arrival))))
    | grows positive => exact Edge.grows (Nat.lt_of_lt_of_le positive (leOfHom arrival))

def value (early : Bool) (stage : Nat) : Value Nat stage := ⟨diagram early, .root⟩

theorem zero_leaf_childless (early : Bool) {parent child : Node}
    (notRoot : parent ≠ .root) (available : Edge early 0 parent child) : False := by
  cases available with
  | old => exact notRoot rfl
  | late _ => exact notRoot rfl
  | grows positive => exact Nat.not_lt_zero 0 positive

inductive InitialPair : Node → Node → Type
  | roots : InitialPair .root .root
  | leaves (first second : Node) (firstNotRoot : first ≠ .root)
      (secondNotRoot : second ≠ .root) : InitialPair first second

def initialStep (first second : Node) (proof : InitialPair first second) :
    GraphBisimulationRealizers.Layer (Edge true 0) (Edge false 0) InitialPair first second := by
  cases proof with
  | roots =>
    refine ⟨?_, ?_⟩
    · rintro ⟨child, available⟩
      cases child with
      | root => exact False.elim (by cases available)
      | old => exact ⟨⟨.old, Edge.old⟩, InitialPair.leaves .old .old (by intro h; cases h) (by intro h; cases h)⟩
      | late => exact ⟨⟨.old, Edge.old⟩, InitialPair.leaves .late .old (by intro h; cases h) (by intro h; cases h)⟩
    · rintro ⟨child, available⟩
      cases child with
      | root => exact False.elim (by cases available)
      | old => exact ⟨⟨.old, Edge.old⟩, InitialPair.leaves .old .old (by intro h; cases h) (by intro h; cases h)⟩
      | late => exact False.elim (by
          cases available with
          | late ready => exact ready.elim (fun impossible => by cases impossible) (Nat.not_lt_zero 0))
  | leaves first second firstNotRoot secondNotRoot =>
    exact ⟨fun child => False.elim (zero_leaf_childless true firstNotRoot child.property),
      fun child => False.elim (zero_leaf_childless false secondNotRoot child.property)⟩

def initialMatching : GraphBisimulationRealizers.Realizer (Edge true 0) (Edge false 0) .root .root :=
  GraphBisimulationRealizers.corec (Edge true 0) (Edge false 0) initialStep InitialPair.roots

theorem positive_edge {first second : Bool} {stage : Nat} (positive : 0 < stage)
    {parent child : Node} (available : Edge first stage parent child) :
    Edge second stage parent child := by
  cases available with
  | old => exact Edge.old
  | late _ => exact Edge.late (Or.inr positive)
  | grows later => exact Edge.grows later

def positiveMatching (stage : Nat) (positive : 0 < stage) :
    GraphBisimulationRealizers.Realizer (Edge true stage) (Edge false stage) .root .root :=
  GraphBisimulationRealizers.Realizer.ofMap (left := Edge true stage) (right := Edge false stage) id
    (fun _ _ available => positive_edge positive available)
    (fun _ child => ⟨⟨child.val, positive_edge positive child.property⟩, rfl⟩) Node.root

def stageMatching : (stage : Nat) →
    GraphBisimulationRealizers.Realizer (Edge true stage) (Edge false stage) .root .root
  | 0 => initialMatching
  | stage+1 => positiveMatching (stage+1) (Nat.zero_lt_succ stage)

theorem all_stage_material_agreement (stage : Nat) :
    HSet.mk (picture Nat (value true stage)) = HSet.mk (picture Nat (value false stage)) :=
  GraphRealizedIdentityBoundary.materialEquality
    (pictureMatching (value true stage) (value false stage) (stageMatching stage))

theorem no_late_old_future_matching (stage : Nat) :
    ¬ Nonempty (ContextualGraphRealizers.Realizer (diagram true) (diagram false) stage .late .old) := by
  rintro ⟨proof⟩
  let response := ContextualGraphRealizers.Realizer.forth proof
    ⟨stage+1, homOfLE (Nat.le_succ stage)⟩ ⟨.old, Edge.grows (Nat.zero_lt_succ stage)⟩
  have impossible : Edge false (stage+1) .old response.1.val := response.1.property
  cases impossible

theorem no_full_future_matching :
    ¬ Nonempty (ContextualRealizedGraphs.Equal (value true 0) (value false 0)) := by
  rintro ⟨proof⟩
  let response := ContextualGraphRealizers.Realizer.forth proof ⟨0, 𝟙 0⟩
    ⟨.late, Edge.late (Or.inl rfl)⟩
  rcases response with ⟨⟨child, available⟩, continued⟩
  cases available with
  | old => exact no_late_old_future_matching 0 ⟨continued⟩
  | late ready => exact ready.elim (fun impossible => by cases impossible) (Nat.not_lt_zero 0)

/-- Even agreement of all current material pictures cannot be promoted
to persistent matching existence. -/
theorem pointwise_material_does_not_reflect :
    (∀ stage, HSet.mk (picture Nat (value true stage)) =
      HSet.mk (picture Nat (value false stage))) ∧
      ¬ Nonempty (ContextualRealizedGraphs.Equal (value true 0) (value false 0)) :=
  ⟨all_stage_material_agreement, no_full_future_matching⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialReflection
