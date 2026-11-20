import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierArrowSteps
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierArrowMoves

/-!
# Native expansions deliver precisely an arrow move's live child bag

The result holds for every supplied complete expansion at the actual native
representative. It never chooses one preferred representative and does not
assume that a nonempty source child bag contains a live child.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives
open Classical

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S} {D : Discipline S Γ star}
  (N : Nodes S Γ star) (P : SourceLanguage.Program κ Γ star D.Ty)
  {supply : Nat → Term S Γ star}

def LeafRep (world : World κ Γ star) (branch : Branch κ Γ star D.Ty) (leaf : Leaf S) : Prop :=
  Hosting.Represents N P world.scope branch leaf.state leaf.active ∧ ArrowBranch branch

theorem LeafRep.mono {world nextWorld : World κ Γ star} {branch : Branch κ Γ star D.Ty}
    {leaf : Leaf S} (paired : LeafRep N P world branch leaf) (scope : world.scope ≤ nextWorld.scope) :
    LeafRep N P nextWorld branch leaf := ⟨paired.1.mono N scope, paired.2⟩

theorem live_iff {world : World κ Γ star} {branch : Branch κ Γ star D.Ty} {leaf : Leaf S}
    (paired : LeafRep N P world branch leaf) :
    Solvable branch.store ↔ (Interface.Frames.contextual S).Solvable leaf.state.knowledge := by
  constructor
  · rintro ⟨names, arity, assignment, solved⟩
    let frame : Interface.Frames.Frame S := ⟨names, arity⟩
    have read : branchReads N branch frame (observe (encBranch N (instantiate assignment) branch)) :=
      ⟨assignment, solved, rfl⟩
    obtain ⟨native, known, _⟩ := (paired.1.reads frame _).mpr read
    exact ⟨frame, native, known⟩
  · rintro ⟨frame, native, known⟩
    obtain ⟨assignment, solved, _⟩ := (paired.1.reads frame _).mp ⟨native, known, rfl⟩
    exact ⟨frame.Names, frame.arity, assignment, solved⟩

theorem valid {world : World κ Γ star} {branch : Branch κ Γ star D.Ty} {leaf : Leaf S}
    (paired : LeafRep N P world branch leaf) (live : Solvable branch.store) :
    FrontierNativeCore.Valid leaf := by
  refine ⟨?_, (live_iff N P paired).mp live⟩
  rw [paired.1.present]
  exact Finset.mem_insert_self _ _

theorem invocation_reflect (arrowP : ArrowProgram P)
    {world : World κ Γ star} {branch : Branch κ Γ star D.Ty} {leaf : Leaf S} {name : Name}
    (paired : LeafRep N P world branch leaf) (hygienic : Hygienic branch)
    (invocation : Invocation N P leaf name) :
    ∃ nextWorld child, NamedMove P world branch name nextWorld child ∧
      LeafRep N P nextWorld child invocation.after ∧ Solvable child.store := by
  obtain ⟨nextWorld, child, named, represented, arrow⟩ :=
    reflection N arrowP paired.1 paired.2 hygienic invocation.fires
  have paired' : LeafRep N P nextWorld child invocation.after := ⟨represented, arrow⟩
  exact ⟨nextWorld, child, named, paired', (live_iff N P paired').mpr invocation.admitted.2.2.1⟩

theorem named_enabled (arrowP : ArrowProgram P)
    {world nextWorld : World κ Γ star} {branch child : Branch κ Γ star D.Ty} {leaf : Leaf S} {name : Name}
    (paired : LeafRep N P world branch leaf) (hygienic : Hygienic branch)
    (named : NamedMove P world branch name nextWorld child) (live : Solvable child.store) :
    Enabled N P leaf name := by
  obtain ⟨next, fired, _, _⟩ := simulation N arrowP named paired.1 paired.2 hygienic live (freshId_not_mem leaf.state)
  obtain ⟨invocation, _⟩ := FrontierNativeCore.invocation_of_fires (catalogue N P)
    (before := leaf) (after := ⟨next, freshId leaf.state⟩) fired
  exact ⟨invocation⟩

theorem children_related (arrowP : ArrowProgram P)
    {world nextWorld : World κ Γ star} {branch : Branch κ Γ star D.Ty} {leaf : Leaf S}
    {branches : Multiset (Branch κ Γ star D.Ty)}
    (paired : LeafRep N P world branch leaf) (hygienic : Hygienic branch)
    (move : Move D P supply world branch nextWorld branches) (chosen : Expansion N P leaf) :
    Multiset.Rel (LeafRep N P nextWorld)
      (branches.filter fun child => Solvable child.store) chosen.children := by
  classical
  obtain ⟨ns, child, nodup, branchesEq, named, unique⟩ := move_names paired.2 move
  have eligible : ∀ name, Enabled N P leaf name ↔ name ∈ ns ∧ Solvable (child name).store := by
    intro name
    constructor
    · rintro ⟨invocation⟩
      obtain ⟨next, result, moved, _, live⟩ := invocation_reflect N P arrowP paired hygienic invocation
      obtain ⟨member, _, same⟩ := unique name next result moved
      exact ⟨member, same ▸ live⟩
    · rintro ⟨member, live⟩
      exact named_enabled N P arrowP paired hygienic (named name member) live
  have labels : chosen.names.val = (ns : Multiset Name).filter (fun name => Solvable (child name).store) := by
    apply (Multiset.Nodup.ext chosen.names.nodup (Multiset.Nodup.filter _ (Multiset.coe_nodup.mpr nodup))).mpr
    intro name
    change name ∈ chosen.names ↔ _
    rw [chosen.complete]
    simpa only [Multiset.mem_filter, Multiset.mem_coe] using eligible name
  have bag : branches.filter (fun child => Solvable child.store) = chosen.names.val.map child := by
    rw [labels, branchesEq, ← Multiset.map_coe, Multiset.filter_map]
    rfl
  have attach : chosen.names.attach.val.map Subtype.val = chosen.names.val := Multiset.attach_map_val _
  rw [← attach, Multiset.map_map] at bag
  rw [bag, FrontierNativeCore.Expansion.children]
  apply Multiset.rel_map.mpr
  apply Multiset.rel_refl_of_refl_on
  intro name _
  obtain ⟨next, result, moved, represented, _⟩ :=
    invocation_reflect N P arrowP paired hygienic (chosen.invocation name.1 name.2)
  obtain ⟨_, rfl, rfl⟩ := unique name.1 next result moved
  exact represented

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow
