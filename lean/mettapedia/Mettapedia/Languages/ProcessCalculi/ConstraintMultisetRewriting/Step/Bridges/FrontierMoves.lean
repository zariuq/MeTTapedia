import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierNames
import Mathlib.Data.Fintype.Card

/-!
# A source move produces exactly the live named children

The source move may produce several alternatives, including dead ones. Its
live child bag is precisely the projection of all enabled named successors.
This is the scope-counter seam: every such successor carries the one world
chosen by the full source move. Other frontier members can then be transported
along the source world's increasing scope.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierMoves

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives
open Classical

variable {S : Signature} {Γ : Ctx S} {star : S.Srt}
  {κ : Keys S} {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}
  {supply : Nat → Term S Γ star}

theorem subtype_names {α : Type*} (p : α → Prop) [Fintype {x // p x}]
    (names : Multiset α) (nodup : names.Nodup) (covers : ∀ x, x ∈ names ↔ p x) :
    (Finset.univ.val : Multiset {x // p x}).map Subtype.val = names := by
  apply (Multiset.Nodup.ext (Multiset.Nodup.map Subtype.val_injective Finset.univ.nodup) nodup).mpr
  intro name
  constructor
  · rintro member
    obtain ⟨choice, _, same⟩ := Multiset.mem_map.mp member
    exact (covers name).mpr (same ▸ choice.2)
  · intro member
    exact Multiset.mem_map.mpr ⟨⟨name, (covers name).mp member⟩, Finset.mem_univ _, rfl⟩

theorem source_children {world nextWorld : World κ Γ star} {branch : Branch κ Γ star D.Ty}
    {branches : Multiset (Branch κ Γ star D.Ty)}
    (plain : PlainBranch branch) (live : Solvable branch.store)
    (move : Move D P supply world branch nextWorld branches) :
    (Frontier.children (HostedEvents.sourceSystem (D := D) P) (world, branch)).map Prod.snd =
        branches.filter (fun child => Solvable child.store) ∧
      ∀ child ∈ Frontier.children (HostedEvents.sourceSystem (D := D) P) (world, branch), child.1 = nextWorld := by
  classical
  obtain ⟨names, child, nodup, branchesEq, named, unique, _, _⟩ := move_names plain live move
  let liveNames : Multiset RuleName := (names : Multiset RuleName).filter fun name => Solvable (child name).store
  have enabled : ∀ name, name ∈ liveNames ↔ HostedEvents.sourceEnabled (D := D) P (world, branch) name := by
    intro name
    simp only [liveNames, Multiset.mem_filter, Multiset.mem_coe]
    constructor
    · rintro ⟨inside, alive⟩
      exact ⟨(nextWorld, child name), named name inside, alive⟩
    · rintro ⟨⟨next, result⟩, moved, alive⟩
      obtain ⟨inside, _, same⟩ := unique name next result moved
      exact ⟨inside, same ▸ alive⟩
  let : Fintype {name : RuleName // HostedEvents.sourceEnabled (D := D) P (world, branch) name} :=
    FrontierNames.sourceChoices (D := D) P (world, branch)
  have labels :
      (Finset.univ.val : Multiset ((HostedEvents.sourceSystem (D := D) P).Choice (world, branch))).map Subtype.val =
        liveNames := subtype_names (HostedEvents.sourceEnabled (D := D) P (world, branch)) liveNames
          (Multiset.Nodup.filter _ (Multiset.coe_nodup.mpr nodup)) enabled
  have nextOf : ∀ choice : (HostedEvents.sourceSystem (D := D) P).Choice (world, branch),
      (HostedEvents.sourceSystem (D := D) P).next (world, branch) choice = (nextWorld, child choice.1) := by
    intro choice
    have moved := HostedEvents.source_next_spec P (world, branch) choice
    obtain ⟨_, sameWorld, sameBranch⟩ := unique choice.1 _ _ moved.1
    exact Prod.ext sameWorld sameBranch
  have allChildren : Frontier.children (HostedEvents.sourceSystem (D := D) P) (world, branch) =
      liveNames.map (fun name => (nextWorld, child name)) := by
    unfold Frontier.children
    rw [← labels, Multiset.map_map]
    exact Multiset.map_congr rfl (fun choice _ => nextOf choice)
  constructor
  · rw [allChildren, Multiset.map_map, branchesEq, ← Multiset.map_coe, Multiset.filter_map]
    rfl
  · intro result member
    rw [allChildren] at member
    obtain ⟨name, _, rfl⟩ := Multiset.mem_map.mp member
    rfl

theorem source_empty_iff_fail {world nextWorld : World κ Γ star} {branch : Branch κ Γ star D.Ty}
    {branches : Multiset (Branch κ Γ star D.Ty)}
    (plain : PlainBranch branch) (live : Solvable branch.store)
    (move : Move D P supply world branch nextWorld branches) :
    Fintype.card ((HostedEvents.sourceSystem (D := D) P).Choice (world, branch)) = 0 ↔
      branch.focus = .eval .fail := by
  constructor
  · intro noChoices
    obtain ⟨names, child, _, _, named, _, failed, someLive⟩ := move_names plain live move
    apply failed
    by_contra nonempty
    obtain ⟨name, inside, alive⟩ := someLive nonempty
    let choice : (HostedEvents.sourceSystem (D := D) P).Choice (world, branch) :=
      ⟨name, (nextWorld, child name), named name inside, alive⟩
    exact (Fintype.card_eq_zero_iff.mp noChoices).false choice
  · intro failing
    apply Fintype.card_eq_zero_iff.mpr
    constructor
    rintro ⟨name, ⟨next, moved, _⟩⟩
    rcases branch with ⟨store, focus, frames, pending⟩
    simp only at failing
    subst focus
    cases moved

theorem related_world_mono (N : Nodes S Γ star) (q : Comp κ Γ star D.Ty)
    {world nextWorld : World κ Γ star} {branch : Branch κ Γ star D.Ty} {word : List RuleName}
    (related : HostedEvents.Related N P q (world, branch) word) (scope : world.scope ≤ nextWorld.scope) :
    HostedEvents.Related N P q (nextWorld, branch) word where
  plain := related.plain
  live := related.live
  reached := related.reached
  uniform := fun state active history => (related.uniform state active history).mono N scope

/-- The target's native enabled-name bag relates to the full move's live children,
all at its updated global world. -/
theorem target_children (N : Nodes S Γ star) (q : Comp κ Γ star D.Ty) (plainP : PlainProgram P)
    {world nextWorld : World κ Γ star} {branch : Branch κ Γ star D.Ty}
    {branches : Multiset (Branch κ Γ star D.Ty)} {word : List RuleName}
    (related : HostedEvents.Related N P q (world, branch) word)
    (move : Move D P supply world branch nextWorld branches) :
    Multiset.Rel (fun child history => HostedEvents.Related N P q (nextWorld, child) history)
      (branches.filter fun child => Solvable child.store)
      (Frontier.children (HostedEvents.targetSystem (D := D) N P q) word) := by
  obtain ⟨branchBag, worlds⟩ := source_children related.plain related.live move
  rw [← branchBag, Multiset.rel_map_left]
  apply (Frontier.children_related (HostedEvents.bisimulation plainP) related).mono
  intro child member history _ paired
  have same : child = (nextWorld, child.2) := Prod.ext (worlds child member) rfl
  exact same ▸ paired

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierMoves

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierMoves.source_children
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierMoves.source_empty_iff_fail
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierMoves.target_children
