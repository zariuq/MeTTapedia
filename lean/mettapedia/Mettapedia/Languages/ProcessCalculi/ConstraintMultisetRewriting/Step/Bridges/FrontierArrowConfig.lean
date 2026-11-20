import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierArrowChildren
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierConfig

/-!
# Whole scoped arrow configurations and the common native controller

Source reachability is ghost evidence used to derive frame hygiene. The
native controller stores only actual native leaves and takes no source-step
premise. A certified empty expansion retires either explicit failure or a
rejected pattern bind. A suspended probe supplies no such certificate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open SourceLanguage Hosting Hosting.Alternatives
open Classical

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S} {D : Discipline S Γ star}
  (N : Nodes S Γ star) (P : SourceLanguage.Program κ Γ star D.Ty)
  (supply : Nat → Term S Γ star) (spaces : Term S Γ star → Multiset (Row κ Γ star))
  (q : Comp κ Γ star D.Ty)

def Retired (old : Multiset (Leaf S)) : Prop := ∀ leaf ∈ old,
  FrontierNativeCore.Valid leaf ∧ ¬ StateFinished N leaf.state leaf.active ∧
    ∀ name, ¬ Enabled N P leaf name

structure Representation (configuration : Config κ Γ star D.Ty) (frontier : State S) : Prop where
  reached : Runs D P supply (Config.initial spaces q) configuration
  leaves : Multiset.Rel (LeafRep N P configuration.world)
    (configuration.branches.filter fun branch => Solvable branch.store) frontier.leaves
  retired : Retired N P frontier.retired

abbrev source := FrontierConfig.source P supply

theorem retire_valid {before : Leaf S} (chosen : Expansion N P before)
    {old : Multiset (Leaf S)} (previous : Retired N P old)
    (valid : FrontierNativeCore.Valid before) (unfinished : ¬ StateFinished N before.state before.active) :
    Retired N P (chosen.retire (catalogue N P) old) := by
  unfold FrontierNativeCore.Expansion.retire
  split
  · rename_i empty
    have noNames : chosen.names = ∅ := Finset.card_eq_zero.mp empty
    intro leaf member
    rcases Multiset.mem_cons.mp member with rfl | other
    · refine ⟨valid, unfinished, fun name enabled => ?_⟩
      have member := (chosen.complete name).mpr enabled
      rw [noNames] at member
      simp at member
    · exact previous leaf other
  · exact previous

variable
  (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
  {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
  (arrowQ : ArrowComp q)

include equations qScoped qDistinct arrowQ

theorem advance
    {world nextWorld : World κ Γ star} {branch : Branch κ Γ star D.Ty}
    {branches rest : Multiset (Branch κ Γ star D.Ty)}
    {leaf : Leaf S} {others retired : Multiset (Leaf S)}
    (reached : Runs D P supply (Config.initial spaces q) ⟨world, branch ::ₘ rest⟩)
    (paired : LeafRep N P world branch leaf) (live : Solvable branch.store)
    (otherPairs : Multiset.Rel (LeafRep N P world) (rest.filter fun branch => Solvable branch.store) others)
    (previous : Retired N P retired) (move : Move D P supply world branch nextWorld branches)
    (chosen : Expansion N P leaf) :
    Representation N P supply spaces q ⟨nextWorld, branches + rest⟩
      ⟨chosen.children + others, chosen.retire (catalogue N P) retired⟩ := by
  have hygiene := reachableHygienic_of_scoped spaces q equations qScoped qDistinct arrowQ
    _ reached branch (Multiset.mem_cons_self _ _)
  have unfinished : ¬ StateFinished N leaf.state leaf.active := fun finished =>
    FrontierConfig.move_not_finished P supply move ((Hosting.finished_iff N paired.1).mpr finished).1
  refine ⟨reached.tail (.move world nextWorld branch rest branches live move), ?_,
    retire_valid N P chosen previous (valid N P paired live) unfinished⟩
  rw [Multiset.filter_add]
  exact (children_related N P (fun e member => (equations e member).2.2) paired hygiene move chosen).add
    (otherPairs.mono (fun branch _ leaf _ represented => represented.mono N P (Move.scope_le move)))

theorem forward {before after : Config κ Γ star D.Ty} {current : State S}
    (represented : Representation N P supply spaces q before current)
    (moved : SourceLanguage.Step D P supply before after) :
    ∃ next, Step N P current next ∧ Representation N P supply spaces q after next := by
  obtain ⟨world, nextWorld, branch, rest, branches, live, move⟩ := moved
  have pairedLeaves := represented.leaves
  rw [Multiset.filter_cons_of_pos (p := fun branch => Solvable branch.store) rest live] at pairedLeaves
  obtain ⟨leaf, others, paired, otherPairs, split⟩ := Multiset.rel_cons_left.mp pairedLeaves
  rcases current with ⟨leaves, retired⟩
  change leaves = leaf ::ₘ others at split
  subst leaves
  let chosen : Expansion N P leaf := FrontierNativeCore.expansion (catalogue N P) leaf
  have unfinished : ¬ StateFinished N leaf.state leaf.active := fun finished =>
    FrontierConfig.move_not_finished P supply move ((Hosting.finished_iff N paired.1).mpr finished).1
  exact ⟨_, FrontierNativeCore.Step.expand leaf others retired (valid N P paired live) unfinished chosen,
    advance N P supply spaces q equations qScoped qDistinct arrowQ represented.reached paired live
      otherPairs represented.retired move chosen⟩

theorem backward {before : Config κ Γ star D.Ty} {current next : State S}
    (represented : Representation N P supply spaces q before current) (moved : Step N P current next) :
    ∃ after, SourceLanguage.Step D P supply before after ∧ Representation N P supply spaces q after next := by
  cases moved with
  | expand leaf others retired validity unfinished chosen =>
    obtain ⟨branch, liveRest, paired, otherPairs, splitLive⟩ := Multiset.rel_cons_right.mp represented.leaves
    have member : branch ∈ before.branches.filter (fun branch => Solvable branch.store) := by
      rw [splitLive]
      exact Multiset.mem_cons_self _ _
    obtain ⟨inSource, live⟩ := Multiset.mem_filter.mp member
    obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem inSource
    have restEq : rest.filter (fun branch => Solvable branch.store) = liveRest := by
      rw [split, Multiset.filter_cons_of_pos (p := fun branch => Solvable branch.store) rest live] at splitLive
      exact (Multiset.cons_inj_right branch).mp splitLive
    rw [← restEq] at otherPairs
    have notFinished : ¬ branch.Finished (D := D) := fun finished =>
      unfinished ((Hosting.finished_iff N paired.1).mp ⟨finished, live⟩)
    obtain ⟨nextWorld, branches, move⟩ := moves (supply := supply) before.world paired.2 notFinished
    have sourceStep : SourceLanguage.Step D P supply before ⟨nextWorld, branches + rest⟩ :=
      SourceLanguage.Step.of_eq split rfl live move
    have reached : Runs D P supply (Config.initial spaces q) ⟨before.world, branch ::ₘ rest⟩ := by
      simpa only [← split] using represented.reached
    exact ⟨_, sourceStep, advance N P supply spaces q equations qScoped qDistinct arrowQ
      reached paired live otherPairs represented.retired move chosen⟩

def correspondence : OperationalCorrespondence (source P supply) (target N P) where
  related := Representation N P supply spaces q
  readStep represented moved := .inr (backward N P supply spaces q equations qScoped qDistinct arrowQ represented moved)
  forward represented moved := by
    obtain ⟨next, step, related⟩ := forward N P supply spaces q equations qScoped qDistinct arrowQ represented moved
    exact ⟨next, ⟨.cons ⟨step⟩ (.refl next)⟩, related⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow
