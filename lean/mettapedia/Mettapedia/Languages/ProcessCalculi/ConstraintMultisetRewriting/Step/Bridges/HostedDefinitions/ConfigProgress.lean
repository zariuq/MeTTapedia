import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.BranchProgress
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.Data.Multiset.DershowitzManna

/-!
# Finite source configurations retain branch termination

One actual source move replaces one live branch by a finite bag of children.
The multiset extension of their accessible ranks decreases, even when several
children have equal readings. Dead branches cannot run and contribute no
live task. The ordinal ranks are proof evidence, not a runtime counter or a
bound on physical execution cost.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ConfigProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration

local instance closedTerms : ProgramBinders.ClosedTerms MSig where
  closed := fun | () => csym "closed-hole"

variable (rows : List (ProgramBinders.Equation MSig [] ()))
  (D : Discipline MSig [] ()) (supply : Nat → MClosed)

abbrev Descends := BranchProgress.Child rows D supply

def branchRank (branch : Branch (BinderCore.keys rows) [] () D.Ty) : Ordinal := by
  classical
  exact if accessible : Acc (Descends rows D supply) branch then accessible.rank else 0

theorem branchRank_of_acc {branch : Branch (BinderCore.keys rows) [] () D.Ty}
    (accessible : Acc (Descends rows D supply) branch) :
    branchRank rows D supply branch = accessible.rank := by
  classical
  rw [branchRank, dif_pos accessible]

theorem child_rank_lt {before after : Branch (BinderCore.keys rows) [] () D.Ty}
    (accessible : Acc (Descends rows D supply) before) (child : Descends rows D supply after before) :
    branchRank rows D supply after < branchRank rows D supply before := by
  rw [branchRank_of_acc rows D supply (accessible.inv child), branchRank_of_acc rows D supply accessible]
  exact Acc.rank_lt_of_rel accessible child

def Ready (configuration : Config (BinderCore.keys rows) [] () D.Ty) : Prop :=
  ∀ branch ∈ configuration.branches, Solvable branch.store → Acc (Descends rows D supply) branch

def rank (configuration : Config (BinderCore.keys rows) [] () D.Ty) : Multiset Ordinal := by
  classical
  exact (configuration.branches.filter fun branch => Solvable branch.store).map (branchRank rows D supply)

theorem step_ready {before after : Config (BinderCore.keys rows) [] () D.Ty}
    (ready : Ready rows D supply before)
    (step : SourceLanguage.Step D (BinderCore.program rows) supply before after) : Ready rows D supply after := by
  cases step with
  | move world nextWorld branch rest children live moved =>
      have current := ready branch (Multiset.mem_cons_self _ _) live
      intro child member childLive
      rcases Multiset.mem_add.mp member with made | kept
      · exact current.inv ⟨live, world, nextWorld, children, moved, made, childLive⟩
      · exact ready child (Multiset.mem_cons_of_mem kept) childLive

theorem step_rank {before after : Config (BinderCore.keys rows) [] () D.Ty}
    (ready : Ready rows D supply before)
    (step : SourceLanguage.Step D (BinderCore.program rows) supply before after) :
    Multiset.IsDershowitzMannaLT (rank rows D supply after) (rank rows D supply before) := by
  classical
  cases step with
  | move world nextWorld branch rest children live moved =>
      have current := ready branch (Multiset.mem_cons_self _ _) live
      refine ⟨(rest.filter fun b => Solvable b.store).map (branchRank rows D supply),
        (children.filter fun b => Solvable b.store).map (branchRank rows D supply),
        {branchRank rows D supply branch}, by simp, ?_, ?_, ?_⟩
      · simp only [rank, Multiset.filter_add, Multiset.map_add]
        exact add_comm _ _
      · change ((branch ::ₘ rest).filter fun b => Solvable b.store).map (branchRank rows D supply) = _
        rw [Multiset.filter_cons_of_pos (p := fun b => Solvable b.store) rest live, Multiset.map_cons]
        exact (Multiset.singleton_add _ _).symm.trans (add_comm _ _)
      · intro ordinal member
        obtain ⟨child, filtered, rfl⟩ := Multiset.mem_map.mp member
        obtain ⟨made, childLive⟩ := Multiset.mem_filter.mp filtered
        exact ⟨branchRank rows D supply branch, Multiset.mem_singleton_self _,
          child_rank_lt rows D supply current ⟨live, world, nextWorld, children, moved, made, childLive⟩⟩

theorem ready_normalizes (configuration : Config (BinderCore.keys rows) [] () D.Ty)
    (ready : Ready rows D supply configuration) :
    Acc (fun after before => SourceLanguage.Step D (BinderCore.program rows) supply before after) configuration := by
  have all : ∀ score : Multiset Ordinal,
      ∀ configuration : Config (BinderCore.keys rows) [] () D.Ty,
        rank rows D supply configuration = score → Ready rows D supply configuration →
        Acc (fun after before => SourceLanguage.Step D (BinderCore.program rows) supply before after) configuration := by
    intro score
    have wellFounded : WellFounded (Multiset.IsDershowitzMannaLT : Multiset Ordinal → Multiset Ordinal → Prop) :=
      Multiset.wellFounded_isDershowitzMannaLT
    refine wellFounded.induction (C := fun score =>
      ∀ current : Config (BinderCore.keys rows) [] () D.Ty,
        rank rows D supply current = score → Ready rows D supply current →
        Acc (fun after before => SourceLanguage.Step D (BinderCore.program rows) supply before after) current)
      score ?_
    intro score smaller current atScore prepared
    refine .intro current ?_
    intro next edge
    exact smaller (rank rows D supply next) (atScore ▸ step_rank rows D supply prepared edge)
      next rfl (step_ready rows D supply prepared edge)
  exact all (rank rows D supply configuration) configuration rfl ready

theorem initial_normalizes (grounded : ∀ rule ∈ rows, GroundRead.Grounding rule) (call : MClosed)
    (normalizing : Acc (fun after before => ProgramBinders.Rewrites rows.get before after) call) :
    Acc (fun after before => SourceLanguage.Step D (BinderCore.program rows) supply before after)
      (BinderCore.start rows call) := by
  apply ready_normalizes rows D supply
  intro branch member _
  rw [Multiset.mem_singleton.mp member]
  apply BranchProgress.call_normalizes rows D supply grounded call normalizing
  constructor
  · exact ⟨Empty, ProgramBinders.ground MSig, ProgramBinders.close (fam (BinderCore.keys rows)),
      fun _ absent => False.elim (List.not_mem_nil absent)⟩
  · intro X target assignment _
    exact Rigid.instantiate_include assignment call

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ConfigProgress

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ConfigProgress.initial_normalizes
