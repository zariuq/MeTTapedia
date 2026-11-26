import Mettapedia.Machines.TIsa.Derivation.OpeningRenaming
import Mettapedia.Machines.TIsa.Derivation.OpeningAction
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.StartPrivacy
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Renaming
import Mathlib.Data.List.Perm.Basic

/-!
# Reopening a round preserves its serial tests

Use a single change of coordinates throughout the serial execution:
one permutation for logical unknowns and one for physical occurrences.
Only the rule's opened terms matter; the authored rule and its meaning
stay fixed. The original store is fixed up to its observable contents.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SerialReopening

open Mettapedia.Logic.LP
open UnificationRenaming (rename rename_leftInverse)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)
open RuleSyntax.OneFrame (Terms)
open RuleSyntax.JointFirings (bagOf)
open RuleSyntax.StepWeb.Rounds (FiresInOrder stateAfter RuntimeRound)
open SymbolicFiring (World LiveWorld act)
open SymbolicJointReopening (Same)
open OpeningAction (Member SameAction)

universe u p
variable {σ : LPSignature.{u, u, p, u}} {program : RuleSyntax.Program (Terms (Term σ))}

private abbrev A := FirstOrder.action σ

def unknowns (π : Equiv.Perm σ.vars) : RuleSyntax.Scope.Renaming (A (σ := σ)) where
  forward := fun v => .var (π v)
  backward := fun v => .var (π.symm v)
  back_forward := rename_leftInverse π π.symm π.symm_apply_apply
  forward_back := rename_leftInverse π.symm π π.apply_symm_apply
  compose_back θ := funext fun v => rename_leftInverse π.symm π π.apply_symm_apply (θ v)
  compose_forward θ := funext fun v => rename_leftInverse π π.symm π.symm_apply_apply (θ v)

def renamedState (π : Equiv.Perm σ.vars) (ι : Equiv.Perm ℕ) (source : World σ ℕ) : World σ ℕ :=
  RuleSyntax.Equivalence.renameState ι (RuleSyntax.Scope.renameState (unknowns π) source)

def renamedMember (π : Equiv.Perm σ.vars) (ι : Equiv.Perm ℕ) (m : Member σ ℕ program) : Member σ ℕ program :=
  RuleSyntax.JointFirings.Member.ofFiring
    (RuleSyntax.Equivalence.renameFiring ι (RuleSyntax.Scope.renameFiring (unknowns π) m.firing))

private theorem renamed_firing (π : Equiv.Perm σ.vars) (ι : Equiv.Perm ℕ) (m : Member σ ℕ program) :
    (renamedMember π ι m).firing =
      RuleSyntax.Equivalence.renameFiring ι (RuleSyntax.Scope.renameFiring (unknowns π) m.firing) := by
  cases m
  rfl

theorem step_renamed (π : Equiv.Perm σ.vars) (ι : Equiv.Perm ℕ) (m : Member σ ℕ program) (s : World σ ℕ) :
    ((renamedMember π ι m).firing.Admits (act σ) (renamedState π ι s) ↔ m.firing.Admits (act σ) s) ∧
      (renamedMember π ι m).firing.result (act σ) (renamedState π ι s) =
        renamedState π ι (m.firing.result (act σ) s) := by
  rw [renamed_firing]
  unfold renamedState
  exact ⟨(RuleSyntax.Equivalence.admits_renameFiring (act σ) ι _).trans
      (RuleSyntax.Scope.admits_rename_iff (unknowns π) m.firing s),
    (RuleSyntax.Equivalence.result_renameFiring (act σ) ι _).trans
      (congrArg (RuleSyntax.Equivalence.renameState ι) (RuleSyntax.Scope.result_rename (unknowns π) m.firing s))⟩

theorem sequence_renamed (π : Equiv.Perm σ.vars) (ι : Equiv.Perm ℕ)
    (members : List (Member σ ℕ program)) (s : World σ ℕ) :
    (FiresInOrder A (renamedState π ι s) (members.map (renamedMember π ι)) ↔ FiresInOrder A s members) ∧
      stateAfter A (renamedState π ι s) (members.map (renamedMember π ι)) = renamedState π ι (stateAfter A s members) := by
  induction members generalizing s with
  | nil => exact ⟨Iff.rfl, rfl⟩
  | cons first rest ih =>
    obtain ⟨allowed, result⟩ := step_renamed π ι first s
    obtain ⟨after, endState⟩ := ih (first.firing.result (act σ) s)
    simp only [List.map_cons, FiresInOrder, stateAfter, result]
    exact ⟨and_congr allowed after, endState⟩

private theorem finite_set_fixed (allowed : Finset ℕ) (ι : Equiv.Perm ℕ)
    (fixed : ∀ i ∈ allowed, ι i = i) (seen : Finset ℕ) (contained : seen ⊆ allowed) :
    seen.map ι.toEmbedding = seen := by
  ext i
  constructor
  · intro found
    obtain ⟨j, inside, eq⟩ := Finset.mem_map.mp found
    change ι j = i at eq
    exact (fixed j (contained inside)).symm.trans eq ▸ inside
  · intro inside
    exact Finset.mem_map.mpr ⟨i, inside, fixed i (contained inside)⟩

private theorem physical_fixed (source : World σ ℕ) (ι : Equiv.Perm ℕ)
    (fixed : ∀ i ∈ source.present, ι i = i) :
    RuleSyntax.Scope.Congruent (RuleSyntax.Equivalence.renameState ι source) source := by
  have sets := finite_set_fixed source.present ι fixed source.present (fun _ h => h)
  refine ⟨fun _ => Iff.rfl, sets, fun i live => ?_⟩
  change source.label (ι.symm i) = source.label i
  have stable : ι i = i := fixed i (sets ▸ live)
  rw [← stable, Equiv.symm_apply_apply, stable]

theorem entry_fixed (s : World σ ℕ) (π : Equiv.Perm σ.vars) (ι : Equiv.Perm ℕ)
    (terms : ∀ term, s.Mentions term → rename π term = term)
    (occurrences : ∀ occurrence ∈ s.present, ι occurrence = occurrence) :
    RuleSyntax.Scope.Congruent (renamedState π ι s) s :=
  (physical_fixed (RuleSyntax.Scope.renameState (unknowns π) s) ι occurrences).trans
    (RuleSyntax.Scope.renameState_congruent_of_fixed (unknowns π) terms)

private theorem congruent_sequence {s t : World σ ℕ} (same : RuleSyntax.Scope.Congruent s t)
    (members : List (Member σ ℕ program)) (ran : FiresInOrder A s members) :
    FiresInOrder A t members ∧ RuleSyntax.Scope.Congruent (stateAfter A s members) (stateAfter A t members) := by
  induction members generalizing s t with
  | nil => exact ⟨ran, same⟩
  | cons first rest ih =>
    obtain ⟨next, tail⟩ := ran
    have related := RuleSyntax.Scope.result_congruent same next
    obtain ⟨ran, related⟩ := ih related tail
    exact ⟨⟨RuleSyntax.Scope.admits_of_congruent same next, ran⟩, related⟩

private theorem aligned_action (s : World σ ℕ) (π : Equiv.Perm σ.vars) (ι : Equiv.Perm ℕ)
    (fixed : ∀ i ∈ s.present, ι i = i) {left right : Member σ ℕ program}
    (same : Same s left right)
    (terms : ∀ term ∈ left.rule.terms, rename π (left.opening.applyTerm term) = right.opening.applyTerm term)
    (outputs : left.selection.made.map ι = right.selection.made)
    (enabled : Enabled (fun _ : ℕ => ()) s.present (left.selection.commit (T := Unit)))
    (collects : ∀ seen ∈ left.seen, seen ⊆ s.present) :
    SameAction (renamedMember π ι left) right := by
  refine ⟨same.rule, ?_, ?_, ?_⟩
  · have taken : left.selection.taken.map ι = right.selection.taken := by
      rw [← same.taken]
      conv_rhs => rw [← List.map_id left.selection.taken]
      apply List.map_congr_left
      exact fun i inside => fixed i (enabled.taken_subset (List.mem_toFinset.mpr inside))
    have read : left.selection.read.map ι = right.selection.read := by
      rw [← same.read]
      conv_rhs => rw [← List.map_id left.selection.read]
      apply List.map_congr_left
      exact fun i inside => fixed i (enabled.kept_subset (List.mem_toFinset.mpr inside))
    change (⟨left.selection.taken.map ι, left.selection.read.map ι, left.selection.made.map ι⟩ : Selection ℕ) =
      right.selection
    rw [taken, read, outputs]
  · change left.seen.map (Finset.map ι.toEmbedding) = right.seen
    have claims : left.seen = right.seen := same.seen
    rw [← claims]
    conv_rhs => rw [← List.map_id left.seen]
    exact List.map_congr_left (fun seen belongs => finite_set_fixed _ ι fixed seen (collects seen belongs))
  · intro term inside
    change right.opening.applyTerm term = (A.compose (unknowns π).forward left.opening).applyTerm term
    exact (terms term inside).symm.trans ((A (σ := σ)).apply_compose _ _ term).symm

/-- One pairing suffices for every order. In particular a serial guard
which fails after a tell cannot be rescued by selecting more convenient
fresh names for the two members separately. -/
theorem round [DecidableEq σ.vars] (before : LiveWorld σ)
    {left right : List (Member σ ℕ program)}
    (paired : List.Forall₂ (Same before.state) left right)
    (original : RuntimeRound A before.state left)
    (fits : (bagOf A right).Fits (act σ) before.state)
    (enabled : Enabled (fun _ : ℕ => ()) before.state.present ((bagOf A right).selection.commit (T := Unit)))
    (collects : ∀ m ∈ left, ∀ seen ∈ m.seen, seen ⊆ before.state.present) :
    RuntimeRound A before.state right := by
  obtain ⟨π, fixedTerms, renamedTerms⟩ := OpeningRenaming.variable_permutation before paired original.1.1.1 fits.1
  obtain ⟨ι, fixedOccurrences, renamedOutputs⟩ := OpeningRenaming.occurrence_permutation
    before paired original.1.1 fits original.1.2.1 enabled
  have entry := entry_fixed before.state π ι fixedTerms fixedOccurrences
  have sameActions : List.Forall₂ SameAction (left.map (renamedMember π ι)) right := by
    refine List.forall₂_map_left_iff.mpr ?_
    have common : List.Forall₂ (fun l r => Same before.state l r ∧
        (∀ term ∈ l.rule.terms, rename π (l.opening.applyTerm term) = r.opening.applyTerm term) ∧
        l.selection.made.map ι = r.selection.made) left right :=
      renamedTerms.mp (fun _ _ h outputs => ⟨h.1, h.2, outputs⟩) renamedOutputs
    suffices ∀ {ls rs : List (Member σ ℕ program)}, ls ⊆ left →
        List.Forall₂ (fun l r => Same before.state l r ∧
          (∀ term ∈ l.rule.terms, rename π (l.opening.applyTerm term) = r.opening.applyTerm term) ∧
          l.selection.made.map ι = r.selection.made) ls rs →
        List.Forall₂ (fun l r => SameAction (renamedMember π ι l) r) ls rs from this (fun _ h => h) common
    intro ls rs subset related
    induction related with
    | nil => exact .nil
    | @cons l r ls rs head tail ih =>
      have inside : l ∈ left := subset List.mem_cons_self
      exact .cons (aligned_action before.state π ι fixedOccurrences head.1 head.2.1 head.2.2
        (RuleSyntax.JointFirings.Bag.enabled_member original.1.2.1 inside) (collects l inside))
        (ih (fun _ h => subset (List.mem_cons_of_mem _ h)))
  apply RuleSyntax.StepWeb.Rounds.runtimeRound_of_fires A
    (SymbolicJointReopening.admits_own paired (RuleSyntax.StepWeb.Rounds.admitsOwn_of_runtimeRound A original) fits enabled)
  intro ordered permutation
  have actions : List.Forall₂ (fun l r => SameAction (renamedMember π ι l) r) left right :=
    List.forall₂_map_left_iff.mp sameActions
  obtain ⟨source, actions', perm⟩ := List.perm_comp_forall₂ permutation actions.flip
  have serial := (original.2 source perm).1
  have asRenamed := (sequence_renamed π ι source before.state).1.mpr serial
  have asEntry := (congruent_sequence entry _ asRenamed).1
  exact (OpeningAction.sequence_exact (List.forall₂_map_left_iff.mpr actions'.flip) before.state).1.mp asEntry

end Mettapedia.Machines.TIsa.Derivation.SerialReopening
