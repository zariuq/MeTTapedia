import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.WavesOnTheStep

/-!
# Witnessed native execution of jointly compatible rounds

The existing native sequential judgment is reified without choosing a new
firing or solver. Its witness produces a complete run of the actual native
step, retaining every selected occurrence. The existing convex-shadow gluing
theorem therefore yields actual runs in every order. The native hollow cube
has no such witness in any order.

This is the contextual live-row native instance. It does not assert convexity
of arbitrary dependent-unifier solution sets or manufacture higher cells
from pairwise admission alone.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.NativeRoundExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NativeResidual NativeIterated ProofRelevantRuns

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

inductive Witness : (state : NativeState S O Γ sort) → List (LiveFiring state) →
    NativeState S O Γ sort → Type 1 where
  | nil (state : NativeState S O Γ sort) : Witness state [] state
  | cons {state : NativeState S O Γ sort} (first : LiveFiring state) (rest : List (LiveFiring state))
      (accepted : first.toNative.Realized) {last : NativeState S O Γ sort}
      (tail : Witness (native.result first.toNative accepted) (rest.map (residualAfter accepted)) last) :
      Witness state (first :: rest) last

namespace Witness

theorem sequential {state last : NativeState S O Γ sort} {round : List (LiveFiring state)}
    (witness : Witness state round last) : Sequential state round last := by
  induction witness with
  | nil state => exact .nil state
  | cons first rest accepted tail ih => exact .cons first rest accepted ih

theorem nonempty_iff {state last : NativeState S O Γ sort} {round : List (LiveFiring state)} :
    Nonempty (Witness state round last) ↔ Sequential state round last := by
  constructor
  · rintro ⟨witness⟩
    exact witness.sequential
  · intro sequential
    induction sequential with
    | nil state => exact ⟨.nil state⟩
    | cons first rest accepted tail ih =>
        obtain ⟨witness⟩ := ih
        exact ⟨.cons first rest accepted witness⟩

noncomputable def toRun : {state last : NativeState S O Γ sort} → {round : List (LiveFiring state)} →
    Witness state round last → native.toStep.Run state
  | _, _, _, .nil state => .nil state
  | _, _, _, .cons first _ accepted tail => .cons first.toNative accepted tail.toRun

theorem toRun_last {state last : NativeState S O Γ sort} {round : List (LiveFiring state)}
    (witness : Witness state round last) : witness.toRun.last = last := by
  induction witness with
  | nil => rfl
  | cons _ _ _ _ ih => exact ih

theorem selections {state last : NativeState S O Γ sort} {round : List (LiveFiring state)}
    (witness : Witness state round last) :
    witness.toRun.word.map (fun event => event.2.selection) = round.map (fun event => event.selection) := by
  induction witness with
  | nil => rfl
  | cons first rest accepted tail ih =>
      simp only [toRun, Step.Run.word, List.map_cons, ih, List.map_map]
      rfl

theorem event_count {state last : NativeState S O Γ sort} {round : List (LiveFiring state)}
    (witness : Witness state round last) : witness.toRun.word.length = round.length := by
  have lengths := congrArg List.length witness.selections
  simpa only [List.length_map] using lengths

end Witness

theorem every_order_run_of_family {state : NativeState S O Γ sort} {round : List (LiveFiring state)}
    (family : FamilyClear state round) {order : List (LiveFiring state)} (permutation : order.Perm round) :
    ∃ (last : NativeState S O Γ sort) (witness : Witness state order last),
      witness.toRun.last = last ∧ witness.toRun.word.length = round.length ∧
        witness.toRun.word.map (fun event => event.2.selection) = order.map (fun event => event.selection) := by
  obtain ⟨last, sequential⟩ := every_order_admitted family permutation
  obtain ⟨witness⟩ := Witness.nonempty_iff.mpr sequential
  exact ⟨last, witness, witness.toRun_last, witness.event_count.trans permutation.length_eq, witness.selections⟩

theorem every_order_run_of_convex {state : NativeState S O Γ sort} {round : List (LiveFiring state)}
    (admitted : ∀ firing ∈ round, firing.toNative.Realized) (clear : round.Pairwise NativeIterated.Clears)
    (frame : Frames.Frame S)
    (median : Assignment state.state.declarations frame.arity → Assignment state.state.declarations frame.arity →
      Assignment state.state.declarations frame.arity → Assignment state.state.declarations frame.arity)
    (nonempty : round ≠ []) (convex : ∀ firing ∈ round, MedianConvex median (shadow state firing frame))
    (pairwise : ∀ first ∈ round, ∀ second ∈ round, (shadow state first frame ∩ shadow state second frame).Nonempty)
    {order : List (LiveFiring state)} (permutation : order.Perm round) :
    ∃ (last : NativeState S O Γ sort) (witness : Witness state order last),
      witness.toRun.last = last ∧ witness.toRun.word.length = round.length ∧
        witness.toRun.word.map (fun event => event.2.selection) = order.map (fun event => event.selection) := by
  obtain ⟨last, sequential⟩ := every_order_admitted_of_convex admitted clear frame median nonempty convex pairwise permutation
  obtain ⟨witness⟩ := Witness.nonempty_iff.mpr sequential
  exact ⟨last, witness, witness.toRun_last, witness.event_count.trans permutation.length_eq, witness.selections⟩

open NativeIteratedControls in
theorem hollow_cube_has_no_execution {order : List (LiveFiring pair)} (permutation : order.Perm tellers)
    {last : NativeState NativeResidualExample.tiny Nat ([] : Ctx NativeResidualExample.tiny) ()} :
    ¬ Nonempty (Witness pair order last) := by
  rintro ⟨witness⟩
  exact tellers_no_order permutation witness.sequential

open NativeIteratedControls NativeResidualExample in
theorem three_makers_have_actual_runs {order : List (LiveFiring initial)} (permutation : order.Perm makers) :
    ∃ (last : NativeState tiny Nat ([] : Ctx tiny) ()) (witness : Witness initial order last),
      witness.toRun.word.length = 3 ∧
        witness.toRun.word.map (fun event => event.2.selection) = order.map (fun event => event.selection) := by
  obtain ⟨last, witness, _, length, selections⟩ := every_order_run_of_family makers_clear permutation
  exact ⟨last, witness, length, selections⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.NativeRoundExecution

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.NativeRoundExecution.every_order_run_of_convex
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.NativeRoundExecution.hollow_cube_has_no_execution
