import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.ResidualPrefixModels

/-!
# Cuts of the supplied native execution witness

Splitting follows the existing witness's constructors and retains its actual
intermediate state. The suffix uses the existing residual operation along
the actual prefix; no firing, model or result state is selected afresh.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativeWitnessCuts

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open NativeIterated
open NativeRoundExecution (Witness)
open ResidualPrefixModels (residuals)

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

def reword {initial last : NativeState S O Γ sort} {first second : List (LiveFiring initial)}
    (same : first = second) (witness : Witness initial first last) : Witness initial second last :=
  same ▸ witness

theorem residuals_reword {initial last : NativeState S O Γ sort}
    {first second : List (LiveFiring initial)} (same : first = second)
    (witness : Witness initial first last) (remaining : List (LiveFiring initial)) :
    residuals (reword same witness) remaining = residuals witness remaining := by
  cases same
  rfl

noncomputable def cutAppend : {initial last : NativeState S O Γ sort} →
    (front back : List (LiveFiring initial)) → Witness initial (front ++ back) last →
    (middle : NativeState S O Γ sort) ×
      (frontRun : Witness initial front middle) × Witness middle (residuals frontRun back) last
  | initial,_,[],back,witness => ⟨initial,.nil initial,witness⟩
  | _,_,first :: front,back,witness => by
      cases witness with
      | cons _ _ admitted tail =>
          let mapped := reword
            (show (front ++ back).map (residualAfter admitted) =
              front.map (residualAfter admitted) ++ back.map (residualAfter admitted) from List.map_append) tail
          obtain ⟨middle,frontRun,suffix⟩ := cutAppend
            (front.map (residualAfter admitted)) (back.map (residualAfter admitted)) mapped
          exact ⟨middle,.cons first front admitted frontRun,suffix⟩
termination_by _ _ front _ _ => front.length
decreasing_by simp_wf

/-- A cut beyond the end is the final cut. A bound is needed only to claim
that the prefix contains exactly the requested number of events. -/
noncomputable def cutAt {initial last : NativeState S O Γ sort} {members : List (LiveFiring initial)}
    (witness : Witness initial members last) (count : Nat) :
    (middle : NativeState S O Γ sort) ×
      (frontRun : Witness initial (members.take count) middle) ×
        Witness middle (residuals frontRun (members.drop count)) last :=
  cutAppend (members.take count) (members.drop count)
    (reword (List.take_append_drop count members).symm witness)

theorem cutAt_event_count_all {initial last : NativeState S O Γ sort} {members : List (LiveFiring initial)}
    (witness : Witness initial members last) (count : Nat) :
    (cutAt witness count).2.1.toRun.word.length = min count members.length := by
  rw [Witness.event_count,List.length_take]

theorem cutAt_event_count {initial last : NativeState S O Γ sort} {members : List (LiveFiring initial)}
    (witness : Witness initial members last) (count : Nat) (bound : count ≤ members.length) :
    (cutAt witness count).2.1.toRun.word.length = count := by
  rw [cutAt_event_count_all,Nat.min_eq_left bound]

theorem empty_cut_does_not_create_an_event (state : NativeState S O Γ sort) :
    (cutAt (Witness.nil state) 1).2.1.toRun.word.length = 0 ∧
      (cutAt (Witness.nil state) 1).2.1.toRun.word.length ≠ 1 := by
  rw [cutAt_event_count_all]
  simp

theorem residuals_selections {initial last : NativeState S O Γ sort} {front : List (LiveFiring initial)}
    (witness : Witness initial front last) (remaining : List (LiveFiring initial)) :
    (residuals witness remaining).map (fun firing => firing.selection) =
      remaining.map (fun firing => firing.selection) := by
  induction witness with
  | nil => rfl
  | cons first rest admitted tail ih =>
      rw [residuals,ih,List.map_map]
      rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativeWitnessCuts
