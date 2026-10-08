import Mettapedia.OSLF.Framework.FundedNuAssayControls

/-!
# No uniform finite confirmation bound on an infinite state family

The state `none` has a persistent self-loop. Each `some n` has a chain of
exactly `n` steps before blocking. Thus every fixed finite unfolding admits
some finite chains which fail the original greatest-fixed-point hypothesis.
The state carrier is infinite while each actual successor list has at most
one occurrence. Finite branching does not supply a uniform finite stage.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.NuInfiniteUnfoldingControls

open Mettapedia.Logic.ModalMuCalculus Inspection Unfolding
open FundedNuAssayControls (continuation)
open FundedNuAssays

def infiniteChains : SuccessorPresentation (Option Nat) Unit where
  successors state _ :=
    match state with
    | none => [none]
    | some 0 => []
    | some (length + 1) => [some length]

theorem atStage_successor (index : Nat) :
    continuation.atStage (index + 1) = .diamond () (continuation.atStage index) := rfl

theorem finite_chain_stage (index length : Nat) :
    satisfies infiniteChains.toLTS Env.empty (continuation.atStage index) (some length) ↔
      index ≤ length := by
  induction index generalizing length with
  | zero => simp only [PositiveHMLBody.atStage, nuUnfolding, satisfies, Nat.zero_le]
  | succ index inductionHypothesis =>
      rw [atStage_successor]
      change (∃ target, target ∈ infiniteChains.successors (some length) () ∧
        satisfies infiniteChains.toLTS Env.empty (continuation.atStage index) target) ↔ _
      cases length with
      | zero => simp [infiniteChains]
      | succ length =>
          change (∃ target, target ∈ [some length] ∧
            satisfies infiniteChains.toLTS Env.empty (continuation.atStage index) target) ↔ _
          simp only [List.mem_singleton, exists_eq_left, Nat.succ_le_succ_iff]
          exact inductionHypothesis length

theorem infinite_loop_stage (index : Nat) :
    satisfies infiniteChains.toLTS Env.empty (continuation.atStage index) none := by
  induction index with
  | zero => exact True.intro
  | succ index inductionHypothesis =>
      rw [atStage_successor]
      exact ⟨none, List.mem_singleton_self none, inductionHypothesis⟩

theorem infinite_loop_original :
    satisfies infiniteChains.toLTS Env.empty (.nu continuation.body) none := by
  refine ⟨{none}, Set.mem_singleton none, ?_⟩
  intro state member
  have same : state = none := Set.mem_singleton_iff.mp member
  subst state
  exact ⟨none, List.mem_singleton_self none, Set.mem_singleton none⟩

theorem finite_chain_original_refuted (length : Nat) :
    ¬ satisfies infiniteChains.toLTS Env.empty (.nu continuation.body) (some length) := by
  apply refuted_stage_refutes_original infiniteChains.toLTS continuation (length + 1) (some length)
  rw [finite_chain_stage]
  exact Nat.not_succ_le_self length

theorem no_uniform_finite_confirmation (index : Nat) :
    ∃ state, satisfies infiniteChains.toLTS Env.empty (continuation.atStage index) state ∧
      ¬ satisfies infiniteChains.toLTS Env.empty (.nu continuation.body) state :=
  ⟨some index, (finite_chain_stage index index).2 le_rfl, finite_chain_original_refuted index⟩

theorem every_successor_list_finite_and_small (state : Option Nat) (action : Unit) :
    (infiniteChains.successors state action).length ≤ 1 := by
  cases state with
  | none => exact le_rfl
  | some length => cases length <;> simp [infiniteChains]

theorem no_finite_stage_is_the_original_predicate (index : Nat) :
    sat infiniteChains.toLTS Env.empty (continuation.atStage index) ≠
      sat infiniteChains.toLTS Env.empty (.nu continuation.body) := by
  intro same
  obtain ⟨state, atStage, notOriginal⟩ := no_uniform_finite_confirmation index
  exact notOriginal ((Set.ext_iff.mp same state).mp atStage)

theorem actual_inspection_confirms_arbitrarily_late (index : Nat) :
    (protocol infiniteChains (fun _ _ => 1)).test (continuation, index) (some index) = true :=
  (test_truth infiniteChains (fun _ _ => 1) (continuation, index) (some index)).2
    ((finite_chain_stage index index).2 le_rfl)

end Mettapedia.OSLF.Framework.NuInfiniteUnfoldingControls
