import Mettapedia.Languages.VibeITP.Spec.ProtocolFrame
import Mathlib.Data.Finset.Card

/-! Exact finite challenge-slot and phase-counter accounting. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec.ProtocolChallenges

open ProtocolFrame

def Totals (state : State) : Prop :=
  match state.phase with
  | .setup => state.satisfied = [] ∧ state.setupChallenges = 0 ∧ state.proofChallenges = 0
  | .proofs => state.openChallenges + state.satisfied.length =
      state.setupChallenges + state.proofChallenges

def Accounting (state : State) : Prop :=
  ∃ occupied : Finset Nat,
    (∀ slot, slot ∈ occupied ↔ (state.challenges slot).isSome = true) ∧
      state.openChallenges = occupied.card ∧ Totals state

theorem initial_accounting : Accounting initialState := by
  refine ⟨∅, ?_, rfl, ?_⟩
  · intro slot
    simp [initialState]
  · simp [Totals, initialState]

theorem frame_accounting {before after : State} (accounted : Accounting before)
    (frame : ChallengeFrame before after) : Accounting after := by
  obtain ⟨occupied, complete, count, totals⟩ := accounted
  refine ⟨occupied, ?_, frame.openCount.trans count, ?_⟩
  · intro slot
    rw [frame.slots]
    exact complete slot
  · simpa [Totals, frame.phase, frame.satisfied, frame.openCount, frame.setupCount, frame.proofCount]
      using totals

theorem enterProofs_accounting (before : State) (setup : before.phase = .setup)
    (accounted : Accounting before) : Accounting (enterProofs before) := by
  obtain ⟨occupied, complete, count, totals⟩ := accounted
  have prior : before.satisfied = [] ∧ before.setupChallenges = 0 ∧ before.proofChallenges = 0 := by
    simpa [Totals, setup] using totals
  refine ⟨occupied, complete, count, ?_⟩
  simp [Totals, enterProofs, prior.1, prior.2.2]

theorem register_accounting (before : State) (destination : Nat) (statement : Term)
    (accounted : Accounting before) (empty : before.challenges destination = none) :
    Accounting { before with
      challenges := setSlot before.challenges destination (some statement)
      openChallenges := before.openChallenges + 1
      proofChallenges := match before.phase with
        | .setup => before.proofChallenges
        | .proofs => before.proofChallenges + 1 } := by
  obtain ⟨occupied, complete, count, totals⟩ := accounted
  have fresh : destination ∉ occupied := by
    intro member
    have present := (complete destination).mp member
    simp [empty] at present
  refine ⟨insert destination occupied, ?_, ?_, ?_⟩
  · intro slot
    by_cases newest : slot = destination
    · simp [setSlot, newest]
    · simpa [setSlot, newest] using complete slot
  · change before.openChallenges + 1 = (insert destination occupied).card
    rw [Finset.card_insert_of_notMem fresh, count]
  · cases phase : before.phase with
    | setup => simpa [Totals, phase] using totals
    | proofs =>
      have prior : before.openChallenges + before.satisfied.length =
          before.setupChallenges + before.proofChallenges := by simpa [Totals, phase] using totals
      simp only [Totals]
      omega

theorem satisfy_accounting (before : State) (source : Nat) (statement : Term)
    (accounted : Accounting before) (proofs : before.phase = .proofs)
    (present : before.challenges source = some statement) :
    Accounting { before with
      challenges := setSlot before.challenges source none
      openChallenges := before.openChallenges - 1
      satisfied := before.satisfied ++ [statement] } := by
  obtain ⟨occupied, complete, count, totals⟩ := accounted
  have member : source ∈ occupied := (complete source).mpr (by simp [present])
  have positive : 0 < before.openChallenges := by
    rw [count]
    exact Finset.card_pos.mpr ⟨source, member⟩
  refine ⟨occupied.erase source, ?_, ?_, ?_⟩
  · intro slot
    by_cases erased : slot = source
    · simp [setSlot, erased]
    · simpa [setSlot, erased] using complete slot
  · simpa [Finset.card_erase_of_mem member] using congrArg (· - 1) count
  · have prior : before.openChallenges + before.satisfied.length =
        before.setupChallenges + before.proofChallenges := by simpa [Totals, proofs] using totals
    simp only [Totals, proofs, List.length_append, List.length_singleton]
    omega

theorem no_open_slots {state : State} (accounted : Accounting state)
    (closed : state.openChallenges = 0) : ∀ slot, state.challenges slot = none := by
  obtain ⟨occupied, complete, count, _⟩ := accounted
  have empty : occupied = ∅ := Finset.card_eq_zero.mp (count.symm.trans closed)
  intro slot
  have absent : (state.challenges slot).isSome = false := by
    have notPresent : ¬ (state.challenges slot).isSome = true := by
      rw [← complete slot, empty]
      simp
    exact Bool.eq_false_iff.mpr notPresent
  cases found : state.challenges slot with
  | none => rfl
  | some value => simp [found] at absent

end Mettapedia.Languages.VibeITP.Spec.ProtocolChallenges
