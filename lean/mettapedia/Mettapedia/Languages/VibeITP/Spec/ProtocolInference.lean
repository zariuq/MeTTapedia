import Mettapedia.Languages.VibeITP.Spec.ProtocolStorage
import Mettapedia.Languages.VibeITP.Spec.ProtocolSuccess
import Mettapedia.Languages.VibeITP.Spec.InstructionBounds

/-! Independent derivations authorize every static theorem publication. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec.ProtocolInference

open ProtocolExecution ProtocolInvariant ProtocolStorage ProtocolSuccess

theorem inProofs_then_place_invariant {before : ObservedState} {after : State}
    (primitive : Primitive) (destination : Nat) (statement : Term)
    (invariant : LogicalInvariant before)
    (derived : DerivesWithExecution before.kernel.theory before.observations statement)
    (accepted : (do before.kernel.inProofs primitive
                    before.kernel.placeTheorem destination statement) = .ok after) :
    LogicalInvariant ⟨after, before.observations⟩ := by
  obtain ⟨proofPhase, _, placed⟩ := (bind_ok_iff _ _ _).mp accepted
  cases proofPhase
  exact place_theorem_invariant invariant derived placed

theorem litIsNat_preserved {before : ObservedState} {after : State} (value destination : Nat)
    (invariant : LogicalInvariant before) (bound : value < wordBound)
    (accepted : execute before.kernel (.litIsNat value destination) = some (.ok after)) :
    LogicalInvariant ⟨after, before.observations⟩ :=
  inProofs_then_place_invariant .litIsNat destination (litIsNatStatement value)
    invariant (.litIsNat bound) (Option.some.inj accepted)

theorem litAdd_preserved {before : ObservedState} {after : State} (left right destination : Nat)
    (invariant : LogicalInvariant before) (leftBound : left < wordBound) (rightBound : right < wordBound)
    (accepted : execute before.kernel (.litAdd left right destination) = some (.ok after)) :
    LogicalInvariant ⟨after, before.observations⟩ :=
  inProofs_then_place_invariant .litAdd destination (litAddStatement left right)
    invariant (.litAdd leftBound rightBound) (Option.some.inj accepted)

theorem litMul_preserved {before : ObservedState} {after : State} (left right destination : Nat)
    (invariant : LogicalInvariant before) (leftBound : left < wordBound) (rightBound : right < wordBound)
    (accepted : execute before.kernel (.litMul left right destination) = some (.ok after)) :
    LogicalInvariant ⟨after, before.observations⟩ :=
  inProofs_then_place_invariant .litMul destination (litMulStatement left right)
    invariant (.litMul leftBound rightBound) (Option.some.inj accepted)

theorem litLt_preserved {before : ObservedState} {after : State} (left right destination : Nat)
    (invariant : LogicalInvariant before) (rightBound : right < wordBound)
    (accepted : execute before.kernel (.litLt left right destination) = some (.ok after)) :
    LogicalInvariant ⟨after, before.observations⟩ := by
  have run := Option.some.inj accepted
  obtain ⟨proofPhase, _, following⟩ := (bind_ok_iff _ _ _).mp run
  cases proofPhase
  by_cases smaller : left < right
  · simp only [if_pos smaller] at following
    exact place_theorem_invariant invariant (.litLt smaller rightBound) following
  · simp only [if_neg smaller] at following
    cases following

theorem litDiv_preserved {before : ObservedState} {after : State} (left right destination : Nat)
    (invariant : LogicalInvariant before) (leftBound : left < wordBound) (rightBound : right < wordBound)
    (accepted : execute before.kernel (.litDiv left right destination) = some (.ok after)) :
    LogicalInvariant ⟨after, before.observations⟩ := by
  have run := Option.some.inj accepted
  obtain ⟨proofPhase, _, following⟩ := (bind_ok_iff _ _ _).mp run
  cases proofPhase
  by_cases zero : right = 0
  · simp only [if_pos zero] at following
    cases following
  · simp only [if_neg zero] at following
    exact place_theorem_invariant invariant (.litDiv leftBound rightBound zero) following

theorem modusPonens_preserved {before : ObservedState} {after : State}
    (implicationSlot premiseSlot destination : Nat) (invariant : LogicalInvariant before)
    (accepted : execute before.kernel (.modusPonens implicationSlot premiseSlot destination) =
      some (.ok after)) : LogicalInvariant ⟨after, before.observations⟩ := by
  have run := Option.some.inj accepted
  obtain ⟨proofPhase, _, reads⟩ := (bind_ok_iff _ _ _).mp run
  cases proofPhase
  obtain ⟨implication, implicationRead, following⟩ := (bind_ok_iff _ _ _).mp reads
  obtain ⟨premise, premiseRead, matched⟩ := (bind_ok_iff _ _ _).mp following
  have implicationDerived := invariant.theorems implicationSlot implication
    ((need_ok_iff _ _ _).mp implicationRead)
  have premiseDerived := invariant.theorems premiseSlot premise
    ((need_ok_iff _ _ _).mp premiseRead)
  split at matched
  · rename_i antecedent conclusion
    split at matched
    · have equal : antecedent = premise := by assumption
      subst premise
      exact place_theorem_invariant invariant (.modusPonens implicationDerived premiseDerived) matched
    · cases matched
  · cases matched

theorem instantiate_preserved {before : ObservedState} {after : State}
    (theoremSlot symbolSlot valueSlot destination : Nat) (invariant : LogicalInvariant before)
    (accepted : execute before.kernel (.thmInstantiate theoremSlot symbolSlot valueSlot destination) =
      some (.ok after)) : LogicalInvariant ⟨after, before.observations⟩ := by
  have run := Option.some.inj accepted
  obtain ⟨proofPhase, _, reads⟩ := (bind_ok_iff _ _ _).mp run
  cases proofPhase
  obtain ⟨statement, statementRead, following⟩ := (bind_ok_iff _ _ _).mp reads
  obtain ⟨head, _, following⟩ := (bind_ok_iff _ _ _).mp following
  obtain ⟨value, valueRead, matched⟩ := (bind_ok_iff _ _ _).mp following
  have statementDerived := invariant.theorems theoremSlot statement
    ((need_ok_iff _ _ _).mp statementRead)
  have valueFormed := invariant.terms valueSlot value ((need_ok_iff _ _ _).mp valueRead)
  split at matched
  · rename_i symbol headRead
    cases instantiated : instantiateStatement before.kernel.sig symbol value statement with
    | none => simp [instantiated] at matched
    | some result =>
      simp only [instantiated] at matched
      exact place_theorem_invariant invariant
        (.instantiate statementDerived valueFormed instantiated) matched
  · cases matched

theorem litLength_preserved {before : ObservedState} {after : State}
    (termSlot destination : Nat) (invariant : LogicalInvariant before)
    (accepted : execute before.kernel (.litLength termSlot destination) = some (.ok after)) :
    LogicalInvariant ⟨after, before.observations⟩ := by
  have run := Option.some.inj accepted
  obtain ⟨proofPhase, _, reads⟩ := (bind_ok_iff _ _ _).mp run
  cases proofPhase
  obtain ⟨term, termRead, matched⟩ := (bind_ok_iff _ _ _).mp reads
  have formed := invariant.terms termSlot term ((need_ok_iff _ _ _).mp termRead)
  split at matched
  · exact place_theorem_invariant invariant (.litLength formed) matched
  · cases matched

theorem litGet_preserved {before : ObservedState} {after : State}
    (termSlot index destination : Nat) (invariant : LogicalInvariant before)
    (accepted : execute before.kernel (.litGet termSlot index destination) = some (.ok after)) :
    LogicalInvariant ⟨after, before.observations⟩ := by
  have run := Option.some.inj accepted
  obtain ⟨proofPhase, _, reads⟩ := (bind_ok_iff _ _ _).mp run
  cases proofPhase
  obtain ⟨term, termRead, matched⟩ := (bind_ok_iff _ _ _).mp reads
  have formed := invariant.terms termSlot term ((need_ok_iff _ _ _).mp termRead)
  split at matched
  · split at matched
    · exact place_theorem_invariant invariant (.litGet formed (by assumption)) matched
    · cases matched
  · cases matched

end Mettapedia.Languages.VibeITP.Spec.ProtocolInference
