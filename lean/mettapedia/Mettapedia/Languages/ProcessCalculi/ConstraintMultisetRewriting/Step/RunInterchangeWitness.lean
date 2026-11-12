import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunSimilarityWitness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.InterchangeTrace
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Rearrangements

/-!
# Witnessed canonical interchanges of actual runs

Each generator retains the admitted firings, their two residuals, the closing
state comparison and the unchanged continuation transported by that map.
The event map exchanges exactly the two positions at which the generator
acts. Its domain is the complete source run, so repeated labels remain
distinct occurrences of events.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} (T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P)

inductive InterchangeWitness : {s : State} → P.Run s → P.Run s → Type (max uS uF uI)
  | here {s : State} {first second : Firing s}
      (accepted : P.Admits first) (accepted' : P.Admits second)
      (afterFirst : P.Admits (T.residual first accepted second))
      (afterSecond : P.Admits (T.residual second accepted' first))
      (close : T.Iso (P.result (T.residual first accepted second) afterFirst)
        (P.result (T.residual second accepted' first) afterSecond))
      (rest : P.Run (P.result (T.residual first accepted second) afterFirst)) :
      InterchangeWitness
        (.cons first accepted (.cons (T.residual first accepted second) afterFirst rest))
        (.cons second accepted' (.cons (T.residual second accepted' first) afterSecond (T.moveRun close rest)))
  | later {s : State} (firing : Firing s) (accepted : P.Admits firing)
      {first second : P.Run (P.result firing accepted)}
      (tail : InterchangeWitness first second) :
      InterchangeWitness (.cons firing accepted first) (.cons firing accepted second)

namespace InterchangeWitness

variable {T}

theorem interchange {s : State} {first second : P.Run s}
    (witness : T.InterchangeWitness first second) : T.Interchange first second := by
  induction witness with
  | here accepted accepted' afterFirst afterSecond close rest =>
      exact .here accepted accepted' afterFirst afterSecond close rest
  | later firing accepted _ ih => exact .later firing accepted ih

theorem nonempty_iff {s : State} {first second : P.Run s} :
    Nonempty (T.InterchangeWitness first second) ↔ T.Interchange first second := by
  constructor
  · rintro ⟨witness⟩
    exact witness.interchange
  · intro related
    induction related with
    | here accepted accepted' afterFirst afterSecond close rest =>
        exact ⟨.here accepted accepted' afterFirst afterSecond close rest⟩
    | later firing accepted _ ih =>
        obtain ⟨witness⟩ := ih
        exact ⟨.later firing accepted witness⟩

def depth : {s : State} → {first second : P.Run s} → T.InterchangeWitness first second → Nat
  | _, _, _, .here .. => 0
  | _, _, _, .later _ _ tail => tail.depth + 1

theorem length_eq {s : State} {first second : P.Run s}
    (witness : T.InterchangeWitness first second) : first.word.length = second.word.length :=
  witness.interchange.toSwap.length_eq.1

theorem depth_bound {s : State} {first second : P.Run s}
    (witness : T.InterchangeWitness first second) : witness.depth + 2 ≤ first.word.length := by
  induction witness with
  | here => simp [depth, Step.Run.word]
  | later _ _ _ ih => simp only [depth, Step.Run.word, List.length_cons]; omega

def lastIso : {s : State} → {first second : P.Run s} →
    T.InterchangeWitness first second → T.Iso first.last second.last
  | _, _, _, .here _ _ _ _ close rest => (SimilarityWitness.moveRun close rest).lastIso
  | _, _, _, .later _ _ tail => tail.lastIso

def position {s : State} {first second : P.Run s}
    (witness : T.InterchangeWitness first second) : Nat → Nat :=
  ProofRelevantRuns.swapAt witness.depth

theorem position_position {s : State} {first second : P.Run s}
    (witness : T.InterchangeWitness first second) (index : Nat) :
    witness.position (witness.position index) = index :=
  ProofRelevantRuns.swapAt_swapAt witness.depth index

theorem position_lt_iff {s : State} {first second : P.Run s}
    (witness : T.InterchangeWitness first second) (index : Nat) :
    witness.position index < second.word.length ↔ index < first.word.length := by
  have inside := witness.depth_bound
  rw [← witness.length_eq]
  unfold position ProofRelevantRuns.swapAt
  split_ifs <;> omega

def events {s : State} {first second : P.Run s}
    (witness : T.InterchangeWitness first second) :
    Fin first.word.length ≃ Fin second.word.length where
  toFun event := ⟨witness.position event.val, (witness.position_lt_iff event.val).mpr event.isLt⟩
  invFun event := ⟨witness.position event.val, by
    have bound := (witness.position_lt_iff (witness.position event.val)).mp
      (by simpa only [witness.position_position] using event.isLt)
    exact bound⟩
  left_inv event := Fin.ext (witness.position_position event.val)
  right_inv event := Fin.ext (witness.position_position event.val)

theorem events_val {s : State} {first second : P.Run s}
    (witness : T.InterchangeWitness first second) (event : Fin first.word.length) :
    (witness.events event).val = witness.position event.val := rfl

theorem moves_first_position {s : State} {first second : P.Run s}
    (witness : T.InterchangeWitness first second) :
    witness.position witness.depth = witness.depth + 1 := by
  simp [position, ProofRelevantRuns.swapAt]

theorem fixes_outside {s : State} {first second : P.Run s}
    (witness : T.InterchangeWitness first second) {index : Nat}
    (outside : first.word.length ≤ index) : witness.position index = index := by
  have inside := witness.depth_bound
  simp only [position, ProofRelevantRuns.swapAt]
  split_ifs <;> omega

end InterchangeWitness

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.InterchangeWitness.nonempty_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.InterchangeWitness.events
