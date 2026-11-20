import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Cells

/-!
# All six executions of an actual three-dimensional admission cell

Schedules retain the admissions of the actual successive residual firings.
The existing all-faces cell judgment is equivalent to these six schedules,
including when the three original firing values repeat. It implies no
endpoint comparison by itself.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} (T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P)

structure TripleSchedule {state : State} (first second third : Firing state) : Prop where
  firstAccepted : P.Admits first
  secondAccepted : P.Admits (T.residual first firstAccepted second)
  thirdAccepted : P.Admits
    (T.residual (T.residual first firstAccepted second) secondAccepted (T.residual first firstAccepted third))

def TripleSchedule.run {state : State} {first second third : Firing state}
    (schedule : T.TripleSchedule first second third) : P.Run state :=
  .cons first schedule.firstAccepted
    (.cons (T.residual first schedule.firstAccepted second) schedule.secondAccepted
      (.cons (T.residual (T.residual first schedule.firstAccepted second) schedule.secondAccepted
        (T.residual first schedule.firstAccepted third)) schedule.thirdAccepted (.nil _)))

theorem TripleSchedule.three_events {state : State} {first second third : Firing state}
    (schedule : T.TripleSchedule first second third) : schedule.run.word.length = 3 := rfl

structure SixSchedules {state : State} (first second third : Firing state) : Prop where
  abc : T.TripleSchedule first second third
  acb : T.TripleSchedule first third second
  bac : T.TripleSchedule second first third
  bca : T.TripleSchedule second third first
  cab : T.TripleSchedule third first second
  cba : T.TripleSchedule third second first

variable {T}

theorem Cell.six_schedules {state : State} {first second third : Firing state}
    (cell : T.Cell state [first, second, third]) : T.SixSchedules first second third := by
  cases cell with
  | intro _ admitted faces =>
      let a := admitted ⟨0, by simp⟩
      let b := admitted ⟨1, by simp⟩
      let c := admitted ⟨2, by simp⟩
      have faceA := faces ⟨0, by simp⟩
      have faceB := faces ⟨1, by simp⟩
      have faceC := faces ⟨2, by simp⟩
      change T.Cell (P.result first a) [T.residual first a second, T.residual first a third] at faceA
      change T.Cell (P.result second b) [T.residual second b first, T.residual second b third] at faceB
      change T.Cell (P.result third c) [T.residual third c first, T.residual third c second] at faceC
      obtain ⟨ab, ac, abc, acb⟩ := cell_pair_iff.mp faceA
      obtain ⟨ba, bc, bac, bca⟩ := cell_pair_iff.mp faceB
      obtain ⟨ca, cb, cab, cba⟩ := cell_pair_iff.mp faceC
      exact ⟨⟨a, ab, abc⟩, ⟨a, ac, acb⟩, ⟨b, ba, bac⟩, ⟨b, bc, bca⟩, ⟨c, ca, cab⟩, ⟨c, cb, cba⟩⟩

theorem SixSchedules.cell {state : State} {first second third : Firing state}
    (schedules : T.SixSchedules first second third) : T.Cell state [first, second, third] := by
  refine .intro [first, second, third] (fun index => ?_) (fun index => ?_)
  · fin_cases index
    · exact schedules.abc.firstAccepted
    · exact schedules.bac.firstAccepted
    · exact schedules.cab.firstAccepted
  · fin_cases index
    · exact cell_pair_iff.mpr ⟨schedules.abc.secondAccepted, schedules.acb.secondAccepted,
        schedules.abc.thirdAccepted, schedules.acb.thirdAccepted⟩
    · exact cell_pair_iff.mpr ⟨schedules.bac.secondAccepted, schedules.bca.secondAccepted,
        schedules.bac.thirdAccepted, schedules.bca.thirdAccepted⟩
    · exact cell_pair_iff.mpr ⟨schedules.cab.secondAccepted, schedules.cba.secondAccepted,
        schedules.cab.thirdAccepted, schedules.cba.thirdAccepted⟩

theorem triple_cell_iff_six_schedules {state : State} (first second third : Firing state) :
    T.Cell state [first, second, third] ↔ T.SixSchedules first second third :=
  ⟨Cell.six_schedules, SixSchedules.cell⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.triple_cell_iff_six_schedules
