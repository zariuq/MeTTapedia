import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreWeightChance
import Mettapedia.Logic.LinearLogic.KnowledgeTensorWeightHarris

/-!
# Harris's inequality for the parts of a cut whose grades shrink

For an arbitrary step, contextual interpretation and family of placements: if each part of a cut
survives the removal of facts from its surrounding, the two parts survive a common independent
random surrounding with positively correlated chances (`cut_harris_of_shrinking`). Absence-only
runs shrink (`AbsenceAlong.down_closed`); counting candidates need not
(`counting_does_not_shrink`, `counts_two_candidate_is_not_monotone`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore

open Mettapedia.Logic.LinearLogic.KnowledgeTensorWeight

universe uO uT uH uOcc uS uF uI uP uA

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} {P : Step X O State Firing}
  {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P}
  (I : ContextualRunInterpretation.{uO,uT,uH,uOcc,uS,uF,uI,uP} T)
  {α : Type uA} [Fintype α] [DecidableEq α] (right : Finset α → State)

/-- **The parts of a cut whose grades shrink are positively correlated.** -/
theorem cut_harris_of_shrinking (p : α → ℝ) (probability : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    {left : State} {place : (S : Finset α) → I.Place left (right S)} {first : P.Run left}
    {second : P.Run first.last}
    (shrinksFirst : ∀ S S', S ⊆ S' → I.Checks (place S') first → I.Checks (place S) first)
    (shrinksSecond : ∀ S S', S ⊆ S' → I.Checks (advanceRun I (place S') first) second →
      I.Checks (advanceRun I (place S) first) second) :
    measure p (fun S => I.Checks (place S) first) *
        measure p (fun S => I.Checks (advanceRun I (place S) first) second) ≤
      measure p (fun S => I.Checks (place S) (first.append second)) := by
  rw [measure_congr p (G := fun S => I.Checks (place S) (first.append second))
    (H := fun S => I.Checks (place S) first ∧ I.Checks (advanceRun I (place S) first) second)
    (fun S => checks_append I (place S) first second)]
  exact harris_down_closed p probability _ _ shrinksFirst shrinksSecond

/-- Absence-only runs shrink, so the absence form of the inequality is an instance. -/
theorem AbsenceAlong.cut_harris_by_shrinking (p : α → ℝ) (probability : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    {left : State} {place : (S : Finset α) → I.Place left (right S)} {first : P.Run left}
    {second : P.Run first.last} {F₁ F₂ : Finset α}
    (one : AbsenceAlong I right place first F₁)
    (two : AbsenceAlong I right (fun S => advanceRun I (place S) first) second F₂) :
    measure p (fun S => I.Checks (place S) first) *
        measure p (fun S => I.Checks (advanceRun I (place S) first) second) ≤
      measure p (fun S => I.Checks (place S) (first.append second)) :=
  cut_harris_of_shrinking I right p probability
    (fun _ _ smaller survives => AbsenceAlong.down_closed I right one smaller survives)
    (fun _ _ smaller survives => AbsenceAlong.down_closed I right two smaller survives)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore
