import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DistinctionObserver

/-!
# Graded readings of actual transform programs

Any bounded family of real-valued queries supplies graded observations of the
same labelled transform transitions. The existing quantitative modal theory
then produces a metric tolerance. Image finiteness licenses equality with
the Hausdorff behavioural distance. This is nondeterministic grading, not a
claim that erasing probabilities preserves stochastic distances.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionObserver
open Interface
open Mettapedia.GSLT.Distinction
universe uOb uT uH uO uS uF uL uJ
variable {Obj : Type uOb} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uO} [DecidableEq O] {State : Type uS}
  {Fir : State → Type uF} {L : Type uL} {J : Type uJ}
  (P : Interface.Step X O State Fir) (offers : L → (s : State) → Fir s → Prop)
  (values : J → State → ℝ) (lower : ∀ j s, 0 ≤ values j s) (upper : ∀ j s, values j s ≤ 1)
  (discount : ℝ) (nonneg : 0 ≤ discount) (bounded : discount ≤ 1)

def gradedReadings : GradedSystem (Race.Generic.gslt P offers) where
  dynamics := Race.Generic.system P offers
  observations := {
    Atom := J
    value := values
    value_nonneg := lower
    value_le_one := upper
    value_resp := by intro j s t same; exact congrArg (values j) same }
  discount := discount
  discount_nonneg := nonneg
  discount_le_one := bounded

theorem gradedReadings_metric :
    (gradedReadings P offers values lower upper discount nonneg bounded).toTolerance.Metric :=
  GradedSystem.toTolerance_metric _

theorem gradedReadings_behavioural_eq
    (finite : ∀ label s, {t | Race.Generic.Moves P offers s label t}.Finite) :
    (gradedReadings P offers values lower upper discount nonneg bounded).behaviouralDistance =
      (gradedReadings P offers values lower upper discount nonneg bounded).logicalDistance := by
  funext s t
  exact GradedSystem.behaviouralDistance_eq_logicalDistance _
    (observed_imageFinite P offers (fun _ => ()) finite) s t

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionObserver
