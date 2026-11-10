import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceGenericFirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RationalStep

/-!
# A race in the step over rational trees

The step over rational trees (`Rational.rationalStep`) is the one-frame instance of the interface
with the rational-tree action. The race pair of `RacePair` is built for every substitution action,
so it lives there, with the answers `b = f(X)` and `c = g(Y)`, which are distinct because their
equation has no rational solution (`Rational.Controls.clash_refuted`).

Read through the generic layer (`RaceGeneric`) over the rational-tree frames (`rational_race`): `P`
and `Q` satisfy the same trace formulas, `⟨A⟩(⟨B⟩⊤ ∧ ⟨C⟩⊤)` holds at `P` and fails at `Q`, and they
are not bisimilar.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Generic.RationalRace

open Rational Rational.Controls
open Mettapedia.Logic.LP
open Mettapedia.GSLT.HennessyMilner (Formula)

/-- The tags of the race pair over rational trees. -/
def tags : Pair.Tags (RTree ctlSig) := ⟨r X, r Y, r X, r (un .f X), r (un .g Y)⟩

/-- **The two answers are distinct**: their equation has no solution. -/
theorem apart : tags.b ≠ tags.c := fun same =>
  clash_refuted.2 (consistent_of_reflexive (rationalAction ctlSig)
    (store := [(r (un .f X), r (un .g Y))]) fun e member => by
      rw [List.mem_singleton.mp member]
      exact same)

/-- The race pair's program, over rational trees, read over the interface. -/
abbrev offers := lift (Pair.offers (S := RSubst ctlSig) tags)

/-- **The race pair in the step over rational trees**: the same traces, separated by
`⟨A⟩(⟨B⟩⊤ ∧ ⟨C⟩⊤)`, not bisimilar. -/
theorem rational_race :
    (∀ w : List (RuleInstance (RTree ctlSig)),
      Sat (rationalStep ctlSig (Pair.label tags)).toStep offers (Formula.after w .top) Pair.P ↔
        Sat (rationalStep ctlSig (Pair.label tags)).toStep offers (Formula.after w .top) Pair.Q) ∧
      Sat (rationalStep ctlSig (Pair.label tags)).toStep offers (Pair.separating tags) Pair.P ∧
      ¬ Sat (rationalStep ctlSig (Pair.label tags)).toStep offers (Pair.separating tags) Pair.Q ∧
      ¬ Bisimilar (rationalStep ctlSig (Pair.label tags)).toStep offers Pair.P Pair.Q :=
  ⟨fun w => (sat_lift_iff _ _).trans
      ((Pair.traceEquivalent_P_Q tags (rationalAction ctlSig) w).trans (sat_lift_iff _ _).symm),
    (sat_lift_iff _ _).mpr (Pair.separating_holds_P tags (rationalAction ctlSig)),
    fun holds => Pair.separating_fails_Q tags (rationalAction ctlSig) apart ((sat_lift_iff _ _).mp holds),
    fun bisimilar => Pair.not_bisimilar_P_Q tags (rationalAction ctlSig) apart
      (bisimilar_lift_iff.mp bisimilar)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Generic.RationalRace

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Generic.RationalRace in
#print axioms apart
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Generic.RationalRace in
#print axioms rational_race
