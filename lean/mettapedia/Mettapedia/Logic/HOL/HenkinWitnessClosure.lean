import Mettapedia.Logic.HOL.Henkinization
import Mettapedia.Logic.HOL.CanonicalTheory

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

namespace OneStepHenkinConst

/--
`ExWitnessClosed T` says that a closed theory over the one-step Henkinized
signature contains the designated witness instance whenever it contains an
existential formula lifted from the original signature.

This is intentionally only closure for formulas from the *base* signature.
-/
def ExWitnessClosed
    (T : ClosedTheorySet (OneStepHenkinConst Base Const)) : Prop :=
  ∀ {σ : Ty Base} {φ : Formula Const [σ]},
    (.ex (liftFormula (Base := Base) (Const := Const) φ) :
        ClosedFormula (OneStepHenkinConst Base Const)) ∈ T →
      exWitnessInstance (Base := Base) (Const := Const) φ ∈ T

/--
`AllCounterexampleClosed T` says that when a universally quantified formula from
the original signature is absent from `T`, the designated counterexample
instance is also absent.

Again, this is only closure for formulas from the *base* signature.
-/
def AllCounterexampleClosed
    (T : ClosedTheorySet (OneStepHenkinConst Base Const)) : Prop :=
  ∀ {σ : Ty Base} {φ : Formula Const [σ]},
    (.all (liftFormula (Base := Base) (Const := Const) φ) :
        ClosedFormula (OneStepHenkinConst Base Const)) ∉ T →
      allCounterexampleInstance (Base := Base) (Const := Const) φ ∉ T

/-- One-step Henkin closure over the original signature. -/
def HenkinClosedOverBase
    (T : ClosedTheorySet (OneStepHenkinConst Base Const)) : Prop :=
  ExWitnessClosed (Base := Base) (Const := Const) T ∧
    AllCounterexampleClosed (Base := Base) (Const := Const) T

theorem exists_witness_of_mem_lift_ex
    {T : ClosedTheorySet (OneStepHenkinConst Base Const)}
    (hT : ExWitnessClosed (Base := Base) (Const := Const) T)
    {σ : Ty Base} {φ : Formula Const [σ]}
    (hEx :
      (.ex (liftFormula (Base := Base) (Const := Const) φ) :
          ClosedFormula (OneStepHenkinConst Base Const)) ∈ T) :
    ∃ t : ClosedTerm (OneStepHenkinConst Base Const) σ,
      instantiate (Base := Base)
          t (liftFormula (Base := Base) (Const := Const) φ) ∈ T := by
  refine ⟨exWitnessTerm (Base := Base) (Const := Const) φ, ?_⟩
  simpa [exWitnessInstance] using
    hT hEx

theorem all_counterexample_of_not_mem_lift_all
    {T : ClosedTheorySet (OneStepHenkinConst Base Const)}
    (hT : AllCounterexampleClosed (Base := Base) (Const := Const) T)
    {σ : Ty Base} {φ : Formula Const [σ]}
    (hAll :
      (.all (liftFormula (Base := Base) (Const := Const) φ) :
          ClosedFormula (OneStepHenkinConst Base Const)) ∉ T) :
    ∃ t : ClosedTerm (OneStepHenkinConst Base Const) σ,
      instantiate (Base := Base)
          t (liftFormula (Base := Base) (Const := Const) φ) ∉ T := by
  refine ⟨allCounterexampleTerm (Base := Base) (Const := Const) φ, ?_⟩
  simpa [allCounterexampleInstance] using
    hT hAll

end OneStepHenkinConst

end Mettapedia.Logic.HOL
