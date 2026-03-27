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

/--
Any one-step canonical world containing the exact Henkin axioms is automatically
existentially witness-closed over the lifted base signature.

Positive example:
membership of the exact witness implication plus membership of the existential
formula forces the designated witness instance by modus ponens.

Negative example:
this only closes over formulas lifted from the base signature; it does not yet
say anything about arbitrary one-step formulas with fresh constants in them.
-/
theorem exWitnessClosed_of_world_exactHenkinAxioms
    {W : ClosedTheorySet.World (OneStepHenkinConst Base Const)}
    (hExact :
      ExactHenkinAxioms (Base := Base) (Const := Const) ⊆ W.carrier) :
    ExWitnessClosed (Base := Base) (Const := Const) W.carrier := by
  intro σ φ hEx
  have hAxiom :
      (.imp
        (.ex (liftFormula (Base := Base) (Const := Const) φ))
        (exWitnessInstance (Base := Base) (Const := Const) φ) :
          ClosedFormula (OneStepHenkinConst Base Const)) ∈ W.carrier := by
    exact hExact (Or.inl ⟨σ, φ, rfl⟩)
  exact ClosedTheorySet.World.mp (W := W) hAxiom hEx

/--
Any one-step canonical world containing the exact Henkin axioms is automatically
universally counterexample-closed over the lifted base signature.

Positive example:
if the designated counterexample instance were present, the exact implication
axiom would force the lifted universal formula itself into the world.

Negative example:
this is still only closure over lifted base formulas, not over arbitrary
one-step formulas.
-/
theorem allCounterexampleClosed_of_world_exactHenkinAxioms
    {W : ClosedTheorySet.World (OneStepHenkinConst Base Const)}
    (hExact :
      ExactHenkinAxioms (Base := Base) (Const := Const) ⊆ W.carrier) :
    AllCounterexampleClosed (Base := Base) (Const := Const) W.carrier := by
  intro σ φ hAll hInst
  have hAxiom :
      (.imp
        (allCounterexampleInstance (Base := Base) (Const := Const) φ)
        (.all (liftFormula (Base := Base) (Const := Const) φ)) :
          ClosedFormula (OneStepHenkinConst Base Const)) ∈ W.carrier := by
    exact hExact (Or.inr ⟨σ, φ, rfl⟩)
  have hAllMem :
      (.all (liftFormula (Base := Base) (Const := Const) φ) :
        ClosedFormula (OneStepHenkinConst Base Const)) ∈ W.carrier :=
    ClosedTheorySet.World.mp (W := W) hAxiom hInst
  exact hAll hAllMem

/-- Exact one-step Henkin worlds are Henkin-closed over the lifted base signature. -/
theorem henkinClosedOverBase_of_world_exactHenkinAxioms
    {W : ClosedTheorySet.World (OneStepHenkinConst Base Const)}
    (hExact :
      ExactHenkinAxioms (Base := Base) (Const := Const) ⊆ W.carrier) :
    HenkinClosedOverBase (Base := Base) (Const := Const) W.carrier :=
  ⟨exWitnessClosed_of_world_exactHenkinAxioms
      (Base := Base) (Const := Const) hExact,
    allCounterexampleClosed_of_world_exactHenkinAxioms
      (Base := Base) (Const := Const) hExact⟩

end OneStepHenkinConst

end Mettapedia.Logic.HOL
