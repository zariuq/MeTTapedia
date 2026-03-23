import Mettapedia.Logic.HOL.Syntax.ConstMap
import Mettapedia.Logic.HOL.CanonicalTheory

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u}
variable {Const : Ty Base → Type v} {Const' : Ty Base → Type w}

/--
A witness provider from a source HOL signature into a target HOL signature.

This is the smallest honest interface the canonical completeness program needs
next: it supplies closed witness and counterexample terms in a larger target
language, while remembering how to lift the old constants into that language.
-/
structure WitnessProvider (Base : Type u)
    (Source : Ty Base → Type v) (Target : Ty Base → Type w) where
  liftConst : ∀ {τ : Ty Base}, Source τ → Target τ
  exWitness : ∀ {σ : Ty Base}, Formula Source [σ] → ClosedTerm Target σ
  allCounterexample : ∀ {σ : Ty Base}, Formula Source [σ] → ClosedTerm Target σ

namespace WitnessProvider

variable (P : WitnessProvider Base Const Const')

/-- Lift HOL terms along the source-to-target signature map. -/
abbrev liftTerm {Γ : Ctx Base} {τ : Ty Base} :
    Term Const Γ τ → Term Const' Γ τ :=
  mapConst P.liftConst

/-- Lift HOL formulas along the source-to-target signature map. -/
abbrev liftFormula {Γ : Ctx Base} :
    Formula Const Γ → Formula Const' Γ :=
  mapConst P.liftConst

/-- Lift closed HOL formulas along the source-to-target signature map. -/
abbrev liftClosedFormula :
    ClosedFormula Const → ClosedFormula Const' :=
  mapConst P.liftConst

/-- The distinguished instantiated witness formula in the target language. -/
def exWitnessInstance {σ : Ty Base} (φ : Formula Const [σ]) :
    ClosedFormula Const' :=
  instantiate (Base := Base) (P.exWitness φ) (P.liftFormula φ)

/-- The distinguished instantiated counterexample formula in the target language. -/
def allCounterexampleInstance {σ : Ty Base} (φ : Formula Const [σ]) :
    ClosedFormula Const' :=
  instantiate (Base := Base) (P.allCounterexample φ) (P.liftFormula φ)

end WitnessProvider

/--
One-step Henkinization of a HOL signature:

- original constants,
- one designated existential witness constant for each one-variable formula,
- one designated universal counterexample constant for each one-variable formula.

This is intentionally a one-step extension over the *old* language. It gives the
next completeness files honest witness terms without pretending the signature is
already recursively Henkin-saturated.
-/
inductive OneStepHenkinConst (Base : Type u) (Const : Ty Base → Type v) :
    Ty Base → Type (max u v) where
  | base : Const τ → OneStepHenkinConst Base Const τ
  | exWitness : {σ : Ty Base} → Formula Const [σ] → OneStepHenkinConst Base Const σ
  | allCounterexample :
      {σ : Ty Base} → Formula Const [σ] → OneStepHenkinConst Base Const σ

namespace OneStepHenkinConst

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Embed original constants into the one-step Henkinized signature. -/
def lift : ∀ {τ : Ty Base}, Const τ → OneStepHenkinConst Base Const τ :=
  fun c => .base c

/-- The canonical one-step witness provider into the Henkinized signature. -/
def witnessProvider :
    WitnessProvider Base Const (OneStepHenkinConst Base Const) where
  liftConst := lift
  exWitness := fun φ => .const (.exWitness φ)
  allCounterexample := fun φ => .const (.allCounterexample φ)

abbrev liftTerm {Γ : Ctx Base} {τ : Ty Base} :
    Term Const Γ τ → Term (OneStepHenkinConst Base Const) Γ τ :=
  (witnessProvider (Base := Base) (Const := Const)).liftTerm

abbrev liftFormula {Γ : Ctx Base} :
    Formula Const Γ → Formula (OneStepHenkinConst Base Const) Γ :=
  (witnessProvider (Base := Base) (Const := Const)).liftFormula

abbrev liftClosedFormula :
    ClosedFormula Const → ClosedFormula (OneStepHenkinConst Base Const) :=
  (witnessProvider (Base := Base) (Const := Const)).liftClosedFormula

def exWitnessTerm {σ : Ty Base} (φ : Formula Const [σ]) :
    ClosedTerm (OneStepHenkinConst Base Const) σ :=
  (witnessProvider (Base := Base) (Const := Const)).exWitness φ

def allCounterexampleTerm {σ : Ty Base} (φ : Formula Const [σ]) :
    ClosedTerm (OneStepHenkinConst Base Const) σ :=
  (witnessProvider (Base := Base) (Const := Const)).allCounterexample φ

def exWitnessInstance {σ : Ty Base} (φ : Formula Const [σ]) :
    ClosedFormula (OneStepHenkinConst Base Const) :=
  (witnessProvider (Base := Base) (Const := Const)).exWitnessInstance φ

def allCounterexampleInstance {σ : Ty Base} (φ : Formula Const [σ]) :
    ClosedFormula (OneStepHenkinConst Base Const) :=
  (witnessProvider (Base := Base) (Const := Const)).allCounterexampleInstance φ

@[simp] theorem lift_const {τ : Ty Base} (c : Const τ) :
    lift (Base := Base) c = .base c := rfl

/--
The one-step Henkin axioms over the immediate witness extension.

This is the exact local theory that the future generic conservativity theorem
should eliminate before reflecting back to the source signature.
-/
def ExactHenkinAxioms : ClosedTheorySet (OneStepHenkinConst Base Const) :=
  fun ψ =>
    (∃ (σ : Ty Base) (φ : Formula Const [σ]),
      ψ = .imp (.ex (liftFormula (Base := Base) (Const := Const) φ))
        (exWitnessInstance (Base := Base) (Const := Const) φ)) ∨
    (∃ (σ : Ty Base) (φ : Formula Const [σ]),
      ψ =
        .imp
          (allCounterexampleInstance (Base := Base) (Const := Const) φ)
          (.all (liftFormula (Base := Base) (Const := Const) φ)))

/--
Generic one-step conservativity target.

This is the theorem boundary the council now prefers for fresh-parameter
elimination: if a closed source formula is provable after a single witness
extension using only lifted old assumptions and the exact one-step Henkin axioms,
then it was already provable over the source signature.
-/
def ConservativityGoal : Prop :=
  ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
    ClosedTheorySet.Provable
      (Const := OneStepHenkinConst Base Const)
      (fun ψ =>
        ψ ∈ Δ.map (liftClosedFormula (Base := Base) (Const := Const) ) ∨
          ψ ∈ ExactHenkinAxioms (Base := Base) (Const := Const))
      (liftClosedFormula (Base := Base) (Const := Const) φ) →
        ExtDerivation Const Δ φ

/--
**Obstruction witness**: The one-step extension of an empty signature can prove
`∃x:b. ⊤` using the fresh `.exWitness` constant, even with no Henkin axioms.

This demonstrates that raw `ConservativityGoal` (without `BaseWitnesses`) is the
wrong theorem target — the one-step extension is NOT conservative over signatures
that lack constants at some base type.
-/
theorem emptySignature_oneStep_existsTop :
    ExtDerivation
      (OneStepHenkinConst Unit (fun _ => PEmpty)) []
      (liftClosedFormula (Base := Unit) (Const := fun _ => PEmpty)
        (.ex (.top : Formula (fun _ => PEmpty) [.base ()]))) := by
  apply ExtDerivation.exI
    (.const (.exWitness (.top : Formula (fun _ => PEmpty) [.base ()])))
  simp [mapConst, instantiate, subst]
  exact ExtDerivation.topI

end OneStepHenkinConst

end Mettapedia.Logic.HOL
