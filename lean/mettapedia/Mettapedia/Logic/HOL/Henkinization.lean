import Mettapedia.Logic.HOL.Syntax.ConstMap

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

end OneStepHenkinConst

end Mettapedia.Logic.HOL
