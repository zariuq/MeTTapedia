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

/-- Lifted source terms have no occurrence of any fresh constant.
    Every constant in `liftTerm t` is `.base c`, so `.exWitness` and
    `.allCounterexample` constants never appear. -/
theorem noConstOccurrence_liftTerm
    {σ : Ty Base} (d : OneStepHenkinConst Base Const σ)
    (hfresh : ∀ (c : Const σ), d ≠ .base c) :
    ∀ {Γ : Ctx Base} {τ : Ty Base}
      (t : Term Const Γ τ),
      NoConstOccurrence d
        (liftTerm (Base := Base) (Const := Const) t)
  | _, _, .var _ => .var
  | _, _, .const c => by
      simp only [liftTerm, mapConst]
      by_cases hτ : σ = ‹Ty Base›
      · subst hτ; exact .const_same_ne _ (hfresh c).symm
      · exact .const_diff_type hτ _
  | _, _, .app f t => .app (noConstOccurrence_liftTerm d hfresh f) (noConstOccurrence_liftTerm d hfresh t)
  | _, _, .lam body => .lam (noConstOccurrence_liftTerm d hfresh body)
  | _, _, .top => .top
  | _, _, .bot => .bot
  | _, _, .and p q => .and (noConstOccurrence_liftTerm d hfresh p) (noConstOccurrence_liftTerm d hfresh q)
  | _, _, .or p q => .or (noConstOccurrence_liftTerm d hfresh p) (noConstOccurrence_liftTerm d hfresh q)
  | _, _, .imp p q => .imp (noConstOccurrence_liftTerm d hfresh p) (noConstOccurrence_liftTerm d hfresh q)
  | _, _, .not p => .not (noConstOccurrence_liftTerm d hfresh p)
  | _, _, .eq t u => .eq (noConstOccurrence_liftTerm d hfresh t) (noConstOccurrence_liftTerm d hfresh u)
  | _, _, .all body => .all (noConstOccurrence_liftTerm d hfresh body)
  | _, _, .ex body => .ex (noConstOccurrence_liftTerm d hfresh body)

/-- `.exWitness` constants are fresh (not `.base`). -/
theorem exWitness_ne_base (φ : Formula Const [σ]) (c : Const σ) :
    (OneStepHenkinConst.exWitness φ : OneStepHenkinConst Base Const σ) ≠ .base c := by
  intro h; cases h

/-- `.allCounterexample` constants are fresh (not `.base`). -/
theorem allCounterexample_ne_base (φ : Formula Const [σ]) (c : Const σ) :
    (OneStepHenkinConst.allCounterexample φ : OneStepHenkinConst Base Const σ) ≠ .base c := by
  intro h; cases h

/--
Retraction from the one-step Henkin signature back to the source.

Under the assumption that `Const τ` is nonempty at every type, maps `.base c ↦ c`
and fresh constants to an arbitrary value via `Classical.choice`. The fresh-constant
values are never encountered when retracting derivations whose constants are all `.base`.

Council notes (Brown, Buzzard, Carneiro, Henkin):
  This assumption is trivially satisfied in Henkin-saturated signatures (the intended
  application). A future `substConst` infrastructure would remove it.
-/
noncomputable def retractConst
    [inst : ∀ (τ : Ty Base), Nonempty (Const τ)] :
    ∀ {τ : Ty Base}, OneStepHenkinConst Base Const τ → Const τ
  | _, .base c => c
  | τ, .exWitness _ => Classical.choice (inst τ)
  | τ, .allCounterexample _ => Classical.choice (inst τ)

theorem retractConst_lift
    [inst : ∀ (τ : Ty Base), Nonempty (Const τ)]
    {τ : Ty Base} (c : Const τ) :
    retractConst (Base := Base) (lift c) = c := rfl

@[simp] theorem mapConst_retractConst_liftClosedFormula
    [inst : ∀ (τ : Ty Base), Nonempty (Const τ)]
    (φ : ClosedFormula Const) :
    Mettapedia.Logic.HOL.mapConst (fun {_τ} => retractConst (Base := Base))
      (liftClosedFormula (Base := Base) (Const := Const) φ) = φ := by
  simp only [liftClosedFormula, WitnessProvider.liftClosedFormula]
  rw [Mettapedia.Logic.HOL.mapConst_comp]
  exact Mettapedia.Logic.HOL.mapConst_id φ

/--
Retract a derivation in the one-step language back to the source language.

If the derivation's hypotheses are all `liftClosedFormula` of source formulas
and the conclusion is `liftClosedFormula φ`, applying `mapConst retractConst`
strips the `.base` wrappers and produces a source-language derivation.
-/
theorem retractDerivation
    [inst : ∀ (τ : Ty Base), Nonempty (Const τ)]
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (d : ExtDerivation (OneStepHenkinConst Base Const)
      (Δ.map (liftClosedFormula (Base := Base) (Const := Const)))
      (liftClosedFormula (Base := Base) (Const := Const) φ)) :
    ExtDerivation Const Δ φ := by
  have d' := ExtDerivation.mapConst
    (fun {τ} => retractConst (Base := Base) (inst := inst))
    d
  have hΔ : (Δ.map liftClosedFormula).map
      (Mettapedia.Logic.HOL.mapConst fun {τ} => retractConst (Base := Base) (inst := inst)) = Δ := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id Δ]
    exact List.map_congr_left fun χ _ => mapConst_retractConst_liftClosedFormula χ
  rw [hΔ] at d'
  convert d' using 1
  exact (mapConst_retractConst_liftClosedFormula φ).symm

end OneStepHenkinConst

end Mettapedia.Logic.HOL
