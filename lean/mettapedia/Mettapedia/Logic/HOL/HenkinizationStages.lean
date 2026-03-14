import Mettapedia.Logic.HOL.Henkinization

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/--
Stage-indexed cumulative Henkinization.

Stage `0` contains the original constants, universe-lifted so the recursive
family remains in a stable universe. Stage `n + 1` is the one-step Henkin
extension of stage `n`.
-/
def HenkinConstStage (Base : Type u) (Const : Ty Base → Type v) :
    Nat → Ty Base → Type (max u (v + 1))
  | 0, τ => ULift.{max u (v + 1), v} (Const τ)
  | n + 1, τ => by
      exact
        (show Type (max u (v + 1)) from
          OneStepHenkinConst Base (HenkinConstStage Base Const n) τ)

namespace HenkinConstStage

/-- Embed original constants into stage `0`. -/
def ofBase {τ : Ty Base} (c : Const τ) :
    HenkinConstStage Base Const 0 τ :=
  ULift.up c

/-- Lift a stage-`n` constant through `k` additional Henkinization stages. -/
def liftOffset :
    (k : Nat) → {n : Nat} → {τ : Ty Base} →
      HenkinConstStage Base Const n τ →
        HenkinConstStage Base Const (n + k) τ
  | 0, _, _, c => by
      simpa using c
  | k + 1, n, τ, c => by
      change OneStepHenkinConst Base (HenkinConstStage Base Const (n + k)) τ
      exact OneStepHenkinConst.base (liftOffset k c)

/-- Lift stage-`m` constants into any later stage `n`. -/
def lift {m n : Nat} (h : m ≤ n) {τ : Ty Base} :
    HenkinConstStage Base Const m τ →
      HenkinConstStage Base Const n τ := by
  intro c
  let k := n - m
  have hk : m + k = n := by
    dsimp [k]
    exact Nat.add_sub_of_le h
  simpa [k, hk] using
    (liftOffset (Base := Base) (Const := Const) (k := k) (n := m) c)

/-- Lift terms from stage `m` to stage `n`. -/
abbrev liftTerm {m n : Nat} (h : m ≤ n) {Γ : Ctx Base} {τ : Ty Base} :
    Term (HenkinConstStage Base Const m) Γ τ →
      Term (HenkinConstStage Base Const n) Γ τ :=
  mapConst (lift (Base := Base) (Const := Const) h)

/-- Lift formulas from stage `m` to stage `n`. -/
abbrev liftFormula {m n : Nat} (h : m ≤ n) {Γ : Ctx Base} :
    Formula (HenkinConstStage Base Const m) Γ →
      Formula (HenkinConstStage Base Const n) Γ :=
  mapConst (lift (Base := Base) (Const := Const) h)

/-- Lift closed formulas from stage `m` to stage `n`. -/
abbrev liftClosedFormula {m n : Nat} (h : m ≤ n) :
    ClosedFormula (HenkinConstStage Base Const m) →
      ClosedFormula (HenkinConstStage Base Const n) :=
  mapConst (lift (Base := Base) (Const := Const) h)

/-- The designated existential witness term at the next Henkin stage. -/
def exWitnessTerm {n : Nat} {σ : Ty Base}
    (φ : Formula (HenkinConstStage Base Const n) [σ]) :
    ClosedTerm (HenkinConstStage Base Const (n + 1)) σ := by
  change ClosedTerm (OneStepHenkinConst Base (HenkinConstStage Base Const n)) σ
  exact .const (OneStepHenkinConst.exWitness φ)

/-- The designated universal counterexample term at the next Henkin stage. -/
def allCounterexampleTerm {n : Nat} {σ : Ty Base}
    (φ : Formula (HenkinConstStage Base Const n) [σ]) :
    ClosedTerm (HenkinConstStage Base Const (n + 1)) σ := by
  change ClosedTerm (OneStepHenkinConst Base (HenkinConstStage Base Const n)) σ
  exact .const (OneStepHenkinConst.allCounterexample φ)

/-- The instantiated existential witness formula at the next Henkin stage. -/
def exWitnessInstance {n : Nat} {σ : Ty Base}
    (φ : Formula (HenkinConstStage Base Const n) [σ]) :
    ClosedFormula (HenkinConstStage Base Const (n + 1)) :=
  instantiate (Base := Base)
    (exWitnessTerm (Base := Base) (Const := Const) φ)
    (liftFormula (Base := Base) (Const := Const) (Nat.le_succ n) φ)

/-- The instantiated universal counterexample formula at the next Henkin stage. -/
def allCounterexampleInstance {n : Nat} {σ : Ty Base}
    (φ : Formula (HenkinConstStage Base Const n) [σ]) :
    ClosedFormula (HenkinConstStage Base Const (n + 1)) :=
  instantiate (Base := Base)
    (allCounterexampleTerm (Base := Base) (Const := Const) φ)
    (liftFormula (Base := Base) (Const := Const) (Nat.le_succ n) φ)

end HenkinConstStage

end Mettapedia.Logic.HOL
