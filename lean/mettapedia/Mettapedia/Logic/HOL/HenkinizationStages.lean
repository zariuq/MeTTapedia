import Mettapedia.Logic.HOL.Henkinization
import Mettapedia.Logic.HOL.DerivationExtensionality

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

/-- Lift original-signature terms directly into stage `n`. -/
abbrev liftBaseTerm (n : Nat) {Γ : Ctx Base} {τ : Ty Base} :
    Term Const Γ τ → Term (HenkinConstStage Base Const n) Γ τ :=
  mapConst (fun c =>
    lift (Base := Base) (Const := Const) (Nat.zero_le n)
      (ofBase (Base := Base) c))

/-- Lift original-signature formulas directly into stage `n`. -/
abbrev liftBaseFormula (n : Nat) {Γ : Ctx Base} :
    Formula Const Γ → Formula (HenkinConstStage Base Const n) Γ :=
  mapConst (fun c =>
    lift (Base := Base) (Const := Const) (Nat.zero_le n)
      (ofBase (Base := Base) c))

/-- Lift original-signature closed formulas directly into stage `n`. -/
abbrev liftBaseClosedFormula (n : Nat) :
    ClosedFormula Const → ClosedFormula (HenkinConstStage Base Const n) :=
  mapConst (fun c =>
    lift (Base := Base) (Const := Const) (Nat.zero_le n)
      (ofBase (Base := Base) c))

@[simp] theorem down_lift_ofBase_zero {τ : Ty Base} (c : Const τ) :
    (lift (Base := Base) (Const := Const) (Nat.zero_le 0)
      (ofBase (Base := Base) c)).down = c := by
  simp [lift, ofBase, HenkinConstStage.liftOffset]

@[simp] theorem reflectZero_liftBaseTerm
    {Γ : Ctx Base} {τ : Ty Base}
    (t : Term Const Γ τ) :
    Mettapedia.Logic.HOL.mapConst (fun c => c.down)
      (liftBaseTerm (Base := Base) (Const := Const) 0 t) = t := by
  rw [liftBaseTerm, Mettapedia.Logic.HOL.mapConst_comp]
  simp [Mettapedia.Logic.HOL.mapConst_id, ofBase, lift,
    HenkinConstStage.liftOffset]

@[simp] theorem reflectZero_liftBaseFormula
    {Γ : Ctx Base}
    (φ : Formula Const Γ) :
    Mettapedia.Logic.HOL.mapConst (fun c => c.down)
      (liftBaseFormula (Base := Base) (Const := Const) 0 φ) = φ :=
  reflectZero_liftBaseTerm (Base := Base) (Const := Const) φ

@[simp] theorem reflectZero_liftBaseClosedFormula
    (φ : ClosedFormula Const) :
    Mettapedia.Logic.HOL.mapClosedFormula (fun c => c.down)
      (liftBaseClosedFormula (Base := Base) (Const := Const) 0 φ) = φ :=
  reflectZero_liftBaseFormula (Base := Base) (Const := Const) φ

@[simp] theorem reflectZero_liftBaseClosedTheory
    (Δ : List (ClosedFormula Const)) :
    List.map
      ((Mettapedia.Logic.HOL.mapClosedFormula (fun c => c.down)) ∘
        liftBaseClosedFormula (Base := Base) (Const := Const) 0)
      Δ = Δ := by
  induction Δ with
  | nil => rfl
  | cons φ Δ ih =>
      simp [Function.comp, ih]

theorem liftBase_formulaProvable
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (n : Nat) (d : ExtDerivation Const Δ φ) :
    ExtDerivation (HenkinConstStage Base Const n)
      (Δ.map (liftBaseFormula (Base := Base) (Const := Const) n))
      (liftBaseFormula (Base := Base) (Const := Const) n φ) := by
  simpa [liftBaseFormula, Mettapedia.Logic.HOL.mapConst] using
    (ExtDerivation.mapConst
      (Base := Base)
      (Const := Const)
      (Const' := HenkinConstStage Base Const n)
      (f := fun c =>
        lift (Base := Base) (Const := Const) (Nat.zero_le n)
          (ofBase (Base := Base) c))
      (Δ := Δ)
      (φ := φ)
      d)

theorem reflectZero_formulaProvable
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstStage Base Const 0) Γ)}
    {φ : Formula (HenkinConstStage Base Const 0) Γ}
    (d : ExtDerivation (HenkinConstStage Base Const 0) Δ φ) :
    ExtDerivation Const
      (Δ.map (Mettapedia.Logic.HOL.mapConst (fun c => c.down)))
      (Mettapedia.Logic.HOL.mapConst (fun c => c.down) φ) := by
  simpa [Mettapedia.Logic.HOL.mapConst] using
    (ExtDerivation.mapConst
      (Base := Base)
      (Const := HenkinConstStage Base Const 0)
      (Const' := Const)
      (f := fun c => c.down)
      (Δ := Δ)
      (φ := φ)
      d)

theorem liftBase_closedTheory_zero_of_original
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (d : ExtDerivation Const Δ φ) :
    ExtDerivation (HenkinConstStage Base Const 0)
      (Δ.map (liftBaseClosedFormula (Base := Base) (Const := Const) 0))
      (liftBaseClosedFormula (Base := Base) (Const := Const) 0 φ) :=
  liftBase_formulaProvable (Base := Base) (Const := Const) 0 d

theorem original_closedTheory_of_stageZero
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (d : ExtDerivation (HenkinConstStage Base Const 0)
      (Δ.map (liftBaseClosedFormula (Base := Base) (Const := Const) 0))
      (liftBaseClosedFormula (Base := Base) (Const := Const) 0 φ)) :
    ExtDerivation Const Δ φ := by
  have h' : ExtDerivation Const
      ((Δ.map (liftBaseClosedFormula (Base := Base) (Const := Const) 0)).map
        (Mettapedia.Logic.HOL.mapClosedFormula (fun c => c.down)))
      (Mettapedia.Logic.HOL.mapClosedFormula (fun c => c.down)
        (liftBaseClosedFormula (Base := Base) (Const := Const) 0 φ)) :=
    reflectZero_formulaProvable (Base := Base) (Const := Const) d
  simpa [Mettapedia.Logic.HOL.mapClosedFormula, List.map_map, Function.comp] using h'

theorem original_closedTheory_iff_stageZero
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const} :
    ExtDerivation Const Δ φ ↔
      ExtDerivation (HenkinConstStage Base Const 0)
        (Δ.map (liftBaseClosedFormula (Base := Base) (Const := Const) 0))
        (liftBaseClosedFormula (Base := Base) (Const := Const) 0 φ) := by
  constructor
  · exact liftBase_closedTheory_zero_of_original (Base := Base) (Const := Const)
  · exact original_closedTheory_of_stageZero (Base := Base) (Const := Const)

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
