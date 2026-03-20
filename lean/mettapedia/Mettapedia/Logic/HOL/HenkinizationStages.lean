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

/--
Transport-aware composition law for `liftOffset`.

This is the mathematically clean dependent equality behind stage-lift
composition: first lift by `k₁`, then by `k₂`, and transport across the
associativity witness on stage indices.
-/
def LiftOffsetCompGoal : Prop :=
  ∀ (k₁ k₂ : Nat) {n : Nat} {τ : Ty Base}
    (c : HenkinConstStage Base Const n τ),
      cast
          (congrArg (fun t => HenkinConstStage Base Const t τ)
            (Nat.add_assoc n k₁ k₂))
          (liftOffset (Base := Base) (Const := Const) k₂
            (liftOffset (Base := Base) (Const := Const) k₁ c)) =
        liftOffset (Base := Base) (Const := Const) (k₁ + k₂) c

/--
Ordinary stage-lift composition.

Downstream transport lemmas should be derived from this goal, not reproved
ad hoc. The hard work is expected to live at the constant-level here.
-/
def LiftCompGoal : Prop :=
  ∀ {l m n : Nat} (hlm : l ≤ m) (hmn : m ≤ n) {τ : Ty Base}
    (c : HenkinConstStage Base Const l τ),
      lift (Base := Base) (Const := Const) hmn
          (lift (Base := Base) (Const := Const) hlm c) =
        lift (Base := Base) (Const := Const) (Nat.le_trans hlm hmn) c

@[simp] theorem cast_base_succ {n m : Nat} (h : n = m) {τ : Ty Base}
    (c : HenkinConstStage Base Const n τ) :
    cast (congrArg (fun t => HenkinConstStage Base Const (t + 1) τ) h)
        (OneStepHenkinConst.base c : HenkinConstStage Base Const (n + 1) τ) =
      (OneStepHenkinConst.base
        (cast (congrArg (fun t => HenkinConstStage Base Const t τ) h) c) :
          HenkinConstStage Base Const (m + 1) τ) := by
  cases h
  rfl

@[simp] theorem liftOffset_cast
    {k n m : Nat} (h : n = m) {τ : Ty Base}
    (c : HenkinConstStage Base Const n τ) :
    cast (congrArg (fun t => HenkinConstStage Base Const (t + k) τ) h)
        (liftOffset (Base := Base) (Const := Const) k c) =
      liftOffset (Base := Base) (Const := Const) k
        (cast (congrArg (fun t => HenkinConstStage Base Const t τ) h) c) := by
  cases h
  rfl

@[simp] theorem liftOffset_congr
    {n k₁ k₂ : Nat} (h : k₁ = k₂) {τ : Ty Base}
    (c : HenkinConstStage Base Const n τ) :
    cast (congrArg (fun t => HenkinConstStage Base Const (n + t) τ) h)
        (liftOffset (Base := Base) (Const := Const) k₁ c) =
      liftOffset (Base := Base) (Const := Const) k₂ c := by
  cases h
  rfl

@[simp] theorem lift_add_right_eq_liftOffset
    {n k : Nat} {τ : Ty Base}
    (c : HenkinConstStage Base Const n τ) :
    lift (Base := Base) (Const := Const) (Nat.le_add_right n k) c =
      liftOffset (Base := Base) (Const := Const) k c := by
  rw [lift]
  let k' := n + k - n
  have hsub : k' = k := by
    dsimp [k']
    simpa [Nat.add_comm] using (Nat.add_sub_cancel_left n k)
  simpa [k'] using
    (liftOffset_congr (Base := Base) (Const := Const)
      (n := n) (k₁ := k') (k₂ := k) hsub c)

theorem lift_eq_cast_liftOffset
    {m n : Nat} (h : m ≤ n) {τ : Ty Base}
    (c : HenkinConstStage Base Const m τ) :
    lift (Base := Base) (Const := Const) h c =
      cast (congrArg (fun t => HenkinConstStage Base Const t τ)
        (Nat.add_sub_of_le h))
        (liftOffset (Base := Base) (Const := Const) (n - m) c) := by
  unfold lift
  let k := n - m
  have hk : m + k = n := by
    dsimp [k]
    exact Nat.add_sub_of_le h
  simpa [k, hk]

theorem liftOffset_comp : LiftOffsetCompGoal (Base := Base) (Const := Const) := by
  intro k₁ k₂
  induction k₂ with
  | zero =>
      intro n τ c
      simp [liftOffset]
  | succ k₂ ih =>
      intro n τ c
      have hih :
          cast
              (congrArg (fun t => HenkinConstStage Base Const t τ)
                (Nat.add_assoc n k₁ k₂))
              (liftOffset (Base := Base) (Const := Const) k₂
                (liftOffset (Base := Base) (Const := Const) k₁ c)) =
            liftOffset (Base := Base) (Const := Const) (k₁ + k₂) c :=
        ih c
      have hcast :=
        cast_base_succ (Base := Base) (Const := Const)
          (h := Nat.add_assoc n k₁ k₂)
          (c := liftOffset (Base := Base) (Const := Const) k₂
            (liftOffset (Base := Base) (Const := Const) k₁ c))
      have hbase :
          (OneStepHenkinConst.base
            (cast
              (congrArg (fun t => HenkinConstStage Base Const t τ)
                (Nat.add_assoc n k₁ k₂))
              (liftOffset (Base := Base) (Const := Const) k₂
                (liftOffset (Base := Base) (Const := Const) k₁ c))) :
              HenkinConstStage Base Const ((n + (k₁ + k₂)) + 1) τ) =
            (OneStepHenkinConst.base
              (liftOffset (Base := Base) (Const := Const) (k₁ + k₂) c) :
              HenkinConstStage Base Const ((n + (k₁ + k₂)) + 1) τ) :=
        congrArg
          (fun x : HenkinConstStage Base Const (n + (k₁ + k₂)) τ =>
            (OneStepHenkinConst.base x :
              HenkinConstStage Base Const ((n + (k₁ + k₂)) + 1) τ))
          hih
      simpa [liftOffset, Nat.add_assoc] using hcast.trans hbase

theorem liftOffset_comp_cast
    {n k₁ k₂ : Nat} {τ : Ty Base}
    (c : HenkinConstStage Base Const n τ) :
    cast (congrArg (fun t => HenkinConstStage Base Const t τ)
      (Nat.add_assoc n k₁ k₂).symm)
      (liftOffset (Base := Base) (Const := Const) (k₁ + k₂) c) =
    (liftOffset (Base := Base) (Const := Const) k₂
      (liftOffset (Base := Base) (Const := Const) k₁ c) :
        HenkinConstStage Base Const (n + k₁ + k₂) τ) := by
  have h := congrArg
    (fun x : HenkinConstStage Base Const (n + (k₁ + k₂)) τ =>
      cast (congrArg (fun t => HenkinConstStage Base Const t τ)
        (Nat.add_assoc n k₁ k₂).symm) x)
    ((liftOffset_comp (Base := Base) (Const := Const) k₁ k₂ c).symm)
  simpa [Nat.add_assoc] using h

theorem lift_comp : LiftCompGoal (Base := Base) (Const := Const) := by
  intro l m n hlm hmn τ c
  let F := fun t => HenkinConstStage Base Const t τ
  let k₁ := m - l
  let k₂ := n - m
  have hk₁ : l + k₁ = m := by
    dsimp [k₁]
    exact Nat.add_sub_of_le hlm
  have hk₂ : m + k₂ = n := by
    dsimp [k₂]
    exact Nat.add_sub_of_le hmn
  have hsum : k₁ + k₂ = n - l := by
    dsimp [k₁, k₂]
    calc
      (m - l) + (n - m) = (n - m) + (m - l) := by rw [Nat.add_comm]
      _ = ((n - m) + m) - l := by
        symm
        exact Nat.add_sub_assoc hlm (n - m)
      _ = n - l := by rw [Nat.add_comm, Nat.add_sub_of_le hmn]
  have eassoc : l + (k₁ + k₂) = l + k₁ + k₂ := by
    exact (Nat.add_assoc l k₁ k₂).symm
  have eleftmid : l + k₁ + k₂ = m + k₂ := by
    simpa [Nat.add_assoc] using congrArg (fun t => t + k₂) hk₁
  have eleft : l + (k₁ + k₂) = n := eassoc.trans eleftmid |>.trans hk₂
  have erightmid : l + (k₁ + k₂) = l + (n - l) := by
    exact congrArg (fun t => l + t) hsum
  have eright :
      l + (k₁ + k₂) = n :=
    erightmid.trans (Nat.add_sub_of_le (Nat.le_trans hlm hmn))
  have hleft :
      lift (Base := Base) (Const := Const) hmn
          (lift (Base := Base) (Const := Const) hlm c) =
        cast (congrArg F eleft)
          (liftOffset (Base := Base) (Const := Const) (k₁ + k₂) c) := by
    rw [lift_eq_cast_liftOffset (Base := Base) (Const := Const) (h := hmn)]
    rw [lift_eq_cast_liftOffset (Base := Base) (Const := Const) (h := hlm)]
    rw [← liftOffset_cast (Base := Base) (Const := Const)
      (h := hk₁) (k := k₂)
      (c := liftOffset (Base := Base) (Const := Const) k₁ c)]
    rw [← liftOffset_comp_cast (Base := Base) (Const := Const)
      (n := l) (k₁ := k₁) (k₂ := k₂) c]
    simpa [F, eleft, eassoc, eleftmid, cast_cast]
  have hright :
      lift (Base := Base) (Const := Const) (Nat.le_trans hlm hmn) c =
        cast (congrArg F eright)
          (liftOffset (Base := Base) (Const := Const) (k₁ + k₂) c) := by
    rw [lift_eq_cast_liftOffset (Base := Base) (Const := Const)
      (h := Nat.le_trans hlm hmn)]
    have hcongr :=
      liftOffset_congr (Base := Base) (Const := Const)
        (n := l) (k₁ := k₁ + k₂) (k₂ := n - l) hsum c
    have hcast :=
      congrArg
        (fun x : HenkinConstStage Base Const (l + (n - l)) τ =>
          cast (congrArg F (Nat.add_sub_of_le (Nat.le_trans hlm hmn))) x)
        hcongr
    simpa [F, eright, cast_cast] using hcast.symm
  have hproof : congrArg F eleft = congrArg F eright := by
    apply Subsingleton.elim
  have hcast :
      cast (congrArg F eleft)
          (liftOffset (Base := Base) (Const := Const) (k₁ + k₂) c) =
        cast (congrArg F eright)
          (liftOffset (Base := Base) (Const := Const) (k₁ + k₂) c) := by
    cases hproof
    rfl
  exact hleft.trans (hcast.trans hright.symm)

theorem liftTerm_comp_of_liftComp
    (hComp : LiftCompGoal (Base := Base) (Const := Const))
    {l m n : Nat} (hlm : l ≤ m) (hmn : m ≤ n)
    {Γ : Ctx Base} {τ : Ty Base}
    (t : Term (HenkinConstStage Base Const l) Γ τ) :
    liftTerm (Base := Base) (Const := Const) hmn
        (liftTerm (Base := Base) (Const := Const) hlm t) =
      liftTerm (Base := Base) (Const := Const) (Nat.le_trans hlm hmn) t := by
  rw [liftTerm, liftTerm, Mettapedia.Logic.HOL.mapConst_comp]
  apply Mettapedia.Logic.HOL.mapConst_ext
  intro τ c
  exact hComp hlm hmn c

theorem liftFormula_comp_of_liftComp
    (hComp : LiftCompGoal (Base := Base) (Const := Const))
    {l m n : Nat} (hlm : l ≤ m) (hmn : m ≤ n)
    {Γ : Ctx Base}
    (φ : Formula (HenkinConstStage Base Const l) Γ) :
    liftFormula (Base := Base) (Const := Const) hmn
        (liftFormula (Base := Base) (Const := Const) hlm φ) =
      liftFormula (Base := Base) (Const := Const) (Nat.le_trans hlm hmn) φ :=
  liftTerm_comp_of_liftComp (Base := Base) (Const := Const) hComp hlm hmn φ

theorem liftClosedFormula_comp_of_liftComp
    (hComp : LiftCompGoal (Base := Base) (Const := Const))
    {l m n : Nat} (hlm : l ≤ m) (hmn : m ≤ n)
    (φ : ClosedFormula (HenkinConstStage Base Const l)) :
    liftClosedFormula (Base := Base) (Const := Const) hmn
        (liftClosedFormula (Base := Base) (Const := Const) hlm φ) =
      liftClosedFormula (Base := Base) (Const := Const) (Nat.le_trans hlm hmn) φ :=
  liftFormula_comp_of_liftComp (Base := Base) (Const := Const) hComp hlm hmn φ

theorem liftTerm_comp
    {l m n : Nat} (hlm : l ≤ m) (hmn : m ≤ n)
    {Γ : Ctx Base} {τ : Ty Base}
    (t : Term (HenkinConstStage Base Const l) Γ τ) :
    liftTerm (Base := Base) (Const := Const) hmn
        (liftTerm (Base := Base) (Const := Const) hlm t) =
      liftTerm (Base := Base) (Const := Const) (Nat.le_trans hlm hmn) t :=
  liftTerm_comp_of_liftComp (Base := Base) (Const := Const)
    (lift_comp (Base := Base) (Const := Const)) hlm hmn t

theorem liftFormula_comp
    {l m n : Nat} (hlm : l ≤ m) (hmn : m ≤ n)
    {Γ : Ctx Base}
    (φ : Formula (HenkinConstStage Base Const l) Γ) :
    liftFormula (Base := Base) (Const := Const) hmn
        (liftFormula (Base := Base) (Const := Const) hlm φ) =
      liftFormula (Base := Base) (Const := Const) (Nat.le_trans hlm hmn) φ :=
  liftFormula_comp_of_liftComp (Base := Base) (Const := Const)
    (lift_comp (Base := Base) (Const := Const)) hlm hmn φ

theorem liftClosedFormula_comp
    {l m n : Nat} (hlm : l ≤ m) (hmn : m ≤ n)
    (φ : ClosedFormula (HenkinConstStage Base Const l)) :
    liftClosedFormula (Base := Base) (Const := Const) hmn
        (liftClosedFormula (Base := Base) (Const := Const) hlm φ) =
      liftClosedFormula (Base := Base) (Const := Const) (Nat.le_trans hlm hmn) φ :=
  liftClosedFormula_comp_of_liftComp (Base := Base) (Const := Const)
    (lift_comp (Base := Base) (Const := Const)) hlm hmn φ

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

theorem liftBaseTerm_comp
    {m n : Nat} (hmn : m ≤ n)
    {Γ : Ctx Base} {τ : Ty Base}
    (t : Term Const Γ τ) :
    liftTerm (Base := Base) (Const := Const) hmn
        (liftBaseTerm (Base := Base) (Const := Const) m t) =
      liftBaseTerm (Base := Base) (Const := Const) n t := by
  rw [liftTerm, liftBaseTerm, Mettapedia.Logic.HOL.mapConst_comp]
  apply Mettapedia.Logic.HOL.mapConst_ext
  intro σ c
  simpa [liftBaseTerm] using
    (lift_comp (Base := Base) (Const := Const)
      (l := 0) (m := m) (n := n)
      (Nat.zero_le m) hmn (ofBase (Base := Base) (Const := Const) c))

theorem liftBaseFormula_comp
    {m n : Nat} (hmn : m ≤ n)
    {Γ : Ctx Base}
    (φ : Formula Const Γ) :
    liftFormula (Base := Base) (Const := Const) hmn
        (liftBaseFormula (Base := Base) (Const := Const) m φ) =
      liftBaseFormula (Base := Base) (Const := Const) n φ :=
  liftBaseTerm_comp (Base := Base) (Const := Const) hmn φ

theorem liftBaseClosedFormula_comp
    {m n : Nat} (hmn : m ≤ n)
    (φ : ClosedFormula Const) :
    liftClosedFormula (Base := Base) (Const := Const) hmn
        (liftBaseClosedFormula (Base := Base) (Const := Const) m φ) =
      liftBaseClosedFormula (Base := Base) (Const := Const) n φ :=
  liftBaseFormula_comp (Base := Base) (Const := Const) hmn φ

@[simp] theorem down_lift_ofBase_zero {τ : Ty Base} (c : Const τ) :
    (lift (Base := Base) (Const := Const) (Nat.zero_le 0)
      (ofBase (Base := Base) c)).down = c := by
  simp [lift, ofBase, HenkinConstStage.liftOffset]

@[simp] theorem down_lift_zero {τ : Ty Base}
    (c : HenkinConstStage Base Const 0 τ) :
    (lift (Base := Base) (Const := Const) (Nat.zero_le 0) c).down = c.down := by
  cases c
  rfl

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
      simp [Function.comp, ih, ofBase]

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
  simpa [Mettapedia.Logic.HOL.mapClosedFormula, List.map_map, Function.comp, ofBase] using h'

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

/-- The existential Henkin axiom generated from a stage-`n` formula. -/
def exWitnessAxiom {n : Nat} {σ : Ty Base}
    (φ : Formula (HenkinConstStage Base Const n) [σ]) :
    ClosedFormula (HenkinConstStage Base Const (n + 1)) :=
  .imp
    (.ex (liftFormula (Base := Base) (Const := Const) (Nat.le_succ n) φ))
    (exWitnessInstance (Base := Base) (Const := Const) φ)

/-- The universal counterexample Henkin axiom generated from a stage-`n` formula. -/
def allCounterexampleAxiom {n : Nat} {σ : Ty Base}
    (φ : Formula (HenkinConstStage Base Const n) [σ]) :
    ClosedFormula (HenkinConstStage Base Const (n + 1)) :=
  .imp
    (allCounterexampleInstance (Base := Base) (Const := Const) φ)
    (.all (liftFormula (Base := Base) (Const := Const) (Nat.le_succ n) φ))

end HenkinConstStage

end Mettapedia.Logic.HOL
