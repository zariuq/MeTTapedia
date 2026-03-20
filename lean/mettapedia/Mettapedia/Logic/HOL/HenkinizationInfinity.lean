import Mettapedia.Logic.HOL.HenkinizationStages
import Mettapedia.Logic.HOL.DerivationExtensionality

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/--
Canonical cumulative Henkin signature.

Base constants are normalized to a unique constructor, while witness and
counterexample constants remember the finite stage whose formula generated them.
-/
inductive HenkinConstInfinity (Base : Type u) (Const : Ty Base → Type v) :
    Ty Base → Type (max u (v + 1)) where
  | base : Const τ → HenkinConstInfinity Base Const τ
  | exWitness :
      {n : Nat} → {σ : Ty Base} →
        Formula (HenkinConstStage Base Const n) [σ] →
          HenkinConstInfinity Base Const σ
  | allCounterexample :
      {n : Nat} → {σ : Ty Base} →
        Formula (HenkinConstStage Base Const n) [σ] →
          HenkinConstInfinity Base Const σ

namespace HenkinConstInfinity

/-- Collapse any finite Henkin stage into the canonical cumulative signature. -/
def ofStage :
    {n : Nat} → {τ : Ty Base} →
      HenkinConstStage Base Const n τ →
        HenkinConstInfinity Base Const τ
  | 0, _, c => .base c.down
  | _ + 1, _, .base c => ofStage c
  | n + 1, _, .exWitness φ => .exWitness (n := n) φ
  | n + 1, _, .allCounterexample φ => .allCounterexample (n := n) φ

theorem ofStage_liftOffset :
    ∀ (k : Nat) {n : Nat} {τ : Ty Base}
      (c : HenkinConstStage Base Const n τ),
      ofStage (HenkinConstStage.liftOffset (Base := Base) (Const := Const) k c) =
        ofStage c
  | 0, _, _, c => by
      simp [HenkinConstStage.liftOffset]
  | k + 1, _, _, c => by
      change
        ofStage
            (HenkinConstStage.liftOffset (Base := Base) (Const := Const) k c) =
          ofStage c
      exact ofStage_liftOffset k c

@[simp] theorem ofStage_ofBase {τ : Ty Base} (c : Const τ) :
    ofStage (HenkinConstStage.ofBase (Base := Base) c) = .base c := rfl

@[simp] theorem ofStage_cast
    {n m : Nat} (h : n = m) {τ : Ty Base}
    (c : HenkinConstStage Base Const n τ) :
    ofStage (Base := Base) (Const := Const)
        (cast (congrArg (fun t => HenkinConstStage Base Const t τ) h) c) =
      ofStage (Base := Base) (Const := Const) c := by
  cases h
  rfl

theorem ofStage_ne_exWitness_future :
    ∀ {n m : Nat} (hnm : n ≤ m) {τ : Ty Base}
      (c : HenkinConstStage Base Const n τ)
      (φ : Formula (HenkinConstStage Base Const m) [τ]),
      ofStage (Base := Base) (Const := Const) c ≠
        .exWitness (n := m) φ
  | 0, m, _, _, c, φ => by
      cases c
      intro h
      cases h
  | n + 1, m, hnm, _, c, φ => by
      cases c with
      | base c =>
          exact ofStage_ne_exWitness_future
            (Nat.le_trans (Nat.le_succ n) hnm) c φ
      | exWitness ψ =>
          intro h
          cases h
          exact Nat.not_succ_le_self n hnm
      | allCounterexample ψ =>
          intro h
          cases h

theorem ofStage_ne_allCounterexample_future :
    ∀ {n m : Nat} (hnm : n ≤ m) {τ : Ty Base}
      (c : HenkinConstStage Base Const n τ)
      (φ : Formula (HenkinConstStage Base Const m) [τ]),
      ofStage (Base := Base) (Const := Const) c ≠
        .allCounterexample (n := m) φ
  | 0, m, _, _, c, φ => by
      cases c
      intro h
      cases h
  | n + 1, m, hnm, _, c, φ => by
      cases c with
      | base c =>
          exact ofStage_ne_allCounterexample_future
            (Nat.le_trans (Nat.le_succ n) hnm) c φ
      | exWitness ψ =>
          intro h
          cases h
      | allCounterexample ψ =>
          intro h
          cases h
          exact Nat.not_succ_le_self n hnm

theorem ofStage_injective
    (n : Nat) {τ : Ty Base} :
    Function.Injective (@ofStage Base Const n τ) := by
  induction n with
  | zero =>
      intro c d h
      cases c
      cases d
      cases h
      rfl
  | succ n ih =>
      intro c d h
      cases c with
      | base c =>
          cases d with
          | base d =>
              have hcd : c = d := ih h
              cases hcd
              rfl
          | exWitness φ =>
              exfalso
              exact ofStage_ne_exWitness_future
                (n := n) (m := n)
                (Nat.le_refl n) c φ (by simpa using h)
          | allCounterexample φ =>
              exfalso
              exact ofStage_ne_allCounterexample_future
                (n := n) (m := n)
                (Nat.le_refl n) c φ (by simpa using h)
      | exWitness φ =>
          cases d with
          | base d =>
              exfalso
              exact ofStage_ne_exWitness_future
                (n := n) (m := n)
                (Nat.le_refl n) d φ (by simpa using h.symm)
          | exWitness ψ =>
              cases h
              rfl
          | allCounterexample ψ =>
              cases h
      | allCounterexample φ =>
          cases d with
          | base d =>
              exfalso
              exact ofStage_ne_allCounterexample_future
                (n := n) (m := n)
                (Nat.le_refl n) d φ (by simpa using h.symm)
          | exWitness ψ =>
              cases h
          | allCounterexample ψ =>
              cases h
              rfl

theorem ofStage_lift
    {m n : Nat} (hmn : m ≤ n) {τ : Ty Base}
    (c : HenkinConstStage Base Const m τ) :
    ofStage (Base := Base) (Const := Const)
        (HenkinConstStage.lift (Base := Base) (Const := Const) hmn c) =
      ofStage (Base := Base) (Const := Const) c := by
  calc
    ofStage (Base := Base) (Const := Const)
        (HenkinConstStage.lift (Base := Base) (Const := Const) hmn c) =
      ofStage (Base := Base) (Const := Const)
        (cast (congrArg (fun t => HenkinConstStage Base Const t τ)
            (Nat.add_sub_of_le hmn))
          (HenkinConstStage.liftOffset (Base := Base) (Const := Const) (n - m) c)) := by
            rw [HenkinConstStage.lift_eq_cast_liftOffset
              (Base := Base) (Const := Const) hmn c]
    _ =
      ofStage (Base := Base) (Const := Const)
        (HenkinConstStage.liftOffset (Base := Base) (Const := Const) (n - m) c) := by
          simpa using
            (ofStage_cast (Base := Base) (Const := Const)
              (h := Nat.add_sub_of_le hmn)
              (c := HenkinConstStage.liftOffset
                (Base := Base) (Const := Const) (n - m) c))
    _ = ofStage (Base := Base) (Const := Const) c := by
          simpa using
            (ofStage_liftOffset (Base := Base) (Const := Const)
              (k := n - m) (c := c))

/-- Directly lift an original-signature term into the cumulative Henkin signature. -/
abbrev liftBaseTerm {Γ : Ctx Base} {τ : Ty Base} :
    Term Const Γ τ → Term (HenkinConstInfinity Base Const) Γ τ :=
  mapConst HenkinConstInfinity.base

/-- Directly lift an original-signature formula into the cumulative Henkin signature. -/
abbrev liftBaseFormula {Γ : Ctx Base} :
    Formula Const Γ → Formula (HenkinConstInfinity Base Const) Γ :=
  mapConst HenkinConstInfinity.base

/-- Directly lift an original-signature closed term into the cumulative Henkin signature. -/
abbrev liftBaseClosedTerm {τ : Ty Base} :
    ClosedTerm Const τ → ClosedTerm (HenkinConstInfinity Base Const) τ :=
  mapConst HenkinConstInfinity.base

/-- Directly lift an original-signature closed formula into the cumulative Henkin signature. -/
abbrev liftBaseClosedFormula :
    ClosedFormula Const → ClosedFormula (HenkinConstInfinity Base Const) :=
  mapConst HenkinConstInfinity.base

/-- Lift a finite-stage term into the canonical cumulative Henkin signature. -/
abbrev liftTerm {n : Nat} {Γ : Ctx Base} {τ : Ty Base} :
    Term (HenkinConstStage Base Const n) Γ τ →
      Term (HenkinConstInfinity Base Const) Γ τ :=
  mapConst (ofStage (Base := Base) (Const := Const))

/-- Lift a finite-stage formula into the canonical cumulative Henkin signature. -/
abbrev liftFormula {n : Nat} {Γ : Ctx Base} :
    Formula (HenkinConstStage Base Const n) Γ →
      Formula (HenkinConstInfinity Base Const) Γ :=
  mapConst (ofStage (Base := Base) (Const := Const))

/-- Lift a finite-stage closed formula into the canonical cumulative Henkin signature. -/
abbrev liftClosedFormula {n : Nat} :
    ClosedFormula (HenkinConstStage Base Const n) →
      ClosedFormula (HenkinConstInfinity Base Const) :=
  mapConst (ofStage (Base := Base) (Const := Const))

@[simp] theorem liftBaseTerm_eq_liftTerm_zero
    {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) :
    liftBaseTerm (Base := Base) (Const := Const) t =
      liftTerm (Base := Base) (Const := Const)
        (mapConst (HenkinConstStage.ofBase (Base := Base) (Const := Const)) t) := by
  induction t with
  | var v => rfl
  | const c => rfl
  | app g t hg ht => simp only [liftBaseTerm, liftTerm, mapConst, hg, ht]
  | lam t ih => simp only [liftBaseTerm, liftTerm, mapConst, ih]
  | top => rfl
  | bot => rfl
  | and φ ψ hφ hψ => simp only [liftBaseTerm, liftTerm, mapConst, hφ, hψ]
  | or φ ψ hφ hψ => simp only [liftBaseTerm, liftTerm, mapConst, hφ, hψ]
  | imp φ ψ hφ hψ => simp only [liftBaseTerm, liftTerm, mapConst, hφ, hψ]
  | not φ hφ => simp only [liftBaseTerm, liftTerm, mapConst, hφ]
  | eq t u ht hu => simp only [liftBaseTerm, liftTerm, mapConst, ht, hu]
  | all φ hφ => simp only [liftBaseTerm, liftTerm, mapConst, hφ]
  | ex φ hφ => simp only [liftBaseTerm, liftTerm, mapConst, hφ]

@[simp] theorem liftBaseFormula_eq_liftFormula_zero
    {Γ : Ctx Base} (φ : Formula Const Γ) :
    liftBaseFormula (Base := Base) (Const := Const) φ =
      liftFormula (Base := Base) (Const := Const)
        (mapConst (HenkinConstStage.ofBase (Base := Base) (Const := Const)) φ) :=
  liftBaseTerm_eq_liftTerm_zero (Base := Base) (Const := Const) φ

@[simp] theorem liftBaseClosedFormula_eq_liftClosedFormula_zero
    (φ : ClosedFormula Const) :
    liftBaseClosedFormula (Base := Base) (Const := Const) φ =
      liftClosedFormula (Base := Base) (Const := Const)
        (mapConst (HenkinConstStage.ofBase (Base := Base) (Const := Const)) φ) :=
  liftBaseFormula_eq_liftFormula_zero (Base := Base) (Const := Const) φ

/-- Raise a finite-stage term by `k` additional Henkinization stages. -/
abbrev stageBumpTerm (k : Nat) {n : Nat} {Γ : Ctx Base} {τ : Ty Base} :
    Term (HenkinConstStage Base Const n) Γ τ →
      Term (HenkinConstStage Base Const (n + k)) Γ τ :=
  mapConst (HenkinConstStage.liftOffset (Base := Base) (Const := Const) k)

/-- Raise a finite-stage formula by `k` additional Henkinization stages. -/
abbrev stageBumpFormula (k : Nat) {n : Nat} {Γ : Ctx Base} :
    Formula (HenkinConstStage Base Const n) Γ →
      Formula (HenkinConstStage Base Const (n + k)) Γ :=
  mapConst (HenkinConstStage.liftOffset (Base := Base) (Const := Const) k)

/-- Raise a finite-stage closed formula by `k` additional Henkinization stages. -/
abbrev stageBumpClosedFormula (k : Nat) {n : Nat} :
    ClosedFormula (HenkinConstStage Base Const n) →
      ClosedFormula (HenkinConstStage Base Const (n + k)) :=
  mapConst (HenkinConstStage.liftOffset (Base := Base) (Const := Const) k)

theorem liftTerm_stageBump (k : Nat) {n : Nat}
    {Γ : Ctx Base} {τ : Ty Base}
    (t : Term (HenkinConstStage Base Const n) Γ τ) :
    liftTerm (Base := Base) (Const := Const)
        (stageBumpTerm (Base := Base) (Const := Const) k t) =
      liftTerm (Base := Base) (Const := Const) t := by
  induction t with
  | var v => rfl
  | const c =>
      simp [stageBumpTerm, liftTerm, mapConst, ofStage_liftOffset]
  | app f t hf ht =>
      simp [stageBumpTerm, liftTerm, mapConst, hf, ht]
  | lam t ih =>
      simp [stageBumpTerm, liftTerm, mapConst, ih]
  | top => rfl
  | bot => rfl
  | and φ ψ hφ hψ =>
      simp [stageBumpTerm, liftTerm, mapConst, hφ, hψ]
  | or φ ψ hφ hψ =>
      simp [stageBumpTerm, liftTerm, mapConst, hφ, hψ]
  | imp φ ψ hφ hψ =>
      simp [stageBumpTerm, liftTerm, mapConst, hφ, hψ]
  | not φ hφ =>
      simp [stageBumpTerm, liftTerm, mapConst, hφ]
  | eq t u ht hu =>
      simp [stageBumpTerm, liftTerm, mapConst, ht, hu]
  | all φ hφ =>
      simp [stageBumpTerm, liftTerm, mapConst, hφ]
  | ex φ hφ =>
      simp [stageBumpTerm, liftTerm, mapConst, hφ]

@[simp] theorem liftTerm_stageLift
    {m n : Nat} (hmn : m ≤ n)
    {Γ : Ctx Base} {τ : Ty Base}
    (t : Term (HenkinConstStage Base Const m) Γ τ) :
    liftTerm (Base := Base) (Const := Const)
        (HenkinConstStage.liftTerm (Base := Base) (Const := Const) hmn t) =
      liftTerm (Base := Base) (Const := Const) t := by
  induction t with
  | var v => rfl
  | const c =>
      simp [HenkinConstStage.liftTerm, liftTerm, mapConst, ofStage_lift, hmn]
  | app g t hg ht =>
      simp [HenkinConstStage.liftTerm, liftTerm, mapConst, hg, ht]
  | lam t ih =>
      simp [HenkinConstStage.liftTerm, liftTerm, mapConst, ih]
  | top => rfl
  | bot => rfl
  | and φ ψ hφ hψ =>
      simp [HenkinConstStage.liftTerm, liftTerm, mapConst, hφ, hψ]
  | or φ ψ hφ hψ =>
      simp [HenkinConstStage.liftTerm, liftTerm, mapConst, hφ, hψ]
  | imp φ ψ hφ hψ =>
      simp [HenkinConstStage.liftTerm, liftTerm, mapConst, hφ, hψ]
  | not φ hφ =>
      simp [HenkinConstStage.liftTerm, liftTerm, mapConst, hφ]
  | eq t u ht hu =>
      simp [HenkinConstStage.liftTerm, liftTerm, mapConst, ht, hu]
  | all φ hφ =>
      simp [HenkinConstStage.liftTerm, liftTerm, mapConst, hφ]
  | ex φ hφ =>
      simp [HenkinConstStage.liftTerm, liftTerm, mapConst, hφ]

@[simp] theorem liftFormula_stageLift
    {m n : Nat} (hmn : m ≤ n)
    {Γ : Ctx Base}
    (φ : Formula (HenkinConstStage Base Const m) Γ) :
    liftFormula (Base := Base) (Const := Const)
        (HenkinConstStage.liftFormula (Base := Base) (Const := Const) hmn φ) =
      liftFormula (Base := Base) (Const := Const) φ :=
  liftTerm_stageLift (Base := Base) (Const := Const) hmn φ

@[simp] theorem liftClosedFormula_stageLift
    {m n : Nat} (hmn : m ≤ n)
    (φ : ClosedFormula (HenkinConstStage Base Const m)) :
    liftClosedFormula (Base := Base) (Const := Const)
        (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) hmn φ) =
      liftClosedFormula (Base := Base) (Const := Const) φ :=
  liftTerm_stageLift (Base := Base) (Const := Const) hmn φ

@[simp] theorem liftBaseFormula_sound
    (n : Nat) {Γ : Ctx Base}
    (φ : Formula Const Γ) :
    liftFormula (Base := Base) (Const := Const)
        (HenkinConstStage.liftBaseFormula (Base := Base) (Const := Const) n φ) =
      liftBaseFormula (Base := Base) (Const := Const) φ := by
  rw [HenkinConstStage.liftBaseFormula, liftFormula, liftBaseFormula,
    Mettapedia.Logic.HOL.mapConst_comp]
  apply Mettapedia.Logic.HOL.mapConst_ext
  intro τ c
  exact
    (ofStage_lift (Base := Base) (Const := Const)
      (Nat.zero_le n)
      (HenkinConstStage.ofBase (Base := Base) (Const := Const) c)).trans
      (ofStage_ofBase (Base := Base) (Const := Const) c)

@[simp] theorem liftBaseClosedFormula_sound
    (n : Nat)
    (φ : ClosedFormula Const) :
    liftClosedFormula (Base := Base) (Const := Const)
        (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n φ) =
      liftBaseClosedFormula (Base := Base) (Const := Const) φ :=
  liftBaseFormula_sound (Base := Base) (Const := Const) n φ

/-- Transport a finite-stage term across an equality of stage indices. -/
def castStageTerm {n m : Nat} (h : n = m) {Γ : Ctx Base} {τ : Ty Base} :
    Term (HenkinConstStage Base Const n) Γ τ →
      Term (HenkinConstStage Base Const m) Γ τ := by
  cases h
  intro t
  exact t

theorem liftTerm_castStageTerm {n m : Nat} (h : n = m)
    {Γ : Ctx Base} {τ : Ty Base}
    (t : Term (HenkinConstStage Base Const n) Γ τ) :
    liftTerm (Base := Base) (Const := Const)
        (castStageTerm (Base := Base) (Const := Const) h t) =
      liftTerm (Base := Base) (Const := Const) t := by
  cases h
  rfl

/-- A term over the cumulative signature together with a finite stage presentation. -/
structure StagedTerm {Γ : Ctx Base} {τ : Ty Base}
    (t : Term (HenkinConstInfinity Base Const) Γ τ) where
  stage : Nat
  term : Term (HenkinConstStage Base Const stage) Γ τ
  sound : liftTerm (Base := Base) (Const := Const) term = t

/-- Recover a finite Henkin stage supporting a cumulative-signature term. -/
def stageTerm :
    {Γ : Ctx Base} → {τ : Ty Base} →
      (t : Term (HenkinConstInfinity Base Const) Γ τ) →
        StagedTerm (Base := Base) (Const := Const) t
  | _, _, .var v =>
      ⟨0, .var v, rfl⟩
  | _, _, .const (.base c) =>
      ⟨0, .const (HenkinConstStage.ofBase (Base := Base) c), rfl⟩
  | _, _, .const (.exWitness (n := n) φ) =>
      ⟨n + 1, .const (.exWitness φ), rfl⟩
  | _, _, .const (.allCounterexample (n := n) φ) =>
      ⟨n + 1, .const (.allCounterexample φ), rfl⟩
  | _, _, .app f t =>
      match stageTerm f, stageTerm t with
      | ⟨nf, tf, hf⟩, ⟨nt, tt, ht⟩ =>
          let tt' :=
            castStageTerm (Base := Base) (Const := Const)
              (Nat.add_comm nt nf)
              (stageBumpTerm (Base := Base) (Const := Const) nf tt)
          have hf' :
              liftTerm (Base := Base) (Const := Const)
                  (stageBumpTerm (Base := Base) (Const := Const) nt tf) = f := by
            simpa [hf] using
              (liftTerm_stageBump (Base := Base) (Const := Const) nt tf)
          have ht₀ :
              liftTerm (Base := Base) (Const := Const)
                  (stageBumpTerm (Base := Base) (Const := Const) nf tt) = t := by
            simpa [ht] using
              (liftTerm_stageBump (Base := Base) (Const := Const) nf tt)
          have ht' :
              liftTerm (Base := Base) (Const := Const) tt' = t := by
            unfold tt'
            rw [liftTerm_castStageTerm]
            exact ht₀
          ⟨nf + nt,
            .app
              (stageBumpTerm (Base := Base) (Const := Const) nt tf)
              tt',
            by
              cases hf'
              cases ht'
              rfl⟩
  | _, _, .lam t =>
      match stageTerm t with
      | ⟨n, t', ht⟩ =>
          ⟨n, .lam t', by
            cases ht
            rfl⟩
  | _, _, .top =>
      ⟨0, .top, rfl⟩
  | _, _, .bot =>
      ⟨0, .bot, rfl⟩
  | _, _, .and φ ψ =>
      match stageTerm φ, stageTerm ψ with
      | ⟨nφ, tφ, hφ⟩, ⟨nψ, tψ, hψ⟩ =>
          let tψ' :=
            castStageTerm (Base := Base) (Const := Const)
              (Nat.add_comm nψ nφ)
              (stageBumpFormula (Base := Base) (Const := Const) nφ tψ)
          have hφ' :
              liftTerm (Base := Base) (Const := Const)
                  (stageBumpFormula (Base := Base) (Const := Const) nψ tφ) = φ := by
            simpa [hφ] using
              (liftTerm_stageBump (Base := Base) (Const := Const) nψ tφ)
          have hψ₀ :
              liftTerm (Base := Base) (Const := Const)
                  (stageBumpFormula (Base := Base) (Const := Const) nφ tψ) = ψ := by
            simpa [hψ] using
              (liftTerm_stageBump (Base := Base) (Const := Const) nφ tψ)
          have hψ' :
              liftTerm (Base := Base) (Const := Const) tψ' = ψ := by
            unfold tψ'
            rw [liftTerm_castStageTerm]
            exact hψ₀
          ⟨nφ + nψ,
            .and
              (stageBumpFormula (Base := Base) (Const := Const) nψ tφ)
              tψ',
            by
              cases hφ'
              cases hψ'
              rfl⟩
  | _, _, .or φ ψ =>
      match stageTerm φ, stageTerm ψ with
      | ⟨nφ, tφ, hφ⟩, ⟨nψ, tψ, hψ⟩ =>
          let tψ' :=
            castStageTerm (Base := Base) (Const := Const)
              (Nat.add_comm nψ nφ)
              (stageBumpFormula (Base := Base) (Const := Const) nφ tψ)
          have hφ' :
              liftTerm (Base := Base) (Const := Const)
                  (stageBumpFormula (Base := Base) (Const := Const) nψ tφ) = φ := by
            simpa [hφ] using
              (liftTerm_stageBump (Base := Base) (Const := Const) nψ tφ)
          have hψ₀ :
              liftTerm (Base := Base) (Const := Const)
                  (stageBumpFormula (Base := Base) (Const := Const) nφ tψ) = ψ := by
            simpa [hψ] using
              (liftTerm_stageBump (Base := Base) (Const := Const) nφ tψ)
          have hψ' :
              liftTerm (Base := Base) (Const := Const) tψ' = ψ := by
            unfold tψ'
            rw [liftTerm_castStageTerm]
            exact hψ₀
          ⟨nφ + nψ,
            .or
              (stageBumpFormula (Base := Base) (Const := Const) nψ tφ)
              tψ',
            by
              cases hφ'
              cases hψ'
              rfl⟩
  | _, _, .imp φ ψ =>
      match stageTerm φ, stageTerm ψ with
      | ⟨nφ, tφ, hφ⟩, ⟨nψ, tψ, hψ⟩ =>
          let tψ' :=
            castStageTerm (Base := Base) (Const := Const)
              (Nat.add_comm nψ nφ)
              (stageBumpFormula (Base := Base) (Const := Const) nφ tψ)
          have hφ' :
              liftTerm (Base := Base) (Const := Const)
                  (stageBumpFormula (Base := Base) (Const := Const) nψ tφ) = φ := by
            simpa [hφ] using
              (liftTerm_stageBump (Base := Base) (Const := Const) nψ tφ)
          have hψ₀ :
              liftTerm (Base := Base) (Const := Const)
                  (stageBumpFormula (Base := Base) (Const := Const) nφ tψ) = ψ := by
            simpa [hψ] using
              (liftTerm_stageBump (Base := Base) (Const := Const) nφ tψ)
          have hψ' :
              liftTerm (Base := Base) (Const := Const) tψ' = ψ := by
            unfold tψ'
            rw [liftTerm_castStageTerm]
            exact hψ₀
          ⟨nφ + nψ,
            .imp
              (stageBumpFormula (Base := Base) (Const := Const) nψ tφ)
              tψ',
            by
              cases hφ'
              cases hψ'
              rfl⟩
  | _, _, .not φ =>
      match stageTerm φ with
      | ⟨nφ, tφ, hφ⟩ =>
          ⟨nφ, .not tφ, by
            cases hφ
            rfl⟩
  | _, _, .eq t u =>
      match stageTerm t, stageTerm u with
      | ⟨nt, tt, ht⟩, ⟨nu, tu, hu⟩ =>
          let tu' :=
            castStageTerm (Base := Base) (Const := Const)
              (Nat.add_comm nu nt)
              (stageBumpTerm (Base := Base) (Const := Const) nt tu)
          have ht' :
              liftTerm (Base := Base) (Const := Const)
                  (stageBumpTerm (Base := Base) (Const := Const) nu tt) = t := by
            simpa [ht] using
              (liftTerm_stageBump (Base := Base) (Const := Const) nu tt)
          have hu₀ :
              liftTerm (Base := Base) (Const := Const)
                  (stageBumpTerm (Base := Base) (Const := Const) nt tu) = u := by
            simpa [hu] using
              (liftTerm_stageBump (Base := Base) (Const := Const) nt tu)
          have hu' :
              liftTerm (Base := Base) (Const := Const) tu' = u := by
            unfold tu'
            rw [liftTerm_castStageTerm]
            exact hu₀
          ⟨nt + nu,
            .eq
              (stageBumpTerm (Base := Base) (Const := Const) nu tt)
              tu',
            by
              cases ht'
              cases hu'
              rfl⟩
  | _, _, .all φ =>
      match stageTerm φ with
      | ⟨nφ, tφ, hφ⟩ =>
          ⟨nφ, .all tφ, by
            cases hφ
            rfl⟩
  | _, _, .ex φ =>
      match stageTerm φ with
      | ⟨nφ, tφ, hφ⟩ =>
          ⟨nφ, .ex tφ, by
            cases hφ
            rfl⟩

theorem exists_stage_term {Γ : Ctx Base} {τ : Ty Base}
    (t : Term (HenkinConstInfinity Base Const) Γ τ) :
    ∃ n, ∃ t' : Term (HenkinConstStage Base Const n) Γ τ,
      liftTerm (Base := Base) (Const := Const) t' = t := by
  let st := stageTerm (Base := Base) (Const := Const) t
  exact ⟨st.stage, st.term, st.sound⟩

theorem exists_stage_formula {Γ : Ctx Base}
    (φ : Formula (HenkinConstInfinity Base Const) Γ) :
    ∃ n, ∃ φ' : Formula (HenkinConstStage Base Const n) Γ,
      liftFormula (Base := Base) (Const := Const) φ' = φ :=
  exists_stage_term (Base := Base) (Const := Const) φ

/-- A finite-stage presentation of a cumulative-signature formula list. -/
structure StagedFormulaList {Γ : Ctx Base}
    (Δ : List (Formula (HenkinConstInfinity Base Const) Γ)) where
  stage : Nat
  formulas : List (Formula (HenkinConstStage Base Const stage) Γ)
  sound : formulas.map (liftFormula (Base := Base) (Const := Const)) = Δ

/-- Canonically stage a cumulative-signature formula list. -/
def stageFormulaList :
    {Γ : Ctx Base} →
      (Δ : List (Formula (HenkinConstInfinity Base Const) Γ)) →
        StagedFormulaList (Base := Base) (Const := Const) Δ
  | Γ, [] =>
      ⟨0, [], rfl⟩
  | Γ, φ :: Δ =>
      let sφ : StagedTerm (Base := Base) (Const := Const) φ :=
        stageTerm (Base := Base) (Const := Const) φ
      let sΔ : StagedFormulaList (Base := Base) (Const := Const) Δ :=
        stageFormulaList Δ
      let φ'' : Formula (HenkinConstStage Base Const (sφ.stage + sΔ.stage)) Γ :=
        stageBumpFormula (Base := Base) (Const := Const) sΔ.stage sφ.term
      let Δ'' : List (Formula (HenkinConstStage Base Const (sφ.stage + sΔ.stage)) Γ) :=
        sΔ.formulas.map (fun ψ =>
          castStageTerm (Base := Base) (Const := Const)
            (Nat.add_comm sΔ.stage sφ.stage)
            (stageBumpFormula (Base := Base) (Const := Const) sφ.stage ψ))
      have hφ'' :
          liftFormula (Base := Base) (Const := Const) φ'' = φ := by
        simpa [φ'', sφ.sound] using
          (liftTerm_stageBump (Base := Base) (Const := Const) sΔ.stage sφ.term)
      have hΔ'' :
          Δ''.map (liftFormula (Base := Base) (Const := Const)) = Δ := by
        have hmaplift :
            ∀ Λ :
              List
                (Formula (HenkinConstStage Base Const sΔ.stage) Γ),
              Λ.map (fun ψ =>
                liftFormula (Base := Base) (Const := Const)
                  (castStageTerm (Base := Base) (Const := Const)
                    (Nat.add_comm sΔ.stage sφ.stage)
                    (stageBumpFormula (Base := Base) (Const := Const)
                      sφ.stage ψ))) =
                Λ.map (liftFormula (Base := Base) (Const := Const)) := by
          intro Λ
          induction Λ with
          | nil => rfl
          | cons ψ Λ ih =>
              simp only [List.map]
              rw [List.cons.injEq]
              refine ⟨?_, ih⟩
              calc
                liftFormula (Base := Base) (Const := Const)
                    (castStageTerm (Base := Base) (Const := Const)
                      (Nat.add_comm sΔ.stage sφ.stage)
                      (stageBumpFormula (Base := Base) (Const := Const)
                        sφ.stage ψ))
                    =
                  liftFormula (Base := Base) (Const := Const)
                    (stageBumpFormula (Base := Base) (Const := Const)
                      sφ.stage ψ) := by
                        simpa using
                          (liftTerm_castStageTerm (Base := Base) (Const := Const)
                            (Nat.add_comm sΔ.stage sφ.stage)
                            (stageBumpFormula (Base := Base) (Const := Const)
                              sφ.stage ψ))
                _ =
                  liftFormula (Base := Base) (Const := Const) ψ := by
                    simpa using
                      (liftTerm_stageBump (Base := Base) (Const := Const)
                        sφ.stage ψ)
        calc
          Δ''.map (liftFormula (Base := Base) (Const := Const))
              = sΔ.formulas.map (fun ψ =>
                  liftFormula (Base := Base) (Const := Const)
                    (castStageTerm (Base := Base) (Const := Const)
                      (Nat.add_comm sΔ.stage sφ.stage)
                      (stageBumpFormula (Base := Base) (Const := Const)
                        sφ.stage ψ))) := by
                  simp [Δ'']
          _ = sΔ.formulas.map (liftFormula (Base := Base) (Const := Const)) :=
                hmaplift sΔ.formulas
          _ = Δ := sΔ.sound
      ⟨sφ.stage + sΔ.stage, φ'' :: Δ'', by
        simp [hφ'', hΔ'']⟩

theorem exists_stage_formulaList {Γ : Ctx Base}
    (Δ : List (Formula (HenkinConstInfinity Base Const) Γ)) :
    ∃ n, ∃ Δ' : List (Formula (HenkinConstStage Base Const n) Γ),
      Δ'.map (liftFormula (Base := Base) (Const := Const)) = Δ := by
  let sΔ := stageFormulaList (Base := Base) (Const := Const) Δ
  exact ⟨sΔ.stage, sΔ.formulas, sΔ.sound⟩

theorem exists_stage_closedFormula
    (φ : ClosedFormula (HenkinConstInfinity Base Const)) :
    ∃ n, ∃ φ' : ClosedFormula (HenkinConstStage Base Const n),
      liftClosedFormula (Base := Base) (Const := Const) φ' = φ :=
  exists_stage_formula (Base := Base) (Const := Const) φ

theorem exists_stage_closedTheory
    (Δ : List (ClosedFormula (HenkinConstInfinity Base Const))) :
    ∃ n, ∃ Δ' : List (ClosedFormula (HenkinConstStage Base Const n)),
      Δ'.map (liftClosedFormula (Base := Base) (Const := Const)) = Δ :=
  exists_stage_formulaList (Base := Base) (Const := Const) Δ

@[simp] theorem liftFormula_stageBump (k : Nat) {n : Nat}
    {Γ : Ctx Base}
    (φ : Formula (HenkinConstStage Base Const n) Γ) :
    liftFormula (Base := Base) (Const := Const)
        (stageBumpFormula (Base := Base) (Const := Const) k φ) =
      liftFormula (Base := Base) (Const := Const) φ :=
  liftTerm_stageBump (Base := Base) (Const := Const) k φ

@[simp] theorem liftClosedFormula_stageBump (k : Nat) {n : Nat}
    (φ : ClosedFormula (HenkinConstStage Base Const n)) :
    liftClosedFormula (Base := Base) (Const := Const)
        (stageBumpClosedFormula (Base := Base) (Const := Const) k φ) =
      liftClosedFormula (Base := Base) (Const := Const) φ :=
  liftTerm_stageBump (Base := Base) (Const := Const) k φ

theorem liftTerm_injective {n : Nat}
    {Γ : Ctx Base} {τ : Ty Base} :
    Function.Injective
      (@liftTerm Base Const n Γ τ) := by
  intro t u h
  induction t with
  | var v =>
      cases u <;> cases h <;> rfl
  | const c =>
      cases u with
      | const d =>
          have hcd :
              ofStage (Base := Base) (Const := Const) c =
                ofStage (Base := Base) (Const := Const) d := by
            simpa [liftTerm, Mettapedia.Logic.HOL.mapConst] using h
          have hc : c = d :=
            ofStage_injective (Base := Base) (Const := Const) n hcd
          cases hc
          rfl
      | _ =>
          cases h
  | app g t hg ht =>
      cases u with
      | app g' t' =>
          injection h with hΓ hσ hτ hg' ht'
          cases hΓ
          cases hσ
          cases hτ
          have hgEq : g = g' := hg (by simpa [liftTerm] using hg')
          have htEq : t = t' := ht (by simpa [liftTerm] using ht')
          cases hgEq
          cases htEq
          rfl
      | _ =>
          cases h
  | lam t ih =>
      cases u with
      | lam u =>
          have htu :
              liftTerm (Base := Base) (Const := Const) t =
                liftTerm (Base := Base) (Const := Const) u := by
            simpa [liftTerm, Mettapedia.Logic.HOL.mapConst] using h
          have hEq : t = u := ih htu
          cases hEq
          rfl
      | _ =>
          cases h
  | top =>
      cases u <;> cases h <;> rfl
  | bot =>
      cases u <;> cases h <;> rfl
  | and φ ψ hφ hψ =>
      cases u with
      | and φ' ψ' =>
          have hpair :
              liftTerm (Base := Base) (Const := Const) φ =
                liftTerm (Base := Base) (Const := Const) φ' ∧
              liftTerm (Base := Base) (Const := Const) ψ =
                liftTerm (Base := Base) (Const := Const) ψ' := by
            simpa [liftTerm, Mettapedia.Logic.HOL.mapConst] using h
          rcases hpair with ⟨hφ', hψ'⟩
          have hφEq : φ = φ' := hφ hφ'
          have hψEq : ψ = ψ' := hψ hψ'
          cases hφEq
          cases hψEq
          rfl
      | _ =>
          cases h
  | or φ ψ hφ hψ =>
      cases u with
      | or φ' ψ' =>
          have hpair :
              liftTerm (Base := Base) (Const := Const) φ =
                liftTerm (Base := Base) (Const := Const) φ' ∧
              liftTerm (Base := Base) (Const := Const) ψ =
                liftTerm (Base := Base) (Const := Const) ψ' := by
            simpa [liftTerm, Mettapedia.Logic.HOL.mapConst] using h
          rcases hpair with ⟨hφ', hψ'⟩
          have hφEq : φ = φ' := hφ hφ'
          have hψEq : ψ = ψ' := hψ hψ'
          cases hφEq
          cases hψEq
          rfl
      | _ =>
          cases h
  | imp φ ψ hφ hψ =>
      cases u with
      | imp φ' ψ' =>
          have hpair :
              liftTerm (Base := Base) (Const := Const) φ =
                liftTerm (Base := Base) (Const := Const) φ' ∧
              liftTerm (Base := Base) (Const := Const) ψ =
                liftTerm (Base := Base) (Const := Const) ψ' := by
            simpa [liftTerm, Mettapedia.Logic.HOL.mapConst] using h
          rcases hpair with ⟨hφ', hψ'⟩
          have hφEq : φ = φ' := hφ hφ'
          have hψEq : ψ = ψ' := hψ hψ'
          cases hφEq
          cases hψEq
          rfl
      | _ =>
          cases h
  | not φ hφ =>
      cases u with
      | not ψ =>
          have hφ' :
              liftTerm (Base := Base) (Const := Const) φ =
                liftTerm (Base := Base) (Const := Const) ψ := by
            simpa [liftTerm, Mettapedia.Logic.HOL.mapConst] using h
          have hEq : φ = ψ := hφ hφ'
          cases hEq
          rfl
      | _ =>
          cases h
  | eq t u ht hu =>
      cases u with
      | eq t' u' =>
          injection h with hΓ hτ ht' hu'
          cases hΓ
          cases hτ
          have htEq : t = t' := ht (by simpa [liftTerm] using ht')
          have huEq : u = u' := hu (by simpa [liftTerm] using hu')
          cases htEq
          cases huEq
          rfl
      | _ =>
          cases h
  | all φ hφ =>
      cases u with
      | all ψ =>
          injection h with hΓ hσ hφ'
          cases hΓ
          cases hσ
          have hEq : φ = ψ := hφ (by simpa [liftTerm] using hφ')
          cases hEq
          rfl
      | _ =>
          cases h
  | ex φ hφ =>
      cases u with
      | ex ψ =>
          injection h with hΓ hσ hφ'
          cases hΓ
          cases hσ
          have hEq : φ = ψ := hφ (by simpa [liftTerm] using hφ')
          cases hEq
          rfl
      | _ =>
          cases h

theorem liftFormula_injective {n : Nat}
    {Γ : Ctx Base} :
    Function.Injective
      (@liftFormula Base Const n Γ) :=
  liftTerm_injective (Base := Base) (Const := Const) (n := n)

theorem liftClosedFormula_injective {n : Nat} :
    Function.Injective
      (@liftClosedFormula Base Const n) :=
  liftFormula_injective (Base := Base) (Const := Const) (n := n)

theorem liftFormulaList_injective {n : Nat}
    {Γ : Ctx Base} :
    Function.Injective
      (fun Δ : List (Formula (HenkinConstStage Base Const n) Γ) =>
        Δ.map (liftFormula (Base := Base) (Const := Const))) := by
  intro Δ Ξ h
  induction Δ generalizing Ξ with
  | nil =>
      cases Ξ with
      | nil => rfl
      | cons ψ Ξ => cases h
  | cons φ Δ ih =>
      cases Ξ with
      | nil => cases h
      | cons ψ Ξ =>
          injection h with hφ hΔ
          have hφEq : φ = ψ :=
            liftFormula_injective (Base := Base) (Const := Const) (n := n) hφ
          have hΔEq : Δ = Ξ := ih hΔ
          cases hφEq
          cases hΔEq
          rfl

/-- A finite-stage presentation of a cumulative-signature judgement. -/
structure StagedJudgement {Γ : Ctx Base}
    (Δ : List (Formula (HenkinConstInfinity Base Const) Γ))
    (φ : Formula (HenkinConstInfinity Base Const) Γ) where
  stage : Nat
  context : List (Formula (HenkinConstStage Base Const stage) Γ)
  formula : Formula (HenkinConstStage Base Const stage) Γ
  soundContext : context.map (liftFormula (Base := Base) (Const := Const)) = Δ
  soundFormula : liftFormula (Base := Base) (Const := Const) formula = φ

/-- Canonically stage a cumulative-signature judgement. -/
def stageJudgement :
    {Γ : Ctx Base} →
      (Δ : List (Formula (HenkinConstInfinity Base Const) Γ)) →
      (φ : Formula (HenkinConstInfinity Base Const) Γ) →
        StagedJudgement (Base := Base) (Const := Const) Δ φ
  | Γ, Δ, φ =>
      match stageFormulaList (φ :: Δ) with
      | ⟨n, [], hΘ⟩ =>
          False.elim (by simp at hΘ)
      | ⟨n, φ' :: Δ', hΘ⟩ =>
          have hsplit :
              liftFormula (Base := Base) (Const := Const) φ' = φ ∧
                Δ'.map (liftFormula (Base := Base) (Const := Const)) = Δ := by
            simpa using hΘ
          ⟨n, Δ', φ', hsplit.2, hsplit.1⟩

/--
A finite-stage presentation of a cumulative-signature derivation.

This is the generic derivation-carrying staging object the council wants as the
real induction engine: unlike the original-lift-specific wrappers downstream,
it works for arbitrary variable contexts and arbitrary cumulative judgements.
-/
structure SupportedStageDerivation {Γ : Ctx Base}
    (Δ : List (Formula (HenkinConstInfinity Base Const) Γ))
    (φ : Formula (HenkinConstInfinity Base Const) Γ) where
  stage : Nat
  context : List (Formula (HenkinConstStage Base Const stage) Γ)
  formula : Formula (HenkinConstStage Base Const stage) Γ
  soundContext : context.map (liftFormula (Base := Base) (Const := Const)) = Δ
  soundFormula : liftFormula (Base := Base) (Const := Const) formula = φ
  deriv : ExtDerivation (HenkinConstStage Base Const stage) context formula

def SupportedStageDerivation.toStagedJudgement
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ : Formula (HenkinConstInfinity Base Const) Γ}
    (S : SupportedStageDerivation (Base := Base) (Const := Const) Δ φ) :
    StagedJudgement (Base := Base) (Const := Const) Δ φ where
  stage := S.stage
  context := S.context
  formula := S.formula
  soundContext := S.soundContext
  soundFormula := S.soundFormula

def SupportedStageDerivation.castStage
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ : Formula (HenkinConstInfinity Base Const) Γ}
    (S : SupportedStageDerivation (Base := Base) (Const := Const) Δ φ)
    {n : Nat} (h : S.stage = n) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ φ := by
  cases h
  exact S

/--
Raise a supported staged derivation by `k` additional finite Henkin stages.

This is the generic stage-alignment operation needed later when multiple
subderivations have to be brought to a common finite stage.
-/
def SupportedStageDerivation.bump
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ : Formula (HenkinConstInfinity Base Const) Γ}
    (S : SupportedStageDerivation (Base := Base) (Const := Const) Δ φ)
    (k : Nat) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ φ := by
  refine
    { stage := S.stage + k
      context := S.context.map (stageBumpFormula (Base := Base) (Const := Const) k)
      formula := stageBumpFormula (Base := Base) (Const := Const) k S.formula
      soundContext := ?_
      soundFormula := ?_
      deriv := ?_ }
  · calc
      List.map (liftFormula (Base := Base) (Const := Const))
          (List.map (stageBumpFormula (Base := Base) (Const := Const) k) S.context) =
        List.map
          (fun ψ =>
            liftFormula (Base := Base) (Const := Const)
              (stageBumpFormula (Base := Base) (Const := Const) k ψ))
          S.context := by
            simp [List.map_map]
      _ =
        List.map
          (fun ψ => liftFormula (Base := Base) (Const := Const) ψ)
          S.context := by
            have hpoint :
                ∀ ψ : Formula (HenkinConstStage Base Const S.stage) Γ,
                  liftFormula (Base := Base) (Const := Const)
                      (stageBumpFormula (Base := Base) (Const := Const) k ψ) =
                    liftFormula (Base := Base) (Const := Const) ψ := by
              intro ψ
              exact liftFormula_stageBump (Base := Base) (Const := Const) k ψ
            induction S.context with
            | nil => rfl
            | cons ψ Γ ih =>
                simp only [List.map, hpoint ψ, ih]
      _ = Δ := S.soundContext
  · exact (liftFormula_stageBump (Base := Base) (Const := Const) k S.formula).trans S.soundFormula
  · simpa [stageBumpFormula, Mettapedia.Logic.HOL.mapConst] using
      (ExtDerivation.mapConst
        (Base := Base)
        (Const := HenkinConstStage Base Const S.stage)
        (Const' := HenkinConstStage Base Const (S.stage + k))
        (f := HenkinConstStage.liftOffset (Base := Base) (Const := Const) k)
        (Δ := S.context)
        (φ := S.formula)
        S.deriv)

theorem stagedFormulaList_preimage
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    (S : StagedFormulaList (Base := Base) (Const := Const) Δ)
    {φ : Formula (HenkinConstInfinity Base Const) Γ}
    (hφ : φ ∈ Δ) :
    ∃ φ' : Formula (HenkinConstStage Base Const S.stage) Γ,
      φ' ∈ S.formulas ∧
        liftFormula (Base := Base) (Const := Const) φ' = φ := by
  have hφ' : φ ∈ S.formulas.map (liftFormula (Base := Base) (Const := Const)) := by
    simpa [S.sound] using hφ
  rcases List.mem_map.mp hφ' with ⟨φ', hφ'mem, hEq⟩
  exact ⟨φ', hφ'mem, hEq⟩

theorem stageJudgement_context_preimage
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {ψ : Formula (HenkinConstInfinity Base Const) Γ}
    (hψ : ψ ∈ Δ) :
    ∃ ψ' :
        Formula
          (HenkinConstStage Base Const
            (stageJudgement (Base := Base) (Const := Const) Δ ψ).stage) Γ,
      ψ' ∈ (stageJudgement (Base := Base) (Const := Const) Δ ψ).context ∧
        liftFormula (Base := Base) (Const := Const) ψ' = ψ := by
  let S := stageJudgement (Base := Base) (Const := Const) Δ ψ
  exact stagedFormulaList_preimage
    (Base := Base) (Const := Const)
    ⟨S.stage, S.context, S.soundContext⟩ hψ

theorem supportedStageDerivation_hyp
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ : Formula (HenkinConstInfinity Base Const) Γ}
    (hφ : φ ∈ Δ) :
    Nonempty
      (SupportedStageDerivation (Base := Base) (Const := Const) Δ φ) := by
  let S := stageJudgement (Base := Base) (Const := Const) Δ φ
  rcases stageJudgement_context_preimage
      (Base := Base) (Const := Const) (Δ := Δ) (ψ := φ) hφ with
    ⟨φ', hφ', hlift⟩
  have hEq : φ' = S.formula :=
    liftFormula_injective (Base := Base) (Const := Const) (n := S.stage)
      (hlift.trans S.soundFormula.symm)
  exact ⟨
    { stage := S.stage
      context := S.context
      formula := S.formula
      soundContext := S.soundContext
      soundFormula := S.soundFormula
      deriv := by
        subst hEq
        exact ExtDerivation.hyp hφ' }⟩

theorem supportedStageDerivation_topI
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)} :
    Nonempty
      (SupportedStageDerivation (Base := Base) (Const := Const) Δ (.top : Formula _ Γ)) := by
  let S := stageJudgement (Base := Base) (Const := Const) Δ (.top : Formula _ Γ)
  have hEq : S.formula = (.top : Formula (HenkinConstStage Base Const S.stage) Γ) :=
    liftFormula_injective (Base := Base) (Const := Const) (n := S.stage)
      (S.soundFormula.trans rfl.symm)
  exact ⟨
    { stage := S.stage
      context := S.context
      formula := S.formula
      soundContext := S.soundContext
      soundFormula := S.soundFormula
      deriv := by
        simpa [hEq] using
          (ExtDerivation.topI :
            ExtDerivation (HenkinConstStage Base Const S.stage) S.context
              (.top : Formula (HenkinConstStage Base Const S.stage) Γ)) }⟩

structure AndLiftWitness
    {n : Nat} {Γ : Ctx Base}
    (θ : Formula (HenkinConstStage Base Const n) Γ)
    (φ ψ : Formula (HenkinConstInfinity Base Const) Γ) where
  left : Formula (HenkinConstStage Base Const n) Γ
  right : Formula (HenkinConstStage Base Const n) Γ
  shape : θ = .and left right
  soundLeft :
    HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) left = φ
  soundRight :
    HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) right = ψ

def liftFormula_eq_and_inv
    {n : Nat} {Γ : Ctx Base}
    {θ : Formula (HenkinConstStage Base Const n) Γ}
    {φ ψ : Formula (HenkinConstInfinity Base Const) Γ}
    (h : HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) θ = .and φ ψ) :
    AndLiftWitness (Base := Base) (Const := Const) θ φ ψ := by
  cases θ with
  | var v => cases h
  | const c => cases h
  | app f t => cases h
  | top => cases h
  | bot => cases h
  | and φ' ψ' =>
      simp [HenkinConstInfinity.liftFormula, liftFormula, Mettapedia.Logic.HOL.mapConst] at h
      exact ⟨φ', ψ', rfl, h.1, h.2⟩
  | or φ' ψ' => cases h
  | imp φ' ψ' => cases h
  | not φ' => cases h
  | eq t u => cases h
  | all φ' => cases h
  | ex φ' => cases h

def SupportedStageDerivation.andEL
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ ψ : Formula (HenkinConstInfinity Base Const) Γ}
    (S : SupportedStageDerivation (Base := Base) (Const := Const) Δ (.and φ ψ)) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ φ := by
  let shp :=
    liftFormula_eq_and_inv (Base := Base) (Const := Const) S.soundFormula
  let φ' := shp.left
  let ψ' := shp.right
  have hshape : S.formula = .and φ' ψ' := shp.shape
  have hφ :
      HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) φ' = φ :=
    shp.soundLeft
  refine
    { stage := S.stage
      context := S.context
      formula := φ'
      soundContext := S.soundContext
      soundFormula := hφ
      deriv := ?_ }
  have hderiv :
      ExtDerivation (HenkinConstStage Base Const S.stage) S.context (.and φ' ψ') := by
    simpa [hshape] using S.deriv
  exact ExtDerivation.andEL hderiv

def SupportedStageDerivation.andER
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ ψ : Formula (HenkinConstInfinity Base Const) Γ}
    (S : SupportedStageDerivation (Base := Base) (Const := Const) Δ (.and φ ψ)) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ ψ := by
  let shp :=
    liftFormula_eq_and_inv (Base := Base) (Const := Const) S.soundFormula
  let φ' := shp.left
  let ψ' := shp.right
  have hshape : S.formula = .and φ' ψ' := shp.shape
  have hψ :
      HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) ψ' = ψ :=
    shp.soundRight
  refine
    { stage := S.stage
      context := S.context
      formula := ψ'
      soundContext := S.soundContext
      soundFormula := hψ
      deriv := ?_ }
  have hderiv :
      ExtDerivation (HenkinConstStage Base Const S.stage) S.context (.and φ' ψ') := by
    simpa [hshape] using S.deriv
  exact ExtDerivation.andER hderiv

theorem exists_stage_judgement {Γ : Ctx Base}
    (Δ : List (Formula (HenkinConstInfinity Base Const) Γ))
    (φ : Formula (HenkinConstInfinity Base Const) Γ) :
    ∃ n, ∃ Δ' : List (Formula (HenkinConstStage Base Const n) Γ),
      ∃ φ' : Formula (HenkinConstStage Base Const n) Γ,
        Δ'.map (liftFormula (Base := Base) (Const := Const)) = Δ ∧
        liftFormula (Base := Base) (Const := Const) φ' = φ := by
  let sJ := stageJudgement (Base := Base) (Const := Const) Δ φ
  exact ⟨sJ.stage, sJ.context, sJ.formula, sJ.soundContext, sJ.soundFormula⟩

theorem exists_stage_closedJudgement
    (Δ : List (ClosedFormula (HenkinConstInfinity Base Const)))
    (φ : ClosedFormula (HenkinConstInfinity Base Const)) :
    ∃ n, ∃ Δ' : List (ClosedFormula (HenkinConstStage Base Const n)),
      ∃ φ' : ClosedFormula (HenkinConstStage Base Const n),
        Δ'.map (liftClosedFormula (Base := Base) (Const := Const)) = Δ ∧
        liftClosedFormula (Base := Base) (Const := Const) φ' = φ :=
  exists_stage_judgement (Base := Base) (Const := Const) Δ φ

theorem mem_liftFormula_preimage
    {Γ : Ctx Base} {n : Nat}
    {Δ : List (Formula (HenkinConstStage Base Const n) Γ)}
    {φ : Formula (HenkinConstInfinity Base Const) Γ}
    (hφ : φ ∈ Δ.map (liftFormula (Base := Base) (Const := Const))) :
    ∃ φ' : Formula (HenkinConstStage Base Const n) Γ,
      φ' ∈ Δ ∧ liftFormula (Base := Base) (Const := Const) φ' = φ := by
  rcases List.mem_map.mp hφ with ⟨φ', hφ', hEq⟩
  exact ⟨φ', hφ', hEq⟩

theorem stageLift_formulaProvable
    {Γ : Ctx Base} {m n : Nat} (h : m ≤ n)
    {Δ : List (Formula (HenkinConstStage Base Const m) Γ)}
    {φ : Formula (HenkinConstStage Base Const m) Γ}
    (d : ExtDerivation (HenkinConstStage Base Const m) Δ φ) :
    ExtDerivation (HenkinConstStage Base Const n)
      (Δ.map (HenkinConstStage.liftFormula (Base := Base) (Const := Const) h))
      (HenkinConstStage.liftFormula (Base := Base) (Const := Const) h φ) := by
  simpa [HenkinConstStage.liftFormula, Mettapedia.Logic.HOL.mapConst] using
    (ExtDerivation.mapConst
      (Base := Base)
      (Const := HenkinConstStage Base Const m)
      (Const' := HenkinConstStage Base Const n)
      (f := HenkinConstStage.lift (Base := Base) (Const := Const) h)
      (Δ := Δ)
      (φ := φ)
      d)

theorem stageLift_closedTheoryProvable
    {m n : Nat} (h : m ≤ n)
    {Δ : List (ClosedFormula (HenkinConstStage Base Const m))}
    {φ : ClosedFormula (HenkinConstStage Base Const m)}
    (d : ExtDerivation (HenkinConstStage Base Const m) Δ φ) :
    ExtDerivation (HenkinConstStage Base Const n)
      (Δ.map (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) h))
      (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) h φ) := by
  exact stageLift_formulaProvable (Base := Base) (Const := Const) h d

theorem stageLift_formulaProvable_comp
    {l m n : Nat} (hlm : l ≤ m) (hmn : m ≤ n)
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstStage Base Const l) Γ)}
    {φ : Formula (HenkinConstStage Base Const l) Γ}
    (d : ExtDerivation (HenkinConstStage Base Const l) Δ φ) :
    ExtDerivation (HenkinConstStage Base Const n)
      (Δ.map
        (HenkinConstStage.liftFormula (Base := Base) (Const := Const)
          (Nat.le_trans hlm hmn)))
      (HenkinConstStage.liftFormula (Base := Base) (Const := Const)
        (Nat.le_trans hlm hmn) φ) := by
  have d' :=
    stageLift_formulaProvable (Base := Base) (Const := Const) hmn
      (stageLift_formulaProvable (Base := Base) (Const := Const) hlm d)
  have hΔ :
      List.map (HenkinConstStage.liftFormula (Base := Base) (Const := Const) hmn)
          (List.map (HenkinConstStage.liftFormula (Base := Base) (Const := Const) hlm) Δ) =
        Δ.map
          (HenkinConstStage.liftFormula (Base := Base) (Const := Const)
            (Nat.le_trans hlm hmn)) := by
    induction Δ with
    | nil => rfl
    | cons ψ Δ ih =>
        simp [HenkinConstStage.liftFormula_comp
          (Base := Base) (Const := Const) hlm hmn]
  have hφ :
      HenkinConstStage.liftFormula (Base := Base) (Const := Const) hmn
          (HenkinConstStage.liftFormula (Base := Base) (Const := Const) hlm φ) =
        HenkinConstStage.liftFormula (Base := Base) (Const := Const)
          (Nat.le_trans hlm hmn) φ := by
    simpa using HenkinConstStage.liftFormula_comp
      (Base := Base) (Const := Const) hlm hmn φ
  exact hΔ ▸ hφ ▸ d'

theorem stageLift_closedTheoryProvable_comp
    {l m n : Nat} (hlm : l ≤ m) (hmn : m ≤ n)
    {Δ : List (ClosedFormula (HenkinConstStage Base Const l))}
    {φ : ClosedFormula (HenkinConstStage Base Const l)}
    (d : ExtDerivation (HenkinConstStage Base Const l) Δ φ) :
    ExtDerivation (HenkinConstStage Base Const n)
      (Δ.map
        (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
          (Nat.le_trans hlm hmn)))
      (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
        (Nat.le_trans hlm hmn) φ) := by
  have d' :=
    stageLift_closedTheoryProvable (Base := Base) (Const := Const) hmn
      (stageLift_closedTheoryProvable (Base := Base) (Const := Const) hlm d)
  have hΔ :
      List.map (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) hmn)
          (List.map (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) hlm) Δ) =
        Δ.map
          (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
            (Nat.le_trans hlm hmn)) := by
    induction Δ with
    | nil => rfl
    | cons ψ Δ ih =>
        simp [HenkinConstStage.liftClosedFormula_comp
          (Base := Base) (Const := Const) hlm hmn]
  have hφ :
      HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) hmn
          (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) hlm φ) =
        HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
          (Nat.le_trans hlm hmn) φ := by
    simpa using HenkinConstStage.liftClosedFormula_comp
      (Base := Base) (Const := Const) hlm hmn φ
  exact hΔ ▸ hφ ▸ d'

/-- Every cumulative-signature formula has a designated witness term one stage above some support stage. -/
theorem exists_stage_witness_term {σ : Ty Base}
    (φ : Formula (HenkinConstInfinity Base Const) [σ]) :
    ∃ n, ∃ φ' : Formula (HenkinConstStage Base Const n) [σ],
      liftFormula (Base := Base) (Const := Const) φ' = φ ∧
      ∃ t : ClosedTerm (HenkinConstInfinity Base Const) σ,
        t = liftTerm (Base := Base) (Const := Const)
          (HenkinConstStage.exWitnessTerm (Base := Base) (Const := Const) φ') := by
  rcases exists_stage_formula (Base := Base) (Const := Const) φ with ⟨n, φ', hφ⟩
  refine ⟨n, φ', hφ, ?_⟩
  refine ⟨liftTerm (Base := Base) (Const := Const)
      (HenkinConstStage.exWitnessTerm (Base := Base) (Const := Const) φ'), rfl⟩

/-- Every cumulative-signature formula has a designated counterexample term one stage above some support stage. -/
theorem exists_stage_counterexample_term {σ : Ty Base}
    (φ : Formula (HenkinConstInfinity Base Const) [σ]) :
    ∃ n, ∃ φ' : Formula (HenkinConstStage Base Const n) [σ],
      liftFormula (Base := Base) (Const := Const) φ' = φ ∧
      ∃ t : ClosedTerm (HenkinConstInfinity Base Const) σ,
        t = liftTerm (Base := Base) (Const := Const)
          (HenkinConstStage.allCounterexampleTerm (Base := Base) (Const := Const) φ') := by
  rcases exists_stage_formula (Base := Base) (Const := Const) φ with ⟨n, φ', hφ⟩
  refine ⟨n, φ', hφ, ?_⟩
  refine ⟨liftTerm (Base := Base) (Const := Const)
      (HenkinConstStage.allCounterexampleTerm (Base := Base) (Const := Const) φ'), rfl⟩

end HenkinConstInfinity

end Mettapedia.Logic.HOL
