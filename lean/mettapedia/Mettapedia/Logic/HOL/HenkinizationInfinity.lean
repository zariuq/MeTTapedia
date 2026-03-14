import Mettapedia.Logic.HOL.HenkinizationStages

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

theorem exists_stage_closedFormula
    (φ : ClosedFormula (HenkinConstInfinity Base Const)) :
    ∃ n, ∃ φ' : ClosedFormula (HenkinConstStage Base Const n),
      liftClosedFormula (Base := Base) (Const := Const) φ' = φ :=
  exists_stage_formula (Base := Base) (Const := Const) φ

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
