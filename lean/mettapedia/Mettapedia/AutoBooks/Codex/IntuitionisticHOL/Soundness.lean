import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Models

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v

/-- The propositional fragment of the native sequent calculus. -/
inductive PropositionalDerivable (Const : Ty Base → Type v) :
    {Γ : Ctx Base} → List (Formula Const Γ) → Formula Const Γ → Prop where
  | ax {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
      φ ∈ Δ → PropositionalDerivable Const Δ φ
  | topR {Γ : Ctx Base} {Δ : List (Formula Const Γ)} :
      PropositionalDerivable Const Δ .top
  | botL {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
      PropositionalDerivable Const (.bot :: Δ) φ
  | andL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ χ : Formula Const Γ} :
      PropositionalDerivable Const (φ :: ψ :: Δ) χ →
      PropositionalDerivable Const (.and φ ψ :: Δ) χ
  | andR {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      PropositionalDerivable Const Δ φ →
      PropositionalDerivable Const Δ ψ →
      PropositionalDerivable Const Δ (.and φ ψ)
  | orL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ χ : Formula Const Γ} :
      PropositionalDerivable Const (φ :: Δ) χ →
      PropositionalDerivable Const (ψ :: Δ) χ →
      PropositionalDerivable Const (.or φ ψ :: Δ) χ
  | orR₁ {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      PropositionalDerivable Const Δ φ →
      PropositionalDerivable Const Δ (.or φ ψ)
  | orR₂ {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      PropositionalDerivable Const Δ ψ →
      PropositionalDerivable Const Δ (.or φ ψ)
  | impL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ χ : Formula Const Γ} :
      PropositionalDerivable Const Δ φ →
      PropositionalDerivable Const (ψ :: Δ) χ →
      PropositionalDerivable Const (.imp φ ψ :: Δ) χ
  | impR {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      PropositionalDerivable Const (φ :: Δ) ψ →
      PropositionalDerivable Const Δ (.imp φ ψ)

namespace PropositionalDerivable

variable {Base : Type u} {Const : Ty Base → Type v}

/-- The propositional fragment embeds into the full native sequent calculus. -/
theorem toDerivable
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    PropositionalDerivable Const Δ φ → Derivable (Base := Base) (Const := Const) Δ φ := by
  intro d
  induction d with
  | ax h => exact .ax h
  | topR => exact .topR
  | botL => exact .botL
  | andL h ih => exact .andL ih
  | andR h₁ h₂ ih₁ ih₂ => exact .andR ih₁ ih₂
  | orL h₁ h₂ ih₁ ih₂ => exact .orL ih₁ ih₂
  | orR₁ h ih => exact .orR₁ ih
  | orR₂ h ih => exact .orR₂ ih
  | impL h₁ h₂ ih₁ ih₂ => exact .impL ih₁ ih₂
  | impR h ih => exact .impR ih

end PropositionalDerivable

namespace SemilocalModel

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Bounded semantic validity at a lower bound `u`. -/
def BoundedValidSequent (M : SemilocalModel Base Const)
    {Γ : Ctx Base} (u : M.Omega)
    (Δ : List (Formula Const Γ)) (φ : Formula Const Γ) : Prop :=
  ∀ ρ : Env M Γ,
    HasExtentLowerBound M u ρ →
    antecedentTruth M ρ Δ ⊓ u ≤ formulaTruth M ρ φ ⊓ u

/-- Semilocal semantic validity under global environments. -/
def ValidSequent (M : SemilocalModel Base Const)
    {Γ : Ctx Base} (Δ : List (Formula Const Γ)) (φ : Formula Const Γ) : Prop :=
  ∀ ρ : Env M Γ,
    IsGlobalEnv M ρ →
    antecedentTruth M ρ Δ ≤ formulaTruth M ρ φ

/-- Conditional semilocal soundness target for the native branch. -/
def SoundnessTarget (M : SemilocalModel Base Const)
    {Γ : Ctx Base} (Δ : List (Formula Const Γ)) (φ : Formula Const Γ) : Prop :=
  SupportsUniformRelativization M →
  Derivable (Base := Base) (Const := Const) Δ φ →
  ValidSequent M Δ φ

theorem validSequent_of_bounded_top (M : SemilocalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (h : BoundedValidSequent M ⊤ Δ φ) :
    ValidSequent M Δ φ := by
  intro ρ hρ
  have htop : HasExtentLowerBound M ⊤ ρ :=
    (isGlobalEnv_iff_hasExtentLowerBound_top M ρ).1 hρ
  simpa using h ρ htop

/-- Identity is sound at every lower bound. -/
theorem ax_bounded_valid (M : SemilocalModel Base Const)
    (u : M.Omega)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (h : φ ∈ Δ) :
    BoundedValidSequent M u Δ φ := by
  intro ρ hρ
  exact inf_le_inf_right _ (antecedentTruth_le_of_mem (M := M) (ρ := ρ) h)

/-- Top-right is sound at every lower bound. -/
theorem topR_bounded_valid (M : SemilocalModel Base Const)
    (u : M.Omega)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} :
    BoundedValidSequent M u Δ (.top : Formula Const Γ) := by
  intro ρ hρ
  simp [formulaTruth_top]

/-- Bottom-left is sound at every lower bound. -/
theorem botL_bounded_valid (M : SemilocalModel Base Const)
    (u : M.Omega)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    BoundedValidSequent M u (.bot :: Δ) φ := by
  intro ρ hρ
  simp [antecedentTruth, formulaTruth_bot]

/-- Conjunction-left is sound at every lower bound. -/
theorem andL_bounded_valid (M : SemilocalModel Base Const)
    (u : M.Omega)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ ψ χ : Formula Const Γ}
    (h : BoundedValidSequent M u (φ :: ψ :: Δ) χ) :
    BoundedValidSequent M u (.and φ ψ :: Δ) χ := by
  intro ρ hρ
  simpa [antecedentTruth, formulaTruth_and, inf_assoc, inf_left_comm, inf_comm] using h ρ hρ

/-- Conjunction-right is sound at every lower bound. -/
theorem andR_bounded_valid (M : SemilocalModel Base Const)
    (u : M.Omega)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ ψ : Formula Const Γ}
    (hφ : BoundedValidSequent M u Δ φ)
    (hψ : BoundedValidSequent M u Δ ψ) :
    BoundedValidSequent M u Δ (.and φ ψ) := by
  intro ρ hρ
  let γ := antecedentTruth M ρ Δ
  let p := formulaTruth M ρ φ
  let q := formulaTruth M ρ ψ
  have hp : γ ⊓ u ≤ p ⊓ u := hφ ρ hρ
  have hq : γ ⊓ u ≤ q ⊓ u := hψ ρ hρ
  have hp' : γ ⊓ u ≤ p := le_trans hp inf_le_left
  have hq' : γ ⊓ u ≤ q := le_trans hq inf_le_left
  have hu : γ ⊓ u ≤ u := inf_le_right
  have hfinal : γ ⊓ u ≤ (p ⊓ q) ⊓ u := by
    exact le_inf (le_inf hp' hq') hu
  simpa [γ, p, q, formulaTruth_and] using hfinal

/-- Left disjunction elimination is sound at every lower bound. -/
theorem orL_bounded_valid (M : SemilocalModel Base Const)
    (u : M.Omega)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ ψ χ : Formula Const Γ}
    (hφ : BoundedValidSequent M u (φ :: Δ) χ)
    (hψ : BoundedValidSequent M u (ψ :: Δ) χ) :
    BoundedValidSequent M u (.or φ ψ :: Δ) χ := by
  intro ρ hρ
  let γ := antecedentTruth M ρ Δ
  let p := formulaTruth M ρ φ
  let q := formulaTruth M ρ ψ
  let r := formulaTruth M ρ χ
  have hp : ((p ⊓ γ) ⊓ u) ≤ r ⊓ u := by
    simpa [γ, p, antecedentTruth, inf_assoc, inf_left_comm, inf_comm] using hφ ρ hρ
  have hq : ((q ⊓ γ) ⊓ u) ≤ r ⊓ u := by
    simpa [γ, q, antecedentTruth, inf_assoc, inf_left_comm, inf_comm] using hψ ρ hρ
  calc
    antecedentTruth M ρ (.or φ ψ :: Δ) ⊓ u
        = (((p ⊔ q) ⊓ γ) ⊓ u) := by
            simp [γ, p, q, antecedentTruth, formulaTruth_or]
    _ = ((p ⊓ γ) ⊓ u) ⊔ ((q ⊓ γ) ⊓ u) := by
          have hinner : γ ⊓ (p ⊔ q) = (γ ⊓ p) ⊔ (γ ⊓ q) := by
            simpa using (inf_sup_left γ p q)
          calc
            (((p ⊔ q) ⊓ γ) ⊓ u) = u ⊓ (γ ⊓ (p ⊔ q)) := by ac_rfl
            _ = u ⊓ ((γ ⊓ p) ⊔ (γ ⊓ q)) := by rw [hinner]
            _ = (u ⊓ (γ ⊓ p)) ⊔ (u ⊓ (γ ⊓ q)) := by
                  simpa using (inf_sup_left u (γ ⊓ p) (γ ⊓ q))
            _ = ((p ⊓ γ) ⊓ u) ⊔ ((q ⊓ γ) ⊓ u) := by ac_rfl
    _ ≤ r ⊓ u := sup_le hp hq

/-- First disjunction introduction is sound at every lower bound. -/
theorem orR₁_bounded_valid (M : SemilocalModel Base Const)
    (u : M.Omega)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ ψ : Formula Const Γ}
    (h : BoundedValidSequent M u Δ φ) :
    BoundedValidSequent M u Δ (.or φ ψ) := by
  intro ρ hρ
  calc
    antecedentTruth M ρ Δ ⊓ u ≤ formulaTruth M ρ φ ⊓ u := h ρ hρ
    _ ≤ formulaTruth M ρ (.or φ ψ) ⊓ u := by
          apply inf_le_inf_right
          simp [formulaTruth_or]

/-- Second disjunction introduction is sound at every lower bound. -/
theorem orR₂_bounded_valid (M : SemilocalModel Base Const)
    (u : M.Omega)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ ψ : Formula Const Γ}
    (h : BoundedValidSequent M u Δ ψ) :
    BoundedValidSequent M u Δ (.or φ ψ) := by
  intro ρ hρ
  calc
    antecedentTruth M ρ Δ ⊓ u ≤ formulaTruth M ρ ψ ⊓ u := h ρ hρ
    _ ≤ formulaTruth M ρ (.or φ ψ) ⊓ u := by
          apply inf_le_inf_right
          simp [formulaTruth_or]

/-- Implication-right is sound at every lower bound. -/
theorem impR_bounded_valid (M : SemilocalModel Base Const)
    (u : M.Omega)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ ψ : Formula Const Γ}
    (h : BoundedValidSequent M u (φ :: Δ) ψ) :
    BoundedValidSequent M u Δ (.imp φ ψ) := by
  intro ρ hρ
  let γ := antecedentTruth M ρ Δ
  let p := formulaTruth M ρ φ
  let q := formulaTruth M ρ ψ
  have hprem : ((p ⊓ γ) ⊓ u) ≤ q ⊓ u := by
    simpa [γ, p, q, antecedentTruth, inf_assoc, inf_left_comm, inf_comm] using h ρ hρ
  have hbody : (γ ⊓ u) ⊓ p ≤ q := by
    calc
      (γ ⊓ u) ⊓ p = (p ⊓ γ) ⊓ u := by ac_rfl
      _ ≤ q ⊓ u := hprem
      _ ≤ q := inf_le_left
  have himp : γ ⊓ u ≤ p ⇨ q := by
    rw [le_himp_iff]
    simpa [inf_assoc, inf_left_comm, inf_comm] using hbody
  have hu : γ ⊓ u ≤ u := inf_le_right
  have hfinal : γ ⊓ u ≤ (p ⇨ q) ⊓ u := le_inf himp hu
  simpa [γ, p, q, formulaTruth_imp] using hfinal

/-- Implication-left is sound at every lower bound. -/
theorem impL_bounded_valid (M : SemilocalModel Base Const)
    (u : M.Omega)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ ψ χ : Formula Const Γ}
    (hφ : BoundedValidSequent M u Δ φ)
    (hχ : BoundedValidSequent M u (ψ :: Δ) χ) :
    BoundedValidSequent M u (.imp φ ψ :: Δ) χ := by
  intro ρ hρ
  let γ := antecedentTruth M ρ Δ
  let p := formulaTruth M ρ φ
  let q := formulaTruth M ρ ψ
  let r := formulaTruth M ρ χ
  have hp : γ ⊓ u ≤ p ⊓ u := hφ ρ hρ
  have hγp : γ ⊓ u ≤ p := le_trans hp inf_le_left
  have hbody : ((q ⊓ γ) ⊓ u) ≤ r ⊓ u := by
    simpa [γ, q, r, antecedentTruth, inf_assoc, inf_left_comm, inf_comm] using hχ ρ hρ
  have hq : (p ⇨ q) ⊓ (γ ⊓ u) ≤ q := by
    calc
      (p ⇨ q) ⊓ (γ ⊓ u) ≤ (p ⇨ q) ⊓ p := inf_le_inf_left _ hγp
      _ = p ⊓ (p ⇨ q) := by rw [inf_comm]
      _ ≤ q := inf_himp_le
  have hinto : (p ⇨ q) ⊓ (γ ⊓ u) ≤ q ⊓ (γ ⊓ u) := le_inf hq inf_le_right
  calc
    antecedentTruth M ρ (.imp φ ψ :: Δ) ⊓ u
        = (p ⇨ q) ⊓ (γ ⊓ u) := by
            simp [γ, p, q, antecedentTruth, formulaTruth_imp, inf_assoc, inf_comm]
    _ ≤ q ⊓ (γ ⊓ u) := hinto
    _ = (q ⊓ γ) ⊓ u := by ac_rfl
    _ ≤ r ⊓ u := hbody

/-- Universal-left is sound at every lower bound. -/
theorem allL_bounded_valid (M : SemilocalModel Base Const)
    (u : M.Omega)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {χ : Formula Const Γ}
    (t : Term Const Γ σ)
    (h : BoundedValidSequent M u
      (instantiate (Base := Base) (Const := Const) t φ :: Δ) χ) :
    BoundedValidSequent M u (.all φ :: Δ) χ := by
  intro ρ hρ
  let e := eval M ρ t
  let γ := antecedentTruth M ρ Δ
  let ψ := formulaTruth M
    (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ e) φ
  have hinst :
      formulaTruth M ρ (instantiate (Base := Base) (Const := Const) t φ) = ψ := by
    exact formulaTruth_instantiate (M := M) t φ ρ
  have hallEq :
      formulaTruth M ρ (.all φ) =
        ⨅ x,
          M.extent x ⇨
            formulaTruth M
              (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x)
              φ := by
    exact formulaTruth_all (M := M) (ρ := ρ) (φ := φ)
  have heu : u ≤ M.extent e := hρ t
  have hall : formulaTruth M ρ (.all φ) ⊓ u ≤ ψ := by
    rw [hallEq]
    calc
      (⨅ x,
          M.extent x ⇨
            formulaTruth M
              (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x)
              φ) ⊓ u ≤
          (M.extent e ⇨ ψ) ⊓ u := by
            exact inf_le_inf_right _ (iInf_le _ e)
      _ ≤ ψ := by
            calc
              (M.extent e ⇨ ψ) ⊓ u ≤ (M.extent e ⇨ ψ) ⊓ M.extent e :=
                inf_le_inf_left _ heu
              _ = M.extent e ⊓ (M.extent e ⇨ ψ) := by rw [inf_comm]
              _ ≤ ψ := inf_himp_le
  have hprem : (ψ ⊓ γ) ⊓ u ≤ formulaTruth M ρ χ ⊓ u := by
    simpa [γ, ψ, hinst, antecedentTruth, inf_assoc, inf_left_comm, inf_comm] using h ρ hρ
  have hinto : ((formulaTruth M ρ (.all φ) ⊓ γ) ⊓ u) ≤ (ψ ⊓ γ) ⊓ u := by
    have hleft : ((formulaTruth M ρ (.all φ) ⊓ γ) ⊓ u) ≤ ψ ⊓ γ := by
      calc
        ((formulaTruth M ρ (.all φ) ⊓ γ) ⊓ u) =
            (formulaTruth M ρ (.all φ) ⊓ u) ⊓ γ := by
              ac_rfl
        _ ≤ ψ ⊓ γ := inf_le_inf_right _ hall
    have hu : ((formulaTruth M ρ (.all φ) ⊓ γ) ⊓ u) ≤ u := by
      exact inf_le_right
    exact le_inf hleft hu
  calc
    antecedentTruth M ρ (.all φ :: Δ) ⊓ u =
        ((formulaTruth M ρ (.all φ) ⊓ γ) ⊓ u) := by
          simp [γ, antecedentTruth, inf_assoc]
    _ ≤ (ψ ⊓ γ) ⊓ u := hinto
    _ ≤ formulaTruth M ρ χ ⊓ u := hprem

/-- Universal-right is sound at every lower bound. -/
theorem allR_bounded_valid (M : SemilocalModel Base Const)
    (hstep : SupportsLowerBoundExtension M)
    (u : M.Omega)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)}
    (h : ∀ v : M.Omega,
      BoundedValidSequent M v
        (weakenAntecedents (Base := Base) (Const := Const) σ Δ) φ) :
    BoundedValidSequent M u Δ (.all φ) := by
  intro ρ hρ
  let γ := antecedentTruth M ρ Δ
  have hallEq :
      formulaTruth M ρ (.all φ) =
        ⨅ x,
          M.extent x ⇨
            formulaTruth M
              (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x)
              φ := by
    exact formulaTruth_all (M := M) (ρ := ρ) (φ := φ)
  have hall : γ ⊓ u ≤ formulaTruth M ρ (.all φ) := by
    rw [hallEq]
    apply le_iInf
    intro x
    rw [le_himp_iff]
    have hρx :
        HasExtentLowerBound M (M.extent x ⊓ u)
          (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) :=
      hstep u ρ x hρ
    have hprem :
        γ ⊓ (M.extent x ⊓ u) ≤
          formulaTruth M
            (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x)
            φ ⊓
          (M.extent x ⊓ u) := by
      simpa [γ, inf_assoc, inf_left_comm, inf_comm] using
        h (M.extent x ⊓ u)
          (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) hρx
    calc
      (γ ⊓ u) ⊓ M.extent x = γ ⊓ (M.extent x ⊓ u) := by ac_rfl
      _ ≤
          formulaTruth M
            (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x)
            φ ⊓
          (M.extent x ⊓ u) := hprem
      _ ≤
          formulaTruth M
            (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x)
            φ := inf_le_left
  have hu : γ ⊓ u ≤ u := inf_le_right
  exact le_inf hall hu

/-- Existential-left is sound at every lower bound. -/
theorem exL_bounded_valid (M : SemilocalModel Base Const)
    (hstep : SupportsLowerBoundExtension M)
    (u : M.Omega)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {χ : Formula Const Γ}
    (h : ∀ v : M.Omega,
      BoundedValidSequent M v
        (φ :: weakenAntecedents (Base := Base) (Const := Const) σ Δ)
        (weaken (Base := Base) (Const := Const) (σ := σ) χ)) :
    BoundedValidSequent M u (.ex φ :: Δ) χ := by
  intro ρ hρ
  let γ := antecedentTruth M ρ Δ
  let r := formulaTruth M ρ χ
  have hbody :
      ∀ x : M.Carrier σ,
        (((M.extent x ⊓
          formulaTruth M
            (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x)
            φ) ⊓ γ) ⊓ u) ≤
          r ⊓ u := by
    intro x
    have hρx :
        HasExtentLowerBound M (M.extent x ⊓ u)
          (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) :=
      hstep u ρ x hρ
    have hprem :
        (formulaTruth M
            (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x)
            φ ⊓ γ) ⊓
          (M.extent x ⊓ u) ≤
        r ⊓ (M.extent x ⊓ u) := by
      simpa [γ, r, antecedentTruth, inf_assoc, inf_left_comm, inf_comm] using
        h (M.extent x ⊓ u)
          (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) hρx
    calc
      (((M.extent x ⊓
          formulaTruth M
            (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x)
            φ) ⊓ γ) ⊓ u) =
          (formulaTruth M
              (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x)
              φ ⊓ γ) ⊓
            (M.extent x ⊓ u) := by
              ac_rfl
      _ ≤ r ⊓ (M.extent x ⊓ u) := hprem
      _ ≤ r ⊓ u := by
            apply inf_le_inf_left
            exact inf_le_right
  calc
    antecedentTruth M ρ (.ex φ :: Δ) ⊓ u =
        (((⨆ x,
            M.extent x ⊓
              formulaTruth M
                (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x)
                φ) ⊓ γ) ⊓ u) := by
          simp [γ, antecedentTruth, formulaTruth_ex]
    _ = ((⨆ x,
            M.extent x ⊓
              formulaTruth M
                (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x)
                φ) ⊓ (γ ⊓ u)) := by
          ac_rfl
    _ = ⨆ x,
          (M.extent x ⊓
            formulaTruth M
              (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x)
              φ) ⊓ (γ ⊓ u) := by
            rw [iSup_inf_eq]
    _ = ⨆ x,
          (((M.extent x ⊓
            formulaTruth M
              (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x)
              φ) ⊓ γ) ⊓ u) := by
            apply iSup_congr
            intro x
            ac_rfl
    _ ≤ r ⊓ u := iSup_le hbody

/-- Existential-right is sound at every lower bound. -/
theorem exR_bounded_valid (M : SemilocalModel Base Const)
    (u : M.Omega)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)}
    (t : Term Const Γ σ)
    (h : BoundedValidSequent M u Δ
      (instantiate (Base := Base) (Const := Const) t φ)) :
    BoundedValidSequent M u Δ (.ex φ) := by
  intro ρ hρ
  let γ := antecedentTruth M ρ Δ
  let e := eval M ρ t
  let ψ := formulaTruth M
    (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ e) φ
  have hinst :
      formulaTruth M ρ (instantiate (Base := Base) (Const := Const) t φ) = ψ := by
    exact formulaTruth_instantiate (M := M) t φ ρ
  have heu : u ≤ M.extent e := hρ t
  have hprem : γ ⊓ u ≤ ψ ⊓ u := by
    simpa [γ, ψ, hinst] using h ρ hρ
  have hψ : γ ⊓ u ≤ ψ := le_trans hprem inf_le_left
  have he : γ ⊓ u ≤ M.extent e := le_trans inf_le_right heu
  have hex : γ ⊓ u ≤ formulaTruth M ρ (.ex φ) := by
    calc
      γ ⊓ u ≤ M.extent e ⊓ ψ := le_inf he hψ
      _ ≤ formulaTruth M ρ (.ex φ) := by
            rw [formulaTruth_ex]
            exact le_iSup
              (fun x =>
                M.extent x ⊓
                  formulaTruth M
                    (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x)
                    φ)
              e
  exact le_inf hex inf_le_right

/-- Beta-eta conversion is sound at every lower bound. -/
theorem lam_bounded_valid (M : SemilocalModel Base Const)
    (u : M.Omega)
    {Γ : Ctx Base}
    {Δ Δ' : List (Formula Const Γ)}
    {φ φ' : Formula Const Γ}
    (hΔ : AntecedentsBetaEtaEq (Base := Base) (Const := Const) Δ Δ')
    (hφ : BetaEtaEq (Base := Base) (Const := Const) φ φ')
    (h : BoundedValidSequent M u Δ' φ') :
    BoundedValidSequent M u Δ φ := by
  intro ρ hρ
  rw [show antecedentTruth M ρ Δ = antecedentTruth M ρ Δ' by
      exact antecedentTruth_betaEtaEq (M := M) (ρ := ρ) hΔ]
  rw [show formulaTruth M ρ φ = formulaTruth M ρ φ' by
      exact formulaTruth_betaEtaEq (M := M) (ρ := ρ) hφ]
  exact h ρ hρ

/-- Native archive-free soundness for the cut-free calculus at every lower bound. -/
theorem bounded_soundness (M : SemilocalModel Base Const)
    (hstep : SupportsLowerBoundExtension M)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    Derivable (Base := Base) (Const := Const) Δ φ →
    ∀ u : M.Omega, BoundedValidSequent M u Δ φ := by
  intro d
  induction d with
  | ax h =>
      intro u
      exact ax_bounded_valid M u h
  | topR =>
      intro u
      exact topR_bounded_valid M u
  | botL =>
      intro u
      exact botL_bounded_valid M u
  | andL h ih =>
      intro u
      exact andL_bounded_valid M u (ih u)
  | andR h₁ h₂ ih₁ ih₂ =>
      intro u
      exact andR_bounded_valid M u (ih₁ u) (ih₂ u)
  | orL h₁ h₂ ih₁ ih₂ =>
      intro u
      exact orL_bounded_valid M u (ih₁ u) (ih₂ u)
  | orR₁ h ih =>
      intro u
      exact orR₁_bounded_valid M u (ih u)
  | orR₂ h ih =>
      intro u
      exact orR₂_bounded_valid M u (ih u)
  | impL h₁ h₂ ih₁ ih₂ =>
      intro u
      exact impL_bounded_valid M u (ih₁ u) (ih₂ u)
  | impR h ih =>
      intro u
      exact impR_bounded_valid M u (ih u)
  | allL t h ih =>
      intro u
      exact allL_bounded_valid M u t (ih u)
  | allR h ih =>
      intro u
      exact allR_bounded_valid M hstep u ih
  | exL h ih =>
      intro u
      exact exL_bounded_valid M hstep u ih
  | exR t h ih =>
      intro u
      exact exR_bounded_valid M u t (ih u)
  | lam hΔ hφ hder ih =>
      intro u
      exact lam_bounded_valid M u hΔ hφ (ih u)

/-- Propositional derivations are sound at every lower bound in every semilocal model,
without any structural extension hypothesis. -/
theorem propositional_bounded_soundness (M : SemilocalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    PropositionalDerivable Const Δ φ →
    ∀ u : M.Omega, BoundedValidSequent M u Δ φ := by
  intro d
  induction d with
  | ax h =>
      intro u
      exact ax_bounded_valid M u h
  | topR =>
      intro u
      exact topR_bounded_valid M u
  | botL =>
      intro u
      exact botL_bounded_valid M u
  | andL h ih =>
      intro u
      exact andL_bounded_valid M u (ih u)
  | andR h₁ h₂ ih₁ ih₂ =>
      intro u
      exact andR_bounded_valid M u (ih₁ u) (ih₂ u)
  | orL h₁ h₂ ih₁ ih₂ =>
      intro u
      exact orL_bounded_valid M u (ih₁ u) (ih₂ u)
  | orR₁ h ih =>
      intro u
      exact orR₁_bounded_valid M u (ih u)
  | orR₂ h ih =>
      intro u
      exact orR₂_bounded_valid M u (ih u)
  | impL h₁ h₂ ih₁ ih₂ =>
      intro u
      exact impL_bounded_valid M u (ih₁ u) (ih₂ u)
  | impR h ih =>
      intro u
      exact impR_bounded_valid M u (ih u)

/-- Propositional derivations are sound in every semilocal model, with no
lower-bound extension assumption. -/
theorem propositional_soundness (M : SemilocalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    PropositionalDerivable Const Δ φ →
    ValidSequent M Δ φ := by
  intro h
  exact validSequent_of_bounded_top M ((propositional_bounded_soundness M h) ⊤)

/-- Conditional native archive-free soundness for semilocal models under the
lower-bound extension law. -/
theorem soundness_of_supportsLowerBoundExtension (M : SemilocalModel Base Const)
    (hstep : SupportsLowerBoundExtension M)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    Derivable (Base := Base) (Const := Const) Δ φ →
    ValidSequent M Δ φ := by
  intro h
  exact validSequent_of_bounded_top M ((bounded_soundness M hstep h) ⊤)

/-- Conditional native archive-free soundness for semilocal models in the
uniform relativization form suggested by Lemma 4.13. -/
theorem soundness (M : SemilocalModel Base Const)
    (hstep : SupportsUniformRelativization M)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    Derivable (Base := Base) (Const := Const) Δ φ →
    ValidSequent M Δ φ := by
  exact soundness_of_supportsLowerBoundExtension M
    (supportsLowerBoundExtension_of_supportsUniformRelativization M hstep)

/-- Conditional native archive-free soundness for semilocal models under the
stronger structural extent package. -/
theorem soundness_of_structuralExtent (M : SemilocalModel Base Const)
    (hstruct : StructuralExtent M)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    Derivable (Base := Base) (Const := Const) Δ φ →
    ValidSequent M Δ φ := by
  exact soundness M (SemilocalModel.StructuralExtent.supportsUniformRelativization hstruct)

/-- The semilocal soundness target is proved in the uniform relativization form. -/
theorem soundness_target (M : SemilocalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    SoundnessTarget M Δ φ := by
  intro hstep h
  exact soundness M hstep h

end SemilocalModel

namespace GlobalModel

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Semantic validity of a sequent in the global-model specialization. -/
def ValidSequent (M : GlobalModel Base Const)
    {Γ : Ctx Base} (Δ : List (Formula Const Γ)) (φ : Formula Const Γ) : Prop :=
  ∀ ρ : Env M Γ,
    antecedentTruth M ρ Δ ≤ formulaTruth M ρ φ

/-- The exact global-model target induced by the Theorem 4.14 rule set. -/
def SoundnessTarget (M : GlobalModel Base Const)
    {Γ : Ctx Base} (Δ : List (Formula Const Γ)) (φ : Formula Const Γ) : Prop :=
  Derivable (Base := Base) (Const := Const) Δ φ → ValidSequent M Δ φ

/-- Identity is already sound in the native global-model interface. -/
theorem ax_valid (M : GlobalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (h : φ ∈ Δ) :
    ValidSequent M Δ φ := by
  intro ρ
  exact SemilocalModel.antecedentTruth_le_of_mem (M := M.toSemilocalModel) (ρ := ρ) h

/-- Top-right is sound in every global model. -/
theorem topR_valid (M : GlobalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} :
    ValidSequent M Δ (.top : Formula Const Γ) := by
  intro ρ
  simp [GlobalModel.formulaTruth]

/-- Bottom-left is sound in every global model. -/
theorem botL_valid (M : GlobalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    ValidSequent M (.bot :: Δ) φ := by
  intro ρ
  calc
    antecedentTruth M ρ (.bot :: Δ) = (⊥ : M.Omega) := by
      simp [GlobalModel.antecedentTruth,
        SemilocalModel.antecedentTruth, SemilocalModel.formulaTruth, SemilocalModel.eval,
        M.toSemilocalModel.truth_bot]
    _ ≤ formulaTruth M ρ φ := bot_le

/-- Conjunction-left is sound in every global model. -/
theorem andL_valid (M : GlobalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ ψ χ : Formula Const Γ}
    (h : ValidSequent M (φ :: ψ :: Δ) χ) :
    ValidSequent M (.and φ ψ :: Δ) χ := by
  intro ρ
  let γ := antecedentTruth M ρ Δ
  have handAnte :
      antecedentTruth M ρ (.and φ ψ :: Δ) =
        formulaTruth M ρ φ ⊓ (formulaTruth M ρ ψ ⊓ γ) := by
    change formulaTruth M ρ (.and φ ψ) ⊓ antecedentTruth M ρ Δ =
      formulaTruth M ρ φ ⊓ (formulaTruth M ρ ψ ⊓ γ)
    rw [show formulaTruth M ρ (.and φ ψ) = formulaTruth M ρ φ ⊓ formulaTruth M ρ ψ by
      simp [GlobalModel.formulaTruth]]
    simp [γ, inf_assoc]
  calc
    antecedentTruth M ρ (.and φ ψ :: Δ) =
        formulaTruth M ρ φ ⊓ (formulaTruth M ρ ψ ⊓ γ) := handAnte
    _ = antecedentTruth M ρ (φ :: ψ :: Δ) := by
          simp [γ, GlobalModel.antecedentTruth,
            SemilocalModel.antecedentTruth]
    _ ≤ formulaTruth M ρ χ := h ρ

/-- Conjunction-right is sound in every global model. -/
theorem andR_valid (M : GlobalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ ψ : Formula Const Γ}
    (hφ : ValidSequent M Δ φ)
    (hψ : ValidSequent M Δ ψ) :
    ValidSequent M Δ (.and φ ψ) := by
  intro ρ
  simpa [GlobalModel.formulaTruth] using le_inf (hφ ρ) (hψ ρ)

/-- Left disjunction elimination is sound in every global model. -/
theorem orL_valid (M : GlobalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ ψ χ : Formula Const Γ}
    (hφ : ValidSequent M (φ :: Δ) χ)
    (hψ : ValidSequent M (ψ :: Δ) χ) :
    ValidSequent M (.or φ ψ :: Δ) χ := by
  intro ρ
  have hφρ : formulaTruth M ρ φ ⊓ antecedentTruth M ρ Δ ≤ formulaTruth M ρ χ := by
    simpa [GlobalModel.antecedentTruth, SemilocalModel.antecedentTruth] using hφ ρ
  have hψρ : formulaTruth M ρ ψ ⊓ antecedentTruth M ρ Δ ≤ formulaTruth M ρ χ := by
    simpa [GlobalModel.antecedentTruth, SemilocalModel.antecedentTruth] using hψ ρ
  have horAnte :
      antecedentTruth M ρ (.or φ ψ :: Δ) =
        (formulaTruth M ρ φ ⊔ formulaTruth M ρ ψ) ⊓ antecedentTruth M ρ Δ := by
    change formulaTruth M ρ (.or φ ψ) ⊓ antecedentTruth M ρ Δ =
      (formulaTruth M ρ φ ⊔ formulaTruth M ρ ψ) ⊓ antecedentTruth M ρ Δ
    rw [show formulaTruth M ρ (.or φ ψ) = formulaTruth M ρ φ ⊔ formulaTruth M ρ ψ by
      simp [GlobalModel.formulaTruth]]
  calc
    antecedentTruth M ρ (.or φ ψ :: Δ)
        = (formulaTruth M ρ φ ⊔ formulaTruth M ρ ψ) ⊓ antecedentTruth M ρ Δ := horAnte
    _ = (formulaTruth M ρ φ ⊓ antecedentTruth M ρ Δ) ⊔
          (formulaTruth M ρ ψ ⊓ antecedentTruth M ρ Δ) := by
            rw [inf_sup_right]
    _ ≤ formulaTruth M ρ χ := sup_le hφρ hψρ

/-- First disjunction introduction is sound in every global model. -/
theorem orR₁_valid (M : GlobalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ ψ : Formula Const Γ}
    (h : ValidSequent M Δ φ) :
    ValidSequent M Δ (.or φ ψ) := by
  intro ρ
  calc
    antecedentTruth M ρ Δ ≤ formulaTruth M ρ φ := h ρ
    _ ≤ formulaTruth M ρ (.or φ ψ) := by
      simp [GlobalModel.formulaTruth]

/-- Second disjunction introduction is sound in every global model. -/
theorem orR₂_valid (M : GlobalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ ψ : Formula Const Γ}
    (h : ValidSequent M Δ ψ) :
    ValidSequent M Δ (.or φ ψ) := by
  intro ρ
  calc
    antecedentTruth M ρ Δ ≤ formulaTruth M ρ ψ := h ρ
    _ ≤ formulaTruth M ρ (.or φ ψ) := by
      simp [GlobalModel.formulaTruth]

/-- Implication-right is sound in every global model. -/
theorem impR_valid (M : GlobalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ ψ : Formula Const Γ}
    (h : ValidSequent M (φ :: Δ) ψ) :
    ValidSequent M Δ (.imp φ ψ) := by
  intro ρ
  have hρ : formulaTruth M ρ φ ⊓ antecedentTruth M ρ Δ ≤ formulaTruth M ρ ψ := by
    simpa [GlobalModel.antecedentTruth, SemilocalModel.antecedentTruth] using h ρ
  have himp : antecedentTruth M ρ Δ ≤ formulaTruth M ρ φ ⇨ formulaTruth M ρ ψ := by
    rw [le_himp_iff]
    simpa [inf_assoc, inf_left_comm, inf_comm] using hρ
  simpa [GlobalModel.formulaTruth] using himp

/-- Implication-left is sound in every global model. -/
theorem impL_valid (M : GlobalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ ψ χ : Formula Const Γ}
    (hφ : ValidSequent M Δ φ)
    (hχ : ValidSequent M (ψ :: Δ) χ) :
    ValidSequent M (.imp φ ψ :: Δ) χ := by
  intro ρ
  let γ := antecedentTruth M ρ Δ
  let p := formulaTruth M ρ φ
  let q := formulaTruth M ρ ψ
  have hγp : γ ≤ p := hφ ρ
  have hbody : q ⊓ γ ≤ formulaTruth M ρ χ := by
    simpa [γ, q, GlobalModel.antecedentTruth, SemilocalModel.antecedentTruth] using hχ ρ
  have hq : (p ⇨ q) ⊓ γ ≤ q := by
    calc
      (p ⇨ q) ⊓ γ ≤ (p ⇨ q) ⊓ p := inf_le_inf_left _ hγp
      _ = p ⊓ (p ⇨ q) := by rw [inf_comm]
      _ ≤ q := inf_himp_le
  have hinto : (p ⇨ q) ⊓ γ ≤ q ⊓ γ := by
    exact le_inf hq inf_le_right
  have himpAnte : antecedentTruth M ρ (.imp φ ψ :: Δ) = (p ⇨ q) ⊓ γ := by
    change formulaTruth M ρ (.imp φ ψ) ⊓ antecedentTruth M ρ Δ = (p ⇨ q) ⊓ γ
    rw [show formulaTruth M ρ (.imp φ ψ) = p ⇨ q by
      simp [p, q, GlobalModel.formulaTruth]]
  have hpsiAnte : antecedentTruth M ρ (ψ :: Δ) = q ⊓ γ := by
    change formulaTruth M ρ ψ ⊓ antecedentTruth M ρ Δ = q ⊓ γ
    simp [q, γ]
  calc
    antecedentTruth M ρ (.imp φ ψ :: Δ) = (p ⇨ q) ⊓ γ := himpAnte
    _ ≤ q ⊓ γ := hinto
    _ = antecedentTruth M ρ (ψ :: Δ) := hpsiAnte.symm
    _ ≤ formulaTruth M ρ χ := hbody

/-- Universal-left is sound in every global model. -/
theorem allL_valid (M : GlobalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {χ : Formula Const Γ}
    (t : Term Const Γ σ)
    (h : ValidSequent M (instantiate (Base := Base) (Const := Const) t φ :: Δ) χ) :
    ValidSequent M (.all φ :: Δ) χ := by
  intro ρ
  have hinst :
      formulaTruth M ρ (instantiate (Base := Base) (Const := Const) t φ) =
        formulaTruth M
          (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ (eval M ρ t))
          φ := by
    exact SemilocalModel.formulaTruth_instantiate
      (M := M.toSemilocalModel) t φ ρ
  have hallEq :
      formulaTruth M ρ (.all φ) =
        ⨅ x,
          M.extent x ⇨
            formulaTruth M
              (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ x)
              φ := by
    exact SemilocalModel.formulaTruth_all
      (M := M.toSemilocalModel) (ρ := ρ) (φ := φ)
  have hall :
      formulaTruth M ρ (.all φ) ≤
        formulaTruth M
          (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ (eval M ρ t))
          φ := by
    rw [hallEq]
    calc
      (⨅ x,
          M.extent x ⇨
            formulaTruth M
              (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ x)
              φ) ≤
          M.extent (eval M ρ t) ⇨
            formulaTruth M
              (ApplicativeStructure.Env.extend
                M.toSemilocalModel.toApplicativeStructure ρ (eval M ρ t))
              φ := by
                exact iInf_le _ (eval M ρ t)
      _ = formulaTruth M
            (ApplicativeStructure.Env.extend
              M.toSemilocalModel.toApplicativeStructure ρ (eval M ρ t))
            φ := by
              simp [M.global]
  have hprem :
      formulaTruth M
          (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ (eval M ρ t))
          φ ⊓
        antecedentTruth M ρ Δ ≤
      formulaTruth M ρ χ := by
    have hprem0 :
        antecedentTruth M ρ (instantiate (Base := Base) (Const := Const) t φ :: Δ) ≤
        formulaTruth M ρ χ := by
      exact h ρ
    have hprem1 :
        formulaTruth M ρ (instantiate (Base := Base) (Const := Const) t φ) ⊓
          antecedentTruth M ρ Δ ≤
        formulaTruth M ρ χ := by
      simpa [GlobalModel.antecedentTruth, SemilocalModel.antecedentTruth] using hprem0
    rw [hinst] at hprem1
    exact hprem1
  calc
    antecedentTruth M ρ (.all φ :: Δ) =
        formulaTruth M ρ (.all φ) ⊓ antecedentTruth M ρ Δ := by
          simp [GlobalModel.antecedentTruth, SemilocalModel.antecedentTruth]
    _ ≤ formulaTruth M
          (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ (eval M ρ t))
          φ ⊓
          antecedentTruth M ρ Δ := by
            exact inf_le_inf_right _ hall
    _ ≤ formulaTruth M ρ χ := hprem

/-- Universal-right is sound in every global model. -/
theorem allR_valid (M : GlobalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)}
    (h : ValidSequent M (weakenAntecedents (Base := Base) (Const := Const) σ Δ) φ) :
    ValidSequent M Δ (.all φ) := by
  intro ρ
  have hallEq :
      formulaTruth M ρ (.all φ) =
      ⨅ x,
        M.extent x ⇨
          formulaTruth M
            (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ x)
            φ := by
    exact SemilocalModel.formulaTruth_all
      (M := M.toSemilocalModel) (ρ := ρ) (φ := φ)
  rw [hallEq]
  apply le_iInf
  intro x
  rw [M.global]
  simpa [GlobalModel.antecedentTruth, GlobalModel.formulaTruth] using
    h (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ x)

/-- Existential-left is sound in every global model. -/
theorem exL_valid (M : GlobalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {χ : Formula Const Γ}
    (h : ValidSequent M
      (φ :: weakenAntecedents (Base := Base) (Const := Const) σ Δ)
      (weaken (Base := Base) (Const := Const) (σ := σ) χ)) :
    ValidSequent M (.ex φ :: Δ) χ := by
  intro ρ
  have hexEq :
      formulaTruth M ρ (.ex φ) =
        ⨆ x,
          M.extent x ⊓
            formulaTruth M
              (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ x)
              φ := by
    exact SemilocalModel.formulaTruth_ex
      (M := M.toSemilocalModel) (ρ := ρ) (φ := φ)
  have hbody :
      ∀ x : M.Carrier σ,
        formulaTruth M
            (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ x)
            φ ⊓
          antecedentTruth M ρ Δ ≤
        formulaTruth M ρ χ := by
    intro x
    have hx :
        antecedentTruth M
            (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ x)
            (φ :: weakenAntecedents (Base := Base) (Const := Const) σ Δ) ≤
          formulaTruth M
            (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ x)
            (weaken (Base := Base) (Const := Const) (σ := σ) χ) := by
      exact h (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ x)
    have hweak :
        antecedentTruth M
            (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ x)
            (weakenAntecedents (Base := Base) (Const := Const) σ Δ) =
          antecedentTruth M ρ Δ := by
      exact SemilocalModel.antecedentTruth_weaken
        (M := M.toSemilocalModel) (ρ := ρ) (x := x) (Δ := Δ)
    have hx' :
        antecedentTruth M
            (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ x)
            (φ :: weakenAntecedents (Base := Base) (Const := Const) σ Δ) ≤
          formulaTruth M ρ χ := by
      simpa [GlobalModel.formulaTruth] using hx
    calc
      formulaTruth M
          (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ x)
          φ ⊓ antecedentTruth M ρ Δ =
        formulaTruth M
            (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ x)
            φ ⊓
          antecedentTruth M
            (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ x)
            (weakenAntecedents (Base := Base) (Const := Const) σ Δ) := by
              rw [← hweak]
      _ =
        antecedentTruth M
            (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ x)
            (φ :: weakenAntecedents (Base := Base) (Const := Const) σ Δ) := by
              simp [GlobalModel.antecedentTruth, SemilocalModel.antecedentTruth]
      _ ≤ formulaTruth M ρ χ := hx'
  calc
    antecedentTruth M ρ (.ex φ :: Δ) =
        formulaTruth M ρ (.ex φ) ⊓ antecedentTruth M ρ Δ := by
          simp [GlobalModel.antecedentTruth, SemilocalModel.antecedentTruth]
    _ =
        (⨆ x,
          M.extent x ⊓
            formulaTruth M
              (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ x)
              φ) ⊓
          antecedentTruth M ρ Δ := by
            rw [hexEq]
    _ =
        ⨆ x,
          (M.extent x ⊓
            formulaTruth M
              (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ x)
              φ) ⊓
            antecedentTruth M ρ Δ := by
              rw [iSup_inf_eq]
    _ =
        ⨆ x,
          formulaTruth M
            (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ x)
            φ ⊓
            antecedentTruth M ρ Δ := by
              apply iSup_congr
              intro x
              simp [M.global]
    _ ≤ formulaTruth M ρ χ := by
          exact iSup_le hbody

/-- Existential-right is sound in every global model. -/
theorem exR_valid (M : GlobalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {σ : Ty Base} {φ : Formula Const (σ :: Γ)}
    (t : Term Const Γ σ)
    (h : ValidSequent M Δ (instantiate (Base := Base) (Const := Const) t φ)) :
    ValidSequent M Δ (.ex φ) := by
  intro ρ
  have hinst :
      formulaTruth M ρ (instantiate (Base := Base) (Const := Const) t φ) =
        formulaTruth M
          (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ (eval M ρ t))
          φ := by
    exact SemilocalModel.formulaTruth_instantiate
      (M := M.toSemilocalModel) t φ ρ
  have hexEq :
      formulaTruth M ρ (.ex φ) =
        ⨆ x,
          M.extent x ⊓
            formulaTruth M
              (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ x)
              φ := by
    exact SemilocalModel.formulaTruth_ex
      (M := M.toSemilocalModel) (ρ := ρ) (φ := φ)
  calc
    antecedentTruth M ρ Δ ≤
        formulaTruth M ρ (instantiate (Base := Base) (Const := Const) t φ) := h ρ
    _ =
        formulaTruth M
          (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ (eval M ρ t))
          φ := hinst
    _ =
        M.extent (eval M ρ t) ⊓
          formulaTruth M
            (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ (eval M ρ t))
            φ := by
              simp [M.global]
    _ ≤ formulaTruth M ρ (.ex φ) := by
          rw [hexEq]
          exact le_iSup
            (fun x =>
              M.extent x ⊓
                formulaTruth M
                  (ApplicativeStructure.Env.extend M.toSemilocalModel.toApplicativeStructure ρ x)
                  φ)
            (eval M ρ t)

/-- Beta-eta conversion is sound in every global model. -/
theorem lam_valid (M : GlobalModel Base Const)
    {Γ : Ctx Base}
    {Δ Δ' : List (Formula Const Γ)}
    {φ φ' : Formula Const Γ}
    (hΔ : AntecedentsBetaEtaEq (Base := Base) (Const := Const) Δ Δ')
    (hφ : BetaEtaEq (Base := Base) (Const := Const) φ φ')
    (h : ValidSequent M Δ' φ') :
    ValidSequent M Δ φ := by
  intro ρ
  rw [show antecedentTruth M ρ Δ = antecedentTruth M ρ Δ' by
      simpa [GlobalModel.antecedentTruth] using
        (SemilocalModel.antecedentTruth_betaEtaEq
          (M := M.toSemilocalModel) (ρ := ρ) hΔ)]
  rw [show formulaTruth M ρ φ = formulaTruth M ρ φ' by
      simpa [GlobalModel.formulaTruth] using
        (SemilocalModel.formulaTruth_betaEtaEq
          (M := M.toSemilocalModel) (ρ := ρ) hφ)]
  exact h ρ

/-- Native archive-free soundness for the propositional sequent fragment. -/
theorem propositional_soundness (M : GlobalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    PropositionalDerivable Const Δ φ → ValidSequent M Δ φ := by
  intro d
  induction d with
  | ax h => exact ax_valid M h
  | topR => exact topR_valid M
  | botL => exact botL_valid M
  | andL h ih => exact andL_valid M ih
  | andR h₁ h₂ ih₁ ih₂ => exact andR_valid M ih₁ ih₂
  | orL h₁ h₂ ih₁ ih₂ => exact orL_valid M ih₁ ih₂
  | orR₁ h ih => exact orR₁_valid M ih
  | orR₂ h ih => exact orR₂_valid M ih
  | impL h₁ h₂ ih₁ ih₂ => exact impL_valid M ih₁ ih₂
  | impR h ih => exact impR_valid M ih

/-- Native archive-free soundness for the full cut-free sequent calculus. -/
theorem soundness (M : GlobalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    Derivable (Base := Base) (Const := Const) Δ φ → ValidSequent M Δ φ := by
  intro d
  induction d with
  | ax h => exact ax_valid M h
  | topR => exact topR_valid M
  | botL => exact botL_valid M
  | andL h ih => exact andL_valid M ih
  | andR h₁ h₂ ih₁ ih₂ => exact andR_valid M ih₁ ih₂
  | orL h₁ h₂ ih₁ ih₂ => exact orL_valid M ih₁ ih₂
  | orR₁ h ih => exact orR₁_valid M ih
  | orR₂ h ih => exact orR₂_valid M ih
  | impL h₁ h₂ ih₁ ih₂ => exact impL_valid M ih₁ ih₂
  | impR h ih => exact impR_valid M ih
  | allL t h ih => exact allL_valid M t ih
  | allR h ih => exact allR_valid M ih
  | exL h ih => exact exL_valid M ih
  | exR t h ih => exact exR_valid M t ih
  | lam hΔ hφ hder ih => exact lam_valid M hΔ hφ ih

/-- The global-model soundness target is now proved natively. -/
theorem soundness_target (M : GlobalModel Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    SoundnessTarget M Δ φ :=
  soundness M

end GlobalModel

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
