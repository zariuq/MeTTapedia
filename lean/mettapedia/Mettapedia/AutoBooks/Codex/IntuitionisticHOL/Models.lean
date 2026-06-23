import Mathlib.Order.LatticeIntervals
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.HeytingAlgebra
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ApplicativeStructure
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Sequent

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v w w'

/-- First-pass semilocal model interface for the DeMarco-Lipton soundness layer. -/
structure SemilocalModel (Base : Type u) (Const : Ty Base → Type v)
    extends ApplicativeStructure Base Const where
  Omega : Type w'
  frame : HeytingFrame Omega
  truth : Carrier propTy → Omega
  extent : {τ : Ty Base} → Carrier τ → Omega
  topP : Carrier propTy
  botP : Carrier propTy
  andP : Carrier propTy → Carrier propTy → Carrier propTy
  orP : Carrier propTy → Carrier propTy → Carrier propTy
  impP : Carrier propTy → Carrier propTy → Carrier propTy
  eqP : {τ : Ty Base} → Carrier τ → Carrier τ → Carrier propTy
  allP : {σ : Ty Base} → (Carrier σ → Carrier propTy) → Carrier propTy
  exP : {σ : Ty Base} → (Carrier σ → Carrier propTy) → Carrier propTy
  truth_top : truth topP = ⊤
  truth_bot : truth botP = ⊥
  truth_and : ∀ p q, truth (andP p q) = truth p ⊓ truth q
  truth_or : ∀ p q, truth (orP p q) = truth p ⊔ truth q
  truth_imp : ∀ p q, truth (impP p q) = truth p ⇨ truth q
  truth_all : ∀ {σ : Ty Base} (f : Carrier σ → Carrier propTy),
    truth (allP f) = ⨅ x, extent x ⇨ truth (f x)
  truth_ex : ∀ {σ : Ty Base} (f : Carrier σ → Carrier propTy),
    truth (exP f) = ⨆ x, extent x ⊓ truth (f x)

attribute [instance] SemilocalModel.frame

namespace IicFrame

variable {α : Type*} [HeytingFrame α]

instance (c : α) : CompleteLattice (Set.Iic c) where
  bot := ⟨⊥, bot_le⟩
  bot_le x := by
    show (⊥ : α) ≤ x.1
    exact bot_le
  top := ⟨c, le_rfl⟩
  le_top x := x.2
  sup x y := ⟨x.1 ⊔ y.1, sup_le x.2 y.2⟩
  le_sup_left x y := by
    show x.1 ≤ x.1 ⊔ y.1
    exact le_sup_left
  le_sup_right x y := by
    show y.1 ≤ x.1 ⊔ y.1
    exact le_sup_right
  sup_le x y z hx hy := by
    show x.1 ⊔ y.1 ≤ z.1
    exact sup_le hx hy
  inf x y := ⟨x.1 ⊓ y.1, le_trans inf_le_left x.2⟩
  inf_le_left x y := by
    show x.1 ⊓ y.1 ≤ x.1
    exact inf_le_left
  inf_le_right x y := by
    show x.1 ⊓ y.1 ≤ y.1
    exact inf_le_right
  le_inf a b d h1 h2 := by
    show a.1 ≤ b.1 ⊓ d.1
    exact le_inf h1 h2
  sSup s := ⟨sSup ((fun x : Set.Iic c => x.1) '' s), by
    apply sSup_le
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact z.2⟩
  isLUB_sSup s := by
    constructor
    · intro x hx
      show x.1 ≤ sSup ((fun x : Set.Iic c => x.1) '' s)
      exact le_sSup ⟨x, hx, rfl⟩
    · intro x hx
      show sSup ((fun x : Set.Iic c => x.1) '' s) ≤ x.1
      exact sSup_le (by
        intro y hy
        rcases hy with ⟨z, hz, rfl⟩
        exact hx hz)
  sInf s := ⟨sInf ((fun x : Set.Iic c => x.1) '' s) ⊓ c, inf_le_right⟩
  isGLB_sInf s := by
    constructor
    · intro x hx
      show sInf ((fun x : Set.Iic c => x.1) '' s) ⊓ c ≤ x.1
      exact le_trans inf_le_left (sInf_le ⟨x, hx, rfl⟩)
    · intro x hx
      show x.1 ≤ sInf ((fun x : Set.Iic c => x.1) '' s) ⊓ c
      apply le_inf
      · apply le_sInf
        intro y hy
        rcases hy with ⟨z, hz, rfl⟩
        exact hx hz
      · exact x.2

noncomputable def himp (c : α) : Set.Iic c → Set.Iic c → Set.Iic c :=
  fun x y => ⟨(x.1 ⇨ y.1) ⊓ c, inf_le_right⟩

@[simp] theorem coe_iSup {ι : Sort*} (c : α) (f : ι → Set.Iic c) :
    (((⨆ i, f i) : Set.Iic c) : α) = ⨆ i, (f i).1 := by
  change sSup ((fun x : Set.Iic c => x.1) '' Set.range f) = _
  have hrange :
      ((fun x : Set.Iic c => x.1) '' Set.range f) = Set.range (fun i => (f i).1) := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · intro hy
      rcases hy with ⟨i, rfl⟩
      exact ⟨f i, ⟨i, rfl⟩, rfl⟩
  rw [hrange, sSup_range]

@[simp] theorem coe_iInf {ι : Sort*} (c : α) (f : ι → Set.Iic c) :
    (((⨅ i, f i) : Set.Iic c) : α) = (⨅ i, (f i).1) ⊓ c := by
  change sInf ((fun x : Set.Iic c => x.1) '' Set.range f) ⊓ c = _
  have hrange :
      ((fun x : Set.Iic c => x.1) '' Set.range f) = Set.range (fun i => (f i).1) := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · intro hy
      rcases hy with ⟨i, rfl⟩
      exact ⟨f i, ⟨i, rfl⟩, rfl⟩
  rw [hrange, sInf_range]

theorem himp_relativize (a b u : α) :
    ((a ⊓ u) ⇨ (b ⊓ u)) ⊓ u = (a ⇨ b) ⊓ u := by
  apply le_antisymm
  · apply le_inf
    · rw [le_himp_iff]
      calc
        (((a ⊓ u) ⇨ (b ⊓ u)) ⊓ u) ⊓ a
            = ((a ⊓ u) ⇨ (b ⊓ u)) ⊓ (a ⊓ u) := by
                rw [inf_assoc, inf_comm u a]
        _ = (a ⊓ u) ⊓ ((a ⊓ u) ⇨ (b ⊓ u)) := by
              rw [inf_comm]
        _ ≤ b ⊓ u := inf_himp_le
        _ ≤ b := inf_le_left
    · exact inf_le_right
  · apply le_inf
    · rw [le_himp_iff]
      apply le_inf
      · have hleA : ((a ⇨ b) ⊓ u) ⊓ (a ⊓ u) ≤ a := by
          exact le_trans inf_le_right inf_le_left
        have hleImp : ((a ⇨ b) ⊓ u) ⊓ (a ⊓ u) ≤ a ⇨ b := by
          exact le_trans inf_le_left inf_le_left
        have hpair : ((a ⇨ b) ⊓ u) ⊓ (a ⊓ u) ≤ a ⊓ (a ⇨ b) := by
          exact le_inf hleA hleImp
        exact le_trans hpair (by
          simp)
      · exact le_trans inf_le_left inf_le_right
    · exact inf_le_right

theorem iInf_inf_cut {ι : Sort*} (f : ι → α) (u : α) :
    ((⨅ i, f i ⊓ u) ⊓ u) = (⨅ i, f i) ⊓ u := by
  apply le_antisymm
  · apply le_inf
    · apply le_iInf
      intro i
      exact le_trans (le_trans inf_le_left (iInf_le (fun i => f i ⊓ u) i)) inf_le_left
    · exact inf_le_right
  · apply le_inf
    · apply le_iInf
      intro i
      exact le_inf (le_trans inf_le_left (iInf_le f i)) inf_le_right
    · exact inf_le_right

/-- The Lemma 4.12 quotient map `v ↦ v ∧ u` into the interval frame `Ω_u`. -/
def cut (u : α) : α → Set.Iic u := fun a => ⟨a ⊓ u, inf_le_right⟩

@[simp] theorem coe_cut (u a : α) :
    ((cut u a : Set.Iic u) : α) = a ⊓ u := rfl

theorem cut_surjective (u : α) : Function.Surjective (cut u) := by
  intro x
  refine ⟨x.1, Subtype.ext ?_⟩
  simpa [cut, inf_comm] using (inf_eq_right.mpr x.2 : u ⊓ x.1 = x.1)

@[simp] theorem cut_top (u : α) : cut u ⊤ = ⊤ := by
  ext
  simp [cut]

@[simp] theorem cut_bot (u : α) : cut u ⊥ = ⊥ := by
  ext
  simp [cut]

@[simp] theorem cut_eq_top_iff (u a : α) :
    cut u a = (⊤ : Set.Iic u) ↔ u ≤ a := by
  constructor
  · intro h
    have hval : (cut u a : Set.Iic u).1 = ((⊤ : Set.Iic u) : Set.Iic u).1 :=
      congrArg Subtype.val h
    change a ⊓ u = u at hval
    exact inf_eq_right.mp (by simpa [inf_comm] using hval)
  · intro hu
    apply Subtype.ext
    simp [cut, inf_eq_right.mpr hu]

@[simp] theorem cut_inf (u a b : α) :
    cut u (a ⊓ b) = cut u a ⊓ cut u b := by
  ext
  simp [cut, inf_left_comm, inf_comm]

@[simp] theorem cut_sup (u a b : α) :
    cut u (a ⊔ b) = cut u a ⊔ cut u b := by
  ext
  simp [cut, inf_sup_right]

@[simp] theorem cut_iSup {ι : Sort*} (u : α) (f : ι → α) :
    cut u (⨆ i, f i) = ⨆ i, cut u (f i) := by
  ext
  change (⨆ i, f i) ⊓ u = (((⨆ i, cut u (f i)) : Set.Iic u) : α)
  rw [coe_iSup, iSup_inf_eq]
  simp [cut]

@[simp] theorem cut_iInf {ι : Sort*} (u : α) (f : ι → α) :
    cut u (⨅ i, f i) = ⨅ i, cut u (f i) := by
  ext
  rw [coe_iInf]
  simp [cut, iInf_inf_cut]

noncomputable instance (c : α) : HeytingFrame (Set.Iic c) := by
  refine Order.Frame.ofMinimalAxioms ?_
  refine
    { toCompleteLattice := inferInstance
      inf_sSup_le_iSup_inf := ?_ }
  intro a s
  show ((a ⊓ sSup s : Set.Iic c) : α) ≤ ((⨆ b ∈ s, a ⊓ b : Set.Iic c) : Set.Iic c)
  show a.1 ⊓ sSup ((fun x : Set.Iic c => x.1) '' s) ≤
      ((⨆ b ∈ s, a ⊓ b : Set.Iic c) : Set.Iic c)
  rw [inf_sSup_eq]
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  rcases hy with ⟨z, hz, rfl⟩
  have hsub : a ⊓ z ≤ (⨆ b ∈ s, a ⊓ b : Set.Iic c) := by
    exact le_iSup_of_le z (le_iSup_of_le hz le_rfl)
  exact hsub

@[simp] theorem cut_himp_frame (u a b : α) :
    cut u (a ⇨ b) = (cut u a ⇨ cut u b : Set.Iic u) := by
  apply le_antisymm
  · rw [le_himp_iff]
    show (((a ⇨ b) ⊓ u) ⊓ (a ⊓ u)) ≤ b ⊓ u
    calc
      (((a ⇨ b) ⊓ u) ⊓ (a ⊓ u)) = ((a ⇨ b) ⊓ a) ⊓ u := by
        ac_rfl
      _ ≤ b ⊓ u := by
        have hab : (a ⇨ b) ⊓ a ≤ b := by
          calc
            (a ⇨ b) ⊓ a = a ⊓ (a ⇨ b) := by
              rw [inf_comm]
            _ ≤ b := inf_himp_le
        apply le_inf
        · exact le_trans inf_le_left hab
        · exact inf_le_right
  · show (((cut u a ⇨ cut u b : Set.Iic u) : Set.Iic u) : α) ≤ (a ⇨ b) ⊓ u
    apply le_inf
    · rw [le_himp_iff]
      have hsub :
          (cut u a : Set.Iic u) ⊓ (cut u a ⇨ cut u b : Set.Iic u) ≤ cut u b := by
        exact inf_himp_le
      have hbase :
          (((cut u a ⇨ cut u b : Set.Iic u) : Set.Iic u) : α) ⊓ (a ⊓ u) ≤ b ⊓ u := by
        calc
          (((cut u a ⇨ cut u b : Set.Iic u) : Set.Iic u) : α) ⊓ (a ⊓ u)
              = (a ⊓ u) ⊓ (((cut u a ⇨ cut u b : Set.Iic u) : Set.Iic u) : α) := by
                  ac_rfl
          _ ≤ b ⊓ u := by
                exact hsub
      have hu : (((cut u a ⇨ cut u b : Set.Iic u) : Set.Iic u) : α) ≤ u :=
        (cut u a ⇨ cut u b : Set.Iic u).2
      have hrew :
          (((cut u a ⇨ cut u b : Set.Iic u) : Set.Iic u) : α) ⊓ a =
            (((cut u a ⇨ cut u b : Set.Iic u) : Set.Iic u) : α) ⊓ (a ⊓ u) := by
        have hru :
            (((cut u a ⇨ cut u b : Set.Iic u) : Set.Iic u) : α) ⊓ a ≤ u :=
          le_trans inf_le_left hu
        calc
          (((cut u a ⇨ cut u b : Set.Iic u) : Set.Iic u) : α) ⊓ a =
              u ⊓ ((((cut u a ⇨ cut u b : Set.Iic u) : Set.Iic u) : α) ⊓ a) := by
                exact (inf_eq_right.mpr hru).symm
          _ =
              (((cut u a ⇨ cut u b : Set.Iic u) : Set.Iic u) : α) ⊓ (a ⊓ u) := by
                ac_rfl
      calc
        (((cut u a ⇨ cut u b : Set.Iic u) : Set.Iic u) : α) ⊓ a =
            (((cut u a ⇨ cut u b : Set.Iic u) : Set.Iic u) : α) ⊓ (a ⊓ u) := hrew
        _ ≤ b ⊓ u := hbase
        _ ≤ b := inf_le_left
    · exact (cut u a ⇨ cut u b : Set.Iic u).2

end IicFrame

/-- Global models are the current theorem-level specialization of semilocal models. -/
structure GlobalModel (Base : Type u) (Const : Ty Base → Type v)
    extends SemilocalModel Base Const where
  global : ∀ {τ : Ty Base} (x : Carrier τ), extent x = ⊤

namespace SemilocalModel

variable {Base : Type u} {Const : Ty Base → Type v}

abbrev Env (M : SemilocalModel Base Const) (Γ : Ctx Base) :=
  ApplicativeStructure.Env M.toApplicativeStructure Γ

/-- Precompose an environment with a variable renaming. -/
def renameEnv (M : SemilocalModel Base Const)
    (ρr : Rename Base Γ Δ) (ν : Env M Δ) : Env M Γ :=
  fun {_τ} v => ν (ρr v)

/-- Interpret a term in a semilocal model. -/
def eval (M : SemilocalModel Base Const) (ρ : Env M Γ) :
    Term Const Γ τ → M.Carrier τ
  | .var v => ρ v
  | .const c => M.const c
  | .app f t => M.app (eval M ρ f) (eval M ρ t)
  | .lam t => M.lam (fun x => eval M (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) t)
  | .top => M.topP
  | .bot => M.botP
  | .and φ ψ => M.andP (eval M ρ φ) (eval M ρ ψ)
  | .or φ ψ => M.orP (eval M ρ φ) (eval M ρ ψ)
  | .imp φ ψ => M.impP (eval M ρ φ) (eval M ρ ψ)
  | .not φ => M.impP (eval M ρ φ) M.botP
  | .eq t u => M.eqP (eval M ρ t) (eval M ρ u)
  | .all φ => M.allP (fun x => eval M (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) φ)
  | .ex φ => M.exP (fun x => eval M (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) φ)

/-- Truth value of a formula under an environment. -/
def formulaTruth (M : SemilocalModel Base Const) (ρ : Env M Γ)
    (φ : Formula Const Γ) : M.Omega :=
  M.truth (eval M ρ φ)

/-- Meet of the antecedent truth values. -/
def antecedentTruth (M : SemilocalModel Base Const) (ρ : Env M Γ) :
    List (Formula Const Γ) → M.Omega
  | [] => ⊤
  | φ :: Δ => formulaTruth M ρ φ ⊓ antecedentTruth M ρ Δ

/-- A local environment is global when every interpreted term has maximal extent. -/
def IsGlobalEnv (M : SemilocalModel Base Const) (ρ : Env M Γ) : Prop :=
  ∀ {τ : Ty Base} (t : Term Const Γ τ), M.extent (eval M ρ t) = ⊤

/-- Lower-bound form of globality used by the relativized model `D_u`. -/
def HasExtentLowerBound (M : SemilocalModel Base Const)
    (u : M.Omega) (ρ : Env M Γ) : Prop :=
  ∀ {τ : Ty Base} (t : Term Const Γ τ), u ≤ M.extent (eval M ρ t)

/-- Paper-facing closure condition for Lemma 4.13's environment-extension step. -/
def SupportsRelativization (M : SemilocalModel Base Const) : Prop :=
  ∀ {Γ : Ctx Base} {σ : Ty Base} (ρ : Env M Γ) (d : M.Carrier σ),
    IsGlobalEnv M ρ →
    HasExtentLowerBound M (M.extent d)
      (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ d)

/-- Lower-bound environments remain lower-bounded after adjoining an element. -/
def SupportsLowerBoundExtension (M : SemilocalModel Base Const) : Prop :=
  ∀ {Γ : Ctx Base} {σ : Ty Base} (u : M.Omega) (ρ : Env M Γ) (d : M.Carrier σ),
    HasExtentLowerBound M u ρ →
    HasExtentLowerBound M (M.extent d ⊓ u)
      (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ d)

@[simp] theorem isGlobalEnv_iff_hasExtentLowerBound_top
    (M : SemilocalModel Base Const) (ρ : Env M Γ) :
    IsGlobalEnv M ρ ↔ HasExtentLowerBound M ⊤ ρ := by
  constructor
  · intro h τ t
    rw [h t]
  · intro h τ t
    apply top_unique
    exact h t

theorem supportsRelativization_of_supportsLowerBoundExtension
    (M : SemilocalModel Base Const)
    (h : SupportsLowerBoundExtension M) :
    SupportsRelativization M := by
  intro Γ σ ρ d hρ
  have htop : HasExtentLowerBound M ⊤ ρ :=
    (isGlobalEnv_iff_hasExtentLowerBound_top M ρ).1 hρ
  intro τ t
  simpa using h ⊤ ρ d htop t

/-- Relativize a semilocal model along a truth value `u`, following Lemma 4.13. -/
noncomputable def relativize (M : SemilocalModel Base Const) (u : M.Omega) :
    SemilocalModel Base Const where
  toApplicativeStructure := M.toApplicativeStructure
  Omega := Set.Iic u
  frame := inferInstance
  truth p := IicFrame.cut u (M.truth p)
  extent x := IicFrame.cut u (M.extent x)
  topP := M.topP
  botP := M.botP
  andP := M.andP
  orP := M.orP
  impP := M.impP
  eqP := M.eqP
  allP := M.allP
  exP := M.exP
  truth_top := by
    rw [M.truth_top]
    exact IicFrame.cut_top u
  truth_bot := by
    rw [M.truth_bot]
    exact IicFrame.cut_bot u
  truth_and := by
    intro p q
    rw [M.truth_and]
    exact IicFrame.cut_inf u (M.truth p) (M.truth q)
  truth_or := by
    intro p q
    rw [M.truth_or]
    exact IicFrame.cut_sup u (M.truth p) (M.truth q)
  truth_imp := by
    intro p q
    rw [M.truth_imp]
    exact IicFrame.cut_himp_frame u (M.truth p) (M.truth q)
  truth_all := by
    intro σ f
    rw [M.truth_all]
    rw [IicFrame.cut_iInf]
    apply iInf_congr
    intro x
    exact IicFrame.cut_himp_frame u (M.extent x) (M.truth (f x))
  truth_ex := by
    intro σ f
    rw [M.truth_ex]
    calc
      IicFrame.cut u (⨆ x, M.extent x ⊓ M.truth (f x)) =
          ⨆ x, IicFrame.cut u (M.extent x ⊓ M.truth (f x)) := by
            exact IicFrame.cut_iSup u (fun x => M.extent x ⊓ M.truth (f x))
      _ = ⨆ x, IicFrame.cut u (M.extent x) ⊓ IicFrame.cut u (M.truth (f x)) := by
            apply iSup_congr
            intro x
            exact IicFrame.cut_inf u (M.extent x) (M.truth (f x))

@[simp] theorem eval_relativize (M : SemilocalModel Base Const)
    (u : M.Omega) :
    ∀ {Γ : Ctx Base} {τ : Ty Base} (ρ : Env M Γ) (t : Term Const Γ τ),
      eval (M.relativize u) ρ t = eval M ρ t
  | _, _, ρ, .var _ => rfl
  | _, _, ρ, .const _ => rfl
  | _, _, ρ, .app f t => by
      change M.app (eval (M.relativize u) ρ f) (eval (M.relativize u) ρ t) =
        M.app (eval M ρ f) (eval M ρ t)
      rw [eval_relativize M u ρ f, eval_relativize M u ρ t]
  | _, _, ρ, .lam t => by
      change M.lam (fun x => eval (M.relativize u)
        (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) t) =
        M.lam (fun x => eval M
          (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) t)
      apply congrArg M.lam
      funext x
      exact eval_relativize M u
        (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) t
  | _, _, ρ, .top => by
      change M.topP = M.topP
      rfl
  | _, _, ρ, .bot => by
      change M.botP = M.botP
      rfl
  | _, _, ρ, .and φ ψ => by
      change M.andP (eval (M.relativize u) ρ φ) (eval (M.relativize u) ρ ψ) =
        M.andP (eval M ρ φ) (eval M ρ ψ)
      rw [eval_relativize M u ρ φ, eval_relativize M u ρ ψ]
  | _, _, ρ, .or φ ψ => by
      change M.orP (eval (M.relativize u) ρ φ) (eval (M.relativize u) ρ ψ) =
        M.orP (eval M ρ φ) (eval M ρ ψ)
      rw [eval_relativize M u ρ φ, eval_relativize M u ρ ψ]
  | _, _, ρ, .imp φ ψ => by
      change M.impP (eval (M.relativize u) ρ φ) (eval (M.relativize u) ρ ψ) =
        M.impP (eval M ρ φ) (eval M ρ ψ)
      rw [eval_relativize M u ρ φ, eval_relativize M u ρ ψ]
  | _, _, ρ, .not φ => by
      change M.impP (eval (M.relativize u) ρ φ) M.botP =
        M.impP (eval M ρ φ) M.botP
      rw [eval_relativize M u ρ φ]
  | _, _, ρ, .eq t v => by
      change M.eqP (eval (M.relativize u) ρ t) (eval (M.relativize u) ρ v) =
        M.eqP (eval M ρ t) (eval M ρ v)
      rw [eval_relativize M u ρ t, eval_relativize M u ρ v]
  | _, _, ρ, .all φ => by
      change M.allP (fun x => eval (M.relativize u)
        (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) φ) =
        M.allP (fun x => eval M
          (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) φ)
      apply congrArg M.allP
      funext x
      exact eval_relativize M u
        (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) φ
  | _, _, ρ, .ex φ => by
      change M.exP (fun x => eval (M.relativize u)
        (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) φ) =
        M.exP (fun x => eval M
          (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) φ)
      apply congrArg M.exP
      funext x
      exact eval_relativize M u
        (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) φ

@[simp] theorem formulaTruth_relativize (M : SemilocalModel Base Const)
    (u : M.Omega) (ρ : Env M Γ) (φ : Formula Const Γ) :
    formulaTruth (M.relativize u) ρ φ = IicFrame.cut u (formulaTruth M ρ φ) := by
  rw [formulaTruth, formulaTruth, eval_relativize]
  rfl

@[simp] theorem coe_formulaTruth_relativize (M : SemilocalModel Base Const)
    (u : M.Omega) (ρ : Env M Γ) (φ : Formula Const Γ) :
    (formulaTruth (M.relativize u) ρ φ).1 =
      formulaTruth M ρ φ ⊓ u := by
  rw [formulaTruth_relativize]
  rfl

@[simp] theorem antecedentTruth_relativize (M : SemilocalModel Base Const)
    (u : M.Omega) (ρ : Env M Γ) (Δ : List (Formula Const Γ)) :
    antecedentTruth (M.relativize u) ρ Δ = IicFrame.cut u (antecedentTruth M ρ Δ) := by
  induction Δ with
  | nil =>
      exact (IicFrame.cut_top u).symm
  | cons φ Δ ih =>
      rw [antecedentTruth, antecedentTruth, formulaTruth_relativize, ih]
      exact (IicFrame.cut_inf u (formulaTruth M ρ φ) (antecedentTruth M ρ Δ)).symm

@[simp] theorem coe_antecedentTruth_relativize (M : SemilocalModel Base Const)
    (u : M.Omega) (ρ : Env M Γ) (Δ : List (Formula Const Γ)) :
    (antecedentTruth (M.relativize u) ρ Δ).1 =
      antecedentTruth M ρ Δ ⊓ u := by
  rw [antecedentTruth_relativize]
  rfl

@[simp] theorem isGlobalEnv_relativize_iff (M : SemilocalModel Base Const)
    (u : M.Omega) (ρ : Env M Γ) :
    IsGlobalEnv (M.relativize u) ρ ↔ HasExtentLowerBound M u ρ := by
  constructor
  · intro h τ t
    have hbound :
        u ≤ M.extent (eval (M.relativize u) ρ t) := by
      have ht := h t
      exact (IicFrame.cut_eq_top_iff u (M.extent (eval (M.relativize u) ρ t))).1 ht
    simpa [eval_relativize] using hbound
  · intro h τ t
    have hbound :
        u ≤ M.extent (eval (M.relativize u) ρ t) := by
      simpa [eval_relativize] using h t
    have hcut :
        IicFrame.cut u (M.extent (eval (M.relativize u) ρ t)) = (⊤ : Set.Iic u) :=
      (IicFrame.cut_eq_top_iff u (M.extent (eval (M.relativize u) ρ t))).2 hbound
    exact hcut

theorem isGlobalEnv_relativize (M : SemilocalModel Base Const)
    (u : M.Omega) (ρ : Env M Γ)
    (h : HasExtentLowerBound M u ρ) :
    IsGlobalEnv (M.relativize u) ρ :=
  (isGlobalEnv_relativize_iff M u ρ).2 h

theorem hasExtentLowerBound_of_isGlobalEnv_relativize
    (M : SemilocalModel Base Const)
    (u : M.Omega) (ρ : Env M Γ)
    (h : IsGlobalEnv (M.relativize u) ρ) :
    HasExtentLowerBound M u ρ :=
  (isGlobalEnv_relativize_iff M u ρ).1 h

/-- Paper-facing uniform version of Lemma 4.13:
every relativized model `D_u` satisfies the semilocal environment-extension clause. -/
def SupportsUniformRelativization (M : SemilocalModel Base Const) : Prop :=
  ∀ u : M.Omega, SupportsRelativization (M.relativize u)

theorem supportsLowerBoundExtension_relativize
    (M : SemilocalModel Base Const)
    (h : SupportsLowerBoundExtension M) (u : M.Omega) :
    SupportsLowerBoundExtension (M.relativize u) := by
  intro Γ σ v ρ d hρ τ t
  have hρbase : HasExtentLowerBound M v.1 ρ := by
    intro τ t
    have hv :
        v.1 ≤ M.extent ((M.relativize u).eval ρ t) ⊓ u := by
      exact hρ t
    have hv' : v.1 ≤ M.extent ((M.relativize u).eval ρ t) :=
      le_trans hv inf_le_left
    simpa [eval_relativize] using hv'
  have hstep :
      M.extent d ⊓ v.1 ≤
        M.extent
          (eval M (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ d) t) := by
    exact h v.1 ρ d hρbase t
  show
      (((M.relativize u).extent d ⊓ v : Set.Iic u).1 ≤
        ((M.relativize u).extent
          ((M.relativize u).eval
            (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ d) t)).1)
  rw [eval_relativize]
  simp [relativize, IicFrame.cut, inf_left_comm, inf_comm]
  calc
    u ⊓ (v.1 ⊓ M.extent d) ≤ v.1 ⊓ M.extent d := inf_le_right
    _ = M.extent d ⊓ v.1 := by ac_rfl
    _ ≤
        M.extent
          (eval M (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ d) t) := hstep

theorem supportsUniformRelativization_of_supportsLowerBoundExtension
    (M : SemilocalModel Base Const)
    (h : SupportsLowerBoundExtension M) :
    SupportsUniformRelativization M := by
  intro u
  exact supportsRelativization_of_supportsLowerBoundExtension
    (M.relativize u) (supportsLowerBoundExtension_relativize M h u)

theorem supportsLowerBoundExtension_of_supportsUniformRelativization
    (M : SemilocalModel Base Const)
    (h : SupportsUniformRelativization M) :
    SupportsLowerBoundExtension M := by
  intro Γ σ u ρ d hρ τ t
  have hρu : IsGlobalEnv (M.relativize u) ρ :=
    isGlobalEnv_relativize M u ρ hρ
  have hrel :
      HasExtentLowerBound (M.relativize u) ((M.relativize u).extent d)
        (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ d) :=
    h u ρ d hρu
  have hrel' :
      (M.extent d ⊓ u) ≤
        M.extent
          (eval M (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ d) t) := by
    have hv :
        (M.extent d ⊓ u) ≤
          M.extent
            ((M.relativize u).eval
              (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ d) t) := by
      simpa [relativize, IicFrame.cut] using
        (show ((M.relativize u).extent d).1 ≤
          ((M.relativize u).extent
            ((M.relativize u).eval
              (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ d) t)).1 from hrel t)
    simpa [eval_relativize] using hv
  exact hrel'

theorem supportsUniformRelativization_iff_supportsLowerBoundExtension
    (M : SemilocalModel Base Const) :
    SupportsUniformRelativization M ↔ SupportsLowerBoundExtension M := by
  constructor
  · exact supportsLowerBoundExtension_of_supportsUniformRelativization M
  · exact supportsUniformRelativization_of_supportsLowerBoundExtension M

/-- A concrete stronger semantic package ensuring that every term constructor
preserves maximal existence strongly enough for structural lower-bound
induction on terms. -/
structure StructuralExtent (M : SemilocalModel Base Const) : Prop where
  const_top : ∀ {τ : Ty Base} (c : Const τ), M.extent (M.const c) = ⊤
  app_mono : ∀ {σ τ : Ty Base} (f : M.Carrier (σ ⇒ τ)) (x : M.Carrier σ),
    M.extent f ⊓ M.extent x ≤ M.extent (M.app f x)
  lam_top : ∀ {σ τ : Ty Base} (f : M.Carrier σ → M.Carrier τ),
    M.extent (M.lam f) = ⊤
  top_top : M.extent M.topP = ⊤
  bot_top : M.extent M.botP = ⊤
  and_top : ∀ p q, M.extent (M.andP p q) = ⊤
  or_top : ∀ p q, M.extent (M.orP p q) = ⊤
  imp_top : ∀ p q, M.extent (M.impP p q) = ⊤
  eq_top : ∀ {τ : Ty Base} (x y : M.Carrier τ), M.extent (M.eqP x y) = ⊤
  all_top : ∀ {σ : Ty Base} (f : M.Carrier σ → M.Carrier propTy),
    M.extent (M.allP f) = ⊤
  ex_top : ∀ {σ : Ty Base} (f : M.Carrier σ → M.Carrier propTy),
    M.extent (M.exP f) = ⊤

namespace StructuralExtent

theorem hasExtentLowerBound_eval
    {M : SemilocalModel Base Const} (h : StructuralExtent M)
    (u : M.Omega) (ρ : Env M Γ)
    (hρ : ∀ {τ : Ty Base} (v : Var Γ τ), u ≤ M.extent (ρ v)) :
    ∀ {τ : Ty Base} (t : Term Const Γ τ), u ≤ M.extent (eval M ρ t)
  | _, .var v => hρ v
  | _, .const c => by
      simp [eval, h.const_top c]
  | _, .app f t => by
      have hf : u ≤ M.extent (eval M ρ f) := hasExtentLowerBound_eval h u ρ hρ f
      have ht : u ≤ M.extent (eval M ρ t) := hasExtentLowerBound_eval h u ρ hρ t
      calc
        u ≤ M.extent (eval M ρ f) ⊓ M.extent (eval M ρ t) := le_inf hf ht
        _ ≤ M.extent (eval M ρ (.app f t)) := h.app_mono _ _
  | _, .lam t => by
      simp [eval, h.lam_top]
  | _, .top => by
      simp [eval, h.top_top]
  | _, .bot => by
      simp [eval, h.bot_top]
  | _, .and φ ψ => by
      simp [eval, h.and_top]
  | _, .or φ ψ => by
      simp [eval, h.or_top]
  | _, .imp φ ψ => by
      simp [eval, h.imp_top]
  | _, .not φ => by
      simp [eval, h.imp_top]
  | _, .eq t u' => by
      simp [eval, h.eq_top]
  | _, .all φ => by
      simp [eval, h.all_top]
  | _, .ex φ => by
      simp [eval, h.ex_top]

theorem supportsLowerBoundExtension
    {M : SemilocalModel Base Const} (h : StructuralExtent M) :
    SupportsLowerBoundExtension M := by
  intro Γ σ u ρ d hρ τ t
  exact hasExtentLowerBound_eval h (M.extent d ⊓ u)
    (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ d)
    (by
      intro τ v
      cases v with
      | vz =>
          exact inf_le_left
      | vs v =>
          exact le_trans inf_le_right (hρ (.var v)))
    t

theorem supportsRelativization
    {M : SemilocalModel Base Const} (h : StructuralExtent M) :
    SupportsRelativization M :=
  supportsRelativization_of_supportsLowerBoundExtension M
    (supportsLowerBoundExtension h)

theorem supportsUniformRelativization
    {M : SemilocalModel Base Const} (h : StructuralExtent M) :
    SupportsUniformRelativization M :=
  supportsUniformRelativization_of_supportsLowerBoundExtension M
    (supportsLowerBoundExtension h)

end StructuralExtent

theorem renameEnv_lift (M : SemilocalModel Base Const)
    (ρr : Rename Base Γ Δ) (ν : Env M Δ) (x : M.Carrier σ) :
    (renameEnv M (Rename.lift (Base := Base) (σ := σ) ρr)
        (ApplicativeStructure.Env.extend M.toApplicativeStructure ν x) :
      Env M (σ :: Γ)) =
      (ApplicativeStructure.Env.extend M.toApplicativeStructure (renameEnv M ρr ν) x :
        Env M (σ :: Γ)) := by
  funext τ v
  cases v <;> rfl

theorem eval_rename (M : SemilocalModel Base Const) :
    ∀ {Γ Δ : Ctx Base} {τ : Ty Base}
      (ρr : Rename Base Γ Δ) (t : Term Const Γ τ) (ν : Env M Δ),
      eval M ν (rename ρr t) = eval M (renameEnv M ρr ν) t
  | _, _, _, ρr, .var v, ν => rfl
  | _, _, _, ρr, .const c, ν => rfl
  | _, _, _, ρr, .app f t, ν => by
      simp [eval, rename, eval_rename M ρr f ν, eval_rename M ρr t ν]
  | _, _, _, ρr, .lam t, ν => by
      apply congrArg M.lam
      funext x
      change
        eval M (ApplicativeStructure.Env.extend M.toApplicativeStructure ν x)
            (rename (Rename.lift (Base := Base) (σ := _) ρr) t) =
          eval M
            (ApplicativeStructure.Env.extend M.toApplicativeStructure (renameEnv M ρr ν) x) t
      rw [eval_rename M (Rename.lift (Base := Base) (σ := _) ρr) t
        (ApplicativeStructure.Env.extend M.toApplicativeStructure ν x)]
      rw [renameEnv_lift M ρr ν x]
  | _, _, _, ρr, .top, ν => rfl
  | _, _, _, ρr, .bot, ν => rfl
  | _, _, _, ρr, .and φ ψ, ν => by
      simp [eval, rename, eval_rename M ρr φ ν, eval_rename M ρr ψ ν]
  | _, _, _, ρr, .or φ ψ, ν => by
      simp [eval, rename, eval_rename M ρr φ ν, eval_rename M ρr ψ ν]
  | _, _, _, ρr, .imp φ ψ, ν => by
      simp [eval, rename, eval_rename M ρr φ ν, eval_rename M ρr ψ ν]
  | _, _, _, ρr, .not φ, ν => by
      simp [eval, rename, eval_rename M ρr φ ν]
  | _, _, _, ρr, .eq t u, ν => by
      simp [eval, rename, eval_rename M ρr t ν, eval_rename M ρr u ν]
  | _, _, _, ρr, .all φ, ν => by
      apply congrArg M.allP
      funext x
      change
        eval M (ApplicativeStructure.Env.extend M.toApplicativeStructure ν x)
            (rename (Rename.lift (Base := Base) (σ := _) ρr) φ) =
          eval M
            (ApplicativeStructure.Env.extend M.toApplicativeStructure (renameEnv M ρr ν) x) φ
      rw [eval_rename M (Rename.lift (Base := Base) (σ := _) ρr) φ
        (ApplicativeStructure.Env.extend M.toApplicativeStructure ν x)]
      rw [renameEnv_lift M ρr ν x]
  | _, _, _, ρr, .ex φ, ν => by
      apply congrArg M.exP
      funext x
      change
        eval M (ApplicativeStructure.Env.extend M.toApplicativeStructure ν x)
            (rename (Rename.lift (Base := Base) (σ := _) ρr) φ) =
          eval M
            (ApplicativeStructure.Env.extend M.toApplicativeStructure (renameEnv M ρr ν) x) φ
      rw [eval_rename M (Rename.lift (Base := Base) (σ := _) ρr) φ
        (ApplicativeStructure.Env.extend M.toApplicativeStructure ν x)]
      rw [renameEnv_lift M ρr ν x]

@[simp] theorem eval_weaken (M : SemilocalModel Base Const)
    (ρ : Env M Γ) (x : M.Carrier σ) (t : Term Const Γ τ) :
    eval M (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x)
        (weaken (Base := Base) (Const := Const) (σ := σ) t) =
      eval M ρ t := by
  rw [weaken]
  rw [eval_rename]
  rfl

/-- Substitute denotations of a term substitution into an environment. -/
def substEnv (M : SemilocalModel Base Const)
    (σs : Subst Const Γ Δ) (ν : Env M Δ) : Env M Γ :=
  fun {_τ} v => eval M ν (σs v)

theorem substEnv_lift (M : SemilocalModel Base Const)
    (σs : Subst Const Γ Δ) (ν : Env M Δ) (x : M.Carrier σ) :
    (substEnv M (Subst.lift (Base := Base) (σ := σ) σs)
        (ApplicativeStructure.Env.extend M.toApplicativeStructure ν x) :
      Env M (σ :: Γ)) =
      (ApplicativeStructure.Env.extend M.toApplicativeStructure (substEnv M σs ν) x :
        Env M (σ :: Γ)) := by
  funext τ v
  cases v with
  | vz => rfl
  | vs v =>
      exact eval_weaken M ν x (σs v)

theorem eval_subst (M : SemilocalModel Base Const) :
    ∀ {Γ Δ : Ctx Base} {τ : Ty Base}
      (σs : Subst Const Γ Δ) (t : Term Const Γ τ) (ν : Env M Δ),
      eval M ν (subst σs t) = eval M (substEnv M σs ν) t
  | _, _, _, σs, .var v, ν => rfl
  | _, _, _, σs, .const c, ν => rfl
  | _, _, _, σs, .app f t, ν => by
      simp [eval, subst, eval_subst M σs f ν, eval_subst M σs t ν]
  | _, _, _, σs, .lam t, ν => by
      apply congrArg M.lam
      funext x
      change
        eval M (ApplicativeStructure.Env.extend M.toApplicativeStructure ν x)
            (subst (Subst.lift (Base := Base) (σ := _) σs) t) =
          eval M
            (ApplicativeStructure.Env.extend M.toApplicativeStructure (substEnv M σs ν) x) t
      rw [eval_subst M (Subst.lift (Base := Base) (σ := _) σs) t
        (ApplicativeStructure.Env.extend M.toApplicativeStructure ν x)]
      rw [substEnv_lift M σs ν x]
  | _, _, _, σs, .top, ν => rfl
  | _, _, _, σs, .bot, ν => rfl
  | _, _, _, σs, .and φ ψ, ν => by
      simp [eval, subst, eval_subst M σs φ ν, eval_subst M σs ψ ν]
  | _, _, _, σs, .or φ ψ, ν => by
      simp [eval, subst, eval_subst M σs φ ν, eval_subst M σs ψ ν]
  | _, _, _, σs, .imp φ ψ, ν => by
      simp [eval, subst, eval_subst M σs φ ν, eval_subst M σs ψ ν]
  | _, _, _, σs, .not φ, ν => by
      simp [eval, subst, eval_subst M σs φ ν]
  | _, _, _, σs, .eq t u, ν => by
      simp [eval, subst, eval_subst M σs t ν, eval_subst M σs u ν]
  | _, _, _, σs, .all φ, ν => by
      apply congrArg M.allP
      funext x
      change
        eval M (ApplicativeStructure.Env.extend M.toApplicativeStructure ν x)
            (subst (Subst.lift (Base := Base) (σ := _) σs) φ) =
          eval M
            (ApplicativeStructure.Env.extend M.toApplicativeStructure (substEnv M σs ν) x) φ
      rw [eval_subst M (Subst.lift (Base := Base) (σ := _) σs) φ
        (ApplicativeStructure.Env.extend M.toApplicativeStructure ν x)]
      rw [substEnv_lift M σs ν x]
  | _, _, _, σs, .ex φ, ν => by
      apply congrArg M.exP
      funext x
      change
        eval M (ApplicativeStructure.Env.extend M.toApplicativeStructure ν x)
            (subst (Subst.lift (Base := Base) (σ := _) σs) φ) =
          eval M
            (ApplicativeStructure.Env.extend M.toApplicativeStructure (substEnv M σs ν) x) φ
      rw [eval_subst M (Subst.lift (Base := Base) (σ := _) σs) φ
        (ApplicativeStructure.Env.extend M.toApplicativeStructure ν x)]
      rw [substEnv_lift M σs ν x]

@[simp] theorem eval_instantiate (M : SemilocalModel Base Const)
    (t : Term Const Γ σ) (u : Term Const (σ :: Γ) τ) (ρ : Env M Γ) :
    eval M ρ (instantiate (Base := Base) (Const := Const) t u) =
      eval M
        (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ (eval M ρ t))
        u := by
  have hsubst := eval_subst M
    (Subst.single (Base := Base) (Const := Const) t) u ρ
  have hsingle :
      (substEnv M (Subst.single (Base := Base) (Const := Const) t) ρ :
        Env M (σ :: Γ)) =
        (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ (eval M ρ t) :
          Env M (σ :: Γ)) := by
    funext τ v
    cases v <;> rfl
  rw [hsingle] at hsubst
  simpa [instantiate] using hsubst

@[simp] theorem formulaTruth_top (M : SemilocalModel Base Const) (ρ : Env M Γ) :
    formulaTruth M ρ (.top : Formula Const Γ) = ⊤ := by
  simp [formulaTruth, eval, M.truth_top]

@[simp] theorem formulaTruth_bot (M : SemilocalModel Base Const) (ρ : Env M Γ) :
    formulaTruth M ρ (.bot : Formula Const Γ) = ⊥ := by
  simp [formulaTruth, eval, M.truth_bot]

@[simp] theorem formulaTruth_and (M : SemilocalModel Base Const) (ρ : Env M Γ)
    (φ ψ : Formula Const Γ) :
    formulaTruth M ρ (.and φ ψ) = formulaTruth M ρ φ ⊓ formulaTruth M ρ ψ := by
  simp [formulaTruth, eval, M.truth_and]

@[simp] theorem formulaTruth_or (M : SemilocalModel Base Const) (ρ : Env M Γ)
    (φ ψ : Formula Const Γ) :
    formulaTruth M ρ (.or φ ψ) = formulaTruth M ρ φ ⊔ formulaTruth M ρ ψ := by
  simp [formulaTruth, eval, M.truth_or]

@[simp] theorem formulaTruth_imp (M : SemilocalModel Base Const) (ρ : Env M Γ)
    (φ ψ : Formula Const Γ) :
    formulaTruth M ρ (.imp φ ψ) = formulaTruth M ρ φ ⇨ formulaTruth M ρ ψ := by
  simp [formulaTruth, eval, M.truth_imp]

@[simp] theorem formulaTruth_not (M : SemilocalModel Base Const) (ρ : Env M Γ)
    (φ : Formula Const Γ) :
    formulaTruth M ρ (.not φ) = formulaTruth M ρ φ ⇨ ⊥ := by
  simp [formulaTruth, eval, M.truth_imp, M.truth_bot]

@[simp] theorem formulaTruth_all (M : SemilocalModel Base Const) (ρ : Env M Γ)
    {σ : Ty Base} (φ : Formula Const (σ :: Γ)) :
    formulaTruth M ρ (.all φ) =
      ⨅ x, M.extent x ⇨ formulaTruth M (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) φ := by
  simp [formulaTruth, eval, M.truth_all]

@[simp] theorem formulaTruth_ex (M : SemilocalModel Base Const) (ρ : Env M Γ)
    {σ : Ty Base} (φ : Formula Const (σ :: Γ)) :
    formulaTruth M ρ (.ex φ) =
      ⨆ x, M.extent x ⊓ formulaTruth M (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) φ := by
  simp [formulaTruth, eval, M.truth_ex]

@[simp] theorem formulaTruth_weaken (M : SemilocalModel Base Const)
    (ρ : Env M Γ) (x : M.Carrier σ) (φ : Formula Const Γ) :
    formulaTruth M (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x)
        (weaken (Base := Base) (Const := Const) (σ := σ) φ) =
      formulaTruth M ρ φ := by
  rw [formulaTruth, formulaTruth]
  congr 1
  exact eval_weaken M ρ x φ

@[simp] theorem formulaTruth_instantiate (M : SemilocalModel Base Const)
    (t : Term Const Γ σ) (φ : Formula Const (σ :: Γ)) (ρ : Env M Γ) :
    formulaTruth M ρ (instantiate (Base := Base) (Const := Const) t φ) =
      formulaTruth M
        (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ (eval M ρ t))
        φ := by
  rw [formulaTruth, formulaTruth]
  congr 1
  exact eval_instantiate M t φ ρ

@[simp] theorem antecedentTruth_weaken (M : SemilocalModel Base Const)
    (ρ : Env M Γ) (x : M.Carrier σ) (Δ : List (Formula Const Γ)) :
    antecedentTruth M
        (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x)
        (weakenAntecedents (Base := Base) (Const := Const) σ Δ) =
      antecedentTruth M ρ Δ := by
  induction Δ with
  | nil =>
      simp [weakenAntecedents, antecedentTruth]
  | cons φ Δ ih =>
      simp [weakenAntecedents, antecedentTruth]
      rw [show antecedentTruth M
          (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x)
          (List.map (weaken (Base := Base) (Const := Const) (σ := σ)) Δ) =
            antecedentTruth M ρ Δ by
              simpa [weakenAntecedents] using ih]

theorem eval_betaEtaEq (M : SemilocalModel Base Const) (ρ : Env M Γ) :
    {t u : Term Const Γ τ} →
      BetaEtaEq (Base := Base) (Const := Const) t u →
      eval M ρ t = eval M ρ u
  | _, _, .refl _ => rfl
  | _, _, .symm h => (eval_betaEtaEq M ρ h).symm
  | _, _, .trans h₁ h₂ => (eval_betaEtaEq M ρ h₁).trans (eval_betaEtaEq M ρ h₂)
  | _, _, .app hf ht => by
      simp [eval, eval_betaEtaEq M ρ hf, eval_betaEtaEq M ρ ht]
  | _, _, .lam h => by
      apply congrArg M.lam
      funext x
      exact eval_betaEtaEq M (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) h
  | _, _, .and hφ hψ => by
      simp [eval, eval_betaEtaEq M ρ hφ, eval_betaEtaEq M ρ hψ]
  | _, _, .or hφ hψ => by
      simp [eval, eval_betaEtaEq M ρ hφ, eval_betaEtaEq M ρ hψ]
  | _, _, .imp hφ hψ => by
      simp [eval, eval_betaEtaEq M ρ hφ, eval_betaEtaEq M ρ hψ]
  | _, _, .not hφ => by
      simp [eval, eval_betaEtaEq M ρ hφ]
  | _, _, .eq ht hu => by
      simp [eval, eval_betaEtaEq M ρ ht, eval_betaEtaEq M ρ hu]
  | _, _, .all hφ => by
      apply congrArg M.allP
      funext x
      exact eval_betaEtaEq M (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) hφ
  | _, _, .ex hφ => by
      apply congrArg M.exP
      funext x
      exact eval_betaEtaEq M (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) hφ
  | _, _, .beta t u => by
      calc
        eval M ρ (.app (.lam u) t) =
            eval M
              (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ (eval M ρ t))
              u := by
                simp [eval, M.beta]
        _ = eval M ρ (instantiate (Base := Base) (Const := Const) t u) := by
              symm
              exact eval_instantiate M t u ρ
  | _, _, .eta f => by
      calc
        eval M ρ (.lam (.app (weaken (Base := Base) (Const := Const) (σ := _) f) (.var .vz))) =
            M.lam (fun x => M.app (eval M ρ f) x) := by
              apply congrArg M.lam
              funext x
              simp [eval, eval_weaken]
        _ = eval M ρ f := by
              simpa [eval] using M.eta (eval M ρ f)

theorem formulaTruth_betaEtaEq (M : SemilocalModel Base Const)
    (ρ : Env M Γ) {φ ψ : Formula Const Γ}
    (h : BetaEtaEq (Base := Base) (Const := Const) φ ψ) :
    formulaTruth M ρ φ = formulaTruth M ρ ψ := by
  rw [formulaTruth, formulaTruth]
  congr 1
  exact eval_betaEtaEq M ρ h

theorem antecedentTruth_betaEtaEq (M : SemilocalModel Base Const)
    (ρ : Env M Γ) {Δ Δ' : List (Formula Const Γ)}
    (h : AntecedentsBetaEtaEq (Base := Base) (Const := Const) Δ Δ') :
    antecedentTruth M ρ Δ = antecedentTruth M ρ Δ' := by
  induction h with
  | nil => rfl
  | cons hφ hΔ ih =>
      simp [antecedentTruth, formulaTruth_betaEtaEq M ρ hφ, ih]

/-- Any antecedent list entails each member by projection. -/
theorem antecedentTruth_le_of_mem (M : SemilocalModel Base Const) (ρ : Env M Γ)
    {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} (h : φ ∈ Δ) :
    antecedentTruth M ρ Δ ≤ formulaTruth M ρ φ := by
  induction Δ with
  | nil => cases h
  | cons ψ Δ ih =>
      rw [List.mem_cons] at h
      simp [antecedentTruth]
      rcases h with rfl | h
      · exact inf_le_left
      · exact le_trans inf_le_right (ih h)

/-- If every antecedent is already true at the top world value, then the whole
antecedent meet is also top. -/
theorem antecedentTruth_eq_top_of_forall_mem (M : SemilocalModel Base Const)
    (ρ : Env M Γ) {Δ : List (Formula Const Γ)}
    (hΔ : ∀ {φ : Formula Const Γ}, φ ∈ Δ → formulaTruth M ρ φ = ⊤) :
    antecedentTruth M ρ Δ = ⊤ := by
  induction Δ with
  | nil =>
      simp [antecedentTruth]
  | cons φ Δ ih =>
      have hφ : formulaTruth M ρ φ = ⊤ := hΔ (by simp)
      have htail : antecedentTruth M ρ Δ = ⊤ := ih (by
        intro ψ hψ
        exact hΔ (by simp [hψ]))
      simp [antecedentTruth, hφ, htail]

end SemilocalModel

namespace GlobalModel

variable {Base : Type u} {Const : Ty Base → Type v}

abbrev Env (M : GlobalModel Base Const) (Γ : Ctx Base) :=
  SemilocalModel.Env M.toSemilocalModel Γ

abbrev eval (M : GlobalModel Base Const) (ρ : Env M Γ) (t : Term Const Γ τ) :=
  SemilocalModel.eval M.toSemilocalModel ρ t

abbrev formulaTruth (M : GlobalModel Base Const) (ρ : Env M Γ) (φ : Formula Const Γ) :=
  SemilocalModel.formulaTruth M.toSemilocalModel ρ φ

abbrev antecedentTruth (M : GlobalModel Base Const) (ρ : Env M Γ)
    (Δ : List (Formula Const Γ)) :=
  SemilocalModel.antecedentTruth M.toSemilocalModel ρ Δ

theorem isGlobalEnv (M : GlobalModel Base Const) (ρ : Env M Γ) :
    SemilocalModel.IsGlobalEnv M.toSemilocalModel ρ := by
  intro τ t
  rw [M.global]

theorem structuralExtent (M : GlobalModel Base Const) :
    SemilocalModel.StructuralExtent M.toSemilocalModel := by
  refine
    { const_top := ?_
      app_mono := ?_
      lam_top := ?_
      top_top := ?_
      bot_top := ?_
      and_top := ?_
      or_top := ?_
      imp_top := ?_
      eq_top := ?_
      all_top := ?_
      ex_top := ?_ }
  · intro τ c
    exact M.global (M.const c)
  · intro σ τ f x
    simp [M.global]
  · intro σ τ f
    exact M.global (M.lam f)
  · exact M.global M.topP
  · exact M.global M.botP
  · intro p q
    exact M.global (M.andP p q)
  · intro p q
    exact M.global (M.orP p q)
  · intro p q
    exact M.global (M.impP p q)
  · intro τ x y
    exact M.global (M.eqP x y)
  · intro σ f
    exact M.global (M.allP f)
  · intro σ f
    exact M.global (M.exP f)

theorem supportsLowerBoundExtension (M : GlobalModel Base Const) :
    SemilocalModel.SupportsLowerBoundExtension M.toSemilocalModel := by
  exact SemilocalModel.StructuralExtent.supportsLowerBoundExtension (structuralExtent M)

theorem supportsRelativization (M : GlobalModel Base Const) :
    SemilocalModel.SupportsRelativization M.toSemilocalModel := by
  exact SemilocalModel.StructuralExtent.supportsRelativization (structuralExtent M)

theorem supportsUniformRelativization (M : GlobalModel Base Const) :
    SemilocalModel.SupportsUniformRelativization M.toSemilocalModel := by
  exact SemilocalModel.StructuralExtent.supportsUniformRelativization (structuralExtent M)

end GlobalModel

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
