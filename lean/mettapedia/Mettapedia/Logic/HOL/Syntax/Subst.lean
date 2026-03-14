import Mettapedia.Logic.HOL.Syntax.Term

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Typed variable renamings. -/
abbrev Rename (Base : Type u) (Γ Δ : Ctx Base) := ∀ {τ}, Var Γ τ → Var Δ τ

/-- Typed substitutions. -/
abbrev Subst (Const : Ty Base → Type v) (Γ Δ : Ctx Base) := ∀ {τ}, Var Γ τ → Term Const Δ τ

namespace Rename

def id : Rename Base Γ Γ := fun v => v

def weaken : Rename Base Γ (σ :: Γ) := fun v => .vs v

def lift (ρ : Rename Base Γ Δ) : Rename Base (σ :: Γ) (σ :: Δ)
  | _, .vz => .vz
  | _, .vs v => .vs (ρ v)

@[simp] theorem lift_id_apply (v : Var (σ :: Γ) τ) :
    Rename.lift (Base := Base) (Γ := Γ) (Δ := Γ) (σ := σ)
      (Rename.id (Base := Base) (Γ := Γ)) v = v := by
  cases v <;> rfl

end Rename

/-- Rename variables in a term. -/
def rename (ρ : Rename Base Γ Δ) : Term Const Γ τ → Term Const Δ τ
  | .var v => .var (ρ v)
  | .const c => .const c
  | .app f t => .app (rename ρ f) (rename ρ t)
  | .lam t => .lam (rename (Rename.lift ρ) t)
  | .top => .top
  | .bot => .bot
  | .and φ ψ => .and (rename ρ φ) (rename ρ ψ)
  | .or φ ψ => .or (rename ρ φ) (rename ρ ψ)
  | .imp φ ψ => .imp (rename ρ φ) (rename ρ ψ)
  | .not φ => .not (rename ρ φ)
  | .eq t u => .eq (rename ρ t) (rename ρ u)
  | .all φ => .all (rename (Rename.lift ρ) φ)
  | .ex φ => .ex (rename (Rename.lift ρ) φ)

theorem rename_ext {ρ ρ' : Rename Base Γ Δ} (h : ∀ {τ}, (v : Var Γ τ) → ρ v = ρ' v)
    : (t : Term Const Γ τ) → rename ρ t = rename ρ' t
  | .var v => by
      simp [rename, h v]
  | .const _ => rfl
  | .app f t => by
      simp [rename, rename_ext h f, rename_ext h t]
  | .lam t => by
      apply congrArg Term.lam
      exact rename_ext
        (ρ := Rename.lift ρ)
        (ρ' := Rename.lift ρ')
        (fun v => by
          cases v with
          | vz => rfl
          | vs v => simp [Rename.lift, h v]) t
  | .top => rfl
  | .bot => rfl
  | .and φ ψ => by
      simp [rename, rename_ext h φ, rename_ext h ψ]
  | .or φ ψ => by
      simp [rename, rename_ext h φ, rename_ext h ψ]
  | .imp φ ψ => by
      simp [rename, rename_ext h φ, rename_ext h ψ]
  | .not φ => by
      simp [rename, rename_ext h φ]
  | .eq t u => by
      simp [rename, rename_ext h t, rename_ext h u]
  | .all φ => by
      apply congrArg Term.all
      exact rename_ext
        (ρ := Rename.lift ρ)
        (ρ' := Rename.lift ρ')
        (fun v => by
          cases v with
          | vz => rfl
          | vs v => simp [Rename.lift, h v]) φ
  | .ex φ => by
      apply congrArg Term.ex
      exact rename_ext
        (ρ := Rename.lift ρ)
        (ρ' := Rename.lift ρ')
        (fun v => by
          cases v with
          | vz => rfl
          | vs v => simp [Rename.lift, h v]) φ

namespace Subst

def id : Subst Const Γ Γ := fun v => .var v

def ofRename (ρ : Rename Base Γ Δ) : Subst Const Γ Δ :=
  fun v => .var (ρ v)

def lift (σs : Subst Const Γ Δ) : Subst Const (σ :: Γ) (σ :: Δ)
  | _, .vz => .var .vz
  | _, .vs v => rename (Rename.weaken (Base := Base) (Γ := Δ) (σ := σ)) (σs v)

def single (t : Term Const Γ σ) : Subst Const (σ :: Γ) Γ
  | _, .vz => t
  | _, .vs v => .var v

end Subst

/-- Substitute terms for variables. -/
def subst (σs : Subst Const Γ Δ) : Term Const Γ τ → Term Const Δ τ
  | .var v => σs v
  | .const c => .const c
  | .app f t => .app (subst σs f) (subst σs t)
  | .lam t => .lam (subst (Subst.lift (Base := Base) σs) t)
  | .top => .top
  | .bot => .bot
  | .and φ ψ => .and (subst σs φ) (subst σs ψ)
  | .or φ ψ => .or (subst σs φ) (subst σs ψ)
  | .imp φ ψ => .imp (subst σs φ) (subst σs ψ)
  | .not φ => .not (subst σs φ)
  | .eq t u => .eq (subst σs t) (subst σs u)
  | .all φ => .all (subst (Subst.lift (Base := Base) σs) φ)
  | .ex φ => .ex (subst (Subst.lift (Base := Base) σs) φ)

/-- Weaken a term by one variable. -/
def weaken (t : Term Const Γ τ) : Term Const (σ :: Γ) τ :=
  rename (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ)) t

/-- Instantiate the top bound variable with a term. -/
def instantiate (t : Term Const Γ σ) (u : Term Const (σ :: Γ) τ) : Term Const Γ τ :=
  subst (Subst.single t) u

theorem subst_ext {σs τs : Subst Const Γ Δ}
    (h : ∀ {τ}, (v : Var Γ τ) → σs v = τs v) :
    (t : Term Const Γ ρ) → subst σs t = subst τs t
  | .var v => by
      simp [subst, h v]
  | .const _ => rfl
  | .app f t => by
      simp [subst, subst_ext h f, subst_ext h t]
  | .lam t => by
      apply congrArg Term.lam
      exact subst_ext
        (σs := Subst.lift (Base := Base) σs)
        (τs := Subst.lift (Base := Base) τs)
        (fun v => by
          cases v with
          | vz => rfl
          | vs v => simp [Subst.lift, h v]) t
  | .top => rfl
  | .bot => rfl
  | .and φ ψ => by
      simp [subst, subst_ext h φ, subst_ext h ψ]
  | .or φ ψ => by
      simp [subst, subst_ext h φ, subst_ext h ψ]
  | .imp φ ψ => by
      simp [subst, subst_ext h φ, subst_ext h ψ]
  | .not φ => by
      simp [subst, subst_ext h φ]
  | .eq t u => by
      simp [subst, subst_ext h t, subst_ext h u]
  | .all φ => by
      apply congrArg Term.all
      exact subst_ext
        (σs := Subst.lift (Base := Base) σs)
        (τs := Subst.lift (Base := Base) τs)
        (fun v => by
          cases v with
          | vz => rfl
          | vs v => simp [Subst.lift, h v]) φ
  | .ex φ => by
      apply congrArg Term.ex
      exact subst_ext
        (σs := Subst.lift (Base := Base) σs)
        (τs := Subst.lift (Base := Base) τs)
        (fun v => by
          cases v with
          | vz => rfl
          | vs v => simp [Subst.lift, h v]) φ

@[simp] theorem rename_var (ρ : Rename Base Γ Δ) (v : Var Γ τ) :
    rename ρ (.var v : Term Const Γ τ) = .var (ρ v) := rfl

@[simp] theorem subst_var (σs : Subst Const Γ Δ) (v : Var Γ τ) :
    subst σs (.var v : Term Const Γ τ) = σs v := rfl

@[simp] theorem instantiate_var_vz (t : Term Const Γ σ) :
    instantiate t (.var (.vz : Var (σ :: Γ) σ)) = t := rfl

@[simp] theorem instantiate_var_vs (t : Term Const Γ σ) (v : Var Γ τ) :
    instantiate t (.var (.vs v) : Term Const (σ :: Γ) τ) = .var v := rfl

theorem rename_id (t : Term Const Γ τ) :
    rename (Rename.id (Base := Base) (Γ := Γ)) t = t := by
  induction t with
  | var v =>
      rfl
  | const c =>
      rfl
  | app f t hf ht =>
      simp [rename, hf, ht]
  | lam t ih =>
      apply congrArg Term.lam
      calc
        rename
            (Rename.lift (Base := Base) (Γ := _) (Δ := _) (σ := _)
              (Rename.id (Base := Base) (Γ := _))) t
            =
            rename (Rename.id (Base := Base) (Γ := _)) t := by
              apply rename_ext
              intro τ v
              exact Rename.lift_id_apply (Base := Base) (Γ := _) (σ := _) v
        _ = t := ih
  | top =>
      rfl
  | bot =>
      rfl
  | and φ ψ hφ hψ =>
      simp [rename, hφ, hψ]
  | or φ ψ hφ hψ =>
      simp [rename, hφ, hψ]
  | imp φ ψ hφ hψ =>
      simp [rename, hφ, hψ]
  | not φ hφ =>
      simp [rename, hφ]
  | eq t u ht hu =>
      simp [rename, ht, hu]
  | all φ ih =>
      apply congrArg Term.all
      calc
        rename
            (Rename.lift (Base := Base) (Γ := _) (Δ := _) (σ := _)
              (Rename.id (Base := Base) (Γ := _))) φ
            =
            rename (Rename.id (Base := Base) (Γ := _)) φ := by
              apply rename_ext
              intro τ v
              exact Rename.lift_id_apply (Base := Base) (Γ := _) (σ := _) v
        _ = φ := ih
  | ex φ ih =>
      apply congrArg Term.ex
      calc
        rename
            (Rename.lift (Base := Base) (Γ := _) (Δ := _) (σ := _)
              (Rename.id (Base := Base) (Γ := _))) φ
            =
            rename (Rename.id (Base := Base) (Γ := _)) φ := by
              apply rename_ext
              intro τ v
              exact Rename.lift_id_apply (Base := Base) (Γ := _) (σ := _) v
        _ = φ := ih

end Mettapedia.Logic.HOL
