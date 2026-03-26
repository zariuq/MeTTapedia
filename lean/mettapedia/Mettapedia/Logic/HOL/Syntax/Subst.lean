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

namespace Subst

/-- Compose substitutions right-to-left: first `σs`, then `τs`. -/
def comp (τs : Subst Const Δ Ξ) (σs : Subst Const Γ Δ) : Subst Const Γ Ξ :=
  fun v => subst τs (σs v)

end Subst

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

@[simp] theorem rename_comp (ρ₂ : Rename Base Δ Ξ) (ρ₁ : Rename Base Γ Δ)
    (t : Term Const Γ τ) :
    rename ρ₂ (rename ρ₁ t) = rename (fun {_τ} v => ρ₂ (ρ₁ v)) t := by
  induction t generalizing Δ Ξ with
  | var v =>
      rfl
  | const c =>
      rfl
  | app f t hf ht =>
      simp [rename, hf (ρ₂ := ρ₂) (ρ₁ := ρ₁), ht (ρ₂ := ρ₂) (ρ₁ := ρ₁)]
  | lam t ih =>
      apply congrArg Term.lam
      calc
        rename
            (Rename.lift (Base := Base) (σ := _) ρ₂)
            (rename (Rename.lift (Base := Base) (σ := _) ρ₁) t)
            =
            rename
              (fun {τ} v =>
                Rename.lift (Base := Base) (σ := _) ρ₂
                  (Rename.lift (Base := Base) (σ := _) ρ₁ v)) t := by
                    exact ih
                      (ρ₂ := Rename.lift (Base := Base) (σ := _) ρ₂)
                      (ρ₁ := Rename.lift (Base := Base) (σ := _) ρ₁)
        _ =
            rename
              (Rename.lift (Base := Base) (σ := _)
                (fun {τ} v => ρ₂ (ρ₁ v))) t := by
                  apply rename_ext
                  intro τ v
                  cases v <;> rfl
  | top =>
      rfl
  | bot =>
      rfl
  | and φ ψ hφ hψ =>
      simp [rename, hφ (ρ₂ := ρ₂) (ρ₁ := ρ₁), hψ (ρ₂ := ρ₂) (ρ₁ := ρ₁)]
  | or φ ψ hφ hψ =>
      simp [rename, hφ (ρ₂ := ρ₂) (ρ₁ := ρ₁), hψ (ρ₂ := ρ₂) (ρ₁ := ρ₁)]
  | imp φ ψ hφ hψ =>
      simp [rename, hφ (ρ₂ := ρ₂) (ρ₁ := ρ₁), hψ (ρ₂ := ρ₂) (ρ₁ := ρ₁)]
  | not φ hφ =>
      simp [rename, hφ (ρ₂ := ρ₂) (ρ₁ := ρ₁)]
  | eq t u ht hu =>
      simp [rename, ht (ρ₂ := ρ₂) (ρ₁ := ρ₁), hu (ρ₂ := ρ₂) (ρ₁ := ρ₁)]
  | all φ hφ =>
      apply congrArg Term.all
      calc
        rename
            (Rename.lift (Base := Base) (σ := _) ρ₂)
            (rename (Rename.lift (Base := Base) (σ := _) ρ₁) φ)
            =
            rename
              (fun {τ} v =>
                Rename.lift (Base := Base) (σ := _) ρ₂
                  (Rename.lift (Base := Base) (σ := _) ρ₁ v)) φ := by
                    exact hφ
                      (ρ₂ := Rename.lift (Base := Base) (σ := _) ρ₂)
                      (ρ₁ := Rename.lift (Base := Base) (σ := _) ρ₁)
        _ =
            rename
              (Rename.lift (Base := Base) (σ := _)
                (fun {τ} v => ρ₂ (ρ₁ v))) φ := by
                  apply rename_ext
                  intro τ v
                  cases v <;> rfl
  | ex φ hφ =>
      apply congrArg Term.ex
      calc
        rename
            (Rename.lift (Base := Base) (σ := _) ρ₂)
            (rename (Rename.lift (Base := Base) (σ := _) ρ₁) φ)
            =
            rename
              (fun {τ} v =>
                Rename.lift (Base := Base) (σ := _) ρ₂
                  (Rename.lift (Base := Base) (σ := _) ρ₁ v)) φ := by
                    exact hφ
                      (ρ₂ := Rename.lift (Base := Base) (σ := _) ρ₂)
                      (ρ₁ := Rename.lift (Base := Base) (σ := _) ρ₁)
        _ =
            rename
              (Rename.lift (Base := Base) (σ := _)
                (fun {τ} v => ρ₂ (ρ₁ v))) φ := by
                  apply rename_ext
                  intro τ v
                  cases v <;> rfl

@[simp] theorem rename_lift_apply (ρ : Rename Base Δ Ξ) (σs : Subst Const Γ Δ)
    (v : Var (σ :: Γ) τ) :
    rename (Rename.lift (Base := Base) (σ := σ) ρ)
        ((Subst.lift (Base := Base) (σ := σ) σs) v) =
      (Subst.lift (Base := Base) (Const := Const) (σ := σ)
        (fun {_τ} v => rename ρ (σs v))) v := by
  cases v with
  | vz =>
      rfl
  | vs v =>
      calc
        rename (Rename.lift (Base := Base) (σ := σ) ρ)
            ((Subst.lift (Base := Base) (σ := σ) σs) (.vs v))
            =
            rename
              (Rename.lift (Base := Base) (σ := σ) ρ)
              (rename (Rename.weaken (Base := Base) (Γ := Δ) (σ := σ)) (σs v)) := by
                rfl
        _ =
            rename
              (fun {τ} x =>
                Rename.lift (Base := Base) (σ := σ) ρ
                  (Rename.weaken (Base := Base) (Γ := Δ) (σ := σ) x))
              (σs v) := by
                simp [rename_comp]
        _ =
            rename
              (fun {τ} x =>
                Rename.weaken (Base := Base) (Γ := Ξ) (σ := σ) (ρ x))
              (σs v) := by
                apply rename_ext
                intro τ x
                simp [Rename.lift, Rename.weaken]
        _ =
            rename (Rename.weaken (Base := Base) (Γ := Ξ) (σ := σ))
              (rename ρ (σs v)) := by
                simp [rename_comp]
        _ = (Subst.lift (Base := Base) (Const := Const) (σ := σ)
              (fun {τ} v => rename ρ (σs v))) (.vs v) := by
                rfl

theorem rename_subst (ρ : Rename Base Δ Ξ) (σs : Subst Const Γ Δ)
    (t : Term Const Γ τ) :
    rename ρ (subst σs t) = subst (fun {_τ} v => rename ρ (σs v)) t := by
  induction t generalizing Δ Ξ with
  | var v =>
      rfl
  | const c =>
      rfl
  | app f t hf ht =>
      simp [rename, subst, hf (ρ := ρ) (σs := σs), ht (ρ := ρ) (σs := σs)]
  | lam t ih =>
      apply congrArg Term.lam
      calc
        rename
            (Rename.lift (Base := Base) (σ := _) ρ)
            (subst (Subst.lift (Base := Base) (σ := _) σs) t)
            =
            subst
              (fun {τ} v =>
                rename (Rename.lift (Base := Base) (σ := _) ρ)
                  ((Subst.lift (Base := Base) (σ := _) σs) v))
              t := by
                exact ih
                  (ρ := Rename.lift (Base := Base) (σ := _) ρ)
                  (σs := Subst.lift (Base := Base) (σ := _) σs)
        _ =
            subst
              (Subst.lift (Base := Base) (Const := Const) (σ := _)
                (fun {τ} v => rename ρ (σs v))) t := by
                  apply subst_ext
                  intro τ v
                  exact rename_lift_apply (Base := Base) (Const := Const) (σ := _) ρ σs v
  | top =>
      rfl
  | bot =>
      rfl
  | and φ ψ hφ hψ =>
      simp [rename, subst, hφ (ρ := ρ) (σs := σs), hψ (ρ := ρ) (σs := σs)]
  | or φ ψ hφ hψ =>
      simp [rename, subst, hφ (ρ := ρ) (σs := σs), hψ (ρ := ρ) (σs := σs)]
  | imp φ ψ hφ hψ =>
      simp [rename, subst, hφ (ρ := ρ) (σs := σs), hψ (ρ := ρ) (σs := σs)]
  | not φ hφ =>
      simp [rename, subst, hφ (ρ := ρ) (σs := σs)]
  | eq t u ht hu =>
      simp [rename, subst, ht (ρ := ρ) (σs := σs), hu (ρ := ρ) (σs := σs)]
  | all φ hφ =>
      apply congrArg Term.all
      calc
        rename
            (Rename.lift (Base := Base) (σ := _) ρ)
            (subst (Subst.lift (Base := Base) (σ := _) σs) φ)
            =
            subst
              (fun {τ} v =>
                rename (Rename.lift (Base := Base) (σ := _) ρ)
                  ((Subst.lift (Base := Base) (σ := _) σs) v))
              φ := by
                exact hφ
                  (ρ := Rename.lift (Base := Base) (σ := _) ρ)
                  (σs := Subst.lift (Base := Base) (σ := _) σs)
        _ =
            subst
              (Subst.lift (Base := Base) (Const := Const) (σ := _)
                (fun {τ} v => rename ρ (σs v))) φ := by
                  apply subst_ext
                  intro τ v
                  exact rename_lift_apply (Base := Base) (Const := Const) (σ := _) ρ σs v
  | ex φ hφ =>
      apply congrArg Term.ex
      calc
        rename
            (Rename.lift (Base := Base) (σ := _) ρ)
            (subst (Subst.lift (Base := Base) (σ := _) σs) φ)
            =
            subst
              (fun {τ} v =>
                rename (Rename.lift (Base := Base) (σ := _) ρ)
                  ((Subst.lift (Base := Base) (σ := _) σs) v))
              φ := by
                exact hφ
                  (ρ := Rename.lift (Base := Base) (σ := _) ρ)
                  (σs := Subst.lift (Base := Base) (σ := _) σs)
        _ =
            subst
              (Subst.lift (Base := Base) (Const := Const) (σ := _)
                (fun {τ} v => rename ρ (σs v))) φ := by
                  apply subst_ext
                  intro τ v
                  exact rename_lift_apply (Base := Base) (Const := Const) (σ := _) ρ σs v

@[simp] theorem Subst.lift_rename_apply (σs : Subst Const Δ Ξ) (ρ : Rename Base Γ Δ)
    (v : Var (σ :: Γ) τ) :
    (Subst.lift (Base := Base) (σ := σ) σs)
        (Rename.lift (Base := Base) (σ := σ) ρ v) =
      (Subst.lift (Base := Base) (Const := Const) (σ := σ)
        (fun {_τ} v => σs (ρ v))) v := by
  cases v with
  | vz =>
      rfl
  | vs v =>
      rfl

theorem subst_rename (σs : Subst Const Δ Ξ) (ρ : Rename Base Γ Δ)
    (t : Term Const Γ τ) :
    subst σs (rename ρ t) = subst (fun {_τ} v => σs (ρ v)) t := by
  induction t generalizing Δ Ξ with
  | var v =>
      rfl
  | const c =>
      rfl
  | app f t hf ht =>
      simp [subst, rename, hf (σs := σs) (ρ := ρ), ht (σs := σs) (ρ := ρ)]
  | lam t ih =>
      apply congrArg Term.lam
      calc
        subst (Subst.lift (Base := Base) (σ := _) σs)
            (rename (Rename.lift (Base := Base) (σ := _) ρ) t)
            =
            subst
              (fun {τ} v =>
                (Subst.lift (Base := Base) (σ := _) σs)
                  (Rename.lift (Base := Base) (σ := _) ρ v))
              t := by
                exact ih
                  (σs := Subst.lift (Base := Base) (σ := _) σs)
                  (ρ := Rename.lift (Base := Base) (σ := _) ρ)
        _ =
            subst
              (Subst.lift (Base := Base) (Const := Const) (σ := _)
                (fun {τ} v => σs (ρ v))) t := by
                  apply subst_ext
                  intro τ v
                  exact Subst.lift_rename_apply (Base := Base) (Const := Const) (σ := _) σs ρ v
  | top =>
      rfl
  | bot =>
      rfl
  | and φ ψ hφ hψ =>
      simp [subst, rename, hφ (σs := σs) (ρ := ρ), hψ (σs := σs) (ρ := ρ)]
  | or φ ψ hφ hψ =>
      simp [subst, rename, hφ (σs := σs) (ρ := ρ), hψ (σs := σs) (ρ := ρ)]
  | imp φ ψ hφ hψ =>
      simp [subst, rename, hφ (σs := σs) (ρ := ρ), hψ (σs := σs) (ρ := ρ)]
  | not φ hφ =>
      simp [subst, rename, hφ (σs := σs) (ρ := ρ)]
  | eq t u ht hu =>
      simp [subst, rename, ht (σs := σs) (ρ := ρ), hu (σs := σs) (ρ := ρ)]
  | all φ hφ =>
      apply congrArg Term.all
      calc
        subst (Subst.lift (Base := Base) (σ := _) σs)
            (rename (Rename.lift (Base := Base) (σ := _) ρ) φ)
            =
            subst
              (fun {τ} v =>
                (Subst.lift (Base := Base) (σ := _) σs)
                  (Rename.lift (Base := Base) (σ := _) ρ v))
              φ := by
                exact hφ
                  (σs := Subst.lift (Base := Base) (σ := _) σs)
                  (ρ := Rename.lift (Base := Base) (σ := _) ρ)
        _ =
            subst
              (Subst.lift (Base := Base) (Const := Const) (σ := _)
                (fun {τ} v => σs (ρ v))) φ := by
                  apply subst_ext
                  intro τ v
                  exact Subst.lift_rename_apply (Base := Base) (Const := Const) (σ := _) σs ρ v
  | ex φ hφ =>
      apply congrArg Term.ex
      calc
        subst (Subst.lift (Base := Base) (σ := _) σs)
            (rename (Rename.lift (Base := Base) (σ := _) ρ) φ)
            =
            subst
              (fun {τ} v =>
                (Subst.lift (Base := Base) (σ := _) σs)
                  (Rename.lift (Base := Base) (σ := _) ρ v))
              φ := by
                exact hφ
                  (σs := Subst.lift (Base := Base) (σ := _) σs)
                  (ρ := Rename.lift (Base := Base) (σ := _) ρ)
        _ =
            subst
              (Subst.lift (Base := Base) (Const := Const) (σ := _)
                (fun {τ} v => σs (ρ v))) φ := by
                  apply subst_ext
                  intro τ v
                  exact Subst.lift_rename_apply (Base := Base) (Const := Const) (σ := _) σs ρ v

@[simp] theorem subst_weaken (σs : Subst Const Γ Δ) (t : Term Const Γ τ) :
    subst (Subst.lift (Base := Base) (σ := σ) σs)
        (weaken (Base := Base) (σ := σ) t) =
      weaken (Base := Base) (σ := σ) (subst σs t) := by
  calc
    subst (Subst.lift (Base := Base) (σ := σ) σs)
        (weaken (Base := Base) (σ := σ) t)
        =
        subst
          (fun {τ} v =>
            (Subst.lift (Base := Base) (σ := σ) σs)
              (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ) v))
          t := by
            simpa [weaken] using
              (subst_rename (Base := Base) (Const := Const)
                (σs := Subst.lift (Base := Base) (σ := σ) σs)
                (ρ := Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))
                (t := t))
    _ =
        subst
          (fun {τ} v =>
            weaken (Base := Base) (Const := Const) (σ := σ) (σs v))
          t := by
            rfl
    _ =
        rename (Rename.weaken (Base := Base) (Γ := Δ) (σ := σ)) (subst σs t) := by
          symm
          simpa [weaken] using
            (rename_subst (Base := Base) (Const := Const)
              (ρ := Rename.weaken (Base := Base) (Γ := Δ) (σ := σ))
              (σs := σs) (t := t))
    _ = weaken (Base := Base) (σ := σ) (subst σs t) := by
          rfl

@[simp] theorem Subst.comp_apply (τs : Subst Const Δ Ξ) (σs : Subst Const Γ Δ)
    (v : Var Γ τ) :
    Subst.comp τs σs v = subst τs (σs v) := rfl

@[simp] theorem Subst.lift_comp_apply (τs : Subst Const Δ Ξ) (σs : Subst Const Γ Δ)
    (v : Var (σ :: Γ) τ) :
    Subst.lift (Base := Base) (σ := σ) (Subst.comp τs σs) v =
      Subst.comp
        (Subst.lift (Base := Base) (σ := σ) τs)
        (Subst.lift (Base := Base) (σ := σ) σs) v := by
  cases v with
  | vz =>
      rfl
  | vs v =>
      simpa [Subst.comp, weaken] using
        (subst_weaken (Base := Base) (Const := Const) (σ := σ) (σs := τs) (t := σs v)).symm

theorem subst_comp (τs : Subst Const Δ Ξ) (σs : Subst Const Γ Δ)
    (t : Term Const Γ ρ) :
    subst τs (subst σs t) = subst (Subst.comp τs σs) t := by
  induction t generalizing Δ Ξ with
  | var v =>
      simp [Subst.comp]
  | const c =>
      rfl
  | app f t hf ht =>
      simp [subst, hf, ht]
  | lam t ih =>
      apply congrArg Term.lam
      calc
        subst (Subst.lift (Base := Base) (σ := _) τs)
            (subst (Subst.lift (Base := Base) (σ := _) σs) t)
            =
            subst
              (Subst.comp
                (Subst.lift (Base := Base) (σ := _) τs)
                (Subst.lift (Base := Base) (σ := _) σs)) t := by
                  exact ih (Subst.lift (Base := Base) τs) (Subst.lift (Base := Base) σs)
        _ =
            subst (Subst.lift (Base := Base) (σ := _) (Subst.comp τs σs)) t := by
              apply subst_ext
              intro τ v
              symm
              exact Subst.lift_comp_apply (Base := Base) (Const := Const) (σ := _) τs σs v
  | top =>
      rfl
  | bot =>
      rfl
  | and φ ψ hφ hψ =>
      simp [subst, hφ, hψ]
  | or φ ψ hφ hψ =>
      simp [subst, hφ, hψ]
  | imp φ ψ hφ hψ =>
      simp [subst, hφ, hψ]
  | not φ hφ =>
      simp [subst, hφ]
  | eq t u ht hu =>
      simp [subst, ht, hu]
  | all φ hφ =>
      apply congrArg Term.all
      calc
        subst (Subst.lift (Base := Base) (σ := _) τs)
            (subst (Subst.lift (Base := Base) (σ := _) σs) φ)
            =
            subst
              (Subst.comp
                (Subst.lift (Base := Base) (σ := _) τs)
                (Subst.lift (Base := Base) (σ := _) σs)) φ := by
                  exact hφ (Subst.lift (Base := Base) τs) (Subst.lift (Base := Base) σs)
        _ =
            subst (Subst.lift (Base := Base) (σ := _) (Subst.comp τs σs)) φ := by
              apply subst_ext
              intro τ v
              symm
              exact Subst.lift_comp_apply (Base := Base) (Const := Const) (σ := _) τs σs v
  | ex φ hφ =>
      apply congrArg Term.ex
      calc
        subst (Subst.lift (Base := Base) (σ := _) τs)
            (subst (Subst.lift (Base := Base) (σ := _) σs) φ)
            =
            subst
              (Subst.comp
                (Subst.lift (Base := Base) (σ := _) τs)
                (Subst.lift (Base := Base) (σ := _) σs)) φ := by
                  exact hφ (Subst.lift (Base := Base) τs) (Subst.lift (Base := Base) σs)
        _ =
            subst (Subst.lift (Base := Base) (σ := _) (Subst.comp τs σs)) φ := by
              apply subst_ext
              intro τ v
              symm
              exact Subst.lift_comp_apply (Base := Base) (Const := Const) (σ := _) τs σs v

theorem subst_id (t : Term Const Γ τ) :
    subst (Subst.id (Base := Base) (Const := Const) (Γ := Γ)) t = t := by
  induction t with
  | var v =>
      rfl
  | const c =>
      rfl
  | app f t hf ht =>
      simp [subst, hf, ht]
  | lam t ih =>
      apply congrArg Term.lam
      calc
        subst
            (Subst.lift (Base := Base) (σ := _)
              (Subst.id (Base := Base) (Const := Const) (Γ := _))) t
            =
            subst (Subst.id (Base := Base) (Const := Const) (Γ := _)) t := by
              apply subst_ext
              intro τ v
              cases v <;> rfl
        _ = t := ih
  | top =>
      rfl
  | bot =>
      rfl
  | and φ ψ hφ hψ =>
      simp [subst, hφ, hψ]
  | or φ ψ hφ hψ =>
      simp [subst, hφ, hψ]
  | imp φ ψ hφ hψ =>
      simp [subst, hφ, hψ]
  | not φ hφ =>
      simp [subst, hφ]
  | eq t u ht hu =>
      simp [subst, ht, hu]
  | all φ hφ =>
      apply congrArg Term.all
      calc
        subst
            (Subst.lift (Base := Base) (σ := _)
              (Subst.id (Base := Base) (Const := Const) (Γ := _))) φ
            =
            subst (Subst.id (Base := Base) (Const := Const) (Γ := _)) φ := by
              apply subst_ext
              intro τ v
              cases v <;> rfl
        _ = φ := hφ
  | ex φ hφ =>
      apply congrArg Term.ex
      calc
        subst
            (Subst.lift (Base := Base) (σ := _)
              (Subst.id (Base := Base) (Const := Const) (Γ := _))) φ
            =
            subst (Subst.id (Base := Base) (Const := Const) (Γ := _)) φ := by
              apply subst_ext
              intro τ v
              cases v <;> rfl
        _ = φ := hφ

@[simp] theorem instantiate_weaken
    (t : Term Const Γ σ) (u : Term Const Γ τ) :
    instantiate (Base := Base) t (weaken (Base := Base) (Γ := Γ) (σ := σ) u) = u := by
  unfold instantiate weaken
  calc
    subst
        (Subst.single (Base := Base) (Const := Const) t)
        (rename (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ)) u)
        =
        subst
          (fun {τ} v =>
            (Subst.single (Base := Base) (Const := Const) t)
              (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ) v))
          u := by
            simpa using
              (subst_rename (Base := Base) (Const := Const)
                (σs := Subst.single (Base := Base) (Const := Const) t)
                (ρ := Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))
                (t := u))
    _ =
        subst (Subst.id (Base := Base) (Const := Const) (Γ := Γ)) u := by
          apply subst_ext
          intro τ v
          rfl
    _ = u := subst_id (Base := Base) (Const := Const) u

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

/-- A constant `c` does not occur in term `t`. -/
inductive NoConstOccurrence (c : Const σ) : Term Const Γ τ → Prop where
  | var : NoConstOccurrence c (.var v)
  | const_diff_type {ρ : Ty Base} (hne : σ ≠ ρ) (d : Const ρ) : NoConstOccurrence c (.const d)
  | const_same_ne (d : Const σ) (hne : d ≠ c) : NoConstOccurrence c (.const d)
  | app : NoConstOccurrence c f → NoConstOccurrence c t → NoConstOccurrence c (.app f t)
  | lam : NoConstOccurrence c t → NoConstOccurrence c (.lam t)
  | top : NoConstOccurrence c .top
  | bot : NoConstOccurrence c .bot
  | and : NoConstOccurrence c φ → NoConstOccurrence c ψ → NoConstOccurrence c (.and φ ψ)
  | or : NoConstOccurrence c φ → NoConstOccurrence c ψ → NoConstOccurrence c (.or φ ψ)
  | imp : NoConstOccurrence c φ → NoConstOccurrence c ψ → NoConstOccurrence c (.imp φ ψ)
  | not : NoConstOccurrence c φ → NoConstOccurrence c (.not φ)
  | eq : NoConstOccurrence c t → NoConstOccurrence c u → NoConstOccurrence c (.eq t u)
  | all : NoConstOccurrence c φ → NoConstOccurrence c (.all φ)
  | ex : NoConstOccurrence c φ → NoConstOccurrence c (.ex φ)

/-- NoConstOccurrence is preserved backward through renaming:
    if `c` doesn't occur in `rename ρ t`, then `c` doesn't occur in `t`. -/
theorem noConstOccurrence_of_rename
    {c : Const σ} (ρ : Rename Base Γ Δ) :
    ∀ {τ : Ty Base} (t : Term Const Γ τ),
      NoConstOccurrence c (rename ρ t) → NoConstOccurrence c t
  | _, .var _, _ => .var
  | _, .const _, h => by
      cases h with
      | const_diff_type hne => exact .const_diff_type hne _
      | const_same_ne d hne => exact .const_same_ne d hne
  | _, .app f t, h => by
      cases h with
      | app hf ht =>
          exact .app (noConstOccurrence_of_rename ρ f hf)
            (noConstOccurrence_of_rename ρ t ht)
  | _, .lam body, h => by
      cases h with
      | lam hb => exact .lam (noConstOccurrence_of_rename (Rename.lift ρ) body hb)
  | _, .top, _ => .top
  | _, .bot, _ => .bot
  | _, .and φ ψ, h => by
      cases h with
      | and h1 h2 =>
          exact .and (noConstOccurrence_of_rename ρ φ h1)
            (noConstOccurrence_of_rename ρ ψ h2)
  | _, .or φ ψ, h => by
      cases h with
      | or h1 h2 =>
          exact .or (noConstOccurrence_of_rename ρ φ h1)
            (noConstOccurrence_of_rename ρ ψ h2)
  | _, .imp φ ψ, h => by
      cases h with
      | imp h1 h2 =>
          exact .imp (noConstOccurrence_of_rename ρ φ h1)
            (noConstOccurrence_of_rename ρ ψ h2)
  | _, .not φ, h => by
      cases h with
      | not h1 => exact .not (noConstOccurrence_of_rename ρ φ h1)
  | _, .eq t u, h => by
      cases h with
      | eq h1 h2 =>
          exact .eq (noConstOccurrence_of_rename ρ t h1)
            (noConstOccurrence_of_rename ρ u h2)
  | _, .all φ, h => by
      cases h with
      | all hb => exact .all (noConstOccurrence_of_rename (Rename.lift ρ) φ hb)
  | _, .ex φ, h => by
      cases h with
      | ex hb => exact .ex (noConstOccurrence_of_rename (Rename.lift ρ) φ hb)

/-- NoConstOccurrence is preserved forward through renaming. -/
theorem noConstOccurrence_rename
    {σ : Ty Base} {c : Const σ} {Γ' Δ' : Ctx Base} (ρ : Rename Base Γ' Δ') :
    ∀ {τ : Ty Base} (t : Term Const Γ' τ),
      NoConstOccurrence c t → NoConstOccurrence c (rename ρ t)
  | _, .var _, _ => .var
  | _, .const _, h => by
      cases h with
      | const_diff_type hne => exact .const_diff_type hne _
      | const_same_ne _ hne => exact .const_same_ne _ hne
  | _, .app f' t', h => by cases h with | app hf ht =>
      exact .app (noConstOccurrence_rename ρ f' hf) (noConstOccurrence_rename ρ t' ht)
  | _, .lam body, h => by cases h with | lam hb =>
      exact .lam (noConstOccurrence_rename (Rename.lift ρ) body hb)
  | _, .top, _ => .top
  | _, .bot, _ => .bot
  | _, .and φ' ψ', h => by cases h with | and h1 h2 =>
      exact .and (noConstOccurrence_rename ρ φ' h1) (noConstOccurrence_rename ρ ψ' h2)
  | _, .or φ' ψ', h => by cases h with | or h1 h2 =>
      exact .or (noConstOccurrence_rename ρ φ' h1) (noConstOccurrence_rename ρ ψ' h2)
  | _, .imp φ' ψ', h => by cases h with | imp h1 h2 =>
      exact .imp (noConstOccurrence_rename ρ φ' h1) (noConstOccurrence_rename ρ ψ' h2)
  | _, .not φ', h => by cases h with | not h1 =>
      exact .not (noConstOccurrence_rename ρ φ' h1)
  | _, .eq t' u', h => by cases h with | eq h1 h2 =>
      exact .eq (noConstOccurrence_rename ρ t' h1) (noConstOccurrence_rename ρ u' h2)
  | _, .all φ', h => by cases h with | all hb =>
      exact .all (noConstOccurrence_rename (Rename.lift ρ) φ' hb)
  | _, .ex φ', h => by cases h with | ex hb =>
      exact .ex (noConstOccurrence_rename (Rename.lift ρ) φ' hb)

/-- NoConstOccurrence through substitution: if `c` doesn't occur in any image of `s`
    and doesn't occur in `t`, then it doesn't occur in `subst s t`. -/
theorem noConstOccurrence_subst
    {σ : Ty Base} {c : Const σ} {Γ' Δ' : Ctx Base}
    {s : ∀ {τ : Ty Base}, Var Δ' τ → Term Const Γ' τ}
    (hs : ∀ {τ} (v : Var Δ' τ), NoConstOccurrence c (s v)) :
    ∀ {τ : Ty Base} (t : Term Const Δ' τ),
      NoConstOccurrence c t → NoConstOccurrence c (subst s t)
  | _, .var v, _ => hs v
  | _, .const _, h => by
      cases h with
      | const_diff_type hne => exact .const_diff_type hne _
      | const_same_ne _ hne => exact .const_same_ne _ hne
  | _, .app f' t', h => by cases h with | app hf ht =>
      exact .app (noConstOccurrence_subst hs f' hf) (noConstOccurrence_subst hs t' ht)
  | _, .lam body, h => by cases h with | lam hb =>
      exact .lam (noConstOccurrence_subst
        (fun v => by cases v with
          | vz => exact .var
          | vs v => exact noConstOccurrence_rename Rename.weaken _ (hs v))
        body hb)
  | _, .top, _ => .top
  | _, .bot, _ => .bot
  | _, .and φ' ψ', h => by cases h with | and h1 h2 =>
      exact .and (noConstOccurrence_subst hs φ' h1) (noConstOccurrence_subst hs ψ' h2)
  | _, .or φ' ψ', h => by cases h with | or h1 h2 =>
      exact .or (noConstOccurrence_subst hs φ' h1) (noConstOccurrence_subst hs ψ' h2)
  | _, .imp φ' ψ', h => by cases h with | imp h1 h2 =>
      exact .imp (noConstOccurrence_subst hs φ' h1) (noConstOccurrence_subst hs ψ' h2)
  | _, .not φ', h => by cases h with | not h1 =>
      exact .not (noConstOccurrence_subst hs φ' h1)
  | _, .eq t' u', h => by cases h with | eq h1 h2 =>
      exact .eq (noConstOccurrence_subst hs t' h1) (noConstOccurrence_subst hs u' h2)
  | _, .all φ', h => by cases h with | all hb =>
      exact .all (noConstOccurrence_subst
        (fun v => by cases v with
          | vz => exact .var
          | vs v => exact noConstOccurrence_rename Rename.weaken _ (hs v))
        φ' hb)
  | _, .ex φ', h => by cases h with | ex hb =>
      exact .ex (noConstOccurrence_subst
        (fun v => by cases v with
          | vz => exact .var
          | vs v => exact noConstOccurrence_rename Rename.weaken _ (hs v))
        φ' hb)

/-- Specialization: NoConstOccurrence through instantiation. -/
theorem noConstOccurrence_instantiate
    {σ σ' : Ty Base} {c : Const σ}
    {t : Term Const [] σ'} {body : Term Const [σ'] τ}
    (ht : NoConstOccurrence c t) (hbody : NoConstOccurrence c body) :
    NoConstOccurrence c (instantiate (Base := Base) t body) :=
  noConstOccurrence_subst
    (fun v => by cases v with | vz => exact ht | vs v => cases v)
    body hbody

/-- Rename that inserts σ after prefix Ξ: maps (Ξ ++ Γ) into (Ξ ++ σ :: Γ). -/
def insertRen
    {Γ : Ctx Base} {σ : Ty Base} :
    (Ξ : Ctx Base) → Rename Base (Ξ ++ Γ) (Ξ ++ σ :: Γ)
  | [] => Rename.weaken
  | _ :: Ξ => Rename.lift (insertRen (Γ := Γ) (σ := σ) Ξ)

/-- Substitution replacing the σ-variable after prefix Ξ with (.const c):
    maps (Ξ ++ σ :: Γ) into (Ξ ++ Γ). -/
def singleAt
    {Γ : Ctx Base} {σ : Ty Base} (c : Const σ) :
    (Ξ : Ctx Base) → Subst Const (Ξ ++ σ :: Γ) (Ξ ++ Γ)
  | [] => Subst.single (.const c)
  | _ :: Ξ => Subst.lift (singleAt (Γ := Γ) (σ := σ) c Ξ)

/-- Key identity: Rename.lift ρ ∘ Rename.weaken = Rename.weaken ∘ ρ
    (as a rename-composition identity on terms). -/
theorem rename_lift_weaken
    (ρ : Rename Base Γ Δ) (t : Term Const Γ τ) :
    rename (Rename.lift (Base := Base) (σ := σ) ρ)
      (rename (Rename.weaken (Base := Base) (σ := σ)) t) =
    rename (Rename.weaken (Base := Base) (σ := σ)) (rename ρ t) := by
  rw [rename_comp, rename_comp]
  apply rename_ext
  intro _ v
  rfl

/-- Variable case of the prefix theorem: for variables in (Ξ ++ σ :: Γ),
    if NoConstOccurrence c holds for the substituted result, then
    the variable equals the renamed-back result. -/
theorem var_singleAt_insertRen
    {Γ : Ctx Base} {σ : Ty Base} (c : Const σ) :
    ∀ (Ξ : Ctx Base) {τ : Ty Base}
      (v : Var (Ξ ++ σ :: Γ) τ),
      NoConstOccurrence c (singleAt (Γ := Γ) (σ := σ) c Ξ v) →
      .var v = rename (insertRen (Γ := Γ) (σ := σ) Ξ)
        (singleAt (Γ := Γ) (σ := σ) c Ξ v)
  | [], _, .vz, hno => by
      simp [singleAt, Subst.single] at hno
      cases hno with
      | const_diff_type hne => exact absurd rfl hne
      | const_same_ne _ hne => exact absurd rfl hne
  | [], _, .vs _, _ => rfl
  | _ :: _, _, .vz, _ => rfl
  | _ :: Ξ, _, .vs w, hno => by
      have hno' : NoConstOccurrence c (singleAt (Γ := Γ) (σ := σ) c Ξ w) :=
        noConstOccurrence_of_rename Rename.weaken (singleAt c Ξ w) hno
      have ih := var_singleAt_insertRen c Ξ w hno'
      simp only [insertRen, singleAt, Subst.lift] at ⊢
      rw [rename_lift_weaken, ← ih]
      rfl

/-- Prefix-generalized auxiliary: the prefix Ξ grows under binders,
    making the structural recursion well-typed.
    Base case Ξ = [] recovers the original single-substitution theorem. -/
theorem weaken_of_instantiate_prefix
    {Γ : Ctx Base} {σ : Ty Base} (c : Const σ) :
    ∀ (Ξ : Ctx Base) {τ : Ty Base}
      (φ : Term Const (Ξ ++ σ :: Γ) τ),
      NoConstOccurrence c (subst (singleAt (Γ := Γ) (σ := σ) c Ξ) φ) →
      φ = rename (insertRen (Γ := Γ) (σ := σ) Ξ)
        (subst (singleAt (Γ := Γ) (σ := σ) c Ξ) φ)
  | Ξ, _, .var v, hno => var_singleAt_insertRen c Ξ v hno
  | _, _, .const _, _ => rfl
  | _, _, .top, _ => rfl
  | _, _, .bot, _ => rfl
  | Ξ, _, .app f t, hno => by
      cases hno with
      | app hf ht =>
          exact congr (congrArg Term.app (weaken_of_instantiate_prefix c Ξ f hf))
            (weaken_of_instantiate_prefix c Ξ t ht)
  | Ξ, _, .and φ ψ, hno => by
      cases hno with
      | and h1 h2 =>
          exact congr (congrArg Term.and (weaken_of_instantiate_prefix c Ξ φ h1))
            (weaken_of_instantiate_prefix c Ξ ψ h2)
  | Ξ, _, .or φ ψ, hno => by
      cases hno with
      | or h1 h2 =>
          exact congr (congrArg Term.or (weaken_of_instantiate_prefix c Ξ φ h1))
            (weaken_of_instantiate_prefix c Ξ ψ h2)
  | Ξ, _, .imp φ ψ, hno => by
      cases hno with
      | imp h1 h2 =>
          exact congr (congrArg Term.imp (weaken_of_instantiate_prefix c Ξ φ h1))
            (weaken_of_instantiate_prefix c Ξ ψ h2)
  | Ξ, _, .not φ, hno => by
      cases hno with
      | not h1 => exact congrArg Term.not (weaken_of_instantiate_prefix c Ξ φ h1)
  | Ξ, _, .eq t u, hno => by
      cases hno with
      | eq h1 h2 =>
          exact congr (congrArg Term.eq (weaken_of_instantiate_prefix c Ξ t h1))
            (weaken_of_instantiate_prefix c Ξ u h2)
  | Ξ, _, .lam body, hno => by
      cases hno with
      | lam hb =>
          exact congrArg Term.lam (weaken_of_instantiate_prefix c (_ :: Ξ) body hb)
  | Ξ, _, .all body, hno => by
      cases hno with
      | all hb =>
          exact congrArg Term.all (weaken_of_instantiate_prefix c (_ :: Ξ) body hb)
  | Ξ, _, .ex body, hno => by
      cases hno with
      | ex hb =>
          exact congrArg Term.ex (weaken_of_instantiate_prefix c (_ :: Ξ) body hb)

/-- If `instantiate (.const c) φ = θ` and `c` doesn't occur in `θ`,
    then `φ = weaken θ` (variable 0 was unused). -/
theorem weaken_of_instantiate_const_noOccurrence
    {Γ : Ctx Base} {σ τ : Ty Base}
    (c : Const σ)
    (φ : Term Const (σ :: Γ) τ)
    (θ : Term Const Γ τ)
    (h : instantiate (Base := Base) (.const c) φ = θ)
    (hno : NoConstOccurrence c θ) :
    φ = weaken (Base := Base) (σ := σ) θ := by
  subst h
  exact weaken_of_instantiate_prefix c [] φ hno

/-- The σ-variable at depth |Ξ| in context (Ξ ++ σ :: Γ). -/
def varAtDepth {Γ : Ctx Base} {σ : Ty Base} :
    (Ξ : Ctx Base) → Var (Ξ ++ σ :: Γ) σ
  | [] => .vz
  | _ :: Ξ => .vs (varAtDepth (Γ := Γ) (σ := σ) Ξ)

/-- Replace occurrences of constant `c : Const σ` with a bound variable at
    depth |Ξ| in the context, shifting all existing variables past the new slot.

    This is the reverse of `subst (singleAt c Ξ) ·`.
    Under binders, Ξ grows (same pattern as `singleAt`/`insertRen`). -/
noncomputable def abstractConstAt (c : Const σ) :
    (Ξ : Ctx Base) → {τ : Ty Base} → Term Const (Ξ ++ Γ) τ → Term Const (Ξ ++ σ :: Γ) τ
  | Ξ, _, .var v => .var (insertRen (Γ := Γ) (σ := σ) Ξ v)
  | Ξ, _, .const d =>
      @dite _ ((⟨_, d⟩ : Sigma Const) = ⟨σ, c⟩) (Classical.propDecidable _)
        (fun h => cast (congrArg (Term Const (Ξ ++ σ :: Γ)) (congrArg Sigma.fst h).symm)
          (.var (varAtDepth (Γ := Γ) (σ := σ) Ξ)))
        (fun _ => .const d)
  | Ξ, _, .app f t => .app (abstractConstAt c Ξ f) (abstractConstAt c Ξ t)
  | Ξ, _, .lam body => .lam (abstractConstAt c (_ :: Ξ) body)
  | _, _, .top => .top
  | _, _, .bot => .bot
  | Ξ, _, .and φ ψ => .and (abstractConstAt c Ξ φ) (abstractConstAt c Ξ ψ)
  | Ξ, _, .or φ ψ => .or (abstractConstAt c Ξ φ) (abstractConstAt c Ξ ψ)
  | Ξ, _, .imp φ ψ => .imp (abstractConstAt c Ξ φ) (abstractConstAt c Ξ ψ)
  | Ξ, _, .not φ => .not (abstractConstAt c Ξ φ)
  | Ξ, _, .eq t u => .eq (abstractConstAt c Ξ t) (abstractConstAt c Ξ u)
  | Ξ, _, .all body => .all (abstractConstAt c (_ :: Ξ) body)
  | Ξ, _, .ex body => .ex (abstractConstAt c (_ :: Ξ) body)

/-- Wrapper: abstract constant c at depth 0. -/
noncomputable abbrev abstractConst (c : Const σ) (t : Term Const Γ τ) :
    Term Const (σ :: Γ) τ :=
  abstractConstAt (Base := Base) c [] t

/-- singleAt c Ξ cancels insertRen Ξ on variables. -/
theorem singleAt_insertRen_cancel {c : Const σ} :
    ∀ (Ξ : Ctx Base) {τ : Ty Base} (v : Var (Ξ ++ Γ) τ),
      singleAt (Γ := Γ) (σ := σ) c Ξ (insertRen (Γ := Γ) (σ := σ) Ξ v) = .var v
  | [], _, v => rfl
  | _ :: Ξ, _, .vz => rfl
  | _ :: Ξ, _, .vs v => by
      simp only [insertRen, singleAt, Rename.lift, Subst.lift]
      rw [singleAt_insertRen_cancel Ξ v]
      rfl

/-- singleAt c Ξ sends varAtDepth Ξ to .const c. -/
theorem singleAt_varAtDepth {c : Const σ} :
    ∀ (Ξ : Ctx Base),
      singleAt (Γ := Γ) (σ := σ) c Ξ (varAtDepth (Γ := Γ) (σ := σ) Ξ) = .const c
  | [] => rfl
  | _ :: Ξ => by
      simp only [varAtDepth, singleAt, Subst.lift]
      rw [singleAt_varAtDepth Ξ]; rfl

/-- When `c` does not occur in `t`, abstracting is the same as inserting a variable. -/
theorem abstractConstAt_noOccurrence {c : Const σ} :
    ∀ (Ξ : Ctx Base) {τ : Ty Base} (t : Term Const (Ξ ++ Γ) τ),
      NoConstOccurrence c t →
      abstractConstAt (Base := Base) c Ξ t =
        rename (insertRen (Γ := Γ) (σ := σ) Ξ) t
  | _, _, .var _, _ => by simp [abstractConstAt, rename]
  | Ξ, _, .const d, h => by
      simp only [abstractConstAt, rename]
      split
      · next heq =>
          -- heq : ⟨_, d⟩ = ⟨σ, c⟩, so d = c — contradicts NoConstOccurrence
          have hτ := congrArg Sigma.fst heq
          subst hτ
          have hd : d = c := eq_of_heq (Sigma.mk.inj heq).2
          subst hd
          cases h with
          | const_diff_type hne => exact absurd rfl hne
          | const_same_ne _ hne => exact absurd rfl hne
      · rfl
  | Ξ, _, .app f t, h => by
      cases h with | app hf ht =>
        simp only [abstractConstAt, rename,
          abstractConstAt_noOccurrence Ξ f hf, abstractConstAt_noOccurrence Ξ t ht]
  | Ξ, _, .lam body, h => by
      cases h with | lam hb =>
        simp only [abstractConstAt, rename, insertRen,
          abstractConstAt_noOccurrence (_ :: Ξ) body hb]
  | _, _, .top, _ => by simp [abstractConstAt, rename]
  | _, _, .bot, _ => by simp [abstractConstAt, rename]
  | Ξ, _, .and p q, h => by
      cases h with | and h1 h2 =>
        simp only [abstractConstAt, rename,
          abstractConstAt_noOccurrence Ξ p h1, abstractConstAt_noOccurrence Ξ q h2]
  | Ξ, _, .or p q, h => by
      cases h with | or h1 h2 =>
        simp only [abstractConstAt, rename,
          abstractConstAt_noOccurrence Ξ p h1, abstractConstAt_noOccurrence Ξ q h2]
  | Ξ, _, .imp p q, h => by
      cases h with | imp h1 h2 =>
        simp only [abstractConstAt, rename,
          abstractConstAt_noOccurrence Ξ p h1, abstractConstAt_noOccurrence Ξ q h2]
  | Ξ, _, .not p, h => by
      cases h with | not h1 =>
        simp only [abstractConstAt, rename,
          abstractConstAt_noOccurrence Ξ p h1]
  | Ξ, _, .eq t u, h => by
      cases h with | eq h1 h2 =>
        simp only [abstractConstAt, rename,
          abstractConstAt_noOccurrence Ξ t h1, abstractConstAt_noOccurrence Ξ u h2]
  | Ξ, _, .all body, h => by
      cases h with | all hb =>
        simp only [abstractConstAt, rename, insertRen,
          abstractConstAt_noOccurrence (_ :: Ξ) body hb]
  | Ξ, _, .ex body, h => by
      cases h with | ex hb =>
        simp only [abstractConstAt, rename, insertRen,
          abstractConstAt_noOccurrence (_ :: Ξ) body hb]

/-- Round-trip: substituting `c` back into the abstracted term recovers the original. -/
theorem subst_singleAt_abstractConstAt (c : Const σ) :
    ∀ (Ξ : Ctx Base) {τ : Ty Base} (t : Term Const (Ξ ++ Γ) τ),
      subst (singleAt (Γ := Γ) (σ := σ) c Ξ)
        (abstractConstAt (Base := Base) c Ξ t) = t
  | Ξ, _, .var v => by
      simp only [abstractConstAt, subst]
      exact singleAt_insertRen_cancel Ξ v
  | Ξ, _, .const d => by
      simp only [abstractConstAt]
      split
      · next heq =>
          have hτ := congrArg Sigma.fst heq
          subst hτ
          have hd : d = c := eq_of_heq (Sigma.mk.inj heq).2
          subst hd
          simp only [cast_eq, subst]
          exact singleAt_varAtDepth Ξ
      · rfl
  | Ξ, _, .app f t => by
      simp only [abstractConstAt, subst,
        subst_singleAt_abstractConstAt c Ξ f, subst_singleAt_abstractConstAt c Ξ t]
  | Ξ, _, .lam body => by
      simp only [abstractConstAt, subst]
      congr 1
      exact subst_singleAt_abstractConstAt c (_ :: Ξ) body
  | _, _, .top => by simp [abstractConstAt, subst]
  | _, _, .bot => by simp [abstractConstAt, subst]
  | Ξ, _, .and p q => by
      simp only [abstractConstAt, subst,
        subst_singleAt_abstractConstAt c Ξ p, subst_singleAt_abstractConstAt c Ξ q]
  | Ξ, _, .or p q => by
      simp only [abstractConstAt, subst,
        subst_singleAt_abstractConstAt c Ξ p, subst_singleAt_abstractConstAt c Ξ q]
  | Ξ, _, .imp p q => by
      simp only [abstractConstAt, subst,
        subst_singleAt_abstractConstAt c Ξ p, subst_singleAt_abstractConstAt c Ξ q]
  | Ξ, _, .not p => by
      simp only [abstractConstAt, subst,
        subst_singleAt_abstractConstAt c Ξ p]
  | Ξ, _, .eq t u => by
      simp only [abstractConstAt, subst,
        subst_singleAt_abstractConstAt c Ξ t, subst_singleAt_abstractConstAt c Ξ u]
  | Ξ, _, .all body => by
      simp only [abstractConstAt, subst]
      congr 1
      exact subst_singleAt_abstractConstAt c (_ :: Ξ) body
  | Ξ, _, .ex body => by
      simp only [abstractConstAt, subst]
      congr 1
      exact subst_singleAt_abstractConstAt c (_ :: Ξ) body

/-- Insert a variable of type `ρ` between upper prefix `Ξ₁` and lower suffix `Ξ₂`.
    Bakes the split into the recursion so both domain and codomain are
    left-associated: `((Ξ₁ ++ Ξ₂) ++ Γ)` and `((Ξ₁ ++ ρ :: Ξ₂) ++ Γ)`.
    Under binders, Ξ₁ grows — no `List.append_assoc` casts needed. -/
def insertRenAt
    {Γ : Ctx Base} {ρ : Ty Base} :
    (Ξ₁ Ξ₂ : Ctx Base) →
      Rename Base (((Ξ₁ ++ Ξ₂) ++ Γ)) (((Ξ₁ ++ (ρ :: Ξ₂)) ++ Γ))
  | [], _ => Rename.weaken
  | _ :: Ξ₁, Ξ₂ => Rename.lift (insertRenAt (Γ := Γ) (ρ := ρ) Ξ₁ Ξ₂)

/-- Insertion commutes with insertion: insertRen through insertRenAt = insertRenAt through insertRen. -/
@[simp] theorem insertRenAt_insertRen
    (Ξ₁ Ξ₂ : Ctx Base) {σ ρ τ : Ty Base}
    (v : Var (((Ξ₁ ++ Ξ₂) ++ Γ)) τ) :
    insertRen (Γ := Γ) (σ := σ) (Ξ₁ ++ (ρ :: Ξ₂))
      (insertRenAt (Base := Base) (Γ := Γ) (ρ := ρ) Ξ₁ Ξ₂ v) =
    insertRenAt (Base := Base) (Γ := σ :: Γ) (ρ := ρ) Ξ₁ Ξ₂
      (insertRen (Γ := Γ) (σ := σ) (Ξ₁ ++ Ξ₂) v) := by
  induction Ξ₁ with
  | nil => simp [insertRenAt, insertRen, Rename.weaken, Rename.lift]
  | cons α Ξ₁ ih =>
      cases v with
      | vz => rfl
      | vs v => simp only [insertRenAt, insertRen, Rename.lift]; exact congrArg Var.vs (ih v)

/-- Insertion preserves the distinguished abstracted variable depth. -/
@[simp] theorem insertRenAt_varAtDepth
    (Ξ₁ Ξ₂ : Ctx Base) {ρ : Ty Base} :
    insertRenAt (Base := Base) (Γ := σ :: Γ) (ρ := ρ) Ξ₁ Ξ₂
      (varAtDepth (Γ := Γ) (σ := σ) (Ξ₁ ++ Ξ₂)) =
    varAtDepth (Γ := Γ) (σ := σ) (Ξ₁ ++ (ρ :: Ξ₂)) := by
  induction Ξ₁ with
  | nil => simp [insertRenAt, varAtDepth, Rename.weaken]
  | cons α Ξ₁ ih =>
      simp only [insertRenAt, varAtDepth, Rename.lift]; exact congrArg Var.vs ih

/-- abstractConstAt commutes with split-point insertion (GPT-5.4 Pro route).
    No `List.append_assoc` casts — the split is structural in the recursion. -/
@[simp] theorem abstractConstAt_insertRenAt
    {c : Const σ}
    (Ξ₁ Ξ₂ : Ctx Base) {ρ τ : Ty Base}
    (t : Term Const (((Ξ₁ ++ Ξ₂) ++ Γ)) τ) :
    abstractConstAt (Base := Base) c (Ξ₁ ++ (ρ :: Ξ₂))
      (rename (insertRenAt (Base := Base) (Γ := Γ) (ρ := ρ) Ξ₁ Ξ₂) t) =
    rename (insertRenAt (Base := Base) (Γ := σ :: Γ) (ρ := ρ) Ξ₁ Ξ₂)
      (abstractConstAt (Base := Base) c (Ξ₁ ++ Ξ₂) t) :=
  match t with
  | .var v => by simp only [abstractConstAt, rename]; exact congrArg Term.var (insertRenAt_insertRen Ξ₁ Ξ₂ v)
  | .const d => by
      simp only [rename, abstractConstAt]; split
      · next h => have hτ := congrArg Sigma.fst h; subst hτ; simp [cast_eq, rename, insertRenAt_varAtDepth]
      · rfl
  | .app f u => by simp [abstractConstAt, rename, abstractConstAt_insertRenAt Ξ₁ Ξ₂ f, abstractConstAt_insertRenAt Ξ₁ Ξ₂ u]
  | .lam body => by simp only [abstractConstAt, rename, insertRenAt]; congr 1; exact abstractConstAt_insertRenAt (_ :: Ξ₁) Ξ₂ body
  | .top => by simp [abstractConstAt, rename]
  | .bot => by simp [abstractConstAt, rename]
  | .and p q => by simp [abstractConstAt, rename, abstractConstAt_insertRenAt Ξ₁ Ξ₂ p, abstractConstAt_insertRenAt Ξ₁ Ξ₂ q]
  | .or p q => by simp [abstractConstAt, rename, abstractConstAt_insertRenAt Ξ₁ Ξ₂ p, abstractConstAt_insertRenAt Ξ₁ Ξ₂ q]
  | .imp p q => by simp [abstractConstAt, rename, abstractConstAt_insertRenAt Ξ₁ Ξ₂ p, abstractConstAt_insertRenAt Ξ₁ Ξ₂ q]
  | .not p => by simp only [abstractConstAt, rename]; congr 1; exact abstractConstAt_insertRenAt Ξ₁ Ξ₂ p
  | .eq a b => by simp [abstractConstAt, rename, abstractConstAt_insertRenAt Ξ₁ Ξ₂ a, abstractConstAt_insertRenAt Ξ₁ Ξ₂ b]
  | .all body => by simp only [abstractConstAt, rename, insertRenAt]; congr 1; exact abstractConstAt_insertRenAt (_ :: Ξ₁) Ξ₂ body
  | .ex body => by simp only [abstractConstAt, rename, insertRenAt]; congr 1; exact abstractConstAt_insertRenAt (_ :: Ξ₁) Ξ₂ body

/-- abstractConstAt commutes with weakening (Ξ₁=[] specialization). -/
@[simp] theorem abstractConstAt_weaken
    {c : Const σ} (Ξ : Ctx Base) {ρ τ : Ty Base}
    (t : Term Const ((Ξ ++ Γ)) τ) :
    abstractConstAt (Base := Base) c (ρ :: Ξ)
      (weaken (Base := Base) (Const := Const) (σ := ρ) t) =
    weaken (Base := Base) (Const := Const) (σ := ρ)
      (abstractConstAt (Base := Base) c Ξ t) := by
  exact abstractConstAt_insertRenAt (c := c) [] Ξ t

/-- Split-point substitution: substitute a term from the lower suffix `Ξ₂ ++ Γ`
    into the distinguished `σ`-slot sitting between an upper prefix `Ξ₁` and
    the lower suffix `Ξ₂`.

    The recursion follows the upper prefix `Ξ₁`, so binder cases can extend the
    split structurally without any `List.append_assoc` casts. -/
def substAt
    {Γ : Ctx Base} {σ : Ty Base} :
    (Ξ₁ Ξ₂ : Ctx Base) →
      Term Const (Ξ₂ ++ Γ) σ →
      Subst Const (((Ξ₁ ++ (σ :: Ξ₂)) ++ Γ)) (((Ξ₁ ++ Ξ₂) ++ Γ))
  | [], _, t => Subst.single t
  | _ :: Ξ₁, Ξ₂, t => Subst.lift (substAt (Γ := Γ) Ξ₁ Ξ₂ t)

/-- Substituting at the split point preserves the abstracted-variable depth:
    the distinguished `ρ`-variable remains the same distinguished variable after
    eliminating the separate `σ` slot. -/
@[simp] theorem substAt_varAtDepth
    {Γ : Ctx Base} {ρ σ : Ty Base}
    (Ξ₁ Ξ₂ : Ctx Base)
    (t : Term Const (Ξ₂ ++ ρ :: Γ) σ) :
    substAt (Base := Base) (Const := Const) (Γ := ρ :: Γ) (σ := σ) Ξ₁ Ξ₂ t
      (varAtDepth (Γ := Γ) (σ := ρ) (Ξ₁ ++ (σ :: Ξ₂))) =
    .var (varAtDepth (Γ := Γ) (σ := ρ) (Ξ₁ ++ Ξ₂)) := by
  induction Ξ₁ with
  | nil =>
      rfl
  | cons α Ξ₁ ih =>
      simpa [substAt, varAtDepth, weaken] using
        congrArg (weaken (Base := Base) (Const := Const) (σ := α)) ih

/-- Variable case of split-point substitution commutation:
    abstracting `c` below the split commutes with substituting a lower-suffix
    term into the `σ`-slot above it. -/
theorem abstractConstAt_substAt_var
    {Γ : Ctx Base} {ρ σ τ : Ty Base}
    {c : Const ρ} :
    ∀ (Ξ₁ Ξ₂ : Ctx Base)
      (t : Term Const (Ξ₂ ++ Γ) σ)
      (v : Var (((Ξ₁ ++ (σ :: Ξ₂)) ++ Γ)) τ),
      abstractConstAt (Base := Base) (Γ := Γ) c (Ξ₁ ++ Ξ₂)
        (substAt (Base := Base) (Const := Const) (Γ := Γ) Ξ₁ Ξ₂ t v) =
      (substAt (Base := Base) (Const := Const) (Γ := ρ :: Γ) Ξ₁ Ξ₂
        (abstractConstAt (Base := Base) (Γ := Γ) c Ξ₂ t))
        (insertRen (Γ := Γ) (σ := ρ) (Ξ₁ ++ (σ :: Ξ₂)) v)
  | [], Ξ₂, t, .vz => by
      rfl
  | [], Ξ₂, t, .vs v => by
      change abstractConstAt (Base := Base) (Γ := Γ) c Ξ₂ (.var v) =
        (substAt (Base := Base) (Const := Const) (Γ := ρ :: Γ) [] Ξ₂
          (abstractConstAt (Base := Base) (Γ := Γ) c Ξ₂ t))
          (insertRen (Γ := Γ) (σ := ρ) ([] ++ (σ :: Ξ₂)) (.vs v))
      simp [substAt, abstractConstAt, insertRen, List.nil_append, Subst.single, Rename.lift]
  | _ :: Ξ₁, Ξ₂, t, .vz => by
      change abstractConstAt (Base := Base) (Γ := Γ) c (_ :: (Ξ₁ ++ Ξ₂)) (.var .vz) =
        (substAt (Base := Base) (Const := Const) (Γ := ρ :: Γ) (_ :: Ξ₁) Ξ₂
          (abstractConstAt (Base := Base) (Γ := Γ) c Ξ₂ t))
          (insertRen (Γ := Γ) (σ := ρ) ((_ :: Ξ₁) ++ (σ :: Ξ₂)) (.vz))
      simp [substAt, abstractConstAt, insertRen, List.cons_append, Subst.lift, Rename.lift]
  | α :: Ξ₁, Ξ₂, t, .vs v => by
      calc
        abstractConstAt (Base := Base) (Γ := Γ) c ((α :: Ξ₁) ++ Ξ₂)
            (substAt (Base := Base) (Const := Const) (Γ := Γ) (α :: Ξ₁) Ξ₂ t (.vs v))
            =
          abstractConstAt (Base := Base) (Γ := Γ) c (α :: (Ξ₁ ++ Ξ₂))
            (weaken (Base := Base) (Const := Const) (σ := α)
              (substAt (Base := Base) (Const := Const) (Γ := Γ) Ξ₁ Ξ₂ t v)) := by
                rfl
        _ =
          weaken (Base := Base) (Const := Const) (σ := α)
            (abstractConstAt (Base := Base) (Γ := Γ) c (Ξ₁ ++ Ξ₂)
              (substAt (Base := Base) (Const := Const) (Γ := Γ) Ξ₁ Ξ₂ t v)) := by
                simp [List.cons_append]
        _ =
          weaken (Base := Base) (Const := Const) (σ := α)
            ((substAt (Base := Base) (Const := Const) (Γ := ρ :: Γ) Ξ₁ Ξ₂
              (abstractConstAt (Base := Base) (Γ := Γ) c Ξ₂ t))
              (insertRen (Γ := Γ) (σ := ρ) (Ξ₁ ++ (σ :: Ξ₂)) v)) := by
                exact congrArg
                  (weaken (Base := Base) (Const := Const) (σ := α))
                  (abstractConstAt_substAt_var (c := c) Ξ₁ Ξ₂ t v)
        _ =
          (substAt (Base := Base) (Const := Const) (Γ := ρ :: Γ) (α :: Ξ₁) Ξ₂
            (abstractConstAt (Base := Base) (Γ := Γ) c Ξ₂ t))
            (insertRen (Γ := Γ) (σ := ρ) ((α :: Ξ₁) ++ (σ :: Ξ₂)) (.vs v)) := by
              rfl

/-- Full commutation: abstractConstAt commutes with split-point substitution.
    Variable case proved by CodeX (abstractConstAt_substAt_var).
    Structural cases by match recursion (same pattern as abstractConstAt_insertRenAt). -/
theorem abstractConstAt_substAt {c : Const ρ} :
    ∀ (Ξ₁ Ξ₂ : Ctx Base) {σ τ : Ty Base}
      (t : Term Const ((Ξ₂ ++ Γ)) σ)
      (u : Term Const (((Ξ₁ ++ (σ :: Ξ₂)) ++ Γ)) τ),
      abstractConstAt (Base := Base) c (Ξ₁ ++ Ξ₂)
        (subst (substAt (Γ := Γ) Ξ₁ Ξ₂ t) u) =
      subst (substAt (Γ := ρ :: Γ) Ξ₁ Ξ₂ (abstractConstAt (Base := Base) c Ξ₂ t))
        (abstractConstAt (Base := Base) c (Ξ₁ ++ (σ :: Ξ₂)) u)
  | Ξ₁, Ξ₂, _, _, t, .var v => by simp only [subst, abstractConstAt]; exact abstractConstAt_substAt_var Ξ₁ Ξ₂ t v
  | _, _, _, _, _, .const d => by
      simp only [subst, abstractConstAt]; split
      · next h => have hτ := congrArg Sigma.fst h; subst hτ; simp [cast_eq, subst, substAt_varAtDepth]
      · rfl
  | Ξ₁, Ξ₂, _, _, t, .app f u => by
      simp only [subst, abstractConstAt, abstractConstAt_substAt Ξ₁ Ξ₂ t f, abstractConstAt_substAt Ξ₁ Ξ₂ t u]
  | Ξ₁, Ξ₂, _, _, t, .lam body => by
      simp only [subst, abstractConstAt, substAt]
      congr 1; exact abstractConstAt_substAt (_ :: Ξ₁) Ξ₂ t body
  | _, _, _, _, _, .top => by simp [subst, abstractConstAt]
  | _, _, _, _, _, .bot => by simp [subst, abstractConstAt]
  | Ξ₁, Ξ₂, _, _, t, .and p q => by
      simp only [subst, abstractConstAt, abstractConstAt_substAt Ξ₁ Ξ₂ t p, abstractConstAt_substAt Ξ₁ Ξ₂ t q]
  | Ξ₁, Ξ₂, _, _, t, .or p q => by
      simp only [subst, abstractConstAt, abstractConstAt_substAt Ξ₁ Ξ₂ t p, abstractConstAt_substAt Ξ₁ Ξ₂ t q]
  | Ξ₁, Ξ₂, _, _, t, .imp p q => by
      simp only [subst, abstractConstAt, abstractConstAt_substAt Ξ₁ Ξ₂ t p, abstractConstAt_substAt Ξ₁ Ξ₂ t q]
  | Ξ₁, Ξ₂, _, _, t, .not p => by
      simp only [subst, abstractConstAt]; congr 1; exact abstractConstAt_substAt Ξ₁ Ξ₂ t p
  | Ξ₁, Ξ₂, _, _, t, .eq a b => by
      simp only [subst, abstractConstAt, abstractConstAt_substAt Ξ₁ Ξ₂ t a, abstractConstAt_substAt Ξ₁ Ξ₂ t b]
  | Ξ₁, Ξ₂, _, _, t, .all body => by
      simp only [subst, abstractConstAt, substAt]
      congr 1; exact abstractConstAt_substAt (_ :: Ξ₁) Ξ₂ t body
  | Ξ₁, Ξ₂, _, _, t, .ex body => by
      simp only [subst, abstractConstAt, substAt]
      congr 1; exact abstractConstAt_substAt (_ :: Ξ₁) Ξ₂ t body

/-- Specialization: abstractConstAt commutes with instantiation (Ξ₁=[], Ξ₂=Ξ). -/
@[simp] theorem abstractConstAt_instantiate {c : Const ρ}
    (Ξ : Ctx Base) {σ τ : Ty Base}
    (t : Term Const ((Ξ ++ Γ)) σ)
    (u : Term Const (((σ :: Ξ) ++ Γ)) τ) :
    abstractConstAt (Base := Base) c Ξ (instantiate (Base := Base) t u) =
    instantiate (Base := Base)
      (abstractConstAt (Base := Base) c Ξ t)
      (abstractConstAt (Base := Base) c (σ :: Ξ) u) :=
  abstractConstAt_substAt [] Ξ t u

end Mettapedia.Logic.HOL
