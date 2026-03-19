import Mettapedia.Logic.HOL.Syntax.Closed

namespace Mettapedia.Logic.HOL

universe u v w x

variable {Base : Type u}
variable {Const : Ty Base → Type v} {Const' : Ty Base → Type w}
variable {Const'' : Ty Base → Type x}

/-- Map the constant symbols in a typed HOL term, leaving variables untouched. -/
def mapConst (f : ∀ {τ : Ty Base}, Const τ → Const' τ) :
    Term Const Γ τ → Term Const' Γ τ
  | .var v => .var v
  | .const c => .const (f c)
  | .app g t => .app (mapConst f g) (mapConst f t)
  | .lam t => .lam (mapConst f t)
  | .top => .top
  | .bot => .bot
  | .and φ ψ => .and (mapConst f φ) (mapConst f ψ)
  | .or φ ψ => .or (mapConst f φ) (mapConst f ψ)
  | .imp φ ψ => .imp (mapConst f φ) (mapConst f ψ)
  | .not φ => .not (mapConst f φ)
  | .eq t u => .eq (mapConst f t) (mapConst f u)
  | .all φ => .all (mapConst f φ)
  | .ex φ => .ex (mapConst f φ)

@[simp] theorem mapConst_var (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (v : Var Γ τ) :
    mapConst f (.var v : Term Const Γ τ) = .var v := rfl

@[simp] theorem mapConst_const (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (c : Const τ) :
    mapConst f (.const c : Term Const Γ τ) = .const (f c) := rfl

@[simp] theorem mapConst_id (t : Term Const Γ τ) :
    mapConst (Const := Const) (Const' := Const) (fun c => c) t = t := by
  induction t with
  | var v => rfl
  | const c => rfl
  | app g t hg ht => simp [mapConst, hg, ht]
  | lam t ih => simp [mapConst, ih]
  | top => rfl
  | bot => rfl
  | and φ ψ hφ hψ => simp [mapConst, hφ, hψ]
  | or φ ψ hφ hψ => simp [mapConst, hφ, hψ]
  | imp φ ψ hφ hψ => simp [mapConst, hφ, hψ]
  | not φ hφ => simp [mapConst, hφ]
  | eq t u ht hu => simp [mapConst, ht, hu]
  | all φ hφ => simp [mapConst, hφ]
  | ex φ hφ => simp [mapConst, hφ]

@[simp] theorem mapConst_comp
    (g : ∀ {τ : Ty Base}, Const' τ → Const'' τ)
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (t : Term Const Γ τ) :
    mapConst g (mapConst f t) =
      mapConst (fun c => g (f c)) t := by
  induction t with
  | var v => rfl
  | const c => rfl
  | app g' t hg ht => simp [mapConst, hg, ht]
  | lam t ih => simp [mapConst, ih]
  | top => rfl
  | bot => rfl
  | and φ ψ hφ hψ => simp [mapConst, hφ, hψ]
  | or φ ψ hφ hψ => simp [mapConst, hφ, hψ]
  | imp φ ψ hφ hψ => simp [mapConst, hφ, hψ]
  | not φ hφ => simp [mapConst, hφ]
  | eq t u ht hu => simp [mapConst, ht, hu]
  | all φ hφ => simp [mapConst, hφ]
  | ex φ hφ => simp [mapConst, hφ]

theorem mapConst_ext
    {f g : ∀ {τ : Ty Base}, Const τ → Const' τ}
    (hfg : ∀ {τ : Ty Base} (c : Const τ), f c = g c)
    (t : Term Const Γ τ) :
    mapConst f t = mapConst g t := by
  induction t with
  | var v => rfl
  | const c => simp [mapConst, hfg c]
  | app g' t hg ht => simp [mapConst, hg, ht]
  | lam t ih => simp [mapConst, ih]
  | top => rfl
  | bot => rfl
  | and φ ψ hφ hψ => simp [mapConst, hφ, hψ]
  | or φ ψ hφ hψ => simp [mapConst, hφ, hψ]
  | imp φ ψ hφ hψ => simp [mapConst, hφ, hψ]
  | not φ hφ => simp [mapConst, hφ]
  | eq t u ht hu => simp [mapConst, ht, hu]
  | all φ hφ => simp [mapConst, hφ]
  | ex φ hφ => simp [mapConst, hφ]

theorem mapConst_rename (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (ρ : Rename Base Γ Δ) (t : Term Const Γ τ) :
    mapConst f (rename ρ t) = rename ρ (mapConst f t) := by
  induction t generalizing Δ with
  | var v => rfl
  | const c => rfl
  | app g t hg ht => simp [rename, mapConst, hg, ht]
  | lam t ih =>
      simp [rename, mapConst, ih]
  | top => rfl
  | bot => rfl
  | and φ ψ hφ hψ => simp [rename, mapConst, hφ, hψ]
  | or φ ψ hφ hψ => simp [rename, mapConst, hφ, hψ]
  | imp φ ψ hφ hψ => simp [rename, mapConst, hφ, hψ]
  | not φ hφ => simp [rename, mapConst, hφ]
  | eq t u ht hu => simp [rename, mapConst, ht, hu]
  | all φ hφ => simp [rename, mapConst, hφ]
  | ex φ hφ => simp [rename, mapConst, hφ]

@[simp] theorem mapConst_weaken (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (t : Term Const Γ τ) :
    mapConst f (weaken (Base := Base) (σ := σ) t) =
      weaken (Base := Base) (σ := σ) (mapConst f t) := by
  simpa [weaken] using
    mapConst_rename
      (Base := Base) (Const := Const) (Const' := Const')
      f (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ)) t

theorem mapConst_subst (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (σs : Subst Const Γ Δ) (t : Term Const Γ τ) :
    mapConst f (subst σs t) =
      subst (fun v => mapConst f (σs v)) (mapConst f t) := by
  induction t generalizing Δ with
  | var v =>
      rfl
  | const c =>
      rfl
  | app g t hg ht =>
      simp [subst, mapConst, hg, ht]
  | lam t ih =>
      apply congrArg Term.lam
      calc
        mapConst f (subst (Subst.lift (Base := Base) σs) t) =
            subst
              (fun {τ} v => mapConst f ((Subst.lift (Base := Base) σs) v))
              (mapConst f t) := ih (Subst.lift (Base := Base) σs)
        _ =
            subst
              (Subst.lift (Base := Base) (Const := Const')
                (fun {τ} v => mapConst f (σs v)))
              (mapConst f t) := by
                apply subst_ext (Base := Base) (Const := Const')
                intro τ v
                cases v with
                | vz =>
                    rfl
                | vs v =>
                    simp [Subst.lift, mapConst_rename]
  | top =>
      rfl
  | bot =>
      rfl
  | and φ ψ hφ hψ =>
      simp [subst, mapConst, hφ, hψ]
  | or φ ψ hφ hψ =>
      simp [subst, mapConst, hφ, hψ]
  | imp φ ψ hφ hψ =>
      simp [subst, mapConst, hφ, hψ]
  | not φ hφ =>
      simp [subst, mapConst, hφ]
  | eq t u ht hu =>
      simp [subst, mapConst, ht, hu]
  | all φ hφ =>
      apply congrArg Term.all
      calc
        mapConst f (subst (Subst.lift (Base := Base) σs) φ) =
            subst
              (fun {τ} v => mapConst f ((Subst.lift (Base := Base) σs) v))
              (mapConst f φ) := hφ (Subst.lift (Base := Base) σs)
        _ =
            subst
              (Subst.lift (Base := Base) (Const := Const')
                (fun {τ} v => mapConst f (σs v)))
              (mapConst f φ) := by
                apply subst_ext (Base := Base) (Const := Const')
                intro τ v
                cases v with
                | vz =>
                    rfl
                | vs v =>
                    simp [Subst.lift, mapConst_rename]
  | ex φ hφ =>
      apply congrArg Term.ex
      calc
        mapConst f (subst (Subst.lift (Base := Base) σs) φ) =
            subst
              (fun {τ} v => mapConst f ((Subst.lift (Base := Base) σs) v))
              (mapConst f φ) := hφ (Subst.lift (Base := Base) σs)
        _ =
            subst
              (Subst.lift (Base := Base) (Const := Const')
                (fun {τ} v => mapConst f (σs v)))
              (mapConst f φ) := by
                apply subst_ext (Base := Base) (Const := Const')
                intro τ v
                cases v with
                | vz =>
                    rfl
                | vs v =>
                    simp [Subst.lift, mapConst_rename]

@[simp] theorem mapConst_instantiate (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (t : Term Const Γ σ) (u : Term Const (σ :: Γ) τ) :
    mapConst f (instantiate t u) =
      instantiate (mapConst f t) (mapConst f u) := by
  unfold instantiate
  calc
    mapConst f (subst (Subst.single t) u) =
        subst
          (fun {τ} v => mapConst f ((Subst.single t) v))
          (mapConst f u) :=
      mapConst_subst (Base := Base) (Const := Const) (Const' := Const')
        f (Subst.single t) u
    _ =
        subst (Subst.single (Base := Base) (Const := Const') (mapConst f t))
          (mapConst f u) := by
            apply subst_ext (Base := Base) (Const := Const')
            intro τ v
            cases v with
            | vz =>
                rfl
            | vs v =>
                rfl

/-- Map constants in a closed HOL term. -/
abbrev mapClosedTerm (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (t : ClosedTerm Const τ) : ClosedTerm Const' τ :=
  mapConst f t

/-- Map constants in a closed HOL formula. -/
abbrev mapClosedFormula (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (φ : ClosedFormula Const) : ClosedFormula Const' :=
  mapConst f φ

end Mettapedia.Logic.HOL
