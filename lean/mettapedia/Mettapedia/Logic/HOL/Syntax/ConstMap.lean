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
  induction t <;> simp [mapConst, *]

@[simp] theorem mapConst_comp
    (g : ∀ {τ : Ty Base}, Const' τ → Const'' τ)
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (t : Term Const Γ τ) :
    mapConst g (mapConst f t) =
      mapConst (fun c => g (f c)) t := by
  induction t <;> simp [mapConst, *]

theorem mapConst_ext
    {f g : ∀ {τ : Ty Base}, Const τ → Const' τ}
    (hfg : ∀ {τ : Ty Base} (c : Const τ), f c = g c)
    (t : Term Const Γ τ) :
    mapConst f t = mapConst g t := by
  have same : (f : ∀ {τ : Ty Base}, Const τ → Const' τ) =
      (g : ∀ {τ : Ty Base}, Const τ → Const' τ) := by
    funext type constant
    exact hfg constant
  rw [same]

theorem mapConst_rename (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (ρ : Rename Base Γ Δ) (t : Term Const Γ τ) :
    mapConst f (rename ρ t) = rename ρ (mapConst f t) := by
  induction t generalizing Δ <;> simp [rename, mapConst, *]

@[simp] theorem mapConst_weaken (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (t : Term Const Γ τ) :
    mapConst f (weaken (Base := Base) (σ := σ) t) =
      weaken (Base := Base) (σ := σ) (mapConst f t) := by
  simpa [weaken] using
    mapConst_rename
      (Base := Base) (Const := Const) (Const' := Const')
      f (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ)) t

/-- Separation lemma: `mapConst` and `rename` act on orthogonal parts
    of a term (constants vs. variables). If `mapConst f ξ = rename ρ ψ`,
    then `ξ` is `rename ρ θ` for some `θ` with `mapConst f θ = ψ`.

    This is the key lemma for staged weakening inversion: if the lift
    of a staged term equals a weakened infinity term, the staged term
    is itself weakened. -/
theorem mapConst_rename_preimage (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (ρ : Rename Base Γ Δ) :
    ∀ (ξ : Term Const Δ τ) (ψ : Term Const' Γ τ),
    mapConst (fun {_} => f) ξ = rename (fun {_} => ρ) ψ →
    ∃ θ : Term Const Γ τ, ξ = rename (fun {_} => ρ) θ ∧
      mapConst (fun {_} => f) θ = ψ := by
  intro ξ ψ h
  induction ξ generalizing Γ with
  | var v =>
      cases ψ <;> simp [mapConst, rename] at h
      case var v' => exact ⟨.var v', by simp [rename, h], by simp [mapConst]⟩
  | const c =>
      cases ψ <;> simp [mapConst, rename] at h
      case const c' => exact ⟨.const c, rfl, by simp [mapConst, h]⟩
  | app g t ihg iht =>
      cases ψ with
      | app g' t' =>
          injection h with hΓ hσ hτ hg' ht'
          cases hΓ; cases hσ; cases hτ
          have hg := ihg ρ g' (by simpa [mapConst, rename] using hg')
          have ht := iht ρ t' (by simpa [mapConst, rename] using ht')
          obtain ⟨θg, hg1, hg2⟩ := hg
          obtain ⟨θt, ht1, ht2⟩ := ht
          exact ⟨.app θg θt, by simp [rename, hg1, ht1], by simp [mapConst, hg2, ht2]⟩
      | _ => simp [mapConst, rename] at h
  | lam t ih =>
      cases ψ with
      | lam t' =>
          have ht : mapConst (fun {τ} => f) t =
              rename (fun {τ} => Rename.lift ρ) t' := by
            simpa [mapConst, rename] using h
          obtain ⟨θ, h1, h2⟩ := ih (Rename.lift ρ) t' ht
          exact ⟨.lam θ, by simp [rename, h1], by simp [mapConst, h2]⟩
      | _ => simp [mapConst, rename] at h
  | top =>
      cases ψ <;> simp [mapConst, rename] at h
      exact ⟨.top, rfl, rfl⟩
  | bot =>
      cases ψ <;> simp [mapConst, rename] at h
      exact ⟨.bot, rfl, rfl⟩
  | and φ ψ ihφ ihψ =>
      cases ψ with
      | and φ' ψ' =>
          have hpair :
              mapConst (fun {τ} => f) φ = rename (fun {τ} => ρ) φ' ∧
              mapConst (fun {τ} => f) ψ = rename (fun {τ} => ρ) ψ' := by
            simpa [mapConst, rename] using h
          obtain ⟨θφ, hφ1, hφ2⟩ := ihφ ρ φ' hpair.1
          obtain ⟨θψ, hψ1, hψ2⟩ := ihψ ρ ψ' hpair.2
          exact ⟨.and θφ θψ, by simp [rename, hφ1, hψ1], by simp [mapConst, hφ2, hψ2]⟩
      | _ => simp [mapConst, rename] at h
  | or φ ψ ihφ ihψ =>
      cases ψ with
      | or φ' ψ' =>
          have hpair :
              mapConst (fun {τ} => f) φ = rename (fun {τ} => ρ) φ' ∧
              mapConst (fun {τ} => f) ψ = rename (fun {τ} => ρ) ψ' := by
            simpa [mapConst, rename] using h
          obtain ⟨θφ, hφ1, hφ2⟩ := ihφ ρ φ' hpair.1
          obtain ⟨θψ, hψ1, hψ2⟩ := ihψ ρ ψ' hpair.2
          exact ⟨.or θφ θψ, by simp [rename, hφ1, hψ1], by simp [mapConst, hφ2, hψ2]⟩
      | _ => simp [mapConst, rename] at h
  | imp φ ψ ihφ ihψ =>
      cases ψ with
      | imp φ' ψ' =>
          have hpair :
              mapConst (fun {τ} => f) φ = rename (fun {τ} => ρ) φ' ∧
              mapConst (fun {τ} => f) ψ = rename (fun {τ} => ρ) ψ' := by
            simpa [mapConst, rename] using h
          obtain ⟨θφ, hφ1, hφ2⟩ := ihφ ρ φ' hpair.1
          obtain ⟨θψ, hψ1, hψ2⟩ := ihψ ρ ψ' hpair.2
          exact ⟨.imp θφ θψ, by simp [rename, hφ1, hψ1], by simp [mapConst, hφ2, hψ2]⟩
      | _ => simp [mapConst, rename] at h
  | not φ ih =>
      cases ψ with
      | not φ' =>
          have hφ : mapConst (fun {τ} => f) φ = rename (fun {τ} => ρ) φ' := by
            simpa [mapConst, rename] using h
          obtain ⟨θ, h1, h2⟩ := ih ρ φ' hφ
          exact ⟨.not θ, by simp [rename, h1], by simp [mapConst, h2]⟩
      | _ => simp [mapConst, rename] at h
  | eq t u iht ihu =>
      cases ψ with
      | eq t' u' =>
          injection h with _ hτ ht' hu'
          subst hτ
          obtain ⟨θt, ht1, ht2⟩ := iht ρ t' (eq_of_heq ht')
          obtain ⟨θu, hu1, hu2⟩ := ihu ρ u' (eq_of_heq hu')
          exact ⟨.eq θt θu, by simp [rename, ht1, hu1], by simp [mapConst, ht2, hu2]⟩
      | _ => simp [mapConst, rename] at h
  | all φ ih =>
      cases ψ with
      | all φ' =>
          injection h with hσeq _ hbody
          subst hσeq
          obtain ⟨θ, h1, h2⟩ := ih (Rename.lift ρ) φ' (eq_of_heq hbody)
          exact ⟨.all θ, by simp [rename, h1], by simp [mapConst, h2]⟩
      | _ => simp [mapConst, rename] at h
  | ex φ ih =>
      cases ψ with
      | ex φ' =>
          injection h with hσeq _ hbody
          subst hσeq
          obtain ⟨θ, h1, h2⟩ := ih (Rename.lift ρ) φ' (eq_of_heq hbody)
          exact ⟨.ex θ, by simp [rename, h1], by simp [mapConst, h2]⟩
      | _ => simp [mapConst, rename] at h

/-- Specialization: if `mapConst f ξ = weaken ψ`, then `ξ = weaken θ`
    for some `θ` with `mapConst f θ = ψ`. -/
theorem mapConst_weaken_preimage (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    {ξ : Term Const (σ :: Γ) τ} {ψ : Term Const' Γ τ}
    (h : mapConst (fun {_} => f) ξ =
      weaken (Base := Base) (σ := σ) ψ) :
    ∃ θ : Term Const Γ τ, ξ = weaken (Base := Base) (σ := σ) θ ∧
      mapConst (fun {_} => f) θ = ψ :=
  mapConst_rename_preimage f Rename.weaken ξ ψ h

/-- List-level version: if `ξs.map (mapConst f) = ψs.map weaken`,
    recover `θs` with `ξs = θs.map weaken` and `θs.map (mapConst f) = ψs`. -/
theorem map_mapConst_eq_map_weaken_preimage
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    {Γ : Ctx Base} {σ : Ty Base} :
    ∀ (ξs : List (Term Const (σ :: Γ) propTy))
      (ψs : List (Term Const' Γ propTy)),
    ξs.map (mapConst (fun {_} => f)) =
      ψs.map (weaken (Base := Base) (σ := σ)) →
    ∃ θs : List (Term Const Γ propTy),
      ξs = θs.map (weaken (Base := Base) (σ := σ)) ∧
      θs.map (mapConst (fun {_} => f)) = ψs := by
  intro ξs ψs h
  induction ξs generalizing ψs with
  | nil =>
      cases ψs with
      | nil => exact ⟨[], rfl, rfl⟩
      | cons _ _ => simp at h
  | cons ξ ξs ih =>
      cases ψs with
      | nil => simp at h
      | cons ψ ψs =>
          simp [List.map] at h
          obtain ⟨θ, h1, h2⟩ :=
            mapConst_weaken_preimage (Base := Base) f h.1
          obtain ⟨θs, hs1, hs2⟩ := ih ψs h.2
          exact ⟨θ :: θs,
            by simp [List.map, h1, hs1],
            by simp [List.map, h2, hs2]⟩

private theorem mapConst_lift_apply (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (σs : Subst Const Γ Δ) (index : Var (σ :: Γ) τ) :
    mapConst f (Subst.lift σs index) = Subst.lift (fun v => mapConst f (σs v)) index :=
  Subst.lift_map_apply σs (mapConst f) (mapConst f) rfl (mapConst_weaken f) index

theorem mapConst_subst (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (σs : Subst Const Γ Δ) (t : Term Const Γ τ) :
    mapConst f (subst σs t) =
      subst (fun v => mapConst f (σs v)) (mapConst f t) := by
  induction t generalizing Δ <;> simp [subst, mapConst, *, mapConst_lift_apply]

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

/-- Weaken a closed term to an arbitrary context by iterated weakening. -/
def weakenCtx : (Γ : Ctx Base) → ClosedTerm Const τ → Term Const Γ τ
  | [], t => t
  | _ :: Γ, t => weaken (weakenCtx Γ t)

@[simp] theorem weakenCtx_nil (t : ClosedTerm Const τ) :
    weakenCtx ([] : Ctx Base) t = t := rfl

@[simp] theorem weakenCtx_cons (t : ClosedTerm Const τ) :
    weakenCtx (σ :: Γ) t = weaken (weakenCtx Γ t) := rfl

theorem weakenCtx_weaken (t : ClosedTerm Const τ) :
    weaken (Base := Base) (σ := σ) (weakenCtx Γ t) = weakenCtx (σ :: Γ) t := rfl

@[simp] theorem weakenCtx_const (Γ : Ctx Base) (c : Const τ) :
    weakenCtx Γ (.const c : ClosedTerm Const τ) = (.const c : Term Const Γ τ) := by
  induction Γ with
  | nil =>
      rfl
  | cons σ Γ ih =>
      simpa [weakenCtx, weaken, rename] using
        congrArg (weaken (Base := Base) (Const := Const) (σ := σ)) ih

/-- Replace each constant in a term with its image under `f`, weakened to the context.

    Unlike `mapConst` which maps constants to constants, `substConst` maps each
    constant `c : Const τ` to a closed term `f c : ClosedTerm Const' τ`, then
    weakens it to the current context. -/
def substConst (f : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const' τ) :
    {Γ : Ctx Base} → Term Const Γ τ → Term Const' Γ τ
  | _, .var v => .var v
  | Γ, .const c => weakenCtx Γ (f c)
  | _, .app g t => .app (substConst f g) (substConst f t)
  | _, .lam t => .lam (substConst f t)
  | _, .top => .top
  | _, .bot => .bot
  | _, .and φ ψ => .and (substConst f φ) (substConst f ψ)
  | _, .or φ ψ => .or (substConst f φ) (substConst f ψ)
  | _, .imp φ ψ => .imp (substConst f φ) (substConst f ψ)
  | _, .not φ => .not (substConst f φ)
  | _, .eq t u => .eq (substConst f t) (substConst f u)
  | _, .all φ => .all (substConst f φ)
  | _, .ex φ => .ex (substConst f φ)

@[simp] theorem substConst_var (f : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const' τ)
    (v : Var Γ τ) :
    substConst f (.var v : Term Const Γ τ) = .var v := rfl

/-- `weakenCtx` commutes with `rename` on closed terms.
    Both `rename ρ (weakenCtx Γ t)` and `weakenCtx Δ t` are the same closed term
    embedded into context Δ. -/
private theorem rename_closed_vacuous
    {τ : Ty Base} (t : ClosedTerm Const τ)
    (Δ' : Ctx Base) (ρ : Rename Base [] Δ') :
    rename ρ t = weakenCtx Δ' t := by
  revert ρ
  induction Δ' with
  | nil =>
      intro ρ
      simp only [weakenCtx]
      have h :
          rename ρ t = rename (Rename.id (Base := Base) (Γ := [])) t := by
        apply rename_ext
        intro τ v
        nomatch v
      simpa [rename_id] using h
  | cons σ Δ ih =>
      intro ρ
      simp only [weakenCtx, weaken]
      have vacuous : Rename Base [] Δ := fun v => nomatch (v : Var [] _)
      calc
        rename ρ t
            = rename (fun {τ} v => Rename.weaken (Γ := Δ) (σ := σ) (vacuous v)) t :=
          @rename_ext Base Const [] (σ :: Δ) τ ρ _ (fun v => nomatch (v : Var [] _)) t
        _ = rename Rename.weaken (rename vacuous t) :=
          (rename_comp Rename.weaken vacuous t).symm
        _ = rename Rename.weaken (weakenCtx Δ t) := by
          rw [ih vacuous]
        _ = weakenCtx (σ :: Δ) t := rfl

theorem rename_weakenCtx {Γ' Δ' : Ctx Base} (ρ : Rename Base Γ' Δ')
    {τ : Ty Base} (t : ClosedTerm Const τ) :
    rename ρ (weakenCtx Γ' t) = weakenCtx Δ' t := by
  induction Γ' generalizing Δ' with
  | nil =>
      simp only [weakenCtx]
      exact rename_closed_vacuous t Δ' ρ
  | cons σ' Γ ih =>
      simp only [weakenCtx, weaken, rename_comp]
      exact ih (fun {_τ} v => ρ (Rename.weaken v))

private theorem lift_ofRename_eq (ρ : Rename Base Γ Δ) :
    (Subst.lift (σ := σ) (Subst.ofRename ρ) : Subst Const (σ :: Γ) (σ :: Δ)) =
      (Subst.ofRename (Rename.lift ρ) : Subst Const (σ :: Γ) (σ :: Δ)) := by
  funext type index
  cases index <;> rfl

@[simp] theorem subst_ofRename
    {Γ' Δ' : Ctx Base}
    (ρ : Rename Base Γ' Δ') :
    ∀ {τ : Ty Base} (t : Term Const Γ' τ),
      subst (Subst.ofRename (Base := Base) (Const := Const) ρ) t = rename ρ t := by
  intro type term
  induction term generalizing Δ' <;> simp [subst, rename, *, lift_ofRename_eq, Subst.ofRename]

/-- Closed terms ignore the specific substitution chosen out of `[]`. -/
private theorem subst_closed_vacuous
    {τ : Ty Base} (t : ClosedTerm Const τ)
    (Δ' : Ctx Base) (σs : Subst Const [] Δ') :
    subst σs t = weakenCtx Δ' t := by
  have vacuous : Rename Base [] Δ' := fun v => nomatch (v : Var [] _)
  calc
    subst σs t
      = subst (Subst.ofRename (Base := Base) (Const := Const) vacuous) t := by
          apply subst_ext
          intro τ v
          nomatch v
    _ = rename vacuous t := by
          exact subst_ofRename vacuous t
    _ = weakenCtx Δ' t := rename_closed_vacuous t Δ' vacuous

/-- `weakenCtx` also commutes with arbitrary substitutions on closed terms. -/
theorem subst_weakenCtx {Γ' Δ' : Ctx Base} (σs : Subst Const Γ' Δ')
    {τ : Ty Base} (t : ClosedTerm Const τ) :
    subst σs (weakenCtx Γ' t) = weakenCtx Δ' t := by
  induction Γ' generalizing Δ' with
  | nil =>
      simpa [weakenCtx] using subst_closed_vacuous (Base := Base) (Const := Const) t Δ' σs
  | cons σ' Γ ih =>
      calc
        subst σs (weakenCtx (σ' :: Γ) t)
          = subst σs (weaken (Base := Base) (Const := Const) (σ := σ') (weakenCtx Γ t)) := rfl
        _ =
            subst
              (fun {τ} v => σs (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ') v))
              (weakenCtx Γ t) := by
                simpa [weaken] using
                  (subst_rename (Base := Base) (Const := Const)
                    (σs := σs)
                    (ρ := Rename.weaken (Base := Base) (Γ := Γ) (σ := σ'))
                    (t := weakenCtx Γ t))
        _ = weakenCtx Δ' t := by
              exact ih (fun {_τ} v => σs (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ') v))

/-- substConst commutes with rename. -/
theorem substConst_rename (f : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const' τ)
    {Γ' Δ' : Ctx Base} (ρ : Rename Base Γ' Δ') :
    ∀ {τ : Ty Base} (t : Term Const Γ' τ),
      substConst f (rename ρ t) = rename ρ (substConst f t) := by
  intro type term
  induction term generalizing Δ' <;> simp [substConst, rename, *, rename_weakenCtx]

@[simp] theorem substConst_weaken (f : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const' τ)
    {Γ' : Ctx Base} {σ' : Ty Base} (t : Term Const Γ' τ) :
    substConst f (weaken (Base := Base) (σ := σ') t) =
      weaken (Base := Base) (σ := σ') (substConst f t) :=
  substConst_rename f Rename.weaken t

private theorem substConst_lift_apply (f : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const' τ)
    (σs : Subst Const Γ Δ) (index : Var (σ :: Γ) τ) :
    substConst f (Subst.lift σs index) = Subst.lift (fun v => substConst f (σs v)) index :=
  Subst.lift_map_apply σs (substConst f) (substConst f) rfl (substConst_weaken f) index

/-- substConst commutes with arbitrary variable substitution. -/
theorem substConst_subst
    (f : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const' τ)
    {Γ' Δ' : Ctx Base} (σs : Subst Const Γ' Δ') :
    ∀ {τ : Ty Base} (t : Term Const Γ' τ),
      subst (fun {_} v => substConst f (σs v)) (substConst f t) =
        substConst f (subst σs t) := by
  intro type term
  symm
  induction term generalizing Δ' <;>
    simp [substConst, subst, *, subst_weakenCtx, substConst_lift_apply]

@[simp] theorem substConst_instantiate
    (f : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const' τ)
    {Γ' : Ctx Base} {σ' : Ty Base}
    (t : Term Const Γ' σ') (u : Term Const (σ' :: Γ') τ) :
    substConst f (instantiate (Base := Base) t u) =
      instantiate (Base := Base) (substConst f t) (substConst f u) := by
  unfold instantiate
  calc
    substConst f (subst (Subst.single (Base := Base) (Const := Const) t) u)
      =
    subst
      (fun {τ} v =>
        substConst f ((Subst.single (Base := Base) (Const := Const) t) v))
      (substConst f u) := by
        symm
        exact substConst_subst
          (Base := Base)
          (Const := Const)
          (Const' := Const')
          f
          (Subst.single (Base := Base) (Const := Const) t)
          u
    _ =
    subst
      (Subst.single (Base := Base) (Const := Const')
        (substConst f t))
      (substConst f u) := by
        apply subst_ext
        intro τ v
        cases v with
        | vz => rfl
        | vs v => rfl
    _ = instantiate (Base := Base) (substConst f t) (substConst f u) := rfl

end Mettapedia.Logic.HOL
