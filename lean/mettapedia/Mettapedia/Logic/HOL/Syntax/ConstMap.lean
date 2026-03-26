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

/-- Separation lemma: `mapConst` and `rename` act on orthogonal parts
    of a term (constants vs. variables). If `mapConst f ξ = rename ρ ψ`,
    then `ξ` is `rename ρ θ` for some `θ` with `mapConst f θ = ψ`.

    This is the key lemma for staged weakening inversion: if the lift
    of a staged term equals a weakened infinity term, the staged term
    is itself weakened. -/
theorem mapConst_rename_preimage (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (ρ : Rename Base Γ Δ) :
    ∀ (ξ : Term Const Δ τ) (ψ : Term Const' Γ τ),
    mapConst (fun {τ} => f) ξ = rename (fun {τ} => ρ) ψ →
    ∃ θ : Term Const Γ τ, ξ = rename (fun {τ} => ρ) θ ∧
      mapConst (fun {τ} => f) θ = ψ := by
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
    (h : mapConst (fun {τ} => f) ξ =
      weaken (Base := Base) (σ := σ) ψ) :
    ∃ θ : Term Const Γ τ, ξ = weaken (Base := Base) (σ := σ) θ ∧
      mapConst (fun {τ} => f) θ = ψ :=
  mapConst_rename_preimage f Rename.weaken ξ ψ h

/-- List-level version: if `ξs.map (mapConst f) = ψs.map weaken`,
    recover `θs` with `ξs = θs.map weaken` and `θs.map (mapConst f) = ψs`. -/
theorem map_mapConst_eq_map_weaken_preimage
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    {Γ : Ctx Base} {σ : Ty Base} :
    ∀ (ξs : List (Term Const (σ :: Γ) propTy))
      (ψs : List (Term Const' Γ propTy)),
    ξs.map (mapConst (fun {τ} => f)) =
      ψs.map (weaken (Base := Base) (σ := σ)) →
    ∃ θs : List (Term Const Γ propTy),
      ξs = θs.map (weaken (Base := Base) (σ := σ)) ∧
      θs.map (mapConst (fun {τ} => f)) = ψs := by
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
