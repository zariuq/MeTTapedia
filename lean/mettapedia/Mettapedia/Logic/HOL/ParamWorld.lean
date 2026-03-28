import Mettapedia.Logic.HOL.DerivationExtensionality
import Mettapedia.Logic.HOL.Syntax.ConstMap
import Mettapedia.Logic.HOL.PrimeHenkinExtension

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u}

/-!
# Growing-Domain Kripke Model Infrastructure  [MAINLINE]

This file defines the parameterized-signature approach to plain intuitionistic
HOL completeness for **arbitrary original signatures**, including empty ones
where base types have no closed terms.

The construction follows Troelstra & van Dalen / Fitting (1969): worlds carry
local parameter contexts, and domains grow as contexts extend. This avoids the
`∃x:b.⊤` obstruction that makes the global HInf bridge impossible for plain
completeness (see `OriginalReflectionObstruction.lean`).

## Key definitions

- `ParamConst`: extend a signature with parameter constants from a context
- `liftParam` / `liftParamFormula`: embed original-signature terms/formulas
- `ExtDerivation.mapConst`: transport derivations along signature morphisms
- `mapConst_weakenHyps`: `mapConst` commutes with hypothesis weakening
-/

section ParamConst

variable {Const : Ty Base → Type v}

/-- Extend a signature with parameter constants drawn from a typing context.

Each variable `v : Var Γ τ` in the context becomes a fresh constant symbol
`Sum.inr v : ParamConst Const Γ τ`. Original constants are embedded as
`Sum.inl c`. -/
def ParamConst (Const : Ty Base → Type v) (Γ : Ctx Base) (τ : Ty Base) : Type (max u v) :=
  Const τ ⊕ Var (Base := Base) Γ τ

/-- Embed an original constant into the parameterized signature. -/
abbrev ParamConst.base (c : Const τ) : ParamConst Const Γ τ := Sum.inl c

/-- Create a parameter constant from a context variable. -/
abbrev ParamConst.param (v : Var (Base := Base) Γ τ) : ParamConst Const Γ τ := Sum.inr v

/-- Lift an original-signature term to the parameterized signature. -/
abbrev liftParam {Γ' : Ctx Base} : Term Const Γ τ → Term (ParamConst Const Γ') Γ τ :=
  mapConst (fun c => Sum.inl c)

/-- Lift a closed formula to the parameterized signature. -/
abbrev liftParamFormula (Γ' : Ctx Base) (φ : ClosedFormula Const) :
    ClosedFormula (ParamConst Const Γ') :=
  mapConst (fun c => Sum.inl c) φ

/-- Lift a closed term to the parameterized signature. -/
abbrev liftParamTerm (Γ' : Ctx Base) {τ : Ty Base} (t : ClosedTerm Const τ) :
    ClosedTerm (ParamConst Const Γ') τ :=
  mapConst (fun c => Sum.inl c) t

@[simp] theorem liftParam_var {Γ' : Ctx Base} (v : Var (Base := Base) Γ τ) :
    (liftParam (Γ' := Γ') (.var v : Term Const Γ τ)) = .var v := rfl

@[simp] theorem liftParam_const {Γ' : Ctx Base} (c : Const τ) :
    (liftParam (Γ' := Γ') (.const c : Term Const Γ τ)) =
      .const (ParamConst.base c) := rfl

@[simp] theorem liftParam_top {Γ' : Ctx Base} :
    (liftParam (Γ' := Γ') (.top : Formula Const Γ)) = .top := rfl

@[simp] theorem liftParam_bot {Γ' : Ctx Base} :
    (liftParam (Γ' := Γ') (.bot : Formula Const Γ)) = .bot := rfl

@[simp] theorem liftParam_and {Γ' : Ctx Base} {φ ψ : Formula Const Γ} :
    (liftParam (Γ' := Γ') (.and φ ψ)) =
      .and (liftParam φ) (liftParam ψ) := rfl

@[simp] theorem liftParam_or {Γ' : Ctx Base} {φ ψ : Formula Const Γ} :
    (liftParam (Γ' := Γ') (.or φ ψ)) =
      .or (liftParam φ) (liftParam ψ) := rfl

@[simp] theorem liftParam_imp {Γ' : Ctx Base} {φ ψ : Formula Const Γ} :
    (liftParam (Γ' := Γ') (.imp φ ψ)) =
      .imp (liftParam φ) (liftParam ψ) := rfl

@[simp] theorem liftParam_not {Γ' : Ctx Base} {φ : Formula Const Γ} :
    (liftParam (Γ' := Γ') (.not φ)) = .not (liftParam φ) := rfl

@[simp] theorem liftParam_eq {Γ' : Ctx Base} {t u : Term Const Γ τ} :
    (liftParam (Γ' := Γ') (.eq t u)) = .eq (liftParam t) (liftParam u) := rfl

@[simp] theorem liftParam_all {Γ' : Ctx Base} {σ : Ty Base} {φ : Formula Const (σ :: Γ)} :
    (liftParam (Γ' := Γ') (.all φ : Formula Const Γ)) =
      .all (liftParam φ) := rfl

@[simp] theorem liftParam_ex {Γ' : Ctx Base} {σ : Ty Base} {φ : Formula Const (σ :: Γ)} :
    (liftParam (Γ' := Γ') (.ex φ : Formula Const Γ)) =
      .ex (liftParam φ) := rfl

@[simp] theorem liftParam_app {Γ' : Ctx Base}
    {g : Term Const Γ (σ ⇒ τ)} {t : Term Const Γ σ} :
    (liftParam (Γ' := Γ') (.app g t)) = .app (liftParam g) (liftParam t) := rfl

@[simp] theorem liftParam_lam {Γ' : Ctx Base} {t : Term Const (σ :: Γ) τ} :
    (liftParam (Γ' := Γ') (.lam t : Term Const Γ (σ ⇒ τ))) =
      .lam (liftParam t) := rfl

/-- `liftParam` commutes with `weaken`. -/
@[simp] theorem liftParam_weaken {Γ' : Ctx Base}
    {t : Term Const Γ τ} :
    liftParam (Γ' := Γ') (weaken (Base := Base) (σ := σ) t) =
      weaken (liftParam t) :=
  mapConst_weaken _ t

/-- `liftParam` commutes with `instantiate`. -/
@[simp] theorem liftParam_instantiate {Γ' : Ctx Base}
    {t : Term Const Γ σ} {u : Term Const (σ :: Γ) τ} :
    liftParam (Γ' := Γ') (instantiate t u) =
      instantiate (liftParam t) (liftParam u) :=
  mapConst_instantiate _ t u

/-- Lifting hypothesis lists commutes with `liftParam`. -/
theorem liftParam_weakenHyps {Γ' : Ctx Base}
    {σ : Ty Base} {Δ : List (Formula Const Γ)} :
    (weakenHyps (Base := Base) (σ := σ) Δ).map (liftParam (Γ' := Γ')) =
      weakenHyps (Δ.map (liftParam (Γ' := Γ'))) := by
  simp [weakenHyps, List.map_map]

end ParamConst

-- Note: `ExtDerivation.mapConst` already exists in `DerivationExtensionality.lean`
-- and transports derivations along constant-symbol maps. We reuse it directly.

/-! ## Parameter context extension -/

section ParamExtension

variable {Const : Ty Base → Type v}

/-- Embed `ParamConst Const Γ` into `ParamConst Const (σ :: Γ)` by weakening
the de Bruijn variable index. Original constants stay unchanged. -/
def paramWeaken {Γ : Ctx Base} {σ : Ty Base} :
    ∀ {τ : Ty Base}, ParamConst Const Γ τ → ParamConst Const (σ :: Γ) τ
  | _, Sum.inl c => Sum.inl c
  | _, Sum.inr v => Sum.inr (.vs v)

/-- The fresh parameter constant introduced by extending context `Γ` with type `σ`. -/
def freshParam (Γ : Ctx Base) (σ : Ty Base) : ParamConst Const (σ :: Γ) σ :=
  Sum.inr .vz

/-- `paramWeaken` is injective. -/
theorem paramWeaken_injective {Γ : Ctx Base} {σ τ : Ty Base}
    {c₁ c₂ : ParamConst Const Γ τ}
    (h : paramWeaken (σ := σ) c₁ = paramWeaken c₂) : c₁ = c₂ := by
  rcases c₁ with c₁ | v₁ <;> rcases c₂ with c₂ | v₂ <;>
    simp only [paramWeaken] at h
  · exact congrArg Sum.inl (Sum.inl.inj h)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact congrArg Sum.inr (Var.vs.inj (Sum.inr.inj h))

/-- Lift a term from `ParamConst Const Γ` to `ParamConst Const (σ :: Γ)`. -/
abbrev liftParamCtx {Γ : Ctx Base} {σ : Ty Base} :
    Term (ParamConst Const Γ) Γ' τ → Term (ParamConst Const (σ :: Γ)) Γ' τ :=
  mapConst paramWeaken

/-- Lift a closed formula from `ParamConst Const Γ` to `ParamConst Const (σ :: Γ)`. -/
abbrev liftParamCtxFormula {Γ : Ctx Base} (σ : Ty Base) :
    ClosedFormula (ParamConst Const Γ) → ClosedFormula (ParamConst Const (σ :: Γ)) :=
  mapConst paramWeaken

/-- `liftParam` factors through `paramWeaken`. Lifting directly from `Const`
to `ParamConst Const (σ :: Γ)` equals first lifting to `ParamConst Const Γ`
then weakening. -/
theorem liftParam_eq_liftParamCtx_comp {Γ : Ctx Base} {σ : Ty Base}
    (t : Term Const Γ' τ) :
    liftParam (Γ' := σ :: Γ) t = liftParamCtx (σ := σ) (liftParam (Γ' := Γ) t) := by
  induction t with
  | var v => rfl
  | const c => rfl
  | app _ _ ih₁ ih₂ => simp [liftParam, liftParamCtx, mapConst, ih₁, ih₂]
  | lam _ ih => simp [liftParam, liftParamCtx, mapConst, ih]
  | top => rfl
  | bot => rfl
  | and _ _ ih₁ ih₂ => simp [liftParam, liftParamCtx, mapConst, ih₁, ih₂]
  | or _ _ ih₁ ih₂ => simp [liftParam, liftParamCtx, mapConst, ih₁, ih₂]
  | imp _ _ ih₁ ih₂ => simp [liftParam, liftParamCtx, mapConst, ih₁, ih₂]
  | not _ ih => simp [liftParam, liftParamCtx, mapConst, ih]
  | eq _ _ ih₁ ih₂ => simp [liftParam, liftParamCtx, mapConst, ih₁, ih₂]
  | all _ ih => simp [liftParam, liftParamCtx, mapConst, ih]
  | ex _ ih => simp [liftParam, liftParamCtx, mapConst, ih]

/-- Lift a derivation from `ParamConst Const Γ` to `ParamConst Const (σ :: Γ)`. -/
theorem liftParamCtx_derivation {Γ : Ctx Base} {σ : Ty Base}
    {Δ : List (ClosedFormula (ParamConst Const Γ))}
    {φ : ClosedFormula (ParamConst Const Γ)}
    (d : ExtDerivation (ParamConst Const Γ) Δ φ) :
    ExtDerivation (ParamConst Const (σ :: Γ))
      (Δ.map (liftParamCtxFormula σ))
      (liftParamCtxFormula σ φ) :=
  ExtDerivation.mapConst paramWeaken d

/-- Lifting a derivation preserves provability from a theory set. -/
theorem liftParamCtx_provable {Γ : Ctx Base} {σ : Ty Base}
    {T : ClosedTheorySet (ParamConst Const Γ)}
    {φ : ClosedFormula (ParamConst Const Γ)}
    (hProv : ClosedTheorySet.Provable T φ) :
    ClosedTheorySet.Provable
      (Const := ParamConst Const (σ :: Γ))
      (fun ψ => ∃ χ ∈ T, liftParamCtxFormula σ χ = ψ)
      (liftParamCtxFormula σ φ) := by
  rcases hProv with ⟨support, hSup, d⟩
  exact ⟨support.map (liftParamCtxFormula σ),
    fun ψ hψ => by
      simp [List.mem_map] at hψ
      rcases hψ with ⟨χ, hχ, rfl⟩
      exact ⟨χ, hSup χ hχ, rfl⟩,
    liftParamCtx_derivation d⟩

end ParamExtension

/-! ## Parameters as local variables -/

section ParamAsVars

variable {Const : Ty Base → Type v}

/-- Embed the local context `Γ` as the left prefix of `Γ ++ Ξ`. -/
def keepPrefixRen : {Γ Ξ : Ctx Base} → Rename Base Γ (Γ ++ Ξ)
  | [], _ => fun v => nomatch v
  | _ :: Γ, Ξ => fun
      | .vz => .vz
      | .vs v => .vs (keepPrefixRen (Γ := Γ) (Ξ := Ξ) v)

/-- Embed the parameter context `Ξ` as the right suffix of `Γ ++ Ξ`. -/
def keepSuffixVar : {Γ Ξ : Ctx Base} → {τ : Ty Base} → Var Ξ τ → Var (Γ ++ Ξ) τ
  | [], _, _, v => by simpa using v
  | _ :: Γ, Ξ, _, v => .vs (keepSuffixVar (Γ := Γ) (Ξ := Ξ) v)

/-- Split a variable of `Γ ++ Ξ` into either the left `Γ` part or the right `Ξ` part. -/
def splitAppendVar : {Γ Ξ : Ctx Base} → {τ : Ty Base} → Var (Γ ++ Ξ) τ → Sum (Var Γ τ) (Var Ξ τ)
  | [], _, _, v => .inr (by simpa using v)
  | _ :: Γ, Ξ, _, .vz => .inl .vz
  | _ :: Γ, Ξ, _, .vs v =>
      match splitAppendVar (Γ := Γ) (Ξ := Ξ) v with
      | .inl v' => .inl (.vs v')
      | .inr v' => .inr v'

@[simp] theorem splitAppendVar_keepPrefixRen
    : {Γ Ξ : Ctx Base} → {τ : Ty Base} → (v : Var Γ τ) →
      splitAppendVar (Γ := Γ) (Ξ := Ξ) (keepPrefixRen (Γ := Γ) (Ξ := Ξ) v) = Sum.inl v
  | [], _, _, v => nomatch v
  | _ :: _, _, _, .vz => rfl
  | _ :: Γ, Ξ, _, .vs v => by
      change
        (match splitAppendVar (Γ := Γ) (Ξ := Ξ) (keepPrefixRen (Γ := Γ) (Ξ := Ξ) v) with
        | Sum.inl v' => Sum.inl (Var.vs v')
        | Sum.inr v' => Sum.inr v') = Sum.inl (Var.vs v)
      rw [splitAppendVar_keepPrefixRen (Γ := Γ) (Ξ := Ξ) v]

@[simp] theorem splitAppendVar_keepSuffixVar
    : {Γ Ξ : Ctx Base} → {τ : Ty Base} → (v : Var Ξ τ) →
      splitAppendVar (Γ := Γ) (Ξ := Ξ) (keepSuffixVar (Γ := Γ) (Ξ := Ξ) v) = Sum.inr v
  | [], _, _, v => by
      simp [keepSuffixVar, splitAppendVar]
  | _ :: Γ, Ξ, _, v => by
      change
        (match splitAppendVar (Γ := Γ) (Ξ := Ξ) (keepSuffixVar (Γ := Γ) (Ξ := Ξ) v) with
        | Sum.inl v' => Sum.inl (Var.vs v')
        | Sum.inr v' => Sum.inr v') = Sum.inr v
      rw [splitAppendVar_keepSuffixVar (Γ := Γ) (Ξ := Ξ) v]

theorem keepPrefixRen_or_keepSuffixVar_of_splitAppendVar
    : {Γ Ξ : Ctx Base} → {τ : Ty Base} → (v : Var (Γ ++ Ξ) τ) →
      match splitAppendVar (Γ := Γ) (Ξ := Ξ) v with
      | Sum.inl v' => keepPrefixRen (Γ := Γ) (Ξ := Ξ) v' = v
      | Sum.inr v' => keepSuffixVar (Γ := Γ) (Ξ := Ξ) v' = v
  | [], _, _, v => by
      simp [splitAppendVar, keepSuffixVar]
  | _ :: _, _, _, .vz => rfl
  | _ :: Γ, Ξ, _, .vs v => by
      cases h : splitAppendVar (Γ := Γ) (Ξ := Ξ) v with
      | inl v' =>
          have ih := keepPrefixRen_or_keepSuffixVar_of_splitAppendVar (Γ := Γ) (Ξ := Ξ) v
          rw [h] at ih
          simp [splitAppendVar, keepPrefixRen, h, ih]
      | inr v' =>
          have ih := keepPrefixRen_or_keepSuffixVar_of_splitAppendVar (Γ := Γ) (Ξ := Ξ) v
          rw [h] at ih
          simp [splitAppendVar, keepSuffixVar, h, ih]

/-- Reinterpret parameter constants as free variables in the suffix context `Ξ`. -/
def paramToOpen : {Ξ Γ : Ctx Base} → Term (ParamConst Const Ξ) Γ τ → Term Const (Γ ++ Ξ) τ
  | Ξ, Γ, .var v => .var (keepPrefixRen (Γ := Γ) (Ξ := Ξ) v)
  | Ξ, Γ, .const (.inl c) => .const c
  | Ξ, Γ, .const (.inr v) => .var (keepSuffixVar (Γ := Γ) (Ξ := Ξ) v)
  | Ξ, Γ, .app f t => .app (paramToOpen (Ξ := Ξ) (Γ := Γ) f) (paramToOpen (Ξ := Ξ) (Γ := Γ) t)
  | Ξ, Γ, .lam t => .lam (paramToOpen (Ξ := Ξ) (Γ := _ :: Γ) t)
  | Ξ, Γ, .top => .top
  | Ξ, Γ, .bot => .bot
  | Ξ, Γ, .and φ ψ => .and (paramToOpen (Ξ := Ξ) (Γ := Γ) φ) (paramToOpen (Ξ := Ξ) (Γ := Γ) ψ)
  | Ξ, Γ, .or φ ψ => .or (paramToOpen (Ξ := Ξ) (Γ := Γ) φ) (paramToOpen (Ξ := Ξ) (Γ := Γ) ψ)
  | Ξ, Γ, .imp φ ψ => .imp (paramToOpen (Ξ := Ξ) (Γ := Γ) φ) (paramToOpen (Ξ := Ξ) (Γ := Γ) ψ)
  | Ξ, Γ, .not φ => .not (paramToOpen (Ξ := Ξ) (Γ := Γ) φ)
  | Ξ, Γ, .eq t u => .eq (paramToOpen (Ξ := Ξ) (Γ := Γ) t) (paramToOpen (Ξ := Ξ) (Γ := Γ) u)
  | Ξ, Γ, .all φ => .all (paramToOpen (Ξ := Ξ) (Γ := _ :: Γ) φ)
  | Ξ, Γ, .ex φ => .ex (paramToOpen (Ξ := Ξ) (Γ := _ :: Γ) φ)

/-- Reinterpret suffix variables of `Γ ++ Ξ` as parameter constants from `Ξ`. -/
def openToParam : {Ξ Γ : Ctx Base} → Term Const (Γ ++ Ξ) τ → Term (ParamConst Const Ξ) Γ τ
  | Ξ, Γ, .var v =>
      match splitAppendVar (Γ := Γ) (Ξ := Ξ) v with
      | .inl v' => .var v'
      | .inr v' => .const (.inr v')
  | Ξ, Γ, .const c => .const (.inl c)
  | Ξ, Γ, .app f t => .app (openToParam (Ξ := Ξ) (Γ := Γ) f) (openToParam (Ξ := Ξ) (Γ := Γ) t)
  | Ξ, Γ, .lam t => .lam (openToParam (Ξ := Ξ) (Γ := _ :: Γ) t)
  | Ξ, Γ, .top => .top
  | Ξ, Γ, .bot => .bot
  | Ξ, Γ, .and φ ψ => .and (openToParam (Ξ := Ξ) (Γ := Γ) φ) (openToParam (Ξ := Ξ) (Γ := Γ) ψ)
  | Ξ, Γ, .or φ ψ => .or (openToParam (Ξ := Ξ) (Γ := Γ) φ) (openToParam (Ξ := Ξ) (Γ := Γ) ψ)
  | Ξ, Γ, .imp φ ψ => .imp (openToParam (Ξ := Ξ) (Γ := Γ) φ) (openToParam (Ξ := Ξ) (Γ := Γ) ψ)
  | Ξ, Γ, .not φ => .not (openToParam (Ξ := Ξ) (Γ := Γ) φ)
  | Ξ, Γ, .eq t u => .eq (openToParam (Ξ := Ξ) (Γ := Γ) t) (openToParam (Ξ := Ξ) (Γ := Γ) u)
  | Ξ, Γ, .all φ => .all (openToParam (Ξ := Ξ) (Γ := _ :: Γ) φ)
  | Ξ, Γ, .ex φ => .ex (openToParam (Ξ := Ξ) (Γ := _ :: Γ) φ)

@[simp] theorem openToParam_paramToOpen
    : {Ξ Γ : Ctx Base} → {τ : Ty Base} → (t : Term (ParamConst Const Ξ) Γ τ) →
      openToParam (Ξ := Ξ) (Γ := Γ) (paramToOpen (Ξ := Ξ) (Γ := Γ) t) = t
  | _, _, _, .var v => by
      simp [paramToOpen, openToParam]
  | _, _, _, .const (.inl c) => by
      simp [paramToOpen, openToParam]
  | _, _, _, .const (.inr v) => by
      simp [paramToOpen, openToParam]
  | Ξ, Γ, _, .app f t => by
      simp [paramToOpen, openToParam,
        openToParam_paramToOpen (Ξ := Ξ) (Γ := Γ) f,
        openToParam_paramToOpen (Ξ := Ξ) (Γ := Γ) t]
  | Ξ, Γ, _, .lam t => by
      simp [paramToOpen, openToParam,
        openToParam_paramToOpen (Ξ := Ξ) (Γ := _ :: Γ) t]
  | _, _, _, .top => by
      simp [paramToOpen, openToParam]
  | _, _, _, .bot => by
      simp [paramToOpen, openToParam]
  | Ξ, Γ, _, .and φ ψ => by
      simp [paramToOpen, openToParam,
        openToParam_paramToOpen (Ξ := Ξ) (Γ := Γ) φ,
        openToParam_paramToOpen (Ξ := Ξ) (Γ := Γ) ψ]
  | Ξ, Γ, _, .or φ ψ => by
      simp [paramToOpen, openToParam,
        openToParam_paramToOpen (Ξ := Ξ) (Γ := Γ) φ,
        openToParam_paramToOpen (Ξ := Ξ) (Γ := Γ) ψ]
  | Ξ, Γ, _, .imp φ ψ => by
      simp [paramToOpen, openToParam,
        openToParam_paramToOpen (Ξ := Ξ) (Γ := Γ) φ,
        openToParam_paramToOpen (Ξ := Ξ) (Γ := Γ) ψ]
  | Ξ, Γ, _, .not φ => by
      simp [paramToOpen, openToParam,
        openToParam_paramToOpen (Ξ := Ξ) (Γ := Γ) φ]
  | Ξ, Γ, _, .eq t u => by
      simp [paramToOpen, openToParam,
        openToParam_paramToOpen (Ξ := Ξ) (Γ := Γ) t,
        openToParam_paramToOpen (Ξ := Ξ) (Γ := Γ) u]
  | Ξ, Γ, _, .all φ => by
      simp [paramToOpen, openToParam,
        openToParam_paramToOpen (Ξ := Ξ) (Γ := _ :: Γ) φ]
  | Ξ, Γ, _, .ex φ => by
      simp [paramToOpen, openToParam,
        openToParam_paramToOpen (Ξ := Ξ) (Γ := _ :: Γ) φ]

@[simp] theorem paramToOpen_openToParam
    : {Ξ Γ : Ctx Base} → {τ : Ty Base} → (t : Term Const (Γ ++ Ξ) τ) →
      paramToOpen (Ξ := Ξ) (Γ := Γ) (openToParam (Ξ := Ξ) (Γ := Γ) t) = t
  | Ξ, Γ, _, .var v => by
      cases h : splitAppendVar (Γ := Γ) (Ξ := Ξ) v with
      | inl v' =>
          have hs := keepPrefixRen_or_keepSuffixVar_of_splitAppendVar (Γ := Γ) (Ξ := Ξ) v
          rw [h] at hs
          simp [openToParam, paramToOpen, h, hs]
      | inr v' =>
          have hs := keepPrefixRen_or_keepSuffixVar_of_splitAppendVar (Γ := Γ) (Ξ := Ξ) v
          rw [h] at hs
          simp [openToParam, paramToOpen, h, hs]
  | _, _, _, .const c => by
      simp [paramToOpen, openToParam]
  | Ξ, Γ, _, .app f t => by
      simp [paramToOpen, openToParam,
        paramToOpen_openToParam (Ξ := Ξ) (Γ := Γ) f,
        paramToOpen_openToParam (Ξ := Ξ) (Γ := Γ) t]
  | Ξ, Γ, _, .lam t => by
      simp [paramToOpen, openToParam,
        paramToOpen_openToParam (Ξ := Ξ) (Γ := _ :: Γ) t]
  | _, _, _, .top => by
      simp [paramToOpen, openToParam]
  | _, _, _, .bot => by
      simp [paramToOpen, openToParam]
  | Ξ, Γ, _, .and φ ψ => by
      simp [paramToOpen, openToParam,
        paramToOpen_openToParam (Ξ := Ξ) (Γ := Γ) φ,
        paramToOpen_openToParam (Ξ := Ξ) (Γ := Γ) ψ]
  | Ξ, Γ, _, .or φ ψ => by
      simp [paramToOpen, openToParam,
        paramToOpen_openToParam (Ξ := Ξ) (Γ := Γ) φ,
        paramToOpen_openToParam (Ξ := Ξ) (Γ := Γ) ψ]
  | Ξ, Γ, _, .imp φ ψ => by
      simp [paramToOpen, openToParam,
        paramToOpen_openToParam (Ξ := Ξ) (Γ := Γ) φ,
        paramToOpen_openToParam (Ξ := Ξ) (Γ := Γ) ψ]
  | Ξ, Γ, _, .not φ => by
      simp [paramToOpen, openToParam,
        paramToOpen_openToParam (Ξ := Ξ) (Γ := Γ) φ]
  | Ξ, Γ, _, .eq t u => by
      simp [paramToOpen, openToParam,
        paramToOpen_openToParam (Ξ := Ξ) (Γ := Γ) t,
        paramToOpen_openToParam (Ξ := Ξ) (Γ := Γ) u]
  | Ξ, Γ, _, .all φ => by
      simp [paramToOpen, openToParam,
        paramToOpen_openToParam (Ξ := Ξ) (Γ := _ :: Γ) φ]
  | Ξ, Γ, _, .ex φ => by
      simp [paramToOpen, openToParam,
        paramToOpen_openToParam (Ξ := Ξ) (Γ := _ :: Γ) φ]

theorem paramToOpen_injective {Ξ Γ : Ctx Base} {τ : Ty Base} :
    Function.Injective (paramToOpen (Base := Base) (Const := Const) (Ξ := Ξ) (Γ := Γ) (τ := τ)) := by
  intro t u h
  simpa using congrArg (openToParam (Base := Base) (Const := Const) (Ξ := Ξ) (Γ := Γ) (τ := τ)) h

theorem openToParam_injective {Ξ Γ : Ctx Base} {τ : Ty Base} :
    Function.Injective (openToParam (Base := Base) (Const := Const) (Ξ := Ξ) (Γ := Γ) (τ := τ)) := by
  intro t u h
  simpa using congrArg (paramToOpen (Base := Base) (Const := Const) (Ξ := Ξ) (Γ := Γ) (τ := τ)) h

end ParamAsVars

section FreshParamAsVar

variable {Const : Ty Base → Type v}

/--
Reinterpret the distinguished fresh parameter from `σ :: Γ` as a free variable
at the right edge of the context, while keeping all older parameters from `Γ`
as constants.
-/
def freshParamToVar {Γ : Ctx Base} {σ : Ty Base} :
    {Ξ : Ctx Base} →
      Term (ParamConst Const (σ :: Γ)) Ξ τ →
        Term (ParamConst Const Γ) (Ξ ++ [σ]) τ
  | Ξ, .var v => .var (keepPrefixRen (Γ := Ξ) (Ξ := [σ]) v)
  | _, .const (.inl c) => .const (.inl c)
  | Ξ, .const (.inr .vz) => .var (keepSuffixVar (Γ := Ξ) (Ξ := [σ]) (.vz))
  | _, .const (.inr (.vs v)) => .const (.inr v)
  | Ξ, .app f t => .app
      (freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) f)
      (freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) t)
  | Ξ, .lam t => .lam (freshParamToVar (Γ := Γ) (σ := σ) (Ξ := _ :: Ξ) t)
  | _, .top => .top
  | _, .bot => .bot
  | Ξ, .and φ ψ => .and
      (freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) φ)
      (freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) ψ)
  | Ξ, .or φ ψ => .or
      (freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) φ)
      (freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) ψ)
  | Ξ, .imp φ ψ => .imp
      (freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) φ)
      (freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) ψ)
  | Ξ, .not φ => .not (freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) φ)
  | Ξ, .eq t u => .eq
      (freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) t)
      (freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) u)
  | Ξ, .all φ => .all (freshParamToVar (Γ := Γ) (σ := σ) (Ξ := _ :: Ξ) φ)
  | Ξ, .ex φ => .ex (freshParamToVar (Γ := Γ) (σ := σ) (Ξ := _ :: Ξ) φ)

/--
Inverse translation: reinterpret the final free variable from `Ξ ++ [σ]` as the
distinguished fresh parameter constant from `σ :: Γ`.
-/
def varToFreshParam {Γ : Ctx Base} {σ : Ty Base} :
    {Ξ : Ctx Base} →
      Term (ParamConst Const Γ) (Ξ ++ [σ]) τ →
        Term (ParamConst Const (σ :: Γ)) Ξ τ
  | Ξ, .var v =>
      match splitAppendVar (Γ := Ξ) (Ξ := [σ]) v with
      | .inl v' => .var v'
      | .inr v' =>
          match v' with
          | .vz => .const (.inr .vz)
  | _, .const (.inl c) => .const (.inl c)
  | _, .const (.inr v) => .const (.inr (.vs v))
  | Ξ, .app f t => .app
      (varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) f)
      (varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) t)
  | Ξ, .lam t => .lam (varToFreshParam (Γ := Γ) (σ := σ) (Ξ := _ :: Ξ) t)
  | _, .top => .top
  | _, .bot => .bot
  | Ξ, .and φ ψ => .and
      (varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) φ)
      (varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) ψ)
  | Ξ, .or φ ψ => .or
      (varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) φ)
      (varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) ψ)
  | Ξ, .imp φ ψ => .imp
      (varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) φ)
      (varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) ψ)
  | Ξ, .not φ => .not (varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) φ)
  | Ξ, .eq t u => .eq
      (varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) t)
      (varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) u)
  | Ξ, .all φ => .all (varToFreshParam (Γ := Γ) (σ := σ) (Ξ := _ :: Ξ) φ)
  | Ξ, .ex φ => .ex (varToFreshParam (Γ := Γ) (σ := σ) (Ξ := _ :: Ξ) φ)

@[simp] theorem varToFreshParam_freshParamToVar
    {Γ : Ctx Base} {σ : Ty Base} :
    {Ξ : Ctx Base} → {τ : Ty Base} →
      (t : Term (ParamConst Const (σ :: Γ)) Ξ τ) →
        varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ)
          (freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) t) = t
  | _, _, .var v => by
      simp [freshParamToVar, varToFreshParam]
  | _, _, .const (.inl c) => by
      simp [freshParamToVar, varToFreshParam]
  | _, _, .const (.inr .vz) => by
      simp [freshParamToVar, varToFreshParam]
  | _, _, .const (.inr (.vs v)) => by
      simp [freshParamToVar, varToFreshParam]
  | Ξ, _, .app f t => by
      simp [freshParamToVar, varToFreshParam,
        varToFreshParam_freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) f,
        varToFreshParam_freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) t]
  | Ξ, _, .lam t => by
      simp [freshParamToVar, varToFreshParam,
        varToFreshParam_freshParamToVar (Γ := Γ) (σ := σ) (Ξ := _ :: Ξ) t]
  | _, _, .top => by
      simp [freshParamToVar, varToFreshParam]
  | _, _, .bot => by
      simp [freshParamToVar, varToFreshParam]
  | Ξ, _, .and φ ψ => by
      simp [freshParamToVar, varToFreshParam,
        varToFreshParam_freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) φ,
        varToFreshParam_freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) ψ]
  | Ξ, _, .or φ ψ => by
      simp [freshParamToVar, varToFreshParam,
        varToFreshParam_freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) φ,
        varToFreshParam_freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) ψ]
  | Ξ, _, .imp φ ψ => by
      simp [freshParamToVar, varToFreshParam,
        varToFreshParam_freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) φ,
        varToFreshParam_freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) ψ]
  | Ξ, _, .not φ => by
      simp [freshParamToVar, varToFreshParam,
        varToFreshParam_freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) φ]
  | Ξ, _, .eq t u => by
      simp [freshParamToVar, varToFreshParam,
        varToFreshParam_freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) t,
        varToFreshParam_freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ) u]
  | Ξ, _, .all φ => by
      simp [freshParamToVar, varToFreshParam,
        varToFreshParam_freshParamToVar (Γ := Γ) (σ := σ) (Ξ := _ :: Ξ) φ]
  | Ξ, _, .ex φ => by
      simp [freshParamToVar, varToFreshParam,
        varToFreshParam_freshParamToVar (Γ := Γ) (σ := σ) (Ξ := _ :: Ξ) φ]

@[simp] theorem freshParamToVar_varToFreshParam
    {Γ : Ctx Base} {σ : Ty Base} :
    {Ξ : Ctx Base} → {τ : Ty Base} →
      (t : Term (ParamConst Const Γ) (Ξ ++ [σ]) τ) →
        freshParamToVar (Γ := Γ) (σ := σ) (Ξ := Ξ)
          (varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) t) = t
  | Ξ, _, .var v => by
      cases h : splitAppendVar (Γ := Ξ) (Ξ := [σ]) v with
      | inl v' =>
          have hs := keepPrefixRen_or_keepSuffixVar_of_splitAppendVar (Γ := Ξ) (Ξ := [σ]) v
          rw [h] at hs
          simp [freshParamToVar, varToFreshParam, h, hs]
      | inr v' =>
          cases v' with
          | vz =>
              have hs := keepPrefixRen_or_keepSuffixVar_of_splitAppendVar (Γ := Ξ) (Ξ := [σ]) v
              rw [h] at hs
              simp [freshParamToVar, varToFreshParam, h, hs]
          | vs v'' =>
              cases v''
  | _, _, .const (.inl c) => by
      simp [freshParamToVar, varToFreshParam]
  | _, _, .const (.inr v) => by
      simp [freshParamToVar, varToFreshParam]
  | Ξ, _, .app f t => by
      simp [freshParamToVar, varToFreshParam,
        freshParamToVar_varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) f,
        freshParamToVar_varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) t]
  | Ξ, _, .lam t => by
      simp [freshParamToVar, varToFreshParam,
        freshParamToVar_varToFreshParam (Γ := Γ) (σ := σ) (Ξ := _ :: Ξ) t]
  | _, _, .top => by
      simp [freshParamToVar, varToFreshParam]
  | _, _, .bot => by
      simp [freshParamToVar, varToFreshParam]
  | Ξ, _, .and φ ψ => by
      simp [freshParamToVar, varToFreshParam,
        freshParamToVar_varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) φ,
        freshParamToVar_varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) ψ]
  | Ξ, _, .or φ ψ => by
      simp [freshParamToVar, varToFreshParam,
        freshParamToVar_varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) φ,
        freshParamToVar_varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) ψ]
  | Ξ, _, .imp φ ψ => by
      simp [freshParamToVar, varToFreshParam,
        freshParamToVar_varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) φ,
        freshParamToVar_varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) ψ]
  | Ξ, _, .not φ => by
      simp [freshParamToVar, varToFreshParam,
        freshParamToVar_varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) φ]
  | Ξ, _, .eq t u => by
      simp [freshParamToVar, varToFreshParam,
        freshParamToVar_varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) t,
        freshParamToVar_varToFreshParam (Γ := Γ) (σ := σ) (Ξ := Ξ) u]
  | Ξ, _, .all φ => by
      simp [freshParamToVar, varToFreshParam,
        freshParamToVar_varToFreshParam (Γ := Γ) (σ := σ) (Ξ := _ :: Ξ) φ]
  | Ξ, _, .ex φ => by
      simp [freshParamToVar, varToFreshParam,
        freshParamToVar_varToFreshParam (Γ := Γ) (σ := σ) (Ξ := _ :: Ξ) φ]

theorem freshParamToVar_injective {Γ : Ctx Base} {σ : Ty Base} {Ξ : Ctx Base} {τ : Ty Base} :
    Function.Injective (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ) (τ := τ)) := by
  intro t u h
  simpa using congrArg (varToFreshParam (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ) (τ := τ)) h

theorem varToFreshParam_injective {Γ : Ctx Base} {σ : Ty Base} {Ξ : Ctx Base} {τ : Ty Base} :
    Function.Injective (varToFreshParam (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ) (τ := τ)) := by
  intro t u h
  simpa using congrArg (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ) (τ := τ)) h

/-- Insert one variable of type `ρ` between a prefix `Ξ₁` and suffix `Ξ₃`. -/
def insertRenPrefix
    {ρ : Ty Base} :
    (Ξ₁ Ξ₃ : Ctx Base) →
      Rename Base (Ξ₁ ++ Ξ₃) (Ξ₁ ++ (ρ :: Ξ₃))
  | [], _ => Rename.weaken
  | _ :: Ξ₁, Ξ₃ => Rename.lift (insertRenPrefix (ρ := ρ) Ξ₁ Ξ₃)

/-- `insertRenPrefix` lifted to contexts of shape `... ++ [σ]`. -/
def insertRenPrefixOut
    {σ ρ : Ty Base} :
    (Ξ₁ Ξ₃ : Ctx Base) →
      Rename Base ((Ξ₁ ++ Ξ₃) ++ [σ]) ((Ξ₁ ++ (ρ :: Ξ₃)) ++ [σ])
  | [], _ => Rename.weaken
  | _ :: Ξ₁, Ξ₃ => Rename.lift (insertRenPrefixOut (σ := σ) (ρ := ρ) Ξ₁ Ξ₃)

@[simp] theorem insertRenPrefix_keepPrefixRen
    {σ ρ : Ty Base} :
    ∀ (Ξ₁ Ξ₃ : Ctx Base) {τ : Ty Base}
      (v : Var (Ξ₁ ++ Ξ₃) τ),
      keepPrefixRen (Base := Base) (Γ := Ξ₁ ++ (ρ :: Ξ₃)) (Ξ := [σ])
        (insertRenPrefix (Base := Base) (ρ := ρ) Ξ₁ Ξ₃ v)
      =
      insertRenPrefixOut (Base := Base) (σ := σ) (ρ := ρ) Ξ₁ Ξ₃
        (keepPrefixRen (Base := Base) (Γ := Ξ₁ ++ Ξ₃) (Ξ := [σ]) v)
  | [], Ξ₃, _, v => by
      simp [insertRenPrefix, insertRenPrefixOut, keepPrefixRen, Rename.weaken]
  | _ :: Ξ₁, Ξ₃, _, .vz => by
      simp [insertRenPrefix, insertRenPrefixOut, keepPrefixRen, Rename.lift]
  | _ :: Ξ₁, Ξ₃, _, .vs v => by
      simpa [insertRenPrefix, insertRenPrefixOut, keepPrefixRen, Rename.lift]
        using insertRenPrefix_keepPrefixRen (σ := σ) (ρ := ρ) Ξ₁ Ξ₃ v

@[simp] theorem insertRenPrefix_keepSuffixVz
    {σ ρ : Ty Base} :
    ∀ (Ξ₁ Ξ₃ : Ctx Base),
      keepSuffixVar (Base := Base) (Γ := Ξ₁ ++ (ρ :: Ξ₃)) (Ξ := [σ]) (.vz : Var [σ] σ)
      =
      insertRenPrefixOut (Base := Base) (σ := σ) (ρ := ρ) Ξ₁ Ξ₃
        (keepSuffixVar (Base := Base) (Γ := Ξ₁ ++ Ξ₃) (Ξ := [σ]) (.vz : Var [σ] σ))
  | [], Ξ₃ => by
      simp [insertRenPrefixOut, keepSuffixVar, Rename.weaken]
  | _ :: Ξ₁, Ξ₃ => by
      simpa [insertRenPrefixOut, keepSuffixVar, Rename.lift]
        using insertRenPrefix_keepSuffixVz (σ := σ) (ρ := ρ) Ξ₁ Ξ₃

/--
Split-point renaming helper for `freshParamToVar`.

The recursion follows the upper prefix `Ξ₁`, matching the `insertRenAt` style:
binder cases extend the split structurally, so no append-associativity casts
are needed.
-/
@[simp] theorem freshParamToVar_insertRenPrefix
    {Γ : Ctx Base} {σ ρ : Ty Base} :
    ∀ {Ξ₁ Ξ₃ : Ctx Base} {τ : Ty Base}
      (t : Term (ParamConst Const (σ :: Γ)) (Ξ₁ ++ Ξ₃) τ),
      freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ)
        (Ξ := Ξ₁ ++ (ρ :: Ξ₃))
        (rename (insertRenPrefix (Base := Base) (ρ := ρ) Ξ₁ Ξ₃) t)
      =
      rename (insertRenPrefixOut (Base := Base) (σ := σ) (ρ := ρ) Ξ₁ Ξ₃)
        (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ)
          (Ξ := Ξ₁ ++ Ξ₃) t)
  | Ξ₁, Ξ₃, _, .var v => by
      simp [freshParamToVar, rename, insertRenPrefix_keepPrefixRen]
  | Ξ₁, Ξ₃, _, .const (.inl c) => by
      simp [freshParamToVar, rename]
  | Ξ₁, Ξ₃, _, .const (.inr .vz) => by
      simp [freshParamToVar, rename, insertRenPrefix_keepSuffixVz]
  | Ξ₁, Ξ₃, _, .const (.inr (.vs v)) => by
      simp [freshParamToVar, rename]
  | Ξ₁, Ξ₃, _, .app f u => by
      simp [freshParamToVar, rename,
        freshParamToVar_insertRenPrefix (Γ := Γ) (σ := σ) (ρ := ρ) (Ξ₁ := Ξ₁) (Ξ₃ := Ξ₃) f,
        freshParamToVar_insertRenPrefix (Γ := Γ) (σ := σ) (ρ := ρ) (Ξ₁ := Ξ₁) (Ξ₃ := Ξ₃) u]
  | Ξ₁, Ξ₃, _, .lam body => by
      simp only [freshParamToVar, rename]
      congr 1
      exact freshParamToVar_insertRenPrefix (Γ := Γ) (σ := σ) (ρ := ρ)
        (Ξ₁ := _ :: Ξ₁) (Ξ₃ := Ξ₃) body
  | Ξ₁, Ξ₃, _, .top => by
      simp [freshParamToVar, rename]
  | Ξ₁, Ξ₃, _, .bot => by
      simp [freshParamToVar, rename]
  | Ξ₁, Ξ₃, _, .and p q => by
      simp [freshParamToVar, rename,
        freshParamToVar_insertRenPrefix (Γ := Γ) (σ := σ) (ρ := ρ) (Ξ₁ := Ξ₁) (Ξ₃ := Ξ₃) p,
        freshParamToVar_insertRenPrefix (Γ := Γ) (σ := σ) (ρ := ρ) (Ξ₁ := Ξ₁) (Ξ₃ := Ξ₃) q]
  | Ξ₁, Ξ₃, _, .or p q => by
      simp [freshParamToVar, rename,
        freshParamToVar_insertRenPrefix (Γ := Γ) (σ := σ) (ρ := ρ) (Ξ₁ := Ξ₁) (Ξ₃ := Ξ₃) p,
        freshParamToVar_insertRenPrefix (Γ := Γ) (σ := σ) (ρ := ρ) (Ξ₁ := Ξ₁) (Ξ₃ := Ξ₃) q]
  | Ξ₁, Ξ₃, _, .imp p q => by
      simp [freshParamToVar, rename,
        freshParamToVar_insertRenPrefix (Γ := Γ) (σ := σ) (ρ := ρ) (Ξ₁ := Ξ₁) (Ξ₃ := Ξ₃) p,
        freshParamToVar_insertRenPrefix (Γ := Γ) (σ := σ) (ρ := ρ) (Ξ₁ := Ξ₁) (Ξ₃ := Ξ₃) q]
  | Ξ₁, Ξ₃, _, .not p => by
      simp [freshParamToVar, rename,
        freshParamToVar_insertRenPrefix (Γ := Γ) (σ := σ) (ρ := ρ) (Ξ₁ := Ξ₁) (Ξ₃ := Ξ₃) p]
  | Ξ₁, Ξ₃, _, .eq a b => by
      simp [freshParamToVar, rename,
        freshParamToVar_insertRenPrefix (Γ := Γ) (σ := σ) (ρ := ρ) (Ξ₁ := Ξ₁) (Ξ₃ := Ξ₃) a,
        freshParamToVar_insertRenPrefix (Γ := Γ) (σ := σ) (ρ := ρ) (Ξ₁ := Ξ₁) (Ξ₃ := Ξ₃) b]
  | Ξ₁, Ξ₃, _, .all body => by
      simp only [freshParamToVar, rename]
      congr 1
      exact freshParamToVar_insertRenPrefix (Γ := Γ) (σ := σ) (ρ := ρ)
        (Ξ₁ := _ :: Ξ₁) (Ξ₃ := Ξ₃) body
  | Ξ₁, Ξ₃, _, .ex body => by
      simp only [freshParamToVar, rename]
      congr 1
      exact freshParamToVar_insertRenPrefix (Γ := Γ) (σ := σ) (ρ := ρ)
        (Ξ₁ := _ :: Ξ₁) (Ξ₃ := Ξ₃) body

/--
`hctx` wrapper for split-point renaming transport.

This mirrors the `hctx`-style equal-context wrappers used in
`Syntax/Subst.lean`, while reusing the structural-recursive core theorem
`freshParamToVar_insertRenPrefix`.
-/
@[simp] theorem freshParamToVar_insertRenPrefix_hctx
    {Γ : Ctx Base} {σ ρ : Ty Base}
    {Γ₀ Ξ₁ Ξ₃ : Ctx Base} {τ : Ty Base}
    (hctx : Γ₀ = Ξ₁ ++ Ξ₃)
    (t : Term (ParamConst Const (σ :: Γ)) Γ₀ τ) :
    freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ)
      (Ξ := Ξ₁ ++ (ρ :: Ξ₃))
      (rename (insertRenPrefix (Base := Base) (ρ := ρ) Ξ₁ Ξ₃) (hctx ▸ t))
    =
    rename (insertRenPrefixOut (Base := Base) (σ := σ) (ρ := ρ) Ξ₁ Ξ₃)
      (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ)
        (Ξ := Ξ₁ ++ Ξ₃) (hctx ▸ t)) := by
  subst hctx
  simpa using
    (freshParamToVar_insertRenPrefix (Base := Base) (Const := Const)
      (Γ := Γ) (σ := σ) (ρ := ρ) (Ξ₁ := Ξ₁) (Ξ₃ := Ξ₃) t)

@[simp] theorem freshParamToVar_weaken
    {Γ : Ctx Base} {σ ρ : Ty Base} :
    {Ξ : Ctx Base} → {τ : Ty Base} →
      (t : Term (ParamConst Const (σ :: Γ)) Ξ τ) →
      freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := ρ :: Ξ)
        (weaken (Base := Base) (Const := ParamConst Const (σ :: Γ)) (σ := ρ) t) =
      weaken (Base := Base) (Const := ParamConst Const Γ) (σ := ρ)
        (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ) t)
  | Ξ, _, t => by
      simpa [weaken, rename, insertRenPrefix, insertRenPrefixOut]
        using (freshParamToVar_insertRenPrefix (Base := Base) (Const := Const)
          (Γ := Γ) (σ := σ) (ρ := ρ) (Ξ₁ := []) (Ξ₃ := Ξ) t)

@[simp] theorem freshParamToVar_weakenHyps
    {Γ : Ctx Base} {σ ρ : Ty Base}
    {Ξ : Ctx Base}
    {Δ : List (Formula (ParamConst Const (σ :: Γ)) Ξ)} :
    (weakenHyps (Base := Base) (Const := ParamConst Const (σ :: Γ)) (σ := ρ) Δ).map
      (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := ρ :: Ξ)) =
    weakenHyps (Base := Base) (Const := ParamConst Const Γ) (σ := ρ)
      (Δ.map
        (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ))) := by
  simp [weakenHyps, List.map_map]

/-- Split-point substitution with no fixed suffix context. -/
def substPrefix
    {Γ : Ctx Base} {σ ρ : Ty Base} :
    (Ξ₁ Ξ₂ : Ctx Base) →
      Term (ParamConst Const (σ :: Γ)) Ξ₂ ρ →
      Subst (ParamConst Const (σ :: Γ)) (Ξ₁ ++ (ρ :: Ξ₂)) (Ξ₁ ++ Ξ₂)
  | [], _, t => Subst.single t
  | _ :: Ξ₁, Ξ₂, t => Subst.lift (substPrefix (Γ := Γ) (σ := σ) (ρ := ρ) Ξ₁ Ξ₂ t)

/-- Split-point substitution in contexts with the fixed right suffix `[σ]`. -/
def substPrefixOut
    {Γ : Ctx Base} {σ ρ : Ty Base} :
    (Ξ₁ Ξ₂ : Ctx Base) →
      Term (ParamConst Const Γ) (Ξ₂ ++ [σ]) ρ →
      Subst (ParamConst Const Γ) ((Ξ₁ ++ (ρ :: Ξ₂)) ++ [σ]) ((Ξ₁ ++ Ξ₂) ++ [σ])
  | [], _, t => Subst.single t
  | _ :: Ξ₁, Ξ₂, t => Subst.lift (substPrefixOut (Γ := Γ) (σ := σ) (ρ := ρ) Ξ₁ Ξ₂ t)

/-- Variable case for split-point substitution transport through `freshParamToVar`. -/
theorem freshParamToVar_substPrefix_var
    {Γ : Ctx Base} {σ : Ty Base} {ρ τ : Ty Base} :
    ∀ (Ξ₁ Ξ₂ : Ctx Base)
      (t : Term (ParamConst Const (σ :: Γ)) Ξ₂ ρ)
      (v : Var (Ξ₁ ++ (ρ :: Ξ₂)) τ),
      freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ₁ ++ Ξ₂)
        ((substPrefix (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (ρ := ρ) Ξ₁ Ξ₂ t) v)
      =
      (substPrefixOut (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (ρ := ρ) Ξ₁ Ξ₂
          (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ₂) t))
        (keepPrefixRen (Base := Base) (Γ := Ξ₁ ++ (ρ :: Ξ₂)) (Ξ := [σ]) v)
  | [], Ξ₂, t, .vz => rfl
  | [], Ξ₂, t, .vs v => rfl
  | _ :: Ξ₁, Ξ₂, t, .vz => rfl
  | α :: Ξ₁, Ξ₂, t, .vs v => by
      change
        freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := α :: (Ξ₁ ++ Ξ₂))
          (weaken (Base := Base) (Const := ParamConst Const (σ :: Γ)) (σ := α)
            ((substPrefix (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (ρ := ρ) Ξ₁ Ξ₂ t) v))
        =
        weaken (Base := Base) (Const := ParamConst Const Γ) (σ := α)
          ((substPrefixOut (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (ρ := ρ) Ξ₁ Ξ₂
              (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ₂) t))
            (keepPrefixRen (Base := Base) (Γ := Ξ₁ ++ (ρ :: Ξ₂)) (Ξ := [σ]) v))
      rw [freshParamToVar_weaken]
      exact congrArg (weaken (Base := Base) (Const := ParamConst Const Γ) (σ := α))
        (freshParamToVar_substPrefix_var Ξ₁ Ξ₂ t v)

theorem substPrefixOut_keepSuffixVz
    {Γ : Ctx Base} {σ ρ : Ty Base} :
    ∀ (Ξ₁ Ξ₂ : Ctx Base)
      (t : Term (ParamConst Const Γ) (Ξ₂ ++ [σ]) ρ),
      (substPrefixOut (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (ρ := ρ) Ξ₁ Ξ₂ t)
        (keepSuffixVar (Base := Base) (Γ := Ξ₁ ++ (ρ :: Ξ₂)) (Ξ := [σ])
          (.vz : Var [σ] σ))
      =
      .var (keepSuffixVar (Base := Base) (Γ := Ξ₁ ++ Ξ₂) (Ξ := [σ]) (.vz : Var [σ] σ))
  | [], Ξ₂, t => rfl
  | α :: Ξ₁, Ξ₂, t => by
      simpa [substPrefixOut, keepSuffixVar, List.cons_append] using
        congrArg (weaken (Base := Base) (Const := ParamConst Const Γ) (σ := α))
          (substPrefixOut_keepSuffixVz Ξ₁ Ξ₂ t)

/--
`freshParamToVar` commutes with split-point substitution.

Specializing to `Ξ₁ = []` yields the desired `instantiate` commutation theorem.
-/
theorem freshParamToVar_substPrefix
    {Γ : Ctx Base} {σ : Ty Base} {ρ : Ty Base} :
    ∀ (Ξ₁ Ξ₂ : Ctx Base) {τ : Ty Base}
      (t : Term (ParamConst Const (σ :: Γ)) Ξ₂ ρ)
      (u : Term (ParamConst Const (σ :: Γ)) (Ξ₁ ++ (ρ :: Ξ₂)) τ),
      freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ₁ ++ Ξ₂)
        (subst
          (substPrefix (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (ρ := ρ) Ξ₁ Ξ₂ t)
          u)
      =
      subst
        (substPrefixOut (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (ρ := ρ) Ξ₁ Ξ₂
          (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ₂) t))
        (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ)
          (Ξ := Ξ₁ ++ (ρ :: Ξ₂)) u)
  | Ξ₁, Ξ₂, _, t, .var v => by
      simpa [subst] using freshParamToVar_substPrefix_var Ξ₁ Ξ₂ t v
  | _, _, _, _, .const (.inl c) => by
      simp [subst, freshParamToVar]
  | Ξ₁, Ξ₂, _, t, .const (.inr .vz) => by
      simp [subst, freshParamToVar]
      rw [← insertRenPrefix_keepSuffixVz (Base := Base) (σ := σ) (ρ := ρ) Ξ₁ Ξ₂]
      symm
      simpa using
        (substPrefixOut_keepSuffixVz (Base := Base) (Const := Const)
          (Γ := Γ) (σ := σ) (ρ := ρ) Ξ₁ Ξ₂
          (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ₂) t))
  | _, _, _, _, .const (.inr (.vs v)) => by
      simp [subst, freshParamToVar]
  | Ξ₁, Ξ₂, _, t, .app f u => by
      simp [subst, freshParamToVar,
        freshParamToVar_substPrefix Ξ₁ Ξ₂ t f,
        freshParamToVar_substPrefix Ξ₁ Ξ₂ t u]
  | Ξ₁, Ξ₂, _, t, .lam body => by
      simp only [subst, freshParamToVar, substPrefix, substPrefixOut]
      congr 1
      exact freshParamToVar_substPrefix (_ :: Ξ₁) Ξ₂ t body
  | _, _, _, _, .top => by
      simp [subst, freshParamToVar]
  | _, _, _, _, .bot => by
      simp [subst, freshParamToVar]
  | Ξ₁, Ξ₂, _, t, .and p q => by
      simp [subst, freshParamToVar,
        freshParamToVar_substPrefix Ξ₁ Ξ₂ t p,
        freshParamToVar_substPrefix Ξ₁ Ξ₂ t q]
  | Ξ₁, Ξ₂, _, t, .or p q => by
      simp [subst, freshParamToVar,
        freshParamToVar_substPrefix Ξ₁ Ξ₂ t p,
        freshParamToVar_substPrefix Ξ₁ Ξ₂ t q]
  | Ξ₁, Ξ₂, _, t, .imp p q => by
      simp [subst, freshParamToVar,
        freshParamToVar_substPrefix Ξ₁ Ξ₂ t p,
        freshParamToVar_substPrefix Ξ₁ Ξ₂ t q]
  | Ξ₁, Ξ₂, _, t, .not p => by
      simp [subst, freshParamToVar,
        freshParamToVar_substPrefix Ξ₁ Ξ₂ t p]
  | Ξ₁, Ξ₂, _, t, .eq a b => by
      simp [subst, freshParamToVar,
        freshParamToVar_substPrefix Ξ₁ Ξ₂ t a,
        freshParamToVar_substPrefix Ξ₁ Ξ₂ t b]
  | Ξ₁, Ξ₂, _, t, .all body => by
      simp only [subst, freshParamToVar, substPrefix, substPrefixOut]
      congr 1
      exact freshParamToVar_substPrefix (_ :: Ξ₁) Ξ₂ t body
  | Ξ₁, Ξ₂, _, t, .ex body => by
      simp only [subst, freshParamToVar, substPrefix, substPrefixOut]
      congr 1
      exact freshParamToVar_substPrefix (_ :: Ξ₁) Ξ₂ t body

@[simp] theorem freshParamToVar_instantiate
    {Γ : Ctx Base} {σ : Ty Base}
    {Ξ : Ctx Base} {ρ τ : Ty Base}
    (t : Term (ParamConst Const (σ :: Γ)) Ξ ρ)
    (u : Term (ParamConst Const (σ :: Γ)) (ρ :: Ξ) τ) :
    freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ)
      (instantiate (Base := Base) t u) =
    instantiate (Base := Base)
      (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ) t)
      (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := ρ :: Ξ) u) := by
  simpa [instantiate, substPrefix, substPrefixOut] using
    (freshParamToVar_substPrefix (Base := Base) (Const := Const) (Γ := Γ) (σ := σ)
      (ρ := ρ) [] Ξ t u)

/--
Lifting a formula into the one-step larger parameter signature and then
reinterpreting the fresh parameter as a right-edge variable just weakens the
original formula into that larger context.

Positive example:
an old parameter `Sum.inr v` becomes `Sum.inr (.vs v)` under `liftParamCtx`,
and `freshParamToVar` immediately drops that back to `Sum.inr v`.

Negative example:
this theorem does not say anything about formulas that genuinely contain the
distinguished fresh parameter `Sum.inr .vz`; those are handled separately.
-/
theorem freshParamToVar_liftParamCtx
    {Γ : Ctx Base} {σ : Ty Base} :
    {Ξ : Ctx Base} → {τ : Ty Base} →
      (t : Term (ParamConst Const Γ) Ξ τ) →
        freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ)
          (liftParamCtx (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) t) =
        Mettapedia.Logic.HOL.rename
          (keepPrefixRen (Base := Base) (Γ := Ξ) (Ξ := [σ])) t
  | _, _, .var _ => rfl
  | _, _, .const (.inl _) => rfl
  | _, _, .const (.inr _) => rfl
  | _, _, .app f t => by
      simp [freshParamToVar, liftParamCtx, Mettapedia.Logic.HOL.mapConst,
        Mettapedia.Logic.HOL.rename,
        freshParamToVar_liftParamCtx (Γ := Γ) (σ := σ) (Ξ := _) f,
        freshParamToVar_liftParamCtx (Γ := Γ) (σ := σ) (Ξ := _) t]
  | Ξ, _, .lam t => by
      simp [freshParamToVar, liftParamCtx, Mettapedia.Logic.HOL.mapConst,
        Mettapedia.Logic.HOL.rename,
        freshParamToVar_liftParamCtx (Γ := Γ) (σ := σ) (Ξ := _ :: Ξ) t]
      apply rename_ext
      intro τ v
      cases v <;> rfl
  | _, _, .top => rfl
  | _, _, .bot => rfl
  | _, _, .and φ ψ => by
      simp [freshParamToVar, liftParamCtx, Mettapedia.Logic.HOL.mapConst,
        Mettapedia.Logic.HOL.rename,
        freshParamToVar_liftParamCtx (Γ := Γ) (σ := σ) (Ξ := _) φ,
        freshParamToVar_liftParamCtx (Γ := Γ) (σ := σ) (Ξ := _) ψ]
  | _, _, .or φ ψ => by
      simp [freshParamToVar, liftParamCtx, Mettapedia.Logic.HOL.mapConst,
        Mettapedia.Logic.HOL.rename,
        freshParamToVar_liftParamCtx (Γ := Γ) (σ := σ) (Ξ := _) φ,
        freshParamToVar_liftParamCtx (Γ := Γ) (σ := σ) (Ξ := _) ψ]
  | _, _, .imp φ ψ => by
      simp [freshParamToVar, liftParamCtx, Mettapedia.Logic.HOL.mapConst,
        Mettapedia.Logic.HOL.rename,
        freshParamToVar_liftParamCtx (Γ := Γ) (σ := σ) (Ξ := _) φ,
        freshParamToVar_liftParamCtx (Γ := Γ) (σ := σ) (Ξ := _) ψ]
  | _, _, .not φ => by
      simp [freshParamToVar, liftParamCtx, Mettapedia.Logic.HOL.mapConst,
        Mettapedia.Logic.HOL.rename,
        freshParamToVar_liftParamCtx (Γ := Γ) (σ := σ) (Ξ := _) φ]
  | _, _, .eq t u => by
      simp [freshParamToVar, liftParamCtx, Mettapedia.Logic.HOL.mapConst,
        Mettapedia.Logic.HOL.rename,
        freshParamToVar_liftParamCtx (Γ := Γ) (σ := σ) (Ξ := _) t,
        freshParamToVar_liftParamCtx (Γ := Γ) (σ := σ) (Ξ := _) u]
  | Ξ, _, .all φ => by
      simp [freshParamToVar, liftParamCtx, Mettapedia.Logic.HOL.mapConst,
        Mettapedia.Logic.HOL.rename,
        freshParamToVar_liftParamCtx (Γ := Γ) (σ := σ) (Ξ := _ :: Ξ) φ]
      apply rename_ext
      intro τ v
      cases v <;> rfl
  | Ξ, _, .ex φ => by
      simp [freshParamToVar, liftParamCtx, Mettapedia.Logic.HOL.mapConst,
        Mettapedia.Logic.HOL.rename,
        freshParamToVar_liftParamCtx (Γ := Γ) (σ := σ) (Ξ := _ :: Ξ) φ]
      apply rename_ext
      intro τ v
      cases v <;> rfl

@[simp] theorem freshParamToVar_liftParamCtxFormula_closed
    {Γ : Ctx Base} {σ : Ty Base}
    (χ : ClosedFormula (ParamConst Const Γ)) :
    freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := [])
      (liftParamCtxFormula (Base := Base) (Const := Const) (Γ := Γ) σ χ) =
    weaken (Base := Base) (Const := ParamConst Const Γ) (σ := σ) χ := by
  have hrename :
      rename (keepPrefixRen (Base := Base) (Γ := ([] : Ctx Base)) (Ξ := [σ])) χ =
      rename (Rename.weaken (Base := Base) (Γ := ([] : Ctx Base)) (σ := σ)) χ := by
    apply rename_ext
    intro τ v
    cases v
  calc
    freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := [])
      (liftParamCtxFormula (Base := Base) (Const := Const) (Γ := Γ) σ χ)
      = rename (keepPrefixRen (Base := Base) (Γ := ([] : Ctx Base)) (Ξ := [σ])) χ := by
          simpa [liftParamCtxFormula] using
            (freshParamToVar_liftParamCtx (Base := Base) (Const := Const)
              (Γ := Γ) (σ := σ) (Ξ := []) χ)
  _ = rename (Rename.weaken (Base := Base) (Γ := ([] : Ctx Base)) (σ := σ)) χ := by
      exact hrename
  _ = weaken (Base := Base) (Const := ParamConst Const Γ) (σ := σ) χ := rfl

/-- Substitute the distinguished suffix variable by the fresh parameter constant. -/
def freshSuffixSubst
    {Γ : Ctx Base} {σ : Ty Base} :
    (Ξ : Ctx Base) →
      Subst (ParamConst Const (σ :: Γ)) (Ξ ++ [σ]) Ξ
  | [] => Subst.single (.const (freshParam (Base := Base) (Const := Const) Γ σ))
  | _ :: Ξ => Subst.lift (freshSuffixSubst (Γ := Γ) (σ := σ) Ξ)

private theorem varToFreshParam_var_vs
    {Γ : Ctx Base} {σ α : Ty Base} {Ξ : Ctx Base} {τ : Ty Base}
    (v : Var (Ξ ++ [σ]) τ) :
    varToFreshParam (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := α :: Ξ)
      (.var (.vs v))
    =
    rename (Base := Base) (Const := ParamConst Const (σ :: Γ))
      (Rename.weaken (Base := Base) (Γ := Ξ) (σ := α))
      (varToFreshParam (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ) (.var v)) := by
  cases h : splitAppendVar (Γ := Ξ) (Ξ := [σ]) v with
  | inl v' =>
      simp [varToFreshParam, splitAppendVar, h, Rename.weaken]
  | inr v' =>
      cases v' with
      | vz =>
          simp [varToFreshParam, splitAppendVar, h, rename]
      | vs v'' =>
          cases v''

private theorem varToFreshParam_var_eq_freshSuffixSubst
    {Γ : Ctx Base} {σ : Ty Base} :
    ∀ (Ξ : Ctx Base) {τ : Ty Base}
      (v : Var (Ξ ++ [σ]) τ),
      varToFreshParam (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ) (.var v) =
      (freshSuffixSubst (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) Ξ) v
  | Ξ, _, v => by
      induction Ξ with
      | nil =>
          cases v with
          | vz =>
              simp [varToFreshParam, freshSuffixSubst, splitAppendVar, Subst.single, freshParam]
          | vs v =>
              cases v
      | cons α Ξ ih =>
          cases v with
          | vz =>
              simp [varToFreshParam, freshSuffixSubst, splitAppendVar, Subst.lift]
          | vs v =>
              calc
                varToFreshParam (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := α :: Ξ)
                    (.var (.vs v))
                    =
                  rename (Base := Base) (Const := ParamConst Const (σ :: Γ))
                    (Rename.weaken (Base := Base) (Γ := Ξ) (σ := α))
                    (varToFreshParam (Base := Base) (Const := Const) (Γ := Γ) (σ := σ)
                      (Ξ := Ξ) (.var v)) := by
                        exact varToFreshParam_var_vs (Base := Base) (Const := Const)
                          (Γ := Γ) (σ := σ) (α := α) (Ξ := Ξ) v
                _ =
                  rename (Base := Base) (Const := ParamConst Const (σ :: Γ))
                    (Rename.weaken (Base := Base) (Γ := Ξ) (σ := α))
                    ((freshSuffixSubst (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) Ξ) v) := by
                      exact congrArg
                        (rename (Base := Base) (Const := ParamConst Const (σ :: Γ))
                          (Rename.weaken (Base := Base) (Γ := Ξ) (σ := α)))
                        (ih v)
                _ =
                  (freshSuffixSubst (Base := Base) (Const := Const) (Γ := Γ) (σ := σ)
                    (α :: Ξ)) (.vs v) := by
                      rfl

private theorem varToFreshParam_eq_freshSuffixSubst
    {Γ : Ctx Base} {σ : Ty Base} :
    ∀ (Ξ : Ctx Base) {τ : Ty Base}
      (t : Term (ParamConst Const Γ) (Ξ ++ [σ]) τ),
      varToFreshParam (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ) t =
      subst
        (freshSuffixSubst (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) Ξ)
        (liftParamCtx (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) t)
  | Ξ, _, .var v => by
      simpa [liftParamCtx, mapConst] using
        (varToFreshParam_var_eq_freshSuffixSubst (Γ := Γ) (σ := σ) Ξ v)
  | _, _, .const (.inl c) => by
      simp [varToFreshParam, liftParamCtx, mapConst, subst, paramWeaken]
  | _, _, .const (.inr v) => by
      simp [varToFreshParam, liftParamCtx, mapConst, subst, paramWeaken]
  | Ξ, _, .app f t => by
      simp [varToFreshParam, liftParamCtx, mapConst, subst,
        varToFreshParam_eq_freshSuffixSubst (Γ := Γ) (σ := σ) Ξ f,
        varToFreshParam_eq_freshSuffixSubst (Γ := Γ) (σ := σ) Ξ t]
  | Ξ, _, .lam body => by
      simp only [varToFreshParam, liftParamCtx, mapConst, freshSuffixSubst, subst]
      congr 1
      exact varToFreshParam_eq_freshSuffixSubst (Γ := Γ) (σ := σ) (_ :: Ξ) body
  | _, _, .top => by simp [varToFreshParam, liftParamCtx, mapConst, subst]
  | _, _, .bot => by simp [varToFreshParam, liftParamCtx, mapConst, subst]
  | Ξ, _, .and p q => by
      simp [varToFreshParam, liftParamCtx, mapConst, subst,
        varToFreshParam_eq_freshSuffixSubst (Γ := Γ) (σ := σ) Ξ p,
        varToFreshParam_eq_freshSuffixSubst (Γ := Γ) (σ := σ) Ξ q]
  | Ξ, _, .or p q => by
      simp [varToFreshParam, liftParamCtx, mapConst, subst,
        varToFreshParam_eq_freshSuffixSubst (Γ := Γ) (σ := σ) Ξ p,
        varToFreshParam_eq_freshSuffixSubst (Γ := Γ) (σ := σ) Ξ q]
  | Ξ, _, .imp p q => by
      simp [varToFreshParam, liftParamCtx, mapConst, subst,
        varToFreshParam_eq_freshSuffixSubst (Γ := Γ) (σ := σ) Ξ p,
        varToFreshParam_eq_freshSuffixSubst (Γ := Γ) (σ := σ) Ξ q]
  | Ξ, _, .not p => by
      simp [varToFreshParam, liftParamCtx, mapConst, subst,
        varToFreshParam_eq_freshSuffixSubst (Γ := Γ) (σ := σ) Ξ p]
  | Ξ, _, .eq a b => by
      simp [varToFreshParam, liftParamCtx, mapConst, subst,
        varToFreshParam_eq_freshSuffixSubst (Γ := Γ) (σ := σ) Ξ a,
        varToFreshParam_eq_freshSuffixSubst (Γ := Γ) (σ := σ) Ξ b]
  | Ξ, _, .all body => by
      simp only [varToFreshParam, liftParamCtx, mapConst, freshSuffixSubst, subst]
      congr 1
      exact varToFreshParam_eq_freshSuffixSubst (Γ := Γ) (σ := σ) (_ :: Ξ) body
  | Ξ, _, .ex body => by
      simp only [varToFreshParam, liftParamCtx, mapConst, freshSuffixSubst, subst]
      congr 1
      exact varToFreshParam_eq_freshSuffixSubst (Γ := Γ) (σ := σ) (_ :: Ξ) body

@[simp] theorem varToFreshParam_eq_fresh_instance
    {Γ : Ctx Base} {σ : Ty Base}
    (ψ : Formula (ParamConst Const Γ) [σ]) :
    varToFreshParam (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := []) ψ =
      instantiate
        (.const (freshParam (Base := Base) (Const := Const) Γ σ))
        (liftParamCtx (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) ψ) := by
  simpa [instantiate, freshSuffixSubst] using
    (varToFreshParam_eq_freshSuffixSubst (Γ := Γ) (σ := σ) [] ψ)

@[simp] theorem freshParamToVar_fresh_instance
    {Γ : Ctx Base} {σ : Ty Base}
    (ψ : Formula (ParamConst Const Γ) [σ]) :
    freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := [])
      (instantiate
        (.const (freshParam (Base := Base) (Const := Const) Γ σ))
        (liftParamCtx (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) ψ)) = ψ := by
  rw [← varToFreshParam_eq_fresh_instance (Base := Base) (Const := Const)
    (Γ := Γ) (σ := σ) ψ]
  simpa using
    (freshParamToVar_varToFreshParam (Base := Base) (Const := Const)
      (Γ := Γ) (σ := σ) (Ξ := []) ψ)

@[simp] theorem freshParamToVar_liftParamCtx_fresh_instance
    {Γ : Ctx Base} {σ : Ty Base}
    (ψ : Formula (ParamConst Const Γ) [σ]) :
    instantiate (Base := Base)
      (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := [])
        (.const (freshParam (Base := Base) (Const := Const) Γ σ)))
      (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := [σ])
        (liftParamCtx (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) ψ))
    = ψ := by
  simpa [freshParamToVar_instantiate] using
    (freshParamToVar_fresh_instance (Base := Base) (Const := Const)
      (Γ := Γ) (σ := σ) ψ)

theorem freshParamToVar_derivation
    {Γ : Ctx Base} {σ : Ty Base} :
    ∀ {Ξ : Ctx Base}
      {Δ : List (Formula (ParamConst Const (σ :: Γ)) Ξ)}
      {φ : Formula (ParamConst Const (σ :: Γ)) Ξ},
      ExtDerivation (ParamConst Const (σ :: Γ)) Δ φ →
      ExtDerivation (ParamConst Const Γ)
        (Δ.map
          (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ)))
        (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ) φ) := by
  intro Ξ Δ φ d
  induction d with
  | hyp hmem =>
      exact .hyp (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  | topI =>
      exact .topI
  | botE h ih =>
      exact .botE ih
  | andI hφ hψ ihφ ihψ =>
      exact .andI ihφ ihψ
  | andEL h ih =>
      exact .andEL ih
  | andER h ih =>
      exact .andER ih
  | orIL h ih =>
      exact .orIL ih
  | orIR h ih =>
      exact .orIR ih
  | orE hor hφ hψ ihor ihφ ihψ =>
      exact .orE ihor ihφ ihψ
  | impI h ih =>
      exact .impI (by
        simpa [List.map] using ih)
  | impE hφψ hφ ihφψ ihφ =>
      exact .impE ihφψ ihφ
  | notI h ih =>
      exact .notI (by
        simpa [List.map] using ih)
  | notE hnot hφ ihnot ihφ =>
      exact .notE ihnot ihφ
  | allI h ih =>
      rename_i Ξ₀ Δ₀ ρ body
      have hwh :
          (weakenHyps (Base := Base) (Const := ParamConst Const (σ :: Γ)) (σ := ρ) Δ₀).map
            (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := ρ :: Ξ₀))
          =
          weakenHyps (Base := Base) (Const := ParamConst Const Γ) (σ := ρ)
            (Δ₀.map
              (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ₀))) :=
        freshParamToVar_weakenHyps (Base := Base) (Const := Const)
          (Γ := Γ) (σ := σ) (ρ := ρ) (Ξ := Ξ₀) (Δ := Δ₀)
      have ih' :
          ExtDerivation (ParamConst Const Γ)
            (weakenHyps (Base := Base) (Const := ParamConst Const Γ) (σ := ρ)
              (Δ₀.map
                (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ)
                  (Ξ := Ξ₀))))
            (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ)
              (Ξ := ρ :: Ξ₀) body) := by
        simpa [hwh] using ih
      exact .allI ih'
  | allE t h ih =>
      simpa [freshParamToVar_instantiate] using
        (.allE
          (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) t)
          ih)
  | exI t h ih =>
      rename_i Ξ₀ Δ₀ ρ body
      have ih' :
          ExtDerivation (ParamConst Const Γ)
            (Δ₀.map
              (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ)
                (Ξ := Ξ₀)))
            (instantiate (Base := Base)
              (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ)
                (Ξ := Ξ₀) t)
              (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ)
                (Ξ := ρ :: Ξ₀) body)) := by
        simpa [freshParamToVar_instantiate] using ih
      exact .exI
        (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ₀) t)
        ih'
  | exE hex hbody ihex ihbody =>
      rename_i Ξ₀ Δ₀ ρ body ψ
      have hwh :
          (weakenHyps (Base := Base) (Const := ParamConst Const (σ :: Γ)) (σ := ρ) Δ₀).map
            (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := ρ :: Ξ₀))
          =
          weakenHyps (Base := Base) (Const := ParamConst Const Γ) (σ := ρ)
            (Δ₀.map
              (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ₀))) :=
        freshParamToVar_weakenHyps (Base := Base) (Const := Const)
          (Γ := Γ) (σ := σ) (ρ := ρ) (Ξ := Ξ₀) (Δ := Δ₀)
      have hbody' :
          ExtDerivation (ParamConst Const Γ)
            (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ)
              (Ξ := ρ :: Ξ₀) body ::
              weakenHyps (Base := Base) (Const := ParamConst Const Γ) (σ := ρ)
                (Δ₀.map
                  (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ)
                    (Ξ := Ξ₀))))
            (weaken (Base := Base) (Const := ParamConst Const Γ) (σ := ρ)
              (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ)
                (Ξ := Ξ₀) ψ)) := by
        simpa [List.map, hwh, freshParamToVar_weaken] using ihbody
      exact .exE ihex hbody'
  | eqRefl t =>
      exact .eqRefl
        (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) t)
  | eqSymm h ih =>
      exact .eqSymm ih
  | eqTrans htu huv ihtu ihuv =>
      exact .eqTrans ihtu ihuv
  | eqPropI hpq hqp ihpq ihqp =>
      exact .eqPropI ihpq ihqp
  | eqPropEL hpq ihpq =>
      exact .eqPropEL ihpq
  | eqPropER hpq ihpq =>
      exact .eqPropER ihpq
  | eqApp t h ih =>
      exact .eqApp
        (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) t)
        ih
  | eqAppArg f h ih =>
      exact .eqAppArg
        (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) f)
        ih
  | eqLam h ih =>
      rename_i Ξ₀ Δ₀ ρ τ t u
      have hwh :
          (weakenHyps (Base := Base) (Const := ParamConst Const (σ :: Γ)) (σ := ρ) Δ₀).map
            (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := ρ :: Ξ₀))
          =
          weakenHyps (Base := Base) (Const := ParamConst Const Γ) (σ := ρ)
            (Δ₀.map
              (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := Ξ₀))) :=
        freshParamToVar_weakenHyps (Base := Base) (Const := Const)
          (Γ := Γ) (σ := σ) (ρ := ρ) (Ξ := Ξ₀) (Δ := Δ₀)
      have ih' :
          ExtDerivation (ParamConst Const Γ)
            (weakenHyps (Base := Base) (Const := ParamConst Const Γ) (σ := ρ)
              (Δ₀.map
                (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ)
                  (Ξ := Ξ₀))))
            (.eq
              (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ)
                (Ξ := ρ :: Ξ₀) t)
              (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ)
                (Ξ := ρ :: Ξ₀) u)) := by
        simpa [hwh] using ih
      exact .eqLam ih'
  | funExt h ih =>
      exact .funExt (by
        simpa [freshParamToVar, freshParamToVar_weaken] using ih)
  | beta t u =>
      simpa [freshParamToVar, freshParamToVar_instantiate] using
        (.beta
          (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) t)
          (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) u))
  | eta f =>
      simpa [freshParamToVar, freshParamToVar_weaken] using
        (.eta (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) f))

end FreshParamAsVar

/-! ## Growing-Domain Kripke Frame -/

section GrowingFrame

variable {Const : Ty Base → Type v}

/-- A prime theory over a parameterized signature.

Unlike `ClosedTheorySet.World`, this does NOT require `exists_witness` or
`all_counterexample`. Those properties are handled cross-world by the
growing-domain Kripke forcing definition. The properties here are exactly
what `exists_prime_extension_separating` provides. -/
structure PrimeTheory (Const : Ty Base → Type v) (Γ : Ctx Base) where
  carrier : ClosedTheorySet (ParamConst Const Γ)
  closed : ClosedTheorySet.DeductivelyClosed carrier
  consistent : ClosedTheorySet.Consistent carrier
  prime_or :
    ∀ {φ ψ : ClosedFormula (ParamConst Const Γ)},
      (.or φ ψ : ClosedFormula (ParamConst Const Γ)) ∈ carrier →
        φ ∈ carrier ∨ ψ ∈ carrier

namespace PrimeTheory

variable {Γ : Ctx Base}

theorem mem_of_provable {W : PrimeTheory Const Γ}
    {φ : ClosedFormula (ParamConst Const Γ)}
    (h : ClosedTheorySet.Provable W.carrier φ) :
    φ ∈ W.carrier :=
  W.closed h

theorem top_mem {W : PrimeTheory Const Γ} :
    (.top : ClosedFormula (ParamConst Const Γ)) ∈ W.carrier :=
  mem_of_provable (ClosedTheorySet.provable_top W.carrier)

theorem bot_not_mem {W : PrimeTheory Const Γ}
    (h : (.bot : ClosedFormula (ParamConst Const Γ)) ∈ W.carrier) : False :=
  W.consistent (ClosedTheorySet.provable_of_mem h)

theorem mp {W : PrimeTheory Const Γ}
    {φ ψ : ClosedFormula (ParamConst Const Γ)}
    (hImp : (.imp φ ψ) ∈ W.carrier)
    (hφ : φ ∈ W.carrier) :
    ψ ∈ W.carrier :=
  mem_of_provable (ClosedTheorySet.provable_mp
    (ClosedTheorySet.provable_of_mem hImp)
    (ClosedTheorySet.provable_of_mem hφ))

theorem and_mem {W : PrimeTheory Const Γ}
    {φ ψ : ClosedFormula (ParamConst Const Γ)}
    (hφ : φ ∈ W.carrier) (hψ : ψ ∈ W.carrier) :
    (.and φ ψ) ∈ W.carrier :=
  mem_of_provable (ClosedTheorySet.provable_and_intro
    (ClosedTheorySet.provable_of_mem hφ)
    (ClosedTheorySet.provable_of_mem hψ))

theorem and_left_mem {W : PrimeTheory Const Γ}
    {φ ψ : ClosedFormula (ParamConst Const Γ)}
    (h : (.and φ ψ) ∈ W.carrier) : φ ∈ W.carrier :=
  mem_of_provable (ClosedTheorySet.provable_and_left
    (ClosedTheorySet.provable_of_mem h))

theorem and_right_mem {W : PrimeTheory Const Γ}
    {φ ψ : ClosedFormula (ParamConst Const Γ)}
    (h : (.and φ ψ) ∈ W.carrier) : ψ ∈ W.carrier :=
  mem_of_provable (ClosedTheorySet.provable_and_right
    (ClosedTheorySet.provable_of_mem h))

theorem or_left_mem {W : PrimeTheory Const Γ}
    {φ ψ : ClosedFormula (ParamConst Const Γ)}
    (h : φ ∈ W.carrier) : (.or φ ψ) ∈ W.carrier :=
  mem_of_provable (ClosedTheorySet.provable_or_intro_left
    (ClosedTheorySet.provable_of_mem h))

theorem or_right_mem {W : PrimeTheory Const Γ}
    {φ ψ : ClosedFormula (ParamConst Const Γ)}
    (h : ψ ∈ W.carrier) : (.or φ ψ) ∈ W.carrier :=
  mem_of_provable (ClosedTheorySet.provable_or_intro_right
    (ClosedTheorySet.provable_of_mem h))

/--
Extract a finite base-support list from a lifted finite support.

Positive example:
if every element of `support` is witnessed to come from some `χ ∈ W.carrier`
via `liftParamCtxFormula σ χ`, this constructs a concrete list `supportBase`
with exactly those preimages.

Negative example:
this is only a finite-support extraction lemma. It does not prove any global
conservativity statement about all formulas in the extended signature.
-/
private theorem extract_lifted_support
    {σ : Ty Base}
    (W : PrimeTheory Const Γ) :
    ∀ (support : ClosedTheory (ParamConst Const (σ :: Γ))),
      (∀ φ, φ ∈ support →
        ∃ χ ∈ W.carrier, liftParamCtxFormula (Base := Base) (Const := Const) (Γ := Γ) σ χ = φ) →
      ∃ supportBase : ClosedTheory (ParamConst Const Γ),
        (∀ χ, χ ∈ supportBase → χ ∈ W.carrier) ∧
        supportBase.map (liftParamCtxFormula (Base := Base) (Const := Const) (Γ := Γ) σ) = support
  | [], _ => by
      refine ⟨[], ?_, rfl⟩
      intro χ hχ
      cases hχ
  | φ :: support, hSup => by
      rcases hSup φ (by simp) with ⟨χ, hχ, rfl⟩
      have hTail :
          ∀ ψ, ψ ∈ support →
            ∃ ξ ∈ W.carrier,
              liftParamCtxFormula (Base := Base) (Const := Const) (Γ := Γ) σ ξ = ψ := by
        intro ψ hψ
        exact hSup ψ (by simp [hψ])
      rcases extract_lifted_support W support hTail with ⟨supportBase, hBase, hMap⟩
      refine ⟨χ :: supportBase, ?_, ?_⟩
      · intro ξ hξ
        rcases List.mem_cons.mp hξ with rfl | hξ
        · exact hχ
        · exact hBase ξ hξ
      · simp [hMap]

end PrimeTheory

/-- A world in the growing-domain Kripke frame.

A world is a context `Γ` together with a prime theory over
`ParamConst Const Γ`. Different worlds may live at different contexts. -/
structure GrowingWorld (Base : Type u) (Const : Ty Base → Type v) where
  ctx : Ctx Base
  theory : PrimeTheory Const ctx

/-- Build a prime extension of a theory at the SAME context that omits φ.
This is the key tool for the implication truth lemma. -/
theorem PrimeTheory.exists_extension_omitting
    {Γ : Ctx Base}
    {W : PrimeTheory Const Γ}
    {φ : ClosedFormula (ParamConst Const Γ)}
    (hNot : ¬ ClosedTheorySet.Provable W.carrier φ) :
    ∃ V : PrimeTheory Const Γ,
      (∀ {ψ : ClosedFormula (ParamConst Const Γ)},
        ψ ∈ W.carrier → ψ ∈ V.carrier) ∧
      φ ∉ V.carrier := by
  rcases ClosedTheorySet.exists_prime_extension_separating hNot with
    ⟨U, hExt, hClosed, hCons, hPrime, hOmit⟩
  exact ⟨⟨U, hClosed, hCons, hPrime⟩, fun h => hExt h, hOmit⟩

/--
Local fresh-parameter reflection for the universal counterexample step.

Positive example:
if the lifted theory at context `σ :: Γ` proved the fresh-parameter instance
`ψ[c/x]`, then we could descend that proof back to a proof of `∀x:σ. ψ` in the
original world `W`.

Negative example:
this is not the same as proving consistency of `liftedT ∪ {¬ ψ[c/x]}`. In
intuitionistic logic, inconsistency of that extension only yields `¬¬ ψ[c/x]`,
not `ψ[c/x]`.
-/
theorem PrimeTheory.reflect_freshParam_instance
    {Γ : Ctx Base}
    {W : PrimeTheory Const Γ}
    {σ : Ty Base} {ψ : Formula (ParamConst Const Γ) [σ]}
    (hProv :
      ClosedTheorySet.Provable
        (Const := ParamConst Const (σ :: Γ))
        (fun φ => ∃ χ ∈ W.carrier, liftParamCtxFormula σ χ = φ)
        (instantiate
          (.const (freshParam Γ σ))
          (liftParamCtx ψ))) :
    ClosedTheorySet.Provable (Const := ParamConst Const Γ) W.carrier (.all ψ) := by
  rcases hProv with ⟨support, hSup, d⟩
  rcases extract_lifted_support (Base := Base) (Const := Const) (Γ := Γ) (σ := σ)
      W support (by
        intro φ hφ
        exact hSup φ hφ) with
    ⟨supportBase, hBase, hMap⟩
  have d' :
      ExtDerivation (ParamConst Const Γ)
        (support.map
          (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := [])))
        (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := [])
          (instantiate
            (.const (freshParam (Base := Base) (Const := Const) Γ σ))
            (liftParamCtx (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) ψ))) :=
    freshParamToVar_derivation (Base := Base) (Const := Const)
      (Γ := Γ) (σ := σ) d
  have hSupportMap :
      support.map
        (freshParamToVar (Base := Base) (Const := Const) (Γ := Γ) (σ := σ) (Ξ := []))
      =
      weakenHyps (Base := Base) (Const := ParamConst Const Γ) (σ := σ) supportBase := by
    rw [← hMap]
    simp [List.map_map, weakenHyps]
  have dBody :
      ExtDerivation (ParamConst Const Γ)
        (weakenHyps (Base := Base) (Const := ParamConst Const Γ) (σ := σ) supportBase)
        ψ := by
    simpa [hSupportMap, freshParamToVar_fresh_instance] using d'
  have dAll :
      ClosedTheory.Provable (Const := ParamConst Const Γ) supportBase (.all ψ) :=
    .allI dBody
  exact
    ClosedTheorySet.provable_of_closedTheory
      (Const := ParamConst Const Γ)
      (T := W.carrier)
      (Δ := supportBase)
      (hΔ := by
        intro χ hχ
        exact hBase χ hχ)
      dAll

/-- Build a prime extension at a ONE-STEP EXTENDED context `σ :: Γ`.

Given `∀x:σ.ψ ∉ W.carrier`, produces a prime theory V at `σ :: Γ`
with a fresh parameter `c : σ` such that `ψ[c/x] ∉ V.carrier`,
while all of W's theory is preserved (lifted into V).

This is the cross-world counterexample for the universal truth lemma.
It uses the specialized fresh-parameter reflection lemma above. -/
theorem PrimeTheory.exists_paramExt_omitting
    {Γ : Ctx Base}
    {W : PrimeTheory Const Γ}
    {σ : Ty Base} {ψ : Formula (ParamConst Const Γ) [σ]}
    (hAll : (.all ψ : ClosedFormula (ParamConst Const Γ)) ∉ W.carrier) :
    ∃ V : PrimeTheory Const (σ :: Γ),
      (∀ {φ : ClosedFormula (ParamConst Const Γ)},
        φ ∈ W.carrier → liftParamCtxFormula σ φ ∈ V.carrier) ∧
      ∃ t : ClosedTerm (ParamConst Const (σ :: Γ)) σ,
        instantiate t (liftParamCtx ψ) ∉ V.carrier := by
  -- The fresh parameter constant
  let c : ClosedTerm (ParamConst Const (σ :: Γ)) σ :=
    .const (freshParam Γ σ)
  -- The instantiation ψ[c/x] in the extended signature
  let ψc : ClosedFormula (ParamConst Const (σ :: Γ)) :=
    instantiate c (liftParamCtx ψ)
  -- The lifted theory in the extended signature
  let liftedT : ClosedTheorySet (ParamConst Const (σ :: Γ)) :=
    fun φ => ∃ χ ∈ W.carrier, liftParamCtxFormula σ χ = φ
  have hNotProv : ¬ ClosedTheorySet.Provable liftedT ψc := by
    intro hProv
    exact hAll (W.closed (W.reflect_freshParam_instance hProv))
  rcases ClosedTheorySet.exists_prime_extension_separating
    (T := liftedT)
    (φ := ψc)
    hNotProv with
    ⟨U, hExt, hClosed, hUCons, hPrime, hOmit⟩
  refine ⟨⟨U, hClosed, hUCons, hPrime⟩, ?_, ⟨c, ?_⟩⟩
  · intro φ hφ
    exact hExt ⟨φ, hφ, rfl⟩
  · exact hOmit

end GrowingFrame

end Mettapedia.Logic.HOL
