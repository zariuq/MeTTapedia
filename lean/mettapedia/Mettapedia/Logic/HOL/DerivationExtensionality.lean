import Mettapedia.Logic.HOL.Derivation
import Mettapedia.Logic.HOL.Syntax.ConstMap

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u}
variable {Const : Ty Base → Type v} {Const' : Ty Base → Type w}

/--
An extensional overlay of the small HOL derivation core.

This keeps the original calculus in
`/home/zar/claude/lean-projects/mettapedia/Mettapedia/Logic/HOL/Derivation.lean`
intact, while adding the missing argument-congruence strength needed by standard
extensional HOL equality.
-/
inductive ExtDerivation (Const : Ty Base → Type v) :
    {Γ : Ctx Base} → List (Formula Const Γ) → Formula Const Γ → Prop where
  | hyp {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
      φ ∈ Δ → ExtDerivation Const Δ φ
  | topI {Γ : Ctx Base} {Δ : List (Formula Const Γ)} :
      ExtDerivation Const Δ .top
  | botE {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
      ExtDerivation Const Δ .bot → ExtDerivation Const Δ φ
  | andI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      ExtDerivation Const Δ φ → ExtDerivation Const Δ ψ →
        ExtDerivation Const Δ (.and φ ψ)
  | andEL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      ExtDerivation Const Δ (.and φ ψ) → ExtDerivation Const Δ φ
  | andER {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      ExtDerivation Const Δ (.and φ ψ) → ExtDerivation Const Δ ψ
  | orIL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      ExtDerivation Const Δ φ → ExtDerivation Const Δ (.or φ ψ)
  | orIR {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      ExtDerivation Const Δ ψ → ExtDerivation Const Δ (.or φ ψ)
  | orE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ χ : Formula Const Γ} :
      ExtDerivation Const Δ (.or φ ψ) →
      ExtDerivation Const (φ :: Δ) χ →
      ExtDerivation Const (ψ :: Δ) χ →
      ExtDerivation Const Δ χ
  | impI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      ExtDerivation Const (φ :: Δ) ψ → ExtDerivation Const Δ (.imp φ ψ)
  | impE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      ExtDerivation Const Δ (.imp φ ψ) →
      ExtDerivation Const Δ φ →
      ExtDerivation Const Δ ψ
  | notI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ : Formula Const Γ} :
      ExtDerivation Const (φ :: Δ) .bot → ExtDerivation Const Δ (.not φ)
  | notE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ : Formula Const Γ} :
      ExtDerivation Const Δ (.not φ) →
      ExtDerivation Const Δ φ →
      ExtDerivation Const Δ .bot
  | allI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)} :
      ExtDerivation Const (weakenHyps (Base := Base) (σ := σ) Δ) φ →
      ExtDerivation Const Δ (.all φ)
  | allE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)}
      (t : Term Const Γ σ) :
      ExtDerivation Const Δ (.all φ) →
      ExtDerivation Const Δ (instantiate (Base := Base) t φ)
  | exI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)}
      (t : Term Const Γ σ) :
      ExtDerivation Const Δ (instantiate (Base := Base) t φ) →
      ExtDerivation Const Δ (.ex φ)
  | exE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {ψ : Formula Const Γ} :
      ExtDerivation Const Δ (.ex φ) →
      ExtDerivation Const (φ :: weakenHyps (Base := Base) (σ := σ) Δ)
        (weaken (Base := Base) (σ := σ) ψ) →
      ExtDerivation Const Δ ψ
  | eqRefl {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {τ : Ty Base} (t : Term Const Γ τ) :
      ExtDerivation Const Δ (.eq t t)
  | eqSymm {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {τ : Ty Base} {t u : Term Const Γ τ} :
      ExtDerivation Const Δ (.eq t u) →
      ExtDerivation Const Δ (.eq u t)
  | eqTrans {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {τ : Ty Base} {t u v : Term Const Γ τ} :
      ExtDerivation Const Δ (.eq t u) →
      ExtDerivation Const Δ (.eq u v) →
      ExtDerivation Const Δ (.eq t v)
  | eqPropI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {p q : Formula Const Γ} :
      ExtDerivation Const Δ (.imp p q) →
      ExtDerivation Const Δ (.imp q p) →
      ExtDerivation Const Δ (.eq p q)
  | eqPropEL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {p q : Formula Const Γ} :
      ExtDerivation Const Δ (.eq p q) →
      ExtDerivation Const Δ (.imp p q)
  | eqPropER {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {p q : Formula Const Γ} :
      ExtDerivation Const Δ (.eq p q) →
      ExtDerivation Const Δ (.imp q p)
  | eqApp {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} {f g : Term Const Γ (σ ⇒ τ)} (t : Term Const Γ σ) :
      ExtDerivation Const Δ (.eq f g) →
      ExtDerivation Const Δ (.eq (.app f t) (.app g t))
  | eqAppArg {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} (f : Term Const Γ (σ ⇒ τ)) {t u : Term Const Γ σ} :
      ExtDerivation Const Δ (.eq t u) →
      ExtDerivation Const Δ (.eq (.app f t) (.app f u))
  | eqLam {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} {t u : Term Const (σ :: Γ) τ} :
      ExtDerivation Const (weakenHyps (Base := Base) (σ := σ) Δ) (.eq t u) →
      ExtDerivation Const Δ (.eq (.lam t) (.lam u))
  | funExt {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} {f g : Term Const Γ (σ ⇒ τ)} :
      ExtDerivation Const Δ
        (.all (.eq (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))
                   (.app (weaken (Base := Base) (σ := σ) g) (.var .vz)))) →
      ExtDerivation Const Δ (.eq f g)
  | beta {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} (t : Term Const Γ σ) (u : Term Const (σ :: Γ) τ) :
      ExtDerivation Const Δ (.eq (.app (.lam u) t) (instantiate (Base := Base) t u))
  | eta {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} (f : Term Const Γ (σ ⇒ τ)) :
      ExtDerivation Const Δ (.eq (.lam (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))) f)

namespace ExtDerivation

variable {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ ψ : Formula Const Γ}

abbrev Theorem (Const : Ty Base → Type v) (φ : ClosedFormula Const) : Prop :=
  ExtDerivation Const ([] : List (ClosedFormula Const)) φ

@[simp] theorem mapConst_weakenHyps
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (Δ : List (Formula Const Γ)) :
    weakenHyps
        (Base := Base)
        (Const := Const')
        (σ := σ)
        (Δ.map (Mettapedia.Logic.HOL.mapConst f)) =
      (weakenHyps (Base := Base) (Const := Const) (σ := σ) Δ).map
        (Mettapedia.Logic.HOL.mapConst f) := by
  simp [weakenHyps, List.map_map, Function.comp, Mettapedia.Logic.HOL.mapConst_weaken]

@[simp] theorem rename_weaken
    {Γ' : Ctx Base}
    (ρ : Rename Base Γ Γ')
    (t : Term Const Γ τ) :
    Mettapedia.Logic.HOL.rename
        (Rename.lift (Base := Base) (σ := σ) ρ)
        (weaken (Base := Base) (Const := Const) (σ := σ) t) =
      weaken (Base := Base) (Const := Const) (σ := σ)
        (Mettapedia.Logic.HOL.rename ρ t) := by
  calc
    Mettapedia.Logic.HOL.rename
        (Rename.lift (Base := Base) (σ := σ) ρ)
        (weaken (Base := Base) (Const := Const) (σ := σ) t) =
      Mettapedia.Logic.HOL.rename
        (fun {τ} v =>
          Rename.lift (Base := Base) (σ := σ) ρ
            (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ) v))
        t := by
          simp [weaken, rename_comp]
    _ =
      Mettapedia.Logic.HOL.rename
        (fun {τ} v =>
          Rename.weaken (Base := Base) (Γ := Γ') (σ := σ) (ρ v))
        t := by
          apply rename_ext
          intro τ v
          rfl
    _ =
      weaken (Base := Base) (Const := Const) (σ := σ)
        (Mettapedia.Logic.HOL.rename ρ t) := by
          symm
          simp [weaken, rename_comp]

@[simp] theorem rename_weakenHyps
    {Γ' : Ctx Base}
    (ρ : Rename Base Γ Γ')
    (Δ : List (Formula Const Γ)) :
    weakenHyps
        (Base := Base)
        (Const := Const)
        (σ := σ)
        (Δ.map (Mettapedia.Logic.HOL.rename ρ)) =
      (weakenHyps (Base := Base) (Const := Const) (σ := σ) Δ).map
        (Mettapedia.Logic.HOL.rename (Rename.lift (Base := Base) (σ := σ) ρ)) := by
  simp [weakenHyps, List.map_map, Function.comp, rename_weaken]

theorem abstractConstAt_weakenHyps
    {ρ : Ty Base} {c : Const ρ}
    (Ξ : Ctx Base)
    (Δ : List (Formula Const (Ξ ++ Γ))) :
    weakenHyps
        (Base := Base)
        (Const := Const)
        (σ := σ)
        (Δ.map
          (fun ψ =>
            abstractConstAt (Base := Base) (Γ := Γ) (τ := .prop) c Ξ ψ)) =
      (weakenHyps (Base := Base) (Const := Const) (σ := σ) Δ).map
        (fun ψ =>
          abstractConstAt (Base := Base) (Γ := Γ) (τ := .prop) c (σ :: Ξ) ψ) := by
  simp [weakenHyps, List.map_map, Function.comp]

@[simp] theorem rename_instantiate
    {Γ' : Ctx Base}
    (ρ : Rename Base Γ Γ')
    (t : Term Const Γ σ) (u : Term Const (σ :: Γ) τ) :
    Mettapedia.Logic.HOL.rename ρ (instantiate (Base := Base) t u) =
      instantiate (Base := Base)
        (Mettapedia.Logic.HOL.rename ρ t)
        (Mettapedia.Logic.HOL.rename
          (Rename.lift (Base := Base) (σ := σ) ρ) u) := by
  unfold instantiate
  calc
    Mettapedia.Logic.HOL.rename ρ
        (subst (Subst.single (Base := Base) (Const := Const) t) u) =
      subst
        (fun {τ} v =>
          Mettapedia.Logic.HOL.rename ρ
            ((Subst.single (Base := Base) (Const := Const) t) v))
        u := by
          exact rename_subst (Base := Base) (Const := Const)
            (ρ := ρ)
            (σs := Subst.single (Base := Base) (Const := Const) t)
            (t := u)
    _ =
      subst
        (fun {τ} v =>
          (Subst.single (Base := Base) (Const := Const)
            (Mettapedia.Logic.HOL.rename ρ t))
            ((Rename.lift (Base := Base) (σ := σ) ρ) v))
        u := by
          apply subst_ext
          intro τ v
          cases v with
          | vz => rfl
          | vs v => rfl
    _ =
      subst
        (Subst.single (Base := Base) (Const := Const)
          (Mettapedia.Logic.HOL.rename ρ t))
        (Mettapedia.Logic.HOL.rename
          (Rename.lift (Base := Base) (σ := σ) ρ) u) := by
          symm
          exact subst_rename (Base := Base) (Const := Const)
            (σs := Subst.single (Base := Base) (Const := Const)
              (Mettapedia.Logic.HOL.rename ρ t))
            (ρ := Rename.lift (Base := Base) (σ := σ) ρ)
            (t := u)

def ofBase {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    Derivation Const Δ φ → ExtDerivation Const Δ φ
  | .hyp h => .hyp h
  | .topI => .topI
  | .botE h => .botE (ofBase h)
  | .andI hφ hψ => .andI (ofBase hφ) (ofBase hψ)
  | .andEL h => .andEL (ofBase h)
  | .andER h => .andER (ofBase h)
  | .orIL h => .orIL (ofBase h)
  | .orIR h => .orIR (ofBase h)
  | .orE hor hφ hψ => .orE (ofBase hor) (ofBase hφ) (ofBase hψ)
  | .impI h => .impI (ofBase h)
  | .impE hφψ hφ => .impE (ofBase hφψ) (ofBase hφ)
  | .notI h => .notI (ofBase h)
  | .notE hnot hφ => .notE (ofBase hnot) (ofBase hφ)
  | .allI h => .allI (ofBase h)
  | .allE t h => .allE t (ofBase h)
  | .exI t h => .exI t (ofBase h)
  | .exE hex hbody => .exE (ofBase hex) (ofBase hbody)
  | .eqRefl t => .eqRefl t
  | .eqSymm h => .eqSymm (ofBase h)
  | .eqTrans htu huv => .eqTrans (ofBase htu) (ofBase huv)
  | .eqApp t h => .eqApp t (ofBase h)
  | .eqLam h => .eqLam (ofBase h)
  | .funExt h => .funExt (ofBase h)
  | .beta t u => .beta t u
  | .eta f => .eta f

theorem mapConst
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ) :
    ExtDerivation Const Δ φ →
      ExtDerivation Const'
        (Δ.map (Mettapedia.Logic.HOL.mapConst f))
        (Mettapedia.Logic.HOL.mapConst f φ) := by
  intro d
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
      exact .impI ih
  | impE hφψ hφ ihφψ ihφ =>
      exact .impE ihφψ ihφ
  | notI h ih =>
      exact .notI ih
  | notE hnot hφ ihnot ihφ =>
      exact .notE ihnot ihφ
  | allI h ih =>
      exact .allI (by
        simpa [mapConst_weakenHyps] using ih)
  | allE t h ih =>
      simpa [Mettapedia.Logic.HOL.mapConst_instantiate] using
        (.allE (Mettapedia.Logic.HOL.mapConst f t) ih)
  | exI t h ih =>
      rename_i Γ' Δ' σ body
      have ih' : ExtDerivation Const'
          (Δ'.map (Mettapedia.Logic.HOL.mapConst f))
          (instantiate (Base := Base)
            (Mettapedia.Logic.HOL.mapConst f t)
            (Mettapedia.Logic.HOL.mapConst f body)) := by
        simpa [Mettapedia.Logic.HOL.mapConst_instantiate] using ih
      exact .exI (Mettapedia.Logic.HOL.mapConst f t) ih'
  | exE hex hbody ihex ihbody =>
      exact .exE ihex (by
        simpa [mapConst_weakenHyps, Mettapedia.Logic.HOL.mapConst_weaken] using ihbody)
  | eqRefl t =>
      exact .eqRefl (Mettapedia.Logic.HOL.mapConst f t)
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
      exact .eqApp (Mettapedia.Logic.HOL.mapConst f t) ih
  | eqAppArg g h ih =>
      exact .eqAppArg (Mettapedia.Logic.HOL.mapConst f g) ih
  | eqLam h ih =>
      exact .eqLam (by
        simpa [mapConst_weakenHyps] using ih)
  | funExt h ih =>
      exact .funExt (by
        simpa [Mettapedia.Logic.HOL.mapConst, Mettapedia.Logic.HOL.mapConst_weaken] using ih)
  | beta t u =>
      simpa [Mettapedia.Logic.HOL.mapConst, Mettapedia.Logic.HOL.mapConst_instantiate] using
        (.beta (Mettapedia.Logic.HOL.mapConst f t)
          (Mettapedia.Logic.HOL.mapConst f u))
  | eta g =>
      simpa [Mettapedia.Logic.HOL.mapConst, Mettapedia.Logic.HOL.mapConst_weaken] using
        (.eta (Mettapedia.Logic.HOL.mapConst f g))

theorem rename
    {Γ' : Ctx Base}
    (ρ : Rename Base Γ Γ') :
    ExtDerivation Const Δ φ →
      ExtDerivation Const
        (Δ.map (Mettapedia.Logic.HOL.rename ρ))
        (Mettapedia.Logic.HOL.rename ρ φ) := by
  intro d
  induction d generalizing Γ' with
  | hyp hmem =>
      exact .hyp (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  | topI =>
      exact .topI
  | botE h ih =>
      exact .botE (ih ρ)
  | andI hφ hψ ihφ ihψ =>
      exact .andI (ihφ ρ) (ihψ ρ)
  | andEL h ih =>
      exact .andEL (ih ρ)
  | andER h ih =>
      exact .andER (ih ρ)
  | orIL h ih =>
      exact .orIL (ih ρ)
  | orIR h ih =>
      exact .orIR (ih ρ)
  | orE hor hφ hψ ihor ihφ ihψ =>
      refine .orE (ihor ρ) ?_ ?_
      · simpa [List.map] using ihφ ρ
      · simpa [List.map] using ihψ ρ
  | impI h ih =>
      exact .impI (by
        simpa [List.map] using ih ρ)
  | impE himp hφ ihimp ihφ =>
      exact .impE (ihimp ρ) (ihφ ρ)
  | notI h ih =>
      exact .notI (by
        simpa [List.map] using ih ρ)
  | notE hnot hφ ihnot ihφ =>
      exact .notE (ihnot ρ) (ihφ ρ)
  | allI h ih =>
      rename_i Γ₀ Δ₀ σ body
      exact .allI (by
        simpa [rename_weakenHyps] using
          ih (Rename.lift (Base := Base) (σ := σ) ρ))
  | allE t h ih =>
      simpa [rename_instantiate] using
        (.allE (Mettapedia.Logic.HOL.rename ρ t) (ih ρ))
  | exI t h ih =>
      rename_i Γ₀ Δ₀ σ body
      have ih' :
          ExtDerivation Const
            (Δ₀.map (Mettapedia.Logic.HOL.rename ρ))
            (instantiate (Base := Base)
              (Mettapedia.Logic.HOL.rename ρ t)
              (Mettapedia.Logic.HOL.rename
                (Rename.lift (Base := Base) (σ := σ) ρ) body)) := by
        simpa [rename_instantiate (Base := Base) (Const := Const) (ρ := ρ) t body] using
          ih ρ
      exact .exI (Mettapedia.Logic.HOL.rename ρ t) ih'
  | exE hex hbody ihex ihbody =>
      rename_i Γ₀ Δ₀ σ body ψ
      refine .exE (ihex ρ) ?_
      simpa [List.map, rename_weakenHyps, rename_weaken] using
        ihbody (Rename.lift (Base := Base) (σ := σ) ρ)
  | eqRefl t =>
      exact .eqRefl (Mettapedia.Logic.HOL.rename ρ t)
  | eqSymm h ih =>
      exact .eqSymm (ih ρ)
  | eqTrans htu huv ihtu ihuv =>
      exact .eqTrans (ihtu ρ) (ihuv ρ)
  | eqPropI hpq hqp ihpq ihqp =>
      exact .eqPropI (ihpq ρ) (ihqp ρ)
  | eqPropEL hpq ihpq =>
      exact .eqPropEL (ihpq ρ)
  | eqPropER hpq ihpq =>
      exact .eqPropER (ihpq ρ)
  | eqApp t h ih =>
      exact .eqApp (Mettapedia.Logic.HOL.rename ρ t) (ih ρ)
  | eqAppArg f h ih =>
      exact .eqAppArg (Mettapedia.Logic.HOL.rename ρ f) (ih ρ)
  | eqLam h ih =>
      rename_i Γ₀ Δ₀ σ τ t u
      exact .eqLam (by
        simpa [rename_weakenHyps] using
          ih (Rename.lift (Base := Base) (σ := σ) ρ))
  | funExt h ih =>
      rename_i Γ₀ Δ₀ σ τ f g
      exact .funExt (by
        simpa [Mettapedia.Logic.HOL.rename, rename_weaken] using ih ρ)
  | beta t u =>
      rename_i Γ₀ Δ₀ σ τ
      simpa [Mettapedia.Logic.HOL.rename, rename_instantiate] using
        (.beta (Mettapedia.Logic.HOL.rename ρ t)
          (Mettapedia.Logic.HOL.rename
            (Rename.lift (Base := Base) (σ := σ) ρ) u))
  | eta f =>
      rename_i Γ₀ Δ₀ σ τ
      simpa [Mettapedia.Logic.HOL.rename, rename_weaken] using
        (.eta (Mettapedia.Logic.HOL.rename ρ f))

/-- The theorem on constants: abstracting a constant from a derivation.
    Transforms a derivation by replacing constant `c` with a bound variable
    at depth |Ξ| in all terms. -/
theorem abstractConstAt_deriv
    {Γ : Ctx Base} {Ξ : Ctx Base} {ρ : Ty Base}
    (c : Const ρ)
    {Δ : List (Formula Const ((Ξ ++ Γ)))}
    {φ : Formula Const ((Ξ ++ Γ))}
    (d : ExtDerivation Const Δ φ) :
    ExtDerivation Const
      (Δ.map (abstractConstAt (Base := Base) (Γ := Γ) c Ξ))
      (abstractConstAt (Base := Base) (Γ := Γ) c Ξ φ) := by
  let go :
      ∀ {Γ₀ : Ctx Base} {Δ₀ : List (Formula Const Γ₀)} {φ₀ : Formula Const Γ₀},
        ExtDerivation Const Δ₀ φ₀ →
        ∀ {Γ : Ctx Base} {Ξ : Ctx Base} {ρ : Ty Base}
          (hctx : Γ₀ = Ξ ++ Γ) (c : Const ρ),
          ExtDerivation Const
            ((hctx ▸ Δ₀).map (abstractConstAt (Base := Base) (Γ := Γ) c Ξ))
            (abstractConstAt (Base := Base) (Γ := Γ) c Ξ (hctx ▸ φ₀)) := by
    intro Γ₀ Δ₀ φ₀ d
    induction d with
    | hyp hmem =>
        intro Γ Ξ ρ hctx c
        subst hctx
        exact .hyp (List.mem_map.mpr ⟨_, hmem, rfl⟩)
    | topI =>
        intro Γ Ξ ρ hctx c
        subst hctx
        simp [abstractConstAt]
        exact .topI
    | botE h ih =>
        intro Γ Ξ ρ hctx c
        subst hctx
        exact .botE (by simpa [abstractConstAt] using ih rfl c)
    | andI hφ hψ ihφ ihψ =>
        intro Γ Ξ ρ hctx c
        subst hctx
        simpa [abstractConstAt] using
          (.andI
            (by simpa [abstractConstAt] using ihφ rfl c)
            (by simpa [abstractConstAt] using ihψ rfl c))
    | andEL h ih =>
        intro Γ Ξ ρ hctx c
        subst hctx
        exact .andEL (by simpa [abstractConstAt] using ih rfl c)
    | andER h ih =>
        intro Γ Ξ ρ hctx c
        subst hctx
        exact .andER (by simpa [abstractConstAt] using ih rfl c)
    | orIL h ih =>
        intro Γ Ξ ρ hctx c
        subst hctx
        simpa [abstractConstAt] using
          (.orIL (by simpa [abstractConstAt] using ih rfl c))
    | orIR h ih =>
        intro Γ Ξ ρ hctx c
        subst hctx
        simpa [abstractConstAt] using
          (.orIR (by simpa [abstractConstAt] using ih rfl c))
    | orE hor hφ hψ ihor ihφ ihψ =>
        intro Γ Ξ ρ hctx c
        subst hctx
        exact .orE
          (by simpa [abstractConstAt] using ihor rfl c)
          (by simpa [List.map, abstractConstAt] using ihφ rfl c)
          (by simpa [List.map, abstractConstAt] using ihψ rfl c)
    | impI h ih =>
        intro Γ Ξ ρ hctx c
        subst hctx
        simpa [abstractConstAt] using
          (.impI (by simpa [List.map, abstractConstAt] using ih rfl c))
    | impE himp hφ ihimp ihφ =>
        intro Γ Ξ ρ hctx c
        subst hctx
        exact .impE
          (by simpa [abstractConstAt] using ihimp rfl c)
          (by simpa [abstractConstAt] using ihφ rfl c)
    | notI h ih =>
        intro Γ Ξ ρ hctx c
        subst hctx
        simpa [abstractConstAt] using
          (.notI (by simpa [List.map, abstractConstAt] using ih rfl c))
    | notE hnot hφ ihnot ihφ =>
        intro Γ Ξ ρ hctx c
        subst hctx
        simpa [abstractConstAt] using
          (.notE
            (by simpa [abstractConstAt] using ihnot rfl c)
            (by simpa [abstractConstAt] using ihφ rfl c))
    | allI h ih =>
        intro Γ Ξ ρ hctx c
        subst hctx
        rename_i _ σ Δ φ
        have ih' :
            ExtDerivation Const
              (weakenHyps (Base := Base) (Const := Const) (σ := σ)
                (Δ.map (abstractConstAt (Base := Base) (Γ := Γ) c Ξ)))
              (abstractConstAt (Base := Base) (Γ := Γ) c (σ :: Ξ) φ) := by
          simpa [abstractConstAt_weakenHyps] using
            (ih (Γ := Γ) (Ξ := σ :: Ξ) rfl c)
        simpa [abstractConstAt] using (.allI ih')
    | allE t h ih =>
        intro Γ Ξ ρ hctx c
        subst hctx
        simpa [abstractConstAt_instantiate] using
          (.allE (abstractConstAt (Base := Base) (Γ := Γ) c Ξ t)
            (by simpa [abstractConstAt] using ih rfl c))
    | exI t h ih =>
        intro Γ Ξ ρ hctx c
        subst hctx
        simpa [abstractConstAt, abstractConstAt_instantiate] using
          (.exI (abstractConstAt (Base := Base) (Γ := Γ) c Ξ t)
            (by simpa [abstractConstAt_instantiate] using ih rfl c))
    | exE hex hbody ihex ihbody =>
        intro Γ Ξ ρ hctx c
        subst hctx
        rename_i _ σ Δ φ ψ
        have hex' :
            ExtDerivation Const
              (Δ.map (abstractConstAt (Base := Base) (Γ := Γ) c Ξ))
              (.ex (abstractConstAt (Base := Base) (Γ := Γ) c (σ :: Ξ) φ)) := by
          simpa [abstractConstAt] using ihex rfl c
        have hbody' :
            ExtDerivation Const
              (abstractConstAt (Base := Base) (Γ := Γ) c (σ :: Ξ) φ ::
                weakenHyps (Base := Base) (Const := Const) (σ := σ)
                  (Δ.map (abstractConstAt (Base := Base) (Γ := Γ) c Ξ)))
              (weaken (Base := Base) (Const := Const) (σ := σ)
                (abstractConstAt (Base := Base) (Γ := Γ) c Ξ ψ)) := by
          simpa [List.map, abstractConstAt_weakenHyps, abstractConstAt_weaken] using
            (ihbody (Γ := Γ) (Ξ := σ :: Ξ) rfl c)
        exact .exE hex' hbody'
    | eqRefl t =>
        intro Γ Ξ ρ hctx c
        subst hctx
        simp [abstractConstAt]
        exact .eqRefl (abstractConstAt (Base := Base) (Γ := Γ) c Ξ t)
    | eqSymm h ih =>
        intro Γ Ξ ρ hctx c
        subst hctx
        simpa [abstractConstAt] using
          (.eqSymm (by simpa [abstractConstAt] using ih rfl c))
    | eqTrans htu huv ihtu ihuv =>
        intro Γ Ξ ρ hctx c
        subst hctx
        simpa [abstractConstAt] using
          (.eqTrans
            (by simpa [abstractConstAt] using ihtu rfl c)
            (by simpa [abstractConstAt] using ihuv rfl c))
    | eqPropI hpq hqp ihpq ihqp =>
        intro Γ Ξ ρ hctx c
        subst hctx
        simpa [abstractConstAt] using
          (.eqPropI
            (by simpa [abstractConstAt] using ihpq rfl c)
            (by simpa [abstractConstAt] using ihqp rfl c))
    | eqPropEL hpq ihpq =>
        intro Γ Ξ ρ hctx c
        subst hctx
        simpa [abstractConstAt] using
          (.eqPropEL (by simpa [abstractConstAt] using ihpq rfl c))
    | eqPropER hpq ihpq =>
        intro Γ Ξ ρ hctx c
        subst hctx
        simpa [abstractConstAt] using
          (.eqPropER (by simpa [abstractConstAt] using ihpq rfl c))
    | eqApp t h ih =>
        intro Γ Ξ ρ hctx c
        subst hctx
        simpa [abstractConstAt] using
          (.eqApp (abstractConstAt (Base := Base) (Γ := Γ) c Ξ t)
            (by simpa [abstractConstAt] using ih rfl c))
    | eqAppArg f h ih =>
        intro Γ Ξ ρ hctx c
        subst hctx
        simpa [abstractConstAt] using
          (.eqAppArg (abstractConstAt (Base := Base) (Γ := Γ) c Ξ f)
            (by simpa [abstractConstAt] using ih rfl c))
    | eqLam h ih =>
        intro Γ Ξ ρ hctx c
        subst hctx
        rename_i _ σ τ Δ t u
        have ih' :
            ExtDerivation Const
              (weakenHyps (Base := Base) (Const := Const) (σ := σ)
                (Δ.map (abstractConstAt (Base := Base) (Γ := Γ) c Ξ)))
              (.eq (abstractConstAt (Base := Base) (Γ := Γ) c (σ :: Ξ) t)
                (abstractConstAt (Base := Base) (Γ := Γ) c (σ :: Ξ) u)) := by
          simpa [abstractConstAt, abstractConstAt_weakenHyps] using
            (ih (Γ := Γ) (Ξ := σ :: Ξ) rfl c)
        simpa [abstractConstAt] using (.eqLam ih')
    | funExt h ih =>
        intro Γ Ξ ρ hctx c
        subst hctx
        simpa [abstractConstAt, abstractConstAt_weaken] using
          (.funExt (by
            simpa [abstractConstAt, abstractConstAt_weaken] using ih rfl c))
    | beta t u =>
        intro Γ Ξ ρ hctx c
        subst hctx
        simpa [abstractConstAt, abstractConstAt_instantiate] using
          (.beta (abstractConstAt (Base := Base) (Γ := Γ) c Ξ t)
            (abstractConstAt (Base := Base) (Γ := Γ) c (_ :: Ξ) u))
    | eta f =>
        intro Γ Ξ ρ hctx c
        subst hctx
        simpa [abstractConstAt, abstractConstAt_weaken] using
          (.eta (abstractConstAt (Base := Base) (Γ := Γ) c Ξ f))
  simpa using go d rfl c

theorem closedTheory_mapConst
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (h : ExtDerivation Const Δ φ) :
    ExtDerivation Const'
      (Δ.map (Mettapedia.Logic.HOL.mapClosedFormula f))
      (Mettapedia.Logic.HOL.mapClosedFormula f φ) := by
  simpa [Mettapedia.Logic.HOL.mapClosedFormula] using
    (mapConst (Base := Base) (Const := Const) (Const' := Const')
      (Δ := Δ) (φ := φ) f h)

theorem theorem_mapConst
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    {φ : ClosedFormula Const}
    (h : Theorem Const φ) :
    Theorem Const' (Mettapedia.Logic.HOL.mapClosedFormula f φ) := by
  simpa [Theorem, Mettapedia.Logic.HOL.mapClosedFormula] using
    (mapConst (Base := Base) (Const := Const) (Const' := Const')
      (Δ := ([] : List (ClosedFormula Const))) (φ := φ) f h)

theorem imp_mp
    (hImp : ExtDerivation Const Δ (.imp φ ψ))
    (hφ : ExtDerivation Const Δ φ) :
    ExtDerivation Const Δ ψ :=
  .impE hImp hφ

theorem not_bot_of
    (hNot : ExtDerivation Const Δ (.not φ))
    (hφ : ExtDerivation Const Δ φ) :
    ExtDerivation Const Δ .bot :=
  .notE hNot hφ

theorem mono {Γ : Ctx Base} {Δ Δ' : List (Formula Const Γ)} {φ : Formula Const Γ}
    (hsub : ∀ {χ : Formula Const Γ}, χ ∈ Δ → χ ∈ Δ') :
    ExtDerivation Const Δ φ → ExtDerivation Const Δ' φ := by
  intro d
  induction d with
  | hyp hmem =>
      exact .hyp (hsub hmem)
  | topI =>
      exact .topI
  | botE h ih =>
      exact .botE (ih hsub)
  | andI hφ hψ ihφ ihψ =>
      exact .andI (ihφ hsub) (ihψ hsub)
  | andEL h ih =>
      exact .andEL (ih hsub)
  | andER h ih =>
      exact .andER (ih hsub)
  | orIL h ih =>
      exact .orIL (ih hsub)
  | orIR h ih =>
      exact .orIR (ih hsub)
  | orE hor hφ hψ ihor ihφ ihψ =>
      refine .orE (ihor hsub) ?_ ?_
      · exact ihφ (by
          intro χ hχ
          rw [List.mem_cons] at hχ ⊢
          rcases hχ with rfl | hχ
          · exact Or.inl rfl
          · exact Or.inr (hsub hχ))
      · exact ihψ (by
          intro χ hχ
          rw [List.mem_cons] at hχ ⊢
          rcases hχ with rfl | hχ
          · exact Or.inl rfl
          · exact Or.inr (hsub hχ))
  | impI h ih =>
      exact .impI (ih (by
        intro χ hχ
        rw [List.mem_cons] at hχ ⊢
        rcases hχ with rfl | hχ
        · exact Or.inl rfl
        · exact Or.inr (hsub hχ)))
  | impE himp hφ ihimp ihφ =>
      exact .impE (ihimp hsub) (ihφ hsub)
  | notI h ih =>
      exact .notI (ih (by
        intro χ hχ
        rw [List.mem_cons] at hχ ⊢
        rcases hχ with rfl | hχ
        · exact Or.inl rfl
        · exact Or.inr (hsub hχ)))
  | notE hnot hφ ihnot ihφ =>
      exact .notE (ihnot hsub) (ihφ hsub)
  | allI h ih =>
      exact .allI (ih (by
        intro χ hχ
        rcases List.mem_map.mp hχ with ⟨ψ, hψ, rfl⟩
        exact List.mem_map.mpr ⟨ψ, hsub hψ, rfl⟩))
  | allE t h ih =>
      exact .allE t (ih hsub)
  | exI t h ih =>
      exact .exI t (ih hsub)
  | exE hex hbody ihex ihbody =>
      refine .exE (ihex hsub) ?_
      exact ihbody (by
        intro χ hχ
        rw [List.mem_cons] at hχ ⊢
        rcases hχ with rfl | hχ
        · exact Or.inl rfl
        · rcases List.mem_map.mp hχ with ⟨ψ, hψ, rfl⟩
          exact Or.inr (List.mem_map.mpr ⟨ψ, hsub hψ, rfl⟩))
  | eqRefl t =>
      exact .eqRefl t
  | eqSymm h ih =>
      exact .eqSymm (ih hsub)
  | eqTrans htu huv ihtu ihuv =>
      exact .eqTrans (ihtu hsub) (ihuv hsub)
  | eqPropI hpq hqp ihpq ihqp =>
      exact .eqPropI (ihpq hsub) (ihqp hsub)
  | eqPropEL hpq ihpq =>
      exact .eqPropEL (ihpq hsub)
  | eqPropER hpq ihpq =>
      exact .eqPropER (ihpq hsub)
  | eqApp t h ih =>
      exact .eqApp t (ih hsub)
  | eqAppArg f h ih =>
      exact .eqAppArg f (ih hsub)
  | eqLam h ih =>
      exact .eqLam (ih (by
        intro χ hχ
        rcases List.mem_map.mp hχ with ⟨ψ, hψ, rfl⟩
        exact List.mem_map.mpr ⟨ψ, hsub hψ, rfl⟩))
  | funExt h ih =>
      exact .funExt (ih hsub)
  | beta t u =>
      exact .beta t u
  | eta f =>
      exact .eta f

theorem ofTheorem {φ : ClosedFormula Const} {Δ : List (ClosedFormula Const)}
    (d : Theorem Const φ) : ExtDerivation Const Δ φ :=
  mono (Δ := []) (Δ' := Δ) (φ := φ) (by
    intro χ hχ
    nomatch hχ) d

theorem theorem_imp_refl (φ : ClosedFormula Const) :
    Theorem Const (.imp φ φ) :=
  .impI (.hyp (by simp))

theorem theorem_imp_top (φ : ClosedFormula Const) :
    Theorem Const (.imp φ .top) :=
  .impI .topI

theorem theorem_imp_trans {φ ψ χ : ClosedFormula Const}
    (hφψ : Theorem Const (.imp φ ψ))
    (hψχ : Theorem Const (.imp ψ χ)) :
    Theorem Const (.imp φ χ) := by
  refine .impI ?_
  have hψ : ExtDerivation Const [φ] ψ :=
    .impE (ofTheorem (Δ := [φ]) hφψ) (.hyp (by simp))
  exact .impE (ofTheorem (Δ := [φ]) hψχ) hψ

theorem eqProp_mp_left {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {p q : Formula Const Γ}
    (hpq : ExtDerivation Const Δ (.eq p q))
    (hp : ExtDerivation Const Δ p) :
    ExtDerivation Const Δ q :=
  .impE (.eqPropEL hpq) hp

theorem eqProp_mp_right {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {p q : Formula Const Γ}
    (hpq : ExtDerivation Const Δ (.eq p q))
    (hq : ExtDerivation Const Δ q) :
    ExtDerivation Const Δ p :=
  .impE (.eqPropER hpq) hq

theorem eqAppCongr {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {σ τ : Ty Base} {f g : Term Const Γ (σ ⇒ τ)} {t u : Term Const Γ σ}
    (hfg : ExtDerivation Const Δ (.eq f g))
    (htu : ExtDerivation Const Δ (.eq t u)) :
    ExtDerivation Const Δ (.eq (.app f t) (.app g u)) := by
  exact
    .eqTrans
      (.eqApp t hfg)
      (.eqAppArg g htu)

theorem eqAppCongrSelf {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {σ τ : Ty Base} {f : Term Const Γ (σ ⇒ τ)} {t u : Term Const Γ σ}
    (htu : ExtDerivation Const Δ (.eq t u)) :
    ExtDerivation Const Δ (.eq (.app f t) (.app f u)) :=
  .eqAppArg f htu

/-- Discharge a theorem assumption from the head of the context.
    If χ is provable from nothing, any derivation using χ as an
    assumption can eliminate it. -/
theorem discharge_head_theorem
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {χ φ : Formula Const Γ}
    (hχ : ExtDerivation Const [] χ)
    (d : ExtDerivation Const (χ :: Δ) φ) :
    ExtDerivation Const Δ φ := by
  apply ExtDerivation.impE (.impI d)
  exact mono (fun h => absurd h List.not_mem_nil) hχ

/-- Discharge a list of theorem assumptions from the front of the context. -/
theorem discharge_theorem_list
    {Γ : Ctx Base} {Θ Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ}
    (hΘ : ∀ {χ : Formula Const Γ}, χ ∈ Θ → ExtDerivation Const [] χ)
    (d : ExtDerivation Const (Θ ++ Δ) φ) :
    ExtDerivation Const Δ φ := by
  induction Θ with
  | nil => simpa using d
  | cons χ Θ ih =>
      have hχ : ExtDerivation Const [] χ := hΘ List.mem_cons_self
      have d' : ExtDerivation Const (Θ ++ Δ) φ :=
        discharge_head_theorem hχ (by simpa [List.cons_append] using d)
      have hΘ' : ∀ {ψ : Formula Const Γ}, ψ ∈ Θ → ExtDerivation Const [] ψ :=
        fun hψ => hΘ (List.mem_cons_of_mem _ hψ)
      exact ih hΘ' d'

end ExtDerivation

end Mettapedia.Logic.HOL
