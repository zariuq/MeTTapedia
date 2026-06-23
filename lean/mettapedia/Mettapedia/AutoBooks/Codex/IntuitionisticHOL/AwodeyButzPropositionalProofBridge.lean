import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzPropositionalFragment
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Terms

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v

namespace SimpleTy

variable {Base : Type u}

/-- Translate a simple-fragment context into the native HOL context syntax. -/
abbrev toCtx (Γ : List (SimpleTy Base)) : Ctx Base :=
  Γ.map SimpleTy.toTy

@[simp] theorem toCtx_nil :
    toCtx ([] : List (SimpleTy Base)) = [] :=
  rfl

@[simp] theorem toCtx_cons (τ : SimpleTy Base) (Γ : List (SimpleTy Base)) :
    toCtx (τ :: Γ) = τ.toTy :: toCtx Γ :=
  rfl

end SimpleTy

namespace SimpleVar

variable {Base : Type u}

/-- Embed a simple-fragment variable into the native HOL de Bruijn variable syntax. -/
def toVar :
    {Γ : List (SimpleTy Base)} → {τ : SimpleTy Base} →
      SimpleVar Base Γ τ → Var (SimpleTy.toCtx Γ) τ.toTy
  | _ :: _, _, .vz => .vz
  | _ :: _, _, .vs x => .vs (toVar x)

@[simp] theorem toVar_vz (τ : SimpleTy Base) (Γ : List (SimpleTy Base)) :
    toVar (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ) = Var.vz :=
  rfl

@[simp] theorem toVar_vs (υ : SimpleTy Base) (x : SimpleVar Base Γ τ) :
    toVar (SimpleVar.vs (υ := υ) x) = Var.vs (toVar x) :=
  rfl

end SimpleVar

namespace SimpleTerm

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Embed a simple-fragment term into the native HOL term syntax. -/
def toTerm :
    {Γ : List (SimpleTy Base)} → {τ : SimpleTy Base} →
      SimpleTerm Base Const Γ τ → Term Const (SimpleTy.toCtx Γ) τ.toTy
  | _, _, .var x => .var (SimpleVar.toVar x)
  | _, _, .const c => .const c

@[simp] theorem toTerm_var (x : SimpleVar Base Γ τ) :
    toTerm (.var x : SimpleTerm Base Const Γ τ) = .var (SimpleVar.toVar x) :=
  rfl

@[simp] theorem toTerm_const (c : Const τ.toTy) :
    toTerm (.const c : SimpleTerm Base Const Γ τ) = .const c :=
  rfl

end SimpleTerm

namespace SimpleSubst

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Auxiliary recursion exposing the native HOL substitution function shape. -/
def toSubstAux :
    {Γ Δ : List (SimpleTy Base)} →
      SimpleSubst Base Const Γ Δ →
      {τ : Ty Base} →
      Var (SimpleTy.toCtx Γ) τ →
      Term Const (SimpleTy.toCtx Δ) τ
  | [], _, _, _, x => nomatch x
  | _ :: _, _, σs, _, Var.vz => SimpleTerm.toTerm (σs SimpleVar.vz)
  | _ :: _, _, σs, _, Var.vs x => toSubstAux (tail σs) x

/-- Translate a simple-fragment substitution into a native HOL substitution. -/
def toSubst :
    {Γ Δ : List (SimpleTy Base)} →
      SimpleSubst Base Const Γ Δ →
      Subst Const (SimpleTy.toCtx Γ) (SimpleTy.toCtx Δ)
  | _, _, σs => toSubstAux σs

@[simp] theorem toSubst_vz (σs : SimpleSubst Base Const (τ :: Γ) Δ) :
    toSubst σs (Var.vz : Var (SimpleTy.toCtx (τ :: Γ)) τ.toTy) =
      SimpleTerm.toTerm (σs SimpleVar.vz) := by
  simp [toSubst, toSubstAux]

@[simp] theorem toSubst_vs (σs : SimpleSubst Base Const (τ :: Γ) Δ)
    {ρ : Ty Base} (x : Var (SimpleTy.toCtx Γ) ρ) :
    toSubst σs (Var.vs x) = toSubst (tail σs) x := by
  simp [toSubst, toSubstAux]

@[simp] theorem toSubst_apply_toVar
    (σs : SimpleSubst Base Const Γ Δ) (x : SimpleVar Base Γ τ) :
    toSubst σs (SimpleVar.toVar x) = SimpleTerm.toTerm (σs x) := by
  induction x generalizing Δ with
  | vz =>
      simp
  | @vs Γ υ τ x ih =>
      change toSubst (tail σs) (SimpleVar.toVar x) =
        SimpleTerm.toTerm ((tail σs) x)
      exact ih (σs := tail σs)

end SimpleSubst

namespace SimpleTerm

variable {Base : Type u} {Const : Ty Base → Type v}

@[simp] theorem toTerm_subst (σs : SimpleSubst Base Const Γ Δ)
    (t : SimpleTerm Base Const Γ τ) :
    toTerm (SimpleTerm.subst σs t) =
      Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst (SimpleSubst.toSubst σs) (toTerm t) := by
  cases t with
  | var x =>
      simp [SimpleTerm.subst,
        SimpleSubst.toSubst_apply_toVar (σs := σs) (x := x)]
  | const c =>
      rfl

end SimpleTerm

namespace SimplePropFormula

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Embed the live simple propositional fragment into the native HOL formula syntax. -/
def toFormula :
    {Γ : List (SimpleTy Base)} →
      SimplePropFormula Base Const Γ → Formula Const (SimpleTy.toCtx Γ)
  | _, .atom t => SimpleTerm.toTerm t
  | _, .top => .top
  | _, .bot => .bot
  | _, .conj φ ψ => .and (toFormula φ) (toFormula ψ)
  | _, .disj φ ψ => .or (toFormula φ) (toFormula ψ)
  | _, .impl φ ψ => .imp (toFormula φ) (toFormula ψ)

@[simp] theorem toFormula_atom (t : SimpleTerm Base Const Γ .prop) :
    toFormula (.atom t : SimplePropFormula Base Const Γ) = SimpleTerm.toTerm t :=
  by simp [toFormula]

@[simp] theorem toFormula_top :
    toFormula (.top : SimplePropFormula Base Const Γ) = (.top : Formula Const (SimpleTy.toCtx Γ)) :=
  by simp [toFormula]

@[simp] theorem toFormula_bot :
    toFormula (.bot : SimplePropFormula Base Const Γ) = (.bot : Formula Const (SimpleTy.toCtx Γ)) :=
  by simp [toFormula]

@[simp] theorem toFormula_conj (φ ψ : SimplePropFormula Base Const Γ) :
    toFormula (.conj φ ψ) = .and (toFormula φ) (toFormula ψ) :=
  by simp [toFormula]

@[simp] theorem toFormula_disj (φ ψ : SimplePropFormula Base Const Γ) :
    toFormula (.disj φ ψ) = .or (toFormula φ) (toFormula ψ) :=
  by simp [toFormula]

@[simp] theorem toFormula_impl (φ ψ : SimplePropFormula Base Const Γ) :
    toFormula (.impl φ ψ) = .imp (toFormula φ) (toFormula ψ) :=
  by simp [toFormula]

@[simp] theorem toFormula_subst (σs : SimpleSubst Base Const Γ Δ)
    (φ : SimplePropFormula Base Const Γ) :
    toFormula (SimplePropFormula.subst σs φ) =
      Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst (SimpleSubst.toSubst σs) (toFormula φ) := by
  induction φ with
  | atom t =>
      simp only [SimplePropFormula.subst, toFormula]
      change
        SimpleTerm.toTerm (SimpleTerm.subst σs t) =
          Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst
            (SimpleSubst.toSubst σs) (SimpleTerm.toTerm t)
      exact SimpleTerm.toTerm_subst (σs := σs) (t := t)
  | top =>
      simp only [SimplePropFormula.subst, toFormula,
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst]
  | bot =>
      simp only [SimplePropFormula.subst, toFormula,
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst]
  | conj φ ψ ihφ ihψ =>
      simp only [SimplePropFormula.subst, toFormula,
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
      simp only [SimplePropFormula.subst, toFormula,
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst, ihφ, ihψ]
  | impl φ ψ ihφ ihψ =>
      simp only [SimplePropFormula.subst, toFormula,
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst, ihφ, ihψ]

end SimplePropFormula

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
