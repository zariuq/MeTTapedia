import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzPropositionalProofBridge
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Models
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Soundness

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v

namespace SimpleTerm

variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ : List (SimpleTy Base)} {τ υ : SimpleTy Base}

@[simp] theorem toTerm_weaken (t : SimpleTerm Base Const Γ τ) :
    toTerm (SimpleTerm.weaken (υ := υ) t) =
      Mettapedia.AutoBooks.Codex.IntuitionisticHOL.weaken
        (Base := Base) (Const := Const) (σ := υ.toTy) (toTerm t) := by
  cases t <;> rfl

end SimpleTerm

namespace SimpleSubst

variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ Δ : List (SimpleTy Base)} {τ υ : SimpleTy Base}

/-- Lift a simple substitution under one additional bound variable. -/
def lift (σs : SimpleSubst Base Const Γ Δ) :
    SimpleSubst Base Const (υ :: Γ) (υ :: Δ) :=
  SimpleSubst.cons (.var (SimpleVar.vz : SimpleVar Base (υ :: Δ) υ))
    (fun x => SimpleTerm.weaken (υ := υ) (σs x))

@[simp] theorem lift_vz (σs : SimpleSubst Base Const Γ Δ) :
    lift (υ := υ) σs (SimpleVar.vz : SimpleVar Base (υ :: Γ) υ) =
      (.var (SimpleVar.vz : SimpleVar Base (υ :: Δ) υ) : SimpleTerm Base Const (υ :: Δ) υ) :=
  rfl

@[simp] theorem lift_vs (σs : SimpleSubst Base Const Γ Δ) (x : SimpleVar Base Γ τ) :
    lift (υ := υ) σs (SimpleVar.vs x) = SimpleTerm.weaken (υ := υ) (σs x) :=
  rfl

@[simp] theorem toSubst_weaken_apply
    (σs : SimpleSubst Base Const Γ Δ) {ρ : Ty Base}
    (x : Var (SimpleTy.toCtx Γ) ρ) :
    SimpleSubst.toSubst (fun {_τ} y => SimpleTerm.weaken (υ := υ) (σs y)) x =
      rename
        (Rename.weaken (Base := Base) (Γ := SimpleTy.toCtx Δ) (σ := υ.toTy))
        (SimpleSubst.toSubst σs x) := by
  induction Γ generalizing ρ with
  | nil =>
      cases x
  | cons τ Γ ih =>
      cases x with
      | vz =>
          exact SimpleTerm.toTerm_weaken (υ := υ)
            (t := σs (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ))
      | vs x =>
          change SimpleSubst.toSubst
              (fun {_τ} y => SimpleTerm.weaken (υ := υ) ((SimpleSubst.tail σs) y)) x =
            rename
              (Rename.weaken (Base := Base) (Γ := SimpleTy.toCtx Δ) (σ := υ.toTy))
              (SimpleSubst.toSubst (SimpleSubst.tail σs) x)
          exact ih (σs := SimpleSubst.tail σs) (x := x)

@[simp] theorem toSubst_lift_apply
    (σs : SimpleSubst Base Const Γ Δ) {ρ : Ty Base}
    (x : Var (SimpleTy.toCtx (υ :: Γ)) ρ) :
    toSubst (lift (υ := υ) σs) x =
      Mettapedia.Logic.HOL.Subst.lift
        (Base := Base) (Const := Const) (σ := υ.toTy) (toSubst σs) x := by
  cases x with
  | vz =>
      rfl
  | vs x =>
      change SimpleSubst.toSubst (fun {τ} y => SimpleTerm.weaken (υ := υ) (σs y)) x =
        rename
          (Rename.weaken (Base := Base) (Γ := SimpleTy.toCtx Δ) (σ := υ.toTy))
          (SimpleSubst.toSubst σs x)
      exact toSubst_weaken_apply (σs := σs) (υ := υ) x

end SimpleSubst

/--
First quantified extension of the live simple proposition fragment, still using
only the proposition/base-sort term layer.
-/
inductive SimpleQuantifiedFormula
    (Base : Type u) (Const : Ty Base → Type v) :
    List (SimpleTy Base) → Type (max u v) where
  | atom : SimpleTerm Base Const Γ .prop → SimpleQuantifiedFormula Base Const Γ
  | top : SimpleQuantifiedFormula Base Const Γ
  | bot : SimpleQuantifiedFormula Base Const Γ
  | conj : SimpleQuantifiedFormula Base Const Γ → SimpleQuantifiedFormula Base Const Γ →
      SimpleQuantifiedFormula Base Const Γ
  | disj : SimpleQuantifiedFormula Base Const Γ → SimpleQuantifiedFormula Base Const Γ →
      SimpleQuantifiedFormula Base Const Γ
  | impl : SimpleQuantifiedFormula Base Const Γ → SimpleQuantifiedFormula Base Const Γ →
      SimpleQuantifiedFormula Base Const Γ
  | all : (τ : SimpleTy Base) → SimpleQuantifiedFormula Base Const (τ :: Γ) →
      SimpleQuantifiedFormula Base Const Γ
  | ex : (τ : SimpleTy Base) → SimpleQuantifiedFormula Base Const (τ :: Γ) →
      SimpleQuantifiedFormula Base Const Γ

namespace SimpleQuantifiedFormula

variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ Δ : List (SimpleTy Base)}

/-- Substitute simple terms into a quantified simple formula. -/
def subst :
    {Γ Δ : List (SimpleTy Base)} →
      SimpleSubst Base Const Γ Δ →
      SimpleQuantifiedFormula Base Const Γ → SimpleQuantifiedFormula Base Const Δ
  | _, _, σs, .atom t => .atom (SimpleTerm.subst σs t)
  | _, _, _, .top => .top
  | _, _, _, .bot => .bot
  | _, _, σs, .conj φ ψ => .conj (subst σs φ) (subst σs ψ)
  | _, _, σs, .disj φ ψ => .disj (subst σs φ) (subst σs ψ)
  | _, _, σs, .impl φ ψ => .impl (subst σs φ) (subst σs ψ)
  | _, _, σs, .all τ φ => .all τ (subst (SimpleSubst.lift (υ := τ) σs) φ)
  | _, _, σs, .ex τ φ => .ex τ (subst (SimpleSubst.lift (υ := τ) σs) φ)

/-- Translate quantified simple formulas into the native HOL syntax. -/
def toFormula :
    {Γ : List (SimpleTy Base)} →
      SimpleQuantifiedFormula Base Const Γ → Formula Const (SimpleTy.toCtx Γ)
  | _, .atom t => SimpleTerm.toTerm t
  | _, .top => .top
  | _, .bot => .bot
  | _, .conj φ ψ => .and (toFormula φ) (toFormula ψ)
  | _, .disj φ ψ => .or (toFormula φ) (toFormula ψ)
  | _, .impl φ ψ => .imp (toFormula φ) (toFormula ψ)
  | _, .all _ φ => .all (toFormula φ)
  | _, .ex _ φ => .ex (toFormula φ)

@[simp] theorem toFormula_subst (σs : SimpleSubst Base Const Γ Δ)
    (φ : SimpleQuantifiedFormula Base Const Γ) :
    toFormula (subst σs φ) =
      Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst (SimpleSubst.toSubst σs) (toFormula φ) := by
  induction φ generalizing Δ with
  | atom t =>
      simp only [subst, toFormula]
      change SimpleTerm.toTerm (SimpleTerm.subst σs t) =
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst
          (SimpleSubst.toSubst σs) (SimpleTerm.toTerm t)
      exact SimpleTerm.toTerm_subst (σs := σs) (t := t)
  | top =>
      simp [subst, toFormula,
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst]
  | bot =>
      simp [subst, toFormula,
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst]
  | conj φ ψ ihφ ihψ =>
      simp [subst, toFormula,
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
      simp [subst, toFormula,
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst, ihφ, ihψ]
  | impl φ ψ ihφ ihψ =>
      simp [subst, toFormula,
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst, ihφ, ihψ]
  | @all Γ' τ φ ih =>
      have hbody :
          toFormula (subst (SimpleSubst.lift (υ := τ) σs) φ) =
            Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst
              (Mettapedia.Logic.HOL.Subst.lift
                (Base := Base) (Const := Const) (σ := τ.toTy)
                (SimpleSubst.toSubst σs))
              (toFormula φ) := by
        calc
          toFormula (subst (SimpleSubst.lift (υ := τ) σs) φ) =
              Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst
                (SimpleSubst.toSubst (SimpleSubst.lift (υ := τ) σs)) (toFormula φ) := by
                  exact ih (SimpleSubst.lift (υ := τ) σs)
          _ =
              Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst
                (Mettapedia.Logic.HOL.Subst.lift
                  (Base := Base) (Const := Const) (σ := τ.toTy)
                  (SimpleSubst.toSubst σs))
                (toFormula φ) := by
                  exact Mettapedia.Logic.HOL.subst_ext
                    (σs := SimpleSubst.toSubst (SimpleSubst.lift (υ := τ) σs))
                    (τs := Mettapedia.Logic.HOL.Subst.lift
                      (Base := Base) (Const := Const) (σ := τ.toTy)
                      (SimpleSubst.toSubst σs))
                    (h := fun v => SimpleSubst.toSubst_lift_apply (σs := σs) (υ := τ) v)
                    (toFormula φ)
      simpa [subst, toFormula, Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst] using
        congrArg
          (fun ψ : Formula Const (SimpleTy.toCtx (τ :: Δ)) => Term.all ψ)
          hbody
  | @ex Γ' τ φ ih =>
      have hbody :
          toFormula (subst (SimpleSubst.lift (υ := τ) σs) φ) =
            Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst
              (Mettapedia.Logic.HOL.Subst.lift
                (Base := Base) (Const := Const) (σ := τ.toTy)
                (SimpleSubst.toSubst σs))
              (toFormula φ) := by
        calc
          toFormula (subst (SimpleSubst.lift (υ := τ) σs) φ) =
              Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst
                (SimpleSubst.toSubst (SimpleSubst.lift (υ := τ) σs)) (toFormula φ) := by
                  exact ih (SimpleSubst.lift (υ := τ) σs)
          _ =
              Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst
                (Mettapedia.Logic.HOL.Subst.lift
                  (Base := Base) (Const := Const) (σ := τ.toTy)
                  (SimpleSubst.toSubst σs))
                (toFormula φ) := by
                  exact Mettapedia.Logic.HOL.subst_ext
                    (σs := SimpleSubst.toSubst (SimpleSubst.lift (υ := τ) σs))
                    (τs := Mettapedia.Logic.HOL.Subst.lift
                      (Base := Base) (Const := Const) (σ := τ.toTy)
                      (SimpleSubst.toSubst σs))
                    (h := fun v => SimpleSubst.toSubst_lift_apply (σs := σs) (υ := τ) v)
                    (toFormula φ)
      simpa [subst, toFormula, Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst] using
        congrArg
          (fun ψ : Formula Const (SimpleTy.toCtx (τ :: Δ)) => Term.ex ψ)
          hbody

/--
Direct semilocal-model evaluation for the quantified simple fragment, stated on
the native HOL side after translation of contexts and atoms.
-/
def semilocalTruth :
    {Γ : List (SimpleTy Base)} →
      (M : SemilocalModel Base Const) →
      SemilocalModel.Env M (SimpleTy.toCtx Γ) →
      SimpleQuantifiedFormula Base Const Γ → M.Omega
  | _, M, ρ, .atom t => SemilocalModel.formulaTruth M ρ (SimpleTerm.toTerm t)
  | _, _, _, .top => ⊤
  | _, _, _, .bot => ⊥
  | _, M, ρ, .conj φ ψ => semilocalTruth M ρ φ ⊓ semilocalTruth M ρ ψ
  | _, M, ρ, .disj φ ψ => semilocalTruth M ρ φ ⊔ semilocalTruth M ρ ψ
  | _, M, ρ, .impl φ ψ => semilocalTruth M ρ φ ⇨ semilocalTruth M ρ ψ
  | Γ, M, ρ, .all τ φ =>
      ⨅ x, M.extent x ⇨
        semilocalTruth (Γ := τ :: Γ) M
          (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) φ
  | Γ, M, ρ, .ex τ φ =>
      ⨆ x, M.extent x ⊓
        semilocalTruth (Γ := τ :: Γ) M
          (ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x) φ

/-- The direct quantified-fragment evaluator matches native formula semantics exactly. -/
@[simp] theorem semilocalTruth_toFormula (M : SemilocalModel Base Const)
    (ρ : SemilocalModel.Env M (SimpleTy.toCtx Γ))
    (φ : SimpleQuantifiedFormula Base Const Γ) :
    semilocalTruth M ρ φ =
      SemilocalModel.formulaTruth M ρ (toFormula φ) := by
  induction φ with
  | atom t =>
      simp [semilocalTruth, toFormula]
  | top =>
      simp [semilocalTruth, toFormula]
  | bot =>
      simp [semilocalTruth, toFormula]
  | conj φ ψ ihφ ihψ =>
      rw [semilocalTruth, toFormula, SemilocalModel.formulaTruth_and]
      rw [ihφ ρ, ihψ ρ]
  | disj φ ψ ihφ ihψ =>
      rw [semilocalTruth, toFormula, SemilocalModel.formulaTruth_or]
      rw [ihφ ρ, ihψ ρ]
  | impl φ ψ ihφ ihψ =>
      rw [semilocalTruth, toFormula, SemilocalModel.formulaTruth_imp]
      rw [ihφ ρ, ihψ ρ]
  | @all Γ' τ φ ih =>
      rw [semilocalTruth, toFormula, SemilocalModel.formulaTruth_all]
      apply iInf_congr
      intro x
      let ρ' : SemilocalModel.Env M (SimpleTy.toCtx (τ :: Γ')) :=
        ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x
      exact congrArg (fun ω => M.extent x ⇨ ω) (ih ρ')
  | @ex Γ' τ φ ih =>
      rw [semilocalTruth, toFormula, SemilocalModel.formulaTruth_ex]
      apply iSup_congr
      intro x
      let ρ' : SemilocalModel.Env M (SimpleTy.toCtx (τ :: Γ')) :=
        ApplicativeStructure.Env.extend M.toApplicativeStructure ρ x
      exact congrArg (fun ω => M.extent x ⊓ ω) (ih ρ')

/--
Semantic substitution for the quantified simple fragment, expressed through the
native semilocal model substitution environment.
-/
@[simp] theorem semilocalTruth_subst (M : SemilocalModel Base Const)
    (ρ : SemilocalModel.Env M (SimpleTy.toCtx Δ))
    (σs : SimpleSubst Base Const Γ Δ)
    (φ : SimpleQuantifiedFormula Base Const Γ) :
    semilocalTruth M ρ (subst σs φ) =
      semilocalTruth M
        (SemilocalModel.substEnv M (SimpleSubst.toSubst σs) ρ) φ := by
  rw [semilocalTruth_toFormula, semilocalTruth_toFormula]
  rw [toFormula_subst]
  unfold SemilocalModel.formulaTruth
  congr 1
  exact SemilocalModel.eval_subst M (SimpleSubst.toSubst σs) (toFormula φ) ρ

/--
Native derivations on translated quantified simple formulas are sound for the
direct simple-fragment evaluator in semilocal models supporting uniform
relativization.
-/
theorem semilocalTruth_sound_of_translated
    (M : SemilocalModel Base Const)
    (hstep : SemilocalModel.SupportsUniformRelativization M)
    {Δ : List (SimpleQuantifiedFormula Base Const Γ)}
    {φ : SimpleQuantifiedFormula Base Const Γ}
    (h : Derivable (Base := Base) (Const := Const) (Δ.map toFormula) (toFormula φ))
    (ρ : SemilocalModel.Env M (SimpleTy.toCtx Γ))
    (hρ : SemilocalModel.IsGlobalEnv M ρ) :
    SemilocalModel.antecedentTruth M ρ (Δ.map toFormula) ≤
      semilocalTruth M ρ φ := by
  simpa [semilocalTruth_toFormula] using (SemilocalModel.soundness M hstep h) ρ hρ

/--
Global models validate translated quantified simple derivations directly in the
simple evaluator.
-/
theorem globalTruth_sound_of_translated
    (M : GlobalModel Base Const)
    {Δ : List (SimpleQuantifiedFormula Base Const Γ)}
    {φ : SimpleQuantifiedFormula Base Const Γ}
    (h : Derivable (Base := Base) (Const := Const) (Δ.map toFormula) (toFormula φ))
    (ρ : SemilocalModel.Env M.toSemilocalModel (SimpleTy.toCtx Γ)) :
    SemilocalModel.antecedentTruth M.toSemilocalModel ρ (Δ.map toFormula) ≤
      semilocalTruth M.toSemilocalModel ρ φ := by
  simpa [semilocalTruth_toFormula] using (GlobalModel.soundness M h) ρ

/--
Closed translated derivations evaluate to truth in every global model.
-/
theorem globalTruth_of_closed_derivable
    (M : GlobalModel Base Const)
    {φ : SimpleQuantifiedFormula Base Const []}
    (h : Derivable (Base := Base) (Const := Const) [] (toFormula φ))
    (ρ : SemilocalModel.Env M.toSemilocalModel (SimpleTy.toCtx ([] : List (SimpleTy Base)))) :
    semilocalTruth M.toSemilocalModel ρ φ = ⊤ := by
  have hs :
      SemilocalModel.antecedentTruth M.toSemilocalModel ρ [] ≤
        semilocalTruth M.toSemilocalModel ρ φ :=
    globalTruth_sound_of_translated (M := M) (Δ := []) (φ := φ) h ρ
  have htop : (⊤ : M.Omega) ≤ semilocalTruth M.toSemilocalModel ρ φ := by
    simpa [SemilocalModel.antecedentTruth] using hs
  exact le_antisymm le_top htop

end SimpleQuantifiedFormula

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
