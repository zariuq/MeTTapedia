import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Models
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzHigherOrderPointModelBridge

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v w

/--
The pure higher-order applicative fragment of HOL: variables, constants,
application, and lambda abstraction, but no propositional constructors yet.

This is the smallest archive-free native syntax fragment that already exercises
the higher-order topological semantics route.
-/
inductive ApplicativeTerm (Base : Type u) (Const : Ty Base → Type v) :
    Ctx Base → Ty Base → Type (max u v) where
  | var : Var Γ τ → ApplicativeTerm Base Const Γ τ
  | const : Const τ → ApplicativeTerm Base Const Γ τ
  | app :
      ApplicativeTerm Base Const Γ (σ ⇒ τ) →
      ApplicativeTerm Base Const Γ σ →
      ApplicativeTerm Base Const Γ τ
  | lam :
      ApplicativeTerm Base Const (σ :: Γ) τ →
      ApplicativeTerm Base Const Γ (σ ⇒ τ)

namespace ApplicativeTerm

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Embed the applicative fragment back into the native HOL syntax. -/
def toTerm : ApplicativeTerm Base Const Γ τ → Term Const Γ τ
  | .var v => .var v
  | .const c => .const c
  | .app f t => .app (toTerm f) (toTerm t)
  | .lam t => .lam (toTerm t)

@[simp] theorem toTerm_var (v : Var Γ τ) :
    toTerm (.var v : ApplicativeTerm Base Const Γ τ) = .var v :=
  rfl

@[simp] theorem toTerm_const (c : Const τ) :
    toTerm (.const c : ApplicativeTerm Base Const Γ τ) = .const c :=
  rfl

@[simp] theorem toTerm_app
    (f : ApplicativeTerm Base Const Γ (σ ⇒ τ))
    (t : ApplicativeTerm Base Const Γ σ) :
    toTerm (.app f t : ApplicativeTerm Base Const Γ τ) = .app (toTerm f) (toTerm t) :=
  rfl

@[simp] theorem toTerm_lam
    (t : ApplicativeTerm Base Const (σ :: Γ) τ) :
    toTerm (.lam t : ApplicativeTerm Base Const Γ (σ ⇒ τ)) = .lam (toTerm t) :=
  rfl

end ApplicativeTerm

/--
Minimal archive-free higher-order topological interface needed to interpret the
applicative fragment over a base space.
-/
structure ApplicativeTopologicalInterpretation
    (Base : Type u) (Const : Ty Base → Type v)
    (X : Type w) [TopologicalSpace X] where
  toBasic : EtaleSpace.BasicTopologicalInterpretation Base Const X
  lam : {Γ : Ctx Base} → {σ τ : Ty Base} →
    toBasic.CtxTerm (σ :: Γ) τ → toBasic.CtxTerm Γ (σ ⇒ τ)
  app : {Γ : Ctx Base} → {σ τ : Ty Base} →
    toBasic.CtxTerm Γ (σ ⇒ τ) → toBasic.CtxTerm Γ σ → toBasic.CtxTerm Γ τ

namespace ApplicativeTopologicalInterpretation

variable {Base : Type u} {Const : Ty Base → Type v}
variable {X : Type w} [TopologicalSpace X]
variable (I : ApplicativeTopologicalInterpretation Base Const X)

/-- Evaluate an applicative-fragment term in the higher-order topological semantics. -/
def evalTerm : ApplicativeTerm Base Const Γ τ → I.toBasic.CtxTerm Γ τ
  | .var v => EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var I.toBasic v
  | .const c => EtaleSpace.BasicTopologicalInterpretation.CtxTerm.const I.toBasic Γ c
  | .app f t => I.app (evalTerm f) (evalTerm t)
  | .lam t => I.lam (evalTerm t)

@[simp] theorem evalTerm_var (v : Var Γ τ) :
    ApplicativeTopologicalInterpretation.evalTerm I (.var v : ApplicativeTerm Base Const Γ τ) =
      EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var I.toBasic v :=
  rfl

@[simp] theorem evalTerm_const (c : Const τ) :
    ApplicativeTopologicalInterpretation.evalTerm I (.const c : ApplicativeTerm Base Const Γ τ) =
      EtaleSpace.BasicTopologicalInterpretation.CtxTerm.const I.toBasic Γ c :=
  rfl

@[simp] theorem evalTerm_app
    (f : ApplicativeTerm Base Const Γ (σ ⇒ τ))
    (t : ApplicativeTerm Base Const Γ σ) :
    ApplicativeTopologicalInterpretation.evalTerm I (.app f t : ApplicativeTerm Base Const Γ τ) =
      I.app (ApplicativeTopologicalInterpretation.evalTerm I f)
        (ApplicativeTopologicalInterpretation.evalTerm I t) :=
  rfl

@[simp] theorem evalTerm_lam
    (t : ApplicativeTerm Base Const (σ :: Γ) τ) :
    ApplicativeTopologicalInterpretation.evalTerm I (.lam t : ApplicativeTerm Base Const Γ (σ ⇒ τ)) =
      I.lam (ApplicativeTopologicalInterpretation.evalTerm I t) :=
  rfl

end ApplicativeTopologicalInterpretation

namespace HigherOrderPointTopologicalGlobalModelBridge

namespace basicInterp

variable {Base : Type u} {Const : Ty Base → Type v}
variable (M : GlobalModel Base Const)

/-- The one-point model instantiates the applicative topological interface. -/
noncomputable def applicativeInterp :
    ApplicativeTopologicalInterpretation Base Const PUnit where
  toBasic := basicInterp M
  lam := fun {Γ} {σ} {τ} t => by
    let _ :
        DiscreteTopology ((ctxSpace (M := M) Γ).Carrier) :=
      EtaleSpace.discreteTopology_of_discrete_base (ctxSpace (M := M) Γ)
    exact
      { toContinuousMap :=
          { toFun := fun γ =>
              pointCarrier (M := M) (τ := σ ⇒ τ)
                (M.lam fun x =>
                  pointCarrierVal (M := M) (t.toContinuousMap (consCtx (M := M) x γ))
            )
            continuous_toFun := continuous_of_discreteTopology }
        proj_comp := by
          funext γ
          simp [pointCarrier_proj, ctx_proj_eq_unit] }
  app := fun {Γ} {σ} {τ} f a => by
    let _ :
        DiscreteTopology ((ctxSpace (M := M) Γ).Carrier) :=
      EtaleSpace.discreteTopology_of_discrete_base (ctxSpace (M := M) Γ)
    exact
      { toContinuousMap :=
          { toFun := fun γ =>
              pointCarrier (M := M) (τ := τ)
                (M.app
                  (pointCarrierVal (M := M) (f.toContinuousMap γ))
                  (pointCarrierVal (M := M) (a.toContinuousMap γ)))
            continuous_toFun := continuous_of_discreteTopology }
        proj_comp := by
          funext γ
          simp [pointCarrier_proj, ctx_proj_eq_unit] }

namespace ApplicativeTopologicalInterpretation

@[simp] theorem eval_val_decode
    {Γ : Ctx Base} {τ : Ty Base}
    (t : ApplicativeTerm Base Const Γ τ)
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    pointCarrierVal (M := M) (((applicativeInterp M).evalTerm t).toContinuousMap γ) =
      SemilocalModel.eval M.toSemilocalModel
        (decodeEnv (M := M) γ) (ApplicativeTerm.toTerm t) := by
  induction t with
  | var v =>
      change pointCarrierVal (M := M)
          ((EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var (basicInterp M) v).toContinuousMap
            γ) =
        SemilocalModel.eval M.toSemilocalModel
          (decodeEnv (M := M) γ) (.var v)
      rw [SemilocalModel.eval]
      exact var_val_decode (M := M) v γ
  | const c =>
      change pointCarrierVal (M := M)
          (((applicativeInterp M).evalTerm (.const c)).toContinuousMap γ) =
        SemilocalModel.eval M.toSemilocalModel (decodeEnv (M := M) γ) (.const c)
      dsimp [ApplicativeTopologicalInterpretation.evalTerm, applicativeInterp,
        EtaleSpace.BasicTopologicalInterpretation.CtxTerm.const,
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp,
        SimpleQuantifiedTopologicalGlobalModelBridge.pointSection,
        EtaleSpace.projMap, SemilocalModel.eval, pointCarrierVal]
      rfl
  | app f a ihf iha =>
      change M.app
          (pointCarrierVal (M := M) (((applicativeInterp M).evalTerm f).toContinuousMap γ))
          (pointCarrierVal (M := M) (((applicativeInterp M).evalTerm a).toContinuousMap γ)) =
        M.app
          (SemilocalModel.eval M.toSemilocalModel (decodeEnv (M := M) γ)
            (ApplicativeTerm.toTerm f))
          (SemilocalModel.eval M.toSemilocalModel (decodeEnv (M := M) γ)
            (ApplicativeTerm.toTerm a))
      exact congrArg₂ (fun u v => M.app u v) (ihf γ) (iha γ)
  | @lam Γ σ τ t iht =>
      simp [ApplicativeTopologicalInterpretation.evalTerm, ApplicativeTerm.toTerm,
        applicativeInterp, SemilocalModel.eval]
      apply congrArg M.lam
      funext x
      have hbody := iht (consCtx (M := M) x γ)
      refine hbody.trans ?_
      apply
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedTopologicalGlobalModelBridge.simpleInterp.SemilocalModel.eval_env_ext
          (S := M.toSemilocalModel)
      intro υ v
      exact decodeEnv_consCtx_apply (M := M) x γ v

end ApplicativeTopologicalInterpretation

end basicInterp

end HigherOrderPointTopologicalGlobalModelBridge

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
