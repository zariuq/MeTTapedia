import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzFullTypedVariables
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzQuantifiedTopologicalGlobalModelBridge

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v

namespace HigherOrderPointTopologicalGlobalModelBridge

open SimpleQuantifiedTopologicalGlobalModelBridge

variable {Base : Type u} {Const : Ty Base → Type v}

/-- The one-point archive-free topological carrier for the full HOL type family. -/
def basicInterp (M : GlobalModel Base Const) :
    EtaleSpace.BasicTopologicalInterpretation Base Const PUnit where
  space := fun τ => pointEtale (M.Carrier τ)
  const := fun c => pointSection (M.const c)

namespace basicInterp

variable (M : GlobalModel Base Const)

abbrev NativeEnv (Γ : Ctx Base) :=
  SemilocalModel.Env M.toSemilocalModel Γ

/-- Contexts as iterated fiber products in the one-point topological model. -/
abbrev ctxSpace (Γ : Ctx Base) : EtaleSpace PUnit :=
  (basicInterp M).ctxSpace Γ

@[simp] theorem ctxSpace_nil :
    ctxSpace (M := M) [] = EtaleSpace.terminal PUnit :=
  rfl

@[simp] theorem ctxSpace_cons (τ : Ty Base) (Γ : Ctx Base) :
    ctxSpace (M := M) (τ :: Γ) =
      EtaleSpace.prod ((basicInterp M).space τ) (ctxSpace (M := M) Γ) :=
  rfl

@[simp] theorem ctx_proj_eq_unit
    {Γ : Ctx Base}
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    (ctxSpace (M := M) Γ).proj γ = () :=
  Subsingleton.elim _ _

/-- Package a native semantic value as a point in the one-point carrier. -/
def pointCarrier {τ : Ty Base}
    (x : M.Carrier τ) : ((basicInterp M).space τ).Carrier :=
  ((), x)

/-- Extract the native semantic value from a one-point carrier. -/
def pointCarrierVal {τ : Ty Base}
    (p : ((basicInterp M).space τ).Carrier) : M.Carrier τ :=
  p.2

@[simp] theorem pointCarrier_val {τ : Ty Base}
    (x : M.Carrier τ) :
    pointCarrierVal (M := M) (pointCarrier (M := M) (τ := τ) x) = x :=
  rfl

@[simp] theorem pointCarrier_eta {τ : Ty Base}
    (p : ((basicInterp M).space τ).Carrier) :
    pointCarrier (M := M) (τ := τ) (pointCarrierVal (M := M) p) = p := by
  cases p
  rfl

@[simp] theorem pointCarrier_proj {τ : Ty Base}
    (x : M.Carrier τ) :
    ((basicInterp M).space τ).proj (pointCarrier (M := M) (τ := τ) x) = () :=
  rfl

/-- The tail component of a one-point higher-order context carrier. -/
noncomputable def tailCtx {Γ : Ctx Base} {τ : Ty Base}
    (γ : (ctxSpace (M := M) (τ :: Γ)).Carrier) :
    (ctxSpace (M := M) Γ).Carrier :=
  EtaleSpace.prodSnd ((basicInterp M).space τ) (ctxSpace (M := M) Γ) γ

/-- The head semantic value of a one-point higher-order context carrier. -/
noncomputable def headVal {Γ : Ctx Base} {τ : Ty Base}
    (γ : (ctxSpace (M := M) (τ :: Γ)).Carrier) :
    M.Carrier τ :=
  pointCarrierVal (M := M)
    (EtaleSpace.prodFst ((basicInterp M).space τ) (ctxSpace (M := M) Γ) γ)

/-- Extend a one-point higher-order context carrier by a new head value. -/
noncomputable def consCtx {Γ : Ctx Base} {τ : Ty Base}
    (x : M.Carrier τ)
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    (ctxSpace (M := M) (τ :: Γ)).Carrier := by
  refine ⟨(pointCarrier (M := M) (τ := τ) x, γ), ?_⟩
  exact (ctx_proj_eq_unit (M := M) γ).symm

@[simp] theorem tailCtx_consCtx
    {Γ : Ctx Base} {τ : Ty Base}
    (x : M.Carrier τ)
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    tailCtx (M := M) (consCtx (M := M) x γ) = γ :=
  rfl

@[simp] theorem headVal_consCtx
    {Γ : Ctx Base} {τ : Ty Base}
    (x : M.Carrier τ)
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    headVal (M := M) (consCtx (M := M) x γ) = x :=
  rfl

/-- Decode a one-point higher-order context carrier as a native environment. -/
noncomputable def decodeEnv :
    {Γ : Ctx Base} →
      (ctxSpace (M := M) Γ).Carrier →
        NativeEnv (M := M) Γ
  | [], _ => fun v => nomatch v
  | _ :: _, γ => fun v =>
      match v with
      | .vz => headVal (M := M) γ
      | .vs w => decodeEnv (tailCtx (M := M) γ) w

@[simp] theorem decodeEnv_cons_vz
    {Γ : Ctx Base} {τ : Ty Base}
    (γ : (ctxSpace (M := M) (τ :: Γ)).Carrier) :
    decodeEnv (M := M) γ (Var.vz : Var (τ :: Γ) τ) =
      headVal (M := M) γ :=
  rfl

@[simp] theorem decodeEnv_cons_vs
    {Γ : Ctx Base} {τ σ : Ty Base}
    (γ : (ctxSpace (M := M) (σ :: Γ)).Carrier)
    (v : Var Γ τ) :
    decodeEnv (M := M) γ (.vs v) =
      decodeEnv (M := M) (tailCtx (M := M) γ) v :=
  rfl

@[simp] theorem decodeEnv_consCtx_apply
    {Γ : Ctx Base} {τ : Ty Base}
    (x : M.Carrier τ)
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    ∀ {σ : Ty Base} (v : Var (τ :: Γ) σ),
      decodeEnv (M := M) (consCtx (M := M) x γ) v =
        ApplicativeStructure.Env.extend M.toApplicativeStructure
          (decodeEnv (M := M) γ) x v := by
  intro σ v
  cases v with
  | vz =>
      rfl
  | vs w =>
      rfl

@[simp] theorem var_val_decode
    {Γ : Ctx Base} {τ : Ty Base}
    (x : Var Γ τ)
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    pointCarrierVal (M := M)
      ((EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var (basicInterp M) x).toContinuousMap γ) =
      decodeEnv (M := M) γ x := by
  induction x with
  | vz =>
      rfl
  | @vs Γ υ τ x ih =>
      change pointCarrierVal (M := M)
        ((EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var (basicInterp M) x).toContinuousMap
          (tailCtx (M := M) γ)) =
        decodeEnv (M := M) (tailCtx (M := M) γ) x
      exact ih (tailCtx (M := M) γ)

/-- Full higher-order term evaluation into the one-point Awodey-Butz carrier. -/
noncomputable def eval
    {Γ : Ctx Base} {τ : Ty Base}
    (t : Term Const Γ τ) :
    C((ctxSpace (M := M) Γ).Carrier, ((basicInterp M).space τ).Carrier) := by
  let _ :
      DiscreteTopology ((ctxSpace (M := M) Γ).Carrier) :=
    EtaleSpace.discreteTopology_of_discrete_base (ctxSpace (M := M) Γ)
  exact
    { toFun := fun γ =>
        pointCarrier (M := M) (τ := τ)
          (SemilocalModel.eval M.toSemilocalModel (decodeEnv (M := M) γ) t)
      continuous_toFun := continuous_of_discreteTopology }

@[simp] theorem eval_val_decode
    {Γ : Ctx Base} {τ : Ty Base}
    (t : Term Const Γ τ)
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    pointCarrierVal (M := M) (eval (M := M) t γ) =
      SemilocalModel.eval M.toSemilocalModel (decodeEnv (M := M) γ) t :=
  rfl

@[simp] theorem eval_val_decode_subst
    {Γ Δ : Ctx Base} {τ : Ty Base}
    (σs : Subst Const Γ Δ)
    (t : Term Const Γ τ)
    (γ : (ctxSpace (M := M) Δ).Carrier) :
    pointCarrierVal (M := M) (eval (M := M) (subst σs t) γ) =
      SemilocalModel.eval M.toSemilocalModel
        (SemilocalModel.substEnv M.toSemilocalModel σs (decodeEnv (M := M) γ))
        t := by
  calc
    pointCarrierVal (M := M) (eval (M := M) (subst σs t) γ) =
      SemilocalModel.eval M.toSemilocalModel
        (decodeEnv (M := M) γ)
        (subst σs t) := by
          exact eval_val_decode (M := M) (t := subst σs t) γ
    _ =
      SemilocalModel.eval M.toSemilocalModel
        (SemilocalModel.substEnv M.toSemilocalModel σs (decodeEnv (M := M) γ))
        t := by
          exact
            SemilocalModel.eval_subst M.toSemilocalModel
              σs t (decodeEnv (M := M) γ)

@[simp] theorem eval_proj
    {Γ : Ctx Base} {τ : Ty Base}
    (t : Term Const Γ τ)
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    ((basicInterp M).space τ).proj (eval (M := M) t γ) = () :=
  rfl

/-- Topological truth of a full HOL formula in the one-point higher-order model. -/
noncomputable def truthEval
    {Γ : Ctx Base}
    (φ : Formula Const Γ)
    (γ : (ctxSpace (M := M) Γ).Carrier) : M.Omega :=
  M.truth (pointCarrierVal (M := M) (eval (M := M) φ γ))

@[simp] theorem truthEval_eq_formulaTruth
    {Γ : Ctx Base}
    (φ : Formula Const Γ)
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    truthEval (M := M) φ γ =
      SemilocalModel.formulaTruth M.toSemilocalModel
        (decodeEnv (M := M) γ) φ := by
  simp [truthEval, SemilocalModel.formulaTruth, eval_val_decode]

@[simp] theorem decodeEnv_consCtx
    {Γ : Ctx Base} {σ : Ty Base}
    (x : M.Carrier σ)
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    (decodeEnv (M := M) (consCtx (M := M) x γ) :
        NativeEnv (M := M) (σ :: Γ)) =
      (ApplicativeStructure.Env.extend M.toApplicativeStructure
        (decodeEnv (M := M) γ) x :
          NativeEnv (M := M) (σ :: Γ)) := by
  funext τ
  funext v
  exact decodeEnv_consCtx_apply (M := M) x γ v

/-- Pointwise truth in an extended one-point context is semilocal truth in the
corresponding extended native environment. -/
@[simp] theorem truthEval_consCtx_eq_formulaTruth
    {Γ : Ctx Base} {σ : Ty Base}
    (φ : Formula Const (σ :: Γ))
    (x : M.Carrier σ)
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    truthEval (M := M) φ (consCtx (M := M) x γ) =
      SemilocalModel.formulaTruth M.toSemilocalModel
        (ApplicativeStructure.Env.extend M.toApplicativeStructure
          (decodeEnv (M := M) γ) x) φ := by
  rw [truthEval_eq_formulaTruth]
  rw [decodeEnv_consCtx (M := M) x γ]

@[simp] theorem truthEval_weaken
    {Γ : Ctx Base} {σ : Ty Base}
    (φ : Formula Const Γ)
    (x : M.Carrier σ)
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    truthEval (M := M) (weaken (Base := Base) (Const := Const) (σ := σ) φ)
        (consCtx (M := M) x γ) =
      truthEval (M := M) φ γ := by
  rw [truthEval_consCtx_eq_formulaTruth
        (M := M)
        (φ := weaken (Base := Base) (Const := Const) (σ := σ) φ)
        x γ,
      truthEval_eq_formulaTruth]
  exact
    (SemilocalModel.formulaTruth_weaken M.toSemilocalModel
      (decodeEnv (M := M) γ) x φ)

@[simp] theorem truthEval_subst
    {Γ Δ : Ctx Base}
    (σs : Subst Const Γ Δ)
    (φ : Formula Const Γ)
    (γ : (ctxSpace (M := M) Δ).Carrier) :
    truthEval (M := M) (subst σs φ) γ =
      SemilocalModel.formulaTruth M.toSemilocalModel
        (SemilocalModel.substEnv M.toSemilocalModel σs (decodeEnv (M := M) γ))
        φ := by
  change
    M.truth
      (pointCarrierVal (M := M) (eval (M := M) (subst σs φ) γ)) =
    M.truth
      (SemilocalModel.eval M.toSemilocalModel
        (SemilocalModel.substEnv M.toSemilocalModel σs (decodeEnv (M := M) γ))
        φ)
  rw [eval_val_decode_subst]

@[simp] theorem truthEval_instantiate
    {Γ : Ctx Base} {σ : Ty Base}
    (t : Term Const Γ σ)
    (φ : Formula Const (σ :: Γ))
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    truthEval (M := M) (instantiate t φ) γ =
      truthEval (M := M) φ
        (consCtx (M := M)
          (SemilocalModel.eval M.toSemilocalModel
            (decodeEnv (M := M) γ) t) γ) := by
  rw [truthEval_eq_formulaTruth, truthEval_consCtx_eq_formulaTruth]
  exact
    (SemilocalModel.formulaTruth_instantiate M.toSemilocalModel
      t φ (decodeEnv (M := M) γ))

@[simp] theorem truthEval_betaEtaEq
    {Γ : Ctx Base}
    {φ ψ : Formula Const Γ}
    (h : BetaEtaEq (Base := Base) (Const := Const) φ ψ)
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    truthEval (M := M) φ γ = truthEval (M := M) ψ γ := by
  rw [truthEval_eq_formulaTruth, truthEval_eq_formulaTruth]
  exact SemilocalModel.formulaTruth_betaEtaEq
    M.toSemilocalModel (decodeEnv (M := M) γ) h

@[simp] theorem truthEval_beta
    {Γ : Ctx Base} {σ : Ty Base}
    (t : Term Const Γ σ)
    (φ : Formula Const (σ :: Γ))
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    truthEval (M := M) (.app (.lam φ) t) γ =
      truthEval (M := M) (instantiate t φ) γ := by
  exact truthEval_betaEtaEq (M := M) (BetaEtaEq.beta t φ) γ

/-- Meet of antecedent truth values in the one-point higher-order model. -/
noncomputable def truthAntecedent
    {Γ : Ctx Base}
    (Δ : List (Formula Const Γ))
    (γ : (ctxSpace (M := M) Γ).Carrier) : M.Omega :=
  match Δ with
  | [] => ⊤
  | ψ :: Δ => truthEval (M := M) ψ γ ⊓ truthAntecedent Δ γ

@[simp] theorem truthAntecedent_eq_antecedentTruth
    {Γ : Ctx Base}
    (Δ : List (Formula Const Γ))
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    truthAntecedent (M := M) Δ γ =
      SemilocalModel.antecedentTruth M.toSemilocalModel
        (decodeEnv (M := M) γ) Δ := by
  induction Δ with
  | nil =>
      simp [truthAntecedent, SemilocalModel.antecedentTruth]
  | cons ψ Δ ih =>
      simp [truthAntecedent, SemilocalModel.antecedentTruth,
        truthEval_eq_formulaTruth, ih]

/-- Direct validity of a full HOL sequent in the one-point Awodey-Butz model. -/
def TruthValidSequent
    {Γ : Ctx Base}
    (Δ : List (Formula Const Γ))
    (φ : Formula Const Γ) : Prop :=
  ∀ γ : (ctxSpace (M := M) Γ).Carrier,
    truthAntecedent (M := M) Δ γ ≤ truthEval (M := M) φ γ

theorem truthValidSequent_of_derivable
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ}
    (h : Derivable (Base := Base) (Const := Const) Δ φ) :
    TruthValidSequent (M := M) Δ φ := by
  intro γ
  rw [truthAntecedent_eq_antecedentTruth (M := M) Δ γ]
  rw [truthEval_eq_formulaTruth (M := M) φ γ]
  exact GlobalModel.soundness M h (decodeEnv (M := M) γ)

theorem truthValidSequent_of_closed_derivable
    {φ : Formula Const []}
    (h : Derivable (Base := Base) (Const := Const) [] φ) :
    TruthValidSequent (M := M) [] φ := by
  exact truthValidSequent_of_derivable (M := M) (Δ := []) (φ := φ) h

theorem not_derivable_of_truth_counterexample
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ}
    (γ : (ctxSpace (M := M) Γ).Carrier)
    (hΔ : truthAntecedent (M := M) Δ γ = ⊤)
    (hφ : truthEval (M := M) φ γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) Δ φ := by
  intro hder
  have hvalid :
      truthAntecedent (M := M) Δ γ ≤ truthEval (M := M) φ γ :=
    truthValidSequent_of_derivable (M := M) (Δ := Δ) (φ := φ) hder γ
  have htop_le : (⊤ : M.Omega) ≤ truthEval (M := M) φ γ := by
    rw [← hΔ]
    exact hvalid
  exact hφ (le_antisymm le_top htop_le)

theorem not_derivable_of_beta_truth_counterexample
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {σ : Ty Base}
    (t : Term Const Γ σ)
    (φ : Formula Const (σ :: Γ))
    (γ : (ctxSpace (M := M) Γ).Carrier)
    (hΔ : truthAntecedent (M := M) Δ γ = ⊤)
    (hφ : truthEval (M := M) (instantiate t φ) γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) Δ (.app (.lam φ) t) := by
  exact not_derivable_of_truth_counterexample (M := M) (Δ := Δ) (φ := .app (.lam φ) t) γ hΔ
    (by
      intro hAppTop
      apply hφ
      rw [← truthEval_beta (M := M) t φ γ]
      exact hAppTop)

theorem not_derivable_of_closed_truth_ne_top
    {φ : Formula Const []}
    (hφ : truthEval (M := M) φ () ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) [] φ := by
  exact not_derivable_of_truth_counterexample (M := M) (Δ := []) (φ := φ) ()
    (by simp [truthAntecedent]) hφ

end basicInterp

/-- Any existential one-point higher-order truth counterexample refutes
derivability. This is the strongest produced-witness theorem currently
available on the live higher-order topological bridge. -/
theorem not_derivable_of_exists_truth_counterexample
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ}
    (hCounter :
      ∃ (M : GlobalModel Base Const)
        (γ : (basicInterp.ctxSpace (M := M) Γ).Carrier),
        basicInterp.truthAntecedent (M := M) Δ γ = ⊤ ∧
          basicInterp.truthEval (M := M) φ γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) Δ φ := by
  rcases hCounter with ⟨M, γ, hΔ, hφ⟩
  exact basicInterp.not_derivable_of_truth_counterexample (M := M) γ hΔ hφ

theorem not_derivable_of_exists_beta_truth_counterexample
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {σ : Ty Base}
    (t : Term Const Γ σ)
    (φ : Formula Const (σ :: Γ))
    (hCounter :
      ∃ (M : GlobalModel Base Const)
        (γ : (basicInterp.ctxSpace (M := M) Γ).Carrier),
        basicInterp.truthAntecedent (M := M) Δ γ = ⊤ ∧
          basicInterp.truthEval (M := M) (instantiate t φ) γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) Δ (.app (.lam φ) t) := by
  rcases hCounter with ⟨M, γ, hΔ, hφ⟩
  exact basicInterp.not_derivable_of_beta_truth_counterexample (M := M) t φ γ hΔ hφ

end HigherOrderPointTopologicalGlobalModelBridge

namespace HigherOrderPointTopologicalSemilocalModelBridge

open SimpleQuantifiedTopologicalGlobalModelBridge

variable {Base : Type u} {Const : Ty Base → Type v}

/-- The one-point archive-free topological carrier induced by a semilocal model. -/
def basicInterp (M : SemilocalModel Base Const) :
    EtaleSpace.BasicTopologicalInterpretation Base Const PUnit where
  space := fun τ => pointEtale (M.Carrier τ)
  const := fun c => pointSection (M.const c)

namespace basicInterp

variable (M : SemilocalModel Base Const)

abbrev NativeEnv (Γ : Ctx Base) :=
  SemilocalModel.Env M Γ

/-- Contexts as iterated fiber products in the one-point semilocal model. -/
abbrev ctxSpace (Γ : Ctx Base) : EtaleSpace PUnit :=
  (basicInterp M).ctxSpace Γ

@[simp] theorem ctx_proj_eq_unit
    {Γ : Ctx Base}
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    (ctxSpace (M := M) Γ).proj γ = () :=
  Subsingleton.elim _ _

/-- Package a native semantic value as a point in the one-point carrier. -/
def pointCarrier {τ : Ty Base}
    (x : M.Carrier τ) : ((basicInterp M).space τ).Carrier :=
  ((), x)

/-- Extract the native semantic value from a one-point carrier. -/
def pointCarrierVal {τ : Ty Base}
    (p : ((basicInterp M).space τ).Carrier) : M.Carrier τ :=
  p.2

/-- The tail component of a one-point semilocal context carrier. -/
noncomputable def tailCtx {Γ : Ctx Base} {τ : Ty Base}
    (γ : (ctxSpace (M := M) (τ :: Γ)).Carrier) :
    (ctxSpace (M := M) Γ).Carrier :=
  EtaleSpace.prodSnd ((basicInterp M).space τ) (ctxSpace (M := M) Γ) γ

/-- The head semantic value of a one-point semilocal context carrier. -/
noncomputable def headVal {Γ : Ctx Base} {τ : Ty Base}
    (γ : (ctxSpace (M := M) (τ :: Γ)).Carrier) :
    M.Carrier τ :=
  pointCarrierVal (M := M)
    (EtaleSpace.prodFst ((basicInterp M).space τ) (ctxSpace (M := M) Γ) γ)

/-- Extend a one-point semilocal context carrier by a new head value. -/
noncomputable def consCtx {Γ : Ctx Base} {τ : Ty Base}
    (x : M.Carrier τ)
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    (ctxSpace (M := M) (τ :: Γ)).Carrier := by
  refine ⟨(pointCarrier (M := M) (τ := τ) x, γ), ?_⟩
  exact (ctx_proj_eq_unit (M := M) γ).symm

@[simp] theorem tailCtx_consCtx
    {Γ : Ctx Base} {τ : Ty Base}
    (x : M.Carrier τ)
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    tailCtx (M := M) (consCtx (M := M) x γ) = γ :=
  rfl

/-- Decode a one-point semilocal context carrier as a native environment. -/
noncomputable def decodeEnv :
    {Γ : Ctx Base} →
      (ctxSpace (M := M) Γ).Carrier →
        NativeEnv (M := M) Γ
  | [], _ => fun v => nomatch v
  | _ :: _, γ => fun v =>
      match v with
      | .vz => headVal (M := M) γ
      | .vs w => decodeEnv (tailCtx (M := M) γ) w

@[simp] theorem decodeEnv_consCtx_apply
    {Γ : Ctx Base} {τ : Ty Base}
    (x : M.Carrier τ)
    (γ : (ctxSpace (M := M) Γ).Carrier) :
    ∀ {σ : Ty Base} (v : Var (τ :: Γ) σ),
      decodeEnv (M := M) (consCtx (M := M) x γ) v =
        ApplicativeStructure.Env.extend M.toApplicativeStructure
          (decodeEnv (M := M) γ) x v := by
  intro σ v
  cases v with
  | vz => rfl
  | vs w =>
      simp [decodeEnv, ApplicativeStructure.Env.extend]

/-- Truth of a formula at a one-point semilocal context carrier. -/
noncomputable def truthEval
    {Γ : Ctx Base}
    (φ : Formula Const Γ)
    (γ : (ctxSpace (M := M) Γ).Carrier) : M.Omega :=
  SemilocalModel.formulaTruth M (decodeEnv (M := M) γ) φ

/-- Meet of antecedent truth values in the one-point semilocal model. -/
noncomputable def truthAntecedent
    {Γ : Ctx Base}
    (Δ : List (Formula Const Γ))
    (γ : (ctxSpace (M := M) Γ).Carrier) : M.Omega :=
  SemilocalModel.antecedentTruth M (decodeEnv (M := M) γ) Δ

/-- Semilocal truth validity of a full HOL sequent in the one-point model. -/
def TruthValidSequent
    {Γ : Ctx Base}
    (Δ : List (Formula Const Γ))
    (φ : Formula Const Γ) : Prop :=
  ∀ γ : (ctxSpace (M := M) Γ).Carrier,
    SemilocalModel.IsGlobalEnv M (decodeEnv (M := M) γ) →
      truthAntecedent (M := M) Δ γ ≤ truthEval (M := M) φ γ

theorem truthValidSequent_of_derivable
    (hM : SemilocalModel.SupportsUniformRelativization M)
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ}
    (h : Derivable (Base := Base) (Const := Const) Δ φ) :
    TruthValidSequent (M := M) Δ φ := by
  intro γ hγ
  exact SemilocalModel.soundness M hM h (decodeEnv (M := M) γ) hγ

theorem not_derivable_of_truth_counterexample
    (hM : SemilocalModel.SupportsUniformRelativization M)
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ}
    (γ : (ctxSpace (M := M) Γ).Carrier)
    (hγ : SemilocalModel.IsGlobalEnv M (decodeEnv (M := M) γ))
    (hΔ : truthAntecedent (M := M) Δ γ = ⊤)
    (hφ : truthEval (M := M) φ γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) Δ φ := by
  intro hder
  have hvalid :
      truthAntecedent (M := M) Δ γ ≤ truthEval (M := M) φ γ :=
    truthValidSequent_of_derivable (M := M) hM (Δ := Δ) (φ := φ) hder γ hγ
  have htop_le : (⊤ : M.Omega) ≤ truthEval (M := M) φ γ := by
    rw [← hΔ]
    exact hvalid
  exact hφ (le_antisymm le_top htop_le)

theorem not_derivable_of_formulaTruth_counterexample
    (hM : SemilocalModel.SupportsUniformRelativization M)
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ}
    (ρ : NativeEnv (M := M) Γ)
    (hρ : SemilocalModel.IsGlobalEnv M ρ)
    (hΔ : SemilocalModel.antecedentTruth M ρ Δ = ⊤)
    (hφ : SemilocalModel.formulaTruth M ρ φ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) Δ φ := by
  intro hder
  have hvalid :
      SemilocalModel.antecedentTruth M ρ Δ ≤ SemilocalModel.formulaTruth M ρ φ :=
    SemilocalModel.soundness M hM hder ρ hρ
  have htop_le : (⊤ : M.Omega) ≤ SemilocalModel.formulaTruth M ρ φ := by
    rw [← hΔ]
    exact hvalid
  exact hφ (le_antisymm le_top htop_le)

end basicInterp

/-- Any existential one-point semilocal truth counterexample refutes
derivability. This is the archive-free bridge from semilocal semantic witnesses
to the point-model truth style used by the Awodey-Butz topological interface. -/
theorem not_derivable_of_exists_semilocal_truth_counterexample
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ}
    (hCounter :
      ∃ (M : SemilocalModel Base Const)
        (ρ : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M ρ ∧
          SemilocalModel.antecedentTruth M ρ Δ = ⊤ ∧
          SemilocalModel.formulaTruth M ρ φ ≠ ⊤ ∧
          SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) Δ φ := by
  rcases hCounter with ⟨M, ρ, hρ, hΔ, hφ, hM⟩
  exact basicInterp.not_derivable_of_formulaTruth_counterexample
    (M := M) hM ρ hρ hΔ hφ

end HigherOrderPointTopologicalSemilocalModelBridge

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
