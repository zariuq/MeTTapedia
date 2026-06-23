import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzQuantifiedTopologicalFragment

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v

namespace SimpleQuantifiedTopologicalGlobalModelBridge

variable {Base : Type u} {Const : Ty Base → Type v}

/-- A discrete étale space over the one-point base. -/
def pointEtale (A : Type*) : EtaleSpace PUnit where
  Carrier := PUnit × A
  carrierTopologicalSpace := ⊥
  proj := Prod.fst
  isLocalHomeomorph_proj := by
    let _ : TopologicalSpace (PUnit × A) := ⊥
    let _ : DiscreteTopology (PUnit × A) := discreteTopology_bot _
    apply IsLocalHomeomorph.mk
    intro xa
    rcases xa with ⟨_, a⟩
    refine ⟨
      { toFun := Prod.fst
        invFun := fun y => (y, a)
        source := Set.univ ×ˢ ({a} : Set A)
        target := Set.univ
        map_source' := fun _ _ => Set.mem_univ _
        map_target' := fun _ _ => ⟨Set.mem_univ _, Set.mem_singleton a⟩
        left_inv' := fun y hy => by
          rcases y with ⟨_, a'⟩
          simp at hy
          simp [hy]
        right_inv' := fun _ _ => rfl
        open_source := by
          exact isOpen_discrete (Set.univ ×ˢ ({a} : Set A))
        open_target := isOpen_univ
        continuousOn_toFun := by
          apply Continuous.continuousOn
          exact continuous_of_discreteTopology
        continuousOn_invFun := by
          apply Continuous.continuousOn
          exact continuous_of_discreteTopology },
      ⟨⟨Set.mem_univ _, Set.mem_singleton a⟩, fun _ _ => rfl⟩⟩

/-- The constant global section of a one-point étale space. -/
def pointSection {A : Type*} (a : A) : (pointEtale A).GlobalSection where
  toContinuousMap :=
    { toFun := fun _ => ((), a)
      continuous_toFun := continuous_const }
  proj_comp := by
    funext x
    cases x
    rfl

/-- Restrict a global model to the simple topological proposition/base fragment. -/
def simpleInterp (M : GlobalModel Base Const) : SimpleTopologicalInterpretation Base Const PUnit where
  propSpace := pointEtale (M.Carrier .prop)
  baseSpace := fun b => pointEtale (M.Carrier (.base b))
  constProp := fun c => pointSection (M.const c)
  constBase := fun c => pointSection (M.const c)

namespace simpleInterp

variable (M : GlobalModel Base Const)

abbrev NativeEnv (Γ : List (SimpleTy Base)) :=
  SemilocalModel.Env M.toSemilocalModel (SimpleTy.toCtx Γ)

@[simp] theorem ctx_proj_eq_unit
    {Γ : List (SimpleTy Base)}
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    ((simpleInterp M).ctxSpace Γ).proj γ = () :=
  Subsingleton.elim _ _

/-- Package a native semantic value as a point in the one-point simple carrier. -/
def pointCarrier {τ : SimpleTy Base}
    (x : M.Carrier τ.toTy) : ((simpleInterp M).space τ).Carrier := by
  cases τ with
  | prop => exact ((), x)
  | base b => exact ((), x)

/-- Extract the native semantic value from a one-point simple carrier. -/
def pointCarrierVal {τ : SimpleTy Base}
    (p : ((simpleInterp M).space τ).Carrier) : M.Carrier τ.toTy := by
  cases τ with
  | prop => exact p.2
  | base b => exact p.2

@[simp] theorem pointCarrier_val {τ : SimpleTy Base}
    (x : M.Carrier τ.toTy) :
    pointCarrierVal (M := M) (pointCarrier (M := M) (τ := τ) x) = x := by
  cases τ <;> rfl

@[simp] theorem pointCarrier_eta {τ : SimpleTy Base}
    (p : ((simpleInterp M).space τ).Carrier) :
    pointCarrier (M := M) (τ := τ) (pointCarrierVal (M := M) p) = p := by
  cases τ <;> cases p <;> rfl

@[simp] theorem pointCarrier_proj {τ : SimpleTy Base}
    (x : M.Carrier τ.toTy) :
    ((simpleInterp M).space τ).proj (pointCarrier (M := M) (τ := τ) x) = () := by
  cases τ <;> rfl

/-- The tail component of a one-point simple context carrier. -/
def tailCtx {Γ : List (SimpleTy Base)} {τ : SimpleTy Base}
    (γ : ((simpleInterp M).ctxSpace (τ :: Γ)).Carrier) :
    ((simpleInterp M).ctxSpace Γ).Carrier :=
  EtaleSpace.prodSnd ((simpleInterp M).space τ) ((simpleInterp M).ctxSpace Γ) γ

/-- The head semantic value of a one-point simple context carrier. -/
def headVal {Γ : List (SimpleTy Base)} {τ : SimpleTy Base}
    (γ : ((simpleInterp M).ctxSpace (τ :: Γ)).Carrier) :
    M.Carrier τ.toTy :=
  pointCarrierVal (M := M)
    (EtaleSpace.prodFst ((simpleInterp M).space τ) ((simpleInterp M).ctxSpace Γ) γ)

/-- Extend a one-point simple context carrier by a new head value. -/
def consCtx {Γ : List (SimpleTy Base)} {τ : SimpleTy Base}
    (x : M.Carrier τ.toTy)
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    ((simpleInterp M).ctxSpace (τ :: Γ)).Carrier := by
  refine ⟨(pointCarrier (M := M) (τ := τ) x, γ), ?_⟩
  exact (ctx_proj_eq_unit (M := M) γ).symm

@[simp] theorem tailCtx_consCtx
    {Γ : List (SimpleTy Base)} {τ : SimpleTy Base}
    (x : M.Carrier τ.toTy)
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    tailCtx (M := M) (consCtx (M := M) x γ) = γ :=
  rfl

@[simp] theorem headVal_consCtx
    {Γ : List (SimpleTy Base)} {τ : SimpleTy Base}
    (x : M.Carrier τ.toTy)
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    headVal (M := M) (consCtx (M := M) x γ) = x := by
  cases τ <;> rfl

/-- Decode a one-point context carrier as a native environment. -/
def decodeEnv :
    {Γ : List (SimpleTy Base)} →
      ((simpleInterp M).ctxSpace Γ).Carrier →
        NativeEnv (M := M) Γ
  | [], _ => fun v => nomatch v
  | _ :: _, γ => fun v =>
      match v with
      | .vz => headVal (M := M) γ
      | .vs w => decodeEnv (tailCtx (M := M) γ) w

@[simp] theorem decodeEnv_cons_vz
    {Γ : List (SimpleTy Base)} {τ : SimpleTy Base}
    (γ : ((simpleInterp M).ctxSpace (τ :: Γ)).Carrier) :
    decodeEnv (M := M) γ (Var.vz : Var (SimpleTy.toCtx (τ :: Γ)) τ.toTy) =
      headVal (M := M) γ := by
  rfl

@[simp] theorem decodeEnv_cons_vs
    {Γ : List (SimpleTy Base)} {τ υ : SimpleTy Base}
    (γ : ((simpleInterp M).ctxSpace (υ :: Γ)).Carrier)
    (v : Var (SimpleTy.toCtx Γ) τ.toTy) :
    decodeEnv (M := M) γ (.vs v) =
      decodeEnv (M := M) (tailCtx (M := M) γ) v := by
  rfl

@[simp] theorem decodeEnv_consCtx_apply
    {Γ : List (SimpleTy Base)} {τ : SimpleTy Base}
    (x : M.Carrier τ.toTy)
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    ∀ {σ : Ty Base} (v : Var (SimpleTy.toCtx (τ :: Γ)) σ),
      decodeEnv (M := M) (consCtx (M := M) x γ) v =
        ApplicativeStructure.Env.extend M.toApplicativeStructure
          (decodeEnv (M := M) γ) x v := by
  intro σ v
  cases v with
  | vz =>
      simp only [decodeEnv_cons_vz, ApplicativeStructure.Env.extend_vz, headVal_consCtx]
  | vs w =>
      change decodeEnv (M := M) (tailCtx (M := M) (consCtx (M := M) x γ)) w =
        decodeEnv (M := M) γ w
      rw [tailCtx_consCtx]

/-- Proposition terms into the one-point proposition space. -/
def mkPred {Γ : List (SimpleTy Base)}
    (f : ((simpleInterp M).ctxSpace Γ).Carrier → M.Carrier .prop) :
    SimpleTopologicalInterpretation.Pred (simpleInterp M) Γ where
  toContinuousMap := by
    let _ :
        DiscreteTopology (((simpleInterp M).ctxSpace Γ).Carrier) :=
      EtaleSpace.discreteTopology_of_discrete_base ((simpleInterp M).ctxSpace Γ)
    exact
      { toFun := fun γ => pointCarrier (M := M) (τ := .prop) (f γ)
        continuous_toFun := continuous_of_discreteTopology }
  proj_comp := by
    funext γ
    simp

@[simp] theorem mkPred_val
    {Γ : List (SimpleTy Base)}
    (f : ((simpleInterp M).ctxSpace Γ).Carrier → M.Carrier .prop)
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    pointCarrierVal (M := M)
      ((mkPred (M := M) f).toContinuousMap γ) = f γ := by
  simp [mkPred]

@[simp] theorem lift_apply_consCtx
    {Γ Δ : List (SimpleTy Base)} {τ : SimpleTy Base}
    (σ : (simpleInterp M).CtxHom Δ Γ)
    (x : M.Carrier τ.toTy)
    (γ : ((simpleInterp M).ctxSpace Δ).Carrier) :
    (SimpleTopologicalInterpretation.CtxHom.lift
        (I := simpleInterp M) (τ := τ) σ).toContinuousMap
        (consCtx (M := M) x γ) =
      consCtx (M := M) x (σ.toContinuousMap γ) := by
  cases τ <;> rfl

/-- The one-point simple quantified interpretation induced by a global model. -/
def quantInterp (M : GlobalModel Base Const) :
    SimpleQuantifiedInterpretation Base Const PUnit where
  toPropositional :=
    { toSimple := simpleInterp M
      topPred := mkPred (M := M) fun _ => M.topP
      botPred := mkPred (M := M) fun _ => M.botP
      andPred := mkPred (M := M) fun γ =>
        M.andP (headVal (M := M) γ)
          (headVal (M := M) (tailCtx (M := M) γ))
      orPred := mkPred (M := M) fun γ =>
        M.orP (headVal (M := M) γ)
          (headVal (M := M) (tailCtx (M := M) γ))
      impPred := mkPred (M := M) fun γ =>
        M.impP (headVal (M := M) γ)
          (headVal (M := M) (tailCtx (M := M) γ)) }
  allPred := fun p =>
    mkPred (M := M) fun γ =>
      M.allP fun x =>
        pointCarrierVal (M := M) (p.toContinuousMap (consCtx (M := M) x γ))
  exPred := fun p =>
    mkPred (M := M) fun γ =>
      M.exP fun x =>
        pointCarrierVal (M := M) (p.toContinuousMap (consCtx (M := M) x γ))
  all_reindex := by
    intro τ Γ Δ p σ
    ext γ
    apply Prod.ext
    · rfl
    · rfl
  ex_reindex := by
    intro τ Γ Δ p σ
    ext γ
    apply Prod.ext
    · rfl
    · rfl

namespace SimpleTopologicalInterpretation

namespace CtxTerm

@[simp] theorem headVal_cons
    {Γ Δ : List (SimpleTy Base)} {τ : SimpleTy Base}
    (t : (simpleInterp M).CtxTerm Γ τ)
    (σ : (simpleInterp M).CtxHom Γ Δ)
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    simpleInterp.headVal (M := M)
      ((SimpleTopologicalInterpretation.CtxTerm.cons t σ).toContinuousMap γ) =
      simpleInterp.pointCarrierVal (M := M) (t.toContinuousMap γ) := by
  cases τ <;> rfl

@[simp] theorem tailCtx_cons
    {Γ Δ : List (SimpleTy Base)} {τ : SimpleTy Base}
    (t : (simpleInterp M).CtxTerm Γ τ)
    (σ : (simpleInterp M).CtxHom Γ Δ)
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    simpleInterp.tailCtx (M := M)
      ((SimpleTopologicalInterpretation.CtxTerm.cons t σ).toContinuousMap γ) =
      σ.toContinuousMap γ :=
  rfl

end CtxTerm

end SimpleTopologicalInterpretation

@[simp] theorem top_val
    {Γ : List (SimpleTy Base)}
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    pointCarrierVal (M := M)
      (((quantInterp M).toPropositional.top Γ).toContinuousMap γ) = M.topP := by
  unfold SimplePropositionalInterpretation.top
  rw [SimpleTopologicalInterpretation.CtxTerm.reindex_apply]
  change pointCarrierVal (M := M)
      (((mkPred (M := M) fun _ => M.topP).toContinuousMap)
        ((SimpleTopologicalInterpretation.CtxHom.terminal (simpleInterp M) Γ).toContinuousMap γ)) =
    M.topP
  rw [mkPred_val]

@[simp] theorem bot_val
    {Γ : List (SimpleTy Base)}
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    pointCarrierVal (M := M)
      (((quantInterp M).toPropositional.bot Γ).toContinuousMap γ) = M.botP := by
  unfold SimplePropositionalInterpretation.bot
  rw [SimpleTopologicalInterpretation.CtxTerm.reindex_apply]
  change pointCarrierVal (M := M)
      (((mkPred (M := M) fun _ => M.botP).toContinuousMap)
        ((SimpleTopologicalInterpretation.CtxHom.terminal (simpleInterp M) Γ).toContinuousMap γ)) =
    M.botP
  rw [mkPred_val]

@[simp] theorem conj_val
    {Γ : List (SimpleTy Base)}
    (p q : SimpleTopologicalInterpretation.Pred (simpleInterp M) Γ)
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    pointCarrierVal (M := M)
      (((quantInterp M).toPropositional.conj p q).toContinuousMap γ) =
      M.andP
        (pointCarrierVal (M := M) (p.toContinuousMap γ))
        (pointCarrierVal (M := M) (q.toContinuousMap γ)) := by
  unfold SimplePropositionalInterpretation.conj
  rw [SimpleTopologicalInterpretation.CtxTerm.reindex_apply]
  change pointCarrierVal (M := M)
      (((mkPred (M := M) fun (δ : ((simpleInterp M).ctxSpace [.prop, .prop]).Carrier) =>
          M.andP (headVal (M := M) δ)
            (headVal (M := M) (tailCtx (M := M) δ))).toContinuousMap)
        (((quantInterp M).toPropositional.pairSubst p q).toContinuousMap γ)) =
      M.andP
        (pointCarrierVal (M := M) (p.toContinuousMap γ))
        (pointCarrierVal (M := M) (q.toContinuousMap γ))
  rw [mkPred_val]
  unfold SimplePropositionalInterpretation.pairSubst
  have hhead :
      headVal (M := M)
        ((SimpleTopologicalInterpretation.CtxTerm.cons p
            (SimpleTopologicalInterpretation.CtxTerm.cons q
              (SimpleTopologicalInterpretation.CtxHom.terminal
                ((quantInterp M).toPropositional.toSimple) Γ))).toContinuousMap γ) =
        pointCarrierVal (M := M) (p.toContinuousMap γ) := by
    simpa [quantInterp] using
      (SimpleTopologicalInterpretation.CtxTerm.headVal_cons
        (M := M) (t := p)
        (σ := SimpleTopologicalInterpretation.CtxTerm.cons q
          (SimpleTopologicalInterpretation.CtxHom.terminal (simpleInterp M) Γ))
        (γ := γ))
  have htail :
      tailCtx (M := M)
        ((SimpleTopologicalInterpretation.CtxTerm.cons p
            (SimpleTopologicalInterpretation.CtxTerm.cons q
              (SimpleTopologicalInterpretation.CtxHom.terminal
                ((quantInterp M).toPropositional.toSimple) Γ))).toContinuousMap γ) =
        (SimpleTopologicalInterpretation.CtxTerm.cons q
          (SimpleTopologicalInterpretation.CtxHom.terminal
            ((quantInterp M).toPropositional.toSimple) Γ)).toContinuousMap γ := by
    simpa [quantInterp] using
      (SimpleTopologicalInterpretation.CtxTerm.tailCtx_cons
        (M := M) (t := p)
        (σ := SimpleTopologicalInterpretation.CtxTerm.cons q
          (SimpleTopologicalInterpretation.CtxHom.terminal (simpleInterp M) Γ))
        (γ := γ))
  have hhead₂ :
      headVal (M := M)
        ((SimpleTopologicalInterpretation.CtxTerm.cons q
            (SimpleTopologicalInterpretation.CtxHom.terminal
              ((quantInterp M).toPropositional.toSimple) Γ)).toContinuousMap γ) =
        pointCarrierVal (M := M) (q.toContinuousMap γ) := by
    simpa [quantInterp] using
      (SimpleTopologicalInterpretation.CtxTerm.headVal_cons
        (M := M) (t := q)
        (σ := SimpleTopologicalInterpretation.CtxHom.terminal (simpleInterp M) Γ)
        (γ := γ))
  let δ₁ :=
    (SimpleTopologicalInterpretation.CtxTerm.cons p
      (SimpleTopologicalInterpretation.CtxTerm.cons q
        (SimpleTopologicalInterpretation.CtxHom.terminal
          ((quantInterp M).toPropositional.toSimple) Γ))).toContinuousMap γ
  let δ₂ :=
    (SimpleTopologicalInterpretation.CtxTerm.cons q
      (SimpleTopologicalInterpretation.CtxHom.terminal
        ((quantInterp M).toPropositional.toSimple) Γ)).toContinuousMap γ
  have h1 :
      M.andP (headVal (M := M) δ₁) (headVal (M := M) (tailCtx (M := M) δ₁)) =
        M.andP (pointCarrierVal (M := M) (p.toContinuousMap γ))
          (headVal (M := M) (tailCtx (M := M) δ₁)) := by
    exact congrArg
      (fun a => M.andP a (headVal (M := M) (tailCtx (M := M) δ₁)))
      hhead
  have h2 :
      M.andP (pointCarrierVal (M := M) (p.toContinuousMap γ))
          (headVal (M := M) (tailCtx (M := M) δ₁)) =
        M.andP (pointCarrierVal (M := M) (p.toContinuousMap γ))
          (headVal (M := M) δ₂) := by
    exact congrArg
      (fun (a : ((simpleInterp M).ctxSpace [.prop]).Carrier) =>
        M.andP (pointCarrierVal (M := M) (p.toContinuousMap γ)) (headVal (M := M) a))
      htail
  have h3 :
      M.andP (pointCarrierVal (M := M) (p.toContinuousMap γ))
          (headVal (M := M) δ₂) =
        M.andP (pointCarrierVal (M := M) (p.toContinuousMap γ))
          (pointCarrierVal (M := M) (q.toContinuousMap γ)) := by
    exact congrArg
      (fun a => M.andP (pointCarrierVal (M := M) (p.toContinuousMap γ)) a)
      hhead₂
  exact h1.trans (h2.trans h3)

@[simp] theorem disj_val
    {Γ : List (SimpleTy Base)}
    (p q : SimpleTopologicalInterpretation.Pred (simpleInterp M) Γ)
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    pointCarrierVal (M := M)
      (((quantInterp M).toPropositional.disj p q).toContinuousMap γ) =
      M.orP
        (pointCarrierVal (M := M) (p.toContinuousMap γ))
        (pointCarrierVal (M := M) (q.toContinuousMap γ)) := by
  unfold SimplePropositionalInterpretation.disj
  rw [SimpleTopologicalInterpretation.CtxTerm.reindex_apply]
  change pointCarrierVal (M := M)
      (((mkPred (M := M) fun (δ : ((simpleInterp M).ctxSpace [.prop, .prop]).Carrier) =>
          M.orP (headVal (M := M) δ)
            (headVal (M := M) (tailCtx (M := M) δ))).toContinuousMap)
        (((quantInterp M).toPropositional.pairSubst p q).toContinuousMap γ)) =
      M.orP
        (pointCarrierVal (M := M) (p.toContinuousMap γ))
        (pointCarrierVal (M := M) (q.toContinuousMap γ))
  rw [mkPred_val]
  unfold SimplePropositionalInterpretation.pairSubst
  have hhead :
      headVal (M := M)
        ((SimpleTopologicalInterpretation.CtxTerm.cons p
            (SimpleTopologicalInterpretation.CtxTerm.cons q
              (SimpleTopologicalInterpretation.CtxHom.terminal
                ((quantInterp M).toPropositional.toSimple) Γ))).toContinuousMap γ) =
        pointCarrierVal (M := M) (p.toContinuousMap γ) := by
    simpa [quantInterp] using
      (SimpleTopologicalInterpretation.CtxTerm.headVal_cons
        (M := M) (t := p)
        (σ := SimpleTopologicalInterpretation.CtxTerm.cons q
          (SimpleTopologicalInterpretation.CtxHom.terminal (simpleInterp M) Γ))
        (γ := γ))
  have htail :
      tailCtx (M := M)
        ((SimpleTopologicalInterpretation.CtxTerm.cons p
            (SimpleTopologicalInterpretation.CtxTerm.cons q
              (SimpleTopologicalInterpretation.CtxHom.terminal
                ((quantInterp M).toPropositional.toSimple) Γ))).toContinuousMap γ) =
        (SimpleTopologicalInterpretation.CtxTerm.cons q
          (SimpleTopologicalInterpretation.CtxHom.terminal
            ((quantInterp M).toPropositional.toSimple) Γ)).toContinuousMap γ := by
    simpa [quantInterp] using
      (SimpleTopologicalInterpretation.CtxTerm.tailCtx_cons
        (M := M) (t := p)
        (σ := SimpleTopologicalInterpretation.CtxTerm.cons q
          (SimpleTopologicalInterpretation.CtxHom.terminal (simpleInterp M) Γ))
        (γ := γ))
  have hhead₂ :
      headVal (M := M)
        ((SimpleTopologicalInterpretation.CtxTerm.cons q
            (SimpleTopologicalInterpretation.CtxHom.terminal
              ((quantInterp M).toPropositional.toSimple) Γ)).toContinuousMap γ) =
        pointCarrierVal (M := M) (q.toContinuousMap γ) := by
    simpa [quantInterp] using
      (SimpleTopologicalInterpretation.CtxTerm.headVal_cons
        (M := M) (t := q)
        (σ := SimpleTopologicalInterpretation.CtxHom.terminal (simpleInterp M) Γ)
        (γ := γ))
  let δ₁ :=
    (SimpleTopologicalInterpretation.CtxTerm.cons p
      (SimpleTopologicalInterpretation.CtxTerm.cons q
        (SimpleTopologicalInterpretation.CtxHom.terminal
          ((quantInterp M).toPropositional.toSimple) Γ))).toContinuousMap γ
  let δ₂ :=
    (SimpleTopologicalInterpretation.CtxTerm.cons q
      (SimpleTopologicalInterpretation.CtxHom.terminal
        ((quantInterp M).toPropositional.toSimple) Γ)).toContinuousMap γ
  have h1 :
      M.orP (headVal (M := M) δ₁) (headVal (M := M) (tailCtx (M := M) δ₁)) =
        M.orP (pointCarrierVal (M := M) (p.toContinuousMap γ))
          (headVal (M := M) (tailCtx (M := M) δ₁)) := by
    exact congrArg
      (fun a => M.orP a (headVal (M := M) (tailCtx (M := M) δ₁)))
      hhead
  have h2 :
      M.orP (pointCarrierVal (M := M) (p.toContinuousMap γ))
          (headVal (M := M) (tailCtx (M := M) δ₁)) =
        M.orP (pointCarrierVal (M := M) (p.toContinuousMap γ))
          (headVal (M := M) δ₂) := by
    exact congrArg
      (fun (a : ((simpleInterp M).ctxSpace [.prop]).Carrier) =>
        M.orP (pointCarrierVal (M := M) (p.toContinuousMap γ)) (headVal (M := M) a))
      htail
  have h3 :
      M.orP (pointCarrierVal (M := M) (p.toContinuousMap γ))
          (headVal (M := M) δ₂) =
        M.orP (pointCarrierVal (M := M) (p.toContinuousMap γ))
          (pointCarrierVal (M := M) (q.toContinuousMap γ)) := by
    exact congrArg
      (fun a => M.orP (pointCarrierVal (M := M) (p.toContinuousMap γ)) a)
      hhead₂
  exact h1.trans (h2.trans h3)

@[simp] theorem impl_val
    {Γ : List (SimpleTy Base)}
    (p q : SimpleTopologicalInterpretation.Pred (simpleInterp M) Γ)
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    pointCarrierVal (M := M)
      (((quantInterp M).toPropositional.impl p q).toContinuousMap γ) =
      M.impP
        (pointCarrierVal (M := M) (p.toContinuousMap γ))
        (pointCarrierVal (M := M) (q.toContinuousMap γ)) := by
  unfold SimplePropositionalInterpretation.impl
  rw [SimpleTopologicalInterpretation.CtxTerm.reindex_apply]
  change pointCarrierVal (M := M)
      (((mkPred (M := M) fun (δ : ((simpleInterp M).ctxSpace [.prop, .prop]).Carrier) =>
          M.impP (headVal (M := M) δ)
            (headVal (M := M) (tailCtx (M := M) δ))).toContinuousMap)
        (((quantInterp M).toPropositional.pairSubst p q).toContinuousMap γ)) =
      M.impP
        (pointCarrierVal (M := M) (p.toContinuousMap γ))
        (pointCarrierVal (M := M) (q.toContinuousMap γ))
  rw [mkPred_val]
  unfold SimplePropositionalInterpretation.pairSubst
  have hhead :
      headVal (M := M)
        ((SimpleTopologicalInterpretation.CtxTerm.cons p
            (SimpleTopologicalInterpretation.CtxTerm.cons q
              (SimpleTopologicalInterpretation.CtxHom.terminal
                ((quantInterp M).toPropositional.toSimple) Γ))).toContinuousMap γ) =
        pointCarrierVal (M := M) (p.toContinuousMap γ) := by
    simpa [quantInterp] using
      (SimpleTopologicalInterpretation.CtxTerm.headVal_cons
        (M := M) (t := p)
        (σ := SimpleTopologicalInterpretation.CtxTerm.cons q
          (SimpleTopologicalInterpretation.CtxHom.terminal (simpleInterp M) Γ))
        (γ := γ))
  have htail :
      tailCtx (M := M)
        ((SimpleTopologicalInterpretation.CtxTerm.cons p
            (SimpleTopologicalInterpretation.CtxTerm.cons q
              (SimpleTopologicalInterpretation.CtxHom.terminal
                ((quantInterp M).toPropositional.toSimple) Γ))).toContinuousMap γ) =
        (SimpleTopologicalInterpretation.CtxTerm.cons q
          (SimpleTopologicalInterpretation.CtxHom.terminal
            ((quantInterp M).toPropositional.toSimple) Γ)).toContinuousMap γ := by
    simpa [quantInterp] using
      (SimpleTopologicalInterpretation.CtxTerm.tailCtx_cons
        (M := M) (t := p)
        (σ := SimpleTopologicalInterpretation.CtxTerm.cons q
          (SimpleTopologicalInterpretation.CtxHom.terminal (simpleInterp M) Γ))
        (γ := γ))
  have hhead₂ :
      headVal (M := M)
        ((SimpleTopologicalInterpretation.CtxTerm.cons q
            (SimpleTopologicalInterpretation.CtxHom.terminal
              ((quantInterp M).toPropositional.toSimple) Γ)).toContinuousMap γ) =
        pointCarrierVal (M := M) (q.toContinuousMap γ) := by
    simpa [quantInterp] using
      (SimpleTopologicalInterpretation.CtxTerm.headVal_cons
        (M := M) (t := q)
        (σ := SimpleTopologicalInterpretation.CtxHom.terminal (simpleInterp M) Γ)
        (γ := γ))
  let δ₁ :=
    (SimpleTopologicalInterpretation.CtxTerm.cons p
      (SimpleTopologicalInterpretation.CtxTerm.cons q
        (SimpleTopologicalInterpretation.CtxHom.terminal
          ((quantInterp M).toPropositional.toSimple) Γ))).toContinuousMap γ
  let δ₂ :=
    (SimpleTopologicalInterpretation.CtxTerm.cons q
      (SimpleTopologicalInterpretation.CtxHom.terminal
        ((quantInterp M).toPropositional.toSimple) Γ)).toContinuousMap γ
  have h1 :
      M.impP (headVal (M := M) δ₁) (headVal (M := M) (tailCtx (M := M) δ₁)) =
        M.impP (pointCarrierVal (M := M) (p.toContinuousMap γ))
          (headVal (M := M) (tailCtx (M := M) δ₁)) := by
    exact congrArg
      (fun a => M.impP a (headVal (M := M) (tailCtx (M := M) δ₁)))
      hhead
  have h2 :
      M.impP (pointCarrierVal (M := M) (p.toContinuousMap γ))
          (headVal (M := M) (tailCtx (M := M) δ₁)) =
        M.impP (pointCarrierVal (M := M) (p.toContinuousMap γ))
          (headVal (M := M) δ₂) := by
    exact congrArg
      (fun (a : ((simpleInterp M).ctxSpace [.prop]).Carrier) =>
        M.impP (pointCarrierVal (M := M) (p.toContinuousMap γ)) (headVal (M := M) a))
      htail
  have h3 :
      M.impP (pointCarrierVal (M := M) (p.toContinuousMap γ))
          (headVal (M := M) δ₂) =
        M.impP (pointCarrierVal (M := M) (p.toContinuousMap γ))
          (pointCarrierVal (M := M) (q.toContinuousMap γ)) := by
    exact congrArg
      (fun a => M.impP (pointCarrierVal (M := M) (p.toContinuousMap γ)) a)
      hhead₂
  exact h1.trans (h2.trans h3)

@[simp] theorem all_val
    {Γ : List (SimpleTy Base)} {τ : SimpleTy Base}
    (p : SimpleTopologicalInterpretation.Pred (simpleInterp M) (τ :: Γ))
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    pointCarrierVal (M := M)
      (((quantInterp M).allPred p).toContinuousMap γ) =
      M.allP fun x =>
        pointCarrierVal (M := M) (p.toContinuousMap (consCtx (M := M) x γ)) := by
  rfl

@[simp] theorem ex_val
    {Γ : List (SimpleTy Base)} {τ : SimpleTy Base}
    (p : SimpleTopologicalInterpretation.Pred (simpleInterp M) (τ :: Γ))
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    pointCarrierVal (M := M)
      (((quantInterp M).exPred p).toContinuousMap γ) =
      M.exP fun x =>
        pointCarrierVal (M := M) (p.toContinuousMap (consCtx (M := M) x γ)) := by
  rfl

namespace SemilocalModel

  @[simp] theorem eval_env_ext
    {S : SemilocalModel Base Const}
    {Γ : Ctx Base} {τ : Ty Base}
    {ρ ν : SemilocalModel.Env S Γ}
    (t : Term Const Γ τ)
    (hρ : ∀ {σ : Ty Base} (v : Var Γ σ), ρ v = ν v) :
    SemilocalModel.eval S ρ t = SemilocalModel.eval S ν t := by
    induction t with
    | var v =>
        exact hρ v
    | const c =>
        rfl
    | app f t ihf iht =>
        simp [SemilocalModel.eval, ihf (ν := ν) hρ, iht (ν := ν) hρ]
    | lam t ih =>
        simp [SemilocalModel.eval]
        apply congrArg S.lam
        funext x
        exact ih (ν := ApplicativeStructure.Env.extend S.toApplicativeStructure ν x) (by
          intro σ v
          cases v with
          | vz =>
              rfl
          | vs w =>
              simpa [ApplicativeStructure.Env.extend] using hρ w)
    | top =>
        rfl
    | bot =>
        rfl
    | and φ ψ ihφ ihψ =>
        simp [SemilocalModel.eval, ihφ (ν := ν) hρ, ihψ (ν := ν) hρ]
    | or φ ψ ihφ ihψ =>
        simp [SemilocalModel.eval, ihφ (ν := ν) hρ, ihψ (ν := ν) hρ]
    | imp φ ψ ihφ ihψ =>
        simp [SemilocalModel.eval, ihφ (ν := ν) hρ, ihψ (ν := ν) hρ]
    | not φ ih =>
        simp [SemilocalModel.eval, ih (ν := ν) hρ]
    | eq t u iht ihu =>
        simp [SemilocalModel.eval, iht (ν := ν) hρ, ihu (ν := ν) hρ]
    | all φ ih =>
        simp [SemilocalModel.eval]
        apply congrArg S.allP
        funext x
        exact ih (ν := ApplicativeStructure.Env.extend S.toApplicativeStructure ν x) (by
          intro σ v
          cases v with
          | vz =>
              rfl
          | vs w =>
              simpa [ApplicativeStructure.Env.extend] using hρ w)
    | ex φ ih =>
        simp [SemilocalModel.eval]
        apply congrArg S.exP
        funext x
        exact ih (ν := ApplicativeStructure.Env.extend S.toApplicativeStructure ν x) (by
          intro σ v
          cases v with
          | vz =>
              rfl
          | vs w =>
              simpa [ApplicativeStructure.Env.extend] using hρ w)

end SemilocalModel

namespace SimpleTopologicalInterpretation

namespace CtxTerm

@[simp] theorem var_val_decode
    {Γ : List (SimpleTy Base)} {τ : SimpleTy Base}
    (x : SimpleVar Base Γ τ)
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    pointCarrierVal (M := M)
      ((SimpleTopologicalInterpretation.CtxTerm.var (simpleInterp M) x).toContinuousMap γ) =
      simpleInterp.decodeEnv (M := M) γ (SimpleVar.toVar x) := by
  induction x with
  | vz =>
      rfl
  | @vs Γ υ τ x ih =>
      change pointCarrierVal (M := M)
        ((SimpleTopologicalInterpretation.CtxTerm.var (simpleInterp M) x).toContinuousMap
          (simpleInterp.tailCtx (M := M) γ)) =
        simpleInterp.decodeEnv (M := M) (simpleInterp.tailCtx (M := M) γ)
          (SimpleVar.toVar x)
      exact ih (simpleInterp.tailCtx (M := M) γ)

end CtxTerm

namespace SimpleTerm

@[simp] theorem eval_val_decode
    {Γ : List (SimpleTy Base)} {τ : SimpleTy Base}
    (t : Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleTerm Base Const Γ τ)
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    pointCarrierVal (M := M)
      ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleTopologicalInterpretation.SimpleTerm.eval
          (simpleInterp M) t).toContinuousMap γ) =
      SemilocalModel.eval M.toSemilocalModel
        (simpleInterp.decodeEnv (M := M) γ)
        (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleTerm.toTerm t) := by
  cases t with
  | var x =>
      rw [Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleTerm.toTerm, SemilocalModel.eval]
      exact CtxTerm.var_val_decode (M := M) x γ
  | const c =>
      cases τ <;> rfl

end SimpleTerm

end SimpleTopologicalInterpretation

namespace SimpleQuantifiedFormula

@[simp] theorem eval_val_decode
    {Γ : List (SimpleTy Base)}
    (φ : SimpleQuantifiedFormula Base Const Γ)
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    pointCarrierVal (M := M)
      ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
          (quantInterp M) φ).toContinuousMap γ) =
      SemilocalModel.eval M.toSemilocalModel
        (simpleInterp.decodeEnv (M := M) γ)
        (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ) := by
  induction φ with
  | atom t =>
      rw [Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval,
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula]
      exact SimpleTopologicalInterpretation.SimpleTerm.eval_val_decode (M := M) t γ
  | top =>
      rw [Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval,
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula,
        SemilocalModel.eval]
      exact top_val (M := M) (γ := γ)
  | bot =>
      rw [Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval,
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula,
        SemilocalModel.eval]
      exact bot_val (M := M) (γ := γ)
  | conj φ ψ ihφ ihψ =>
      rw [Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval,
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula,
        SemilocalModel.eval]
      rw [conj_val (M := M)
        (p := Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
          (quantInterp M) φ)
        (q := Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
          (quantInterp M) ψ)
        γ]
      calc
        M.andP
            (pointCarrierVal (M := M)
              ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
                  (quantInterp M) φ).toContinuousMap γ))
            (pointCarrierVal (M := M)
              ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
                  (quantInterp M) ψ).toContinuousMap γ))
            =
          M.andP
            (SemilocalModel.eval M.toSemilocalModel
              (simpleInterp.decodeEnv (M := M) γ)
              (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ))
            (pointCarrierVal (M := M)
              ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
                  (quantInterp M) ψ).toContinuousMap γ)) := by
            exact congrArg
              (fun a => M.andP a
                (pointCarrierVal (M := M)
                  ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
                      (quantInterp M) ψ).toContinuousMap γ)))
              (ihφ γ)
        _ =
          M.andP
            (SemilocalModel.eval M.toSemilocalModel
              (simpleInterp.decodeEnv (M := M) γ)
              (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ))
            (SemilocalModel.eval M.toSemilocalModel
              (simpleInterp.decodeEnv (M := M) γ)
              (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula ψ)) := by
            exact congrArg
              (fun a => M.andP
                (SemilocalModel.eval M.toSemilocalModel
                  (simpleInterp.decodeEnv (M := M) γ)
                  (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ)) a)
              (ihψ γ)
  | disj φ ψ ihφ ihψ =>
      rw [Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval,
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula,
        SemilocalModel.eval]
      rw [disj_val (M := M)
        (p := Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
          (quantInterp M) φ)
        (q := Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
          (quantInterp M) ψ)
        γ]
      calc
        M.orP
            (pointCarrierVal (M := M)
              ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
                  (quantInterp M) φ).toContinuousMap γ))
            (pointCarrierVal (M := M)
              ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
                  (quantInterp M) ψ).toContinuousMap γ))
            =
          M.orP
            (SemilocalModel.eval M.toSemilocalModel
              (simpleInterp.decodeEnv (M := M) γ)
              (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ))
            (pointCarrierVal (M := M)
              ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
                  (quantInterp M) ψ).toContinuousMap γ)) := by
            exact congrArg
              (fun a => M.orP a
                (pointCarrierVal (M := M)
                  ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
                      (quantInterp M) ψ).toContinuousMap γ)))
              (ihφ γ)
        _ =
          M.orP
            (SemilocalModel.eval M.toSemilocalModel
              (simpleInterp.decodeEnv (M := M) γ)
              (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ))
            (SemilocalModel.eval M.toSemilocalModel
              (simpleInterp.decodeEnv (M := M) γ)
              (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula ψ)) := by
            exact congrArg
              (fun a => M.orP
                (SemilocalModel.eval M.toSemilocalModel
                  (simpleInterp.decodeEnv (M := M) γ)
                  (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ)) a)
              (ihψ γ)
  | impl φ ψ ihφ ihψ =>
      rw [Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval,
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula,
        SemilocalModel.eval]
      rw [impl_val (M := M)
        (p := Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
          (quantInterp M) φ)
        (q := Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
          (quantInterp M) ψ)
        γ]
      calc
        M.impP
            (pointCarrierVal (M := M)
              ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
                  (quantInterp M) φ).toContinuousMap γ))
            (pointCarrierVal (M := M)
              ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
                  (quantInterp M) ψ).toContinuousMap γ))
            =
          M.impP
            (SemilocalModel.eval M.toSemilocalModel
              (simpleInterp.decodeEnv (M := M) γ)
              (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ))
            (pointCarrierVal (M := M)
              ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
                  (quantInterp M) ψ).toContinuousMap γ)) := by
            exact congrArg
              (fun a => M.impP a
                (pointCarrierVal (M := M)
                  ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
                      (quantInterp M) ψ).toContinuousMap γ)))
              (ihφ γ)
        _ =
          M.impP
            (SemilocalModel.eval M.toSemilocalModel
              (simpleInterp.decodeEnv (M := M) γ)
              (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ))
            (SemilocalModel.eval M.toSemilocalModel
              (simpleInterp.decodeEnv (M := M) γ)
              (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula ψ)) := by
            exact congrArg
              (fun a => M.impP
                (SemilocalModel.eval M.toSemilocalModel
                  (simpleInterp.decodeEnv (M := M) γ)
                  (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ)) a)
              (ihψ γ)
  | @all Γ τ φ ih =>
      rw [Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval,
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula,
        SemilocalModel.eval]
      rw [all_val (M := M)
        (p := Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
          (quantInterp M) φ)
        γ]
      apply congrArg M.allP
      funext x
      have henv :
          ∀ {σ : Ty Base} (v : Var (SimpleTy.toCtx (τ :: Γ)) σ),
            simpleInterp.decodeEnv (M := M) (simpleInterp.consCtx (M := M) x γ) v =
              ApplicativeStructure.Env.extend M.toApplicativeStructure
                (simpleInterp.decodeEnv (M := M) γ) x v :=
        simpleInterp.decodeEnv_consCtx_apply (M := M) x γ
      calc
        pointCarrierVal (M := M)
            ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
                (quantInterp M) φ).toContinuousMap
              (simpleInterp.consCtx (M := M) x γ))
            =
          SemilocalModel.eval M.toSemilocalModel
            (simpleInterp.decodeEnv (M := M) (simpleInterp.consCtx (M := M) x γ))
            (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ) := by
            exact ih (simpleInterp.consCtx (M := M) x γ)
        _ =
          SemilocalModel.eval M.toSemilocalModel
            (ApplicativeStructure.Env.extend M.toApplicativeStructure
              (simpleInterp.decodeEnv (M := M) γ) x)
            (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ) := by
            exact SemilocalModel.eval_env_ext
              (S := M.toSemilocalModel)
              (t := Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ)
              (hρ := henv)
  | @ex Γ τ φ ih =>
      rw [Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval,
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula,
        SemilocalModel.eval]
      rw [ex_val (M := M)
        (p := Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
          (quantInterp M) φ)
        γ]
      apply congrArg M.exP
      funext x
      have henv :
          ∀ {σ : Ty Base} (v : Var (SimpleTy.toCtx (τ :: Γ)) σ),
            simpleInterp.decodeEnv (M := M) (simpleInterp.consCtx (M := M) x γ) v =
              ApplicativeStructure.Env.extend M.toApplicativeStructure
                (simpleInterp.decodeEnv (M := M) γ) x v :=
        simpleInterp.decodeEnv_consCtx_apply (M := M) x γ
      calc
        pointCarrierVal (M := M)
            ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
                (quantInterp M) φ).toContinuousMap
              (simpleInterp.consCtx (M := M) x γ))
            =
          SemilocalModel.eval M.toSemilocalModel
            (simpleInterp.decodeEnv (M := M) (simpleInterp.consCtx (M := M) x γ))
            (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ) := by
            exact ih (simpleInterp.consCtx (M := M) x γ)
        _ =
          SemilocalModel.eval M.toSemilocalModel
            (ApplicativeStructure.Env.extend M.toApplicativeStructure
              (simpleInterp.decodeEnv (M := M) γ) x)
            (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ) := by
            exact SemilocalModel.eval_env_ext
              (S := M.toSemilocalModel)
              (t := Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ)
              (hρ := henv)

theorem truth_eval_eq_formulaTruth
    {Γ : List (SimpleTy Base)}
    (φ : SimpleQuantifiedFormula Base Const Γ)
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    M.truth
        (simpleInterp.pointCarrierVal (M := M)
          ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
              (quantInterp M) φ).toContinuousMap γ)) =
      SemilocalModel.formulaTruth M.toSemilocalModel
        (simpleInterp.decodeEnv (M := M) γ)
        (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ) := by
  simp [SemilocalModel.formulaTruth, eval_val_decode]

/-- Topological truth of a simple quantified formula in the one-point model. -/
def truthEval
    {Γ : List (SimpleTy Base)}
    (φ : SimpleQuantifiedFormula Base Const Γ)
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) : M.Omega :=
  M.truth
    (simpleInterp.pointCarrierVal (M := M)
      ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
          (quantInterp M) φ).toContinuousMap γ))

@[simp] theorem truthEval_eq_formulaTruth
    {Γ : List (SimpleTy Base)}
    (φ : SimpleQuantifiedFormula Base Const Γ)
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    truthEval (M := M) φ γ =
      SemilocalModel.formulaTruth M.toSemilocalModel
        (simpleInterp.decodeEnv (M := M) γ)
        (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ) := by
  simpa [truthEval] using truth_eval_eq_formulaTruth (M := M) φ γ

/-- Meet of the translated antecedents in the one-point topological semantics. -/
def truthAntecedent
    {Γ : List (SimpleTy Base)}
    (Δ : List (SimpleQuantifiedFormula Base Const Γ))
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) : M.Omega :=
  match Δ with
  | [] => ⊤
  | ψ :: Δ => truthEval M ψ γ ⊓ truthAntecedent Δ γ

@[simp] theorem truthAntecedent_eq_antecedentTruth
    {Γ : List (SimpleTy Base)}
    (Δ : List (SimpleQuantifiedFormula Base Const Γ))
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    truthAntecedent M Δ γ =
      SemilocalModel.antecedentTruth M.toSemilocalModel
        (simpleInterp.decodeEnv (M := M) γ)
        (Δ.map Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula) := by
  induction Δ with
  | nil =>
      simp [truthAntecedent, SemilocalModel.antecedentTruth]
  | cons ψ Δ ih =>
      simpa [truthAntecedent, SemilocalModel.antecedentTruth,
        truthEval_eq_formulaTruth (M := M) ψ γ] using
        congrArg
          (fun ω : M.Omega =>
            SemilocalModel.formulaTruth M.toSemilocalModel
              (simpleInterp.decodeEnv (M := M) γ)
              (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula ψ) ⊓ ω)
          ih

/-- Direct validity of a translated simple sequent in the Awodey-Butz point model. -/
def TruthValidSequent
    {Γ : List (SimpleTy Base)}
    (Δ : List (SimpleQuantifiedFormula Base Const Γ))
    (φ : SimpleQuantifiedFormula Base Const Γ) : Prop :=
  ∀ γ : ((simpleInterp M).ctxSpace Γ).Carrier,
    truthAntecedent M Δ γ ≤ truthEval M φ γ

theorem truthValidSequent_of_translated
    {Γ : List (SimpleTy Base)}
    {Δ : List (SimpleQuantifiedFormula Base Const Γ)}
    {φ : SimpleQuantifiedFormula Base Const Γ}
    (h : Derivable (Base := Base) (Const := Const)
      (Δ.map Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula)
      (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ)) :
    TruthValidSequent M Δ φ := by
  intro γ
  rw [truthAntecedent_eq_antecedentTruth (M := M) Δ γ]
  rw [truthEval_eq_formulaTruth (M := M) φ γ]
  exact GlobalModel.soundness M h (simpleInterp.decodeEnv (M := M) γ)

theorem truthValidSequent_of_closed_derivable
    {φ : SimpleQuantifiedFormula Base Const []}
    (h : Derivable (Base := Base) (Const := Const) []
      (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ)) :
    TruthValidSequent M [] φ := by
  exact truthValidSequent_of_translated (M := M) (Δ := []) (φ := φ) h

theorem not_derivable_of_truth_counterexample
    {Γ : List (SimpleTy Base)}
    {Δ : List (SimpleQuantifiedFormula Base Const Γ)}
    {φ : SimpleQuantifiedFormula Base Const Γ}
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier)
    (hΔ : truthAntecedent M Δ γ = ⊤)
    (hφ : truthEval (M := M) φ γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const)
      (Δ.map Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula)
      (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ) := by
  intro hder
  have hvalid :
      truthAntecedent M Δ γ ≤ truthEval (M := M) φ γ :=
    truthValidSequent_of_translated (M := M) (Δ := Δ) (φ := φ) hder γ
  have htop_le : (⊤ : M.Omega) ≤ truthEval (M := M) φ γ := by
    rw [← hΔ]
    exact hvalid
  exact hφ (le_antisymm le_top htop_le)

theorem not_derivable_of_closed_truth_ne_top
    {φ : SimpleQuantifiedFormula Base Const []}
    (hφ : truthEval (M := M) φ () ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) []
      (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ) := by
  exact not_derivable_of_truth_counterexample (M := M) (Δ := []) (φ := φ) ()
    (by simp [truthAntecedent]) hφ

theorem truth_eval_sound_of_translated
    {Γ : List (SimpleTy Base)}
    {Δ : List (SimpleQuantifiedFormula Base Const Γ)}
    {φ : SimpleQuantifiedFormula Base Const Γ}
    (h : Derivable (Base := Base) (Const := Const)
      (Δ.map Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula)
      (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ))
    (γ : ((simpleInterp M).ctxSpace Γ).Carrier) :
    SemilocalModel.antecedentTruth M.toSemilocalModel
        (simpleInterp.decodeEnv (M := M) γ)
        (Δ.map Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula) ≤
      M.truth
        (simpleInterp.pointCarrierVal (M := M)
          ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
              (quantInterp M) φ).toContinuousMap γ)) := by
  rw [truth_eval_eq_formulaTruth (M := M) φ γ]
  exact GlobalModel.soundness M h (simpleInterp.decodeEnv (M := M) γ)

theorem truth_eval_of_closed_derivable
    {φ : SimpleQuantifiedFormula Base Const []}
    (h : Derivable (Base := Base) (Const := Const) []
      (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.toFormula φ)) :
    M.truth
        (simpleInterp.pointCarrierVal (M := M)
          ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
              (quantInterp M) φ).toContinuousMap ())) = ⊤ := by
  let γ0 : ((simpleInterp M).ctxSpace ([] : List (SimpleTy Base))).Carrier := ()
  have hs :
      SemilocalModel.antecedentTruth M.toSemilocalModel
          (simpleInterp.decodeEnv (M := M) γ0)
          ([] : List (Formula Const (SimpleTy.toCtx ([] : List (SimpleTy Base))))) ≤
        M.truth
          (simpleInterp.pointCarrierVal (M := M)
            ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
                (quantInterp M) φ).toContinuousMap γ0)) :=
    truth_eval_sound_of_translated (M := M) (Δ := []) (φ := φ) h γ0
  have htop :
      (⊤ : M.Omega) ≤
        M.truth
          (simpleInterp.pointCarrierVal (M := M)
            ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedFormula.SimpleQuantifiedInterpretation.eval
                (quantInterp M) φ).toContinuousMap γ0)) := by
    simpa [SemilocalModel.antecedentTruth] using hs
  exact le_antisymm le_top htop

end SimpleQuantifiedFormula

end simpleInterp

end SimpleQuantifiedTopologicalGlobalModelBridge

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
