import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermHenkinWorldBridge

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermHenkinWorldBridgeRegression

open Mettapedia.Logic.HOL
open Mettapedia.Logic.PLNWorldModel
open CompletenessFrontier
open ClosedTermCanonicalWorldModel
open scoped ENNReal

inductive TestBase where
  | atom
deriving DecidableEq, Repr

inductive TestConst : Ty TestBase → Type where
  | a : TestConst (.base .atom)

def closeAtomSubst : Subst TestConst [(.base .atom)] [] :=
  fun {_τ} v =>
    match v with
    | .vz => .const TestConst.a

def atomVarReflFormula : Formula TestConst [(.base .atom)] :=
  .eq (.var .vz) (.var .vz)

def atomConstReflFormula : ClosedFormula TestConst :=
  .eq (.const TestConst.a) (.const TestConst.a)

theorem subst_instantiate_canary
    {Γ Γ' : Ctx TestBase} {σ τ : Ty TestBase}
    (σs : Subst TestConst Γ Γ') (t : Term TestConst Γ σ)
    (u : Term TestConst (σ :: Γ) τ) :
    subst σs (instantiate (Base := TestBase) t u) =
      instantiate (Base := TestBase)
        (subst σs t)
        (subst (Subst.lift (Base := TestBase) (Const := TestConst) (σ := σ) σs) u) :=
  subst_instantiate (Base := TestBase) (Const := TestConst) σs t u

theorem extDerivation_subst_weakenHyps_canary
    {Γ Γ' : Ctx TestBase} {σ : Ty TestBase}
    (σs : Subst TestConst Γ Γ') (Δ : List (Formula TestConst Γ)) :
    weakenHyps
        (Base := TestBase)
        (Const := TestConst)
        (σ := σ)
        (Δ.map (subst σs)) =
      (weakenHyps (Base := TestBase) (Const := TestConst) (σ := σ) Δ).map
        (subst (Subst.lift (Base := TestBase) (Const := TestConst) (σ := σ) σs)) :=
  ExtDerivation.subst_weakenHyps
    (Base := TestBase) (Const := TestConst) σs Δ

theorem extDerivation_subst_derivation_canary
    {Γ Γ' : Ctx TestBase}
    {Δ : List (Formula TestConst Γ)} {φ : Formula TestConst Γ}
    (σs : Subst TestConst Γ Γ')
    (hDer : ExtDerivation TestConst Δ φ) :
    ExtDerivation TestConst (Δ.map (subst σs)) (subst σs φ) :=
  ExtDerivation.subst_derivation
    (Base := TestBase) (Const := TestConst) σs hDer

theorem weakenHyps_append_canary
    {Γ : Ctx TestBase} {σ : Ty TestBase}
    (Δ Ε : List (Formula TestConst Γ)) :
    weakenHyps (Base := TestBase) (Const := TestConst) (σ := σ) (Δ ++ Ε) =
      weakenHyps (Base := TestBase) (Const := TestConst) (σ := σ) Δ ++
        weakenHyps (Base := TestBase) (Const := TestConst) (σ := σ) Ε :=
  weakenHyps_append (Base := TestBase) (Const := TestConst) Δ Ε

theorem weakenClosedTheoryToCtx_append_canary
    (Γ : Ctx TestBase) (Δ E : ClosedTheory TestConst) :
    weakenClosedTheoryToCtx (Base := TestBase) (Const := TestConst) Γ (Δ ++ E) =
      weakenClosedTheoryToCtx (Base := TestBase) (Const := TestConst) Γ Δ ++
        weakenClosedTheoryToCtx (Base := TestBase) (Const := TestConst) Γ E :=
  weakenClosedTheoryToCtx_append
    (Base := TestBase) (Const := TestConst) Γ Δ E

theorem weakenClosedTheoryToCtx_ctx_cons_canary
    {σ : Ty TestBase} (Γ : Ctx TestBase) (Δ : ClosedTheory TestConst) :
    weakenClosedTheoryToCtx (Base := TestBase) (Const := TestConst) (σ :: Γ) Δ =
      weakenHyps (Base := TestBase) (Const := TestConst) (σ := σ)
        (weakenClosedTheoryToCtx (Base := TestBase) (Const := TestConst) Γ Δ) :=
  weakenClosedTheoryToCtx_ctx_cons
    (Base := TestBase) (Const := TestConst) Γ Δ

theorem weakenAntecedents_eq_weakenHyps_canary
    {Γ : Ctx TestBase} {σ : Ty TestBase} (Δ : List (Formula TestConst Γ)) :
    weakenAntecedents (Base := TestBase) (Const := TestConst) σ Δ =
      weakenHyps (Base := TestBase) (Const := TestConst) (σ := σ) Δ :=
  weakenAntecedents_eq_weakenHyps
    (Base := TestBase) (Const := TestConst) Δ

theorem noConstOccurrence_weakenClosedFormulaToCtx_canary
    {Γ : Ctx TestBase} {σ : Ty TestBase}
    (c : TestConst σ) {φ : ClosedFormula TestConst}
    (hφ : NoConstOccurrence c φ) :
    NoConstOccurrence c
      (weakenClosedFormulaToCtx (Base := TestBase) (Const := TestConst) Γ φ) :=
  noConstOccurrence_weakenClosedFormulaToCtx
    (Base := TestBase) (Const := TestConst) c Γ hφ

theorem noConstOccurrenceIn_weakenClosedTheoryToCtx_canary
    {Γ : Ctx TestBase} {σ : Ty TestBase}
    (c : TestConst σ) {Δ : ClosedTheory TestConst}
    (hΔ :
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) c Δ)
    {φ : Formula TestConst Γ}
    (hφ : φ ∈
      weakenClosedTheoryToCtx (Base := TestBase) (Const := TestConst) Γ Δ) :
    NoConstOccurrence c φ :=
  ClosedTheorySet.noConstOccurrenceIn_weakenClosedTheoryToCtx
    (Base := TestBase) (Const := TestConst) c Γ hΔ hφ

theorem extDerivation_weakenClosedTheoryToCtx_canary
    (Γ : Ctx TestBase) {Δ : ClosedTheory TestConst}
    {θ : ClosedFormula TestConst}
    (hDer : ClosedTheory.Provable (Const := TestConst) Δ θ) :
    ExtDerivation TestConst
      (weakenClosedTheoryToCtx (Base := TestBase) (Const := TestConst) Γ Δ)
      (weakenClosedFormulaToCtx (Base := TestBase) (Const := TestConst) Γ θ) :=
  extDerivation_weakenClosedTheoryToCtx
    (Base := TestBase) (Const := TestConst) Γ hDer

theorem extDerivation_subst_hyp_concrete_canary :
    ExtDerivation TestConst [atomConstReflFormula] atomConstReflFormula := by
  simpa [atomVarReflFormula, atomConstReflFormula, closeAtomSubst, subst]
    using
      ExtDerivation.subst_derivation
        (Base := TestBase) (Const := TestConst)
        closeAtomSubst
        (ExtDerivation.hyp
          (Const := TestConst)
          (Δ := [atomVarReflFormula])
          (φ := atomVarReflFormula)
          (by simp))

theorem abstractConstAt_instantiate_const_self_canary
    {σ : Ty TestBase} (c : TestConst σ) (φ : Formula TestConst [σ])
    (hφno : NoConstOccurrence c φ) :
    abstractConstAt (Base := TestBase) (Γ := []) (τ := .prop) c []
      (instantiate (Base := TestBase) (.const c) φ) = φ :=
  abstractConstAt_instantiate_const_self
    (Base := TestBase) (Const := TestConst) c φ hφno

theorem weakenClosedFormulaToCtx_imp_canary
    (Γ : Ctx TestBase) (φ ψ : ClosedFormula TestConst) :
    weakenClosedFormulaToCtx (Base := TestBase) (Const := TestConst) Γ (.imp φ ψ) =
      .imp
        (weakenClosedFormulaToCtx (Base := TestBase) (Const := TestConst) Γ φ)
        (weakenClosedFormulaToCtx (Base := TestBase) (Const := TestConst) Γ ψ) :=
  weakenClosedFormulaToCtx_imp
    (Base := TestBase) (Const := TestConst) Γ φ ψ

def constantHenkinAbstractedBody_canary
    {σ : Ty TestBase} (φ : Formula TestConst [σ]) :
    Formula TestConst (σ :: [σ]) :=
  ClosedTheorySet.constantHenkinAbstractedBody
    (Base := TestBase) (Const := TestConst) φ

theorem abstractConstAt_constantHenkinExImplication_canary
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {σ : Ty TestBase} (φ : Formula TestConst [σ])
    (hφno : NoConstOccurrence (exConst φ) φ) :
    abstractConstAt (Base := TestBase) (Γ := []) (τ := .prop) (exConst φ) []
        (ClosedTheorySet.constantHenkinExImplication
          (Base := TestBase) (Const := TestConst) exConst φ) =
      .imp (.ex (ClosedTheorySet.constantHenkinAbstractedBody
          (Base := TestBase) (Const := TestConst) φ))
        φ :=
  ClosedTheorySet.abstractConstAt_constantHenkinExImplication
    (Base := TestBase) (Const := TestConst) exConst φ hφno

theorem abstractConstAt_constantHenkinAllImplication_canary
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {σ : Ty TestBase} (φ : Formula TestConst [σ])
    (hφno : NoConstOccurrence (allConst φ) φ) :
    abstractConstAt (Base := TestBase) (Γ := []) (τ := .prop) (allConst φ) []
        (ClosedTheorySet.constantHenkinAllImplication
          (Base := TestBase) (Const := TestConst) allConst φ) =
      .imp φ (.all (ClosedTheorySet.constantHenkinAbstractedBody
          (Base := TestBase) (Const := TestConst) φ)) :=
  ClosedTheorySet.abstractConstAt_constantHenkinAllImplication
    (Base := TestBase) (Const := TestConst) allConst φ hφno

theorem weakenClosedFormulaToCtx_constantHenkinExImplication_canary
    (Γ : Ctx TestBase)
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {σ : Ty TestBase} (φ : Formula TestConst [σ]) :
    weakenClosedFormulaToCtx (Base := TestBase) (Const := TestConst) Γ
        (ClosedTheorySet.constantHenkinExImplication
          (Base := TestBase) (Const := TestConst) exConst φ) =
      .imp
        (weakenClosedFormulaToCtx (Base := TestBase) (Const := TestConst) Γ
          (.ex φ : ClosedFormula TestConst))
        (weakenClosedFormulaToCtx (Base := TestBase) (Const := TestConst) Γ
          (instantiate (Base := TestBase) (.const (exConst φ)) φ)) :=
  ClosedTheorySet.weakenClosedFormulaToCtx_constantHenkinExImplication
    (Base := TestBase) (Const := TestConst) Γ exConst φ

theorem weakenClosedFormulaToCtx_constantHenkinAllImplication_canary
    (Γ : Ctx TestBase)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {σ : Ty TestBase} (φ : Formula TestConst [σ]) :
    weakenClosedFormulaToCtx (Base := TestBase) (Const := TestConst) Γ
        (ClosedTheorySet.constantHenkinAllImplication
          (Base := TestBase) (Const := TestConst) allConst φ) =
      .imp
        (weakenClosedFormulaToCtx (Base := TestBase) (Const := TestConst) Γ
          (instantiate (Base := TestBase) (.const (allConst φ)) φ))
        (weakenClosedFormulaToCtx (Base := TestBase) (Const := TestConst) Γ
          (.all φ : ClosedFormula TestConst)) :=
  ClosedTheorySet.weakenClosedFormulaToCtx_constantHenkinAllImplication
    (Base := TestBase) (Const := TestConst) Γ allConst φ

def henkinWitnessData_of_world_canary
    (W : ClosedTheorySet.World TestConst) :
    ClosedTheorySet.HenkinWitnessData (Const := TestConst) W.carrier :=
  ClosedTheorySet.HenkinWitnessData.of_world (Const := TestConst) W

def constantHenkinWitnessData_to_henkinWitnessData_canary
    {U : ClosedTheorySet TestConst}
    (hConst :
      ClosedTheorySet.ConstantHenkinWitnessData (Const := TestConst) U) :
    ClosedTheorySet.HenkinWitnessData (Const := TestConst) U :=
  hConst.toHenkinWitnessData

def constantHenkinImplicationData_to_constantWitnessData_canary
    {U : ClosedTheorySet TestConst}
    (hClosed : ClosedTheorySet.DeductivelyClosed (Const := TestConst) U)
    (hImp :
      ClosedTheorySet.ConstantHenkinImplicationData (Const := TestConst) U) :
    ClosedTheorySet.ConstantHenkinWitnessData (Const := TestConst) U :=
  hImp.toConstantHenkinWitnessData hClosed

def constantHenkinWitnessDataOfImplications_canary
    {U : ClosedTheorySet TestConst}
    (hClosed : ClosedTheorySet.DeductivelyClosed (Const := TestConst) U)
    (hImp :
      ClosedTheorySet.ConstantHenkinImplicationData (Const := TestConst) U) :
    ClosedTheorySet.ConstantHenkinWitnessData (Const := TestConst) U :=
  ClosedTheorySet.constantHenkinWitnessDataOfImplications
    (Const := TestConst) hClosed hImp

theorem constantHenkinExImplication_mem_theorySet_canary
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {σ : Ty TestBase} (φ : Formula TestConst [σ]) :
    ClosedTheorySet.constantHenkinExImplication
        (Base := TestBase) (Const := TestConst) exConst φ ∈
      ClosedTheorySet.constantHenkinImplicationTheorySet
        (Base := TestBase) (Const := TestConst) exConst allConst :=
  ClosedTheorySet.constantHenkinExImplication_mem_theorySet
    (Base := TestBase) (Const := TestConst) exConst allConst φ

theorem constantHenkinAllImplication_mem_theorySet_canary
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {σ : Ty TestBase} (φ : Formula TestConst [σ]) :
    ClosedTheorySet.constantHenkinAllImplication
        (Base := TestBase) (Const := TestConst) allConst φ ∈
      ClosedTheorySet.constantHenkinImplicationTheorySet
        (Base := TestBase) (Const := TestConst) exConst allConst :=
  ClosedTheorySet.constantHenkinAllImplication_mem_theorySet
    (Base := TestBase) (Const := TestConst) exConst allConst φ

def constantHenkinImplicationData_of_contains_theorySet_canary
    {U : ClosedTheorySet TestConst}
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hContains :
      ∀ {θ : ClosedFormula TestConst},
        θ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
          (Base := TestBase) (Const := TestConst) exConst allConst →
          θ ∈ U) :
    ClosedTheorySet.ConstantHenkinImplicationData (Const := TestConst) U :=
  ClosedTheorySet.constantHenkinImplicationDataOfContainsTheorySet
    (Base := TestBase) (Const := TestConst) exConst allConst hContains

theorem withConstantHenkinImplications_base_mem_canary
    {T : ClosedTheorySet TestConst}
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {θ : ClosedFormula TestConst} (hθ : θ ∈ T) :
    θ ∈ ClosedTheorySet.withConstantHenkinImplications
      (Base := TestBase) (Const := TestConst) T exConst allConst :=
  ClosedTheorySet.mem_withConstantHenkinImplications_of_base
    (Base := TestBase) (Const := TestConst) exConst allConst hθ

theorem withConstantHenkinImplications_implication_mem_canary
    {T : ClosedTheorySet TestConst}
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {θ : ClosedFormula TestConst}
    (hθ :
      θ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
        (Base := TestBase) (Const := TestConst) exConst allConst) :
    θ ∈ ClosedTheorySet.withConstantHenkinImplications
      (Base := TestBase) (Const := TestConst) T exConst allConst :=
  ClosedTheorySet.mem_withConstantHenkinImplications_of_implication
    (Base := TestBase) (Const := TestConst) exConst allConst hθ

theorem contains_constantHenkinImplicationTheorySet_of_withConstantHenkinImplications_canary
    {T U : ClosedTheorySet TestConst}
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hExt :
      ∀ {θ : ClosedFormula TestConst},
        θ ∈ ClosedTheorySet.withConstantHenkinImplications
          (Base := TestBase) (Const := TestConst) T exConst allConst →
          θ ∈ U) :
    ∀ {θ : ClosedFormula TestConst},
      θ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
        (Base := TestBase) (Const := TestConst) exConst allConst →
        θ ∈ U :=
  ClosedTheorySet.contains_constantHenkinImplicationTheorySet_of_withConstantHenkinImplications
    (Base := TestBase) (Const := TestConst) exConst allConst hExt

theorem provable_of_iterImp_provable_canary
    {T : ClosedTheorySet TestConst}
    {Γ : ClosedTheory TestConst} {θ : ClosedFormula TestConst}
    (hImp :
      ClosedTheorySet.Provable (Const := TestConst) T
        (ClosedTheory.iterImp (Const := TestConst) Γ θ))
    (hΓ :
      ∀ ψ, ψ ∈ Γ → ClosedTheorySet.Provable (Const := TestConst) T ψ) :
    ClosedTheorySet.Provable (Const := TestConst) T θ :=
  ClosedTheorySet.provable_of_iterImp_provable
    (Const := TestConst) hImp hΓ

theorem provable_of_closedTheoryProvable_of_provable_hyps_canary
    {T : ClosedTheorySet TestConst}
    {Γ : ClosedTheory TestConst} {θ : ClosedFormula TestConst}
    (hΓ :
      ∀ ψ, ψ ∈ Γ → ClosedTheorySet.Provable (Const := TestConst) T ψ)
    (hDer : ClosedTheory.Provable (Const := TestConst) Γ θ) :
    ClosedTheorySet.Provable (Const := TestConst) T θ :=
  ClosedTheorySet.provable_of_closedTheoryProvable_of_provable_hyps
    (Const := TestConst) hΓ hDer

theorem split_withConstantHenkinImplications_support_canary
    {T : ClosedTheorySet TestConst}
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {Γ : ClosedTheory TestConst}
    (hΓ :
      ∀ ψ, ψ ∈ Γ →
        ψ ∈ ClosedTheorySet.withConstantHenkinImplications
          (Base := TestBase) (Const := TestConst) T exConst allConst) :
    ∃ ΓBase ΓHenkin : ClosedTheory TestConst,
      (∀ ψ, ψ ∈ ΓBase → ψ ∈ T) ∧
      (∀ ψ, ψ ∈ ΓHenkin →
        ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
          (Base := TestBase) (Const := TestConst) exConst allConst) ∧
      (∀ {ψ : ClosedFormula TestConst}, ψ ∈ Γ → ψ ∈ ΓBase ++ ΓHenkin) :=
  ClosedTheorySet.split_withConstantHenkinImplications_support
    (Base := TestBase) (Const := TestConst) exConst allConst hΓ

theorem provable_withConstantHenkinImplications_iff_exists_split_canary
    {T : ClosedTheorySet TestConst}
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {θ : ClosedFormula TestConst} :
    ClosedTheorySet.Provable (Const := TestConst)
        (ClosedTheorySet.withConstantHenkinImplications
          (Base := TestBase) (Const := TestConst) T exConst allConst)
        θ ↔
      ∃ ΓBase ΓHenkin : ClosedTheory TestConst,
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ T) ∧
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := TestBase) (Const := TestConst) exConst allConst) ∧
        ClosedTheory.Provable (Const := TestConst) (ΓBase ++ ΓHenkin) θ :=
  ClosedTheorySet.provable_withConstantHenkinImplications_iff_exists_split
    (Base := TestBase) (Const := TestConst) exConst allConst

theorem noConstOccurrenceInClosedTheory_nil_canary :
    ClosedTheorySet.NoConstOccurrenceInClosedTheory
      (Const := TestConst) TestConst.a [] :=
  ClosedTheorySet.noConstOccurrenceInClosedTheory_nil
    (Const := TestConst) TestConst.a

theorem noConstOccurrenceInClosedTheory_cons_iff_canary
    (θ : ClosedFormula TestConst) (Γ : ClosedTheory TestConst) :
    ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) TestConst.a (θ :: Γ) ↔
      NoConstOccurrence TestConst.a θ ∧
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := TestConst) TestConst.a Γ :=
  ClosedTheorySet.noConstOccurrenceInClosedTheory_cons_iff
    (Const := TestConst) TestConst.a θ Γ

theorem noConstOccurrenceInClosedTheory_append_iff_canary
    (Γ Δ : ClosedTheory TestConst) :
    ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) TestConst.a (Γ ++ Δ) ↔
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := TestConst) TestConst.a Γ ∧
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := TestConst) TestConst.a Δ :=
  ClosedTheorySet.noConstOccurrenceInClosedTheory_append_iff
    (Const := TestConst) TestConst.a Γ Δ

theorem noConstOccurrenceInClosedTheory_of_subset_canary
    {Γ Δ : ClosedTheory TestConst}
    (hΔ :
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) TestConst.a Δ)
    (hSub : ∀ {θ : ClosedFormula TestConst}, θ ∈ Γ → θ ∈ Δ) :
    ClosedTheorySet.NoConstOccurrenceInClosedTheory
      (Const := TestConst) TestConst.a Γ :=
  ClosedTheorySet.noConstOccurrenceInClosedTheory_of_subset
    (Const := TestConst) hΔ hSub

theorem noConstOccurrenceInClosedTheory_of_mem_set_canary
    {T : ClosedTheorySet TestConst} {Γ : ClosedTheory TestConst}
    (hT :
      ClosedTheorySet.NoConstOccurrenceInClosedTheorySet
        (Const := TestConst) TestConst.a T)
    (hΓ : ∀ {θ : ClosedFormula TestConst}, θ ∈ Γ → θ ∈ T) :
    ClosedTheorySet.NoConstOccurrenceInClosedTheory
      (Const := TestConst) TestConst.a Γ :=
  ClosedTheorySet.noConstOccurrenceInClosedTheory_of_mem_set
    (Const := TestConst) hT hΓ

theorem noSigmaConstOccurrence_mk_iff_canary
    {Γ : Ctx TestBase} {τ : Ty TestBase} (t : Term TestConst Γ τ) :
    ClosedTheorySet.NoSigmaConstOccurrence
        (Const := TestConst) ⟨(.base .atom), TestConst.a⟩ t ↔
      NoConstOccurrence TestConst.a t :=
  ClosedTheorySet.noSigmaConstOccurrence_mk_iff
    (Const := TestConst) TestConst.a t

theorem noSigmaConstOccurrenceInClosedTheory_mk_iff_canary
    (Γ : ClosedTheory TestConst) :
    ClosedTheorySet.NoSigmaConstOccurrenceInClosedTheory
        (Const := TestConst) ⟨(.base .atom), TestConst.a⟩ Γ ↔
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) TestConst.a Γ :=
  ClosedTheorySet.noSigmaConstOccurrenceInClosedTheory_mk_iff
    (Const := TestConst) TestConst.a Γ

theorem noSigmaConstOccurrenceInClosedTheorySet_mk_iff_canary
    (T : ClosedTheorySet TestConst) :
    ClosedTheorySet.NoSigmaConstOccurrenceInClosedTheorySet
        (Const := TestConst) ⟨(.base .atom), TestConst.a⟩ T ↔
      ClosedTheorySet.NoConstOccurrenceInClosedTheorySet
        (Const := TestConst) TestConst.a T :=
  ClosedTheorySet.noSigmaConstOccurrenceInClosedTheorySet_mk_iff
    (Const := TestConst) TestConst.a T

theorem noSigmaConstOccurrenceInClosedTheory_append_iff_canary
    (Γ Δ : ClosedTheory TestConst) :
    ClosedTheorySet.NoSigmaConstOccurrenceInClosedTheory
        (Const := TestConst) ⟨(.base .atom), TestConst.a⟩ (Γ ++ Δ) ↔
      ClosedTheorySet.NoSigmaConstOccurrenceInClosedTheory
          (Const := TestConst) ⟨(.base .atom), TestConst.a⟩ Γ ∧
        ClosedTheorySet.NoSigmaConstOccurrenceInClosedTheory
          (Const := TestConst) ⟨(.base .atom), TestConst.a⟩ Δ :=
  ClosedTheorySet.noSigmaConstOccurrenceInClosedTheory_append_iff
    (Const := TestConst) ⟨(.base .atom), TestConst.a⟩ Γ Δ

theorem extDerivation_weaken_closedTheory_canary
    {Γ : ClosedTheory TestConst} {θ : ClosedFormula TestConst}
    {σ : Ty TestBase}
    (hDer : ClosedTheory.Provable (Const := TestConst) Γ θ) :
    ExtDerivation TestConst
      (weakenHyps (Base := TestBase) (Const := TestConst) (σ := σ) Γ)
      (weaken (Base := TestBase) (Const := TestConst) (σ := σ) θ) :=
  ClosedTheorySet.extDerivation_weaken_closedTheory
    (Base := TestBase) (Const := TestConst) hDer

theorem extDerivation_abstractConstAt_closedTheory_canary
    {Γ : ClosedTheory TestConst} {θ : ClosedFormula TestConst}
    {σ : Ty TestBase} (c : TestConst σ)
    (hDer : ClosedTheory.Provable (Const := TestConst) Γ θ) :
    ExtDerivation TestConst
      (Γ.map (fun ψ =>
        abstractConstAt (Base := TestBase) (Γ := []) (τ := .prop) c [] ψ))
      (abstractConstAt (Base := TestBase) (Γ := []) (τ := .prop) c [] θ) :=
  ClosedTheorySet.extDerivation_abstractConstAt_closedTheory
    (Base := TestBase) (Const := TestConst) c hDer

theorem abstractConstAt_closedTheory_eq_weakenHyps_canary
    {σ : Ty TestBase} (c : TestConst σ)
    {Γ : ClosedTheory TestConst}
    (hΓno :
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) c Γ) :
    Γ.map (fun ψ =>
        abstractConstAt (Base := TestBase) (Γ := []) (τ := .prop) c [] ψ) =
      weakenHyps (Base := TestBase) (Const := TestConst) (σ := σ) Γ :=
  ClosedTheorySet.abstractConstAt_closedTheory_eq_weakenHyps
    (Base := TestBase) (Const := TestConst) c hΓno

theorem extDerivation_abstractConstAt_weaken_of_noOccurrence_canary
    {Γ : ClosedTheory TestConst} {θ : ClosedFormula TestConst}
    {σ : Ty TestBase} {c : TestConst σ}
    (hΓno :
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) c Γ)
    (hθno : NoConstOccurrence c θ)
    (hDer : ClosedTheory.Provable (Const := TestConst) Γ θ) :
    ExtDerivation TestConst
      (weakenHyps (Base := TestBase) (Const := TestConst) (σ := σ) Γ)
      (weaken (Base := TestBase) (Const := TestConst) (σ := σ) θ) :=
  ClosedTheorySet.extDerivation_abstractConstAt_weaken_of_noOccurrence
    (Base := TestBase) (Const := TestConst) hΓno hθno hDer

theorem closedTheoryProvable_all_of_const_instance_append_canary
    {ΓBase ΓTail : ClosedTheory TestConst}
    {σ : Ty TestBase} {φ : Formula TestConst [σ]} {c : TestConst σ}
    (hBaseNo :
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) c ΓBase)
    (hTailNo :
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) c ΓTail)
    (hφno : NoConstOccurrence c φ)
    (hInst : ClosedTheory.Provable (Const := TestConst) (ΓBase ++ ΓTail)
      (instantiate (Base := TestBase) (.const c) φ)) :
    ClosedTheory.Provable (Const := TestConst) (ΓBase ++ ΓTail) (.all φ) :=
  ClosedTheorySet.closedTheoryProvable_all_of_const_instance_append
    (Base := TestBase) (Const := TestConst)
    hBaseNo hTailNo hφno hInst

theorem closedTheoryProvable_all_of_freshHenkinAllAntecedent_canary
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {ΓBase ΓTail : ClosedTheory TestConst}
    {σ : Ty TestBase} (φ : Formula TestConst [σ])
    (hBaseNo :
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) (allConst φ) ΓBase)
    (hTailNo :
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) (allConst φ) ΓTail)
    (hφno : NoConstOccurrence (allConst φ) φ)
    (hInst : ClosedTheory.Provable (Const := TestConst) (ΓBase ++ ΓTail)
      (instantiate (Base := TestBase) (.const (allConst φ)) φ)) :
    ClosedTheory.Provable (Const := TestConst) (ΓBase ++ ΓTail) (.all φ) :=
  ClosedTheorySet.closedTheoryProvable_all_of_freshHenkinAllAntecedent
    (Base := TestBase) (Const := TestConst)
    allConst φ hBaseNo hTailNo hφno hInst

theorem closedTheoryProvable_exImplication_of_instance_noConstOccurrence_canary
    {σ : Ty TestBase} {φ : Formula TestConst [σ]} {c : TestConst σ}
    (hInstNo :
      NoConstOccurrence c (instantiate (Base := TestBase) (.const c) φ)) :
    ClosedTheory.Provable (Const := TestConst) []
      (.imp (.ex φ : ClosedFormula TestConst)
        (instantiate (Base := TestBase) (.const c) φ)) :=
  ClosedTheorySet.closedTheoryProvable_exImplication_of_instance_noConstOccurrence
    (Base := TestBase) (Const := TestConst) hInstNo

theorem closedTheoryProvable_allImplication_of_instance_noConstOccurrence_canary
    {σ : Ty TestBase} {φ : Formula TestConst [σ]} {c : TestConst σ}
    (hInstNo :
      NoConstOccurrence c (instantiate (Base := TestBase) (.const c) φ)) :
    ClosedTheory.Provable (Const := TestConst) []
      (.imp (instantiate (Base := TestBase) (.const c) φ)
        (.all φ : ClosedFormula TestConst)) :=
  ClosedTheorySet.closedTheoryProvable_allImplication_of_instance_noConstOccurrence
    (Base := TestBase) (Const := TestConst) hInstNo

theorem closedTheoryProvable_constantHenkinExImplication_of_instance_noConstOccurrence_canary
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {σ : Ty TestBase} (φ : Formula TestConst [σ])
    (hInstNo :
      NoConstOccurrence (exConst φ)
        (instantiate (Base := TestBase) (.const (exConst φ)) φ)) :
    ClosedTheory.Provable (Const := TestConst) []
      (ClosedTheorySet.constantHenkinExImplication
        (Base := TestBase) (Const := TestConst) exConst φ) :=
  ClosedTheorySet.closedTheoryProvable_constantHenkinExImplication_of_instance_noConstOccurrence
    (Base := TestBase) (Const := TestConst) exConst φ hInstNo

theorem closedTheoryProvable_constantHenkinAllImplication_of_instance_noConstOccurrence_canary
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {σ : Ty TestBase} (φ : Formula TestConst [σ])
    (hInstNo :
      NoConstOccurrence (allConst φ)
        (instantiate (Base := TestBase) (.const (allConst φ)) φ)) :
    ClosedTheory.Provable (Const := TestConst) []
      (ClosedTheorySet.constantHenkinAllImplication
        (Base := TestBase) (Const := TestConst) allConst φ) :=
  ClosedTheorySet.closedTheoryProvable_constantHenkinAllImplication_of_instance_noConstOccurrence
    (Base := TestBase) (Const := TestConst) allConst φ hInstNo

theorem extDerivation_cons_append_of_append_cons_canary
    {Γ : Ctx TestBase}
    {ΓHead ΓTail : List (Formula TestConst Γ)}
    {χ θ : Formula TestConst Γ}
    (hDer : ExtDerivation TestConst (ΓHead ++ χ :: ΓTail) θ) :
    ExtDerivation TestConst (χ :: ΓHead ++ ΓTail) θ :=
  ExtDerivation.cons_append_of_append_cons
    (Base := TestBase) (Const := TestConst) hDer

theorem extDerivation_append_cons_of_cons_append_canary
    {Γ : Ctx TestBase}
    {ΓHead ΓTail : List (Formula TestConst Γ)}
    {χ θ : Formula TestConst Γ}
    (hDer : ExtDerivation TestConst (χ :: ΓHead ++ ΓTail) θ) :
    ExtDerivation TestConst (ΓHead ++ χ :: ΓTail) θ :=
  ExtDerivation.append_cons_of_cons_append
    (Base := TestBase) (Const := TestConst) hDer

theorem closedTheoryProvable_cons_append_of_append_cons_canary
    {ΓHead ΓTail : ClosedTheory TestConst}
    {χ θ : ClosedFormula TestConst}
    (hDer : ClosedTheory.Provable (Const := TestConst) (ΓHead ++ χ :: ΓTail) θ) :
    ClosedTheory.Provable (Const := TestConst) (χ :: ΓHead ++ ΓTail) θ :=
  ClosedTheorySet.closedTheoryProvable_cons_append_of_append_cons
    (Base := TestBase) (Const := TestConst) hDer

theorem closedTheoryProvable_append_cons_of_cons_append_canary
    {ΓHead ΓTail : ClosedTheory TestConst}
    {χ θ : ClosedFormula TestConst}
    (hDer : ClosedTheory.Provable (Const := TestConst) (χ :: ΓHead ++ ΓTail) θ) :
    ClosedTheory.Provable (Const := TestConst) (ΓHead ++ χ :: ΓTail) θ :=
  ClosedTheorySet.closedTheoryProvable_append_cons_of_cons_append
    (Base := TestBase) (Const := TestConst) hDer

theorem closedTheoryProvable_of_exists_of_fresh_instance_assumption_canary
    {Γ : ClosedTheory TestConst}
    {σ : Ty TestBase} {φ : Formula TestConst [σ]} {c : TestConst σ}
    {θ : ClosedFormula TestConst}
    (hΓno :
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) c Γ)
    (hφno : NoConstOccurrence c φ)
    (hθno : NoConstOccurrence c θ)
    (hDer : ClosedTheory.Provable (Const := TestConst)
      (instantiate (Base := TestBase) (.const c) φ :: Γ) θ) :
    ClosedTheory.Provable (Const := TestConst) ((.ex φ : ClosedFormula TestConst) :: Γ) θ :=
  ClosedTheorySet.closedTheoryProvable_of_exists_of_fresh_instance_assumption
    (Base := TestBase) (Const := TestConst)
    hΓno hφno hθno hDer

theorem closedTheoryProvable_of_fresh_ex_principal_cut_canary
    {Γ : ClosedTheory TestConst}
    {σ : Ty TestBase} {φ : Formula TestConst [σ]} {c : TestConst σ}
    {θ : ClosedFormula TestConst}
    (hΓno :
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) c Γ)
    (hφno : NoConstOccurrence c φ)
    (hθno : NoConstOccurrence c θ)
    (hEx : ClosedTheory.Provable (Const := TestConst) Γ (.ex φ : ClosedFormula TestConst))
    (hUse : ClosedTheory.Provable (Const := TestConst)
      (instantiate (Base := TestBase) (.const c) φ :: Γ) θ) :
    ClosedTheory.Provable (Const := TestConst) Γ θ :=
  ClosedTheorySet.closedTheoryProvable_of_fresh_ex_principal_cut
    (Base := TestBase) (Const := TestConst)
    hΓno hφno hθno hEx hUse

theorem closedTheoryProvable_of_fresh_ex_principal_cut_append_canary
    {ΓBase ΓTail : ClosedTheory TestConst}
    {σ : Ty TestBase} {φ : Formula TestConst [σ]} {c : TestConst σ}
    {θ : ClosedFormula TestConst}
    (hBaseNo :
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) c ΓBase)
    (hTailNo :
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) c ΓTail)
    (hφno : NoConstOccurrence c φ)
    (hθno : NoConstOccurrence c θ)
    (hEx : ClosedTheory.Provable (Const := TestConst)
      (ΓBase ++ ΓTail) (.ex φ : ClosedFormula TestConst))
    (hUse : ClosedTheory.Provable (Const := TestConst)
      (ΓBase ++ instantiate (Base := TestBase) (.const c) φ :: ΓTail) θ) :
    ClosedTheory.Provable (Const := TestConst) (ΓBase ++ ΓTail) θ :=
  ClosedTheorySet.closedTheoryProvable_of_fresh_ex_principal_cut_append
    (Base := TestBase) (Const := TestConst)
    hBaseNo hTailNo hφno hθno hEx hUse

theorem closedTheoryProvable_of_fresh_ex_principal_cut_derivable_append_canary
    {ΓBase ΓTail : ClosedTheory TestConst}
    {σ : Ty TestBase} {φ : Formula TestConst [σ]} {c : TestConst σ}
    {θ : ClosedFormula TestConst}
    (hBaseNo :
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) c ΓBase)
    (hTailNo :
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) c ΓTail)
    (hφno : NoConstOccurrence c φ)
    (hθno : NoConstOccurrence c θ)
    (hEx : Derivable (Base := TestBase) (Const := TestConst)
      (ΓBase ++ ΓTail) (.ex φ : ClosedFormula TestConst))
    (hUse : Derivable (Base := TestBase) (Const := TestConst)
      (ΓBase ++ instantiate (Base := TestBase) (.const c) φ :: ΓTail) θ) :
    ClosedTheory.Provable (Const := TestConst) (ΓBase ++ ΓTail) θ :=
  ClosedTheorySet.closedTheoryProvable_of_fresh_ex_principal_cut_derivable_append
    (Base := TestBase) (Const := TestConst)
    hBaseNo hTailNo hφno hθno hEx hUse

theorem closedTheoryProvable_of_fresh_all_principal_cut_canary
    {Γ : ClosedTheory TestConst}
    {σ : Ty TestBase} {φ : Formula TestConst [σ]} {c : TestConst σ}
    {θ : ClosedFormula TestConst}
    (hΓno :
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) c Γ)
    (hφno : NoConstOccurrence c φ)
    (hInst : ClosedTheory.Provable (Const := TestConst) Γ
      (instantiate (Base := TestBase) (.const c) φ))
    (hUse : ClosedTheory.Provable (Const := TestConst)
      ((.all φ : ClosedFormula TestConst) :: Γ) θ) :
    ClosedTheory.Provable (Const := TestConst) Γ θ :=
  ClosedTheorySet.closedTheoryProvable_of_fresh_all_principal_cut
    (Base := TestBase) (Const := TestConst)
    hΓno hφno hInst hUse

theorem closedTheoryProvable_of_fresh_all_principal_cut_append_canary
    {ΓBase ΓTail : ClosedTheory TestConst}
    {σ : Ty TestBase} {φ : Formula TestConst [σ]} {c : TestConst σ}
    {θ : ClosedFormula TestConst}
    (hBaseNo :
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) c ΓBase)
    (hTailNo :
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) c ΓTail)
    (hφno : NoConstOccurrence c φ)
    (hInst : ClosedTheory.Provable (Const := TestConst) (ΓBase ++ ΓTail)
      (instantiate (Base := TestBase) (.const c) φ))
    (hUse : ClosedTheory.Provable (Const := TestConst)
      (ΓBase ++ (.all φ : ClosedFormula TestConst) :: ΓTail) θ) :
    ClosedTheory.Provable (Const := TestConst) (ΓBase ++ ΓTail) θ :=
  ClosedTheorySet.closedTheoryProvable_of_fresh_all_principal_cut_append
    (Base := TestBase) (Const := TestConst)
    hBaseNo hTailNo hφno hInst hUse

theorem closedTheoryProvable_of_fresh_all_principal_cut_derivable_append_canary
    {ΓBase ΓTail : ClosedTheory TestConst}
    {σ : Ty TestBase} {φ : Formula TestConst [σ]} {c : TestConst σ}
    {θ : ClosedFormula TestConst}
    (hBaseNo :
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) c ΓBase)
    (hTailNo :
      ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := TestConst) c ΓTail)
    (hφno : NoConstOccurrence c φ)
    (hInst : Derivable (Base := TestBase) (Const := TestConst)
      (ΓBase ++ ΓTail) (instantiate (Base := TestBase) (.const c) φ))
    (hUse : Derivable (Base := TestBase) (Const := TestConst)
      (ΓBase ++ (.all φ : ClosedFormula TestConst) :: ΓTail) θ) :
    ClosedTheory.Provable (Const := TestConst) (ΓBase ++ ΓTail) θ :=
  ClosedTheorySet.closedTheoryProvable_of_fresh_all_principal_cut_derivable_append
    (Base := TestBase) (Const := TestConst)
    hBaseNo hTailNo hφno hInst hUse

theorem not_noConstOccurrence_self_const_canary :
    ¬ NoConstOccurrence TestConst.a
      ((.const TestConst.a : ClosedTerm TestConst (.base .atom))) := by
  intro h
  cases h with
  | const_diff_type hne _ =>
      exact hne rfl
  | const_same_ne _ hne =>
      exact hne rfl

def constantHenkinImplicationShape_selected_canary
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {θ : ClosedFormula TestConst}
    (hθ :
      ClosedTheorySet.ConstantHenkinImplicationShape
        (Base := TestBase) (Const := TestConst) exConst allConst θ) :
    Sigma TestConst :=
  hθ.selected

theorem constantHenkinImplication_mem_of_shape_canary
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {θ : ClosedFormula TestConst}
    (hθ :
      ClosedTheorySet.ConstantHenkinImplicationShape
        (Base := TestBase) (Const := TestConst) exConst allConst θ) :
    θ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
      (Base := TestBase) (Const := TestConst) exConst allConst :=
  ClosedTheorySet.constantHenkinImplication_mem_of_shape
    (Base := TestBase) (Const := TestConst) exConst allConst hθ

def freshConstantHenkinImplicationShape_to_shape_canary
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {θ : ClosedFormula TestConst}
    (hθ :
      ClosedTheorySet.FreshConstantHenkinImplicationShape
        (Base := TestBase) (Const := TestConst) exConst allConst θ) :
    ClosedTheorySet.ConstantHenkinImplicationShape
      (Base := TestBase) (Const := TestConst) exConst allConst θ :=
  hθ.toShape

def freshConstantHenkinImplicationShape_selected_canary
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {θ : ClosedFormula TestConst}
    (hθ :
      ClosedTheorySet.FreshConstantHenkinImplicationShape
        (Base := TestBase) (Const := TestConst) exConst allConst θ) :
    Sigma TestConst :=
  hθ.selected

theorem freshConstantHenkinImplicationShape_toMem_canary
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {θ : ClosedFormula TestConst}
    (hθ :
      ClosedTheorySet.FreshConstantHenkinImplicationShape
        (Base := TestBase) (Const := TestConst) exConst allConst θ) :
    θ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
      (Base := TestBase) (Const := TestConst) exConst allConst :=
  hθ.toMem

theorem freshConstantHenkinImplicationShape_sourceNoOccurrence_canary
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {θ : ClosedFormula TestConst}
    (hθ :
      ClosedTheorySet.FreshConstantHenkinImplicationShape
        (Base := TestBase) (Const := TestConst) exConst allConst θ) :
    (∃ (σ : Ty TestBase) (φ : Formula TestConst [σ]),
      θ = ClosedTheorySet.constantHenkinExImplication
          (Base := TestBase) (Const := TestConst) exConst φ ∧
      hθ.selected = ⟨σ, exConst φ⟩ ∧
      NoConstOccurrence (exConst φ) φ) ∨
    (∃ (σ : Ty TestBase) (φ : Formula TestConst [σ]),
      θ = ClosedTheorySet.constantHenkinAllImplication
          (Base := TestBase) (Const := TestConst) allConst φ ∧
      hθ.selected = ⟨σ, allConst φ⟩ ∧
      NoConstOccurrence (allConst φ) φ) :=
  hθ.sourceNoOccurrence

def freshConstantHenkinImplicationListFor_canary
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (ΓBase ΓHenkin : ClosedTheory TestConst) (θ : ClosedFormula TestConst) :
    Prop :=
  ClosedTheorySet.FreshConstantHenkinImplicationListFor
    (Base := TestBase) (Const := TestConst) exConst allConst ΓBase ΓHenkin θ

def henkinizedAntecedentTheorySet_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ) :
    ClosedTheorySet TestConst :=
  F.henkinizedAntecedentTheorySet
    (Base := TestBase) (Const := TestConst) exConst allConst

theorem antecedent_mem_henkinizedAntecedentTheorySet_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {θ : ClosedFormula TestConst} (hθ : θ ∈ F.antecedents) :
    θ ∈ F.henkinizedAntecedentTheorySet
      (Base := TestBase) (Const := TestConst) exConst allConst :=
  F.antecedent_mem_henkinizedAntecedentTheorySet
    (Base := TestBase) (Const := TestConst) exConst allConst hθ

theorem henkinImplication_mem_henkinizedAntecedentTheorySet_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {θ : ClosedFormula TestConst}
    (hθ :
      θ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
        (Base := TestBase) (Const := TestConst) exConst allConst) :
    θ ∈ F.henkinizedAntecedentTheorySet
      (Base := TestBase) (Const := TestConst) exConst allConst :=
  F.henkinImplication_mem_henkinizedAntecedentTheorySet
    (Base := TestBase) (Const := TestConst) exConst allConst hθ

theorem henkinizedProvable_of_antecedentTheorySetProvable_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    {θ : ClosedFormula TestConst}
    (hθ : ClosedTheorySet.Provable (Const := TestConst) F.antecedentTheorySet θ) :
    ClosedTheorySet.Provable (Const := TestConst)
      (F.henkinizedAntecedentTheorySet
        (Base := TestBase) (Const := TestConst) exConst allConst)
      θ :=
  F.henkinizedProvable_of_antecedentTheorySetProvable
    (Base := TestBase) (Const := TestConst) exConst allConst hθ

def henkinImplicationConservative_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ) :
    Prop :=
  F.HenkinImplicationConservative
    (Base := TestBase) (Const := TestConst) exConst allConst

def finiteHenkinImplicationConservative_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ) :
    Prop :=
  F.FiniteHenkinImplicationConservative
    (Base := TestBase) (Const := TestConst) exConst allConst

def oneStepHenkinImplicationConservative_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ) :
    Prop :=
  F.OneStepHenkinImplicationConservative
    (Base := TestBase) (Const := TestConst) exConst allConst

def freshOneStepHenkinImplicationConservative_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ) :
    Prop :=
  F.FreshOneStepHenkinImplicationConservative
    (Base := TestBase) (Const := TestConst) exConst allConst

def freshFiniteHenkinImplicationConservative_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ) :
    Prop :=
  F.FreshFiniteHenkinImplicationConservative
    (Base := TestBase) (Const := TestConst) exConst allConst

def henkinImplicationOneStepFreshness_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ) :
    Prop :=
  F.HenkinImplicationOneStepFreshness
    (Base := TestBase) (Const := TestConst) exConst allConst

theorem freshOneStepHenkinImplicationConservative_of_branch_cases_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hEx :
      ∀ {θ : ClosedFormula TestConst} {ΓBase ΓHenkin : ClosedTheory TestConst}
        {σ : Ty TestBase} (φ : Formula TestConst [σ]),
        NoConstOccurrence (exConst φ) φ →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := TestConst) (exConst φ) ΓBase →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := TestConst) (exConst φ) ΓHenkin →
        NoConstOccurrence (exConst φ) θ →
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := TestBase) (Const := TestConst) exConst allConst) →
        ClosedTheory.Provable (Const := TestConst)
          (ΓBase ++
            ClosedTheorySet.constantHenkinExImplication
              (Base := TestBase) (Const := TestConst) exConst φ :: ΓHenkin) θ →
        ClosedTheory.Provable (Const := TestConst) (ΓBase ++ ΓHenkin) θ)
    (hAll :
      ∀ {θ : ClosedFormula TestConst} {ΓBase ΓHenkin : ClosedTheory TestConst}
        {σ : Ty TestBase} (φ : Formula TestConst [σ]),
        NoConstOccurrence (allConst φ) φ →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := TestConst) (allConst φ) ΓBase →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := TestConst) (allConst φ) ΓHenkin →
        NoConstOccurrence (allConst φ) θ →
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := TestBase) (Const := TestConst) exConst allConst) →
        ClosedTheory.Provable (Const := TestConst)
          (ΓBase ++
            ClosedTheorySet.constantHenkinAllImplication
              (Base := TestBase) (Const := TestConst) allConst φ :: ΓHenkin) θ →
        ClosedTheory.Provable (Const := TestConst) (ΓBase ++ ΓHenkin) θ) :
    F.FreshOneStepHenkinImplicationConservative
      (Base := TestBase) (Const := TestConst) exConst allConst :=
  F.freshOneStepHenkinImplicationConservative_of_branch_cases
    (Base := TestBase) (Const := TestConst) exConst allConst hEx hAll

theorem closedTheoryProvable_withoutHenkin_of_oneStepHenkinImplicationConservative_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hStep :
      F.OneStepHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst)
    {θ : ClosedFormula TestConst} {ΓBase ΓHenkin : ClosedTheory TestConst}
    (hBase : ∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents)
    (hHenkin :
      ∀ ψ, ψ ∈ ΓHenkin →
        ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
          (Base := TestBase) (Const := TestConst) exConst allConst)
    (hDer : ClosedTheory.Provable (Const := TestConst) (ΓBase ++ ΓHenkin) θ) :
    ClosedTheory.Provable (Const := TestConst) ΓBase θ :=
  F.closedTheoryProvable_withoutHenkin_of_oneStepHenkinImplicationConservative
    (Base := TestBase) (Const := TestConst) exConst allConst
    hStep hBase hHenkin hDer

theorem closedTheoryProvable_withoutFreshHenkin_of_freshOneStepHenkinImplicationConservative_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hStep :
      F.FreshOneStepHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst)
    {θ : ClosedFormula TestConst} {ΓBase ΓHenkin : ClosedTheory TestConst}
    (hBase : ∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents)
    (hHenkin :
      ∀ ψ, ψ ∈ ΓHenkin →
        ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
          (Base := TestBase) (Const := TestConst) exConst allConst)
    (hFresh :
      ClosedTheorySet.FreshConstantHenkinImplicationListFor
        (Base := TestBase) (Const := TestConst) exConst allConst ΓBase ΓHenkin θ)
    (hDer : ClosedTheory.Provable (Const := TestConst) (ΓBase ++ ΓHenkin) θ) :
    ClosedTheory.Provable (Const := TestConst) ΓBase θ :=
  F.closedTheoryProvable_withoutFreshHenkin_of_freshOneStepHenkinImplicationConservative
    (Base := TestBase) (Const := TestConst) exConst allConst
    hStep hBase hHenkin hFresh hDer

theorem finiteHenkinImplicationConservative_of_oneStep_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hStep :
      F.OneStepHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst) :
    F.FiniteHenkinImplicationConservative
      (Base := TestBase) (Const := TestConst) exConst allConst :=
  F.finiteHenkinImplicationConservative_of_oneStep
    (Base := TestBase) (Const := TestConst) exConst allConst hStep

theorem freshFiniteHenkinImplicationConservative_of_freshOneStep_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hStep :
      F.FreshOneStepHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst) :
    F.FreshFiniteHenkinImplicationConservative
      (Base := TestBase) (Const := TestConst) exConst allConst :=
  F.freshFiniteHenkinImplicationConservative_of_freshOneStep
    (Base := TestBase) (Const := TestConst) exConst allConst hStep

theorem oneStepHenkinImplicationConservative_of_freshOneStep_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hStep :
      F.FreshOneStepHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst)
    (hFresh :
      F.HenkinImplicationOneStepFreshness
        (Base := TestBase) (Const := TestConst) exConst allConst) :
    F.OneStepHenkinImplicationConservative
      (Base := TestBase) (Const := TestConst) exConst allConst :=
  F.oneStepHenkinImplicationConservative_of_freshOneStep
    (Base := TestBase) (Const := TestConst) exConst allConst hStep hFresh

theorem henkinImplicationOneStepFreshness_of_listFreshness_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hFreshList :
      ∀ {θ : ClosedFormula TestConst} {ΓBase ΓHenkin : ClosedTheory TestConst},
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := TestBase) (Const := TestConst) exConst allConst) →
        ClosedTheorySet.FreshConstantHenkinImplicationListFor
          (Base := TestBase) (Const := TestConst) exConst allConst ΓBase ΓHenkin θ) :
    F.HenkinImplicationOneStepFreshness
      (Base := TestBase) (Const := TestConst) exConst allConst :=
  F.henkinImplicationOneStepFreshness_of_listFreshness
    (Base := TestBase) (Const := TestConst) exConst allConst hFreshList

theorem finiteHenkinImplicationConservative_of_freshOneStep_listFreshness_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hStep :
      F.FreshOneStepHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst)
    (hFreshList :
      ∀ {θ : ClosedFormula TestConst} {ΓBase ΓHenkin : ClosedTheory TestConst},
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := TestBase) (Const := TestConst) exConst allConst) →
        ClosedTheorySet.FreshConstantHenkinImplicationListFor
          (Base := TestBase) (Const := TestConst) exConst allConst ΓBase ΓHenkin θ) :
    F.FiniteHenkinImplicationConservative
      (Base := TestBase) (Const := TestConst) exConst allConst :=
  F.finiteHenkinImplicationConservative_of_freshOneStep_listFreshness
    (Base := TestBase) (Const := TestConst) exConst allConst hStep hFreshList

theorem henkinImplicationConservative_of_freshOneStep_listFreshness_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hStep :
      F.FreshOneStepHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst)
    (hFreshList :
      ∀ {θ : ClosedFormula TestConst} {ΓBase ΓHenkin : ClosedTheory TestConst},
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := TestBase) (Const := TestConst) exConst allConst) →
        ClosedTheorySet.FreshConstantHenkinImplicationListFor
          (Base := TestBase) (Const := TestConst) exConst allConst ΓBase ΓHenkin θ) :
    F.HenkinImplicationConservative
      (Base := TestBase) (Const := TestConst) exConst allConst :=
  F.henkinImplicationConservative_of_freshOneStep_listFreshness
    (Base := TestBase) (Const := TestConst) exConst allConst hStep hFreshList

theorem finiteHenkinImplicationConservative_of_branch_cases_and_listFreshness_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hEx :
      ∀ {θ : ClosedFormula TestConst} {ΓBase ΓHenkin : ClosedTheory TestConst}
        {σ : Ty TestBase} (φ : Formula TestConst [σ]),
        NoConstOccurrence (exConst φ) φ →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := TestConst) (exConst φ) ΓBase →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := TestConst) (exConst φ) ΓHenkin →
        NoConstOccurrence (exConst φ) θ →
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := TestBase) (Const := TestConst) exConst allConst) →
        ClosedTheory.Provable (Const := TestConst)
          (ΓBase ++
            ClosedTheorySet.constantHenkinExImplication
              (Base := TestBase) (Const := TestConst) exConst φ :: ΓHenkin) θ →
        ClosedTheory.Provable (Const := TestConst) (ΓBase ++ ΓHenkin) θ)
    (hAll :
      ∀ {θ : ClosedFormula TestConst} {ΓBase ΓHenkin : ClosedTheory TestConst}
        {σ : Ty TestBase} (φ : Formula TestConst [σ]),
        NoConstOccurrence (allConst φ) φ →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := TestConst) (allConst φ) ΓBase →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := TestConst) (allConst φ) ΓHenkin →
        NoConstOccurrence (allConst φ) θ →
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := TestBase) (Const := TestConst) exConst allConst) →
        ClosedTheory.Provable (Const := TestConst)
          (ΓBase ++
            ClosedTheorySet.constantHenkinAllImplication
              (Base := TestBase) (Const := TestConst) allConst φ :: ΓHenkin) θ →
        ClosedTheory.Provable (Const := TestConst) (ΓBase ++ ΓHenkin) θ)
    (hFreshList :
      ∀ {θ : ClosedFormula TestConst} {ΓBase ΓHenkin : ClosedTheory TestConst},
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := TestBase) (Const := TestConst) exConst allConst) →
        ClosedTheorySet.FreshConstantHenkinImplicationListFor
          (Base := TestBase) (Const := TestConst) exConst allConst ΓBase ΓHenkin θ) :
    F.FiniteHenkinImplicationConservative
      (Base := TestBase) (Const := TestConst) exConst allConst :=
  F.finiteHenkinImplicationConservative_of_branch_cases_and_listFreshness
    (Base := TestBase) (Const := TestConst) exConst allConst hEx hAll hFreshList

theorem henkinImplicationConservative_of_branch_cases_and_listFreshness_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hEx :
      ∀ {θ : ClosedFormula TestConst} {ΓBase ΓHenkin : ClosedTheory TestConst}
        {σ : Ty TestBase} (φ : Formula TestConst [σ]),
        NoConstOccurrence (exConst φ) φ →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := TestConst) (exConst φ) ΓBase →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := TestConst) (exConst φ) ΓHenkin →
        NoConstOccurrence (exConst φ) θ →
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := TestBase) (Const := TestConst) exConst allConst) →
        ClosedTheory.Provable (Const := TestConst)
          (ΓBase ++
            ClosedTheorySet.constantHenkinExImplication
              (Base := TestBase) (Const := TestConst) exConst φ :: ΓHenkin) θ →
        ClosedTheory.Provable (Const := TestConst) (ΓBase ++ ΓHenkin) θ)
    (hAll :
      ∀ {θ : ClosedFormula TestConst} {ΓBase ΓHenkin : ClosedTheory TestConst}
        {σ : Ty TestBase} (φ : Formula TestConst [σ]),
        NoConstOccurrence (allConst φ) φ →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := TestConst) (allConst φ) ΓBase →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := TestConst) (allConst φ) ΓHenkin →
        NoConstOccurrence (allConst φ) θ →
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := TestBase) (Const := TestConst) exConst allConst) →
        ClosedTheory.Provable (Const := TestConst)
          (ΓBase ++
            ClosedTheorySet.constantHenkinAllImplication
              (Base := TestBase) (Const := TestConst) allConst φ :: ΓHenkin) θ →
        ClosedTheory.Provable (Const := TestConst) (ΓBase ++ ΓHenkin) θ)
    (hFreshList :
      ∀ {θ : ClosedFormula TestConst} {ΓBase ΓHenkin : ClosedTheory TestConst},
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := TestBase) (Const := TestConst) exConst allConst) →
        ClosedTheorySet.FreshConstantHenkinImplicationListFor
          (Base := TestBase) (Const := TestConst) exConst allConst ΓBase ΓHenkin θ) :
    F.HenkinImplicationConservative
      (Base := TestBase) (Const := TestConst) exConst allConst :=
  F.henkinImplicationConservative_of_branch_cases_and_listFreshness
    (Base := TestBase) (Const := TestConst) exConst allConst hEx hAll hFreshList

theorem henkinImplicationConservative_iff_finite_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ) :
    F.HenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst ↔
      F.FiniteHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst :=
  F.henkinImplicationConservative_iff_finite
    (Base := TestBase) (Const := TestConst) exConst allConst

theorem henkinImplicationConservative_of_finite_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hFinite :
      F.FiniteHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst) :
    F.HenkinImplicationConservative
      (Base := TestBase) (Const := TestConst) exConst allConst :=
  F.henkinImplicationConservative_of_finite
    (Base := TestBase) (Const := TestConst) exConst allConst hFinite

theorem henkinImplicationConservative_of_oneStep_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hStep :
      F.OneStepHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst) :
    F.HenkinImplicationConservative
      (Base := TestBase) (Const := TestConst) exConst allConst :=
  F.henkinImplicationConservative_of_oneStep
    (Base := TestBase) (Const := TestConst) exConst allConst hStep

theorem henkinImplicationConservative_of_freshOneStep_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hStep :
      F.FreshOneStepHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst)
    (hFresh :
      F.HenkinImplicationOneStepFreshness
        (Base := TestBase) (Const := TestConst) exConst allConst) :
    F.HenkinImplicationConservative
      (Base := TestBase) (Const := TestConst) exConst allConst :=
  F.henkinImplicationConservative_of_freshOneStep
    (Base := TestBase) (Const := TestConst) exConst allConst hStep hFresh

theorem henkinImplicationConservative_of_implicationsProvable_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hImp :
      ∀ {θ : ClosedFormula TestConst},
        θ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
          (Base := TestBase) (Const := TestConst) exConst allConst →
        ClosedTheorySet.Provable (Const := TestConst) F.antecedentTheorySet θ) :
    F.HenkinImplicationConservative
      (Base := TestBase) (Const := TestConst) exConst allConst :=
  F.henkinImplicationConservative_of_implicationsProvable
    (Base := TestBase) (Const := TestConst) exConst allConst hImp

theorem not_henkinizedProvable_of_not_antecedentTheorySetProvable_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hCons : F.HenkinImplicationConservative
      (Base := TestBase) (Const := TestConst) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := TestConst)
        F.antecedentTheorySet F.succedent) :
    ¬ ClosedTheorySet.Provable (Const := TestConst)
      (F.henkinizedAntecedentTheorySet
        (Base := TestBase) (Const := TestConst) exConst allConst)
      F.succedent :=
  F.not_henkinizedProvable_of_not_antecedentTheorySetProvable
    (Base := TestBase) (Const := TestConst) exConst allConst hCons hNot

def world_of_primeSeparatingExtension_henkin_canary
    {F : CompletenessFrontier TestConst []}
    {U : ClosedTheorySet TestConst}
    (hFU : PrimeSeparatingExtension (Const := TestConst) F U)
    (hWit : ClosedTheorySet.HenkinWitnessData (Const := TestConst) U) :
    ClosedTheorySet.World TestConst :=
  hFU.toWorldOfHenkinWitnessData hWit

theorem world_of_primeSeparatingExtension_henkin_carrier_canary
    {F : CompletenessFrontier TestConst []}
    {U : ClosedTheorySet TestConst}
    (hFU : PrimeSeparatingExtension (Const := TestConst) F U)
    (hWit : ClosedTheorySet.HenkinWitnessData (Const := TestConst) U) :
    (hFU.toWorldOfHenkinWitnessData hWit).carrier = U :=
  PrimeSeparatingExtension.toWorldOfHenkinWitnessData_carrier
    (Base := TestBase) (Const := TestConst) hFU hWit

theorem world_of_primeSeparatingExtension_henkin_contains_antecedent_canary
    {F : CompletenessFrontier TestConst []}
    {U : ClosedTheorySet TestConst}
    (hFU : PrimeSeparatingExtension (Const := TestConst) F U)
    (hWit : ClosedTheorySet.HenkinWitnessData (Const := TestConst) U)
    {φ : ClosedFormula TestConst} (hφ : φ ∈ F.antecedents) :
    φ ∈ (hFU.toWorldOfHenkinWitnessData hWit).carrier :=
  hFU.mem_toWorldOfHenkinWitnessData_of_antecedent hWit hφ

theorem world_of_primeSeparatingExtension_henkin_omits_succedent_canary
    {F : CompletenessFrontier TestConst []}
    {U : ClosedTheorySet TestConst}
    (hFU : PrimeSeparatingExtension (Const := TestConst) F U)
    (hWit : ClosedTheorySet.HenkinWitnessData (Const := TestConst) U) :
    F.succedent ∉ (hFU.toWorldOfHenkinWitnessData hWit).carrier :=
  hFU.succedent_not_mem_toWorldOfHenkinWitnessData hWit

def singletonCountermodel_of_primeSeparatingExtension_henkin_canary
    {F : CompletenessFrontier TestConst []}
    {U : ClosedTheorySet TestConst}
    (hFU : PrimeSeparatingExtension (Const := TestConst) F U)
    (hWit : ClosedTheorySet.HenkinWitnessData (Const := TestConst) U) :
    SingletonWorldModelCounterexample (Const := TestConst) F :=
  singletonWorldModelCounterexampleOfPrimeSeparatingExtensionHenkin
    (Base := TestBase) (Const := TestConst) hFU hWit

theorem not_derivable_of_primeSeparatingExtension_henkin_canary
    {F : CompletenessFrontier TestConst []}
    {U : ClosedTheorySet TestConst}
    (hFU : PrimeSeparatingExtension (Const := TestConst) F U)
    (hWit : ClosedTheorySet.HenkinWitnessData (Const := TestConst) U) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  not_derivable_of_primeSeparatingExtension_henkin
    (Base := TestBase) (Const := TestConst) hFU hWit

theorem not_singletonStrengthConsequence_of_primeSeparatingExtension_henkin_canary
    {F : CompletenessFrontier TestConst []}
    {U : ClosedTheorySet TestConst}
    (hFU : PrimeSeparatingExtension (Const := TestConst) F U)
    (hWit : ClosedTheorySet.HenkinWitnessData (Const := TestConst) U) :
    ¬ SingletonStrengthConsequence (Base := TestBase) (Const := TestConst) F :=
  not_singletonStrengthConsequence_of_primeSeparatingExtension_henkin
    (Base := TestBase) (Const := TestConst) hFU hWit

def primeHenkinSeparatingExtension_toWorld_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeHenkinSeparatingExtension (Const := TestConst) F) :
    ClosedTheorySet.World TestConst :=
  E.toWorld

theorem primeHenkinSeparatingExtension_toWorld_carrier_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeHenkinSeparatingExtension (Const := TestConst) F) :
    E.toWorld.carrier = E.carrier :=
  PrimeHenkinSeparatingExtension.toWorld_carrier
    (Base := TestBase) (Const := TestConst) E

theorem primeHenkinSeparatingExtension_contains_antecedents_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeHenkinSeparatingExtension (Const := TestConst) F)
    {φ : ClosedFormula TestConst} (hφ : φ ∈ F.antecedents) :
    φ ∈ E.toWorld.carrier :=
  E.contains_antecedents hφ

theorem primeHenkinSeparatingExtension_omits_succedent_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeHenkinSeparatingExtension (Const := TestConst) F) :
    F.succedent ∉ E.toWorld.carrier :=
  E.omits_succedent

def primeHenkinSeparatingExtension_singletonCountermodel_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeHenkinSeparatingExtension (Const := TestConst) F) :
    SingletonWorldModelCounterexample (Const := TestConst) F :=
  E.toSingletonWorldModelCounterexample

theorem primeHenkinSeparatingExtension_not_derivable_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeHenkinSeparatingExtension (Const := TestConst) F) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  E.not_derivable

theorem primeHenkinSeparatingExtension_not_singletonStrengthConsequence_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeHenkinSeparatingExtension (Const := TestConst) F) :
    ¬ SingletonStrengthConsequence (Base := TestBase) (Const := TestConst) F :=
  E.not_singletonStrengthConsequence

def primeConstantHenkinSeparatingExtension_toPrimeHenkin_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeConstantHenkinSeparatingExtension (Const := TestConst) F) :
    PrimeHenkinSeparatingExtension (Const := TestConst) F :=
  E.toPrimeHenkinSeparatingExtension

def primeConstantHenkinSeparatingExtension_toWorld_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeConstantHenkinSeparatingExtension (Const := TestConst) F) :
    ClosedTheorySet.World TestConst :=
  E.toWorld

theorem primeConstantHenkinSeparatingExtension_toWorld_carrier_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeConstantHenkinSeparatingExtension (Const := TestConst) F) :
    E.toWorld.carrier = E.carrier :=
  PrimeConstantHenkinSeparatingExtension.toWorld_carrier
    (Base := TestBase) (Const := TestConst) E

def primeConstantHenkinSeparatingExtension_singletonCountermodel_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeConstantHenkinSeparatingExtension (Const := TestConst) F) :
    SingletonWorldModelCounterexample (Const := TestConst) F :=
  E.toSingletonWorldModelCounterexample

theorem primeConstantHenkinSeparatingExtension_not_derivable_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeConstantHenkinSeparatingExtension (Const := TestConst) F) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  E.not_derivable

theorem primeConstantHenkinSeparatingExtension_not_singletonStrengthConsequence_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeConstantHenkinSeparatingExtension (Const := TestConst) F) :
    ¬ SingletonStrengthConsequence (Base := TestBase) (Const := TestConst) F :=
  E.not_singletonStrengthConsequence

def primeHenkinImplicationSeparatingExtension_implicationData_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeHenkinImplicationSeparatingExtension (Const := TestConst) F) :
    ClosedTheorySet.ConstantHenkinImplicationData (Const := TestConst) E.carrier :=
  E.implicationData

def primeHenkinImplicationSeparatingExtension_toPrimeConstantHenkin_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeHenkinImplicationSeparatingExtension (Const := TestConst) F) :
    PrimeConstantHenkinSeparatingExtension (Const := TestConst) F :=
  E.toPrimeConstantHenkinSeparatingExtension

def primeHenkinImplicationSeparatingExtension_toPrimeHenkin_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeHenkinImplicationSeparatingExtension (Const := TestConst) F) :
    PrimeHenkinSeparatingExtension (Const := TestConst) F :=
  E.toPrimeHenkinSeparatingExtension

def primeHenkinImplicationSeparatingExtension_toWorld_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeHenkinImplicationSeparatingExtension (Const := TestConst) F) :
    ClosedTheorySet.World TestConst :=
  E.toWorld

theorem primeHenkinImplicationSeparatingExtension_toWorld_carrier_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeHenkinImplicationSeparatingExtension (Const := TestConst) F) :
    E.toWorld.carrier = E.carrier :=
  PrimeHenkinImplicationSeparatingExtension.toWorld_carrier
    (Base := TestBase) (Const := TestConst) E

def primeHenkinImplicationSeparatingExtension_singletonCountermodel_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeHenkinImplicationSeparatingExtension (Const := TestConst) F) :
    SingletonWorldModelCounterexample (Const := TestConst) F :=
  E.toSingletonWorldModelCounterexample

theorem primeHenkinImplicationSeparatingExtension_not_derivable_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeHenkinImplicationSeparatingExtension (Const := TestConst) F) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  E.not_derivable

theorem primeHenkinImplicationSeparatingExtension_not_singletonStrengthConsequence_canary
    {F : CompletenessFrontier TestConst []}
    (E : PrimeHenkinImplicationSeparatingExtension (Const := TestConst) F) :
    ¬ SingletonStrengthConsequence (Base := TestBase) (Const := TestConst) F :=
  E.not_singletonStrengthConsequence

theorem nonempty_primeHenkinImplicationSeparatingExtension_of_not_henkinizedProvable_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := TestConst)
        (F.henkinizedAntecedentTheorySet
          (Base := TestBase) (Const := TestConst) exConst allConst)
        F.succedent) :
    Nonempty (PrimeHenkinImplicationSeparatingExtension
      (Base := TestBase) (Const := TestConst) F) :=
  F.nonempty_primeHenkinImplicationSeparatingExtension_of_not_henkinizedProvable
    (Base := TestBase) (Const := TestConst) exConst allConst hNot

theorem nonempty_singletonWorldModelCounterexample_of_not_henkinizedProvable_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := TestConst)
        (F.henkinizedAntecedentTheorySet
          (Base := TestBase) (Const := TestConst) exConst allConst)
        F.succedent) :
    Nonempty (SingletonWorldModelCounterexample (Base := TestBase) (Const := TestConst) F) :=
  F.nonempty_singletonWorldModelCounterexample_of_not_henkinizedProvable
    (Base := TestBase) (Const := TestConst) exConst allConst hNot

theorem not_derivable_of_not_henkinizedProvable_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := TestConst)
        (F.henkinizedAntecedentTheorySet
          (Base := TestBase) (Const := TestConst) exConst allConst)
        F.succedent) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  F.not_derivable_of_not_henkinizedProvable
    (Base := TestBase) (Const := TestConst) exConst allConst hNot

theorem not_singletonStrengthConsequence_of_not_henkinizedProvable_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := TestConst)
        (F.henkinizedAntecedentTheorySet
          (Base := TestBase) (Const := TestConst) exConst allConst)
        F.succedent) :
    ¬ SingletonStrengthConsequence (Base := TestBase) (Const := TestConst) F :=
  F.not_singletonStrengthConsequence_of_not_henkinizedProvable
    (Base := TestBase) (Const := TestConst) exConst allConst hNot

theorem nonempty_singletonWorldModelCounterexample_of_not_antecedentTheorySetProvable_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hCons : F.HenkinImplicationConservative
      (Base := TestBase) (Const := TestConst) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := TestConst)
        F.antecedentTheorySet F.succedent) :
    Nonempty (SingletonWorldModelCounterexample (Base := TestBase) (Const := TestConst) F) :=
  F.nonempty_singletonWorldModelCounterexample_of_not_antecedentTheorySetProvable
    (Base := TestBase) (Const := TestConst) exConst allConst hCons hNot

theorem not_derivable_of_not_antecedentTheorySetProvable_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hCons : F.HenkinImplicationConservative
      (Base := TestBase) (Const := TestConst) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := TestConst)
        F.antecedentTheorySet F.succedent) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  F.not_derivable_of_not_antecedentTheorySetProvable
    (Base := TestBase) (Const := TestConst) exConst allConst hCons hNot

theorem not_singletonStrengthConsequence_of_not_antecedentTheorySetProvable_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hCons : F.HenkinImplicationConservative
      (Base := TestBase) (Const := TestConst) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := TestConst)
        F.antecedentTheorySet F.succedent) :
    ¬ SingletonStrengthConsequence (Base := TestBase) (Const := TestConst) F :=
  F.not_singletonStrengthConsequence_of_not_antecedentTheorySetProvable
    (Base := TestBase) (Const := TestConst) exConst allConst hCons hNot

theorem not_henkinizedProvable_of_not_antecedentTheorySetProvable_of_finite_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hFinite :
      F.FiniteHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := TestConst)
        F.antecedentTheorySet F.succedent) :
    ¬ ClosedTheorySet.Provable (Const := TestConst)
      (F.henkinizedAntecedentTheorySet
        (Base := TestBase) (Const := TestConst) exConst allConst)
      F.succedent :=
  F.not_henkinizedProvable_of_not_antecedentTheorySetProvable_of_finite
    (Base := TestBase) (Const := TestConst) exConst allConst hFinite hNot

theorem nonempty_primeHenkinImplicationSeparatingExtension_of_not_antecedentTheorySetProvable_of_finite_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hFinite :
      F.FiniteHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := TestConst)
        F.antecedentTheorySet F.succedent) :
    Nonempty (PrimeHenkinImplicationSeparatingExtension
      (Base := TestBase) (Const := TestConst) F) :=
  F.nonempty_primeHenkinImplicationSeparatingExtension_of_not_antecedentTheorySetProvable_of_finite
    (Base := TestBase) (Const := TestConst) exConst allConst hFinite hNot

theorem nonempty_singletonWorldModelCounterexample_of_not_antecedentTheorySetProvable_of_finite_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hFinite :
      F.FiniteHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := TestConst)
        F.antecedentTheorySet F.succedent) :
    Nonempty (SingletonWorldModelCounterexample (Base := TestBase) (Const := TestConst) F) :=
  F.nonempty_singletonWorldModelCounterexample_of_not_antecedentTheorySetProvable_of_finite
    (Base := TestBase) (Const := TestConst) exConst allConst hFinite hNot

theorem not_henkinizedProvable_of_not_antecedentTheorySetProvable_of_oneStep_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hStep :
      F.OneStepHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := TestConst)
        F.antecedentTheorySet F.succedent) :
    ¬ ClosedTheorySet.Provable (Const := TestConst)
      (F.henkinizedAntecedentTheorySet
        (Base := TestBase) (Const := TestConst) exConst allConst)
      F.succedent :=
  F.not_henkinizedProvable_of_not_antecedentTheorySetProvable_of_oneStep
    (Base := TestBase) (Const := TestConst) exConst allConst hStep hNot

theorem nonempty_primeHenkinImplicationSeparatingExtension_of_not_antecedentTheorySetProvable_of_oneStep_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hStep :
      F.OneStepHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := TestConst)
        F.antecedentTheorySet F.succedent) :
    Nonempty (PrimeHenkinImplicationSeparatingExtension
      (Base := TestBase) (Const := TestConst) F) :=
  F.nonempty_primeHenkinImplicationSeparatingExtension_of_not_antecedentTheorySetProvable_of_oneStep
    (Base := TestBase) (Const := TestConst) exConst allConst hStep hNot

theorem not_derivable_of_not_antecedentTheorySetProvable_of_finite_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hFinite :
      F.FiniteHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := TestConst)
        F.antecedentTheorySet F.succedent) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  F.not_derivable_of_not_antecedentTheorySetProvable_of_finite
    (Base := TestBase) (Const := TestConst) exConst allConst hFinite hNot

theorem not_singletonStrengthConsequence_of_not_antecedentTheorySetProvable_of_finite_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hFinite :
      F.FiniteHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := TestConst)
        F.antecedentTheorySet F.succedent) :
    ¬ SingletonStrengthConsequence (Base := TestBase) (Const := TestConst) F :=
  F.not_singletonStrengthConsequence_of_not_antecedentTheorySetProvable_of_finite
    (Base := TestBase) (Const := TestConst) exConst allConst hFinite hNot

theorem nonempty_singletonWorldModelCounterexample_of_not_antecedentTheorySetProvable_of_oneStep_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hStep :
      F.OneStepHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := TestConst)
        F.antecedentTheorySet F.succedent) :
    Nonempty (SingletonWorldModelCounterexample (Base := TestBase) (Const := TestConst) F) :=
  F.nonempty_singletonWorldModelCounterexample_of_not_antecedentTheorySetProvable_of_oneStep
    (Base := TestBase) (Const := TestConst) exConst allConst hStep hNot

theorem not_derivable_of_not_antecedentTheorySetProvable_of_oneStep_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hStep :
      F.OneStepHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := TestConst)
        F.antecedentTheorySet F.succedent) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  F.not_derivable_of_not_antecedentTheorySetProvable_of_oneStep
    (Base := TestBase) (Const := TestConst) exConst allConst hStep hNot

theorem not_singletonStrengthConsequence_of_not_antecedentTheorySetProvable_of_oneStep_canary
    (F : CompletenessFrontier TestConst [])
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hStep :
      F.OneStepHenkinImplicationConservative
        (Base := TestBase) (Const := TestConst) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := TestConst)
        F.antecedentTheorySet F.succedent) :
    ¬ SingletonStrengthConsequence (Base := TestBase) (Const := TestConst) F :=
  F.not_singletonStrengthConsequence_of_not_antecedentTheorySetProvable_of_oneStep
    (Base := TestBase) (Const := TestConst) exConst allConst hStep hNot

def primeSeparatingExtension_to_primeConstantHenkin_of_implications_canary
    {F : CompletenessFrontier TestConst []}
    {U : ClosedTheorySet TestConst}
    (hFU : PrimeSeparatingExtension (Const := TestConst) F U)
    (hImp :
      ClosedTheorySet.ConstantHenkinImplicationData (Const := TestConst) U) :
    PrimeConstantHenkinSeparatingExtension (Const := TestConst) F :=
  hFU.toPrimeConstantHenkinSeparatingExtensionOfImplications hImp

def primeSeparatingExtension_to_primeConstantHenkin_of_contained_implications_canary
    {F : CompletenessFrontier TestConst []}
    {U : ClosedTheorySet TestConst}
    (hFU : PrimeSeparatingExtension (Const := TestConst) F U)
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hContains :
      ∀ {θ : ClosedFormula TestConst},
        θ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
          (Base := TestBase) (Const := TestConst) exConst allConst →
          θ ∈ U) :
    PrimeConstantHenkinSeparatingExtension (Const := TestConst) F :=
  hFU.toPrimeConstantHenkinSeparatingExtensionOfContainedImplications
    exConst allConst hContains

theorem primeSeparatingExtension_not_derivable_of_implications_canary
    {F : CompletenessFrontier TestConst []}
    {U : ClosedTheorySet TestConst}
    (hFU : PrimeSeparatingExtension (Const := TestConst) F U)
    (hImp :
      ClosedTheorySet.ConstantHenkinImplicationData (Const := TestConst) U) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  (hFU.toPrimeConstantHenkinSeparatingExtensionOfImplications hImp).not_derivable

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermHenkinWorldBridgeRegression
