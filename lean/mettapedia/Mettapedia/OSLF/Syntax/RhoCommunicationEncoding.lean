import Mettapedia.OSLF.Syntax.RhoEquationEncoding
import Mettapedia.OSLF.Syntax.RhoAuthoredDropProfile
import Mettapedia.OSLF.MeTTaIL.InterpretedRuleExtension
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep

/-!
# Chapter 7 communication across intrinsic and authored rho presentations

The intrinsic rule substitutes a quoted payload and leaves `Drop (Quote P)`
as its immediate reduct. The authored COMM interpretation contracts that
round trip during semantic substitution. The two selected COMM reducts are
therefore not structurally congruent, but they are related by the established
process residual equivalence. The separately declared Drop rule makes the
intrinsic reduct executable in the same interpreted authored profile.

These statements compare one closed communication instance and the residual
observations on its reducts. They do not assert a general operational
equivalence between all intrinsic and authored processes.
-/

namespace Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep

set_option autoImplicit false

/-- The open input body used by the closed COMM instance. -/
def boundDropBody : Pattern := .apply "PDrop" [.bvar 0]
def zeroPattern : Pattern := .apply "PZero" []

/-- Input-first spelling of the intrinsic COMM source on the authored carrier. -/
def authoredCommSource : Pattern :=
  .collection .hashBag
    [.apply "PInput" [encodeTerm chan, .lambda none boundDropBody],
     .apply "POutput" [encodeTerm chan, zeroPattern]] none

/-- The immediate reduct computed by interpreted authored COMM. -/
def authoredCommReduct : Pattern :=
  .collection .hashBag [semanticCommSubst boundDropBody zeroPattern] none

/-- The existing authored COMM rule really fires at this closed source. -/
theorem authoredCommStep : RhoStep authoredCommSource authoredCommReduct := by
  apply RhoStep.comm (free := FreeSortContext.empty) (bound := [])
    (encodeTerm chan) boundDropBody zeroPattern []
  · exact ProcWellSorted.drop (NameWellSorted.bvar (by decide))
  · exact ProcWellSorted.unit

/-- The corresponding intrinsic closed instance uses its COMM rule. -/
theorem sourceCommStep :
    rhoSourceWithDrop.StepModE commSource commTarget := by
  apply Presentation.stepModE_of_rule (i := ⟨0, by decide⟩)
  exact stepModE_of_step (E := rhoSourceE)
    (step_of_rootStep comm rho_communicates)

/-- Binary source order and authored input-first order differ only by PAR commutation. -/
theorem encodedSource_structurallyCongruent :
    StructuralCongruence (encodeTerm commSource) authoredCommSource := by
  change StructuralCongruence
    (.collection .hashBag
      [.apply "POutput" [encodeTerm chan, zeroPattern],
       .apply "PInput" [encodeTerm chan, .lambda none boundDropBody]] none)
    (.collection .hashBag
      [.apply "PInput" [encodeTerm chan, .lambda none boundDropBody],
       .apply "POutput" [encodeTerm chan, zeroPattern]] none)
  exact StructuralCongruence.par_comm _ _

theorem authoredCommReduct_is_zero :
    Canonical.canonicalize authoredCommReduct = zeroPattern := by
  decide +kernel

theorem intrinsicCommTarget_is_drop_quote :
    encodeTerm commTarget = .apply "PDrop" [.apply "NQuote" [zeroPattern]] := by
  decide +kernel

/-- Intrinsic substitution produces the author's no-collapse representative. -/
theorem intrinsicTarget_is_noCollapseRepresentative :
    encodeTerm commTarget =
      semanticCommRepresentative boundDropBody zeroPattern := by
  decide +kernel

/-- The established general semantic-substitution transport specializes to
the two immediate COMM bodies. -/
theorem commTargets_residualEquivalent :
    ProcResidualEquiv (semanticCommSubst boundDropBody zeroPattern)
      (encodeTerm commTarget) := by
  rw [intrinsicTarget_is_noCollapseRepresentative]
  exact semanticCommSubst_transport_to_representative
    boundDropBody zeroPattern

theorem commWholeReducts_residualEquivalent :
    ProcResidualEquiv authoredCommReduct
      (.collection .hashBag [encodeTerm commTarget] none) := by
  apply ProcResidualEquiv.collection_cong .hashBag
    [semanticCommSubst boundDropBody zeroPattern]
    [encodeTerm commTarget] none rfl
  intro i h₁ h₂
  have hi : i = 0 := by
    have bound : i < 1 := by simpa using h₁
    omega
  subst hi
  simpa using commTargets_residualEquivalent

/-- After removing a singleton parallel wrapper, the actual reducts are
equivalent for residual-sensitive process semantics. -/
theorem commReduct_residualEquivalent :
    ProcResidualEquiv authoredCommReduct (encodeTerm commTarget) := by
  exact ProcResidualEquiv.trans commWholeReducts_residualEquivalent
    (ProcResidualEquiv.struct
      (StructuralCongruence.par_singleton (encodeTerm commTarget)))

/-- Every observation saturated under process residual equivalence agrees on
the two selected reducts. -/
theorem residualObservation_agrees (φ : ProcPred)
    (hφ : ProcPredRespectsResidualEquiv φ) :
    φ authoredCommReduct ↔ φ (encodeTerm commTarget) := by
  constructor
  · exact hφ commReduct_residualEquivalent
  · exact hφ (ProcResidualEquiv.symm commReduct_residualEquivalent)

/-- The source profile has a second, distinct Drop step from the COMM reduct. -/
theorem intrinsicComm_then_Drop :
    rhoSourceWithDrop.StepModE commTarget nilP := by
  change rhoSourceWithDrop.StepModE dropChan nilP
  exact source_drop_nil

theorem authoredDrop_on_intrinsicTarget :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      Mettapedia.OSLF.Binding.RhoSchema.Authored.rhoCalcWithDrop
      (encodeTerm commTarget) zeroPattern := by
  simpa only [intrinsicCommTarget_is_drop_quote,
    Mettapedia.OSLF.Binding.RhoSchema.Authored.dropQuotedZero,
    Mettapedia.OSLF.Binding.RhoSchema.Authored.zero,
    zeroPattern] using
    Mettapedia.OSLF.Binding.RhoSchema.Authored.authored_drop_is_step

/-- The declared Drop rule also fires under the same interpreted authored
profile used by COMM. -/
theorem interpretedDrop_on_intrinsicTarget :
    Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step
      rhoRuleInterpretation rhoBasePremises
      Mettapedia.OSLF.Binding.RhoSchema.Authored.rhoCalcWithDrop
      (encodeTerm commTarget) zeroPattern := by
  refine ⟨1, Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.mem_rewriteAt_iff_stepAt.mp ?_⟩
  decide +kernel

/-- Every interpreted COMM/ParCong derivation, including recursive ParCong
uses, survives addition of Drop. The shared reflection and base-premise
interpreters satisfy the generic extension theorem's stability conditions. -/
theorem interpretedCore_step_in_withDrop {source target : Pattern}
    (evidence : RhoStep source target) :
    Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step
      rhoRuleInterpretation rhoBasePremises
      Mettapedia.OSLF.Binding.RhoSchema.Authored.rhoCalcWithDrop
      source target := by
  apply Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step.mono_language
    (interpretation := rhoRuleInterpretation) (base := rhoBasePremises)
    (lang₁ := rhoCalc)
    (lang₂ := Mettapedia.OSLF.Binding.RhoSchema.Authored.rhoCalcWithDrop)
    ?_ ?_ ?_ ?_ evidence
  · intro rule member
    exact List.mem_append.mpr (Or.inl member)
  · intro rule term
    rfl
  · intro rule bindings
    rfl
  · intro bindings premise result member
    cases premise with
    | congruence _ _ =>
        simp [rhoBasePremises,
          Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises] at member
    | scopedStep _ =>
        simp [rhoBasePremises,
          Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises,
          Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv] at member
    | freshness _ | relationQuery _ _ | forAll _ _ _ =>
        simp only [rhoBasePremises,
          Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises] at member ⊢
        exact Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv_mono
          (lang₁ := rhoCalc)
          (lang₂ := Mettapedia.OSLF.Binding.RhoSchema.Authored.rhoCalcWithDrop)
          (fun rule present => List.mem_append.mpr (Or.inl present))
          Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
          bindings _ result member

/-- The concrete COMM step in the extended profile follows from the general
interpreter extension law, rather than a second bounded calculation. -/
theorem interpretedComm_in_withDrop :
    Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step
      rhoRuleInterpretation rhoBasePremises
      Mettapedia.OSLF.Binding.RhoSchema.Authored.rhoCalcWithDrop
      authoredCommSource authoredCommReduct :=
  interpretedCore_step_in_withDrop authoredCommStep

/-- Free Drop is new behavior in the interpreted profile; it cannot be
derived from the established authored COMM and ParCong rules. -/
theorem interpretedDrop_is_properExtension :
    Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step
      rhoRuleInterpretation rhoBasePremises
      Mettapedia.OSLF.Binding.RhoSchema.Authored.rhoCalcWithDrop
      (encodeTerm commTarget) zeroPattern ∧
    ¬ RhoStep (encodeTerm commTarget) zeroPattern := by
  refine ⟨interpretedDrop_on_intrinsicTarget, ?_⟩
  simpa only [intrinsicCommTarget_is_drop_quote, freeDrop,
    zeroPattern] using no_freeDrop_step zeroPattern

theorem targetImagesDiffer :
    Canonical.canonicalize (encodeTerm commTarget) ≠
      Canonical.canonicalize authoredCommReduct := by
  decide +kernel

/-- The chosen immediate COMM reducts cannot be identified by structural
congruence alone. This does not exclude other authored steps. -/
theorem notStructurallyCongruent :
    ¬ StructuralCongruence (encodeTerm commTarget) authoredCommReduct := by
  intro congruence
  have same := Canonical.canonicalize_eq_of_structuralCongruence
    congruence (encodedTerm_hashSetFree commTarget) (by trivial)
  exact targetImagesDiffer same

/-- Canonical structural observation distinguishes the two immediate reducts,
so residual saturation is a substantive hypothesis above. -/
theorem structuralObservation_distinguishes :
    Canonical.canonicalize authoredCommReduct = zeroPattern ∧
    Canonical.canonicalize (encodeTerm commTarget) ≠ zeroPattern := by
  constructor
  · exact authoredCommReduct_is_zero
  · intro equalZero
    exact targetImagesDiffer (equalZero.trans authoredCommReduct_is_zero.symm)

end Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding
