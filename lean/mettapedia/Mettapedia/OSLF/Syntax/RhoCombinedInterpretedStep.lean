import Mettapedia.OSLF.Syntax.RhoClosedDropComparison
import Mettapedia.OSLF.Syntax.RhoParCongResidualSimulation
import Mettapedia.OSLF.Syntax.RhoCommunicationEncoding

/-!
# The combined interpreted rho operational profile

The same authored language runs reflective COMM, unconditional Drop, and
recursive ParCong. This module gives their common least-step interface. It
does not identify intrinsic binary firing trees with authored hash-bag
histories; that comparison still needs an occurrence-preserving map.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoCombinedInterpretedStep

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Binding.RhoSchema.Authored
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding
open Mettapedia.OSLF.Binding.RhoSemanticRulePolynomial
open Mettapedia.OSLF.Binding.RhoClosedDropComparison
open Mettapedia.OSLF.Binding.RhoParCongResidualSimulation
open Mettapedia.OSLF.Framework.ConstructorCategory

/-- Least reduction for the complete Chapter 7 authored rule profile. -/
abbrev RhoStepWithDrop : Pattern → Pattern → Prop :=
  Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step
    rhoRuleInterpretation rhoBasePremises rhoCalcWithDrop

/-- The established interpreted core is a subrelation of the complete rule
profile, including its recursive ParCong uses. -/
theorem core_in_combined {source target : Pattern}
    (step : RhoStep source target) :
    RhoStepWithDrop source target :=
  Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding.interpretedCore_step_in_withDrop step

private theorem drop_no_matchingPresentation :
    matchingPresentationForRule? rhoReflectionProfile rhoDropRewrite = none := by
  decide +kernel

private theorem drop_no_substitutionPresentation :
    substitutionPresentationForRule? rhoReflectionProfile rhoDropRewrite = none := by
  decide +kernel

/-- The added rule fires for every raw process pattern. Admission to the
closed reflective carrier is a separate condition on the supplied pattern. -/
theorem drop (process : Pattern) :
    RhoStepWithDrop
      (.apply "PDrop" [.apply "NQuote" [process]]) process := by
  refine ⟨1, StepAt.rule (rule := rhoDropRewrite)
    (initialBindings := [("P", process)])
    (finalBindings := [("P", process)]) ?_ ?_ ?_ ?_⟩
  · simp [rhoCalcWithDrop, rhoCalc]
  · change [("P", process)] ∈
      matchPatternForRuleUsing rhoReflectionProfile rhoDropRewrite
        (.apply "PDrop" [.apply "NQuote" [process]])
    rw [matchPatternForRuleUsing, drop_no_matchingPresentation]
    simp [rhoDropRewrite, matchPattern, matchArgs, mergeBindings]
  · exact .nil _
  · change applyBindingsForRuleUsing rhoReflectionProfile rhoDropRewrite
      [("P", process)] = process
    rw [applyBindingsForRuleUsing, drop_no_substitutionPresentation]
    simp [rhoDropRewrite, applyRuleBindings, applyBindings]

/-- Recursive ParCong acts on any step of the combined profile, including a
new Drop step or an older COMM step. -/
theorem par {source target : Pattern} (rest : List Pattern)
    (step : RhoStepWithDrop source target) :
    RhoStepWithDrop
      (.collection .hashBag (source :: rest) none)
      (.collection .hashBag (target :: rest) none) := by
  refine step_of_single_congruence_rule
    (base := rhoBasePremises)
    (rule := rhoParCongRewrite)
    (initialBindings :=
      [("rest", .collection .hashBag rest none), ("S", source)])
    (finalBindings :=
      [("T", target),
       ("rest", .collection .hashBag rest none),
       ("S", source)])
    (premiseBindings := [("T", target)])
    (premiseSource := .fvar "S")
    (premiseTarget := .fvar "T")
    (candidate := target)
    (by simp [rhoCalcWithDrop, rhoCalc])
    (rhoParCong_match_exact source rest)
    rfl ?_ ?_ rfl ?_
  · simpa [applyBindings, Bindings.lookup] using step
  · simp [matchPattern]
  · change applyBindingsForRuleUsing rhoReflectionProfile rhoParCongRewrite
      [("T", target),
       ("rest", .collection .hashBag rest none),
       ("S", source)] = _
    rw [applyBindingsForRuleUsing, rhoParCong_no_substitutionPresentation,
      applyRuleBindings, applyBindingsScoped_zero_of_binderFree _ _ _ (by decide)]
    simp [rhoParCongRewrite, applyBindings]

/-- A Drop firing can be carried through any authored parallel residue. -/
theorem par_drop (process : Pattern) (rest : List Pattern) :
    RhoStepWithDrop
      (.collection .hashBag
        ((.apply "PDrop" [.apply "NQuote" [process]]) :: rest) none)
      (.collection .hashBag (process :: rest) none) :=
  par rest (drop process)

/-- The common profile carries an arbitrary child simulation through the
authored selected-component parallel frame. The two endpoint comparisons
remain distinct: structural congruence at the source, residual equivalence
at the target. -/
theorem par_simulation
    {intrinsicSource intrinsicTarget authoredSource authoredTarget rest : Pattern}
    (sourceComparison : StructuralCongruence intrinsicSource authoredSource)
    (child : RhoStepWithDrop authoredSource authoredTarget)
    (targetComparison : ProcResidualEquiv authoredTarget intrinsicTarget) :
    RhoStepWithDrop
      (.collection .hashBag [authoredSource, rest] none)
      (.collection .hashBag [authoredTarget, rest] none) ∧
    StructuralCongruence
      (.collection .hashBag [intrinsicSource, rest] none)
      (.collection .hashBag [authoredSource, rest] none) ∧
    ProcResidualEquiv
      (.collection .hashBag [authoredTarget, rest] none)
      (.collection .hashBag [intrinsicTarget, rest] none) :=
  ⟨par [rest] child,
    parallel_source_congruence sourceComparison,
    parallel_target_residual targetComparison⟩

/-- The previously proved quote-safe COMM/ParCong comparison is a step in
the same interpreted profile that also runs Drop. -/
theorem comm_under_par_in_combined
    (channel : Term sig [] Srt.nm)
    (payload rest : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr)
    (channelSafe : intrinsicQuoteSafe 0 channel = true)
    (payloadSafe : intrinsicQuoteSafe 0 payload = true)
    (bodySafe : intrinsicQuoteSafe 1 body = true) :
    RhoStepWithDrop
      (.collection .hashBag
        [Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover.authoredInputFirst
          channel payload body, encodeTerm rest] none)
      (.collection .hashBag
        [Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover.authoredResult
          payload body, encodeTerm rest] none) ∧
    StructuralCongruence
      (encodeTerm (RhoSemanticRulePolynomial.par
        (BindingCloneAlgebra.terms sig)
        (Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover.intrinsicSource
          channel payload body) rest))
      (.collection .hashBag
        [Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover.authoredInputFirst
          channel payload body, encodeTerm rest] none) ∧
    ProcResidualEquiv
      (.collection .hashBag
        [Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover.authoredResult
          payload body, encodeTerm rest] none)
      (encodeTerm (RhoSemanticRulePolynomial.par
        (BindingCloneAlgebra.terms sig)
        (RhoSemanticRulePolynomial.commTarget
          (BindingCloneAlgebra.terms sig) payload body) rest)) := by
  have core := comm_under_par_simulation
    channel payload rest body channelSafe payloadSafe bodySafe
  exact ⟨core_in_combined core.1, core.2⟩

/-- The intrinsic Drop constructor under binary parallel and the actual
interpreted hash-bag firing coexist for every quote-safe closed instance.
Their firing witnesses are retained separately; no tree bijection is claimed. -/
theorem intrinsic_par_drop_interpreted
    (process rest : Term sig [] Srt.pr)
    (processSafe : intrinsicQuoteSafe 0 process = true)
    (restSafe : intrinsicQuoteSafe 0 rest = true) :
    Nonempty ((rules (BindingCloneAlgebra.terms sig)).Fix ()
      (judgment (BindingCloneAlgebra.terms sig)
        (RhoSemanticRulePolynomial.par (BindingCloneAlgebra.terms sig)
          (intrinsicDropSource process) rest)
        (RhoSemanticRulePolynomial.par (BindingCloneAlgebra.terms sig) process rest))) ∧
    RhoStepWithDrop
      (encodeTerm (RhoSemanticRulePolynomial.par (BindingCloneAlgebra.terms sig)
        (intrinsicDropSource process) rest))
      (encodeTerm (RhoSemanticRulePolynomial.par (BindingCloneAlgebra.terms sig) process rest)) ∧
    RhoClosedTermWellSorted rhoProc
      (encodeTerm (RhoSemanticRulePolynomial.par (BindingCloneAlgebra.terms sig)
        (intrinsicDropSource process) rest)) ∧
    RhoClosedTermWellSorted rhoProc
      (encodeTerm (RhoSemanticRulePolynomial.par (BindingCloneAlgebra.terms sig) process rest)) := by
  have sourceClosed := (encoded_drop_source_admitted_iff process).mpr processSafe
  have processClosed := (encoded_process_admitted_iff_quoteSafe process).mpr processSafe
  have restClosed := (encoded_process_admitted_iff_quoteSafe rest).mpr restSafe
  refine ⟨⟨parCongTree (intrinsicDropTree process)⟩, ?_, ?_, ?_⟩
  · change RhoStepWithDrop
      (.collection .hashBag
        [encodeTerm (intrinsicDropSource process), encodeTerm rest] none)
      (.collection .hashBag [encodeTerm process, encodeTerm rest] none)
    rw [encoded_drop_source_eq]
    exact par [encodeTerm rest] (drop (encodeTerm process))
  · change RhoClosedTermWellSorted rhoProc
      (.collection .hashBag
        [encodeTerm (intrinsicDropSource process), encodeTerm rest] none)
    exact closed_parallel (encodeTerm (intrinsicDropSource process))
      (encodeTerm rest) sourceClosed restClosed
  · change RhoClosedTermWellSorted rhoProc
      (.collection .hashBag [encodeTerm process, encodeTerm rest] none)
    exact closed_parallel (encodeTerm process) (encodeTerm rest)
      processClosed restClosed

/-- Drop is proper new behavior, even under the reflective interpretation. -/
theorem core_does_not_drop_zero :
    ¬ RhoStep dropQuotedZero Authored.zero := by
  have h := Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding.interpretedDrop_is_properExtension.2
  rw [Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding.intrinsicCommTarget_is_drop_quote] at h
  simpa [dropQuotedZero, Authored.zero,
    Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding.zeroPattern] using h

theorem combined_strict_over_core :
    RhoStepWithDrop dropQuotedZero Authored.zero ∧
    ¬ RhoStep dropQuotedZero Authored.zero :=
  ⟨drop Authored.zero, core_does_not_drop_zero⟩

#print axioms core_in_combined
#print axioms drop
#print axioms par
#print axioms par_simulation
#print axioms comm_under_par_in_combined
#print axioms intrinsic_par_drop_interpreted
#print axioms combined_strict_over_core

end Mettapedia.OSLF.Binding.RhoCombinedInterpretedStep
