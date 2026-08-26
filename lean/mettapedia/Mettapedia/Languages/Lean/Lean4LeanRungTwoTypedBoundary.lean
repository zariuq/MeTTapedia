import Lean4Lean.Theory.Typing.Strong
import Mettapedia.Languages.Lean.Lean4LeanRungOneDeltaDecision

/-!
# Typed boundary after executable Lean GSLT rung one

The raw beta/delta/head executor is independent of typing.  This module
records the first obstruction to reusing that executor as a decision procedure
for the typed operational GSLT: the same syntactic beta step exists in an
environment where its argument constant has no type.

This is a boundary theorem, not a typed checker.  A later checker must consume
or reconstruct Lean4Lean typing evidence in addition to reproducing the raw
step relation.
-/

namespace Mettapedia.Languages.Lean.Lean4LeanRungTwoTypedBoundary

open Lean4Lean
open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
open Mettapedia.Languages.Lean.Lean4LeanDirectedReduction
open Mettapedia.Languages.Lean.Lean4LeanRungZeroDecision

private abbrev source : VExpr :=
  Lean4LeanDirectedReduction.Canary.betaSource

private abbrev target : VExpr :=
  Lean4LeanDirectedReduction.Canary.betaTarget

private abbrev expectedType : VExpr :=
  Lean4LeanDirectedReduction.Canary.betaType

/-- The raw beta event needs no environment typing authority. -/
theorem empty_raw_beta_step :
    (coreRawHeadGSLT VEnv.empty 0).Step source target := by
  exact ⟨CoreRawHeadEvent.beta⟩

/-- No term in the empty environment can type the fixture's named constant.
This uses Lean4Lean's independently proved syntax inversion for constants. -/
theorem empty_has_no_fixture_argument_type
    (candidateType : VExpr) :
    ¬VEnv.empty.HasType 0 []
      Lean4LeanDirectedReduction.Canary.argument candidateType := by
  intro typed
  obtain ⟨constantInfo, present, _, _⟩ :=
    typed.const_inv VEnv.Ordered.empty (by trivial)
  change (none : Option VConstant) = some constantInfo at present
  contradiction

/-- The corresponding typed operational fibre is empty.  In the beta case
the missing argument typing is exposed directly; the indexed source and target
exclude the other event constructors. -/
theorem empty_has_no_typed_beta_event :
    ¬Nonempty (CoreHeadEvent VEnv.empty 0 [] expectedType source target) := by
  rintro ⟨event⟩
  have sourceTyped := event.endpointsTyped.1
  obtain ⟨domain, codomain, _, argumentTyped⟩ :=
    sourceTyped.app_inv VEnv.Ordered.empty (by trivial)
  exact empty_has_no_fixture_argument_type domain argumentTyped

/-- The raw decision accepts the step while the typed OSLF/NTT exact-target
predicate rejects it.  Raw reduction correctness therefore cannot be reused
as typed-kernel correctness without a separate typing realization. -/
theorem raw_accepts_while_typed_ntt_rejects :
    (coreRawStepDecisionOfNoDelta VEnv.empty 0 (by
      intro definition member
      exact member.elim)).decideStep source target = true ∧
    ¬(gsltOSLF (coreHeadGSLT VEnv.empty 0 [] expectedType)).satisfies source
      (exactCoreHeadTargetType VEnv.empty 0 [] expectedType target).pred := by
  constructor
  · rfl
  · rw [satisfies_exactCoreHeadTargetType_iff_event]
    exact empty_has_no_typed_beta_event

/-- In contrast, the authored one-axiom environment supplies the exact typing
evidence and the same syntactic event inhabits the typed NTT. -/
theorem typed_ntt_accepts_after_required_declaration :
    (gsltOSLF (coreHeadGSLT
      Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom 0 [] expectedType)).satisfies
      source
      (exactCoreHeadTargetType
        Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom 0 [] expectedType
        target).pred :=
  Lean4LeanDirectedReduction.Canary.beta_inhabits_directed_ntt

/-- Any future exact typed step decision must reject the fixture before the
declaration.  This is a checker-independent consequence of the typed GSLT. -/
theorem every_typed_step_decision_rejects_before_declaration
    (decision : EffectiveStructure.StepDecision
      (coreHeadGSLT VEnv.empty 0 [] expectedType)) :
    decision.decideStep source target = false := by
  cases decided : decision.decideStep source target with
  | false => rfl
  | true =>
      have event : (coreHeadGSLT VEnv.empty 0 [] expectedType).Step
          source target :=
        (decision.correct source target).mp decided
      exact (empty_has_no_typed_beta_event event).elim

/-- The declaration changes the typed NTT fibre even though the underlying
syntactic beta event is already present.  This is the minimal typed
environment-growth canary for the indexed Lean GSLT family. -/
theorem declaration_changes_typed_not_raw_fibre :
    (coreRawHeadGSLT VEnv.empty 0).Step source target ∧
    ¬(coreHeadGSLT VEnv.empty 0 [] expectedType).Step source target ∧
    (coreHeadGSLT Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom
      0 [] expectedType).Step source target := by
  refine ⟨empty_raw_beta_step, empty_has_no_typed_beta_event, ?_⟩
  exact (satisfies_exactCoreHeadTargetType_iff_event
    Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom 0 [] expectedType
    source target).mp typed_ntt_accepts_after_required_declaration

section AxiomAudit

#print axioms VEnv.HasType.const_inv
#print axioms empty_has_no_fixture_argument_type
#print axioms empty_has_no_typed_beta_event
#print axioms raw_accepts_while_typed_ntt_rejects
#print axioms typed_ntt_accepts_after_required_declaration
#print axioms every_typed_step_decision_rejects_before_declaration
#print axioms declaration_changes_typed_not_raw_fibre

end AxiomAudit

end Mettapedia.Languages.Lean.Lean4LeanRungTwoTypedBoundary
