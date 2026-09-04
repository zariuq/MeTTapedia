import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTyped

/-!
# Relation-aware operational projection of the typed call-guard compiler

The flat typed compiler contains the authenticated cold object language and
its generated selected-native proof calculus.  Object execution must retain
the cold language's nonempty premise interpretation; proof search occupies a
disjoint summand and contributes no object rewrite.

This module instantiates the generic relation-aware totalizer and proves the
operational erasure boundary before any lowering to StructuredC.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTypedOperational

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTyped

/-- The flat typed language has no equations, so its real relation environment
induces a lawful object GSLT without any extra semantic assumption. -/
def reductionLaws : ReductionRespectsEquationsUsing relationEnv
    generated.1.toLanguageDef :=
  ReductionRespectsEquationsUsing.of_equation_free relationEnv
    flatTyped_equationFree

/-- The one relation-aware typed theory: cold object execution on the left,
generic generated-calculus proof search on the right. -/
def typedCompilerTheory : GSLT :=
  generated.1.toGSLTUsing relationEnv generated.2 reductionLaws

/-- Enlarging the object signature with generated typing constructors changes
no least contextual reduction.  In the five-field core that relation is
monotone in—and therefore, under equality, determined by—the authored rewrite
list. -/
theorem flat_langReduces_iff_cold (relations : RelationEnv)
    (source target : Pattern) :
    langReducesUsing relations generated.1.toLanguageDef source target ↔
      langReducesUsing relations language source target := by
  constructor
  · intro step
    unfold langReducesUsing at step ⊢
    apply Step.mono_rules (lang₁ := generated.1.toLanguageDef)
      (lang₂ := language) (relEnv := relations) ?_ step
    intro rule membership
    simpa only [flatTyped_rewrites] using membership
  · intro step
    unfold langReducesUsing at step ⊢
    apply Step.mono_rules (lang₁ := language)
      (lang₂ := generated.1.toLanguageDef) (relEnv := relations) ?_ step
    intro rule membership
    simpa only [flatTyped_rewrites] using membership

/-- The left summand of the typed theory is exactly the authenticated cold
compiler language, globally on raw patterns. -/
theorem typedCompilerTheory_object_step_iff_cold
    (source target : Pattern) :
    typedCompilerTheory.Step
        (inLanguage source) (inLanguage target) ↔
      langReducesUsing relationEnv language source target := by
  simpa only [typedCompilerTheory] using
    ((CalculusLanguageDef.toGSLTUsing_object_step generated.1
      relationEnv generated.2 reductionLaws source target).trans
        (flat_langReduces_iff_cold relationEnv source target))

/-- The right summand remains exactly generic proof search for the admitted
flat calculus. -/
theorem typedCompilerTheory_proof_step_iff
    (source target : GoalState) :
    typedCompilerTheory.Step
        (inCalculus source) (inCalculus target) ↔
      (proofSearchGSLT generated).Step source target := by
  exact CalculusLanguageDef.toGSLTUsing_proof_step
    generated.1 relationEnv generated.2 reductionLaws source target

/-- Object execution and proof search cannot manufacture steps in each
other's carrier. -/
theorem typedCompilerTheory_no_crossing
    (pattern : Pattern) (state : GoalState) :
    ¬ typedCompilerTheory.Step (inLanguage pattern) (inCalculus state) ∧
      ¬ typedCompilerTheory.Step (inCalculus state) (inLanguage pattern) := by
  exact CalculusLanguageDef.toGSLTUsing_no_crossing
    generated.1 relationEnv generated.2 reductionLaws pattern state

/-- On the canonical codec image, one typed object step is exactly the unique
independent cold micro-machine transition. -/
theorem typedCompilerTheory_object_step_iff_compileLanguageStep
    (source : CompileLanguageControl) (wire : Pattern) :
    typedCompilerTheory.Step
        (inLanguage (encodeCompileLanguageControl source))
        (inLanguage wire) ↔
      ∃ target, compileLanguageStep? source = some target ∧
        wire = encodeCompileLanguageControl target := by
  exact (typedCompilerTheory_object_step_iff_cold
    (encodeCompileLanguageControl source) wire).trans
      (language_step_iff_compileLanguageStep source wire)

/-- Generated derivability is still exactly right-summand reduction to the
empty obligation list.  This theorem is structural; semantic soundness of the
generated rules is a separate displayed-model obligation. -/
theorem typedCompilerTheory_derivability (goals : GoalState) :
    Nonempty (DerivationList generated goals) ↔
      typedCompilerTheory.MultiStep (inCalculus goals) (inCalculus []) := by
  exact CalculusLanguageDef.toGSLTUsing_derivability
    generated.1 relationEnv generated.2 reductionLaws goals

/-! ## The relation environment is load-bearing -/

namespace RelationEnvironmentCanary

def owner : SpaceOwner := ⟨0⟩

def declaration : ArrowDeclaration :=
  ⟨0, "g", [], undefinedType⟩

def sourceControl : CompileLanguageControl :=
  .running owner 0 "f" 0 [declaration] []

def targetControl : CompileLanguageControl :=
  .running owner 0 "f" 0 [] []

def sourceWire : Pattern := encodeCompileLanguageControl sourceControl

def targetWire : Pattern := encodeCompileLanguageControl targetControl

theorem compile_step :
    compileLanguageStep? sourceControl = some targetControl := by
  decide +kernel

/-- With the authored relation environment, the typed theory performs the
required skip-head transition. -/
theorem relation_aware_theory_steps :
    typedCompilerTheory.Step
      (inLanguage sourceWire) (inLanguage targetWire) := by
  apply (typedCompilerTheory_object_step_iff_compileLanguageStep
    sourceControl targetWire).2
  exact ⟨targetControl, compile_step, rfl⟩

/-- The closed environment cannot discharge the transition's inequality
query, so the exact root executor has no result. -/
theorem empty_root_executor_stuck :
    rewriteStepWithPremisesUsing RelationEnv.empty language sourceWire = [] := by
  decide +kernel

theorem empty_cold_has_no_step :
    ¬ langReducesUsing RelationEnv.empty language sourceWire targetWire := by
  intro step
  unfold langReducesUsing at step
  have rootStep : RootStep RelationEnv.empty language sourceWire targetWire :=
    (step_iff_rootStep_of_noncontextualRules
      language_rules_noncontextual).mp step
  have member : targetWire ∈
      rewriteStepWithPremisesUsing RelationEnv.empty language sourceWire := by
    simpa [RootStep, rewriteStepWithPremisesUsing,
      applyRuleWithPremisesUsing] using rootStep
  rw [empty_root_executor_stuck] at member
  exact List.not_mem_nil member

def emptyReductionLaws : ReductionRespectsEquations
    generated.1.toLanguageDef :=
  ReductionRespectsEquations.of_equation_free flatTyped_equationFree

def emptyTheory : GSLT :=
  generated.1.toGSLT generated.2 emptyReductionLaws

/-- The historical empty-environment totalizer loses a genuine cold compiler
step.  This is the negative control that makes relation-aware totalization a
semantic requirement rather than an API convenience. -/
theorem empty_theory_misses_real_step :
    ¬ emptyTheory.Step
      (inLanguage sourceWire) (inLanguage targetWire) := by
  intro step
  have flatStep :
      langReducesUsing RelationEnv.empty generated.1.toLanguageDef
        sourceWire targetWire :=
    (CalculusLanguageDef.toGSLT_object_step generated.1 generated.2
      emptyReductionLaws sourceWire targetWire).mp (by
        simpa only [emptyTheory] using step)
  exact empty_cold_has_no_step
    ((flat_langReduces_iff_cold RelationEnv.empty sourceWire targetWire).mp
      flatStep)

theorem relation_environment_is_load_bearing :
    typedCompilerTheory.Step
        (inLanguage sourceWire) (inLanguage targetWire) ∧
      ¬ emptyTheory.Step
        (inLanguage sourceWire) (inLanguage targetWire) :=
  ⟨relation_aware_theory_steps, empty_theory_misses_real_step⟩

end RelationEnvironmentCanary

#print axioms flat_langReduces_iff_cold
#print axioms typedCompilerTheory_object_step_iff_cold
#print axioms typedCompilerTheory_proof_step_iff
#print axioms typedCompilerTheory_no_crossing
#print axioms typedCompilerTheory_object_step_iff_compileLanguageStep
#print axioms typedCompilerTheory_derivability
#print axioms RelationEnvironmentCanary.relation_environment_is_load_bearing

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTypedOperational
