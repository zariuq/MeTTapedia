import Mettapedia.OSLF.Framework.WMCalculusCombinedStructuralPresentation
import Mettapedia.GSLT.LanguageDef.EquationPremiseStability

/-!
# Equation-modulo transport into the combined structural WM presentation

The literal structural map carries the core equation declarations. This file
checks the stronger semantic consequence on the exact generic OSLF relation:
an instance, a contextual equation path, and an equation-saturated directed
step of the structural core each remain valid in the guarded extension.
The map is forward only; no target-to-source completeness is asserted.
-/

namespace Mettapedia.OSLF.Framework.WMCalculusCombinedStructuralSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.WMCalculusStructuralPresentation
open Mettapedia.OSLF.Framework.WMCalculusCombinedStructuralPresentation
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics

set_option autoImplicit false

private theorem structuralEquation_premises_nil (equation : Equation)
    (member : equation ∈ wmStructuralLanguageDef.equations) :
    equation.premises = [] := by
  change equation ∈ structuralEquations at member
  simp only [structuralEquations, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

/-- Every actual core equation instance, in either direction, is still an
instance in the combined structural presentation. Its three source schemas
have no premises, so the target uses exactly the same match and substitution. -/
theorem structuralEquationInstance_in_combined
    {base : BasePremiseEvaluator} {source target : Pattern}
    (equationInstance : EquationInstance base wmStructuralLanguageDef source target) :
    EquationInstance base combinedStructuralLanguageDef source target := by
  exact (Mettapedia.GSLT.LanguageDef.EquationPremiseStability.equationInstance_iff
    (source := wmStructuralLanguageDef)
    (target := combinedStructuralLanguageDef)
    (sourceBase := base) (targetBase := base)
    rfl (Mettapedia.GSLT.LanguageDef.EquationPremiseStability.premisesAgree_of_premise_free
      structuralEquation_premises_nil) source target).mp equationInstance

private theorem no_structuralCore_derivedInstance (source target : Pattern) :
    ¬ DerivedInstance wmStructuralLanguageDef source target := by
  apply no_derivedInstance_of_no_derived_laws
  all_goals decide +kernel

/-- Contextual equation generators transport. The source has no declared
collection carrier, so its generators are precisely authored instances. -/
theorem structuralEquationContextStep_in_combined
    {base : BasePremiseEvaluator} {source target : Pattern}
    (step : EquationContextStep base wmStructuralLanguageDef source target) :
    EquationContextStep base combinedStructuralLanguageDef source target := by
  cases step with
  | inContext context witness =>
      rcases witness with authored | derived
      · exact .inContext context
          (Or.inl (structuralEquationInstance_in_combined authored))
      · exact False.elim (no_structuralCore_derivedInstance _ _ derived)

/-- The entire contextual symmetric/transitive closure of structural-core
equations is retained by the guarded structural extension. -/
theorem structuralEquationEquiv_in_combined
    {base : BasePremiseEvaluator} {source target : Pattern}
    (equivalent : EquationEquiv base wmStructuralLanguageDef source target) :
    EquationEquiv base combinedStructuralLanguageDef source target := by
  induction equivalent with
  | rel source target step =>
      exact Relation.EqvGen.rel _ _
        (structuralEquationContextStep_in_combined step)
  | refl pattern => exact Relation.EqvGen.refl pattern
  | symm source target _ inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans source middle target _ _ firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- The actual OSLF one-step relation, with equation changes at both ends,
is preserved from the structural core into the structural combined vertex. -/
theorem structuralSemanticStep_in_combined
    {source target : Pattern}
    (step : langSemanticReduces wmStructuralLanguageDef source target) :
    langSemanticReduces combinedStructuralLanguageDef source target := by
  change StepModuloEquations (engineBasePremises RelationEnv.empty)
    wmStructuralLanguageDef source target at step
  change StepModuloEquations (engineBasePremises RelationEnv.empty)
    combinedStructuralLanguageDef source target
  obtain ⟨redex, contractum, before, primitive, after⟩ := step
  refine ⟨redex, contractum,
    structuralEquationEquiv_in_combined before, ?_,
    structuralEquationEquiv_in_combined after⟩
  apply Step.mono_rules (lang₁ := wmStructuralLanguageDef)
    (lang₂ := combinedStructuralLanguageDef) ?_ primitive
  intro rule member
  change rule ∈ computationalRules ++ coreCongruenceRules at member
  change rule ∈ computationalRules ++ extensionComputations ++
    coreCongruenceRules ++ combinedExtensionCongruenceRules
  simp only [List.mem_append] at member ⊢
  tauto

#print axioms structuralEquationInstance_in_combined
#print axioms structuralEquationEquiv_in_combined
#print axioms structuralSemanticStep_in_combined

end Mettapedia.OSLF.Framework.WMCalculusCombinedStructuralSemantics
