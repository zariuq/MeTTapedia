import Mettapedia.GSLT.LanguageDef.ConstructorSupport
import Mettapedia.GSLT.LanguageDef.CostStatic
import Mettapedia.GSLT.LanguageDef.EquationSemantics

/-!
# Boundary examples for constructor-fragment stability

Premise-free, constructor-supported equation schemas do not by themselves
make constructor support invariant under the raw equation relation.  Matching
observes an explicit-substitution schema, while contractum instantiation
executes that substitution.  The negative fixture below isolates why an
iterable continued presentation must state a normalization-stability law in
addition to schema retypability.
-/

namespace Mettapedia.GSLT.LanguageDef.ConstructorSupportBoundaryExamples

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.LanguageDef

private def staticConstructor : Pattern := .apply "Static" []
private def interactionPrincipal : Pattern := .apply "Principal" []

/-- This schema contains only the static constructor, but applying a binding
executes its explicit substitution and erases the replacement. -/
private def erasingSchema : Pattern :=
  .subst staticConstructor (.fvar "x")

private def erasingEquation : Equation where
  name := "erase-replacement"
  typeContext := [("x", .base "Term")]
  premises := []
  left := erasingSchema
  right := erasingSchema

private def revealingEquation : Equation where
  name := "reveal-replacement"
  typeContext := [("x", .base "Term")]
  premises := []
  left := erasingSchema
  right := .fvar "x"

private def boundaryLanguage : LanguageDef :=
  { LanguageDef.empty "constructor-support-boundary" with
    equations := [erasingEquation, revealingEquation] }

private def principalBindings : Bindings :=
  [("x", interactionPrincipal)]

private def rawMatchedSource : Pattern :=
  .subst staticConstructor interactionPrincipal

private theorem erasingSchema_matches_raw :
    principalBindings ∈ matchPattern erasingSchema rawMatchedSource := by
  apply matchRel_complete
  apply MatchRel.subst
  · exact MatchRel.apply MatchArgsRel.nil rfl
  · exact MatchRel.fvar
  · rfl

private theorem raw_equationStep_static :
    EquationSemantics.EquationContextStep defaultBasePremises
      boundaryLanguage rawMatchedSource staticConstructor := by
  apply EquationSemantics.EquationContextStep.inContext .hole
  refine ⟨0, EquationSemantics.EquationInstanceAt.forward
    (equation := erasingEquation)
    (initialBindings := principalBindings)
    (finalBindings := principalBindings) ?_ erasingSchema_matches_raw
      (.nil principalBindings) ?_⟩
  · exact .head _
  · simp [erasingEquation, erasingSchema, principalBindings,
      staticConstructor, interactionPrincipal, applyBindings,
      Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVar,
      Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt]

private theorem raw_equationStep_principal :
    EquationSemantics.EquationContextStep defaultBasePremises
      boundaryLanguage rawMatchedSource interactionPrincipal := by
  apply EquationSemantics.EquationContextStep.inContext .hole
  refine ⟨0, EquationSemantics.EquationInstanceAt.forward
    (equation := revealingEquation)
    (initialBindings := principalBindings)
    (finalBindings := principalBindings) ?_ erasingSchema_matches_raw
      (.nil principalBindings) ?_⟩
  · exact .tail _ (.head _)
  · simp [revealingEquation, principalBindings, interactionPrincipal,
      applyBindings]

/-- The current raw equation interface can equate a term using only the
static fragment with a genuine interaction principal even though both
authored schemas themselves use only the static fragment. -/
theorem equationEquiv_can_escape_schema_constructor_support :
    EquationSemantics.EquationEquiv defaultBasePremises boundaryLanguage
      staticConstructor interactionPrincipal := by
  exact Relation.EqvGen.trans _ rawMatchedSource _
    (Relation.EqvGen.symm _ _
      (Relation.EqvGen.rel _ _ raw_equationStep_static))
    (Relation.EqvGen.rel _ _ raw_equationStep_principal)

/-- Both schemas pass the existing syntactic instantiation-stability check;
that check is not the missing constructor-fragment law. -/
theorem counterexample_schemas_instantiationStable :
    schemaInstantiationStable erasingSchema = true ∧
      schemaInstantiationStable (.fvar "x") = true := by
  decide

/-- The source term and both schemas lie in the selected static fragment. -/
theorem counterexample_static_support :
    ConstructorsWithin (· = "Static") staticConstructor ∧
      ConstructorsWithin (· = "Static") erasingSchema ∧
      ConstructorsWithin (· = "Static") (.fvar "x") := by
  simp [staticConstructor, erasingSchema]

/-- The equivalent interaction principal lies outside that fragment. -/
theorem counterexample_principal_not_supported :
    ¬ ConstructorsWithin (· = "Static") interactionPrincipal := by
  simp [interactionPrincipal]

end Mettapedia.GSLT.LanguageDef.ConstructorSupportBoundaryExamples
