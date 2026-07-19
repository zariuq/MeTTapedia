import Mettapedia.Languages.MeTTa.HE.HumanTypePresentationPrincipalAlpha
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance

/-!
# Alpha-exact observation of LeaTTa type presentations

This module instantiates finite-presentation alpha uniqueness with repaired
LeaTTa's canonical runtime binding invariant.  The human presentation and the
runtime binding list are related only by their complete solution theories;
no equality-class representative or binding-list order is exposed.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationPrincipalAlpha

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HumanTypePresentation
open HumanTypePresentationTheory
open HumanTypePresentationMatchSolutionTheory
open HumanTypeRuntimeRefinement
open HumanTypePresentationAlpha
open HumanTypePresentationPrincipalAlpha
open LeaTTaBridge
open LeaTTaHumanConformance
open LeaTTaTypeConformance

/-- A normal finite human presentation and a repaired reachable LeaTTa
binding state with the same complete solution theory present every declared
type up to alpha-renaming. -/
theorem observedTypeAlpha_of_solutionTheory
    {substitution : TypeSubst} (normal : substitution.Normal)
    {bindings : Metta.Bindings}
    (theory : LeaBindingSolutionTheoryEquiv
      (typeSubstAsHumanBindings substitution) bindings)
    (runtime : LeaRuntimeBindingInvariant bindings)
    (declared : Atom) :
    ObservedTypeAlphaRel
      (substitution.apply declared)
      (fromLeaTTaAtom
        (Metta.instantiate bindings (toLeaTTaAtom declared))) := by
  let leaModel := leaClassSolution bindings
  let nativeModel : String → Atom :=
    fun name => fromLeaTTaAtom (leaModel name)
  have nativeModelSatisfied :
      TypeSubstSatisfied nativeModel substitution := by
    have humanModel : HEBindingSatisfied leaModel
        (typeSubstAsHumanBindings substitution) :=
      (theory leaModel).mpr runtime.canonical.1
    have nativeHumanModel :=
      humanTypeBindingSatisfied_of_heBindingSatisfied humanModel
    exact (humanTypeBindingSatisfied_asHumanBindings_iff
      nativeModel substitution).mp nativeHumanModel
  have presentationRefinesModel :
      ∃ post : String → Atom, ∀ name,
        presentedValuation substitution name =
          applyTypeValuation post (nativeModel name) := by
    let presentationModel := presentedValuation substitution
    let leaPresentationModel : String → Metta.Atom :=
      fun name => toLeaTTaAtom (presentationModel name)
    have presentationSatisfied :
        TypeSubstSatisfied presentationModel substitution :=
      normal_presentedValuation_satisfied normal
    have humanPresentationSatisfied : HumanTypeBindingSatisfied
        presentationModel (typeSubstAsHumanBindings substitution) :=
      (humanTypeBindingSatisfied_asHumanBindings_iff
        presentationModel substitution).mpr presentationSatisfied
    have heaPresentationSatisfied : HEBindingSatisfied
        leaPresentationModel (typeSubstAsHumanBindings substitution) :=
      heBindingSatisfied_of_humanTypeBindingSatisfied
        humanPresentationSatisfied
    have leaPresentationSatisfied :
        LeaBindingSatisfied leaPresentationModel bindings :=
      (theory leaPresentationModel).mp heaPresentationSatisfied
    obtain ⟨leaPost, hleaPost⟩ :=
      runtime.canonical.2 leaPresentationModel leaPresentationSatisfied
    refine ⟨fun name => fromLeaTTaAtom (leaPost name), ?_⟩
    intro name
    have decoded := congrArg fromLeaTTaAtom (hleaPost name)
    rw [fromLeaTTaAtom_applyClassSolution_any] at decoded
    simpa [leaPresentationModel, presentationModel,
      nativeModel, leaModel] using decoded
  have alpha := observedTypeAlpha_of_mutuallyPrincipal normal
    nativeModelSatisfied presentationRefinesModel declared
  simpa [nativeModel, leaModel, ← fromLeaTTaAtom_applyClassSolution,
    applyClassSolution_lea_eq_instantiate] using alpha

/-! ## Boundary examples -/

/-- Positive: the empty runtime presentation agrees literally, hence also
alpha-exactly, with the empty finite presentation. -/
theorem empty_presentation_alpha (declared : Atom) :
    ObservedTypeAlphaRel
      (TypeSubst.apply ([] : TypeSubst) declared)
      (fromLeaTTaAtom
        (Metta.instantiate Metta.Bindings.empty
          (toLeaTTaAtom declared))) := by
  apply observedTypeAlpha_of_solutionTheory TypeSubst.normal_empty
  · intro valuation
    simp [typeSubstAsHumanBindings, HEBindingSatisfied,
      LeaBindingSatisfied, Metta.Bindings.empty]
  · exact leaRuntimeBindingInvariant_empty

/-- Negative boundary: alpha-exactness does not identify a runtime symbol
with a human variable merely because both are legal type atoms. -/
theorem variable_symbol_boundary_not_alpha :
    ¬ObservedTypeAlphaRel (.var "x") (.symbol "A") :=
  HumanTypePresentationPrincipalAlpha.variable_symbol_not_alpha

end Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationPrincipalAlpha
