import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationExactConformance
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationPrincipalAlpha

/-!
# Exact finite-presentation simulation of the application type fold

The repaired runtime carries equality-class bindings, while exact human type
packages carry a normal finite substitution.  The simulation state relates
the finite presentation to the already-sealed native human binding theory,
and relates that theory to LeaTTa independently through `TypeBindingState`.

Each successful runtime type match is reconstructed as one presentation
step by semantic completeness.  The resulting finite presentation is not
identified with LeaTTa's binding list; their declared-return observations
are related only up to the alpha theorem for mutually principal models.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationFoldConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HumanTypePresentation
open HumanTypePresentationTheory
open HumanTypePresentationMatchSolutionTheory
open HumanTypePresentationCompleteness
open HumanTypePresentationAlpha
open HumanTypePresentationPrincipalAlpha
open HumanTypePresentationExact
open HumanTypeRuntimeRefinement
open LeaTTaBridge
open LeaTTaHumanConformance
open LeaTTaTypeConformance

/-- The exact presentation carried alongside the semantic human/LeaTTa
binding state.  `humanSolutions` is representation-independent equality of
native solution sets; it does not identify the finite substitution with the
human binding record. -/
structure TypePresentationSimulationState
    (presentation : TypeSubst) (human : Bindings)
    (lea : Metta.Bindings) : Prop where
  normal : presentation.Normal
  humanSolutions : ∀ valuation,
    TypeSubstSatisfied valuation presentation ↔
      HumanTypeBindingSatisfied valuation human
  semantic : TypeBindingState human lea

/-- Empty finite, human, and runtime presentations establish the simulation
state used at every application-inference boundary. -/
theorem typePresentationSimulationState_empty :
    TypePresentationSimulationState [] Bindings.empty
      Metta.Bindings.empty := by
  refine ⟨TypeSubst.normal_empty, ?_, typeBindingState_empty⟩
  intro valuation
  simp [TypeSubstSatisfied, HumanTypeBindingSatisfied, Bindings.empty]

/-- One successful repaired runtime type match has a normal finite
presentation with exactly the same native human solution theory. -/
theorem TypePresentationSimulationState.matchType
    {presentation : TypeSubst} {human : Bindings}
    {lea leaOutput : Metta.Bindings}
    (state : TypePresentationSimulationState presentation human lea)
    (expected actual : Atom)
    (success : Metta.Minimal.matchType lea
      (toLeaTTaAtom expected) (toLeaTTaAtom actual) = some leaOutput) :
    ∃ presentationOutput humanOutput,
      CorePlusR2TypePresentationMatchRel
          presentation expected actual presentationOutput ∧
        TypePresentationSimulationState
          presentationOutput humanOutput leaOutput := by
  obtain ⟨humanOutput, humanMatch, semanticOutput⟩ :=
    matchType_corePlusR2_sound state.semantic success
  obtain ⟨valuation, outputSatisfied⟩ :=
    semanticOutput.humanSatisfiable
  have parts := (humanMatch.solutions valuation).mp outputSatisfied
  have presentationSatisfied :
      TypeSubstSatisfied valuation presentation :=
    (state.humanSolutions valuation).mpr parts.1
  obtain ⟨presentationOutput, presentationMatch,
      outputNormal, _outputSatisfied⟩ :=
    CorePlusR2TypePresentationMatchRel.exists_of_satisfied
      state.normal presentationSatisfied expected actual parts.2
  refine ⟨presentationOutput, humanOutput, presentationMatch,
    ⟨outputNormal, ?_, semanticOutput⟩⟩
  intro otherValuation
  rw [HumanTypePresentationMatchSolutionTheory.CorePlusR2TypePresentationMatchRel.solutions
        presentationMatch state.normal otherValuation,
    state.humanSolutions otherValuation,
    ← humanMatch.solutions otherValuation]

/-- The finite presentation and LeaTTa's canonical runtime resolver observe
any declared type up to alpha-renaming. -/
theorem TypePresentationSimulationState.returnAlpha
    {presentation : TypeSubst} {human : Bindings}
    {lea : Metta.Bindings}
    (state : TypePresentationSimulationState presentation human lea)
    (declared : Atom) :
    ObservedTypeAlphaRel
      (presentation.apply declared)
      (fromLeaTTaAtom
        (Metta.instantiate lea (toLeaTTaAtom declared))) := by
  let leaModel := leaClassSolution lea
  let nativeModel : String → Atom :=
    fun name => fromLeaTTaAtom (leaModel name)
  have nativeModelSatisfied :
      TypeSubstSatisfied nativeModel presentation := by
    have humanModel : HEBindingSatisfied leaModel human :=
      (state.semantic.theory leaModel).mpr state.semantic.runtime.canonical.1
    have nativeHumanModel :=
      humanTypeBindingSatisfied_of_heBindingSatisfied humanModel
    exact (state.humanSolutions nativeModel).mpr nativeHumanModel
  have presentationRefinesModel :
      ∃ post : String → Atom, ∀ name,
        presentedValuation presentation name =
          applyTypeValuation post (nativeModel name) := by
    let presentationModel := presentedValuation presentation
    let leaPresentationModel : String → Metta.Atom :=
      fun name => toLeaTTaAtom (presentationModel name)
    have presentationSatisfied :
        TypeSubstSatisfied presentationModel presentation :=
      normal_presentedValuation_satisfied state.normal
    have humanPresentationSatisfied :
        HumanTypeBindingSatisfied presentationModel human :=
      (state.humanSolutions presentationModel).mp presentationSatisfied
    have heaPresentationSatisfied :
        HEBindingSatisfied leaPresentationModel human :=
      heBindingSatisfied_of_humanTypeBindingSatisfied
        humanPresentationSatisfied
    have leaPresentationSatisfied :
        LeaBindingSatisfied leaPresentationModel lea :=
      (state.semantic.theory leaPresentationModel).mp
        heaPresentationSatisfied
    obtain ⟨leaPost, hleaPost⟩ :=
      state.semantic.runtime.canonical.2
        leaPresentationModel leaPresentationSatisfied
    refine ⟨fun name => fromLeaTTaAtom (leaPost name), ?_⟩
    intro name
    have decoded := congrArg fromLeaTTaAtom (hleaPost name)
    rw [fromLeaTTaAtom_applyClassSolution_any] at decoded
    simpa [leaPresentationModel, presentationModel,
      nativeModel, leaModel] using decoded
  have alpha := observedTypeAlpha_of_mutuallyPrincipal state.normal
    nativeModelSatisfied presentationRefinesModel declared
  simpa [nativeModel, leaModel, ← fromLeaTTaAtom_applyClassSolution,
    applyClassSolution_lea_eq_instantiate] using alpha

/-- Repaired LeaTTa's left-to-right argument-type fold is realized by the
executable-independent finite-presentation fold, preserving the complete
simulation state. -/
theorem matchApplicationTypeArguments_presentation_sound :
    ∀ (expectedTypes actualTypes : List Atom)
      {presentation : TypeSubst} {human : Bindings}
      {lea leaOutput : Metta.Bindings},
      TypePresentationSimulationState presentation human lea →
      Metta.Minimal.matchApplicationTypeArguments lea
        (toLeaTTaAtoms expectedTypes) (toLeaTTaAtoms actualTypes) =
          some leaOutput →
      ∃ presentationOutput humanOutput,
        PresentationArgumentListMatchRel expectedTypes actualTypes
            presentation presentationOutput ∧
          TypePresentationSimulationState
            presentationOutput humanOutput leaOutput := by
  intro expectedTypes
  induction expectedTypes with
  | nil =>
      intro actualTypes presentation human lea leaOutput state success
      cases actualTypes with
      | nil =>
          have same : lea = leaOutput := by
            simpa [toLeaTTaAtoms,
              Metta.Minimal.matchApplicationTypeArguments] using success
          subst leaOutput
          exact ⟨presentation, human,
            PresentationArgumentListMatchRel.nil presentation, state⟩
      | cons actual actualTypes =>
          simp [toLeaTTaAtoms,
            Metta.Minimal.matchApplicationTypeArguments] at success
  | cons expected expectedTypes inductionHypothesis =>
      intro actualTypes presentation human lea leaOutput state success
      cases actualTypes with
      | nil =>
          simp [toLeaTTaAtoms,
            Metta.Minimal.matchApplicationTypeArguments] at success
      | cons actual actualTypes =>
          simp only [toLeaTTaAtoms,
            Metta.Minimal.matchApplicationTypeArguments] at success
          generalize nextEquation : Metta.Minimal.matchType lea
            (toLeaTTaAtom expected) (toLeaTTaAtom actual) = next at success
          cases next with
          | none => simp at success
          | some leaNext =>
              obtain ⟨presentationNext, humanNext,
                  headMatch, nextState⟩ :=
                state.matchType expected actual nextEquation
              obtain ⟨presentationOutput, humanOutput,
                  tailMatch, outputState⟩ :=
                inductionHypothesis actualTypes nextState success
              exact ⟨presentationOutput, humanOutput,
                PresentationArgumentListMatchRel.cons headMatch tailMatch,
                outputState⟩

/-- End-to-end fold boundary from empty input: the exact human argument
presentation exists, and its emitted return is alpha-exactly LeaTTa's
instantiated return. -/
theorem matchApplicationTypeArguments_exact_return
    {expectedTypes actualTypes : List Atom}
    {leaOutput : Metta.Bindings} {returnType : Atom}
    (success : Metta.Minimal.matchApplicationTypeArguments
      Metta.Bindings.empty (toLeaTTaAtoms expectedTypes)
        (toLeaTTaAtoms actualTypes) = some leaOutput) :
    ∃ presentation humanOutput,
      PresentationArgumentListMatchRel
          expectedTypes actualTypes [] presentation ∧
        TypePresentationSimulationState
          presentation humanOutput leaOutput ∧
        ObservedTypeAlphaRel
          (presentation.apply returnType)
          (fromLeaTTaAtom
            (Metta.instantiate leaOutput (toLeaTTaAtom returnType))) := by
  obtain ⟨presentation, humanOutput, fold, state⟩ :=
    matchApplicationTypeArguments_presentation_sound
      expectedTypes actualTypes typePresentationSimulationState_empty success
  exact ⟨presentation, humanOutput, fold, state,
    state.returnAlpha returnType⟩

/-! ## Boundary examples -/

/-- Positive: the empty application fold produces the empty exact
presentation and preserves its simulation state. -/
theorem empty_application_fold_exact :
    ∃ presentation humanOutput,
      PresentationArgumentListMatchRel [] [] [] presentation ∧
        TypePresentationSimulationState presentation humanOutput
          Metta.Bindings.empty := by
  exact ⟨[], Bindings.empty,
    PresentationArgumentListMatchRel.nil [],
    typePresentationSimulationState_empty⟩

/-- Negative: unequal argument arities admit no presentation derivation. -/
theorem unequal_arity_has_no_presentation
    (expected : Atom) :
    ¬∃ output,
      PresentationArgumentListMatchRel [expected] [] [] output := by
  rintro ⟨output, derivation⟩
  cases derivation

end Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationFoldConformance
