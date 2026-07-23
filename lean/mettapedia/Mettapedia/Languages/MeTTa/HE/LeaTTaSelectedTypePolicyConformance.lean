import Mettapedia.Languages.MeTTa.HE.Spec.Type.CandidateLocalization
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationFoldConformance

/-!
# Selected type-policy correspondence

This module connects repaired LeaTTa's private application-type binding fold
to the evaluator-visible specification binding state.  It deliberately states
the agreement fragment shared by the literal published applicability rule and
the current runtime: an expected return of `%Undefined%` or `Atom`.

The runtime keeps its type bindings in the selected policy and instantiates
the selected return with them.  The specification threads the corresponding
finite presentation into its ordinary binding carrier.  That presentation
may bind caller-visible variables, so the general success boundary records
exact solution-theory conjunction.  Scoped observational inertness remains a
separate theorem for the genuinely private fragment.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaSelectedTypePolicyConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Bindings.ScopeObservation
open Spec.Eval
open Spec.Type.CandidateLocalization
open Spec.Type.Presentation
open Spec.Type.Presentation.Alpha
open Spec.Type.Presentation.Exact
open Spec.Type.Presentation.Freshness
open LeaTTaBridge
open LeaTTaTypeConformance
open LeaTTaTypePresentationFoldConformance

/-- A successful argument fold followed by the repaired raw-return gate has
one exact finite-presentation derivation.  Both sides inspect wildcard syntax
before applying the threaded presentation, so the final step uses the declared
return directly rather than an eagerly instantiated image. -/
theorem matchApplicationTypeArguments_expectedGate_presentation_sound
    {expectedTypes actualTypes : List Atom}
    {expectedType returnType : Atom}
    {argumentBindings output : Metta.Bindings}
    (arguments : Metta.Minimal.matchApplicationTypeArguments
      Metta.Bindings.empty (toLeaTTaAtoms expectedTypes)
        (toLeaTTaAtoms actualTypes) = some argumentBindings)
    (returnGate : Metta.Minimal.matchType argumentBindings
      (toLeaTTaAtom expectedType)
      (toLeaTTaAtom returnType) = some output) :
    ∃ presentation specOutput,
      PresentationArgumentListMatchRel
        (expectedTypes ++ [expectedType])
        (actualTypes ++ [returnType])
        [] presentation ∧
      TypePresentationSimulationState presentation specOutput output := by
  obtain ⟨argumentPresentation, argumentBindingOutput, argumentFold,
      argumentState⟩ :=
    matchApplicationTypeArguments_presentation_sound
      expectedTypes actualTypes typePresentationSimulationState_empty
        arguments
  obtain ⟨presentation, specOutput, returnPresentation, outputState⟩ :=
    argumentState.matchType expectedType returnType returnGate
  exact ⟨presentation, specOutput,
    presentationArgumentList_appendOne argumentFold returnPresentation,
    outputState⟩

/-- The repaired expected-return gate yields the exact specification-side
private extension for an arbitrary expected return.  The selected return is
observed only up to private alpha names; the evaluator-visible binding carrier
is the canonical incoming record extended by the finite presentation. -/
theorem matchApplicationTypeArguments_localized_expected
    {scope : List String} {incoming : Bindings}
    {expectedType : Atom} {actualTypes : List Atom}
    {policy : SelectedTypePolicy}
    {argumentBindings output : Metta.Bindings}
    (arguments : Metta.Minimal.matchApplicationTypeArguments
      Metta.Bindings.empty (toLeaTTaAtoms policy.argumentTypes)
        (toLeaTTaAtoms actualTypes) = some argumentBindings)
    (returnGate : Metta.Minimal.matchType argumentBindings
      (toLeaTTaAtom expectedType) (toLeaTTaAtom policy.returnType) =
        some output)
    (expectedFresh : AtomsAvoid
      (policy.argumentTypes ++ [expectedType])
      (scope ++ specBindingVars incoming))
    (actualFresh : AtomsAvoid
      (actualTypes ++ [policy.returnType])
      (scope ++ specBindingVars incoming)) :
    ∃ substitution,
      LocalizedSelectedTypePolicyRel scope incoming expectedType actualTypes
        policy substitution
        ⟨incoming.assignments ++ substitution, incoming.equalities⟩ ∧
      ObservedTypeAlphaRel
        (substitution.apply policy.returnType)
        (fromLeaTTaAtom
          (Metta.instantiate output (toLeaTTaAtom policy.returnType))) := by
  obtain ⟨substitution, _specOutput, constraints, state⟩ :=
    matchApplicationTypeArguments_expectedGate_presentation_sound
      arguments returnGate
  exact ⟨substitution,
    LocalizedSelectedTypePolicyRel.ofFold
      constraints expectedFresh actualFresh,
    state.returnAlpha policy.returnType⟩

/-- The arbitrary-expected gate exposes the complete scan-success boundary:
one finite presentation, one specification output carrier, and the
independent solution-theory bridge to LeaTTa's selected binding record.
Unlike the private-localization theorem, this result permits the presentation
to bind variables visible in the expected type or application. -/
theorem matchApplicationTypeArguments_expected_scanSuccessCorrespond
    {incoming : Bindings}
    {expectedType : Atom} {actualTypes : List Atom}
    {policy : SelectedTypePolicy}
    {argumentBindings leaTypeBindings : Metta.Bindings}
    (arguments : Metta.Minimal.matchApplicationTypeArguments
      Metta.Bindings.empty (toLeaTTaAtoms policy.argumentTypes)
        (toLeaTTaAtoms actualTypes) = some argumentBindings)
    (returnGate : Metta.Minimal.matchType argumentBindings
      (toLeaTTaAtom expectedType) (toLeaTTaAtom policy.returnType) =
        some leaTypeBindings) :
    ∃ substitution output,
      output =
        ⟨incoming.assignments ++ substitution, incoming.equalities⟩ ∧
      PresentationExtensionRel incoming substitution output ∧
      (∃ privateBindings,
        TypePresentationSimulationState substitution privateBindings
          leaTypeBindings) ∧
      ObservedTypeAlphaRel
        (substitution.apply policy.returnType)
        (fromLeaTTaAtom
          (Metta.instantiate leaTypeBindings
            (toLeaTTaAtom policy.returnType))) := by
  obtain ⟨substitution, privateBindings, constraints, state⟩ :=
    matchApplicationTypeArguments_expectedGate_presentation_sound
      arguments returnGate
  let output : Bindings :=
    ⟨incoming.assignments ++ substitution, incoming.equalities⟩
  exact ⟨substitution, output, rfl,
    presentationExtension_append incoming substitution,
    ⟨privateBindings, state⟩, state.returnAlpha policy.returnType⟩

/-- A successful repaired runtime argument fold yields the exact
specification-side private extension in the unconstrained-return fragment,
and its selected return presentation is alpha-exact with the runtime's
private instantiation. -/
theorem matchApplicationTypeArguments_localized_unconstrained
    {scope : List String} {incoming : Bindings}
    {expectedType : Atom} {actualTypes : List Atom}
    {policy : SelectedTypePolicy} {leaOutput : Metta.Bindings}
    (run : Metta.Minimal.matchApplicationTypeArguments
      Metta.Bindings.empty (toLeaTTaAtoms policy.argumentTypes)
        (toLeaTTaAtoms actualTypes) = some leaOutput)
    (unconstrained : ExpectedReturnUnconstrained expectedType)
    (expectedFresh : AtomsAvoid
      (policy.argumentTypes ++ [expectedType])
      (scope ++ specBindingVars incoming))
    (actualFresh : AtomsAvoid
      (actualTypes ++ [policy.returnType])
      (scope ++ specBindingVars incoming)) :
    ∃ substitution,
      LocalizedSelectedTypePolicyRel scope incoming expectedType actualTypes
        policy substitution
        ⟨incoming.assignments ++ substitution, incoming.equalities⟩ ∧
      ObservedTypeAlphaRel
        (substitution.apply policy.returnType)
        (fromLeaTTaAtom
          (Metta.instantiate leaOutput
            (toLeaTTaAtom policy.returnType))) := by
  obtain ⟨substitution, _specOutput, fold, _state, returnAlpha⟩ :=
    matchApplicationTypeArguments_exact_return
      (returnType := policy.returnType) run
  exact ⟨substitution,
    LocalizedSelectedTypePolicyRel.ofArgumentFold
      fold unconstrained expectedFresh actualFresh,
    returnAlpha⟩

/-- The specification binding carrier recovered from a successful private
runtime fold is observationally identical to the caller state on the declared
public scope. -/
theorem matchApplicationTypeArguments_scoped_inert
    {scope : List String} {incoming : Bindings}
    {expectedType : Atom} {actualTypes : List Atom}
    {policy : SelectedTypePolicy} {leaOutput : Metta.Bindings}
    (run : Metta.Minimal.matchApplicationTypeArguments
      Metta.Bindings.empty (toLeaTTaAtoms policy.argumentTypes)
        (toLeaTTaAtoms actualTypes) = some leaOutput)
    (unconstrained : ExpectedReturnUnconstrained expectedType)
    (expectedFresh : AtomsAvoid
      (policy.argumentTypes ++ [expectedType])
      (scope ++ specBindingVars incoming))
    (actualFresh : AtomsAvoid
      (actualTypes ++ [policy.returnType])
      (scope ++ specBindingVars incoming)) :
    ∃ substitution,
      BindingTheoryEquivAt scope incoming
        ⟨incoming.assignments ++ substitution, incoming.equalities⟩ := by
  obtain ⟨substitution, localized, _returnAlpha⟩ :=
    matchApplicationTypeArguments_localized_unconstrained
      run unconstrained expectedFresh actualFresh
  exact ⟨substitution, localized.scopedInert⟩

/-! ## Boundary canaries -/

private def closedPolicy : SelectedTypePolicy :=
  ⟨.expression [.symbol "->", .symbol "R"], [], .symbol "R", rfl⟩

/-- Positive: an empty runtime argument fold recovers an inert empty private
presentation and the literal selected return. -/
theorem empty_runtime_fold_localizes :
    ∃ substitution,
      LocalizedSelectedTypePolicyRel [] Bindings.empty Atom.undefinedType []
        closedPolicy substitution
        ⟨Bindings.empty.assignments ++ substitution,
          Bindings.empty.equalities⟩ ∧
      ObservedTypeAlphaRel (substitution.apply (.symbol "R"))
        (fromLeaTTaAtom
          (Metta.instantiate Metta.Bindings.empty (.sym "R"))) := by
  apply matchApplicationTypeArguments_localized_unconstrained
      (policy := closedPolicy) (leaOutput := Metta.Bindings.empty)
  · rfl
  · exact Or.inl rfl
  · simp [closedPolicy, AtomsAvoid, specBindingVars, Bindings.empty]
  · simp [closedPolicy, AtomsAvoid, specBindingVars, Bindings.empty]

end Mettapedia.Languages.MeTTa.HE.LeaTTaSelectedTypePolicyConformance
