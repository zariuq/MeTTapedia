import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ScopeObservation
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.MatchSolutionTheory

/-!
# Matching independently private alpha presentations

An evaluator may select one private spelling of a type and later present the
same source type under a second, independently fresh spelling.  This module
constructs a genuine finite-presentation match between those siblings while
preserving an existing normal presentation.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.PrivateAlphaMatch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Alpha
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Completeness
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.MatchSolutionTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ScopeObservation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Theory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement

/-- Two independently alpha-presented copies of one type admit a finite
match over any model of a normal incoming presentation.  The constructed
model changes only variables of the second copy, so it preserves every
explicitly protected name. -/
theorem exists_match_of_alpha_fresh_from_model
    {incoming : TypeSubst} {expected actual : Atom}
    {base : String → Atom} {protectedScope : List String}
    (normal : incoming.Normal)
    (baseSatisfied : TypeSubstSatisfied base incoming)
    (alpha : ObservedTypeAlphaRel expected actual)
    (separated : ∀ name, name ∈ TypeSubst.typeVars expected →
      name ∉ TypeSubst.typeVars actual)
    (actualFreshIncoming : ∀ name,
      name ∈ TypeSubst.typeVars actual →
      name ∉ specBindingVars (⟨incoming, []⟩ : Bindings))
    (actualFreshProtected : ∀ name,
      name ∈ TypeSubst.typeVars actual → name ∉ protectedScope) :
    ∃ output model,
      CorePlusR2TypePresentationMatchRel incoming expected actual output ∧
        output.Normal ∧ TypeSubstSatisfied model output ∧
          ValuationsAgreeOn protectedScope base model := by
  obtain ⟨permutation, actualEquation⟩ :=
    ObservedTypeAlphaRel.exists_permutation alpha
  let model : String → Atom := fun name =>
    if name ∈ TypeSubst.typeVars actual
    then base (permutation.symm name)
    else base name
  have agreesIncoming : ValuationsAgreeOn
      (specBindingVars (⟨incoming, []⟩ : Bindings)) base model := by
    intro name member
    have notActual : name ∉ TypeSubst.typeVars actual := by
      intro actualMember
      exact actualFreshIncoming name actualMember member
    simp [model, notActual]
  have incomingSatisfied : TypeSubstSatisfied model incoming :=
    (typeSubstSatisfied_congr_of_presentationVars agreesIncoming).mp
      baseSatisfied
  have agreesProtected : ValuationsAgreeOn protectedScope base model := by
    intro name member
    have notActual : name ∉ TypeSubst.typeVars actual := by
      intro actualMember
      exact actualFreshProtected name actualMember member
    simp [model, notActual]
  have corresponding : ∀ name, name ∈ TypeSubst.typeVars expected →
      model name = model (permutation name) := by
    intro name member
    have leftNotActual : name ∉ TypeSubst.typeVars actual :=
      separated name member
    have rightActual : permutation name ∈ TypeSubst.typeVars actual := by
      rw [actualEquation, typeVars_renameTypeVars]
      exact List.mem_map.mpr ⟨name, member, rfl⟩
    simp [model, leftNotActual, rightActual]
  have consistent : CorePlusR2TypeConsistent model expected actual := by
    have renamed := corePlusR2TypeConsistent_two_renames
      model id permutation expected (by
        intro name member
        simpa using corresponding name member)
    simpa [renameTypeVars_id, actualEquation] using renamed
  obtain ⟨output, derivation, outputNormal, outputSatisfied⟩ :=
    CorePlusR2TypePresentationMatchRel.exists_of_satisfied normal
      incomingSatisfied expected actual consistent
  exact ⟨output, model, derivation, outputNormal, outputSatisfied,
    agreesProtected⟩

/-- Two independently alpha-presented copies of one type admit a finite
match over any normal incoming presentation, provided the second copy is
fresh from both the first copy and the complete incoming support. -/
theorem exists_match_of_alpha_fresh
    {incoming : TypeSubst} {expected actual : Atom}
    (normal : incoming.Normal)
    (alpha : ObservedTypeAlphaRel expected actual)
    (separated : ∀ name, name ∈ TypeSubst.typeVars expected →
      name ∉ TypeSubst.typeVars actual)
    (actualFresh : ∀ name, name ∈ TypeSubst.typeVars actual →
      name ∉ specBindingVars (⟨incoming, []⟩ : Bindings)) :
    ∃ output,
      CorePlusR2TypePresentationMatchRel incoming expected actual output ∧
        output.Normal := by
  obtain ⟨output, _model, derivation, outputNormal,
      _outputSatisfied, _agrees⟩ :=
    exists_match_of_alpha_fresh_from_model normal
      (normal_presentedValuation_satisfied normal) alpha separated actualFresh
      (protectedScope := []) (by simp)
  exact ⟨output, derivation, outputNormal⟩

/-- Replacing an exact incoming presentation by its abstract binding theory
does not change a finite presentation match.  The output uses the canonical
binding carrier of the selected finite presentation. -/
theorem CorePlusR2TypePresentationMatchRel.to_exact_binding_match
    {incoming output : TypeSubst} {expected actual : Atom}
    {bindings : Bindings}
    (normal : incoming.Normal)
    (derivation : CorePlusR2TypePresentationMatchRel
      incoming expected actual output)
    (exactIncoming : ∀ valuation,
      TypeSubstSatisfied valuation incoming ↔
        TypeBindingSatisfied valuation bindings) :
    CorePlusR2TypeMatchRel expected actual bindings
      (typeSubstAsBindings output) := by
  constructor
  · obtain ⟨valuation, satisfied⟩ :=
      corePlusR2_output_satisfiable derivation normal
    exact ⟨valuation,
      (typeBindingSatisfied_asBindings_iff valuation output).mpr satisfied⟩
  · intro valuation
    rw [typeBindingSatisfied_asBindings_iff,
      CorePlusR2TypePresentationMatchRel.solutions derivation normal,
      exactIncoming valuation]

/-- Matching two independently private alpha spellings adds no observation
on a scope avoided by the second spelling.  Exactness remains intra-side:
the incoming presentation denotes `bindings` literally, while the crossing
claim is scoped model equivalence. -/
theorem CorePlusR2TypePresentationMatchRel.alpha_fresh_observationally_inert
    {incoming output : TypeSubst} {expected actual : Atom}
    {bindings : Bindings} {scope : List String}
    (normal : incoming.Normal)
    (derivation : CorePlusR2TypePresentationMatchRel
      incoming expected actual output)
    (exactIncoming : ∀ valuation,
      TypeSubstSatisfied valuation incoming ↔
        TypeBindingSatisfied valuation bindings)
    (alpha : ObservedTypeAlphaRel expected actual)
    (separated : ∀ name, name ∈ TypeSubst.typeVars expected →
      name ∉ TypeSubst.typeVars actual)
    (actualFreshIncoming : ∀ name,
      name ∈ TypeSubst.typeVars actual →
      name ∉ specBindingVars (⟨incoming, []⟩ : Bindings))
    (actualFreshScope : ∀ name,
      name ∈ TypeSubst.typeVars actual → name ∉ scope) :
    BindingTheoryEquivAt scope bindings (typeSubstAsBindings output) := by
  obtain ⟨permutation, actualEquation⟩ :=
    ObservedTypeAlphaRel.exists_permutation alpha
  constructor
  · intro base baseSatisfied
    let model : String → Atom := fun name =>
      if name ∈ TypeSubst.typeVars actual
      then base (permutation.symm name)
      else base name
    have agreesIncoming : ValuationsAgreeOn
        (specBindingVars (⟨incoming, []⟩ : Bindings)) base model := by
      intro name member
      have notActual : name ∉ TypeSubst.typeVars actual := by
        intro actualMember
        exact actualFreshIncoming name actualMember member
      simp [model, notActual]
    have incomingSatisfied : TypeSubstSatisfied model incoming :=
      (typeSubstSatisfied_congr_of_presentationVars agreesIncoming).mp
        ((exactIncoming base).mpr baseSatisfied)
    have corresponding : ∀ name, name ∈ TypeSubst.typeVars expected →
        model name = model (permutation name) := by
      intro name member
      have leftNotActual : name ∉ TypeSubst.typeVars actual :=
        separated name member
      have rightActual : permutation name ∈ TypeSubst.typeVars actual := by
        rw [actualEquation, typeVars_renameTypeVars]
        exact List.mem_map.mpr ⟨name, member, rfl⟩
      simp [model, leftNotActual, rightActual]
    have consistent : CorePlusR2TypeConsistent model expected actual := by
      have renamed := corePlusR2TypeConsistent_two_renames
        model id permutation expected (by
          intro name member
          simpa using corresponding name member)
      simpa [renameTypeVars_id, actualEquation] using renamed
    have outputSatisfied : TypeSubstSatisfied model output :=
      (CorePlusR2TypePresentationMatchRel.solutions
        derivation normal model).mpr ⟨incomingSatisfied, consistent⟩
    refine ⟨model,
      (typeBindingSatisfied_asBindings_iff model output).mpr outputSatisfied,
      ?_⟩
    intro name member
    have notActual : name ∉ TypeSubst.typeVars actual := by
      intro actualMember
      exact actualFreshScope name actualMember member
    simp [model, notActual]
  · intro model outputSatisfied
    have outputSatisfied' : TypeSubstSatisfied model output :=
      (typeBindingSatisfied_asBindings_iff model output).mp outputSatisfied
    have incomingSatisfied :=
      (CorePlusR2TypePresentationMatchRel.solutions
        derivation normal model).mp outputSatisfied' |>.1
    exact ⟨model, (exactIncoming model).mp incomingSatisfied,
      fun _ _ => rfl⟩

/-! ## Boundary canaries -/

/-- Positive: two distinct private spellings of one variable match from the
empty presentation. -/
example : ∃ output,
    CorePlusR2TypePresentationMatchRel [] (.var "left") (.var "right")
      output := by
  have alpha : ObservedTypeAlphaRel (.var "left") (.var "right") :=
    ⟨.var "source",
      ⟨Equiv.swap "source" "left", (Equiv.swap "source" "left").injective,
        by simp [renameTypeVars]⟩,
      ⟨Equiv.swap "source" "right", (Equiv.swap "source" "right").injective,
        by simp [renameTypeVars]⟩⟩
  obtain ⟨output, derivation, _normal⟩ :=
    exists_match_of_alpha_fresh (incoming := []) TypeSubst.normal_empty alpha
      (by simp [TypeSubst.typeVars])
      (by simp [specBindingVars, TypeSubst.typeVars])
  exact ⟨output, derivation⟩

/-- Negative: the freshness premise cannot be discarded when the two private
spellings collide. -/
example : ¬(∀ name, name ∈ TypeSubst.typeVars (.var "same") →
    name ∉ TypeSubst.typeVars (.var "same")) := by
  simp [TypeSubst.typeVars]

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.PrivateAlphaMatch
