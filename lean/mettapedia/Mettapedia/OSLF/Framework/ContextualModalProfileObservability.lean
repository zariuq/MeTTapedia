import Mettapedia.OSLF.Framework.ContextualModalSignatureCompiler
import Mettapedia.OSLF.Framework.SelectedNativeTypeDemand

/-!
# Signature projection and contextual modal profiles

The selected native-type demand retains a local `star`/`box` choice at every
contextual slot.  This module pins the current compiler boundary with one
fully grounded, non-root rewrite occurrence.

The two endpoint demands are observably different before generation, while
their profile-free foundations are equal. The contextual-signature compiler
therefore emits the same flat signature for both by design: its job is to
declare the contextual telescope shared by every local hypercube assignment.

The later native-type proof-calculus generator has a different obligation. It
must consume the complete profiled demand and distinguish these endpoints in
the generated formation/introduction/elimination rules. These theorems pin the
boundary so signature projection cannot be mistaken for full NTT generation.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

namespace ContextualModalProfileObservability

abbrev source : ValidatedLanguageDef :=
  ContextualModalSignature.Canary.source

abbrev typing : DisplayedRewriteTyping source :=
  ContextualModalSignature.Canary.middleTyping

/-- The concrete middle occurrence is grounded entirely in its source term
sort, including both fixed-context dependencies. -/
theorem typing_grounded :
    SelectedNativeTypeFoundation.CarrierGrounded typing := by
  intro object objectMembership name nameMembership
  have termNameDeclared :
      ContextualModalSignature.Canary.termType.name ∈
        source.language.typeNames := by
    simp [source, ContextualModalSignature.Canary.source,
      ContextualModalSignature.Canary.sourceLanguage,
      ContextualModalSignature.Canary.termType, LanguageDef.typeNames]
  simp [SelectedNativeTypeFoundation.requiredCarrierRoots,
    typing, ContextualModalSignature.Canary.middleTyping,
    DisplayedContextProfile.carrierTypes]
    at objectMembership
  rcases objectMembership with direct | contextual
  · subst object
    have nameEquality :
        name = ContextualModalSignature.Canary.termType.name := by
      simpa [TypeExpr.baseNames] using nameMembership
    subst name
    exact termNameDeclared
  · obtain ⟨binderName, membership⟩ := contextual
    change (binderName, object) ∈
      DisplayedContextProfile.bindings typing at membership
    rw [ContextualModalSignature.Canary.middle_occurrence_dependencies_exact]
      at membership
    simp only [List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false] at membership
    rcases membership with ⟨_, objectEquality⟩ | ⟨_, objectEquality⟩
    all_goals
      subst object
      have nameEquality :
          name = ContextualModalSignature.Canary.termType.name := by
        simpa [TypeExpr.baseNames] using nameMembership
      subst name
      exact termNameDeclared

/-- One genuinely contextual, grounded occurrence is enough to expose the
profile-erasure boundary. -/
def singletonFoundation : SelectedNativeTypeFoundation.Demand source where
  typings := [typing]
  grounded := by
    intro selected membership
    have equality : selected = typing := List.mem_singleton.mp membership
    subst selected
    exact typing_grounded

def allStar : SelectedNativeTypeDemand source :=
  SelectedNativeTypeDemand.constant singletonFoundation .star

def allBox : SelectedNativeTypeDemand source :=
  SelectedNativeTypeDemand.constant singletonFoundation .box

/-- The authored endpoint demands are genuinely different. -/
theorem demands_distinct : allStar ≠ allBox :=
  SelectedNativeTypeDemand.constant_singleton_star_ne_box
    singletonFoundation typing rfl

/-- Their stable profile wires are already distinguishable before running a
generator. -/
theorem profile_wires_distinct : allStar.choices ≠ allBox.choices := by
  exact SelectedNativeTypeDemand.constant_singleton_choices_star_ne_box
    singletonFoundation typing rfl

/-- Signature projection intentionally identifies demands with the same
profile-free grounded typing foundation. -/
theorem signature_projection_identifies_profiles :
    ContextualModalSignatureCompiler.definition allStar.foundation =
      ContextualModalSignatureCompiler.definition allBox.foundation := by
  simp [allStar, allBox]

/-- Every observation of the shared signature consequently identifies these
two endpoint profiles. The proof-calculus output must not. -/
theorem every_signature_observation_identifies_profiles {Observation : Sort _}
    (observe : CalculusLanguageDef → Observation) :
    observe (ContextualModalSignatureCompiler.definition allStar.foundation) =
      observe (ContextualModalSignatureCompiler.definition allBox.foundation) :=
  congrArg observe signature_projection_identifies_profiles

/-- The negative result is not caused by empty input: the selected occurrence
generates a nonempty constructor theory. -/
theorem generated_terms_nonempty :
    (ContextualModalSignatureCompiler.definition allStar.foundation).terms ≠
      [] := by
  intro empty
  have lengths :=
    (ContextualModalSignatureCompiler.definition_constructorPermutation_grouped
      allStar.foundation).terms.length_eq
  rw [empty, ContextualModalExtension.language_terms, List.length_append,
    ContextualModalExtension.length_modalTerms] at lengths
  simp [allStar, singletonFoundation] at lengths

/-- The concrete generated output passes the ordinary structural language
gate. -/
theorem generated_language_valid :
    (ContextualModalSignatureCompiler.definition
      allStar.foundation).toLanguageDef.validate = [] :=
  ContextualModalSignatureCompiler.definition_language_validate
    allStar.foundation

#print axioms typing_grounded
#print axioms demands_distinct
#print axioms profile_wires_distinct
#print axioms signature_projection_identifies_profiles
#print axioms every_signature_observation_identifies_profiles
#print axioms generated_terms_nonempty
#print axioms generated_language_valid

end ContextualModalProfileObservability

end Mettapedia.OSLF.Framework
