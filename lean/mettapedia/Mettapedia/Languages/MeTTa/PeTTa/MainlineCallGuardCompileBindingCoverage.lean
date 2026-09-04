import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileActivationClaim
import Mettapedia.OSLF.Framework.SelectedNativeTypeSourceMatchBinding

/-!
# Matcher-derived premise binding coverage for the cold call guard

Every relation premise selected from the cold compiler uses only variables
occurring in its exact authored rewrite source.  The ordinary cold matcher
therefore supplies the complete ordered argument row before premise
execution begins.  This module proves that statement uniformly for all
thirty selected star/box endpoints and removes the residual binding-coverage
hypothesis from the generated-claim factorization.

No relation answer, target state, or successful guard result is used to
construct the coverage evidence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileBindingCoverage

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationPremise
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationEvidence
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationClaim
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceMatchBinding
open Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedOccurrenceSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompilePremiseProfile
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompilePremiseClaim
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileActivationClaim

/-- One exact selected star/box occurrence of the cold compiler. -/
abbrev Occurrence :=
  SelectedNativeTypeContextualCalculus.Occurrence demand

/-- Every authored cold source pattern is a hole skeleton.  This finite fact
is checked once at the fifteen source roots; endpoint duplication does not
create a second pattern proof. -/
theorem root_left_holeSkeleton
    (index : Fin coldSource.language.rewrites.length) :
    patternHoleSkeleton (rootTyping index).site.rewrite.left = true := by
  fin_cases index <;> decide +kernel

/-- Every decoded selected premise argument is a variable from the exact
authored rewrite source. -/
theorem selected_view_sourceBound (slot : Occurrence)
    (view : SelectedNativeTypeBoundRelationPremise.View
      (typingAt demand slot).site.rewrite)
    (member : view ∈ viewsAt premiseProfile slot) :
    ∀ argument ∈ view.arguments,
      ArgumentSourceBound (typingAt demand slot).site.rewrite argument := by
  have allBound :
      PremisesSourceBound (typingAt demand slot).site.rewrite := by
    rw [typingAt_eq_rootTyping]
    exact rootPremises_sourceBound _
  have encodedMember :
      view.encode ∈ (typingAt demand slot).site.rewrite.premises := by
    rw [← viewsAt_encoded premiseProfile slot]
    exact List.mem_map_of_mem member
  obtain ⟨relation, arguments, encodedEq, argumentsBound⟩ :=
    allBound view.encode encodedMember
  cases view with
  | mk viewRelation viewArguments viewTypes =>
      simp only [SelectedNativeTypeBoundRelationPremise.View.encode,
        Premise.relationQuery.injEq] at encodedEq
      rcases encodedEq with ⟨relationEq, argumentsEq⟩
      subst relation
      subst arguments
      exact argumentsBound

/-- Every actual source-match environment covers every variable that an
authored selected premise may inspect. -/
theorem selected_match_covers (slot : Occurrence) (before : Pattern)
    (activation : SelectedOccurrenceActivation relationEnv
      (typingAt demand slot) before) :
    ∀ name ∈ (typingAt demand slot).site.rewrite.left.freeFvarNames,
      (Bindings.lookup activation.initialBindings name).isSome := by
  have hole : patternHoleSkeleton
      (typingAt demand slot).site.rewrite.left = true := by
    rw [typingAt_eq_rootTyping]
    exact root_left_holeSkeleton _
  have matched := activation.matched
  rw [matchPatternForRule_eq_syntactic] at matched
  exact matchPattern_holeSkeleton_covers hole
    activation.initialBindings matched

/-- All thirty selected endpoints satisfy premise-binding coverage at every
source state.  The construction uses only the source matcher and the literal
source-bound premise profile. -/
noncomputable def premiseBindingCoverage (slot : Occurrence)
    (before : Pattern) :
    PremiseBindingCoverage slot before := by
  intro activation view member
  exact BoundArguments.ofSourceBound
    (selected_view_sourceBound slot view member)
    (selected_match_covers slot before activation)

/-- The generated premise-claim activation relation is exactly the
occurrence-indexed behavioral meaning, without a caller-supplied coverage
hypothesis. -/
theorem occurrenceMeaning_iff_claimedOccursAt_exact
    (slot : Occurrence) (before after : Pattern) :
    Mettapedia.OSLF.Framework.SelectedNativeTypeOccurrenceStepClaim.View.Meaning
      relationEnv { occurrence := slot, before := before, after := after } ↔
      ClaimedOccursAt slot before after :=
  occurrenceMeaning_iff_claimedOccursAt slot before after
    (premiseBindingCoverage slot before)

/-! ## Discriminating controls -/

namespace Canary

/-- The checked-input root is guarded by a genuine relation premise. -/
private abbrev checkedInputStar : Occurrence :=
  ⟨16, by
    change 16 < selectedOccurrences.length
    rw [selectedOccurrences_count]
    decide⟩

/-- A matcher environment for a guarded source occurrence binds the complete
generated query row before any relation answer is considered. -/
theorem checkedInput_match_binds_selected_premise
    (before : Pattern) (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language
      (typingAt demand checkedInputStar).site.rewrite before)
    (view : SelectedNativeTypeBoundRelationPremise.View
      (typingAt demand checkedInputStar).site.rewrite)
    (member : view ∈ viewsAt premiseProfile checkedInputStar) :
    Nonempty (BoundArguments view bindings) := by
  apply BoundArguments.nonempty_ofSourceBound
  · exact selected_view_sourceBound checkedInputStar view member
  · have hole : patternHoleSkeleton
        (typingAt demand checkedInputStar).site.rewrite.left = true := by
      rw [typingAt_eq_rootTyping]
      exact root_left_holeSkeleton _
    rw [matchPatternForRule_eq_syntactic] at matched
    exact matchPattern_holeSkeleton_covers hole bindings matched

end Canary

#print axioms root_left_holeSkeleton
#print axioms selected_view_sourceBound
#print axioms selected_match_covers
#print axioms premiseBindingCoverage
#print axioms occurrenceMeaning_iff_claimedOccursAt_exact
#print axioms Canary.checkedInput_match_binds_selected_premise

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileBindingCoverage
