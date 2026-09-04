import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompilePremiseEvidence
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT
import Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationClaim

/-!
# Generated premise claims for the cold PeTTa call-guard compiler

The fifteen authored cold transitions contain seven guarded relation queries.
The selected native-type demand contains both universe endpoints for each
transition, so this module generates fourteen occurrence-and-position-indexed
formula constructors directly from the source premise rows.

These formulas carry questions, not answers.  Their independent meaning is
membership in the actual cold `relationEnv`, and the crown theorem proves that
the complete ordered formula row is exactly the existing proof-relevant
`PremisesAt` boundary for the same source occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompilePremiseClaim

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationPremise
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationEvidence
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationClaim
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompilePremiseEvidence

/-- Every selected star/box occurrence computes a complete ordered premise
view from its exact authored root. -/
theorem selectedViews?_isSome
    (slot : SelectedNativeTypeContextualCalculus.Occurrence demand) :
    (decodeViews? (typingAt demand slot).site.rewrite).isSome = true := by
  rw [typingAt_eq_rootTyping]
  exact rootViews?_isSome (rootIndexAt slot)

/-- Exact source-computed premise profile consumed by shared claim generation.
It contains only decoder-success evidence, never query truth. -/
def premiseProfile : Profile demand where
  supported := selectedViews?_isSome

/-- Both universe endpoints inherit the same authored premise count. -/
theorem selectedPremiseCount
    (slot : SelectedNativeTypeContextualCalculus.Occurrence demand) :
    (viewsAt premiseProfile slot).length =
      (rootTyping (rootIndexAt slot)).site.rewrite.premises.length := by
  calc
    _ = (typingAt demand slot).site.rewrite.premises.length := by
      simpa using congrArg List.length
        (viewsAt_encoded premiseProfile slot)
    _ = _ := by rw [typingAt_eq_rootTyping]

/-- Exactly fourteen premise constructors are generated: seven guarded cold
roots, each selected once at star and once at box. -/
theorem generatedPremiseTerm_count :
    (terms premiseProfile).length = 14 := by
  rw [length_terms]
  simp_rw [selectedPremiseCount]
  decide +kernel

/-- Generated premise labels remain in the private constructor namespace. -/
theorem generatedPremiseLabels_private :
    ∀ name ∈ (terms premiseProfile).map GrammarRule.label,
      name.toList.head? = some '$' := by
  exact termLabels_private premiseProfile

/-- A decoded selected view inherits relation authority from its exact authored
root occurrence.  This transports only premise membership; it does not cast or
identify the dependent view carriers of the two presentations. -/
theorem selectedView_supported
    (slot : SelectedNativeTypeContextualCalculus.Occurrence demand)
    {view : SelectedNativeTypeBoundRelationPremise.View
      (typingAt demand slot).site.rewrite}
    (membership : view ∈ viewsAt premiseProfile slot) :
    SupportedRelation view.relation := by
  have authored :
      view.encode ∈ (typingAt demand slot).site.rewrite.premises := by
    rw [← viewsAt_encoded premiseProfile slot]
    exact List.mem_map_of_mem membership
  have rootAuthored :
      view.encode ∈
        (rootTyping (rootIndexAt slot)).site.rewrite.premises := by
    simpa only [typingAt_eq_rootTyping] using authored
  have supported := rootPremises_useSupportedRelations (rootIndexAt slot)
    view.encode rootAuthored
  simpa [PremiseUsesSupportedRelation,
    SelectedNativeTypeBoundRelationPremise.View.encode] using supported

/-- Exact ordered echo contract for one selected occurrence. -/
def selectedContractRow
    (slot : SelectedNativeTypeContextualCalculus.Occurrence demand)
    {bindings : Bindings}
    (bound : ∀ view ∈ viewsAt premiseProfile slot,
      BoundArguments view bindings) :
    ContractRow relationEnv language bindings (viewsAt premiseProfile slot) :=
  contractRowOf (viewsAt premiseProfile slot)
    (fun _ membership => selectedView_supported slot membership)
    (viewsAt_typed premiseProfile slot) bound

/-- Central semantic boundary for every selected occurrence.  Ground meanings
of the generated claim row are equivalent to the cold source's ordered
premise execution, including exact preservation of the matched bindings. -/
theorem selectedPremisesAt_iff_claimMeanings
    (slot : SelectedNativeTypeContextualCalculus.Occurrence demand)
    {fuel : Nat} {bindings final : Bindings}
    (bound : ∀ view ∈ viewsAt premiseProfile slot,
      BoundArguments view bindings) :
    PremisesAt (engineBasePremises relationEnv) language fuel bindings
        (typingAt demand slot).site.rewrite.premises final ↔
      GroundMeanings premiseProfile relationEnv slot bindings ∧
        final = bindings := by
  rw [groundMeanings_iff_relationMeanings]
  rw [← viewsAt_encoded premiseProfile slot]
  exact (selectedContractRow slot bound).premisesAt_iff_meanings

/-! ## Discriminating concrete controls -/

private abbrev skipHeadStar :
    SelectedNativeTypeContextualCalculus.Occurrence demand :=
  ⟨2, by
    change 2 < selectedOccurrences.length
    rw [selectedOccurrences_count]
    decide⟩

private abbrev skipHeadBox :
    SelectedNativeTypeContextualCalculus.Occurrence demand :=
  ⟨3, by
    change 3 < selectedOccurrences.length
    rw [selectedOccurrences_count]
    decide⟩

private abbrev finishStar :
    SelectedNativeTypeContextualCalculus.Occurrence demand :=
  ⟨0, by
    change 0 < selectedOccurrences.length
    rw [selectedOccurrences_count]
    decide⟩

/-- The guarded skip-head transition has one exact source query at each
universe endpoint. -/
theorem skipHeadStar_claim_count :
    (authoredClaims premiseProfile skipHeadStar).length = 1 := by
  rw [length_authoredClaims, selectedPremiseCount]
  decide +kernel

theorem skipHeadBox_claim_count :
    (authoredClaims premiseProfile skipHeadBox).length = 1 := by
  rw [length_authoredClaims, selectedPremiseCount]
  decide +kernel

private def skipHeadStarPremise :
    Fin (viewsAt premiseProfile skipHeadStar).length :=
  ⟨0, by rw [selectedPremiseCount]; decide +kernel⟩

private def skipHeadBoxPremise :
    Fin (viewsAt premiseProfile skipHeadBox).length :=
  ⟨0, by rw [selectedPremiseCount]; decide +kernel⟩

/-- Selecting star versus box never collapses authored premise provenance,
even though both slots refer to the same cold rewrite and relation meaning. -/
theorem skipHead_endpoint_claims_distinct :
    authoredClaim premiseProfile skipHeadStar skipHeadStarPremise ≠
      authoredClaim premiseProfile skipHeadBox skipHeadBoxPremise := by
  intro equality
  have labels := (Pattern.apply.inj equality).1
  have coordinates := (Naming.label_eq_iff _ _ _ _).mp labels
  have different : skipHeadStar.val ≠ skipHeadBox.val := by decide
  exact different coordinates.1

/-- The premise-free finish transition cannot decode a fabricated first
premise claim. -/
theorem finish_fabricated_premise_rejected :
    decode? premiseProfile
      (.apply (Naming.label finishStar.val 0) []) = none := by
  have noPremises : (viewsAt premiseProfile finishStar).length = 0 := by
    rw [selectedPremiseCount]
    decide +kernel
  simpa only [noPremises] using
    firstPremiseOutOfRange_rejected premiseProfile finishStar []

/-- The first occurrence outside the exact thirty-slot demand is rejected. -/
theorem foreign_occurrence_rejected :
    decode? premiseProfile
      (.apply (Naming.label demand.occurrences.length 0) []) = none :=
  firstOccurrenceOutOfRange_rejected premiseProfile []

/-- A structurally overlong skip-head alias is rejected before it can receive
semantic meaning.  The argument row is manufactured from the source arity, so
the proof does not normalize the full generated inventory. -/
private def skipHeadWrongArguments : List Pattern :=
  List.replicate
    ((sourceView premiseProfile skipHeadStar skipHeadStarPremise).arguments.length + 1)
    (.fvar "extra-query-argument")

theorem skipHead_wrong_arity_rejected :
    decode? premiseProfile
      (.apply (Naming.label skipHeadStar.val skipHeadStarPremise.val)
        skipHeadWrongArguments) = none := by
  apply wrongArity_rejected premiseProfile skipHeadStar skipHeadStarPremise
  simp [skipHeadWrongArguments]

#print axioms selectedViews?_isSome
#print axioms selectedPremiseCount
#print axioms generatedPremiseTerm_count
#print axioms generatedPremiseLabels_private
#print axioms selectedView_supported
#print axioms selectedContractRow
#print axioms selectedPremisesAt_iff_claimMeanings
#print axioms skipHead_endpoint_claims_distinct
#print axioms finish_fabricated_premise_rejected
#print axioms foreign_occurrence_rejected
#print axioms skipHead_wrong_arity_rejected

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompilePremiseClaim
