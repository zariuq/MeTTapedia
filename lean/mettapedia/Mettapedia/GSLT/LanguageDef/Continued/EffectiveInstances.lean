import Mettapedia.GSLT.LanguageDef.BagNormalFormEffective
import Mettapedia.GSLT.LanguageDef.Continued.Effective
import Mettapedia.GSLT.LanguageDef.Continued.InstanceTable
import Mettapedia.Languages.Calculator.EffectiveSection
import Mettapedia.Languages.PartrecMachine.HistoryContinued
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalSectionEffective

/-!
# Effective sections of the listed continued instances

A continued theory is effectively continued when the section of one of its
continued presentations is tracked by a computable function on term codes.

* CCS, the asynchronous and the synchronous pi calculus, and mobile ambients
  have the bag normal form as section, and the bag normal form is primitive
  recursive on codes.
* Silent composition in an interaction category and the contact theory author
  no static equation, and their section is the identity.  The lambda calculus
  is the same case.
* CCS has a second section, the normal form with its outermost bag listed in
  the opposite order.  It is effective too, so the two continued
  presentations of CCS are both effective: being continued is added structure
  also when the section is required to be computable.
* The calculator has no interaction and is not continued; its normal form,
  evaluation to a numeral, is effective as a section on closed expressions.
* The rho calculus is continued through its reflective presentation, and its
  section is a section of the reflective static equivalence; that section is
  effective, proved with the rho calculus.
* The history theory is continued and none of its sections is effective.

The synchronous rho section selected by choice on its ordinary equation
quotient is not included among the effective sections below. Its algebraic
section does not supply a computability witness.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode

/-! ## A re-chosen representative -/

/-- An effective section followed by a re-choice of representative that is
computable on codes is effective. -/
theorem ComputableCanonicalSection.Effective.rerepresent {theory : IGSLT}
    {canonical : ComputableCanonicalSection theory} (effective : canonical.Effective)
    {choice : theory.toGSLT.Term → theory.toGSLT.Term}
    (sound : ∀ term, theory.toGSLT.equations.r (choice term) term)
    {choiceCode : ℕ → ℕ} (computable : Computable choiceCode)
    (tracks : ∀ term, theory.termCode (choice term) = choiceCode (theory.termCode term)) :
    (canonical.rerepresent choice sound).Effective := by
  obtain ⟨track, trackComputable, tracked⟩ := effective
  exact ⟨fun code => choiceCode (track code), computable.comp trackComputable,
    fun term => (tracks _).trans (congrArg choiceCode (tracked term))⟩

namespace BagNormalForm

/-- Reverse, on codes, the components of an outermost closed bag. -/
def reverseTopCode (code : ℕ) : ℕ :=
  if IsClosedCollectionCode (collectionCode .hashBag) code then
    closedCollectionCode (collectionCode .hashBag) (collectionComponents code).reverse
  else code

/-- A pattern that is not a closed bag is its own reversal. -/
theorem reverseTop_of_not_bag {pattern : Pattern} (notBag : ¬ IsBagNode pattern) :
    reverseTop pattern = pattern := by
  cases pattern with
  | collection kind elements rest =>
      cases kind <;> cases rest <;> first
        | rfl
        | exact absurd ⟨elements, rfl⟩ notBag
  | _ => rfl

theorem reverseTopCode_patternCode (pattern : Pattern) :
    reverseTopCode (patternCode pattern) = patternCode (reverseTop pattern) := by
  by_cases bag : IsBagNode pattern
  · obtain ⟨elements, rfl⟩ := bag
    have reversed : reverseTop (.collection .hashBag elements none) =
        .collection .hashBag elements.reverse none := rfl
    rw [reverseTopCode,
      if_pos ((isClosedCollectionCode_patternCode .hashBag _).mpr ⟨elements, rfl⟩), reversed,
      patternCode_closedCollection, patternCode_closedCollection,
      collectionComponents_closedCollectionCode, List.map_reverse]
  · rw [reverseTopCode,
      if_neg (mt (isClosedCollectionCode_patternCode .hashBag pattern).mp bag),
      reverseTop_of_not_bag bag]

theorem reverseTopCode_primrec : Primrec reverseTopCode :=
  Primrec.ite (isClosedCollectionCode_primrecPred _)
    ((closedCollectionCode_primrec _).comp
      (Primrec.list_reverse.comp collectionComponents_primrec)) Primrec.id

/-- **The second section of a bag theory is effective.** -/
theorem reversedBagSection_effective (theory : IGSLT) {bag : GrammarRule}
    {unit : Option String}
    (laws : BagTheory theory.presentation.presentation.language bag unit) :
    (reversedBagSection theory laws).Effective :=
  (bagCanonicalSection_effective theory laws).rerepresent
    (reverseTopClosed_equivalent theory laws) reverseTopCode_primrec.to_comp
    fun term => (reverseTopCode_patternCode term.1).symm

end BagNormalForm

open BagNormalForm

/-! ## The rows whose section is the bag normal form -/

section Bags

open Mettapedia.Languages.ProcessCalculi.CCS
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Synchronous
open Mettapedia.Languages.ProcessCalculi.Ambient.Mobile
open InstanceTable

/-- **CCS is effectively continued**: the section of its continued
presentation is the bag normal form. -/
theorem ccs_isEffectivelyContinued : IsEffectivelyContinued ccsIGSLT :=
  ⟨ccsContinuedPresentation, bagCanonicalSection_effective ccsIGSLT ccs_bagTheory⟩

/-- **The asynchronous pi calculus is effectively continued**, by the bag
normal form without a unit. -/
theorem pi_isEffectivelyContinued : IsEffectivelyContinued piIGSLT :=
  ⟨piContinuedPresentation, bagCanonicalSection_effective piIGSLT pi_bagTheory⟩

/-- **The synchronous pi calculus is effectively continued**, by the bag
normal form without a unit. -/
theorem piSync_isEffectivelyContinued : IsEffectivelyContinued piSyncIGSLT :=
  ⟨piSyncContinuedPresentation, bagCanonicalSection_effective piSyncIGSLT piSync_bagTheory⟩

/-- **Mobile ambients are effectively continued**, by the bag normal form
with inaction as unit. -/
theorem ambient_isEffectivelyContinued : IsEffectivelyContinued ambientIGSLT :=
  ⟨ambientContinuedPresentation, bagCanonicalSection_effective ambientIGSLT ambient_bagTheory⟩

/-- **Both sections of CCS are effective**, and the two continued
presentations they give over the one iGSLT are different. -/
theorem ccs_two_effective_presentations :
    ccsContinuedPresentation.canonical.Effective ∧
      ccsReversedContinuedPresentation.canonical.Effective ∧
        ccsContinuedPresentation ≠ ccsReversedContinuedPresentation :=
  ⟨bagCanonicalSection_effective ccsIGSLT ccs_bagTheory,
    reversedBagSection_effective ccsIGSLT ccs_bagTheory, ccs_two_continuedPresentations⟩

/-- The tracking function at work on CCS.  Both listings of the handshake
have the code of the action-first handshake as tracked code, and the two
components of the handshake, which are not equivalent, have different tracked
codes. -/
theorem ccs_tracked_codes :
    normalFormCode (some "CNil") (patternCode handshakeSwapped) = patternCode handshake ∧
      normalFormCode (some "CNil") (patternCode handshake) = patternCode handshake ∧
      normalFormCode (some "CNil") (patternCode actionTerm.1) ≠
        normalFormCode (some "CNil") (patternCode coActionTerm.1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [normalFormCode_patternCode, handshakeSwapped_normalForm]
  · rw [normalFormCode_patternCode, handshake_normalForm]
  · rw [normalFormCode_patternCode, normalFormCode_patternCode]
    intro same
    exact components_normalize_apart (Subtype.ext (patternCode_injective same))

end Bags

/-! ## The rows whose section is the identity -/

/-- **Silent composition in an interaction category is effectively
continued**: it authors no static equation and its section is the identity. -/
theorem silent_isEffectivelyContinued :
    IsEffectivelyContinued (Mettapedia.Languages.InteractionCategory.theory .silent) :=
  ⟨Mettapedia.Languages.InteractionCategory.silentContinuedPresentation,
    ComputableCanonicalSection.effective_of_normalize_eq _ fun _ => rfl⟩

/-- **The contact theory without static laws is effectively continued**: its
section is the identity. -/
theorem bare_isEffectivelyContinued :
    IsEffectivelyContinued Interaction.Controls.EquationalContact.bare :=
  ⟨Interaction.Controls.EquationalContact.bareContinued.toContinuedPresentation rfl,
    ComputableCanonicalSection.effective_of_normalize_eq _ fun _ => Subtype.ext rfl⟩

/-! ## The rows side by side with the control -/

/-- The explicitly listed continued instances are effectively continued,
and the history theory is continued without being so. The statement
assembles their row theorems and juxtaposes them with the control. -/
theorem effectivelyContinued_rows :
    IsEffectivelyContinued Mettapedia.Languages.ProcessCalculi.CCS.ccsIGSLT ∧
      IsEffectivelyContinued (Mettapedia.Languages.InteractionCategory.theory .silent) ∧
      IsEffectivelyContinued Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction.piIGSLT ∧
      IsEffectivelyContinued
        Mettapedia.Languages.ProcessCalculi.PiCalculus.Synchronous.piSyncIGSLT ∧
      IsEffectivelyContinued LambdaContinuedInteraction.lambdaIGSLT ∧
      IsEffectivelyContinued Mettapedia.Languages.ProcessCalculi.Ambient.Mobile.ambientIGSLT ∧
      (IsContinued Mettapedia.Languages.PartrecMachine.historyTheory ∧
        ¬ IsEffectivelyContinued Mettapedia.Languages.PartrecMachine.historyTheory) :=
  ⟨ccs_isEffectivelyContinued, silent_isEffectivelyContinued, pi_isEffectivelyContinued,
    piSync_isEffectivelyContinued, lambda_isEffectivelyContinued,
    ambient_isEffectivelyContinued,
    Mettapedia.Languages.PartrecMachine.history_not_effectivelyContinued⟩

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefCanonicalSection in
/-- The following sections are effective: evaluation in the calculator,
the bag normal form of CCS, of both pi calculi and of mobile ambients, the
reflective canonical form of the asynchronous rho calculus, and the identity
of silent composition and of the lambda calculus. No section of the history
theory is effective. The synchronous rho section selected by choice on its
ordinary quotient is outside this statement. -/
theorem table_sections_effective :
    Mettapedia.Languages.Calculator.calculatorSection.Effective ∧
      Mettapedia.Languages.ProcessCalculi.CCS.ccsCanonicalSection.Effective ∧
      (Mettapedia.Languages.InteractionCategory.canonicalSection .silent).Effective ∧
      rhoCanonicalSection.Effective ∧
      InstanceTable.piCanonicalSection.Effective ∧
      InstanceTable.piSyncCanonicalSection.Effective ∧
      LambdaContinuedInteraction.lambdaCanonicalSection.Effective ∧
      Mettapedia.Languages.ProcessCalculi.Ambient.Mobile.ambientCanonicalSection.Effective ∧
      ∀ canonical :
          ComputableCanonicalSection Mettapedia.Languages.PartrecMachine.historyTheory,
        ¬ canonical.Effective :=
  ⟨Mettapedia.Languages.Calculator.calculatorSection_effective,
    bagCanonicalSection_effective _ _,
    ComputableCanonicalSection.effective_of_normalize_eq _ fun _ => rfl,
    rhoCanonicalSection_effective,
    bagCanonicalSection_effective _ _, bagCanonicalSection_effective _ _,
    lambdaCanonicalSection_effective, bagCanonicalSection_effective _ _,
    Mettapedia.Languages.PartrecMachine.historyTheory_no_effective_section⟩

end Mettapedia.GSLT.LanguageDef
