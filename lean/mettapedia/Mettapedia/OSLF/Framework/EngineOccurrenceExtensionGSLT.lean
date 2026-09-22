import Mettapedia.OSLF.Framework.EngineOccurrenceGSLT
import Mettapedia.OSLF.Framework.PremiseAwareOccurrenceExtension

/-!
# A certified rule-position shift on exact operational evidence

An equality of complete numbered occurrence lists, with an injective
occurrence map, induces an exact equivalence of the fixed query/answer
proof-relevant judgment fibres. This is pointwise exactness, not an exact
translation of entire GSLTs unless such equalities hold at every request.
The prefix theorem in `PremiseAwareOccurrenceExtension` supplies one source
of the required list equality under explicit engine-compatibility laws.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.EngineOccurrenceExtensionGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.WeightedOccurrence
open Mettapedia.OSLF.Framework.PremiseAwareOccurrence
open Mettapedia.OSLF.Framework.PremiseAwareOccurrenceExtension
open Mettapedia.OSLF.Framework.EngineOccurrenceGSLT

/-- Map a selected proof-relevant engine receipt using a certified equality
of complete occurrence lists. The original target and alternative position
remain attached to the shifted occurrence. -/
def shiftEvidence
    (firstBase secondBase : BasePremiseEvaluator)
    (firstLanguage secondLanguage : LanguageDef)
    (fuel : Nat) (source answer : Pattern)
    (sameLists :
      rewriteAtOccurrences secondBase secondLanguage fuel source =
        (rewriteAtOccurrences firstBase firstLanguage fuel source).map
          shiftRuleIndex)
    (evidence : (judgment firstBase firstLanguage fuel).Evidence source answer) :
    (judgment secondBase secondLanguage fuel).Evidence source answer := by
  obtain ⟨occurrence, admitted, reaches⟩ := evidence
  refine ⟨shiftRuleIndex occurrence, ?_, ?_⟩
  · rw [sameLists]
    exact List.mem_map.mpr ⟨occurrence, admitted, rfl⟩
  · exact (shiftRuleIndex_target occurrence).trans reaches

@[simp] theorem shiftEvidence_occurrence
    (firstBase secondBase : BasePremiseEvaluator)
    (firstLanguage secondLanguage : LanguageDef)
    (fuel : Nat) (source answer : Pattern)
    (sameLists :
      rewriteAtOccurrences secondBase secondLanguage fuel source =
        (rewriteAtOccurrences firstBase firstLanguage fuel source).map
          shiftRuleIndex)
    (evidence : (judgment firstBase firstLanguage fuel).Evidence source answer) :
    (shiftEvidence firstBase secondBase firstLanguage secondLanguage fuel
      source answer sameLists evidence).val = shiftRuleIndex evidence.val := by
  rcases evidence with ⟨occurrence, admitted, reaches⟩
  simp [shiftEvidence]

/-- The pointwise map reflects equality because the rule-position shift
does not merge formerly different occurrences. -/
theorem shiftEvidence_injective
    (firstBase secondBase : BasePremiseEvaluator)
    (firstLanguage secondLanguage : LanguageDef)
    (fuel : Nat) (source answer : Pattern)
    (sameLists :
      rewriteAtOccurrences secondBase secondLanguage fuel source =
        (rewriteAtOccurrences firstBase firstLanguage fuel source).map
          shiftRuleIndex) :
    Function.Injective (shiftEvidence firstBase secondBase
      firstLanguage secondLanguage fuel source answer sameLists) := by
  intro first second equal
  apply Subtype.ext
  apply shiftRuleIndex_injective
  simpa only [shiftEvidence_occurrence] using congrArg Subtype.val equal

/-- The complete-list equality supplies every target occurrence with an
old preimage. In particular no new successful route is silently assumed to
be a transported old route. -/
theorem shiftEvidence_surjective
    (firstBase secondBase : BasePremiseEvaluator)
    (firstLanguage secondLanguage : LanguageDef)
    (fuel : Nat) (source answer : Pattern)
    (sameLists :
      rewriteAtOccurrences secondBase secondLanguage fuel source =
        (rewriteAtOccurrences firstBase firstLanguage fuel source).map
          shiftRuleIndex) :
    Function.Surjective (shiftEvidence firstBase secondBase
      firstLanguage secondLanguage fuel source answer sameLists) := by
  intro evidence
  obtain ⟨occurrence, admitted, reaches⟩ := evidence
  rw [sameLists] at admitted
  obtain ⟨oldOccurrence, oldAdmitted, shifted⟩ := List.mem_map.mp admitted
  have oldReaches : oldOccurrence.target = answer := by
    calc
      oldOccurrence.target = (shiftRuleIndex oldOccurrence).target := rfl
      _ = occurrence.target := congrArg RewriteOccurrence.target shifted
      _ = answer := reaches
  let oldEvidence :
      (judgment firstBase firstLanguage fuel).Evidence source answer :=
    ⟨oldOccurrence, oldAdmitted, oldReaches⟩
  refine ⟨oldEvidence, ?_⟩
  apply Subtype.ext
  exact (shiftEvidence_occurrence firstBase secondBase firstLanguage
    secondLanguage fuel source answer sameLists oldEvidence).trans shifted

/-- Exactness holds for this one query/answer evidence fibre, since both
faithfulness and completeness were proved for the list-level action. -/
noncomputable def evidenceEquivOfShift
    (firstBase secondBase : BasePremiseEvaluator)
    (firstLanguage secondLanguage : LanguageDef)
    (fuel : Nat) (source answer : Pattern)
    (sameLists :
      rewriteAtOccurrences secondBase secondLanguage fuel source =
        (rewriteAtOccurrences firstBase firstLanguage fuel source).map
          shiftRuleIndex) :
    (judgment firstBase firstLanguage fuel).Evidence source answer ≃
      (judgment secondBase secondLanguage fuel).Evidence source answer :=
  Equiv.ofBijective
    (shiftEvidence firstBase secondBase firstLanguage secondLanguage fuel
      source answer sameLists)
    ⟨shiftEvidence_injective firstBase secondBase firstLanguage secondLanguage
      fuel source answer sameLists,
     shiftEvidence_surjective firstBase secondBase firstLanguage secondLanguage
      fuel source answer sameLists⟩

@[simp] theorem evidenceEquivOfShift_occurrence
    (firstBase secondBase : BasePremiseEvaluator)
    (firstLanguage secondLanguage : LanguageDef)
    (fuel : Nat) (source answer : Pattern)
    (sameLists :
      rewriteAtOccurrences secondBase secondLanguage fuel source =
        (rewriteAtOccurrences firstBase firstLanguage fuel source).map
          shiftRuleIndex)
    (evidence : (judgment firstBase firstLanguage fuel).Evidence source answer) :
    (evidenceEquivOfShift firstBase secondBase firstLanguage secondLanguage
      fuel source answer sameLists evidence).val =
        shiftRuleIndex evidence.val := by
  exact shiftEvidence_occurrence firstBase secondBase firstLanguage
    secondLanguage fuel source answer sameLists evidence

#print axioms shiftEvidence_injective
#print axioms shiftEvidence_surjective
#print axioms evidenceEquivOfShift
#print axioms evidenceEquivOfShift_occurrence

end Mettapedia.OSLF.Framework.EngineOccurrenceExtensionGSLT
