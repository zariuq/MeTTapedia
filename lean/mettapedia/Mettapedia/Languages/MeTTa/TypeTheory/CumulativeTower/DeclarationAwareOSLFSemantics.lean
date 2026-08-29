import Mettapedia.GSLT.LanguageDef.CalculusOSLFSemantics
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareStructuralTyping
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareFormedTyping

/-!
# OSLF semantics of declaration-aware Prime structural typing

The declaration-aware Prime calculus already has a proof-relevant semantics
into an independently defined intrinsic `StructuralTyping` family.  This
module reuses that semantics at the calculus-generated OSLF boundary.

For every canonically encoded typing claim, reachability of the empty
proof-search state is equivalent to inhabitation of the intrinsic typing
fibre.  The equivalence then maps into the common cumulative `HasType` spine.
An adversarial raw goal records the necessary boundary: unrestricted schema
search may derive malformed constructor data, while the positive intrinsic
fibre rejects it.  Exact adequacy is therefore indexed by canonical support;
it is not a property of arbitrary raw patterns.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace DeclarationAwareOSLFSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.CalculusOSLFSemantics
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open DeclarationAwareStructuralTyping
open Presentation

/-! ## Reuse of the established proof-relevant interpretation -/

/-- OSLF soundness is inherited from the existing compositional
interpretation of all four declaration-aware structural rules. -/
def structuralSoundModel :
    SoundModel checked (fun goal ↦ Nonempty (CanonicalMeaning goal)) :=
  SoundModel.ofProofRelevant structuralSemantics

theorem oslf_sound (goal : Pattern)
    (satisfies :
      (gsltOSLF (proofSearchGSLT checked)).satisfies [goal]
        (derivableNativeType checked).pred) :
    Nonempty (CanonicalMeaning goal) :=
  structuralSoundModel.nativeTypeSound goal satisfies

/-! ## Exact adequacy on canonical Prime typing claims -/

/-- The generated OSLF native type agrees exactly with the independently
defined intrinsic typing fibre on every canonical declaration-aware claim. -/
theorem oslf_iff_intrinsicStructuralTyping
    {n : Nat} (context : Tower.Ctx n) (term type : Tower.Tm n) :
    (gsltOSLF (proofSearchGSLT checked)).satisfies
        [claimPattern context term type] (derivableNativeType checked).pred ↔
      Nonempty (StructuralTyping context term type) := by
  rw [satisfies_derivableNativeType_iff_derivation]
  constructor
  · rintro ⟨derivation⟩
    apply exists_accepted_raw_iff_nonempty_structuralTyping.mp
    exact ⟨derivation.erase, checkRaw_erase derivation⟩
  · rintro ⟨evidence⟩
    obtain ⟨derivation, _erases⟩ :=
      G2_checkRaw_iff_exists_derivation_erases_to.mp evidence.raw_accepted
    exact ⟨derivation⟩

/-- The OSLF judgment consequently constructs evidence in the common
cumulative Prime typing spine; no new intrinsic typing relation is added. -/
theorem oslf_implies_hasType
    {n : Nat} (context : Tower.Ctx n) (term type : Tower.Tm n)
    (satisfies :
      (gsltOSLF (proofSearchGSLT checked)).satisfies
        [claimPattern context term type] (derivableNativeType checked).pred) :
    Nonempty (Tower.HasType context term type) := by
  obtain ⟨evidence⟩ :=
    (oslf_iff_intrinsicStructuralTyping context term type).mp satisfies
  exact ⟨evidence.toHasType⟩

/-! ## Positive and negative controls -/

/-- Dependent-function formation is a genuinely binder-sensitive positive
control: both ordered universe premises survive into intrinsic evidence. -/
theorem simplePi_oslf :
    (gsltOSLF (proofSearchGSLT checked)).satisfies
        [claimPattern (.nil : Tower.Ctx 0) simplePi simplePiUniverse]
        (derivableNativeType checked).pred :=
  (oslf_iff_intrinsicStructuralTyping (.nil : Tower.Ctx 0)
    simplePi simplePiUniverse).2 ⟨simplePiEvidence⟩

/-- The same Pi term cannot acquire an arbitrary smaller universe through
OSLF reachability. -/
theorem wrongSimplePi_not_oslf :
    ¬ (gsltOSLF (proofSearchGSLT checked)).satisfies
        [claimPattern wrongSimplePiClaim.claim.context
          wrongSimplePiClaim.claim.subject wrongSimplePiClaim.claim.type]
        (derivableNativeType checked).pred := by
  intro satisfies
  apply wrongSimplePiClaim_has_no_structuralEvidence
  exact (oslf_iff_intrinsicStructuralTyping
    wrongSimplePiClaim.claim.context wrongSimplePiClaim.claim.subject
      wrongSimplePiClaim.claim.type).mp satisfies

/-- Raw schema search still derives the deliberately malformed constructor
goal.  This is the negative half of the support-indexed adequacy theorem. -/
theorem malformed_raw_goal_oslf :
    (gsltOSLF (proofSearchGSLT checked)).satisfies [malformedLegacyGoal]
      (derivableNativeType checked).pred := by
  apply (satisfies_derivableNativeType_iff_derivation checked
    malformedLegacyGoal).2
  obtain ⟨derivation, _erases⟩ :=
    G2_checkRaw_iff_exists_derivation_erases_to.mp
      generic_checker_alone_accepts_malformed_context
  exact ⟨derivation⟩

/-- Generated raw OSLF reachability and positive intrinsic support are
provably distinct outside the canonical codec image. -/
theorem malformed_oslf_but_no_positiveMeaning :
    (gsltOSLF (proofSearchGSLT checked)).satisfies [malformedLegacyGoal]
        (derivableNativeType checked).pred ∧
      ¬ Nonempty (PositiveCanonicalMeaning malformedLegacyGoal) := by
  exact ⟨malformed_raw_goal_oslf,
    fun ⟨meaning⟩ ↦ malformedLegacyGoal_no_positiveMeaning meaning⟩

/-! ## Complete formed judgments construct CwF terms -/

namespace Formed

open DeclarationAwareFormedTyping
open Presentation.SyntacticContextual

/-- A complete formed judgment packages its intrinsic evidence together with
the actual term it constructs in the syntactic contextual category. -/
def IntrinsicTermWitness (query : FormedTypingQuery) : Type :=
  Σ evidence : IntrinsicFormedTyping query,
    Term evidence.nativeGoal.formedContext
      (evidence.typeOver evidence.nativeGoal)

/-- OSLF reachability for the complete rooted judgment is exactly
inhabitation of its independent formed-typing fibre. -/
theorem oslf_iff_intrinsicFormedTyping (query : FormedTypingQuery) :
    (gsltOSLF (proofSearchGSLT formedTypingExtension.target)).satisfies
        [encodeFormedTypingQuery query]
        (derivableNativeType formedTypingExtension.target).pred ↔
      Nonempty (IntrinsicFormedTyping query) := by
  rw [satisfies_derivableNativeType_iff_derivation]
  constructor
  · rintro ⟨derivation⟩
    let meaning := formedTypingSemanticExtension.interpret derivation
    exact ⟨meaning.2 query rfl⟩
  · rintro ⟨evidence⟩
    obtain ⟨proof, accepted⟩ :=
      (exists_derived_accepted_iff_nonempty_intrinsic query).2 ⟨evidence⟩
    obtain ⟨derivation, _erases⟩ :=
      G2_checkRaw_iff_exists_derivation_erases_to.mp accepted
    exact ⟨derivation⟩

/-- A complete OSLF judgment constructs a displayed type and term directly;
the checker does not occur in the resulting native witness. -/
theorem oslf_constructs_intrinsicTerm (query : FormedTypingQuery)
    (satisfies :
      (gsltOSLF (proofSearchGSLT formedTypingExtension.target)).satisfies
        [encodeFormedTypingQuery query]
        (derivableNativeType formedTypingExtension.target).pred) :
    Nonempty (IntrinsicTermWitness query) := by
  obtain ⟨evidence⟩ := (oslf_iff_intrinsicFormedTyping query).mp satisfies
  exact ⟨⟨evidence, evidence.term evidence.nativeGoal⟩⟩

open DeclarationAwareFormedTyping.Examples

theorem simplePi_formed_oslf :
    (gsltOSLF (proofSearchGSLT formedTypingExtension.target)).satisfies
        [encodeFormedTypingQuery simplePiQuery]
        (derivableNativeType formedTypingExtension.target).pred :=
  (oslf_iff_intrinsicFormedTyping simplePiQuery).2 ⟨simplePiIntrinsic⟩

/-- Selecting the wrong universe level remains impossible even though the
subject's older structural typing component is independently inhabited. -/
theorem wrongLevel_not_oslf :
    ¬ (gsltOSLF (proofSearchGSLT formedTypingExtension.target)).satisfies
        [encodeFormedTypingQuery wrongLevelQuery]
        (derivableNativeType formedTypingExtension.target).pred := by
  intro satisfies
  exact wrongLevel_has_no_intrinsic_formed_typing
    ((oslf_iff_intrinsicFormedTyping wrongLevelQuery).mp satisfies)

end Formed

#print axioms structuralSoundModel
#print axioms oslf_sound
#print axioms oslf_iff_intrinsicStructuralTyping
#print axioms oslf_implies_hasType
#print axioms simplePi_oslf
#print axioms wrongSimplePi_not_oslf
#print axioms malformed_oslf_but_no_positiveMeaning
#print axioms Formed.oslf_iff_intrinsicFormedTyping
#print axioms Formed.oslf_constructs_intrinsicTerm
#print axioms Formed.simplePi_formed_oslf
#print axioms Formed.wrongLevel_not_oslf

end DeclarationAwareOSLFSemantics
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
