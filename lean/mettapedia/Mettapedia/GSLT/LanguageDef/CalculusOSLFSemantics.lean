import Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
import Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Semantic models for calculus-generated OSLF

An authored `CalculusLanguageDef` already induces a proof-search GSLT, and
every GSLT already induces an OSLF native-type system.  This module connects
those constructions to an independently chosen semantic meaning.

Structural validation is deliberately insufficient.  A `SoundModel` proves
that every admitted rule preserves the external meaning; an `ExactModel` also
proves that every semantically valid judgment has a retained derivation.  The
resulting theorems say exactly when the reachability native type is sound or
adequate for that independent model.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CalculusOSLFSemantics

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

namespace ProofRelevant

open Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension

universe uMeaning

/-- Pointwise inhabitation of all ordered premise fibres constructs an
ordered proof-relevant evidence list.  Occurrences are retained even when two
premises have equal patterns. -/
theorem nonemptyEvidenceList {Meaning : Pattern → Type uMeaning} :
    (premises : List Pattern) →
      (∀ premise ∈ premises, Nonempty (Meaning premise)) →
        Nonempty (EvidenceList Meaning premises)
  | [], _ => ⟨.nil⟩
  | premise :: premises, pointwise => by
      obtain ⟨head⟩ := pointwise premise (by simp)
      obtain ⟨tail⟩ := nonemptyEvidenceList premises (fun next member =>
        pointwise next (by simp [member]))
      exact ⟨.cons head tail⟩

end ProofRelevant

/-! ## The native type generated from authored proof search -/

/-- The behavioral native type of obligation lists that can reach the empty
proof-search state.  It is a predicate in the OSLF generated from the authored
calculus GSLT, not a second proof checker. -/
def derivableNativeType (definition : ValidatedCalculusLanguageDef) :
    GSLTNativeType (proofSearchGSLT definition) where
  sort := ()
  pred := fun goals =>
    (proofSearchGSLT definition).MultiStep goals []

/-- Satisfaction of the generated reachability native type is exactly
inhabitation of the authored ordered derivation list. -/
theorem satisfies_derivableNativeType_iff_derivationList
    (definition : ValidatedCalculusLanguageDef) (goals : List Pattern) :
    (gsltOSLF (proofSearchGSLT definition)).satisfies goals
        (derivableNativeType definition).pred ↔
      Nonempty (DerivationList definition goals) := by
  change (proofSearchGSLT definition).MultiStep goals [] ↔
    Nonempty (DerivationList definition goals)
  exact (derivationList_nonempty_iff_proofSearch definition goals).symm

/-- Singleton form: one authored judgment inhabits the generated native type
exactly when it has a retained type-valued derivation. -/
theorem satisfies_derivableNativeType_iff_derivation
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    (gsltOSLF (proofSearchGSLT definition)).satisfies [goal]
        (derivableNativeType definition).pred ↔
      Nonempty (Derivation definition goal) := by
  change (proofSearchGSLT definition).MultiStep [goal] [] ↔
    Nonempty (Derivation definition goal)
  exact (derivation_nonempty_iff_proofSearch definition goal).symm

/-! ## Independent semantic models -/

/-- An independently interpreted model of an authored calculus.  Soundness
is local and compositional: every admitted rule must preserve the selected
meaning whenever all of its ordered premises have that meaning. -/
structure SoundModel (definition : ValidatedCalculusLanguageDef)
    (meaning : Pattern → Prop) where
  ruleSound : ∀ ruleInstance premises conclusion,
    RuleApplication definition ruleInstance premises conclusion →
      (∀ premise ∈ premises, meaning premise) → meaning conclusion

namespace SoundModel

variable {definition : ValidatedCalculusLanguageDef}
variable {meaning : Pattern → Prop}

universe uMeaning

/-- Any existing proof-relevant calculus interpretation induces a sound
proposition-valued model by retaining inhabitation of each semantic fibre.
This adapter lets OSLF reuse established intrinsic semantics without defining
a second rule interpretation. -/
def ofProofRelevant {Meaning : Pattern → Type uMeaning}
    (semantics :
      Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension.CalculusLanguageSemantics
        definition Meaning) :
    SoundModel definition (fun goal => Nonempty (Meaning goal)) where
  ruleSound := by
    intro ruleInstance premises conclusion application premiseMeanings
    obtain ⟨evidence⟩ :=
      ProofRelevant.nonemptyEvidenceList premises premiseMeanings
    exact ⟨semantics.ruleMeaning application evidence⟩

/-- Every retained derivation is sound in the independent model. -/
theorem derivationSound (model : SoundModel definition meaning)
    {goal : Pattern} (derivation : Derivation definition goal) :
    meaning goal :=
  derivation.sound_of_ruleApplications meaning model.ruleSound

/-- OSLF reachability for an authored judgment implies its independent
semantic meaning. -/
theorem nativeTypeSound (model : SoundModel definition meaning)
    (goal : Pattern)
    (satisfies :
      (gsltOSLF (proofSearchGSLT definition)).satisfies [goal]
        (derivableNativeType definition).pred) :
    meaning goal := by
  obtain ⟨derivation⟩ :=
    (satisfies_derivableNativeType_iff_derivation definition goal).mp satisfies
  exact model.derivationSound derivation

/-- Direct OSLF soundness corollary for an established proof-relevant
interpretation. -/
theorem nativeTypeSound_ofProofRelevant {Meaning : Pattern → Type uMeaning}
    (semantics :
      Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension.CalculusLanguageSemantics
        definition Meaning)
    (goal : Pattern)
    (satisfies :
      (gsltOSLF (proofSearchGSLT definition)).satisfies [goal]
        (derivableNativeType definition).pred) :
    Nonempty (Meaning goal) :=
  (ofProofRelevant semantics).nativeTypeSound goal satisfies

/-- A retained derivation of a semantic counterexample prevents any sound
model with that proposed meaning.  Structural validation cannot manufacture
semantic authority. -/
theorem nonempty_forbidden_of_counterexample
    {goal : Pattern} (derivation : Derivation definition goal)
    (counterexample : ¬ meaning goal) :
    ¬ Nonempty (SoundModel definition meaning) := by
  rintro ⟨model⟩
  exact counterexample (model.derivationSound derivation)

end SoundModel

/-- An exact independent model adds completeness to local rule soundness.
This is the contract needed before the generated OSLF native type may be read
as an adequate model judgment rather than only a sound operational one. -/
structure ExactModel (definition : ValidatedCalculusLanguageDef)
    (meaning : Pattern → Prop)
    extends SoundModel definition meaning where
  complete : ∀ goal, meaning goal → Nonempty (Derivation definition goal)

namespace ExactModel

variable {definition : ValidatedCalculusLanguageDef}
variable {meaning : Pattern → Prop}

/-- For an exact model, the calculus-generated OSLF native type and the
independent semantic judgment agree pointwise. -/
theorem nativeType_iff_meaning (model : ExactModel definition meaning)
    (goal : Pattern) :
    (gsltOSLF (proofSearchGSLT definition)).satisfies [goal]
        (derivableNativeType definition).pred ↔
      meaning goal := by
  rw [satisfies_derivableNativeType_iff_derivation]
  constructor
  · rintro ⟨derivation⟩
    exact model.toSoundModel.derivationSound derivation
  · exact model.complete goal

end ExactModel

#print axioms satisfies_derivableNativeType_iff_derivationList
#print axioms satisfies_derivableNativeType_iff_derivation
#print axioms SoundModel.derivationSound
#print axioms SoundModel.ofProofRelevant
#print axioms SoundModel.nativeTypeSound
#print axioms SoundModel.nativeTypeSound_ofProofRelevant
#print axioms SoundModel.nonempty_forbidden_of_counterexample
#print axioms ExactModel.nativeType_iff_meaning

end Mettapedia.GSLT.LanguageDef.CalculusOSLFSemantics
