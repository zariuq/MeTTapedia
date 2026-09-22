import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveJudgmentReplay
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitivePresheafSemantics

/-!
# Accepted formed replay in the source representation

An accepted context and term certificate supplies the actual formed source
term. Universe regularity supplies formation of its annotation. The existing
representation then interprets this very subject under every admitted
substitution. No raw-context default or independently assumed typing is used.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay

open FormationSensitive FormationSensitiveContextual
open _root_.CategoryTheory Mettapedia.TypeTheory

variable {Head : Type} {ConversionCode : Nat → Type}
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)]
variable [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)]
variable [∀ u v, Decidable (R.cumulative u v)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)
variable (conversionSound : ∀ {n : Nat} {code : ConversionCode n} {left right : Tm Head n},
  conversionCheck code left right = true → Conv R.headEq left right R.computation)

include conversionSound

/-- The represented subject and annotation are pinned to the actual checked
inputs; section evaluation uses the same admitted simultaneous substitution. -/
theorem accepted_has_represented_term (universes : UniverseRegularity R)
    {n : Nat} {context : Ctx Head n} {subject type : Tm Head n}
    {contextCode : ContextCode Head ConversionCode n} {termCode : Code Head ConversionCode n}
    (accepted : checkJudgment R conversionCheck context subject type contextCode termCode = true) :
    ∃ formed : ContextFormation R context,
      ∃ actualType : TypeOver (⟨n, context, formed⟩ : Context R),
        ∃ actualTerm : Term (⟨n, context, formed⟩ : Context R) actualType,
          actualType.code = type ∧ actualTerm.code = subject ∧
            ∀ (target : Context R) (σ : Hom target ⟨n, context, formed⟩),
              (CwfYoneda.decodeTerm (asCwf R) actualType σ
                ((PresheafSemantics.termEquiv actualType actualTerm).val
                  ⟨Opposite.op (CwfYoneda.context (asCwf R) target), σ⟩)).code =
                subst σ.substitution subject := by
  have judgment := checkJudgment_sound R conversionCheck conversionSound accepted
  obtain ⟨level, isUniverse, annotation⟩ := judgment.regularity universes
  refine ⟨judgment.context, ⟨type, level, isUniverse, annotation.typing⟩,
    ⟨subject, judgment.typing⟩, rfl, rfl, ?_⟩
  intro target σ
  rw [PresheafSemantics.section_at]
  rfl

#print axioms accepted_has_represented_term

end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
