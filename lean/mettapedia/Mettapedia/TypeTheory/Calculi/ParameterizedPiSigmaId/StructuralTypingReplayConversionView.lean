import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayGeneration

/-!
# Conversion evidence from an extracted principal typing rule

The existing principal view retains a result-type adjustment tail. This module
composes its supplied conversion codes. A cumulative adjustment is not silently
converted into equality. When the principal type is separated from every
universe head by the conversion checker, accepted replay cannot contain such
an adjustment, and the extraction succeeds with a checked conversion.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay

variable {Head : Type} {ConversionCode : Nat → Type}

def ResultTail.conversion?
    (reflexivity : {n : Nat} → Tm Head n → ConversionCode n)
    (compose : {n : Nat} → ConversionCode n → ConversionCode n → ConversionCode n)
    {n : Nat} (principalType : Tm Head n) :
    ResultTail Head ConversionCode n → Option (ConversionCode n)
  | .hole => some (reflexivity principalType)
  | .cumul .. => none
  | .convert _ _ _ conversion inner =>
      (inner.conversion? reflexivity compose principalType).map fun prior => compose prior conversion

variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)] [∀ u v, Decidable (R.cumulative u v)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)
variable (reflexivity : {n : Nat} → Tm Head n → ConversionCode n)
variable (compose : {n : Nat} → ConversionCode n → ConversionCode n → ConversionCode n)
variable (reflexivityChecked : ∀ {n} (type : Tm Head n),
  conversionCheck (reflexivity type) type type = true)
variable (composeChecked : ∀ {n} {a b c : Tm Head n} {first second : ConversionCode n},
  conversionCheck first a b = true → conversionCheck second b c = true →
    conversionCheck (compose first second) a c = true)

include reflexivityChecked composeChecked in
theorem Code.principal_conversion_checked {n : Nat} (code : Code Head ConversionCode n) :
    ∀ {context : Ctx Head n} {subject displayed : Tm Head n}
      {view : PrincipalView Head ConversionCode n},
      check R conversionCheck context subject displayed code = true →
      code.principalView displayed = some view →
      (∀ (head : Head) (conversion : ConversionCode n),
        conversionCheck conversion view.type (.head head) = false) →
      ∃ conversion,
        view.tail.conversion? reflexivity compose view.type = some conversion ∧
        conversionCheck conversion view.type displayed = true := by
  induction code with
  | cumul level source ih =>
      intro context subject displayed view accepted computed separated
      cases displayed <;> simp only [check, Bool.false_eq_true] at accepted
      rename_i head
      simp only [Bool.and_eq_true] at accepted
      simp only [principalView] at computed
      cases earlier : source.principalView (.head level) with
      | none => simp [earlier] at computed
      | some prior =>
          simp only [earlier, Option.map_some, Option.some.injEq] at computed
          subst view
          obtain ⟨conversion, _, checked⟩ := ih accepted.1 earlier separated
          rw [separated level conversion] at checked
          cases checked
  | convert sourceType level source formation conversion ih _ =>
      intro context subject displayed view accepted computed separated
      simp only [check, Bool.and_eq_true] at accepted
      simp only [principalView] at computed
      cases earlier : source.principalView sourceType with
      | none => simp [earlier] at computed
      | some prior =>
          simp only [earlier, Option.map_some, Option.some.injEq] at computed
          subst view
          obtain ⟨before, equation, checked⟩ := ih accepted.1.1.2 earlier separated
          refine ⟨compose before conversion, ?_, composeChecked checked accepted.2⟩
          simp only [ResultTail.conversion?, equation, Option.map_some]
  | _ =>
      intro context subject displayed view accepted computed separated
      simp only [principalView, Option.some.injEq] at computed
      subst view
      exact ⟨reflexivity displayed, rfl, reflexivityChecked displayed⟩

#print axioms Code.principal_conversion_checked

end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
