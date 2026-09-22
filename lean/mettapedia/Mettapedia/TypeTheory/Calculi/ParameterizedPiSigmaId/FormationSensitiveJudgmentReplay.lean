import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplay

/-!
# Exact finite replay of formation-sensitive judgments

The existing replay tree includes all rules of the formation-sensitive
judgment, including an independently formed conversion target. A separate
finite telescope certificate checks every ambient assumption. Qualified
conversion replay yields soundness and completeness for the unchanged
judgment, for arbitrary selected head and declaration rules.

Completeness means that each derivation has an accepted finite certificate.
The checker does not search for a certificate or decide arbitrary typing.
Its executable arguments contain syntax and finite evidence, not judgments.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay

open FormationSensitive

variable {Head : Type} {ConversionCode : Nat → Type}
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)]
variable [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)]
variable [∀ u v, Decidable (R.cumulative u v)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)
variable (conversionComplete : ∀ {n : Nat} {left right : Tm Head n},
  Conv R.headEq left right R.computation →
    ∃ code : ConversionCode n, conversionCheck code left right = true)

include conversionComplete in
/-- Every actual derivation has a finite replay tree, including conversion
inside premises, beneath binders, and in closed declaration formation. -/
theorem check_complete {n : Nat} {context : Ctx Head n} {subject type : Tm Head n}
    (typing : Typing R context subject type) :
    ∃ code : Code Head ConversionCode n, check R conversionCheck context subject type code = true := by
  induction typing with
  | headType typed => exact ⟨.headType, by simp [check, typed]⟩
  | var index => exact ⟨.var, by simp [check]⟩
  | @const n context name declared u known _ isUniverse ih =>
      obtain ⟨formation, accepted⟩ := ih
      exact ⟨.const u formation, by simp [check, known, isUniverse, accepted]⟩
  | @piForm n context A B u v w _ isU _ isV joined ihA ihB =>
      obtain ⟨domain, domainAccepted⟩ := ihA
      obtain ⟨body, bodyAccepted⟩ := ihB
      exact ⟨.piForm u v domain body, by
        simp [check, isU, isV, joined, domainAccepted, bodyAccepted]⟩
  | @sigmaForm n context A B u v w _ isU _ isV joined ihA ihB =>
      obtain ⟨domain, domainAccepted⟩ := ihA
      obtain ⟨body, bodyAccepted⟩ := ihB
      exact ⟨.sigmaForm u v domain body, by
        simp [check, isU, isV, joined, domainAccepted, bodyAccepted]⟩
  | @lamIntro n context A body B u _ isUniverse _ ihFormation ihBody =>
      obtain ⟨formation, formationAccepted⟩ := ihFormation
      obtain ⟨bodyCode, bodyAccepted⟩ := ihBody
      exact ⟨.lamIntro u formation bodyCode, by
        simp [check, isUniverse, formationAccepted, bodyAccepted]⟩
  | @appElim n context function argument A B _ _ ihFunction ihArgument =>
      obtain ⟨functionCode, functionAccepted⟩ := ihFunction
      obtain ⟨argumentCode, argumentAccepted⟩ := ihArgument
      exact ⟨.appElim A B functionCode argumentCode, by
        simp [check, functionAccepted, argumentAccepted]⟩
  | @pairIntro n context a b A B u _ isUniverse _ _ ihFormation ihFirst ihSecond =>
      obtain ⟨formation, formationAccepted⟩ := ihFormation
      obtain ⟨first, firstAccepted⟩ := ihFirst
      obtain ⟨second, secondAccepted⟩ := ihSecond
      exact ⟨.pairIntro u formation first second, by
        simp [check, isUniverse, formationAccepted, firstAccepted, secondAccepted]⟩
  | @fstElim n context pair A B _ ih =>
      obtain ⟨code, accepted⟩ := ih
      exact ⟨.fstElim B code, by simp [check, accepted]⟩
  | @sndElim n context pair A B _ ih =>
      obtain ⟨code, accepted⟩ := ih
      exact ⟨.sndElim A B code, by simp [check, accepted]⟩
  | @idForm n context A a b u _ isUniverse _ _ ihFormation ihLeft ihRight =>
      obtain ⟨formation, formationAccepted⟩ := ihFormation
      obtain ⟨left, leftAccepted⟩ := ihLeft
      obtain ⟨right, rightAccepted⟩ := ihRight
      exact ⟨.idForm u formation left right, by
        simp [check, isUniverse, formationAccepted, leftAccepted, rightAccepted]⟩
  | @reflIntro n context a A _ ih =>
      obtain ⟨code, accepted⟩ := ih
      exact ⟨.reflIntro A code, by simp [check, accepted]⟩
  | @cumul n context term u v _ order ih =>
      obtain ⟨code, accepted⟩ := ih
      exact ⟨.cumul u code, by simp [check, accepted, order]⟩
  | @conv n context term A B u _ _ isUniverse converted ihSource ihFormation =>
      obtain ⟨source, sourceAccepted⟩ := ihSource
      obtain ⟨formation, formationAccepted⟩ := ihFormation
      obtain ⟨conversion, conversionAccepted⟩ := conversionComplete converted
      exact ⟨.convert A u source formation conversion, by
        simp [check, isUniverse, sourceAccepted, formationAccepted, conversionAccepted]⟩

/-- Telescope certificates retain the universe and type evidence for every
assumption. The supplied context itself remains the authored context. -/
inductive ContextCode (Head : Type) (ConversionCode : Nat → Type) : Nat → Type where
  | nil : ContextCode Head ConversionCode 0
  | snoc {n : Nat} (prior : ContextCode Head ConversionCode n) (levelHead : Head)
      (formation : Code Head ConversionCode n) : ContextCode Head ConversionCode (n + 1)

def checkContext : {n : Nat} → Ctx Head n → ContextCode Head ConversionCode n → Bool
  | _, .nil, .nil => true
  | _, .snoc context type, .snoc prior levelHead formation =>
      checkContext context prior && decide (R.isUniverse levelHead) &&
        check R conversionCheck context type (.head levelHead) formation

variable (conversionSound : ∀ {n : Nat} {code : ConversionCode n} {left right : Tm Head n},
  conversionCheck code left right = true → Conv R.headEq left right R.computation)

include conversionSound in
theorem checkContext_sound {n : Nat} (code : ContextCode Head ConversionCode n) :
    ∀ {context : Ctx Head n}, checkContext R conversionCheck context code = true →
      ContextFormation R context := by
  induction code with
  | nil => intro context accepted; cases context; exact .nil
  | snoc prior levelHead formation ih =>
      intro context accepted
      cases context with
      | snoc context type =>
          simp only [checkContext, Bool.and_eq_true, decide_eq_true_eq] at accepted
          exact .snoc (ih accepted.1.1)
            (check_sound R conversionCheck conversionSound formation accepted.2) accepted.1.2

include conversionComplete in
theorem checkContext_complete {n : Nat} {context : Ctx Head n}
    (formed : ContextFormation R context) :
    ∃ code : ContextCode Head ConversionCode n, checkContext R conversionCheck context code = true := by
  induction formed with
  | nil => exact ⟨.nil, rfl⟩
  | @snoc n context type u _ formed isUniverse ih =>
      obtain ⟨prior, priorAccepted⟩ := ih
      obtain ⟨formation, formationAccepted⟩ := check_complete R conversionCheck conversionComplete formed
      exact ⟨.snoc prior u formation, by
        simp [checkContext, priorAccepted, isUniverse, formationAccepted]⟩

/-- Check the entire formed judgment, not merely a derivation in an
unchecked ambient context. Both certificates are finite executable data. -/
def checkJudgment {n : Nat} (context : Ctx Head n) (subject type : Tm Head n)
    (contextCode : ContextCode Head ConversionCode n) (termCode : Code Head ConversionCode n) : Bool :=
  checkContext R conversionCheck context contextCode && check R conversionCheck context subject type termCode

include conversionSound in
theorem checkJudgment_sound {n : Nat} {context : Ctx Head n} {subject type : Tm Head n}
    {contextCode : ContextCode Head ConversionCode n} {termCode : Code Head ConversionCode n}
    (accepted : checkJudgment R conversionCheck context subject type contextCode termCode = true) :
    Judgment R context subject type := by
  simp only [checkJudgment, Bool.and_eq_true] at accepted
  obtain ⟨formed, typed⟩ := accepted
  exact ⟨checkContext_sound R conversionCheck conversionSound contextCode formed,
    check_sound R conversionCheck conversionSound termCode typed⟩

include conversionSound conversionComplete in
/-- Exactness for the full existing judgment. This quantifies over finite
certificates; it is not a decision procedure for existence of a derivation. -/
theorem judgment_iff_checked {n : Nat} {context : Ctx Head n} {subject type : Tm Head n} :
    Judgment R context subject type ↔
      ∃ contextCode termCode,
        checkJudgment R conversionCheck context subject type contextCode termCode = true := by
  constructor
  · intro judgment
    obtain ⟨contextCode, formed⟩ := checkContext_complete R conversionCheck conversionComplete judgment.context
    obtain ⟨termCode, typed⟩ := check_complete R conversionCheck conversionComplete judgment.typing
    exact ⟨contextCode, termCode, by simp only [checkJudgment, formed, typed, Bool.and_self]⟩
  · rintro ⟨contextCode, termCode, accepted⟩
    exact checkJudgment_sound R conversionCheck conversionSound accepted

#print axioms check_complete
#print axioms checkContext_sound
#print axioms checkContext_complete
#print axioms checkJudgment_sound
#print axioms judgment_iff_checked

end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
