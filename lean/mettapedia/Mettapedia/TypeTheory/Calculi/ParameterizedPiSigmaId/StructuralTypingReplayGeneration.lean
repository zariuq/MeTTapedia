import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplay

/-!
# Executable generation of principal typing certificates

A replay tree splits into its actual principal rule and the cumulative and
conversion wrappers above that rule. The wrappers retain every original
formation and conversion certificate. Filling the extracted wrapper with its
original principal certificate reconstructs the input exactly; replacing the
subject at the principal type replays the same wrappers at the displayed type.

This is syntactic certificate generation, not conversion-component injectivity
or normalization. The principal type can differ from the displayed type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay

variable {Head : Type} {ConversionCode : Nat → Type}

inductive ResultTail (Head : Type) (ConversionCode : Nat → Type) (n : Nat) where
  | hole
  | cumul (sourceUniverse : Head) (inner : ResultTail Head ConversionCode n)
  | convert (sourceType : Tm Head n) (level : Head)
      (formation : Code Head ConversionCode n) (conversion : ConversionCode n)
      (inner : ResultTail Head ConversionCode n)

def ResultTail.fill {n : Nat} (tail : ResultTail Head ConversionCode n)
    (principal : Code Head ConversionCode n) : Code Head ConversionCode n :=
  match tail with
  | .hole => principal
  | .cumul level inner => .cumul level (inner.fill principal)
  | .convert type level formation conversion inner =>
      .convert type level (inner.fill principal) formation conversion

structure PrincipalView (Head : Type) (ConversionCode : Nat → Type) (n : Nat) where
  type : Tm Head n
  code : Code Head ConversionCode n
  tail : ResultTail Head ConversionCode n

def Code.isPrincipal {n : Nat} : Code Head ConversionCode n → Bool
  | .cumul .. | .convert .. => false
  | _ => true

/-- Only a malformed cumulative node, whose displayed type is not a head,
prevents the syntactic split. Acceptance is checked independently. -/
def Code.principalView {n : Nat} (displayed : Tm Head n) :
    Code Head ConversionCode n → Option (PrincipalView Head ConversionCode n)
  | .cumul level code => match displayed with
      | .head _ => (code.principalView (.head level)).map fun view =>
          { view with tail := .cumul level view.tail }
      | _ => none
  | .convert sourceType level source formation conversion =>
      (source.principalView sourceType).map fun view =>
        { view with tail := .convert sourceType level formation conversion view.tail }
  | code => some ⟨displayed, code, .hole⟩

theorem Code.principalView_reconstruct {n : Nat} (code : Code Head ConversionCode n) :
    ∀ {displayed : Tm Head n} {view : PrincipalView Head ConversionCode n},
      code.principalView displayed = some view →
        view.tail.fill view.code = code ∧ view.code.isPrincipal = true := by
  induction code with
  | cumul level code ih =>
      intro displayed view computed
      cases displayed <;> simp only [principalView] at computed <;> try contradiction
      rename_i head
      cases priorComputed : code.principalView (.head level) with
      | none => simp [priorComputed] at computed
      | some prior =>
          simp only [priorComputed, Option.map_some, Option.some.injEq] at computed
          subst view
          obtain ⟨reconstructed, principal⟩ := ih priorComputed
          exact ⟨congrArg (Code.cumul level) reconstructed, principal⟩
  | convert sourceType level source formation conversion ih _ =>
      intro displayed view computed
      simp only [principalView] at computed
      cases priorComputed : source.principalView sourceType with
      | none => simp [priorComputed] at computed
      | some prior =>
          simp only [priorComputed, Option.map_some, Option.some.injEq] at computed
          subst view
          obtain ⟨reconstructed, principal⟩ := ih priorComputed
          exact ⟨congrArg (fun code => Code.convert sourceType level code formation conversion) reconstructed,
            principal⟩
  | _ =>
      intro displayed view computed
      simp only [principalView, Option.some.injEq] at computed
      subst view
      exact ⟨rfl, rfl⟩

variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)]
variable [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)]
variable [∀ u v, Decidable (R.cumulative u v)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)

/-- Accepted replay computes its principal judgment and an executable
wrapper that is valid for every replacement proof at that principal type. -/
theorem Code.principalView_checked {n : Nat} (code : Code Head ConversionCode n) :
    ∀ {context : Ctx Head n} {subject displayed : Tm Head n},
      check R conversionCheck context subject displayed code = true →
        ∃ view, code.principalView displayed = some view ∧
          check R conversionCheck context subject view.type view.code = true ∧
          ∀ (replacement : Tm Head n) (replacementCode : Code Head ConversionCode n),
            check R conversionCheck context replacement view.type replacementCode = true →
              check R conversionCheck context replacement displayed (view.tail.fill replacementCode) = true := by
  induction code with
  | cumul level code ih =>
      intro context subject displayed accepted
      cases displayed <;> simp only [check, Bool.false_eq_true] at accepted
      simp only [Bool.and_eq_true] at accepted
      obtain ⟨view, computed, principalChecked, replay⟩ := ih accepted.1
      refine ⟨{ view with tail := .cumul level view.tail }, ?_, principalChecked, ?_⟩
      · simp only [principalView, computed, Option.map_some]
      · intro replacement replacementCode replacementChecked
        simp only [ResultTail.fill, check, Bool.and_eq_true]
        exact ⟨replay replacement replacementCode replacementChecked, accepted.2⟩
  | convert sourceType level source formation conversion ih _ =>
      intro context subject displayed accepted
      simp only [check, Bool.and_eq_true] at accepted
      obtain ⟨view, computed, principalChecked, replay⟩ := ih accepted.1.1.2
      refine ⟨{ view with tail := .convert sourceType level formation conversion view.tail },
        ?_, principalChecked, ?_⟩
      · simp only [principalView, computed, Option.map_some]
      · intro replacement replacementCode replacementChecked
        simp only [ResultTail.fill, check, Bool.and_eq_true]
        exact ⟨⟨⟨accepted.1.1.1, replay replacement replacementCode replacementChecked⟩,
          accepted.1.2⟩, accepted.2⟩
  | _ =>
      intro context subject displayed accepted
      exact ⟨⟨displayed, _, .hole⟩, rfl, accepted, fun _ _ checked => checked⟩

/-- When the subject is a lambda, the computed principal rule is its
actual introduction, even if its displayed type was changed repeatedly. -/
theorem Code.principal_lambda {n : Nat} {context : Ctx Head n} {body : Tm Head (n + 1)}
    {type : Tm Head n} (code : Code Head ConversionCode n)
    (principal : code.isPrincipal = true)
    (accepted : check R conversionCheck context (.lam body) type code = true) :
    ∃ A B level formation bodyCode,
      type = .pi A B ∧ code = .lamIntro level formation bodyCode ∧
      R.isUniverse level ∧ check R conversionCheck context (.pi A B) (.head level) formation = true ∧
      check R conversionCheck (.snoc context A) body B bodyCode = true := by
  cases code <;> simp only [isPrincipal, Bool.false_eq_true] at principal
  all_goals try { simp [check] at accepted }
  rename_i level formation bodyCode
  cases type <;> simp only [check, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact ⟨_, _, level, formation, bodyCode, rfl, rfl, accepted.1.1, accepted.1.2, accepted.2⟩

theorem Code.principal_pair {n : Nat} {context : Ctx Head n} {first second type : Tm Head n}
    (code : Code Head ConversionCode n) (principal : code.isPrincipal = true)
    (accepted : check R conversionCheck context (.pair first second) type code = true) :
    ∃ A B level formation firstCode secondCode,
      type = .sigma A B ∧ code = .pairIntro level formation firstCode secondCode ∧
      R.isUniverse level ∧ check R conversionCheck context (.sigma A B) (.head level) formation = true ∧
      check R conversionCheck context first A firstCode = true ∧
      check R conversionCheck context second (inst0 first B) secondCode = true := by
  cases code <;> simp only [isPrincipal, Bool.false_eq_true] at principal
  all_goals try { simp [check] at accepted }
  rename_i level formation firstCode secondCode
  cases type <;> simp only [check, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact ⟨_, _, level, formation, firstCode, secondCode, rfl, rfl, accepted.1.1.1,
    accepted.1.1.2, accepted.1.2, accepted.2⟩

/-- The identity former checks both endpoint certificates at the carrier
written in its subject, not at independently selected heterogeneous types. -/
theorem Code.principal_identity {n : Nat} {context : Ctx Head n} {A left right type : Tm Head n}
    (code : Code Head ConversionCode n) (principal : code.isPrincipal = true)
    (accepted : check R conversionCheck context (.id A left right) type code = true) :
    ∃ level formation leftCode rightCode,
      type = .head level ∧ code = .idForm level formation leftCode rightCode ∧
      R.isUniverse level ∧ check R conversionCheck context A (.head level) formation = true ∧
      check R conversionCheck context left A leftCode = true ∧
      check R conversionCheck context right A rightCode = true := by
  cases code <;> simp only [isPrincipal, Bool.false_eq_true] at principal
  all_goals try { simp [check] at accepted }
  rename_i level formation leftCode rightCode
  cases type <;> simp only [check, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact ⟨level, formation, leftCode, rightCode, congrArg Tm.head accepted.2, rfl,
    accepted.1.1.1.1, accepted.1.1.1.2, accepted.1.1.2, accepted.1.2⟩

/-- Existing principal-view computation extracts the exact identity formation
and preserves every result wrapper. This includes cumulative chains and does
not reconstruct certificates from the erased subject. -/
theorem Code.identity_generation {n : Nat} {context : Ctx Head n}
    {A left right displayed : Tm Head n} (code : Code Head ConversionCode n)
    (accepted : check R conversionCheck context (.id A left right) displayed code = true) :
    ∃ level formation leftCode rightCode tail,
      code.principalView displayed =
        some ⟨.head level, .idForm level formation leftCode rightCode, tail⟩ ∧
      tail.fill (.idForm level formation leftCode rightCode) = code ∧
      R.isUniverse level ∧ check R conversionCheck context A (.head level) formation = true ∧
      check R conversionCheck context left A leftCode = true ∧
      check R conversionCheck context right A rightCode = true := by
  obtain ⟨view, computed, checked, _⟩ := code.principalView_checked R conversionCheck accepted
  obtain ⟨reconstructed, principal⟩ := code.principalView_reconstruct computed
  obtain ⟨level, formation, leftCode, rightCode, atType, atCode, isUniverse,
    formationChecked, leftChecked, rightChecked⟩ :=
    view.code.principal_identity R conversionCheck principal checked
  refine ⟨level, formation, leftCode, rightCode, view.tail, ?_, ?_,
    isUniverse, formationChecked, leftChecked, rightChecked⟩
  · cases view
    simp_all
  · rw [← atCode]
    exact reconstructed

#print axioms Code.principalView_reconstruct
#print axioms Code.principalView_checked
#print axioms Code.principal_lambda
#print axioms Code.principal_pair
#print axioms Code.principal_identity
#print axioms Code.identity_generation

end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
