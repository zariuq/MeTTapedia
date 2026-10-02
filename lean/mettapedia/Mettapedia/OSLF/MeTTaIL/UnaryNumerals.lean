import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Unary numerals in an authored signature

A language that indexes states, symbols or channels by natural numbers can
author them with a nullary constructor and a unary constructor of one sort.
This module fixes that encoding once, for arbitrary constructor labels, and
proves the facts a generated rule needs before it can pass
`LanguageDef.validate`: which constructors a numeral mentions, that it has no
metavariable, binder or dangling index, and that the encoding is injective.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Syntax

namespace Pattern

/-- The unary numeral `succ (succ (… zero))` with the given constructor
labels. -/
def unary (zero succ : String) : Nat → Pattern
  | 0 => .apply zero []
  | count + 1 => .apply succ [unary zero succ count]

@[simp] theorem unary_zero (zero succ : String) :
    unary zero succ 0 = .apply zero [] := rfl

@[simp] theorem unary_succ (zero succ : String) (count : Nat) :
    unary zero succ (count + 1) = .apply succ [unary zero succ count] := rfl

/-- Distinct constructor labels make the encoding injective. -/
theorem unary_injective {zero succ : String} (distinct : zero ≠ succ) :
    Function.Injective (unary zero succ) := by
  intro first
  induction first with
  | zero =>
      intro second same
      cases second with
      | zero => rfl
      | succ second =>
          simp only [unary_zero, unary_succ, Pattern.apply.injEq] at same
          exact absurd same.1 distinct
  | succ first inductionHypothesis =>
      intro second same
      cases second with
      | zero =>
          simp only [unary_zero, unary_succ, Pattern.apply.injEq] at same
          exact absurd same.1.symm distinct
      | succ second =>
          simp only [unary_succ, Pattern.apply.injEq, List.cons.injEq,
            and_true, true_and] at same
          exact congrArg Nat.succ (inductionHypothesis same)

/-- A numeral has no free metavariable. -/
@[simp] theorem freeFvarNames_unary (zero succ : String) (count : Nat) :
    (unary zero succ count).freeFvarNames = [] := by
  induction count with
  | zero => simp [freeFvarNames]
  | succ count inductionHypothesis =>
      simp [freeFvarNames, inductionHypothesis]

/-- A numeral is locally closed at every binder depth. -/
@[simp] theorem isWellScopedAt_unary (zero succ : String) (depth count : Nat) :
    (unary zero succ count).isWellScopedAt depth = true := by
  induction count with
  | zero => simp [isWellScopedAt, isWellScopedListAt]
  | succ count inductionHypothesis =>
      simp [isWellScopedAt, isWellScopedListAt, inductionHypothesis]

/-- A numeral is ground. -/
@[simp] theorem isGroundAt_unary (zero succ : String) (depth count : Nat) :
    (unary zero succ count).isGroundAt depth = true := by
  induction count with
  | zero => simp [isGroundAt, isGroundListAt]
  | succ count inductionHypothesis =>
      simp [isGroundAt, isGroundListAt, inductionHypothesis]

/-- A nullary application mentions exactly its own constructor. -/
theorem constructorRefs_apply_nil (label : String) :
    constructorRefs (.apply label []) = [(label, 0)] := by
  unfold constructorRefs
  split <;> simp_all [constructorRefsList]

/-- A unary application mentions its own constructor and then its argument's. -/
theorem constructorRefs_apply_singleton (label : String) (argument : Pattern) :
    constructorRefs (.apply label [argument]) =
      (label, 1) :: constructorRefs argument := by
  conv_lhs => unfold constructorRefs
  split <;> simp_all [constructorRefsList]

/-- The constructors a numeral mentions. -/
theorem constructorRefs_unary (zero succ : String) (count : Nat) :
    (unary zero succ count).constructorRefs =
      List.replicate count (succ, 1) ++ [(zero, 0)] := by
  induction count with
  | zero => simp [constructorRefs_apply_nil]
  | succ count inductionHypothesis =>
      rw [unary_succ, constructorRefs_apply_singleton, inductionHypothesis]
      simp [List.replicate_succ]

/-- Every constructor reference of a numeral is one of its two formers. -/
theorem mem_constructorRefs_unary {zero succ : String} {count : Nat}
    {reference : String × Nat}
    (membership : reference ∈ (unary zero succ count).constructorRefs) :
    reference = (succ, 1) ∨ reference = (zero, 0) := by
  rw [constructorRefs_unary] at membership
  rcases List.mem_append.mp membership with replicated | last
  · exact Or.inl (List.eq_of_mem_replicate replicated)
  · exact Or.inr (by simpa using last)

end Pattern

/-- A numeral introduces no binder name. -/
@[simp] theorem LanguageDef.patternBinderNames_unary (zero succ : String)
    (count : Nat) :
    LanguageDef.patternBinderNames (Pattern.unary zero succ count) = [] := by
  induction count with
  | zero => simp [LanguageDef.patternBinderNames]
  | succ count inductionHypothesis =>
      simp [LanguageDef.patternBinderNames, inductionHypothesis]

/-- A numeral contributes no metavariable to a rule. -/
@[simp] theorem LanguageDef.patternFvarNames_unary (bound : List String)
    (zero succ : String) (count : Nat) :
    LanguageDef.patternFvarNames bound (Pattern.unary zero succ count) = [] := by
  simp [LanguageDef.patternFvarNames]

end Mettapedia.OSLF.MeTTaIL.Syntax
