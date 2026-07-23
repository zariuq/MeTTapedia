import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Quote-aware scope checking for locally nameless patterns

`Pattern` is a shared raw representation, so it contains dangling de Bruijn
indices.  Reflective calculi also need one additional boundary: a quotation
seals its body against binders outside the quotation.  The check below is
parameterized by the quotation constructor named by a language presentation.
It therefore belongs to the representation layer rather than to any one
process calculus.
-/

namespace Mettapedia.OSLF.MeTTaIL.ScopedPattern

open Mettapedia.OSLF.MeTTaIL.Syntax

mutual
  /-- `binderSafeAt quoteConstructor depth pattern` checks that every bound
  index is below `depth`, except that the body of the declared quotation
  constructor is checked from depth zero. -/
  def binderSafeAt (quoteConstructor : String) (depth : Nat) : Pattern → Bool
    | .bvar index => decide (index < depth)
    | .fvar _ => true
    | .apply constructor [body] =>
        if constructor == quoteConstructor then
          binderSafeAt quoteConstructor 0 body
        else
          binderSafeListAt quoteConstructor depth [body]
    | .apply _ arguments => binderSafeListAt quoteConstructor depth arguments
    | .lambda _ body => binderSafeAt quoteConstructor (depth + 1) body
    | .multiLambda arity _ body =>
        binderSafeAt quoteConstructor (depth + arity) body
    | .subst body replacement =>
        binderSafeAt quoteConstructor (depth + 1) body &&
          binderSafeAt quoteConstructor depth replacement
    | .collection _ elements _ =>
        binderSafeListAt quoteConstructor depth elements

  /-- List recursion for `binderSafeAt`. -/
  def binderSafeListAt (quoteConstructor : String) (depth : Nat) :
      List Pattern → Bool
    | [] => true
    | pattern :: patterns =>
        binderSafeAt quoteConstructor depth pattern &&
          binderSafeListAt quoteConstructor depth patterns
end

/-- Closedness with respect to bound indices, with quotation sealing. -/
def binderSafe (quoteConstructor : String) (pattern : Pattern) : Bool :=
  binderSafeAt quoteConstructor 0 pattern

/-- Ordinary locally nameless scope is pointwise on lists. -/
theorem isWellScopedListAt_eq_true_iff
    (depth : Nat) (patterns : List Pattern) :
    Pattern.isWellScopedListAt depth patterns = true ↔
      ∀ pattern ∈ patterns, pattern.isWellScopedAt depth = true := by
  induction patterns with
  | nil => simp [Pattern.isWellScopedListAt]
  | cons pattern patterns inductionHypothesis =>
      simp [Pattern.isWellScopedListAt, inductionHypothesis]

/-- Increasing the available binder depth preserves ordinary local scope. -/
theorem isWellScopedAt_mono
    {small large : Nat} {pattern : Pattern}
    (safe : pattern.isWellScopedAt small = true)
    (scope : small ≤ large) :
    pattern.isWellScopedAt large = true := by
  induction pattern using Pattern.inductionOn generalizing small large with
  | hbvar index =>
      simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at safe ⊢
      omega
  | hfvar name => simp [Pattern.isWellScopedAt]
  | happly constructor arguments inductionHypothesis =>
      simp only [Pattern.isWellScopedAt] at safe ⊢
      rw [isWellScopedListAt_eq_true_iff] at safe ⊢
      intro argument membership
      exact inductionHypothesis argument membership
        (safe argument membership) scope
  | hlambda binderName body inductionHypothesis =>
      simp only [Pattern.isWellScopedAt] at safe ⊢
      exact inductionHypothesis safe (Nat.add_le_add_right scope 1)
  | hmultiLambda arity binderNames body inductionHypothesis =>
      simp only [Pattern.isWellScopedAt] at safe ⊢
      exact inductionHypothesis safe (Nat.add_le_add_right scope arity)
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at safe ⊢
      exact ⟨bodyInduction safe.1 (Nat.add_le_add_right scope 1),
        replacementInduction safe.2 scope⟩
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [Pattern.isWellScopedAt] at safe ⊢
      rw [isWellScopedListAt_eq_true_iff] at safe ⊢
      intro element membership
      exact inductionHypothesis element membership
        (safe element membership) scope

/-- List safety is pointwise. -/
theorem binderSafeListAt_eq_true_iff
    (quoteConstructor : String) (depth : Nat) (patterns : List Pattern) :
    binderSafeListAt quoteConstructor depth patterns = true ↔
      ∀ pattern ∈ patterns,
        binderSafeAt quoteConstructor depth pattern = true := by
  induction patterns with
  | nil => simp [binderSafeListAt]
  | cons pattern patterns inductionHypothesis =>
      simp [binderSafeListAt, inductionHypothesis]

/-- Quote-aware binder safety is stronger than ordinary local scope.  The
quotation case resets the binder depth to zero and then weakens the resulting
ordinary scope back to the surrounding depth. -/
theorem isWellScopedAt_of_binderSafeAt
    (quoteConstructor : String) {depth : Nat} {pattern : Pattern}
    (safe : binderSafeAt quoteConstructor depth pattern = true) :
    pattern.isWellScopedAt depth = true := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      simpa only [binderSafeAt, Pattern.isWellScopedAt] using safe
  | hfvar name => simp [Pattern.isWellScopedAt]
  | happly constructor arguments inductionHypothesis =>
      cases arguments with
      | nil => simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt]
      | cons argument arguments =>
          cases arguments with
          | nil =>
              by_cases quoted : constructor = quoteConstructor
              · subst constructor
                simp only [binderSafeAt, beq_self_eq_true, if_true] at safe
                simp only [Pattern.isWellScopedAt,
                  Pattern.isWellScopedListAt, Bool.and_true]
                exact isWellScopedAt_mono
                  (inductionHypothesis argument (by simp) safe)
                  (Nat.zero_le depth)
              · simp only [binderSafeAt, beq_iff_eq, if_neg quoted,
                  binderSafeListAt, Bool.and_true] at safe
                simp only [Pattern.isWellScopedAt,
                  Pattern.isWellScopedListAt, Bool.and_true]
                exact inductionHypothesis argument (by simp) safe
          | cons second remainder =>
              rw [show binderSafeAt quoteConstructor depth
                    (.apply constructor (argument :: second :: remainder)) =
                    binderSafeListAt quoteConstructor depth
                      (argument :: second :: remainder) by rfl] at safe
              simp only [Pattern.isWellScopedAt]
              rw [binderSafeListAt_eq_true_iff] at safe
              rw [isWellScopedListAt_eq_true_iff]
              intro member membership
              exact inductionHypothesis member (by simp_all)
                (safe member membership)
  | hlambda binderName body inductionHypothesis =>
      simp only [binderSafeAt] at safe
      simp only [Pattern.isWellScopedAt]
      exact inductionHypothesis safe
  | hmultiLambda arity binderNames body inductionHypothesis =>
      simp only [binderSafeAt] at safe
      simp only [Pattern.isWellScopedAt]
      exact inductionHypothesis safe
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [binderSafeAt, Bool.and_eq_true] at safe
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true]
      exact ⟨bodyInduction safe.1, replacementInduction safe.2⟩
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [binderSafeAt] at safe
      simp only [Pattern.isWellScopedAt]
      rw [binderSafeListAt_eq_true_iff] at safe
      rw [isWellScopedListAt_eq_true_iff]
      intro element membership
      exact inductionHypothesis element membership (safe element membership)

/-- Removing one list element preserves pointwise scope safety. -/
theorem binderSafeListAt_eraseIdx
    (quoteConstructor : String) (depth index : Nat)
    {patterns : List Pattern}
    (safe : binderSafeListAt quoteConstructor depth patterns = true) :
    binderSafeListAt quoteConstructor depth
      (patterns.eraseIdx index) = true := by
  rw [binderSafeListAt_eq_true_iff] at safe ⊢
  intro pattern membership
  exact safe pattern (List.eraseIdx_subset membership)

/-- Increasing the available binder depth preserves scope safety.  Quoted
bodies remain checked at depth zero in both the premise and conclusion. -/
theorem binderSafeAt_mono
    (quoteConstructor : String) {small large : Nat} {pattern : Pattern}
    (safe : binderSafeAt quoteConstructor small pattern = true)
    (scope : small ≤ large) :
    binderSafeAt quoteConstructor large pattern = true := by
  induction pattern using Pattern.inductionOn generalizing small large with
  | hbvar index =>
      simp only [binderSafeAt, decide_eq_true_eq] at safe ⊢
      omega
  | hfvar name =>
      simp [binderSafeAt]
  | happly constructor arguments inductionHypothesis =>
      cases arguments with
      | nil =>
          simp [binderSafeAt, binderSafeListAt]
      | cons argument arguments =>
          cases arguments with
          | nil =>
              by_cases quoted : constructor = quoteConstructor
              · subst constructor
                simpa [binderSafeAt] using safe
              · simp only [binderSafeAt, beq_iff_eq, if_neg quoted,
                  binderSafeListAt, Bool.and_true] at safe ⊢
                exact inductionHypothesis argument (by simp) safe scope
          | cons second remainder =>
              rw [show binderSafeAt quoteConstructor small
                    (.apply constructor (argument :: second :: remainder)) =
                    binderSafeListAt quoteConstructor small
                      (argument :: second :: remainder) by rfl] at safe
              rw [show binderSafeAt quoteConstructor large
                    (.apply constructor (argument :: second :: remainder)) =
                    binderSafeListAt quoteConstructor large
                      (argument :: second :: remainder) by rfl]
              rw [binderSafeListAt_eq_true_iff] at safe ⊢
              intro member membership
              exact inductionHypothesis member (by simp_all) (safe member membership) scope
  | hlambda binderName body inductionHypothesis =>
      simp only [binderSafeAt] at safe ⊢
      exact inductionHypothesis safe (Nat.add_le_add_right scope 1)
  | hmultiLambda arity binderNames body inductionHypothesis =>
      simp only [binderSafeAt] at safe ⊢
      exact inductionHypothesis safe (Nat.add_le_add_right scope arity)
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [binderSafeAt, Bool.and_eq_true] at safe ⊢
      exact ⟨bodyInduction safe.1 (Nat.add_le_add_right scope 1),
        replacementInduction safe.2 scope⟩
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [binderSafeAt] at safe ⊢
      rw [binderSafeListAt_eq_true_iff] at safe ⊢
      intro member membership
      exact inductionHypothesis member membership (safe member membership) scope

/-! ## Positive and negative controls -/

/-- Positive: a lambda binds its innermost index. -/
theorem lambda_bvar_zero_binderSafe (quoteConstructor : String) :
    binderSafe quoteConstructor (.lambda none (.bvar 0)) = true := by
  simp [binderSafe, binderSafeAt]

/-- Negative: a top-level bound index is dangling. -/
theorem top_bvar_zero_not_binderSafe (quoteConstructor : String) :
    binderSafe quoteConstructor (.bvar 0) = false := by
  simp [binderSafe, binderSafeAt]

/-- Negative: an outer lambda does not bind through quotation. -/
theorem lambda_does_not_bind_under_quote (quoteConstructor : String) :
    binderSafe quoteConstructor
        (.lambda none (.apply quoteConstructor [.bvar 0])) = false := by
  simp [binderSafe, binderSafeAt]

end Mettapedia.OSLF.MeTTaIL.ScopedPattern
