import Mettapedia.OSLF.MeTTaIL.ScopedPattern

/-!
# The scope safety a declared quote scope asks for

A presentation declares whether binders reach into its quotations
(`ReflectivePresentationDecl.quoteScope`). A closed scope keeps quoted code
opaque to substitution, so it asks every quotation to be sealed against outer
binders (`binderSafeAt`). A reaching scope enters quotations with its view, and
the view's substitution needs only ordinary locally nameless scope
(`ReflectiveContextualQuote.applyView_scoped`, `freezeView_scoped`,
`closureView_scoped`), so ordinary scope is all it asks.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ScopedPattern

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- **The scope safety a quote scope asks of a pattern at binder depth `depth`.**
A closed scope seals every quotation of `quoteConstructor`; a reaching scope asks
ordinary scope. -/
def scopeSafeAt : QuoteScope → String → Nat → Pattern → Bool
  | .closed, quoteConstructor, depth, pattern => binderSafeAt quoteConstructor depth pattern
  | .reaching _, _, depth, pattern => pattern.isWellScopedAt depth

@[simp] theorem scopeSafeAt_closed (quoteConstructor : String) (depth : Nat) (pattern : Pattern) :
    scopeSafeAt .closed quoteConstructor depth pattern =
      binderSafeAt quoteConstructor depth pattern := rfl

@[simp] theorem scopeSafeAt_reaching (view : QuoteView) (quoteConstructor : String) (depth : Nat)
    (pattern : Pattern) :
    scopeSafeAt (.reaching view) quoteConstructor depth pattern = pattern.isWellScopedAt depth :=
  rfl

theorem scopeSafeAt_of_closed {scope : QuoteScope} (closed : scope = .closed)
    (quoteConstructor : String) (depth : Nat) (pattern : Pattern) :
    scopeSafeAt scope quoteConstructor depth pattern =
      binderSafeAt quoteConstructor depth pattern := by
  subst closed; rfl

/-- Every quote scope asks at least ordinary scope. -/
theorem isWellScopedAt_of_scopeSafeAt {scope : QuoteScope} {quoteConstructor : String}
    {depth : Nat} {pattern : Pattern}
    (safe : scopeSafeAt scope quoteConstructor depth pattern = true) :
    pattern.isWellScopedAt depth = true := by
  cases scope with
  | closed => exact isWellScopedAt_of_binderSafeAt _ safe
  | reaching _ => exact safe

/-- A closed scope asks the most: a sealed pattern is safe under every scope. -/
theorem scopeSafeAt_of_binderSafeAt (scope : QuoteScope) {quoteConstructor : String}
    {depth : Nat} {pattern : Pattern}
    (safe : binderSafeAt quoteConstructor depth pattern = true) :
    scopeSafeAt scope quoteConstructor depth pattern = true := by
  cases scope with
  | closed => exact safe
  | reaching _ => exact isWellScopedAt_of_binderSafeAt _ safe

/-- An operation that keeps sealing and keeps ordinary scope keeps the safety of
every quote scope. -/
theorem scopeSafeAt_map {scope : QuoteScope} {quoteConstructor : String}
    {depth depth' : Nat} {pattern pattern' : Pattern}
    (sealing : binderSafeAt quoteConstructor depth pattern = true →
      binderSafeAt quoteConstructor depth' pattern' = true)
    (scoping : pattern.isWellScopedAt depth = true → pattern'.isWellScopedAt depth' = true)
    (safe : scopeSafeAt scope quoteConstructor depth pattern = true) :
    scopeSafeAt scope quoteConstructor depth' pattern' = true := by
  cases scope with
  | closed => exact sealing safe
  | reaching _ => exact scoping safe

/-- An operation that keeps sealing and ordinary scope in both directions keeps
the safety of every quote scope in both directions. -/
theorem scopeSafeAt_congr {scope : QuoteScope} {quoteConstructor : String}
    {depth depth' : Nat} {pattern pattern' : Pattern}
    (sealing : binderSafeAt quoteConstructor depth pattern =
      binderSafeAt quoteConstructor depth' pattern')
    (scoping : pattern.isWellScopedAt depth = pattern'.isWellScopedAt depth') :
    scopeSafeAt scope quoteConstructor depth pattern =
      scopeSafeAt scope quoteConstructor depth' pattern' := by
  cases scope with
  | closed => exact sealing
  | reaching _ => exact scoping

/-- More available binders keep every scope's safety. -/
theorem scopeSafeAt_mono {scope : QuoteScope} {quoteConstructor : String}
    {small large : Nat} {pattern : Pattern}
    (safe : scopeSafeAt scope quoteConstructor small pattern = true) (le : small ≤ large) :
    scopeSafeAt scope quoteConstructor large pattern = true :=
  scopeSafeAt_map (fun sealed => binderSafeAt_mono _ sealed le)
    (fun inScope => isWellScopedAt_mono inScope le) safe

/-- List form of `scopeSafeAt`. -/
def scopeSafeListAt : QuoteScope → String → Nat → List Pattern → Bool
  | .closed, quoteConstructor, depth, patterns => binderSafeListAt quoteConstructor depth patterns
  | .reaching _, _, depth, patterns => Pattern.isWellScopedListAt depth patterns

@[simp] theorem scopeSafeListAt_closed (quoteConstructor : String) (depth : Nat)
    (patterns : List Pattern) :
    scopeSafeListAt .closed quoteConstructor depth patterns =
      binderSafeListAt quoteConstructor depth patterns := rfl

@[simp] theorem scopeSafeListAt_reaching (view : QuoteView) (quoteConstructor : String)
    (depth : Nat) (patterns : List Pattern) :
    scopeSafeListAt (.reaching view) quoteConstructor depth patterns =
      Pattern.isWellScopedListAt depth patterns := rfl

theorem scopeSafeListAt_of_closed {scope : QuoteScope} (closed : scope = .closed)
    (quoteConstructor : String) (depth : Nat) (patterns : List Pattern) :
    scopeSafeListAt scope quoteConstructor depth patterns =
      binderSafeListAt quoteConstructor depth patterns := by
  subst closed; rfl

/-- A list is safe exactly when each of its members is. -/
theorem scopeSafeListAt_eq_true_iff (scope : QuoteScope) (quoteConstructor : String)
    (depth : Nat) (patterns : List Pattern) :
    scopeSafeListAt scope quoteConstructor depth patterns = true ↔
      ∀ pattern ∈ patterns, scopeSafeAt scope quoteConstructor depth pattern = true := by
  cases scope with
  | closed => exact binderSafeListAt_eq_true_iff quoteConstructor depth patterns
  | reaching _ => exact isWellScopedListAt_eq_true_iff depth patterns

@[simp] theorem scopeSafeListAt_nil (scope : QuoteScope) (quoteConstructor : String)
    (depth : Nat) : scopeSafeListAt scope quoteConstructor depth [] = true := by
  cases scope <;> rfl

@[simp] theorem scopeSafeListAt_cons (scope : QuoteScope) (quoteConstructor : String)
    (depth : Nat) (pattern : Pattern) (patterns : List Pattern) :
    scopeSafeListAt scope quoteConstructor depth (pattern :: patterns) =
      (scopeSafeAt scope quoteConstructor depth pattern &&
        scopeSafeListAt scope quoteConstructor depth patterns) := by
  cases scope <;> rfl

/-! Structural equations shared by every scope: only a sealing quotation, a
unary application of the quotation constructor under a closed scope, resets the
depth. -/

@[simp] theorem scopeSafeAt_bvar (scope : QuoteScope) (quoteConstructor : String)
    (depth index : Nat) :
    scopeSafeAt scope quoteConstructor depth (.bvar index) = decide (index < depth) := by
  cases scope <;> rfl

@[simp] theorem scopeSafeAt_fvar (scope : QuoteScope) (quoteConstructor : String)
    (depth : Nat) (name : String) :
    scopeSafeAt scope quoteConstructor depth (.fvar name) = true := by
  cases scope <;> rfl

@[simp] theorem scopeSafeAt_lambda (scope : QuoteScope) (quoteConstructor : String)
    (depth : Nat) (binder : Option String) (body : Pattern) :
    scopeSafeAt scope quoteConstructor depth (.lambda binder body) =
      scopeSafeAt scope quoteConstructor (depth + 1) body := by
  cases scope <;> rfl

@[simp] theorem scopeSafeAt_multiLambda (scope : QuoteScope) (quoteConstructor : String)
    (depth arity : Nat) (binders : List String) (body : Pattern) :
    scopeSafeAt scope quoteConstructor depth (.multiLambda arity binders body) =
      scopeSafeAt scope quoteConstructor (depth + arity) body := by
  cases scope <;> rfl

@[simp] theorem scopeSafeAt_subst (scope : QuoteScope) (quoteConstructor : String)
    (depth : Nat) (body replacement : Pattern) :
    scopeSafeAt scope quoteConstructor depth (.subst body replacement) =
      (scopeSafeAt scope quoteConstructor (depth + 1) body &&
        scopeSafeAt scope quoteConstructor depth replacement) := by
  cases scope <;> rfl

@[simp] theorem scopeSafeAt_collection (scope : QuoteScope) (quoteConstructor : String)
    (depth : Nat) (kind : CollType) (elements : List Pattern) (rest : Option String) :
    scopeSafeAt scope quoteConstructor depth (.collection kind elements rest) =
      scopeSafeListAt scope quoteConstructor depth elements := by
  cases scope <;> rfl

/-- An application that is not a sealing quotation checks its arguments at the
same depth. -/
theorem scopeSafeAt_apply_of_not_sealing {scope : QuoteScope} {quoteConstructor constructor : String}
    (notSealing : scope = .closed → constructor ≠ quoteConstructor) (depth : Nat)
    (arguments : List Pattern) :
    scopeSafeAt scope quoteConstructor depth (.apply constructor arguments) =
      scopeSafeListAt scope quoteConstructor depth arguments := by
  cases scope with
  | reaching _ => rfl
  | closed =>
      have other := notSealing rfl
      match arguments with
      | [] => rfl
      | [argument] => simp [scopeSafeAt, scopeSafeListAt, binderSafeAt, other]
      | _ :: _ :: _ => rfl

/-- A sealing quotation checks its body at depth zero. -/
theorem scopeSafeAt_apply_quote_closed (quoteConstructor : String) (depth : Nat) (body : Pattern) :
    scopeSafeAt .closed quoteConstructor depth (.apply quoteConstructor [body]) =
      binderSafeAt quoteConstructor 0 body := by
  simp [scopeSafeAt, binderSafeAt]

@[simp] theorem scopeSafeListAt_append (scope : QuoteScope) (quoteConstructor : String)
    (depth : Nat) (left right : List Pattern) :
    scopeSafeListAt scope quoteConstructor depth (left ++ right) =
      (scopeSafeListAt scope quoteConstructor depth left &&
        scopeSafeListAt scope quoteConstructor depth right) := by
  induction left with
  | nil => simp
  | cons head tail inductionHypothesis =>
      simp [inductionHypothesis, Bool.and_assoc]

theorem scopeSafeListAt_mono {scope : QuoteScope} {quoteConstructor : String}
    {small large : Nat} {patterns : List Pattern}
    (safe : scopeSafeListAt scope quoteConstructor small patterns = true) (le : small ≤ large) :
    scopeSafeListAt scope quoteConstructor large patterns = true := by
  rw [scopeSafeListAt_eq_true_iff] at safe ⊢
  exact fun pattern member => scopeSafeAt_mono (safe pattern member) le

/-- An application is safe when its arguments are, at depth zero beneath a
sealing quotation and at the ambient depth otherwise. -/
theorem scopeSafeAt_apply_of_arguments {scope : QuoteScope} {quoteConstructor constructor : String}
    {depth : Nat} {arguments : List Pattern}
    (resetSafe : scope = .closed → constructor = quoteConstructor →
      scopeSafeListAt scope quoteConstructor 0 arguments = true)
    (ordinarySafe : scopeSafeListAt scope quoteConstructor depth arguments = true) :
    scopeSafeAt scope quoteConstructor depth (.apply constructor arguments) = true := by
  cases scope with
  | reaching _ => exact ordinarySafe
  | closed =>
      simp only [scopeSafeListAt_closed, scopeSafeAt_closed] at resetSafe ordinarySafe ⊢
      match arguments with
      | [] => rfl
      | [argument] =>
          by_cases quoted : constructor = quoteConstructor
          · simpa [binderSafeAt, binderSafeListAt, quoted] using resetSafe trivial quoted
          · simpa [binderSafeAt, binderSafeListAt, quoted] using ordinarySafe
      | _ :: _ :: _ => exact ordinarySafe

/-- Away from a sealing quotation, application safety is the safety of the
argument spine. -/
theorem scopeSafeListAt_of_apply {scope : QuoteScope} {quoteConstructor constructor : String}
    {depth : Nat} {arguments : List Pattern}
    (notSealing : scope = .closed → constructor ≠ quoteConstructor)
    (safe : scopeSafeAt scope quoteConstructor depth (.apply constructor arguments) = true) :
    scopeSafeListAt scope quoteConstructor depth arguments = true := by
  rwa [scopeSafeAt_apply_of_not_sealing notSealing] at safe

/-- Replacing an application spine by a length-preserving spine that keeps the
safety of every scope keeps the safety of the application. -/
theorem scopeSafeAt_apply_of_length_eq_of_list_preserving {scope : QuoteScope}
    {quoteConstructor constructor : String} {depth : Nat} {source target : List Pattern}
    (length_eq : target.length = source.length)
    (preserves : ∀ localDepth, scopeSafeListAt scope quoteConstructor localDepth source = true →
      scopeSafeListAt scope quoteConstructor localDepth target = true)
    (safe : scopeSafeAt scope quoteConstructor depth (.apply constructor source) = true) :
    scopeSafeAt scope quoteConstructor depth (.apply constructor target) = true := by
  by_cases sealing : scope = .closed ∧ constructor = quoteConstructor ∧ source.length = 1
  · obtain ⟨closed, quoted, single⟩ := sealing
    subst closed quoted
    obtain ⟨argument, rfl⟩ := List.length_eq_one_iff.mp single
    obtain ⟨targetArgument, rfl⟩ := List.length_eq_one_iff.mp (length_eq.trans single)
    rw [scopeSafeAt_apply_quote_closed] at safe ⊢
    have outputList := preserves 0 (by simpa [binderSafeListAt] using safe)
    simpa [binderSafeListAt] using outputList
  · have notSealing : scope = .closed → constructor = quoteConstructor →
        ∀ argument, source = [argument] → False := fun closed quoted argument single =>
      sealing ⟨closed, quoted, by simp [single]⟩
    have ordinaryArguments : ∀ depth', scopeSafeAt scope quoteConstructor depth'
        (.apply constructor source) = scopeSafeListAt scope quoteConstructor depth' source := by
      intro depth'
      cases scope with
      | reaching _ => rfl
      | closed =>
          match source, notSealing with
          | [], _ => rfl
          | [argument], notSealing =>
              have other : constructor ≠ quoteConstructor := fun quoted =>
                notSealing rfl quoted argument rfl
              simp [scopeSafeAt, scopeSafeListAt, binderSafeAt, other]
          | _ :: _ :: _, _ => rfl
    have targetArguments : scopeSafeAt scope quoteConstructor depth
        (.apply constructor target) = scopeSafeListAt scope quoteConstructor depth target := by
      cases scope with
      | reaching _ => rfl
      | closed =>
          match target, length_eq with
          | [], _ => rfl
          | [targetArgument], lengthOne =>
              have other : constructor ≠ quoteConstructor := fun quoted =>
                sealing ⟨rfl, quoted, by simpa using lengthOne.symm⟩
              simp [scopeSafeAt, scopeSafeListAt, binderSafeAt, other]
          | _ :: _ :: _, _ => rfl
    rw [targetArguments]
    exact preserves depth ((ordinaryArguments depth) ▸ safe)

/-- Moving a safe pattern beneath fresh binders keeps the safety of every scope. -/
theorem scopeSafeAt_liftBVars {scope : QuoteScope} {quoteConstructor : String}
    {pattern : Pattern} {ambient cutoff shift : Nat}
    (safe : scopeSafeAt scope quoteConstructor (ambient + cutoff) pattern = true) :
    scopeSafeAt scope quoteConstructor (ambient + cutoff + shift)
      (Substitution.liftBVars cutoff shift pattern) = true :=
  scopeSafeAt_map (fun sealed => binderSafeAt_liftBVars _ sealed (Nat.le_add_left _ _))
    (fun inScope => Substitution.liftBVars_isWellScopedAt inScope) safe

/-! ## Controls -/

/-- Positive: a reaching scope lets a quotation mention the binder around it. -/
example : scopeSafeAt (.reaching .apply) "Q" 1 (.apply "Q" [.bvar 0]) = true := by decide

/-- Negative: a closed scope seals that quotation against the binder. -/
example : scopeSafeAt .closed "Q" 1 (.apply "Q" [.bvar 0]) = false := by decide

/-- Negative: a reaching scope still asks ordinary scope. -/
example : scopeSafeAt (.reaching .apply) "Q" 0 (.apply "Q" [.bvar 0]) = false := by decide

end Mettapedia.OSLF.MeTTaIL.ScopedPattern
