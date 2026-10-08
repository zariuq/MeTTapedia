import Mettapedia.GSLT.LanguageDef.LFTyping

/-!
# Lifting, substitution and instantiation of λΠ terms

The terms are the existing de Bruijn λΠ terms `LF.Term`, with the existing
`LFTyping.lift` and `LFTyping.subst`.  This module adds what a calculus with
declared rewrite rules needs on top of them.

* `instantiate` replaces every free variable of a term at once.  The left and
  right sides of a declared rule are terms whose free variables are the
  pattern variables; an instance of the rule is the pair of instantiations.
  Existing `subst` replaces one variable, so it does not express an instance.
* Cancellation laws of `subst` against `lift`, used when a rule with a
  higher-order pattern variable is applied to an abstraction.
* A term that is well scoped at depth `n` (existing `LF.WellScoped`) is
  unchanged by lifting and by substitution above `n`.  This is what makes the
  interpretation of a constant by a closed term commute with substitution.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping

/-- Lifting by nothing changes nothing. -/
theorem lift_zero (term : Term) : ∀ cutoff : Nat, lift 0 cutoff term = term := by
  induction term with
  | var index => intro cutoff; simp [lift]
  | srt sort => intro cutoff; rfl
  | con name => intro cutoff; rfl
  | pi domain body ihDomain ihBody => intro cutoff; simp [lift, ihDomain, ihBody]
  | lam domain body ihDomain ihBody => intro cutoff; simp [lift, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      intro cutoff; simp [lift, ihFunction, ihArgument]

/-- Substituting for a variable that was just skipped changes nothing. -/
theorem subst_lift_cancel (term : Term) :
    ∀ (cutoff : Nat) (replacement : Term), subst cutoff replacement (lift 1 cutoff term) = term := by
  induction term with
  | var index =>
      intro cutoff replacement
      by_cases below : index < cutoff
      · have notSame : index ≠ cutoff := by omega
        have notAbove : ¬ cutoff < index := by omega
        simp [lift, subst, below, notSame, notAbove]
      · have notSame : index + 1 ≠ cutoff := by omega
        have above : cutoff < index + 1 := by omega
        simp [lift, subst, below, notSame, above]
  | srt sort => intro cutoff replacement; rfl
  | con name => intro cutoff replacement; rfl
  | pi domain body ihDomain ihBody =>
      intro cutoff replacement; simp [lift, subst, ihDomain, ihBody]
  | lam domain body ihDomain ihBody =>
      intro cutoff replacement; simp [lift, subst, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      intro cutoff replacement; simp [lift, subst, ihFunction, ihArgument]

/-- Skipping a variable and then substituting it for the next one is the
identity: the computation behind `(λ x. b) x ⟶ b` under a binder. -/
theorem subst_var_lift (term : Term) :
    ∀ cutoff : Nat, subst cutoff (.var cutoff) (lift 1 (cutoff + 1) term) = term := by
  induction term with
  | var index =>
      intro cutoff
      by_cases below : index < cutoff + 1
      · by_cases same : index = cutoff
        · simp [lift, subst, same]
        · have notAbove : ¬ cutoff < index := by omega
          simp [lift, subst, below, same, notAbove]
      · have notSame : index + 1 ≠ cutoff := by omega
        have above : cutoff < index + 1 := by omega
        simp [lift, subst, below, notSame, above]
  | srt sort => intro cutoff; rfl
  | con name => intro cutoff; rfl
  | pi domain body ihDomain ihBody =>
      intro cutoff; simp [lift, subst, ihDomain, ihBody]
  | lam domain body ihDomain ihBody =>
      intro cutoff; simp [lift, subst, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      intro cutoff; simp [lift, subst, ihFunction, ihArgument]

/-- The instance of the previous law at the outermost binder. -/
theorem subst0_var_lift (term : Term) : subst0 (.var 0) (lift 1 1 term) = term :=
  subst_var_lift term 0

/-! ## Closed terms -/

/-- A term that is well scoped at a depth is unchanged by lifting above that
depth. -/
theorem lift_of_wellScoped {term : Term} {depth : Nat} (wellScoped : WellScoped depth term) :
    ∀ {amount cutoff : Nat}, depth ≤ cutoff → lift amount cutoff term = term := by
  induction wellScoped with
  | srt => intro amount cutoff _; rfl
  | con => intro amount cutoff _; rfl
  | var bound =>
      intro amount cutoff above
      have below : _ < cutoff := Nat.lt_of_lt_of_le bound above
      simp [lift, below]
  | pi _ _ ihDomain ihBody =>
      intro amount cutoff above
      simp [lift, ihDomain above, ihBody (Nat.succ_le_succ above)]
  | lam _ _ ihDomain ihBody =>
      intro amount cutoff above
      simp [lift, ihDomain above, ihBody (Nat.succ_le_succ above)]
  | app _ _ ihFunction ihArgument =>
      intro amount cutoff above
      simp [lift, ihFunction above, ihArgument above]

/-- A term that is well scoped at a depth is unchanged by substitution above
that depth. -/
theorem subst_of_wellScoped {term : Term} {depth : Nat} (wellScoped : WellScoped depth term) :
    ∀ {target : Nat} {replacement : Term}, depth ≤ target → subst target replacement term = term := by
  induction wellScoped with
  | srt => intro target replacement _; rfl
  | con => intro target replacement _; rfl
  | @var depth index bound =>
      intro target replacement above
      have notSame : index ≠ target := by omega
      have notAbove : ¬ target < index := by omega
      simp [subst, notSame, notAbove]
  | pi _ _ ihDomain ihBody =>
      intro target replacement above
      simp [subst, ihDomain above, ihBody (Nat.succ_le_succ above)]
  | lam _ _ ihDomain ihBody =>
      intro target replacement above
      simp [subst, ihDomain above, ihBody (Nat.succ_le_succ above)]
  | app _ _ ihFunction ihArgument =>
      intro target replacement above
      simp [subst, ihFunction above, ihArgument above]

/-- A closed term: no free variable. -/
abbrev Closed (term : Term) : Prop := WellScoped 0 term

theorem Closed.lift {term : Term} (closed : Closed term) (amount cutoff : Nat) :
    lift amount cutoff term = term :=
  lift_of_wellScoped closed (Nat.zero_le cutoff)

theorem Closed.subst {term : Term} (closed : Closed term) (target : Nat) (replacement : Term) :
    subst target replacement term = term :=
  subst_of_wellScoped closed (Nat.zero_le target)

/-- A test for being well scoped at a depth. -/
def wellScopedTest (depth : Nat) : Term → Bool
  | .var index => decide (index < depth)
  | .srt _ => true
  | .con _ => true
  | .pi domain body => wellScopedTest depth domain && wellScopedTest (depth + 1) body
  | .lam domain body => wellScopedTest depth domain && wellScopedTest (depth + 1) body
  | .app function argument => wellScopedTest depth function && wellScopedTest depth argument

/-- The test is sound. -/
theorem wellScoped_of_test (term : Term) :
    ∀ depth : Nat, wellScopedTest depth term = true → WellScoped depth term := by
  induction term with
  | var index => intro depth passed; exact .var (of_decide_eq_true passed)
  | srt sort => intro depth _; exact .srt
  | con name => intro depth _; exact .con
  | pi domain body ihDomain ihBody =>
      intro depth passed
      simp only [wellScopedTest, Bool.and_eq_true] at passed
      exact .pi (ihDomain _ passed.1) (ihBody _ passed.2)
  | lam domain body ihDomain ihBody =>
      intro depth passed
      simp only [wellScopedTest, Bool.and_eq_true] at passed
      exact .lam (ihDomain _ passed.1) (ihBody _ passed.2)
  | app function argument ihFunction ihArgument =>
      intro depth passed
      simp only [wellScopedTest, Bool.and_eq_true] at passed
      exact .app (ihFunction _ passed.1) (ihArgument _ passed.2)

/-! ## Instantiating all free variables -/

/-- Replace every free variable of a term at once.  Under `depth` binders the
variable `depth + k` is replaced by `assignment k`, lifted over the binders. -/
def instantiate (assignment : Nat → Term) (depth : Nat) : Term → Term
  | .var index =>
      if index < depth then .var index else lift depth 0 (assignment (index - depth))
  | .srt sort => .srt sort
  | .con name => .con name
  | .pi domain body =>
      .pi (instantiate assignment depth domain) (instantiate assignment (depth + 1) body)
  | .lam domain body =>
      .lam (instantiate assignment depth domain) (instantiate assignment (depth + 1) body)
  | .app function argument =>
      .app (instantiate assignment depth function) (instantiate assignment depth argument)

/-- Instantiate the free variables of a term that is under no binder. -/
abbrev inst (assignment : Nat → Term) (term : Term) : Term := instantiate assignment 0 term

@[simp] theorem inst_var (assignment : Nat → Term) (index : Nat) :
    inst assignment (.var index) = assignment index := by
  simp [inst, instantiate, lift_zero]

@[simp] theorem inst_srt (assignment : Nat → Term) (sort : Srt) :
    inst assignment (.srt sort) = .srt sort := rfl

@[simp] theorem inst_con (assignment : Nat → Term) (name : String) :
    inst assignment (.con name) = .con name := rfl

@[simp] theorem inst_app (assignment : Nat → Term) (function argument : Term) :
    inst assignment (.app function argument) =
      .app (inst assignment function) (inst assignment argument) := rfl

/-- A closed term has no variable to instantiate. -/
theorem instantiate_of_wellScoped {term : Term} {depth : Nat} (wellScoped : WellScoped depth term)
    (assignment : Nat → Term) : ∀ {under : Nat}, depth ≤ under →
      instantiate assignment under term = term := by
  induction wellScoped with
  | srt => intro under _; rfl
  | con => intro under _; rfl
  | var bound =>
      intro under above
      have below : _ < under := Nat.lt_of_lt_of_le bound above
      simp [instantiate, below]
  | pi _ _ ihDomain ihBody =>
      intro under above
      simp [instantiate, ihDomain above, ihBody (Nat.succ_le_succ above)]
  | lam _ _ ihDomain ihBody =>
      intro under above
      simp [instantiate, ihDomain above, ihBody (Nat.succ_le_succ above)]
  | app _ _ ihFunction ihArgument =>
      intro under above
      simp [instantiate, ihFunction above, ihArgument above]

theorem Closed.inst {term : Term} (closed : Closed term) (assignment : Nat → Term) :
    inst assignment term = term :=
  instantiate_of_wellScoped closed assignment (Nat.le_refl 0)

/-! ## The head of an applicative term -/

/-- The constant at the head of an application spine, if there is one. -/
def headConst : Term → Option String
  | .con name => some name
  | .app function _ => headConst function
  | _ => none

/-- Instantiation keeps the head constant of a pattern. -/
theorem headConst_instantiate {pattern : Term} {name : String} (assignment : Nat → Term) :
    ∀ depth : Nat, headConst pattern = some name →
      headConst (instantiate assignment depth pattern) = some name := by
  induction pattern with
  | var index => intro depth head; simp [headConst] at head
  | srt sort => intro depth head; simp [headConst] at head
  | con other => intro depth head; simpa [instantiate, headConst] using head
  | pi domain body _ _ => intro depth head; simp [headConst] at head
  | lam domain body _ _ => intro depth head; simp [headConst] at head
  | app function argument ihFunction _ =>
      intro depth head
      simp only [headConst] at head
      simpa [instantiate, headConst] using ihFunction depth head

#print axioms subst_lift_cancel
#print axioms subst_var_lift
#print axioms lift_of_wellScoped
#print axioms headConst_instantiate

end Mettapedia.GSLT.Dedukti
