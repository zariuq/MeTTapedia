import Mettapedia.GSLT.Dedukti.Confluence

/-!
# A test for orthogonal rule lists

`Theory.Orthogonal` states the absence of overlap by quantifying over all
instances.  For a theory whose declared rules lie in a finite list and which
has no transparent definition, a computation suffices (`orthogonal_of_check`).

* `clashes left right` holds when the two terms differ at a position where
  neither is a variable.  Then they have no common instance
  (`ne_inst_of_clashes`).  The test is sound and not complete: it answers
  `false` whenever a binder is met.
* `usesOnly allowed depth term` holds when every free variable of the term is
  in the list.  Then an instance of the term is determined by the listed
  variables (`instantiate_congr_of_usesOnly`).
* `orthogonalCheck rules` runs the two on every rule of the list.

The list may be larger than the set of declared rules: a theory whose rules
are among those of an orthogonal list is orthogonal.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0)

/-- A sufficient test that two terms have no common instance: they differ at
a position where both have a constant, a sort or an application. -/
def clashes : Term → Term → Bool
  | .con first, .con second => first != second
  | .srt first, .srt second => first != second
  | .app function argument, .app function' argument' =>
      clashes function function' || clashes argument argument'
  | .con _, .app _ _ => true
  | .app _ _, .con _ => true
  | .con _, .srt _ => true
  | .srt _, .con _ => true
  | .srt _, .app _ _ => true
  | .app _ _, .srt _ => true
  | _, _ => false

/-- **Terms that clash have no common instance.** -/
theorem ne_inst_of_clashes :
    ∀ {left right : Term}, clashes left right = true →
      ∀ first second : Nat → Term, inst first left ≠ inst second right := by
  intro left
  induction left with
  | var index => intro right clash; cases right <;> simp [clashes] at clash
  | pi domain body _ _ => intro right clash; cases right <;> simp [clashes] at clash
  | lam domain body _ _ => intro right clash; cases right <;> simp [clashes] at clash
  | con name =>
      intro right clash first second same
      cases right with
      | con other =>
          simp only [clashes, bne_iff_ne, ne_eq] at clash
          rw [inst_con, inst_con] at same
          exact clash (Term.con.inj same)
      | srt sort => rw [inst_con, inst_srt] at same; cases same
      | app function argument => rw [inst_con, inst_app] at same; cases same
      | var index => simp [clashes] at clash
      | pi domain body => simp [clashes] at clash
      | lam domain body => simp [clashes] at clash
  | srt sort =>
      intro right clash first second same
      cases right with
      | srt other =>
          simp only [clashes, bne_iff_ne, ne_eq] at clash
          rw [inst_srt, inst_srt] at same
          exact clash (Term.srt.inj same)
      | con name => rw [inst_srt, inst_con] at same; cases same
      | app function argument => rw [inst_srt, inst_app] at same; cases same
      | var index => simp [clashes] at clash
      | pi domain body => simp [clashes] at clash
      | lam domain body => simp [clashes] at clash
  | app function argument ihFunction ihArgument =>
      intro right clash first second same
      cases right with
      | app function' argument' =>
          simp only [clashes, Bool.or_eq_true] at clash
          rw [inst_app, inst_app] at same
          obtain ⟨functions, arguments⟩ := Term.app.inj same
          rcases clash with inFunction | inArgument
          · exact ihFunction inFunction first second functions
          · exact ihArgument inArgument first second arguments
      | con name => rw [inst_app, inst_con] at same; cases same
      | srt sort => rw [inst_app, inst_srt] at same; cases same
      | var index => simp [clashes] at clash
      | pi domain body => simp [clashes] at clash
      | lam domain body => simp [clashes] at clash

/-- Every free variable of the term, read beneath `depth` binders, is in the
list. -/
def usesOnly (allowed : List Nat) (depth : Nat) : Term → Bool
  | .var index => decide (index < depth) || decide (index - depth ∈ allowed)
  | .srt _ => true
  | .con _ => true
  | .pi domain body => usesOnly allowed depth domain && usesOnly allowed (depth + 1) body
  | .lam domain body => usesOnly allowed depth domain && usesOnly allowed (depth + 1) body
  | .app function argument => usesOnly allowed depth function && usesOnly allowed depth argument

/-- **An instance is determined by the free variables of the term.** -/
theorem instantiate_congr_of_usesOnly {allowed : List Nat} {first second : Nat → Term}
    (agree : ∀ index ∈ allowed, first index = second index) :
    ∀ (term : Term) (depth : Nat), usesOnly allowed depth term = true →
      instantiate first depth term = instantiate second depth term := by
  intro term
  induction term with
  | var index =>
      intro depth uses
      by_cases below : index < depth
      · simp [instantiate, below]
      · simp only [usesOnly, below, decide_false, Bool.false_or, decide_eq_true_eq] at uses
        simp only [instantiate, below, if_false]
        rw [agree _ uses]
  | srt sort => intro depth _; rfl
  | con name => intro depth _; rfl
  | pi domain body ihDomain ihBody =>
      intro depth uses
      simp only [usesOnly, Bool.and_eq_true] at uses
      simp only [instantiate, ihDomain depth uses.1, ihBody (depth + 1) uses.2]
  | lam domain body ihDomain ihBody =>
      intro depth uses
      simp only [usesOnly, Bool.and_eq_true] at uses
      simp only [instantiate, ihDomain depth uses.1, ihBody (depth + 1) uses.2]
  | app function argument ihFunction ihArgument =>
      intro depth uses
      simp only [usesOnly, Bool.and_eq_true] at uses
      simp only [instantiate, ihFunction depth uses.1, ihArgument depth uses.2]

/-- The test of one rule against a list of rules. -/
def ruleChecked (rules : List RewriteRule) (rule : RewriteRule) : Bool :=
  algebraic true rule.lhs && decide (patternVars rule.lhs).Nodup &&
    usesOnly (patternVars rule.lhs) 0 rule.rhs &&
    (subpatterns rule.lhs).all (fun part =>
      !algebraic true part || rules.all fun other => clashes part other.lhs) &&
    rules.all fun other => decide (rule = other) || clashes rule.lhs other.lhs

/-- **The test**: every rule of the list is algebraic and linear on the left
and uses on the right only the variables of the left; no headed proper part
of a left side, and no left side of another rule, can have a common instance
with a left side. -/
def orthogonalCheck (rules : List RewriteRule) : Bool :=
  rules.all (ruleChecked rules)

/-- **A theory without definitions whose rules are among those of a list that
passes the test is orthogonal.** -/
theorem orthogonal_of_check {theory : Theory} (rules : List RewriteRule)
    (covered : ∀ rule, theory.rule rule → rule ∈ rules)
    (undefined : ∀ name, theory.body name = none)
    (checked : orthogonalCheck rules = true) : theory.Orthogonal := by
  have each : ∀ rule, theory.rule rule →
      algebraic true rule.lhs = true ∧ (patternVars rule.lhs).Nodup ∧
        usesOnly (patternVars rule.lhs) 0 rule.rhs = true ∧
        (∀ part ∈ subpatterns rule.lhs, algebraic true part = true →
          ∀ other ∈ rules, clashes part other.lhs = true) ∧
        ∀ other ∈ rules, rule = other ∨ clashes rule.lhs other.lhs = true := by
    intro rule member
    have passed := List.all_eq_true.mp checked rule (covered rule member)
    simp only [ruleChecked, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true'] at passed
    obtain ⟨⟨⟨⟨isAlgebraic, nodup⟩, uses⟩, parts⟩, roots⟩ := passed
    refine ⟨isAlgebraic, nodup, uses, fun part partMember partAlgebraic other otherMember => ?_,
      roots⟩
    rcases parts part partMember with notAlgebraic | clash
    · rw [partAlgebraic] at notAlgebraic
      cases notAlgebraic
    · exact clash other otherMember
  refine
    { closedBodies := fun name term defined => ?_
      leftAlgebraic := fun rule member => (each rule member).1
      leftLinear := fun rule member => (each rule member).2.1
      rightDetermined := fun rule member first second agree =>
        instantiate_congr_of_usesOnly agree rule.rhs 0 (each rule member).2.2.1
      leftUndefined := fun _ _ name _ => undefined name
      rootUnique := fun first second firstMember secondMember left right same => ?_
      nonOverlapping := fun rule member part partMember partAlgebraic =>
        { undefined := fun name _ => undefined name
          unmatched := fun other first second otherMember =>
            ne_inst_of_clashes
              ((each rule member).2.2.2.1 part partMember partAlgebraic other
                (covered other otherMember)) first second } }
  · rw [undefined name] at defined
    cases defined
  · rcases (each first firstMember).2.2.2.2 second (covered second secondMember) with equal | clash
    · exact equal
    · exact (ne_inst_of_clashes clash left right same).elim

#print axioms ne_inst_of_clashes
#print axioms instantiate_congr_of_usesOnly
#print axioms orthogonal_of_check

end Mettapedia.GSLT.Dedukti
