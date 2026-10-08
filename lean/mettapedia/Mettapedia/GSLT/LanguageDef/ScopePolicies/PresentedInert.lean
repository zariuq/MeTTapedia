import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.GSLT.LanguageDef.ScopePolicies.StraightLine

/-!
# The theory that `lexicalFreshCore` presents has no reduction

The exact form of the first blocker of the agreement between the five-field
definition and the core.

The one rule of `lexicalFreshCore`, `LetFresh`, carries a freshness premise on
the name of the slot.  A freshness premise is checked for a *free variable*:
the rule fires only when the pattern of the `let` is one.  The terms of a
presented theory are typed in the empty context of free variables, so they are
ground at their stage.

* `step_source_not_ground` — a step of the definition starts at a pattern
  that mentions a free variable: the source is a configuration whose term is a
  `let` into a named slot.
* `presented_term_ground` — a term of the presented theory mentions none.
* `lexicalFreshTheory_no_step` — so the presented theory `lexicalFreshTheory`
  has no reduction at all, at any interface.
* `slot_let_not_presented` — and the configurations of the straight-line
  fragment are not among its terms.

The agreement of `StraightLine` and `StraightText` is therefore a statement
about the reduction that the definition generates on patterns with named
slots, and about no term of `lexicalFreshTheory`.

Positive, for contrast: `letFresh_fires` and `letFresh_step` are steps of that
reduction on patterns.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ScopePolicies

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open LexicalFreshCore

/-- The left side of the rule is rebuilt from the bindings of a match. -/
theorem letFresh_left_matchCorrect : Pattern.isMatchCorrect letFresh.left = true := by decide

/-- The left side of the rule under bindings. -/
theorem applyBindings_letFresh_left (bindings : Bindings) :
    applyBindings bindings letFresh.left =
      cfg (applyBindings bindings (.fvar "st"))
        (letT (applyBindings bindings (.fvar "k")) (symT (applyBindings bindings (.fvar "s")))
          (applyBindings bindings (.fvar "b"))) := by
  simp [letFresh, cfg, letT, symT, applyBindings]

/-- A configuration whose term is a `let` into a named slot is not ground. -/
theorem slot_let_not_ground (depth : ℕ) (name : String) (store value body : Pattern) :
    (cfg store (letT (.fvar name) value body)).isGroundAt depth = false := by
  simp [cfg, letT, Pattern.isGroundAt, Pattern.isGroundListAt]

/-- When the first freshness premise of the rule holds under some bindings, the
pattern of the `let` is a free variable under them. -/
theorem slot_of_freshness {bindings result : Bindings} {term : Pattern}
    (member : result ∈ premiseStepWithEnv RelationEnv.empty lexicalFreshCore bindings
      (.freshness { varName := "k", term := term })) :
    ∃ name, applyBindings bindings (.fvar "k") = .fvar name := by
  obtain ⟨resolved, found, -⟩ := premiseStepWithEnv_freshness_check member
  simp only [Bindings.lookup] at found
  cases entry : bindings.find? (·.1 == "k") with
  | none => exact ⟨"k", by simp [applyBindings, entry]⟩
  | some pair =>
      obtain ⟨key, value⟩ := pair
      rw [entry] at found
      cases value with
      | fvar name => exact ⟨name, by simp [applyBindings, entry]⟩
      | bvar _ => simp at found
      | apply _ _ => simp at found
      | lambda _ _ => simp at found
      | multiLambda _ _ _ => simp at found
      | subst _ _ => simp at found
      | collection _ _ _ => simp at found

/-- **A step of the definition starts at a pattern that mentions a free
variable.**  The source is a configuration whose term is a `let` into a named
slot, so it is not ground at any depth. -/
theorem step_source_not_ground {source target : Pattern}
    (step : Step (engineBasePremises RelationEnv.empty) lexicalFreshCore source target)
    (depth : ℕ) : source.isGroundAt depth = false := by
  obtain ⟨fuel, step⟩ := step
  cases step with
  | @rule fuel source target rule initial final member matched premises applied =>
      have isRule : rule = letFresh := by simpa [lexicalFreshCore] using member
      subst isRule
      rw [matchPatternForRule_eq_syntactic] at matched
      have rebuilt : applyBindings initial letFresh.left = source :=
        matchPattern_correct matched letFresh_left_matchCorrect
      have premiseList : letFresh.premises =
          [.freshness { varName := "k", term := symT (.fvar "s") },
            .freshness { varName := "k", term := .fvar "st" }] := rfl
      rw [premiseList] at premises
      cases premises with
      | cons first rest =>
          cases first with
          | freshness firstMember =>
              have firstStep : _ ∈ premiseStepWithEnv RelationEnv.empty lexicalFreshCore initial
                  (.freshness { varName := "k", term := symT (.fvar "s") }) := firstMember
              obtain ⟨name, slot⟩ := slot_of_freshness firstStep
              rw [← rebuilt, applyBindings_letFresh_left, slot]
              exact slot_let_not_ground depth name _ _ _

/-- **A term of the presented theory mentions no free variable**: it is ground
at its stage. -/
theorem presented_term_ground (interface : Contexts.Interface)
    (term : Contexts.Term lexicalFreshCore interface) :
    term.1.isGroundAt interface.stage.length = true :=
  term.2.1.empty_isGroundAt term.2.2.2.1 term.2.2.2.2

/-- **The presented theory has no reduction**, at any interface. -/
theorem lexicalFreshTheory_no_step {interface : lexicalFreshTheory.Interface}
    (source target : lexicalFreshTheory.Term interface) :
    ¬ lexicalFreshTheory.rewrites source target := by
  rintro ⟨redex, contractum, -, step, -⟩
  have ground := presented_term_ground interface redex
  rw [step_source_not_ground step] at ground
  cases ground

/-- **The configurations of the straight-line fragment are not terms of the
presented theory.** -/
theorem slot_let_not_presented (name : String) (store value body : Pattern)
    (interface : Contexts.Interface) (term : Contexts.Term lexicalFreshCore interface) :
    term.1 ≠ cfg store (letT (.fvar name) value body) := by
  intro same
  have ground := presented_term_ground interface term
  rw [same, slot_let_not_ground] at ground
  cases ground

#print axioms step_source_not_ground
#print axioms presented_term_ground
#print axioms lexicalFreshTheory_no_step
#print axioms slot_let_not_presented

end Mettapedia.GSLT.LanguageDef.ScopePolicies
