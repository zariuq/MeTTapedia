import Mettapedia.OSLF.MeTTaIL.GeneratedRuleValidation
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Composition in an interaction category as a language definition

In an interaction category a morphism is a process with a left and a right
interface, and composition joins two processes along the interface they
share.  The fragment authored here has synchronous processes that perform one
action on each interface and continue, `Act(a, b, p)`, and composition
`Comp`.

Composition is the contact.  Its rule fires when the right action of the
first process is the left action of the second:

* in the **silent** reading the shared action is consumed and the composite
  continues as the composition of the two continuations,
  `Comp(Act(a, b, p), Act(b, c, q)) ⟶ Comp(p, q)`;
* in the **visible** reading the composite is itself a process performing the
  two outer actions, `Comp(Act(a, b, p), Act(b, c, q)) ⟶ Act(a, c, Comp(p, q))`,
  which is the law by which a composite of synchronous processes is computed.

Interface actions are unary numerals of their own sort.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.InteractionCategory

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-- What a composite shows of the two outer actions. -/
inductive Reading where
  /-- The shared action is consumed; the outer actions are not recorded. -/
  | silent
  /-- The composite performs the two outer actions. -/
  | visible
deriving DecidableEq, Repr

/-- The constructors: actions, the stopped process, a process performing one
action on each interface, and composition. -/
def terms : List GrammarRule := [
    { label := "LBase", category := "Label", params := [], syntaxPattern := [] },
    { label := "LNext", category := "Label",
      params := [.simple "label" (.base "Label")],
      syntaxPattern := [.nonTerminal "label"] },
    { label := "Stop", category := "Proc", params := [], syntaxPattern := [] },
    { label := "Act", category := "Proc",
      params := [.simple "left" (.base "Label"), .simple "right" (.base "Label"),
        .simple "next" (.base "Proc")],
      syntaxPattern := [.nonTerminal "left", .nonTerminal "right", .nonTerminal "next"] },
    { label := "Comp", category := "Proc",
      params := [.simple "first" (.base "Proc"), .simple "second" (.base "Proc")],
      syntaxPattern := [.nonTerminal "first", .nonTerminal "second"] }
  ]

/-- A process performing `left` and `right` and continuing as `next`. -/
def act (left right next : Pattern) : Pattern := .apply "Act" [left, right, next]

/-- The composition of two processes. -/
def comp (first second : Pattern) : Pattern := .apply "Comp" [first, second]

/-- The stopped process. -/
def stop : Pattern := .apply "Stop" []

/-- The interface action numbered `index`. -/
def action (index : Nat) : Pattern := Pattern.unary "LBase" "LNext" index

/-- What the composition rule produces under each reading. -/
def composite : Reading → Pattern
  | .silent => comp (.fvar "p") (.fvar "q")
  | .visible => act (.fvar "a") (.fvar "c") (comp (.fvar "p") (.fvar "q"))

/-- Composition along a shared action. -/
def composeRule (reading : Reading) : RewriteRule where
  name := "Compose"
  typeContext := [("a", .base "Label"), ("b", .base "Label"), ("c", .base "Label"),
    ("p", .base "Proc"), ("q", .base "Proc")]
  premises := []
  left := comp (act (.fvar "a") (.fvar "b") (.fvar "p")) (act (.fvar "b") (.fvar "c") (.fvar "q"))
  right := composite reading

/-- Composition in an interaction category, under a reading. -/
def interactionCategory (reading : Reading) : LanguageDef :=
  { name := "InteractionCategory"
    types := ["Proc", "Label"]
    terms := terms
    equations := []
    rewrites := [composeRule reading] }

/-! ## Validation -/

theorem composeRule_validates (reading : Reading) :
    LanguageDef.validateRewrite (interactionCategory reading) (composeRule reading) = [] := by
  cases reading <;>
    apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [composeRule, composite, interactionCategory, terms, comp, act]

/-- Both readings pass the declaration gate. -/
theorem interactionCategory_validate_eq_nil (reading : Reading) :
    (interactionCategory reading).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  · rfl
  · show (["Proc", "Label"] : List String).Nodup
    decide
  · show (terms.map (·.label)).Nodup
    decide
  · show (["Compose"] : List String).Nodup
    decide
  · show ∀ term ∈ terms, term.category ∈ (["Proc", "Label"] : List String)
    decide
  · show ∀ term ∈ terms, ∀ param ∈ term.params,
      ∀ typeName ∈ (TermParam.typeExpr param).baseNames,
        typeName ∈ (["Proc", "Label"] : List String)
    decide
  · show ∀ term ∈ terms, term.syntaxPattern = [] ∨
      term.syntaxPattern = term.params.map (fun param =>
        SyntaxItem.nonTerminal (TermParam.bodyName param))
    decide +kernel
  · intro rewrite membership
    obtain rfl : rewrite = composeRule reading := List.mem_singleton.mp membership
    exact composeRule_validates reading

/-- The rule binds every variable of its right side on the left. -/
theorem interactionCategory_executionFlowErrors_eq_nil (reading : Reading) :
    (interactionCategory reading).executionFlowErrors [] = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_premiseFree
  · rfl
  · intro rule membership
    obtain rfl : rule = composeRule reading := List.mem_singleton.mp membership
    rfl
  · intro rule membership name nameMembership
    obtain rfl : rule = composeRule reading := List.mem_singleton.mp membership
    cases reading <;>
      simp [composeRule, composite, comp, act, Pattern.freeFvarNames]
        at nameMembership ⊢ <;>
      tauto

/-! ## What composition does -/

/-- The engine with no external relations. -/
abbrev base : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

/-- Two processes that agree on the shared interface. -/
def matched : Pattern :=
  comp (act (action 0) (action 1) stop) (act (action 1) (action 2) stop)

/-- Under the silent reading the composite continues as the composition of
the continuations. -/
theorem matched_composes_silently :
    Step base (interactionCategory .silent) matched (comp stop stop) :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

/-- Under the visible reading the composite performs the two outer actions. -/
theorem matched_composes_visibly :
    Step base (interactionCategory .visible) matched
      (act (action 0) (action 2) (comp stop stop)) :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

/-- Two processes that disagree on the shared interface do not compose. -/
theorem mismatched_stuck (reading : Reading) (target : Pattern) :
    ¬ Step base (interactionCategory reading)
      (comp (act (action 0) (action 1) stop) (act (action 2) (action 0) stop)) target := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule membership
  obtain rfl : rule = composeRule reading := List.mem_singleton.mp membership
  cases reading <;> decide +kernel

end Mettapedia.Languages.InteractionCategory
