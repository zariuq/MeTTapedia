import Mettapedia.OSLF.MeTTaIL.ScopedSyntax

/-!
# Rule-aware firing compared with raw and target-depth-only application

The live `rewriteStep` uses rule-aware binding application. The wrap and
duplicate-binder examples below prove its corrected reducts and show that the
old capturing reduct is no longer produced. The duplicate-binder example also
distinguishes this result from target-depth-only lifting, which shifts too far.

The old raw result remains a negative control: ambient-scope checks alone do
not detect a change of binder identity when both terms are closed. These
worked rules do not establish general conditional-premise scope correctness.
-/

namespace Mettapedia.OSLF.Binding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ScopedSyntax
open Mettapedia.OSLF.MeTTaIL.Substitution

set_option autoImplicit false

namespace StepCapture

/-- `wrap(X)  ~>  lambda y. X`.  Nothing exotic: a rule that moves a matched
subterm under a binder it introduces. -/
def wrapRule : RewriteRule where
  name := "wrap-under-binder"
  typeContext := []
  premises := []
  left := .apply "wrap" [.fvar "X"]
  right := .lambda (some "y") (.fvar "X")

def wrapLang : LanguageDef where
  name := "wrap"
  types := []
  terms := []
  equations := []
  rewrites := [wrapRule]

/-- The term the rule is fired at: a `wrap` whose payload names one enclosing
binder.  This is what a contextual match produces when it descends under a
binder, which is the only way a rule ever sees a depth-relative index. -/
def openTerm : Pattern := .apply "wrap" [.bvar 0]

/-- **What the live step relation produces**, since rule firing became
scope-correct: the index moves past the binder the rule introduced.  Before the
repair this was `bvar 0`, which named the rule's own binder instead of the one
the payload was matched under. -/
theorem step_result :
    rewriteStep wrapLang openTerm = [.lambda (some "y") (.bvar 1)] := by
  decide +kernel

/-- The value the scoped layer computes, here by the lifting applier, which
agrees at this depth because the value was matched at ambient depth zero. -/
theorem corrected_result :
    applyBindingsLifting 0 [("X", Pattern.bvar 0)] wrapRule.right
      = .lambda (some "y") (.bvar 1) := by
  decide +kernel

/-- **The engine now agrees with the correction.**  This is the regression
guard: the equation is what the repair bought, and it fails if rule firing ever
stops shifting a matched value across the binders it is inserted under. -/
theorem step_agrees_with_correction :
    rewriteStep wrapLang openTerm
      = [applyBindingsLifting 0 [("X", Pattern.bvar 0)] wrapRule.right] := by
  rw [step_result, corrected_result]

/-! ## What the defect is, and what it is not

A first guess at the broken invariant is that the reduct is closed where the
redex was not.  That guess is wrong, and the control below says why: a rule may
legitimately discard a free variable, and such a rule closes an open term
without doing anything improper.  Scope checks cannot separate the two cases.

The actual breakage is that a *retained* occurrence changes which binder it
refers to.  That is invisible to any ambient-scope check -- both reducts below
are closed -- and is exhibited by asking the enclosing binder's own substitution
whether it still reaches the occurrence. -/

/-- A rule that throws its argument away.  Perfectly legitimate. -/
def dropRule : RewriteRule where
  name := "drop"
  typeContext := []
  premises := []
  left := .apply "wrap" [.fvar "X"]
  right := .apply "nil" []

def dropLang : LanguageDef where
  name := "drop"
  types := []
  terms := []
  equations := []
  rewrites := [dropRule]

/-- **Closing an open term is not the defect.**  This rule takes the same open
redex to a closed reduct, and nothing is wrong with it. -/
theorem discarding_also_closes :
    rewriteStep dropLang openTerm = [.apply "nil" []]
      ∧ (Pattern.apply "nil" []).isWellScopedAt 0 = true := by
  constructor
  · decide +kernel
  · decide +kernel

/-! ## The witness: core formers only, a closed program, a changed referent

Nothing here is an undeclared constructor and nothing is open at the top: the
rule is stated with `lambda`, which is a term former of the pattern language
itself, and the program it fires on is closed. -/

/-- `lambda y. X  ~>  lambda y. lambda y. X`: a rule that introduces a binder
around a matched subterm.  Binder annotations are ignored by matching, so this
matches any abstraction. -/
def dupBinderRule : RewriteRule where
  name := "duplicate-binder"
  typeContext := []
  premises := []
  left := .lambda (some "y") (.fvar "X")
  right := .lambda (some "y") (.lambda (some "y") (.fvar "X"))

def dupLang : LanguageDef where
  name := "dup"
  types := []
  terms := []
  equations := []
  rewrites := [dupBinderRule]

/-- A closed program.  Its inner occurrence refers to the outer binder. -/
def prog : Pattern := .lambda (some "y") (.lambda (some "q") (.bvar 1))

theorem prog_is_closed : prog.isWellScopedAt 0 = true := by decide +kernel

/-- What the live step relation produced **before** rule firing became
scope-correct: the retained occurrence kept the index it had and so named a
different binder. -/
def progActual : Pattern :=
  .lambda (some "y") (.lambda (some "y") (.lambda (some "q") (.bvar 1)))

/-- What it must produce: the occurrence moves past the binder the rule
introduced. -/
def progCorrect : Pattern :=
  .lambda (some "y") (.lambda (some "y") (.lambda (some "q") (.bvar 2)))

/-- **And what it now produces.**  The value here was matched one binder deep
and is inserted two deep, so the shift is one; neither leaving it alone nor
lifting by two is right, and the difference of the two depths is. -/
theorem prog_step : rewriteStep dupLang prog = [progCorrect] := by decide +kernel

/-- The repaired engine no longer produces the capturing reduct. -/
theorem prog_step_ne_actual : rewriteStep dupLang prog ≠ [progActual] := by
  rw [prog_step]
  decide

/-- **The proposed patch is wrong here too, in the other direction.**  The
lifting applier weakens a matched value by the number of binders it has passed
on the right-hand side, which is correct only when the value was matched at
ambient depth zero.  This value was matched one binder deep, so lifting by two
is one too many. -/
theorem lifting_over_lifts :
    applyBindingsLifting 0 [("X", Pattern.lambda (some "q") (.bvar 1))]
        (.lambda (some "y") (.lambda (some "y") (.fvar "X")))
      = .lambda (some "y") (.lambda (some "y") (.lambda (some "q") (.bvar 3))) := by
  decide +kernel

/-- And the index it produces is not in scope at all: a closed program has been
taken to an open term. -/
theorem lifting_escapes :
    (Pattern.lambda (some "y") (.lambda (some "y") (.lambda (some "q") (.bvar 3)))).isWellScopedAt 0
      = false := by
  decide +kernel

/-- **The only correct reduct.**  The value was under one binder and goes under
two, so it moves by exactly one. -/
theorem progCorrect_is_closed : progCorrect.isWellScopedAt 0 = true := by decide +kernel

/-- The retained raw result captures, while target-depth-only lifting escapes.
The rule-aware engine above computes the correct result by using both source
and target depths. Declared metavariable arguments provide a separate scoped
way to retain the dependency; exchanging raw appliers alone is insufficient. -/
theorem neither_applier_is_correct :
    progActual ≠ progCorrect
      ∧ Pattern.lambda (some "y") (.lambda (some "y") (.lambda (some "q") (.bvar 3)))
          ≠ progCorrect := by
  constructor
  · decide
  · decide

/-- **Both reducts are closed.**  No ambient-scope check separates them, which
is why the defect cannot be caught by scope validation. -/
theorem both_reducts_closed :
    progActual.isWellScopedAt 0 = true ∧ progCorrect.isWellScopedAt 0 = true := by
  constructor
  · decide +kernel
  · decide +kernel

/-- A closed term to substitute for the program's outer binder. -/
def witnessValue : Pattern := .apply "W" []

/-- **The occurrence changed owner.**  Substituting for the program's outer
binder reaches the occurrence in the reduct that is correct, and does not reach
it in the reduct the step relation produced -- there it has been caught by the
binder the rule itself introduced. -/
theorem occurrence_changed_owner :
    instantiateBVar witnessValue (.lambda (some "y") (.lambda (some "q") (.bvar 1)))
        = .lambda (some "y") (.lambda (some "q") (.bvar 1))
      ∧ instantiateBVar witnessValue (.lambda (some "y") (.lambda (some "q") (.bvar 2)))
        = .lambda (some "y") (.lambda (some "q") witnessValue) := by
  constructor
  · decide +kernel
  · decide +kernel

/-- The two reducts are different terms, so this is a disagreement and not a
presentation detail. -/
theorem reducts_differ : progActual ≠ progCorrect := by decide

/-! ## Sufficient conditions for agreement, and their necessity

The theorem below is a sufficient condition.  It is followed by three witnesses,
one per hypothesis, each satisfying the other two -- so no hypothesis can be
dropped, and the condition is sharp rather than merely safe. -/

mutual
/-- The pattern uses neither an explicit-substitution node nor a collection
rest variable.  These are the two term formers on which the corrected applier
and the current one do different things for reasons other than scope. -/
def plain : Pattern → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .apply _ args => plainList args
  | .lambda _ body => plain body
  | .multiLambda _ _ body => plain body
  | .subst _ _ => false
  | .collection _ elems rest => plainList elems && rest.isNone

def plainList : List Pattern → Bool
  | [] => true
  | p :: rest => plain p && plainList rest
end

theorem plain_of_mem : ∀ (l : List Pattern), plainList l = true →
    ∀ q ∈ l, plain q = true
  | [], _, _, hq => by cases hq
  | p :: rest, h, q, hq => by
      rw [plainList, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hq with hq | hq
      · exact hq ▸ h.1
      · exact plain_of_mem rest h.2 q hq

/-- **Agreement.**  Where every bound value is closed and the pattern uses
neither an explicit substitution nor a collection rest, the lifting applier and
the current one are the same function. -/
theorem lifting_eq_applyBindings_of_closed
    (bindings : Bindings)
    (hclosed : ∀ e ∈ bindings, Pattern.isWellScopedAt 0 e.2 = true) :
    ∀ (p : Pattern), plain p = true →
      ∀ (depth : Nat), applyBindingsLifting depth bindings p = applyBindings bindings p := by
  intro p
  induction p using Pattern.inductionOn with
  | hbvar n => intro _ _; rw [applyBindingsLifting, applyBindings]
  | hfvar x =>
      intro _ depth
      rw [applyBindingsLifting, applyBindings]
      cases hfind : bindings.find? (fun entry => entry.1 == x) with
      | none => rfl
      | some e =>
          have hmem : e ∈ bindings := List.mem_of_find?_eq_some hfind
          exact liftBVars_eq_self_of_isWellScopedAt (hclosed e hmem)
  | happly c args ih =>
      intro hrf depth
      rw [applyBindingsLifting, applyBindings]
      refine congrArg (fun l => Pattern.apply c l) (List.map_congr_left ?_)
      intro q hq
      exact ih q hq (plain_of_mem args (by rw [plain] at hrf; exact hrf) q hq) depth
  | hlambda nm body ih =>
      intro hrf depth
      rw [applyBindingsLifting, applyBindings]
      exact congrArg (fun b => Pattern.lambda nm b)
        (ih (by rw [plain] at hrf; exact hrf) (depth + 1))
  | hmultiLambda n nms body ih =>
      intro hrf depth
      rw [applyBindingsLifting, applyBindings]
      exact congrArg (fun b => Pattern.multiLambda n nms b)
        (ih (by rw [plain] at hrf; exact hrf) (depth + n))
  | hsubst body repl _ _ =>
      intro hrf _
      rw [plain] at hrf
      exact absurd hrf (by decide)
  | hcollection ct elems rest ih =>
      intro hrf depth
      rw [plain, Bool.and_eq_true] at hrf
      have hnone : rest = none := Option.isNone_iff_eq_none.mp (by
        simpa using hrf.2)
      subst hnone
      rw [applyBindingsLifting, applyBindings]
      simp only [List.append_nil]
      exact congrArg (fun l => Pattern.collection ct l none) (List.map_congr_left
        (fun q hq => ih q hq (plain_of_mem elems hrf.1 q hq) depth))

theorem agreement_at_top_level
    (bindings : Bindings)
    (hclosed : ∀ e ∈ bindings, Pattern.isWellScopedAt 0 e.2 = true)
    (p : Pattern) (hrf : plain p = true) :
    applyBindingsLifting 0 bindings p = applyBindings bindings p :=
  lifting_eq_applyBindings_of_closed bindings hclosed p hrf 0

/-- **Closedness of the bindings cannot be dropped.**  The pattern is plain and
the two appliers still disagree. -/
theorem closedness_is_necessary :
    plain (.lambda (some "y") (.fvar "X")) = true
      ∧ Pattern.isWellScopedAt 0 (.bvar 0) = false
      ∧ applyBindingsLifting 0 [("X", Pattern.bvar 0)] (.lambda (some "y") (.fvar "X"))
          ≠ applyBindings [("X", Pattern.bvar 0)] (.lambda (some "y") (.fvar "X")) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro h
  revert h
  decide +kernel

/-- **Absence of an explicit substitution cannot be dropped.**  The binding is
closed and the two appliers still disagree: the current one evaluates the node,
the corrected one preserves it. -/
theorem substitution_node_is_necessary :
    Pattern.isWellScopedAt 0 (.apply "c" []) = true
      ∧ plain (.subst (.fvar "X") (.fvar "X")) = false
      ∧ applyBindingsLifting 0 [("X", Pattern.apply "c" [])] (.subst (.fvar "X") (.fvar "X"))
          ≠ applyBindings [("X", Pattern.apply "c" [])] (.subst (.fvar "X") (.fvar "X")) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro h
  revert h
  decide +kernel

/-- **Absence of a collection rest cannot be dropped.**  The binding is closed,
there is no explicit substitution, and the two appliers still disagree: the
current one splices the rest, the corrected one leaves it unresolved. -/
theorem collection_rest_is_necessary :
    Pattern.isWellScopedAt 0 (.collection .vec [.apply "c" []] none) = true
      ∧ plain (.collection .vec [] (some "R")) = false
      ∧ applyBindingsLifting 0 [("R", Pattern.collection .vec [.apply "c" []] none)]
            (.collection .vec [] (some "R"))
          ≠ applyBindings [("R", Pattern.collection .vec [.apply "c" []] none)]
            (.collection .vec [] (some "R")) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro h
  revert h
  decide +kernel

end StepCapture

end Mettapedia.OSLF.Binding
