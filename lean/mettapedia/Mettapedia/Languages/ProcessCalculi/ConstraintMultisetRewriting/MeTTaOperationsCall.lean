import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsCollapse

/-!
# A function call as a fresh read of a stored equation

Evaluating `(f 3)` against `(= (f $x) body)` reads one stored equation through
the pattern `(= (f 3) $r)` and continues with `$r`. This is the single-read
encoding of `MeTTaOperationsMatch` on equation atoms, with the stored equation
opened once per use. Each equation that matches is a separate valid firing at
the same store; the answers form a bag, as for `match`.

* `Probe.closed_call`: with `(= (f $x) (g $x))` and `(= (f 0) zero)`, the call
  `(f 0)` has exactly the two answers `(g 0)` and `zero`.
* `Probe.open_call_binds_caller`: the open call `(f $y)` through the second
  equation binds the caller's `y` to `0` in every solution, giving
  `(pair 0 zero)`; through the first it reads `(g y)` with `y` still open.
  Hyperon Experimental, PeTTa and the CeTTa draft print both answers.
* `Probe.shared_equation_conflates_calls`: reading one stored equation without
  opening it lets the first call `(f 3)` fix its variable for the second call
  `(f 4)`. `Probe.fresh_equation_serves_both` opens a copy per call.
* `Probe.no_equation_returns_call`: `(g 0)` with no equation for `g` is one
  firing with an `absent` check; the check fails once `(= (g $z) w)` is stored.

The existing adequacy results cover the two halves of a call separately.
`NeedMachine.source_derivation_iff` relates every derivation of the
CallTimeChoice source to ordinary firing paths: dispatch to every rule with
the call's head and arity in program order, ordered results with
multiplicity, call-time choice, memoized and resampled suspensions, effects
and quotation. Its arguments are values; head patterns are cases in bodies,
not unification with caller variables. The first-order Horn modules
(`FirstOrderHornActivations`, `LinearHornAdequacy`, `ActivatedHornProofs`)
cover per-use activation and unification with logic variables, without
evaluation order, sharing or effects. Their composition is not yet proved.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsCall

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (fire)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsMatch

/-- A stored equation `(= head body)`. -/
def eqn (head body : Atom) : Atom := .expression [.symbol "=", head, body]

/-- A call reads one equation through `(= call $result)` and continues with
`continuation`, which mentions `$result`. -/
def callRule (call : Atom) (result : Var) (continuation : Atom) : RuleInstance Atom :=
  rule (eqn call (.var result)) continuation

theorem subst_eqn (σ : Subst) (head body : Atom) :
    subst σ (eqn head body) = eqn (subst σ head) (subst σ body) := by
  simp [eqn, subst, subst.substList]

theorem eqn_inj {h₁ b₁ h₂ b₂ : Atom} (same : eqn h₁ b₁ = eqn h₂ b₂) : h₁ = h₂ ∧ b₁ = b₂ := by
  simpa [eqn] using same

namespace Probe

open Insertion (wrap)

def zero : Atom := .symbol "0"
def three : Atom := .symbol "3"
def four : Atom := .symbol "4"
def zeroValue : Atom := .symbol "zero"
def f (value : Atom) : Atom := wrap "f" value
def g (value : Atom) : Atom := wrap "g" value
def pair (first second : Atom) : Atom := .expression [.symbol "pair", first, second]

/-- Occurrence 0 stores `(= (f $x1) (g $x1))`, opened for this use; occurrence
1 stores `(= (f 0) zero)`. Outputs carry the template. -/
def label (template : Atom) (n : Nat) : Atom :=
  if n = 0 then eqn (f (.var "x1")) (g (.var "x1"))
  else if n = 1 then eqn (f zero) zeroValue else template

def before : Configuration Atom Nat := ⟨[], {0, 1}⟩

def r : Atom := .var "r"
def y : Atom := .var "y"

theorem first_equation_answer :
    (selection 0 2).Valid atomAction (label r) (callRule (f zero) "r" r) before ∧
      ∀ σ, atomAction.Models σ ((selection 0 2).result (label r) (callRule (f zero) "r" r) before).equations →
        subst σ r = g zero := by
  constructor
  · refine (valid_iff (label r) _ _ before 0 2).mpr ⟨by decide, by decide, rfl, ?_⟩
    refine ⟨fun v => if v = "x1" then some zero else if v = "r" then some (g zero) else none, ?_⟩
    intro e member
    simp only [before, List.nil_append, List.mem_singleton] at member
    subst member
    change subst _ (eqn (f zero) (.var "r")) = subst _ (label r 0)
    simp [label, eqn, f, g, zero, wrap, subst, subst.substList]
  · intro σ solved
    have equation := solved (eqn (f zero) (.var "r"), label r 0)
      (by simp [Selection.result, problem_eq, before, callRule])
    change subst σ (eqn (f zero) (.var "r")) = subst σ (label r 0) at equation
    simp only [label, if_true, subst_eqn, f, g, Insertion.subst_wrap] at equation
    obtain ⟨heads, bodies⟩ := eqn_inj equation
    have argument : subst σ zero = subst σ (.var "x1") := by simpa [wrap] using heads
    rw [show subst σ zero = zero from rfl] at argument
    change subst σ (.var "r") = g zero
    rw [bodies, show g zero = wrap "g" zero from rfl, argument]

theorem second_equation_answer :
    (selection 1 2).Valid atomAction (label r) (callRule (f zero) "r" r) before ∧
      ∀ σ, atomAction.Models σ ((selection 1 2).result (label r) (callRule (f zero) "r" r) before).equations →
        subst σ r = zeroValue := by
  constructor
  · refine (valid_iff (label r) _ _ before 1 2).mpr ⟨by decide, by decide, rfl, ?_⟩
    refine ⟨fun v => if v = "r" then some zeroValue else none, ?_⟩
    intro e member
    simp only [before, List.nil_append, List.mem_singleton] at member
    subst member
    change subst _ (eqn (f zero) (.var "r")) = subst _ (label r 1)
    simp [label, eqn, f, zero, zeroValue, wrap, subst, subst.substList]
  · intro σ solved
    have equation := solved (eqn (f zero) (.var "r"), label r 1)
      (by simp [Selection.result, problem_eq, before, callRule])
    change subst σ (eqn (f zero) (.var "r")) = subst σ (label r 1) at equation
    simp only [label, show (1 : Nat) ≠ 0 by decide, if_false, if_true, subst_eqn] at equation
    exact (eqn_inj equation).2

/-- The call `(f 0)` has exactly two valid answer firings, one per equation. -/
theorem closed_call :
    answerOccurrences (label r) (eqn (f zero) r) r before = {0, 1} := by
  ext o
  rw [MeTTaOperationsCollapse.mem_answerOccurrences_iff_consistent (label := label r)
    (pattern := eqn (f zero) r) (template := r) (before := before) ⟨2, by decide, rfl⟩]
  constructor
  · rintro ⟨present, _⟩
    simpa [before] using present
  · intro member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact ⟨by decide, (valid_iff (label r) _ _ before 0 2).mp first_equation_answer.1 |>.2.2.2⟩
    · exact ⟨by decide, (valid_iff (label r) _ _ before 1 2).mp second_equation_answer.1 |>.2.2.2⟩

/-- The open call `(f $y)` through `(= (f 0) zero)` binds the caller's `y`. -/
theorem open_call_binds_caller :
    (selection 1 2).Valid atomAction (label (pair y r)) (callRule (f y) "r" (pair y r)) before ∧
      ∀ σ, atomAction.Models σ
          ((selection 1 2).result (label (pair y r)) (callRule (f y) "r" (pair y r)) before).equations →
        subst σ (pair y r) = pair zero zeroValue := by
  constructor
  · refine (valid_iff (label (pair y r)) _ _ before 1 2).mpr ⟨by decide, by decide, rfl, ?_⟩
    refine ⟨fun v => if v = "y" then some zero else if v = "r" then some zeroValue else none, ?_⟩
    intro e member
    simp only [before, List.nil_append, List.mem_singleton] at member
    subst member
    change subst _ (eqn (f y) (.var "r")) = subst _ (label (pair y r) 1)
    simp [label, eqn, f, y, zero, zeroValue, wrap, subst, subst.substList]
  · intro σ solved
    have equation := solved (eqn (f y) (.var "r"), label (pair y r) 1)
      (by simp [Selection.result, problem_eq, before, callRule])
    change subst σ (eqn (f y) (.var "r")) = subst σ (label (pair y r) 1) at equation
    simp only [label, show (1 : Nat) ≠ 0 by decide, if_false, if_true, subst_eqn, f,
      Insertion.subst_wrap] at equation
    obtain ⟨heads, bodies⟩ := eqn_inj equation
    have argument : subst σ y = zero := by simpa [wrap, zero, subst] using heads
    simp only [pair, subst, subst.substList]
    change Atom.expression [.symbol "pair", subst σ y, subst σ (.var "r")] = _
    rw [argument, bodies]
    rfl

/-- Through `(= (f $x1) (g $x1))` the open call reads `(g y)` with `y` open. -/
theorem open_call_keeps_variable :
    (selection 0 2).Valid atomAction (label (pair y r)) (callRule (f y) "r" (pair y r)) before ∧
      ∀ σ, atomAction.Models σ
          ((selection 0 2).result (label (pair y r)) (callRule (f y) "r" (pair y r)) before).equations →
        subst σ (pair y r) = pair (subst σ y) (g (subst σ y)) := by
  constructor
  · refine (valid_iff (label (pair y r)) _ _ before 0 2).mpr ⟨by decide, by decide, rfl, ?_⟩
    refine ⟨fun v => if v = "x1" then some y else if v = "r" then some (g y) else none, ?_⟩
    intro e member
    simp only [before, List.nil_append, List.mem_singleton] at member
    subst member
    change subst _ (eqn (f y) (.var "r")) = subst _ (label (pair y r) 0)
    simp [label, eqn, f, g, y, wrap, subst, subst.substList]
  · intro σ solved
    have equation := solved (eqn (f y) (.var "r"), label (pair y r) 0)
      (by simp [Selection.result, problem_eq, before, callRule])
    change subst σ (eqn (f y) (.var "r")) = subst σ (label (pair y r) 0) at equation
    simp only [label, if_true, subst_eqn, f, g, Insertion.subst_wrap] at equation
    obtain ⟨heads, bodies⟩ := eqn_inj equation
    have argument : subst σ y = subst σ (.var "x1") := by simpa [wrap] using heads
    simp only [pair, subst, subst.substList]
    change Atom.expression [.symbol "pair", subst σ y, subst σ (.var "r")] =
      Atom.expression [.symbol "pair", subst σ y, g (subst σ y)]
    rw [bodies, argument]
    rfl

/-- One stored equation read twice without opening: the call `(f 3)` fixes
`x1`, and the call `(f 4)` through the same occurrence is refused. -/
theorem shared_equation_conflates_calls :
    (selection 0 2).Valid atomAction (label r) (callRule (f three) "r" r) before ∧
      ¬ (selection 0 3).Valid atomAction (label r) (callRule (f four) "s" (.var "s"))
        ((selection 0 2).result (label r) (callRule (f three) "r" r) before) := by
  constructor
  · refine (valid_iff (label r) _ _ before 0 2).mpr ⟨by decide, by decide, rfl, ?_⟩
    refine ⟨fun v => if v = "x1" then some three else if v = "r" then some (g three) else none, ?_⟩
    intro e member
    simp only [before, List.nil_append, List.mem_singleton] at member
    subst member
    change subst _ (eqn (f three) (.var "r")) = subst _ (label r 0)
    simp [label, eqn, f, g, three, wrap, subst, subst.substList]
  · intro valid
    obtain ⟨_, _, _, ⟨σ, solved⟩⟩ := (valid_iff _ _ _ _ 0 3).mp valid
    have first := solved (eqn (f three) (.var "r"), label r 0)
      (by simp [Selection.result, problem_eq, before, callRule])
    have second := solved (eqn (f four) (.var "s"), label r 0)
      (by simp [Selection.result, problem_eq, before, callRule])
    change subst σ (eqn (f three) (.var "r")) = subst σ (label r 0) at first
    change subst σ (eqn (f four) (.var "s")) = subst σ (label r 0) at second
    simp only [label, if_true, subst_eqn, f, Insertion.subst_wrap] at first second
    have one := (eqn_inj first).1
    have two := (eqn_inj second).1
    simp only [wrap, Atom.expression.injEq, List.cons.injEq, true_and, and_true] at one two
    have same := one.trans two.symm
    simp [three, four, subst] at same

/-- Opening a second copy `(= (f $x2) (g $x2))` serves the second call. -/
def openedLabel (n : Nat) : Atom :=
  if n = 0 then eqn (f (.var "x1")) (g (.var "x1"))
  else if n = 1 then eqn (f (.var "x2")) (g (.var "x2")) else r

theorem fresh_equation_serves_both :
    (selection 1 3).Valid atomAction openedLabel (callRule (f four) "s" r)
      ((selection 0 2).result openedLabel (callRule (f three) "r" r) ⟨[], {0, 1}⟩) := by
  refine (valid_iff openedLabel _ _ _ 1 3).mpr ⟨?_, ?_, rfl, ?_⟩
  · simp [Selection.result, fire, Selection.commit, selection]
  · simp [Selection.result, fire, Selection.commit, selection]
  · refine ⟨fun v => if v = "x1" then some three else if v = "r" then some (g three)
      else if v = "x2" then some four else if v = "s" then some (g four) else none, ?_⟩
    intro e member
    simp [Selection.result, problem_eq, callRule] at member
    rcases member with rfl | rfl
    · change subst _ (eqn (f three) (.var "r")) = subst _ (openedLabel 0)
      simp [openedLabel, eqn, f, g, three, four, wrap, subst, subst.substList]
    · change subst _ (eqn (f four) (.var "s")) = subst _ (openedLabel 1)
      simp [openedLabel, eqn, f, g, three, four, wrap, subst, subst.substList]

/-! ### No equation: the call is its own value -/

def evalToken (call : Atom) : Atom := wrap "eval" call
def valueToken (call : Atom) : Atom := wrap "value" call

/-- Take the evaluation request, check that no stored equation has the call as
its head, and produce the call itself as the value. -/
def noMatchRule (call : Atom) : RuleInstance Atom :=
  ⟨[evalToken call], [], [], [.absent (eqn call (.var "w"))], [valueToken call]⟩

def noMatchLabel (n : Nat) : Atom :=
  if n = 0 then eqn (f (.var "x1")) (g (.var "x1"))
  else if n = 1 then eqn (f zero) zeroValue
  else if n = 2 then evalToken (g zero) else valueToken (g zero)

def noMatchBefore : Configuration Atom Nat := ⟨[], {0, 1, 2}⟩

/-- `(g 0)` has no equation: one firing returns it, as Hyperon Experimental
returns `(g 0)` for `(f 0)` through `(= (f $x) (g $x))`. -/
theorem no_equation_returns_call :
    (⟨[2], [], [3]⟩ : Selection Nat).Valid atomAction noMatchLabel (noMatchRule (g zero)) noMatchBefore := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · refine ⟨empty, ?_⟩
    intro e member
    simp [Selection.problem, Selection.equations, noMatchRule, noMatchBefore] at member
    subst member
    rfl
  · intro check member σ _
    simp only [noMatchRule, List.mem_singleton] at member
    subst member
    intro o present
    simp only [noMatchBefore, Finset.mem_insert, Finset.mem_singleton] at present
    change ¬ subst σ (eqn (g zero) (.var "w")) = subst σ (noMatchLabel o)
    rcases present with rfl | rfl | rfl <;>
      simp [noMatchLabel, eqn, f, g, zero, zeroValue, evalToken, wrap, subst, subst.substList]

/-- A stored `(= (g $z) w)` refutes the same check: the rule is the negation
of an instance, so it is not monotone in the stored equations. -/
def withEquationLabel (n : Nat) : Atom :=
  if n = 4 then eqn (g (.var "z")) (.symbol "w0") else noMatchLabel n

theorem stored_equation_blocks_return :
    ¬ (⟨[2], [], [3]⟩ : Selection Nat).Valid atomAction withEquationLabel (noMatchRule (g zero))
      ⟨[], {0, 1, 2, 4}⟩ := by
  intro valid
  have check := valid.checks (.absent (eqn (g zero) (.var "w"))) (by simp [noMatchRule])
    (fun v => if v = "z" then some zero else if v = "w" then some (.symbol "w0") else none)
  have holds := check (by
    intro e member
    simp [Selection.problem, Selection.equations, noMatchRule] at member
    subst member
    rfl) 4 (by decide)
  apply holds
  change subst _ _ = subst _ _
  simp [withEquationLabel, eqn, g, zero, wrap, subst, subst.substList]

end Probe

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsCall
