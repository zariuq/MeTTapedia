import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierCollectionSource

/-!
# Recursive source drivers with an observable productive-round counter

A phase returns its completed next-frontier tuple. The actual authored driver
stops on an empty tuple and otherwise increments its counter and recurses.
The private allowance bounds complete phases, not evaluator steps. Exhaustion
or phase refusal remains `none`, never a fabricated successful termination.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierIterationSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval SpaceSemantics EffectfulQuerySource

structure Names where
  frontier : String
  counter : String
  next : String
  distinct : [frontier, counter, next].Nodup

def number (n : Nat) : Atom := .grounded (.int n)
def callee (names : Names) (frontier : List Atom) (count : Nat) : Subst :=
  [(names.counter, number count), (names.frontier, .expression frontier)]
def bound (names : Names) (frontier next : List Atom) (count : Nat) : Subst :=
  (names.next, .expression next) :: callee names frontier count
def condition (names : Names) : Atom := .expression [.symbol "==", .var names.next, .expression []]
def increment (names : Names) : Atom := .expression [.symbol "+", .var names.counter, number 1]
def recursiveCall (driver : String) (names : Names) : Atom :=
  .expression [.symbol driver, .var names.next, increment names]
def body (driver : String) (names : Names) (phase : Atom) : Atom :=
  .expression [.symbol "let", .var names.next, phase,
    .expression [.symbol "if", condition names, .var names.counter, recursiveCall driver names]]

def iterate (worker : Body) (names : Names) : Nat → List Atom → Nat → Effects.State → Option (Effects.State × Nat)
  | 0, _, _, _ => none
  | fuel + 1, frontier, count, before => do
      let result ← worker (callee names frontier count) before
      if result.2 = [] then some (result.1, count)
      else iterate worker names fuel result.2 (count + 1) result.1

structure Certificate (program : Program) (driver : String) (names : Names) (phase : Atom) : Type where
  notIO : ioHead driver = false
  notNative : StdLib.known driver = false
  notControl : driver ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"]
  registered : program.equations.any (·.head == driver) = true
  counterDemanded : argumentIsRaw program driver 1 = false
  selected : ∀ frontier count, clauses program driver [.expression frontier, number count] =
    [.evaluate (callee names frontier count) (body driver names phase)]

private theorem fresh (names : Names) (frontier : List Atom) (count : Nat) :
    Subst.lookup (callee names frontier count) names.next = none := by
  have distinct : (names.frontier ≠ names.counter ∧ names.frontier ≠ names.next) ∧ names.counter ≠ names.next := by
    simpa using names.distinct
  simp [callee, Subst.lookup, distinct.1.2, distinct.2]

private theorem read_counter (names : Names) (frontier next : List Atom) (count : Nat) :
    applySubst (bound names frontier next count) (.var names.counter) = number count := by
  have distinct : (names.frontier ≠ names.counter ∧ names.frontier ≠ names.next) ∧ names.counter ≠ names.next := by
    simpa using names.distinct
  simp [applySubst, bound, callee, Subst.lookup, Ne.symm distinct.2]

theorem condition_returns (program : Program) (names : Names) (frontier next : List Atom)
    (count : Nat) (state : Effects.State) :
    PureReturns program (bound names frontier next count) state (condition names) state
      (Effects.boolean (decide (next = []))) := by
  have empty : PureReturns program (bound names frontier next count) state (.expression []) state (.expression []) :=
    .step (step_transition rfl) (.step (step_transition rfl) (.refl _))
  apply native_binary_call_returns program _ state state state state "==" _ _ _ _ _
    (by decide) (by decide)
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (by simpa [applySubst, bound, Subst.lookup] using variable_returns program (bound names frontier next count) state names.next)
    empty _ (by decide)
  have equal : (Atom.expression next == Atom.expression []) = decide (next = []) := by
    apply Bool.eq_iff_iff.mpr
    simp
  simp only [StdLib.structural_equality, equal]

theorem increment_returns (program : Program) (names : Names) (frontier next : List Atom)
    (count : Nat) (state : Effects.State) :
    PureReturns program (bound names frontier next count) state (increment names) state (number (count + 1)) := by
  apply native_binary_call_returns program _ state state state state "+" _ _ _ _ _
    (by decide) (by decide)
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (by simpa only [read_counter] using variable_returns program (bound names frontier next count) state names.counter)
    (grounded_returns program _ state (.int 1)) _ (by decide)
  change Except.ok (state, [Atom.grounded (.int ((count : Int) + 1))]) = _
  simp [number]

theorem body_returns {program : Program} {driver : String} {names : Names} {phase : Atom}
    (certificate : Certificate program driver names phase) (worker : Body)
    (law : ∀ bindings before after next, worker bindings before = some (after, next) →
      PureReturns program bindings before phase after (.expression next))
    (fuel : Nat) (frontier : List Atom) (count : Nat) (before after : Effects.State) (result : Nat)
    (completed : iterate worker names fuel frontier count before = some (after, result)) :
    PureReturns program (callee names frontier count) before (body driver names phase) after (number result) := by
  induction fuel generalizing frontier count before after result with
  | zero => cases completed
  | succ fuel ih =>
      obtain ⟨first, ran, tail⟩ := Option.bind_eq_some_iff.mp completed
      apply let_returns program (callee names frontier count) (bound names frontier first.2 count)
        before first.1 after (.var names.next) phase _ (.expression first.2) _ (law _ _ _ _ ran)
        (by simp [matchBinding, matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, fresh, bound])
      have tested := condition_returns program names frontier first.2 count first.1
      split at tail
      next quiet =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj tail)
        apply if_returns program _ first.1 first.1 first.1 _ (Effects.boolean true) _ _ _
          (by simpa only [quiet, decide_true] using tested)
        simpa [Effects.boolean, read_counter] using variable_returns program (bound names frontier first.2 count) first.1 names.counter
      next productive =>
        have continued := ih first.2 (count + 1) first.1 after result tail
        have invoked := authored_function_arguments_return program (bound names frontier first.2 count)
          (callee names first.2 (count + 1)) first.1 after driver [.expression first.2, number (count + 1)] 2
          _ _ certificate.notIO certificate.notNative (certificate.selected first.2 (count + 1)) continued
        have computed := evaluated_argument_returns program (bound names frontier first.2 count) first.1 first.1 after
          (.function driver) (increment names) (number (count + 1)) (number result) [] [.expression first.2] 1
          certificate.counterDemanded (increment_returns program names frontier first.2 count first.1) invoked
        have argumentPath := variable_prefix_arguments_return program (bound names frontier first.2 count) first.1 after
          (.function driver) [names.next] [increment names] [] 0 (number result)
          (by simpa [applySubst, bound, Subst.lookup] using computed)
        have recursive := Eval.call_returns program (bound names frontier first.2 count) first.1 after driver _ _
          (by simp [certificate.registered]) argumentPath certificate.notControl
        apply if_returns program _ first.1 first.1 after _ (Effects.boolean false) _ _ _
          (by simpa only [productive, decide_false] using tested)
        simpa [Effects.boolean, recursiveCall] using recursive

theorem call_returns {program : Program} {driver : String} {names : Names} {phase : Atom}
    (certificate : Certificate program driver names phase) (worker : Body)
    (law : ∀ bindings before after next, worker bindings before = some (after, next) →
      PureReturns program bindings before phase after (.expression next))
    (fuel : Nat) (frontier : List Atom) (count : Nat) (before after : Effects.State) (result : Nat)
    (completed : iterate worker names fuel frontier count before = some (after, result)) :
    PureReturns program (callee names frontier count) before
      (.expression [.symbol driver, .var names.frontier, .var names.counter]) after (number result) := by
  have different : names.frontier ≠ names.counter := by
    have distinct := names.distinct
    simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
    exact distinct.1.1
  apply authored_variable_call_returns program (callee names frontier count) (callee names frontier count)
    before after driver [names.frontier, names.counter] _ _ certificate.notIO certificate.notNative
    certificate.registered _ (body_returns certificate worker law fuel frontier count before after result completed)
    (by have h := certificate.notControl
        simp only [List.mem_cons, not_or] at h ⊢
        tauto)
  simpa [applySubst, callee, Subst.lookup, Ne.symm different] using certificate.selected frontier count

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierIterationSource
