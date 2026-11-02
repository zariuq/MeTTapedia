import Mettapedia.Languages.MeTTa.PeTTa.FoldSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.OptionalCallExtraction
import Mettapedia.Machines.PrivateScalarFold

/-!
# Source-certified callbacks for a captured fold driver

Preparation follows each actual source callback with its own accumulator and
item bindings. A complete private attempt carries a derivation of the fold
driver for every effect state. It does not equate a source callback with an
uninterpreted step function or run a source effect during failed preparation.

The callback trace retains every intermediate accumulator, distinguishing the
stronger prefix observer from a final-value observer. The captured host driver
is specified in `FoldSource`, separately from outer evaluator dispatch.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldCallbackExtraction

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics FoldSource

structure Prepared (program : Program) (callback : Callback) (items : List Atom) (initial : Atom) where
  result : Atom
  trace : List Atom
  returns : ∀ state, Evaluates program callback state items initial result
  prefixes : ∀ state, Trace program callback state items initial trace

def prepare (budget : Nat) (program : Program) (callback : Callback) :
    (items : List Atom) → (initial : Atom) → Option (Prepared program callback items initial)
  | [], initial => some ⟨initial, [], fun _ => .nil _, fun _ => .nil _⟩
  | item :: rest, initial => do
      let optional ← OptionalCallExtraction.prepare budget program
        (bindings callback initial item) (expression callback)
      let called ← OptionalCallExtraction.singleton optional
      let later ← prepare budget program callback rest called.value
      return ⟨later.result, called.value :: later.trace,
        fun state => .cons (called.returns state) (later.returns state),
        fun state => .cons (called.returns state) (later.prefixes state)⟩

def callbackStep (budget : Nat) (program : Program) (callback : Callback)
    (accumulator item : Atom) : Option Atom :=
  (OptionalCallExtraction.prepare budget program (bindings callback accumulator item) (expression callback)).bind
    fun optional => (OptionalCallExtraction.singleton optional).map PureCallExtraction.Certified.value

theorem callbackStep_source (budget : Nat) (program : Program) (callback : Callback)
    (accumulator item value : Atom) (accepted : callbackStep budget program callback accumulator item = some value)
    (state : Effects.State) : Invokes program callback state accumulator item value := by
  obtain ⟨optional, _, rest⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨called, _, same⟩ := Option.map_eq_some_iff.mp rest
  rw [← same]
  exact called.returns state

/-- The existing private-fold executor is now discharged by actual source
callback proofs, including refusal/cancellation separation. -/
theorem private_attempt_source (budget : Nat) (program : Program) (callback : Callback)
    (cancel : Nat → Bool) (index : Nat) (items : List Atom) (initial result : Atom)
    (accepted : Mettapedia.Machines.PrivateScalarFold.attempt (callbackStep budget program callback)
      cancel index items initial = .value result) (state : Effects.State) :
    Evaluates program callback state items initial result := by
  induction items generalizing initial index with
  | nil =>
      have same : initial = result := by simpa [Mettapedia.Machines.PrivateScalarFold.attempt] using accepted
      subst result
      exact .nil _
  | cons item rest ih =>
      by_cases stopped : cancel index = true
      · simp [Mettapedia.Machines.PrivateScalarFold.attempt, stopped] at accepted
      · cases called : callbackStep budget program callback initial item with
        | none => simp [Mettapedia.Machines.PrivateScalarFold.attempt, stopped, called] at accepted
        | some next =>
            exact .cons (callbackStep_source budget program callback initial item next called state)
              (ih (index + 1) next (by
                simpa [Mettapedia.Machines.PrivateScalarFold.attempt, stopped, called] using accepted))

theorem prepared_prefix_count {program : Program} {callback : Callback} {items : List Atom} {initial : Atom}
    (prepared : Prepared program callback items initial) (state : Effects.State) :
    prepared.trace.length = items.length := trace_length (prepared.prefixes state)

theorem prepared_result_exact {program : Program} {callback : Callback} {items : List Atom} {initial : Atom}
    (prepared : Prepared program callback items initial) (state : Effects.State) (value : Atom) :
    Evaluates program callback state items initial value ↔ value = prepared.result := by
  constructor
  · intro result
    exact evaluates_unique result (prepared.returns state)
  · rintro rfl
    exact prepared.returns state

theorem split_result {program : Program} {callback : Callback} {first later : List Atom}
    {initial : Atom} (one : Prepared program callback first initial)
    (two : Prepared program callback later one.result) (state : Effects.State) :
    Evaluates program callback state (first ++ later) initial two.result :=
  evaluates_append (one.returns state) (two.returns state)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldCallbackExtraction
