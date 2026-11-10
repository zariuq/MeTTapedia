import Mettapedia.Machines.QueryState
import Mettapedia.GSLT.Core.NonFactorization
import Mathlib.Tactic

/-!
# Operator specialization relative to future observations

The state-threaded interpreter is `QueryState.run`, including adaptive
continuations and the ordered sequence of replies. A representation map is
usable by every such finite client when each service operation commutes with
the map and preserves the represented-state invariant. Merely retaining the
current answer is insufficient: an operation can expose erased information.

The service equation below concerns replies and state transitions. It is not
`FrameMap.LicensedAt` in constraint-multiset dispatch, whose obligations concern
solution factorization and reflection of solvability. Neither condition is a
runtime cost bound. All clients in this module are finite inductive programs;
the cursor protocol separately treats suspension and nonterminating clients.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OperatorChoice.ObserverContracts

open Mettapedia.Machines.ReadOnlyQuery (Program)
open Mettapedia.Machines.QueryState
open Mettapedia.GSLT.Core.NonFactorization

variable {Key Reply Answer State Representation : Type}

/-- Only state representation is changed; answers and occurrence traces remain. -/
def eraseObservation (erase : State → Representation)
    (result : Observation Key Reply Answer State) :
    Observation Key Reply Answer Representation :=
  ⟨result.answer, erase result.state, result.reads⟩

/-- A local commuting equation and a maintained invariant suffice for all
finite adaptive clients, including their full ordered reply history. -/
theorem run_erasure_on
    (source : State → Key → Reply × State)
    (target : Representation → Key → Reply × Representation)
    (erase : State → Representation) (valid : State → Prop)
    (closed : ∀ state, valid state → ∀ key, valid (source state key).2)
    (step : ∀ state, valid state → ∀ key,
      target (erase state) key = ((source state key).1, erase (source state key).2))
    (program : Program Key Reply Answer) (state : State) (good : valid state) :
    run target program (erase state) = eraseObservation erase (run source program state) := by
  induction program generalizing state with
  | pure answer => rfl
  | read key next ih =>
      simp only [run, step state good key]
      rw [ih (source state key).1 _ (closed state good key)]
      rfl

/-- The observer of answer and reply history factors through the representation
on exactly the invariant domain established by the caller. -/
theorem observed_run_factors_on
    (source : State → Key → Reply × State)
    (target : Representation → Key → Reply × Representation)
    (erase : State → Representation) (valid : State → Prop)
    (closed : ∀ state, valid state → ∀ key, valid (source state key).2)
    (step : ∀ state, valid state → ∀ key,
      target (erase state) key = ((source state key).1, erase (source state key).2))
    (program : Program Key Reply Answer) :
    Factors (fun state : {s // valid s} => erase state.val)
      (fun state : {s // valid s} =>
        ((run source program state.val).answer, (run source program state.val).reads)) := by
  refine ⟨fun rep => ((run target program rep).answer, (run target program rep).reads), ?_⟩
  intro state
  dsimp only
  rw [run_erasure_on source target erase valid closed step program state.val state.property]
  rfl

/-- Preservation for even the one-request clients forces the same local
equation. Thus agreement of all adaptive clients cannot repair a bad lowering. -/
theorem step_of_single_request
    (source : State → Key → Reply × State)
    (target : Representation → Key → Reply × Representation)
    (erase : State → Representation) (state : State)
    (preserves : ∀ key,
      run target (.read key .pure : Program Key Reply Reply) (erase state) =
        eraseObservation erase (run source (.read key .pure) state)) :
    ∀ key, target (erase state) key = ((source state key).1, erase (source state key).2) := by
  intro key
  have same := preserves key
  have answers := congrArg Observation.answer same
  have states := congrArg Observation.state same
  exact Prod.ext answers states

namespace Residue

/-- The source really retains an unbounded counter and independently computes
the next residue as its reply. -/
def source (modulus : Nat) (counter increment : Nat) : Nat × Nat :=
  ((counter + increment) % modulus, counter + increment)

/-- The specialized representation retains only a residue. -/
def target (modulus : Nat) (residue increment : Nat) : Nat × Nat :=
  let next := (residue + increment) % modulus
  (next, next)

theorem service_square (modulus counter increment : Nat) :
    target modulus (counter % modulus) increment =
      ((source modulus counter increment).1,
        (source modulus counter increment).2 % modulus) := by
  simp [source, target, Nat.add_mod]

/-- Arbitrary adaptive programs over increment-and-observe can use the
smaller representation. This is not an assertion that all counter observers
or all possible counter operations descend to residues. -/
theorem adaptive_specialization (modulus : Nat) (program : Program Nat Nat Answer)
    (counter : Nat) :
    run (target modulus) program (counter % modulus) =
      eraseObservation (fun n => n % modulus) (run (source modulus) program counter) := by
  induction program generalizing counter with
  | pure answer => rfl
  | read increment next ih =>
      simp only [run, service_square]
      rw [ih]
      rfl

/-- The representation genuinely forgets state; the positive theorem is not
an invertible renaming of the original counter. -/
theorem noninjective : ¬ Function.Injective (fun n : Nat => n % 2) := by
  intro injective
  have impossible := injective (a₁ := 0) (a₂ := 2) (by decide)
  omega

/-- Adding an exact-counter observer makes this specialization invalid. -/
theorem exact_counter_not_retained : ¬ Factors (fun n : Nat => n % 2) id := by
  exact (show NonTrivialFiber (fun n : Nat => n % 2) id from
    ⟨0, 2, rfl, by decide⟩).not_factors

end Residue

namespace HiddenState

/-- A later operation exposes a bit hidden by the current numeric observer. -/
def expose (state : Nat × Bool) (_ : Unit) : Nat × (Nat × Bool) :=
  let value := if state.2 then 1 else 0
  (value, (value, state.2))

theorem current_agreement_loses_future_agreement :
    (0, false).1 = (0, true).1 ∧
      (run expose (.read () .pure : Program Unit Nat Nat) (0, false)).answer ≠
        (run expose (.read () .pure) (0, true)).answer := by
  exact ⟨rfl, by decide⟩

/-- No implementation that receives only the current numeric field can
implement this service for both erased states. -/
theorem no_erased_service :
    ¬ ∃ target : Nat → Unit → Nat × Nat,
      ∀ state key, target state.1 key =
        ((expose state key).1, (expose state key).2.1) := by
  rintro ⟨target, square⟩
  have left := square (0, false) ()
  have right := square (0, true) ()
  have impossible := congrArg Prod.fst (left.symm.trans right)
  change (0 : Nat) = 1 at impossible
  omega

end HiddenState

end Mettapedia.Machines.OperatorChoice.ObserverContracts
