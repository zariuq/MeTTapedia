import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceSpec

/-!
# Atom and Proc at the compiled argument boundary

An Atom argument retains its compiled syntax as an explicit code value. A
Proc argument allocates one memoized computation; its continuation decides
whether to demand it. Both use the existing branch-local Need calculus.

The two elimination theorems characterize all derivations of these adapters,
including their result stores and ordered alternatives. The controls separate
ordinary observation of code, explicit activation, shared demand and unused
arguments. No source reader or correspondence with a C evaluator is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Native.AtomProcArgument

open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

/-- Demand on one argument position, independent of its result's value type. -/
inductive Mode where
  | atom
  | proc
  deriving DecidableEq, Repr

/-- The continuation receives code or a shared suspension at index zero.
The producer's captured environment is unchanged in both cases. -/
def pass (mode : Mode) (producer continuation : Comp) : Comp :=
  match mode with
  | .atom => .seq (.quote producer) continuation
  | .proc => .need producer continuation

theorem atom_iff (program : Program) (store : Store) (environment : List (Val Nat))
    (producer continuation : Comp) (results : List Result) :
    Derives program (.eval store environment (pass .atom producer continuation)) results ↔
      Derives program
        (.eval (store.alloc producer environment)
          (.code store.cells.length :: environment) continuation) results := by
  constructor
  · intro evaluated
    cases evaluated with
    | seq quoted rest =>
      cases quoted
      cases rest with
      | seqKOk body tail =>
        cases tail
        simpa only [List.append_nil] using body
      | seqKStop stopped _ => simp [Outcome.isOk] at stopped
  · intro body
    exact Derives.seq_single Derives.quote body

theorem proc_iff (program : Program) (store : Store) (environment : List (Val Nat))
    (producer continuation : Comp) (results : List Result) :
    Derives program (.eval store environment (pass .proc producer continuation)) results ↔
      Derives program
        (.eval (store.alloc producer environment)
          (.need store.cells.length :: environment) continuation) results := by
  constructor
  · intro evaluated
    cases evaluated with
    | need body => exact body
  · exact Derives.need

/-- Observing a data argument does not activate it, even when the producer
contains effects, failure, divergence or nondeterministic alternatives. -/
theorem observe_atom (program : Program) (store : Store)
    (environment : List (Val Nat)) (producer : Comp) :
    Derives program
      (.eval store environment (pass .atom producer (.force (.var 0))))
      [(.ok (.code store.cells.length), store.alloc producer environment)] := by
  apply (atom_iff program store environment producer _ _).mpr
  exact Derives.force (Derives.forceWhnf rfl)

/-- An unused computation remains pending and contributes no events. -/
theorem discard_proc (program : Program) (store : Store)
    (environment : List (Val Nat)) (producer : Comp) (answer : Nat) :
    Derives program
      (.eval store environment (pass .proc producer (.ret (.sym answer))))
      [(.ok (.sym answer), store.alloc producer environment)] := by
  apply (proc_iff program store environment producer _ _).mpr
  exact Derives.ret

theorem discard_proc_trace (program : Program) (store : Store)
    (environment : List (Val Nat)) (producer : Comp) (answer : Nat)
    (results : List Result)
    (evaluated : Derives program
      (.eval store environment (pass .proc producer (.ret (.sym answer)))) results) :
    ∀ result ∈ results, result.2.trace = store.trace := by
  have exactResults := Derives.deterministic evaluated
    (discard_proc program store environment producer answer)
  subst results
  simp [Store.alloc]

/-- Every possible observation has the same inert code value and captured
producer. Determinism here is that of the reused calculus, not an assumed
property of the adapter or its native implementation. -/
theorem observe_atom_exact (program : Program) (store : Store)
    (environment : List (Val Nat)) (producer : Comp) (results : List Result)
    (evaluated : Derives program
      (.eval store environment (pass .atom producer (.force (.var 0)))) results) :
    results = [(.ok (.code store.cells.length), store.alloc producer environment)] :=
  Derives.deterministic evaluated (observe_atom program store environment producer)

namespace Controls

def producer : Comp := .emit 11 (.ret (.sym 7))

def twice : Comp := .seq (.force (.var 0)) (.force (.var 1))

def observations (mode : Mode) (body : Comp) : Option (List Result) :=
  run [] 100 (.eval Store.empty [] (pass mode producer body))

theorem data_observation_preserves_code :
    (observations .atom twice).map
        (fun results => results.map fun result => (result.1, result.2.trace)) =
      some [(.ok (.code 0), [])] := by
  decide +kernel

theorem shared_computation_emits_once :
    (observations .proc twice).map
        (fun results => results.map fun result => (result.1, result.2.trace)) =
      some [(.ok (.sym 7), [11])] := by
  decide +kernel

theorem explicit_activation_emits :
    (observations .atom (.run (.var 0))).map
        (fun results => results.map fun result => (result.1, result.2.trace)) =
      some [(.ok (.sym 7), [11])] := by
  decide +kernel

theorem discarded_computation_emits_nothing :
    (observations .proc (.ret (.sym 9))).map
        (fun results => results.map fun result => (result.1, result.2.trace)) =
      some [(.ok (.sym 9), [])] := by
  decide +kernel

theorem modes_cannot_be_erased_from_execution :
    (observations .atom twice).map (fun results => results.map (·.1)) ≠
      (observations .proc twice).map (fun results => results.map (·.1)) := by
  decide +kernel

def choosing : Comp := .choose (.ret (.sym 2)) (.ret (.sym 3))

def pairTwice : Comp :=
  .seq (.force (.var 0))
    (.seq (.force (.var 1))
      (.ret (.app (.app (.sym 5) (.var 1)) (.var 0))))

def pair (left right : Nat) : Val Nat :=
  .app (.app (.sym 5) (.sym left)) (.sym right)

theorem proc_shares_each_nondeterministic_branch :
    (run [] 100 (.eval Store.empty [] (pass .proc choosing pairTwice))).map
        (fun results => results.map (·.1)) =
      some [.ok (pair 2 2), .ok (pair 3 3)] := by
  decide +kernel

theorem resampling_changes_the_answers :
    (run [] 100 (.eval Store.empty [] (.delay choosing pairTwice))).map
        (fun results => results.map (·.1)) =
      some [.ok (pair 2 2), .ok (pair 2 3), .ok (pair 3 2), .ok (pair 3 3)] := by
  decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PrimeCandidates.Native.AtomProcArgument
