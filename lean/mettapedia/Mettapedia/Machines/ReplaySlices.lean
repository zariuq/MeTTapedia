import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Composition of independently checked execution slices

A completed prefix certificate may be opaque. Composition needs only its
actual exhaustion frontier and the suffix certificate, preserving prior
events and every terminal disposition. It does not restart the prefix.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ReplaySlices

open Mettapedia.GSLT.Distinction.ProductiveBlocks

theorem compose {State Event Verdict Request : Type} (machine : Machine State Event Verdict Request)
    (first second : Nat) (initial middle : State) (earlier later : List Event)
    (outcome : Outcome State Verdict Request)
    (head : machine.run first initial = (earlier, .exhausted middle))
    (tail : machine.run second middle = (later, outcome)) :
    machine.run (first + second) initial = (earlier ++ later, outcome) := by
  rw [Machine.run_add, head]
  simp only [Machine.continueRun, tail]

namespace Controls

def counted : Machine Nat Nat Nat Unit where
  step
    | 0 => some (.finish 0)
    | n + 1 => some (.publish [1] n)

theorem two_equal_occurrences_survive_composition : counted.run 3 2 = ([1, 1], .finished 0) := by
  simpa using compose counted 1 2 2 1 [1] [1] (.finished 0) (by rfl) (by rfl)

theorem dropping_the_prefix_is_not_composition :
    counted.run 3 2 ≠ counted.run 2 1 := by
  rw [two_equal_occurrences_survive_composition]
  intro same
  have events := congrArg (fun reply => reply.1.length) same
  norm_num [Machine.run, counted] at events

theorem a_suspended_suffix_retains_earlier_events :
    let machine : Machine Nat Nat Nat Unit := ⟨fun n =>
      if n = 0 then some (.call () 0) else some (.publish [n] 0)⟩
    machine.run 2 7 = ([7], .suspended () 0) := by rfl

end Controls

end Mettapedia.Machines.ReplaySlices
