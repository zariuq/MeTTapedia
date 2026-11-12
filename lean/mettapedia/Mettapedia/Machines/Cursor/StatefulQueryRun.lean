import Mettapedia.Machines.Cursor.QueryCore
import Mettapedia.Machines.QueryState

/-!
# Completion of finite stateful query clients by the common cursor

The recursive reference interpreter and the bounded cursor agree on the
actual answer, final service state, ordered request/reply history and invoice.
Each visited request needs one inspection; observing the terminal return needs
one more. A service call's internal work remains outside that inspection count.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.StatefulQueryRun

open Mettapedia.Machines.ReadOnlyQuery (Program Reads)
open Cursor.ReadOnlyQuery

variable {Key Reply Answer World : Type}

def invoice (price : Key → Nat) (reads : Reads Key Reply) : Nat :=
  (reads.map fun entry => price entry.1).sum

theorem advance_pure (sample : World → Key → Reply × World) (price : Key → Nat)
    (fuel : Nat) (answer : Answer) (world : World) (reads : Reads Key Reply) :
    Sampled.advance sample price (fuel + 1) (.pure answer) world reads =
      (0, .done ⟨PUnit.unit, answer, world, reads⟩) := rfl

theorem advance_read (sample : World → Key → Reply × World) (price : Key → Nat)
    (fuel : Nat) (key : Key) (next : Reply → Program Key Reply Answer)
    (world : World) (reads : Reads Key Reply) :
    Sampled.advance sample price (fuel + 1) (.read key next) world reads =
      let observed := sample world key
      let later := Sampled.advance sample price fuel (next observed.1) observed.2
        ((key, observed.1) :: reads)
      (price key + later.1, later.2) := rfl

/-- The bound and invoice come from requests actually executed by the
independent reference, including early error replies and adaptive branches. -/
theorem completed_run (sample : World → Key → Reply × World) (price : Key → Nat)
    (program : Program Key Reply Answer) (world : World) (reads : Reads Key Reply) :
    let result := QueryState.run sample program world
    Sampled.advance sample price (result.reads.length + 1) program world reads =
      (invoice price result.reads,
        .done ⟨PUnit.unit, result.answer, result.state, result.reads.reverse ++ reads⟩) := by
  induction program generalizing world reads with
  | pure answer => rfl
  | read key next ih =>
      simp only [QueryState.run, List.length_cons, advance_read]
      rw [ih]
      simp [invoice, List.reverse_cons, List.append_assoc]

theorem completed_answer (sample : World → Key → Reply × World) (price : Key → Nat)
    (program : Program Key Reply Answer) (world : World) :
    let result := QueryState.run sample program world
    let observed := Sampled.advance sample price (result.reads.length + 1) program world []
    Sampled.completed? sample observed.2 = some ⟨result.answer, result.reads⟩ ∧
      (Sampled.savedState sample observed.2).1 = result.state ∧
      observed.1 = invoice price result.reads := by
  dsimp only
  rw [completed_run]
  simp [Sampled.completed?, Sampled.savedState]

/-- A larger scheduler allowance cannot execute anything after the client's
return. The bound still counts actual requests, not all possible branches. -/
theorem completed_above (sample : World → Key → Reply × World) (price : Key → Nat)
    (program : Program Key Reply Answer) (world : World) (reads : Reads Key Reply)
    (fuel : Nat) (enough : (QueryState.run sample program world).reads.length + 1 ≤ fuel) :
    let result := QueryState.run sample program world
    Sampled.advance sample price fuel program world reads =
      (invoice price result.reads,
        .done ⟨PUnit.unit, result.answer, result.state, result.reads.reverse ++ reads⟩) := by
  dsimp only
  have split : fuel = ((QueryState.run sample program world).reads.length + 1) +
      (fuel - ((QueryState.run sample program world).reads.length + 1)) := by omega
  conv_lhs => rw [split]
  rw [show Sampled.advance sample price
      (((QueryState.run sample program world).reads.length + 1) +
        (fuel - ((QueryState.run sample program world).reads.length + 1))) program world reads =
      Sampled.resume sample price (fuel - ((QueryState.run sample program world).reads.length + 1))
        (Sampled.advance sample price ((QueryState.run sample program world).reads.length + 1)
          program world reads) from Cursor.advance_add ..]
  rw [completed_run]
  rfl

end Mettapedia.Machines.Cursor.StatefulQueryRun
