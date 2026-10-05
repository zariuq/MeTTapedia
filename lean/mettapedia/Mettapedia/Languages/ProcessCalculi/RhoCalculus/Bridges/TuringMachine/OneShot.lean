import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.Dispatch
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.RowProgram

/-!
# One table lookup and tape transition in canonical rho

The controller contains one finite input prefix per authored table entry.
Configuration data supplies the two tapes and the state-symbol request.
The dispatcher constructs the request's quoted key through communication.
Exactly twelve COMM steps select an applicable entry and return the entire
updated configuration. Unselected listeners remain in the resulting process;
they are not discarded or silently treated as zero.

This is a one-shot controller, not a repeated machine encoding. Persistent
control and reflection of every reachable target execution are separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.OneShot

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.TuringMachine
open Stack TapeActions

def listener (entry : Transition) : Pattern :=
  receive (LookupKey.key entry.state entry.read) (RowProgram.program entry)

def listeners (entries : List Transition) : List Pattern := entries.map listener

def invocation (machine : Machine) (configuration : Configuration) : Pattern :=
  parallel ([send statePort (symbolCode configuration.state), Dispatch.program,
    send scannedPort (symbolCode configuration.scanned), send leftPort (encode configuration.left),
    send rightPort (encode configuration.right)] ++ listeners machine.transitions)

def result (configuration : Configuration) (remaining : List Transition) : Pattern :=
  parallel (configurationReply configuration :: listeners remaining)

/-- Key matching tests precisely the authored state-symbol condition. -/
theorem key_matches_iff (entry : Transition) (configuration : Configuration) :
    StructuralCongruence (LookupKey.key configuration.state configuration.scanned)
      (LookupKey.key entry.state entry.read) ↔ entry.Applies configuration := by
  rw [LookupKey.key_sc_iff]
  simp only [Transition.Applies, eq_comm]

private theorem dispatched (machine : Machine) (configuration : Configuration) :
    Nonempty (ReducesN 3 (invocation machine configuration)
      (parallel ([send (LookupKey.key configuration.state configuration.scanned) zero,
        send leftPort (encode configuration.left), send rightPort (encode configuration.right)] ++
          listeners machine.transitions))) := by
  obtain ⟨path⟩ := Dispatch.invocation_reduces configuration.state configuration.scanned
  have framed := path.par_head
    (rest := [send leftPort (encode configuration.left), send rightPort (encode configuration.right)] ++
      listeners machine.transitions)
  exact ⟨framed.transport
    (.symm _ _ (Context.par_flatten_head _ _)) (.refl _)⟩

/-- Selection is implemented by the finite target controller. The witness
identifies which enabled source transition its execution realizes. -/
theorem invocation_reduces (machine : Machine) (configuration : Configuration)
    (entry : Transition) (member : entry ∈ machine.transitions) (applies : entry.Applies configuration) :
    ∃ before after : List Transition, machine.transitions = before ++ entry :: after ∧
      Nonempty (ReducesN 12 (invocation machine configuration)
        (result (configuration.after entry) (before ++ after))) := by
  obtain ⟨before, after, table⟩ := List.mem_iff_append.mp member
  refine ⟨before, after, table, ?_⟩
  obtain ⟨first⟩ := dispatched machine configuration
  obtain ⟨states, symbols⟩ := applies
  have keyEqual : LookupKey.key configuration.state configuration.scanned =
      LookupKey.key entry.state entry.read := by rw [states, symbols]
  rw [keyEqual, table] at first
  have rawLookup := Reduces.comm (n := LookupKey.key entry.state entry.read)
    (q := zero) (p := RowProgram.program entry)
    (rest := [send leftPort (encode configuration.left), send rightPort (encode configuration.right)] ++
      listeners (before ++ after))
  rw [RowProgram.comm_program] at rawLookup
  have lookup : Reduces
      (parallel ([send (LookupKey.key entry.state entry.read) zero,
        send leftPort (encode configuration.left), send rightPort (encode configuration.right)] ++
          listeners (before ++ entry :: after)))
      (parallel ([send leftPort (encode configuration.left), RowProgram.program entry,
        send rightPort (encode configuration.right)] ++ listeners (before ++ after))) := by
    refine .equiv ?_ rawLookup ?_
    · apply StructuralCongruence.par_perm
      simp only [listeners, List.map_append, List.map_cons,
        List.cons_append, List.nil_append, listener]
      apply List.Perm.cons
      exact List.perm_middle
        (l₁ := [send leftPort (encode configuration.left), send rightPort (encode configuration.right)] ++
          before.map listener) (l₂ := after.map listener)
    · exact StructuralCongruence.par_perm _ _ (List.Perm.swap _ _ _)
  obtain ⟨last⟩ := RowProgram.invocation_reduces entry configuration
  have framed := last.par_head (rest := listeners (before ++ after))
  have finish := framed.transport (.symm _ _ (Context.par_flatten_head _ _)) (.refl _)
  exact ⟨reducesN_concat first (.succ lookup finish)⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.OneShot
