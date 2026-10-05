import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.Dispatch
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.RowProgram
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.GuardedReplication
import Mathlib.Data.Multiset.Basic

/-!
# A persistent finite table controller in canonical rho

The fixed controller consists of a guarded dispatcher and one guarded server
per table entry. Each source transition has a fifteen-COMM target execution
that restores the same controller and returns the complete next tape packet.
The controller is independent of the configuration and any execution bound.
Requests, rearming, key construction, and tape manipulation all use the
canonical rho reduction relation.

The theorems here preserve source executions. Reflection of arbitrary target
schedules and their terminal observations requires a further reachable-state
invariant; forward simulation alone does not establish that equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.Persistent

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.TuringMachine
open Stack TapeActions

abbrev pulsePort : Pattern := port 12

def dispatcher : Pattern := GuardedReplication.idle (port 19) pulsePort Dispatch.program

def rowHandler (entry : Transition) : Pattern :=
  parallel [RowProgram.program entry, send pulsePort zero]

def rowServer (index : Nat) (entry : Transition) : Pattern :=
  GuardedReplication.idle (port (20 + index)) (LookupKey.key entry.state entry.read) (rowHandler entry)

def serversFrom : Nat → List Transition → List Pattern
  | _, [] => []
  | index, entry :: rest => rowServer index entry :: serversFrom (index + 1) rest

def packet (configuration : Configuration) : List Pattern :=
  [send statePort (symbolCode configuration.state), send leftPort (encode configuration.left),
    send scannedPort (symbolCode configuration.scanned), send rightPort (encode configuration.right)]

/-- One controller, encoded once from the finite table, beside changing data. -/
def encoding (machine : Machine) (configuration : Configuration) : Pattern :=
  parallel ([send pulsePort zero, dispatcher] ++ packet configuration ++ serversFrom 0 machine.transitions)

/-- The table has received its state/symbol query; both half-tapes and the
idle controller remain available. -/
def awaiting (machine : Machine) (configuration : Configuration) : Pattern :=
  parallel ([send (LookupKey.key configuration.state configuration.scanned) zero,
    send leftPort (encode configuration.left), send rightPort (encode configuration.right), dispatcher] ++
      serversFrom 0 machine.transitions)

theorem serversFrom_append (index : Nat) (before after : List Transition) :
    serversFrom index (before ++ after) =
      serversFrom index before ++ serversFrom (index + before.length) after := by
  induction before generalizing index with
  | nil => simp [serversFrom]
  | cons entry rest ih =>
      simp only [List.cons_append, serversFrom, ih, List.length_cons]
      have addition : index + 1 + rest.length = index + (rest.length + 1) := by omega
      rw [addition]

theorem normalize_rowHandler (entry : Transition) :
    semanticNormalizeProc (rowHandler entry) = rowHandler entry := by
  simp [rowHandler, parallel, send, zero, semanticNormalizeProc, semanticNormalizeProcList,
    RowProgram.normalize_program]

theorem subst_rowHandler (entry : Transition) (k : Nat) (replacement : Pattern) :
    semanticSubstProc k replacement (rowHandler entry) = rowHandler entry := by
  simp [rowHandler, parallel, send, zero, semanticSubstProc, semanticSubstProcList,
    semanticSubstName, RowProgram.subst_program]

theorem dispatcher_request :
    Nonempty (ReducesN 2 (parallel [send pulsePort zero, dispatcher])
      (parallel [dispatcher, Dispatch.program])) :=
  GuardedReplication.request_reduces (normalize_port 19) (normalize_port 12)
    Dispatch.normalize_program (fun k replacement => subst_port 19 k replacement)
    (fun k replacement => subst_port 12 k replacement) Dispatch.subst_program zero

theorem row_request (index : Nat) (entry : Transition) :
    Nonempty (ReducesN 2
      (parallel [send (LookupKey.key entry.state entry.read) zero, rowServer index entry])
      (parallel [rowServer index entry, rowHandler entry])) :=
  GuardedReplication.request_reduces (normalize_port (20 + index))
    (LookupKey.normalize_key entry.state entry.read) (normalize_rowHandler entry)
    (fun k replacement => subst_port (20 + index) k replacement)
    (LookupKey.subst_key entry.state entry.read) (subst_rowHandler entry) zero

theorem dispatcher_coreShape : rhoProcCoreShape dispatcher = true :=
  GuardedReplication.idle_coreShape _ _ _ (port_coreShape 19) (port_coreShape 12)
    Dispatch.program_coreShape

theorem rowServer_coreShape (index : Nat) (entry : Transition) :
    rhoProcCoreShape (rowServer index entry) = true := by
  apply GuardedReplication.idle_coreShape _ _ _ (port_coreShape (20 + index))
    (LookupKey.key_coreShape entry.state entry.read)
  simp [rowHandler, parallel, send, zero, rhoProcCoreShape, rhoProcCoreShapeList,
    RowProgram.program_coreShape]

theorem serversFrom_coreShape (index : Nat) (entries : List Transition) :
    rhoProcCoreShapeList (serversFrom index entries) = true := by
  induction entries generalizing index with
  | nil => rfl
  | cons entry rest ih => simp [serversFrom, rhoProcCoreShapeList, rowServer_coreShape, ih]

theorem encoding_coreShape (machine : Machine) (configuration : Configuration) :
    rhoProcCoreShape (encoding machine configuration) = true := by
  simp [encoding, packet, parallel, send, zero, rhoProcCoreShape, rhoProcCoreShapeList,
    symbolCode_coreShape, encode_coreShape, dispatcher_coreShape, serversFrom_coreShape]

theorem dispatcher_binderSafe (depth : Nat) :
    Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt "NQuote" depth dispatcher = true :=
  GuardedReplication.idle_binderSafe _ _ _ depth (port_binderSafe 19) (port_binderSafe 12)
    Dispatch.program_binderSafe

theorem rowServer_binderSafe (index : Nat) (entry : Transition) (depth : Nat) :
    Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt "NQuote" depth
      (rowServer index entry) = true := by
  apply GuardedReplication.idle_binderSafe _ _ _ depth (port_binderSafe (20 + index))
    (LookupKey.key_binderSafe entry.state entry.read)
  intro d
  simp [rowHandler, parallel, send, zero, Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt,
    Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeListAt, RowProgram.program_binderSafe]

theorem serversFrom_binderSafe (index : Nat) (entries : List Transition) (depth : Nat) :
    binderSafeListAt "NQuote" depth (serversFrom index entries) = true := by
  induction entries generalizing index with
  | nil => rfl
  | cons entry rest ih => simp [serversFrom, binderSafeListAt, rowServer_binderSafe, ih]

theorem encoding_binderSafe (machine : Machine) (configuration : Configuration) :
    binderSafeAt "NQuote" 0 (encoding machine configuration) = true := by
  simp [encoding, packet, parallel, send, zero, binderSafeAt, binderSafeListAt,
    symbolCode_binderSafe, encode_binderSafe, dispatcher_binderSafe, serversFrom_binderSafe]

theorem awaiting_coreShape (machine : Machine) (configuration : Configuration) :
    rhoProcCoreShape (awaiting machine configuration) = true := by
  simp [awaiting, parallel, send, zero, rhoProcCoreShape, rhoProcCoreShapeList,
    LookupKey.key_coreShape, encode_coreShape, dispatcher_coreShape, serversFrom_coreShape]

theorem awaiting_binderSafe (machine : Machine) (configuration : Configuration) :
    binderSafeAt "NQuote" 0 (awaiting machine configuration) = true := by
  simp [awaiting, parallel, send, zero, binderSafeAt, binderSafeListAt,
    LookupKey.key_binderSafe, encode_binderSafe, dispatcher_binderSafe, serversFrom_binderSafe]

/-- Dispatch consumes the pulse, state, and scanned-symbol packet and
constructs a reflective query in five communications. -/
theorem dispatch_reduces (machine : Machine) (configuration : Configuration) :
    Nonempty (ReducesN 5 (encoding machine configuration) (awaiting machine configuration)) := by
  obtain ⟨wake⟩ := dispatcher_request
  have first : ReducesN 2 (encoding machine configuration)
      (parallel ([dispatcher, Dispatch.program] ++ packet configuration ++ serversFrom 0 machine.transitions)) := by
    simpa only [encoding, List.nil_append, List.append_assoc] using
      wake.splice [] (packet configuration ++ serversFrom 0 machine.transitions)
  obtain ⟨dispatch⟩ := Dispatch.invocation_reduces configuration.state configuration.scanned
  have dispatchFrame := dispatch.par_head
    (rest := [send leftPort (encode configuration.left), send rightPort (encode configuration.right),
      dispatcher] ++ serversFrom 0 machine.transitions)
  have second : ReducesN 3
      (parallel ([dispatcher, Dispatch.program] ++ packet configuration ++ serversFrom 0 machine.transitions))
      (awaiting machine configuration) := dispatchFrame.transport
    (.trans _ _ _ (by
      apply StructuralCongruence.par_perm
      apply Multiset.coe_eq_coe.mp
      simp only [packet, ← Multiset.coe_add, ← Multiset.cons_coe,
        Multiset.coe_nil, ← Multiset.singleton_add]
      ac_rfl) (.symm _ _ (Context.par_flatten_head _ _))) (.refl _)
  exact ⟨reducesN_concat first second⟩

/-- An applicable authored transition is fifteen actual communications, with
the same finite controller retained at the next configuration. -/
theorem transition_preserved (machine : Machine) (configuration : Configuration)
    (entry : Transition) (member : entry ∈ machine.transitions) (applies : entry.Applies configuration) :
    Nonempty (ReducesN 15 (encoding machine configuration)
      (encoding machine (configuration.after entry))) := by
  obtain ⟨before, after, table⟩ := List.mem_iff_append.mp member
  let leading := serversFrom 0 before
  let trailing := serversFrom (before.length + 1) after
  have rows : serversFrom 0 machine.transitions =
      leading ++ rowServer before.length entry :: trailing := by
    simp [table, serversFrom_append, serversFrom, leading, trailing]
  obtain ⟨dispatch⟩ := dispatch_reduces machine configuration
  obtain ⟨states, symbols⟩ := applies
  have keyEqual : LookupKey.key configuration.state configuration.scanned =
      LookupKey.key entry.state entry.read := by rw [states, symbols]
  simp only [awaiting, keyEqual, rows] at dispatch
  obtain ⟨serve⟩ := row_request before.length entry
  have rowFrame := serve.splice []
    ([send leftPort (encode configuration.left), send rightPort (encode configuration.right), dispatcher] ++
      leading ++ trailing)
  have third : ReducesN 2
      (parallel ([send (LookupKey.key entry.state entry.read) zero,
        send leftPort (encode configuration.left), send rightPort (encode configuration.right), dispatcher] ++
          (leading ++ rowServer before.length entry :: trailing)))
      (parallel ([rowServer before.length entry, rowHandler entry] ++
        ([send leftPort (encode configuration.left), send rightPort (encode configuration.right), dispatcher] ++
          leading ++ trailing))) := rowFrame.transport (by
    apply StructuralCongruence.par_perm
    apply Multiset.coe_eq_coe.mp
    simp only [List.nil_append, ← Multiset.coe_add, ← Multiset.cons_coe,
      Multiset.coe_nil, ← Multiset.singleton_add]
    ac_rfl) (.refl _)
  obtain ⟨execute⟩ := RowProgram.invocation_reduces entry configuration
  have executeFrame := execute.par_head
    (rest := [send pulsePort zero, dispatcher, rowServer before.length entry] ++ leading ++ trailing)
  have fourth : ReducesN 8
      (parallel ([rowServer before.length entry, rowHandler entry] ++
        ([send leftPort (encode configuration.left), send rightPort (encode configuration.right), dispatcher] ++
          leading ++ trailing)))
      (encoding machine (configuration.after entry)) := executeFrame.transport
    (.trans _ _ _ (StructuralCongruence.flatten_at [rowServer before.length entry]
      [RowProgram.program entry, send pulsePort zero]
      ([send leftPort (encode configuration.left), send rightPort (encode configuration.right), dispatcher] ++
        leading ++ trailing))
      (.trans _ _ _ (by
        apply StructuralCongruence.par_perm
        apply Multiset.coe_eq_coe.mp
        simp only [← Multiset.coe_add, ← Multiset.cons_coe,
          Multiset.coe_nil, ← Multiset.singleton_add]
        ac_rfl) (.symm _ _ (Context.par_flatten_head _ _))))
    (.trans _ _ _ (Context.par_flatten_head _ _) (by
      apply StructuralCongruence.par_perm
      apply Multiset.coe_eq_coe.mp
      simp only [packet, rows,
        ← Multiset.coe_add, ← Multiset.cons_coe, Multiset.coe_nil, ← Multiset.singleton_add]
      ac_rfl))
  exact ⟨reducesN_concat dispatch (reducesN_concat third fourth)⟩

/-- Every finite authored run is preserved without an execution fuel bound. -/
theorem reaches_preserved (machine : Machine) {initial : Configuration} {target : Pattern}
    (path : Reaches machine initial.term target) :
    ∃ final : Configuration, target = final.term ∧
      Nonempty (ReducesStar (encoding machine initial) (encoding machine final)) := by
  induction path with
  | refl => exact ⟨initial, rfl, ⟨.refl _⟩⟩
  | tail _ step ih =>
      obtain ⟨current, rfl, ⟨reached⟩⟩ := ih
      obtain ⟨entry, member, applies, rfl⟩ := step_term_iff.mp step
      obtain ⟨advanced⟩ := transition_preserved machine current entry member applies
      exact ⟨current.after entry, rfl, ⟨reached.trans (reducesN_to_star advanced)⟩⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.Persistent
