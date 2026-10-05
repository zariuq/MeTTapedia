import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.Persistent
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ChannelPartition

/-!
# Source halting reaches quiescence in the persistent tape protocol

Dispatch leaves a state/symbol query, both half-tapes, and the unchanged
controller. If no table entry applies, every output channel is separated
from every waiting input channel, including modulo structural congruence.
This proves a genuine target normal form, rather than a bounded timeout.

The result preserves halting. It does not reflect arbitrary target runs or
exclude interference from other programs using the same protocol ports.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.Halting

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.TuringMachine
open Stack TapeActions Persistent

private def OutputChannel (configuration : Configuration) (channel : Pattern) : Prop :=
  StructuralCongruence channel leftPort ∨ StructuralCongruence channel rightPort ∨
    StructuralCongruence channel (LookupKey.key configuration.state configuration.scanned)

private noncomputable def side (configuration : Configuration) (channel : Pattern) : Nat := by
  classical
  exact if OutputChannel configuration channel then 1 else 0

private theorem outputChannel_SC (configuration : Configuration) {first second : Pattern}
    (related : StructuralCongruence first second) :
    OutputChannel configuration first ↔ OutputChannel configuration second := by
  constructor
  · intro matched
    rcases matched with left | right | key
    · exact .inl (.trans _ _ _ (.symm _ _ related) left)
    · exact .inr (.inl (.trans _ _ _ (.symm _ _ related) right))
    · exact .inr (.inr (.trans _ _ _ (.symm _ _ related) key))
  · intro matched
    rcases matched with left | right | key
    · exact .inl (.trans _ _ _ related left)
    · exact .inr (.inl (.trans _ _ _ related right))
    · exact .inr (.inr (.trans _ _ _ related key))

private theorem side_SC (configuration : Configuration) {first second : Pattern}
    (related : StructuralCongruence first second) :
    side configuration first = side configuration second := by
  unfold side
  rw [propext (outputChannel_SC configuration related)]

private theorem side_left (configuration : Configuration) : side configuration leftPort = 1 := by
  exact if_pos (Or.inl (StructuralCongruence.refl _) : OutputChannel configuration leftPort)

private theorem side_right (configuration : Configuration) : side configuration rightPort = 1 := by
  exact if_pos (Or.inr (Or.inl (StructuralCongruence.refl _)) : OutputChannel configuration rightPort)

private theorem side_key (configuration : Configuration) :
    side configuration (LookupKey.key configuration.state configuration.scanned) = 1 := by
  exact if_pos (Or.inr (Or.inr (StructuralCongruence.refl _)) :
    OutputChannel configuration (LookupKey.key configuration.state configuration.scanned))

private theorem side_pulse (configuration : Configuration) : side configuration pulsePort = 0 := by
  unfold side
  apply if_neg
  intro matched
  rcases matched with left | right | key
  · have impossible := (port_sc_iff 12 8).mp left
    omega
  · have impossible := (port_sc_iff 12 10).mp right
    omega
  · exact LookupKey.key_not_port _ _ 12 (.symm _ _ key)

private theorem side_row (configuration : Configuration) (entry : Transition)
    (inapplicable : ¬ entry.Applies configuration) :
    side configuration (LookupKey.key entry.state entry.read) = 0 := by
  unfold side
  apply if_neg
  intro matched
  rcases matched with left | right | key
  · exact LookupKey.key_not_port _ _ 8 left
  · exact LookupKey.key_not_port _ _ 10 right
  · exact inapplicable ((LookupKey.key_sc_iff _ _ _ _).mp key)

private theorem dispatcher_separated (configuration : Configuration) :
    separationBy (side configuration) dispatcher = 0 := by
  simp [dispatcher, GuardedReplication.idle, separationBy, separationHead, side_pulse]

private theorem rowServer_separated (configuration : Configuration) (index : Nat) (entry : Transition)
    (inapplicable : ¬ entry.Applies configuration) :
    separationBy (side configuration) (rowServer index entry) = 0 := by
  simp [rowServer, GuardedReplication.idle, separationBy, separationHead, side_row _ _ inapplicable]

private theorem servers_separated (configuration : Configuration) (index : Nat) (entries : List Transition)
    (inapplicable : ∀ entry ∈ entries, ¬ entry.Applies configuration) :
    ((serversFrom index entries).map (separationBy (side configuration))).sum = 0 := by
  induction entries generalizing index with
  | nil => rfl
  | cons entry rest ih =>
      have head := inapplicable entry (List.mem_cons_self)
      have tail := ih (index + 1) (fun row member => inapplicable row (List.mem_cons_of_mem _ member))
      simp only [serversFrom, List.map_cons, List.sum_cons,
        rowServer_separated configuration index entry head, tail, Nat.add_zero]

/-- Every source-halted configuration has a genuinely quiescent query state. -/
theorem awaiting_normal {machine : Machine} {configuration : Configuration}
    (halted : Halted machine configuration.term) : NormalForm (awaiting machine configuration) := by
  apply normalForm_of_separationBy_zero (side configuration) (side_SC configuration)
  simp [awaiting, parallel, send, zero, separationBy, separationHead,
    side_left, side_right, side_key, dispatcher_separated,
    servers_separated configuration 0 machine.transitions (halted_term_iff.mp halted)]

/-- An applicable row can receive the query: a successful dispatch cannot
be mistaken for a halting observation. -/
theorem awaiting_not_normal {machine : Machine} {configuration : Configuration}
    {entry : Transition} (member : entry ∈ machine.transitions) (applies : entry.Applies configuration) :
    ¬ NormalForm (awaiting machine configuration) := by
  obtain ⟨before, after, table⟩ := List.mem_iff_append.mp member
  let leading := serversFrom 0 before
  let trailing := serversFrom (before.length + 1) after
  have rows : serversFrom 0 machine.transitions =
      leading ++ rowServer before.length entry :: trailing := by
    simp [table, serversFrom_append, serversFrom, leading, trailing]
  have sameKey : LookupKey.key configuration.state configuration.scanned =
      LookupKey.key entry.state entry.read := by rw [← applies.1, ← applies.2]
  obtain ⟨receive⟩ := row_request before.length entry
  have frame := receive.splice []
    ([send leftPort (encode configuration.left), send rightPort (encode configuration.right), dispatcher] ++
      leading ++ trailing)
  have sourceRelated : StructuralCongruence (awaiting machine configuration)
      (parallel ([send (LookupKey.key entry.state entry.read) zero, rowServer before.length entry] ++
        ([send leftPort (encode configuration.left), send rightPort (encode configuration.right), dispatcher] ++
          leading ++ trailing))) := by
    simp only [awaiting, sameKey, rows]
    apply StructuralCongruence.par_perm
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add, ← Multiset.cons_coe,
      Multiset.coe_nil, ← Multiset.singleton_add]
    ac_rfl
  exact (frame.transport sourceRelated (.refl _)).not_normal

/-- At the completed dispatch boundary, target quiescence is exactly source
halting. This boundary comparison does not classify intermediate runs. -/
theorem awaiting_normal_iff (machine : Machine) (configuration : Configuration) :
    NormalForm (awaiting machine configuration) ↔ Halted machine configuration.term := by
  constructor
  · intro quiet
    apply halted_term_iff.mpr
    intro entry member applies
    exact awaiting_not_normal member applies quiet
  · exact awaiting_normal

/-- The initial packet always has dispatch work, including when its source
configuration is halted. Terminal observations belong to `awaiting`. -/
theorem encoding_not_normal (machine : Machine) (configuration : Configuration) :
    ¬ NormalForm (encoding machine configuration) := by
  obtain ⟨dispatch⟩ := dispatch_reduces machine configuration
  exact dispatch.not_normal

/-- Five real communications finish dispatch and retain both tapes and the
state/symbol key in a normal form. -/
theorem halted_dispatch {machine : Machine} {configuration : Configuration}
    (halted : Halted machine configuration.term) :
    Nonempty (ReducesN 5 (encoding machine configuration) (awaiting machine configuration)) ∧
      NormalForm (awaiting machine configuration) :=
  ⟨dispatch_reduces machine configuration, awaiting_normal halted⟩

/-- An authored halting run reaches the encoded terminal configuration's
quiescent query state, without a fuel bound. -/
theorem haltsFrom_preserved {machine : Machine} {initial : Configuration}
    (halts : HaltsFrom machine initial.term) :
    ∃ final : Configuration, Halted machine final.term ∧
      Nonempty (ReducesStar (encoding machine initial) (awaiting machine final)) ∧
      NormalForm (awaiting machine final) := by
  obtain ⟨target, sourceRun, halted⟩ := halts
  obtain ⟨final, rfl, ⟨run⟩⟩ := reaches_preserved machine sourceRun
  obtain ⟨⟨finish⟩, quiet⟩ := halted_dispatch halted
  exact ⟨final, halted, ⟨run.trans (reducesN_to_star finish)⟩, quiet⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.Halting
