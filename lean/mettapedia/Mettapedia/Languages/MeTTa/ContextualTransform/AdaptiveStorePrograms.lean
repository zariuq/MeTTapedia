import Mettapedia.Languages.MeTTa.ContextualTransform.StoreOperations
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStoreSelection
import Mettapedia.Machines.OperatorChoice.ObserverContracts

/-!
# Adaptive ordered-store programs realized by transform runs

The source service directly uses the ordered-list contracts. Its target
constructs admitted requests and executes the actual transform step. The
correspondence covers every finite adaptive client and the full ordered reply
history. Every target execution also constructs an Interface.Step.Run.

This service boundary handles completed Boolean selection, ordered readout and
append. Scoped PeTTa preparation is connected separately. It does not identify
Boolean selection with a possibly interrupted unifier, or prove termination of
arbitrary source programs. Fresh allocation is an explicit representation
contract, not an assumed evaluator-equivalence law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.AdaptiveStorePrograms

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Interface
open Mettapedia.Machines
open ReadOnlyQuery (Program)
open OperatorChoice.ObserverContracts (eraseObservation run_erasure_on)
open StoreAndDemand StoreOperations
open PeTTaStoreSelection (atomFrames)

inductive Command where
  | append (values : List Atom)
  | remove (select : Atom → Bool)
  | query (select : Atom → Bool)

inductive Reply where
  | count (amount : Nat)
  | changed (value : Bool)
  | rows (values : List Atom)
  deriving DecidableEq

def source (rows : List Atom) : Command → Reply × List Atom
  | .append values =>
      let routed := StoreEffects.route rows values
      (.count routed.2, routed.1)
  | .remove select =>
      let removed := StoreEffects.removeAll select rows
      (.changed removed.2, removed.1)
  | .query select => (.rows (rows.filter select), rows)

variable {O : Type} [DecidableEq O] (label : O → Atom)

/-- All three fields are allocation obligations, independent of execution. -/
structure Allocation where
  make : List O → List Atom → List O
  values : ∀ rows values, (make rows values).map label = values
  distinct : ∀ rows values, (make rows values).Nodup
  fresh : ∀ rows values, Disjoint (make rows values).toFinset rows.toFinset

abbrev State (O : Type) := { rows : List O // rows.Nodup }

def decode (state : State O) : List Atom := state.val.map label

def lower (allocation : Allocation label) (state : State O) : Command → OrderedStore.Publication Atom O
  | .append values => appendRequest (Tm := fun _ : PUnit.{1} => Atom) (a := PUnit.unit) (allocation.make state.val values)
  | .remove select => removeRequest (Tm := fun _ : PUnit.{1} => Atom) (a := PUnit.unit) label select state.val
  | .query select => readRequest (Tm := fun _ : PUnit.{1} => Atom) (a := PUnit.unit) label select state.val

variable (knowledge : EquationStore Atom) (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge)

include consistent in
theorem admitted (allocation : Allocation label) (state : State O) (command : Command) :
    (OrderedStore.step atomFrames PUnit.unit label).Admits (s := (knowledge, state.val))
      (lower label allocation state command) := by
  cases command with
  | append values =>
      exact (append_admits_exact atomFrames PUnit.unit label knowledge _ _).mpr
        ⟨state.property, allocation.distinct _ _, allocation.fresh _ _, consistent⟩
  | remove select =>
      exact (remove_admits_exact atomFrames PUnit.unit label select knowledge _).mpr
        ⟨state.property, consistent⟩
  | query select =>
      exact (read_admits_exact atomFrames PUnit.unit label select knowledge _).mpr
        ⟨state.property, consistent⟩

def reply (command : Command) (request : OrderedStore.Publication Atom O) : Reply :=
  match command with
  | .append _ => .count request.selection.made.length
  | .remove _ => .changed (!request.selection.taken.isEmpty)
  | .query _ => .rows (request.selection.read.map label)

/-- Publication uses the admitted calculus operation; validity of the next
ordered representation follows from its checked contraction/append theorem. -/
def target (allocation : Allocation label) (state : State O) (command : Command) : Reply × State O :=
  let request := lower label allocation state command
  let permitted := admitted label knowledge consistent allocation state command
  let after := (OrderedStore.step atomFrames PUnit.unit label).result request permitted
  (reply label command request, ⟨after.2, OrderedStore.result_nodup atomFrames PUnit.unit label permitted⟩)

theorem service_square (allocation : Allocation label) (state : State O) (command : Command) :
    source (decode label state) command =
      ((target label knowledge consistent allocation state command).1,
        decode label (target label knowledge consistent allocation state command).2) := by
  cases command with
  | append values =>
      have routed := route_correspondence atomFrames PUnit.unit label knowledge state.val
        (allocation.make state.val values) (admitted label knowledge consistent allocation state (.append values))
      rw [allocation.values] at routed
      have count := congrArg List.length (allocation.values state.val values)
      simp only [List.length_map] at count
      apply Prod.ext
      · change Reply.count values.length = Reply.count (allocation.make state.val values).length
        exact congrArg Reply.count count.symm
      · exact congrArg Prod.fst routed
  | remove select =>
      have removed := remove_all_correspondence atomFrames PUnit.unit label select knowledge state.val
        (admitted label knowledge consistent allocation state (.remove select))
      apply Prod.ext
      · exact congrArg Reply.changed (congrArg Prod.snd removed)
      · exact congrArg Prod.fst removed
  | query select =>
      apply Prod.ext
      · exact congrArg Reply.rows (read_answers_exact (Tm := fun _ : PUnit.{1} => Atom) PUnit.unit label select state.val).symm
      · change state.val.map label =
          (((OrderedStore.step atomFrames PUnit.unit label).result
            (readRequest (Tm := fun _ : PUnit.{1} => Atom) (a := PUnit.unit) label select state.val)
            (admitted label knowledge consistent allocation state (.query select))).2.map label)
        exact congrArg (fun st => st.2.map label) (read_store_unchanged atomFrames PUnit.unit label select knowledge state.val (admitted label knowledge consistent allocation state (.query select))).symm

/-- Both answers and complete reply histories commute with decoding, for
arbitrary finite programs whose later commands depend on earlier replies. -/
theorem adaptive_exact (allocation : Allocation label) {Answer : Type}
    (program : Program Command Reply Answer) (state : State O) :
    QueryState.run source program (decode label state) =
      eraseObservation (decode label) (QueryState.run (target label knowledge consistent allocation) program state) :=
  run_erasure_on (target label knowledge consistent allocation) source (decode label)
    (fun current => current.val.Nodup)
    (fun current _ command => (target label knowledge consistent allocation current command).2.property)
    (fun current _ command => service_square label knowledge consistent allocation current command)
    program state state.property

/-- Every target interaction is an actual admitted run, without replacing
the calculus's run relation by the source interpreter. -/
def realization (allocation : Allocation label) {Answer : Type} :
    (program : Program Command Reply Answer) → (state : State O) →
      (OrderedStore.step atomFrames PUnit.unit label).Run (knowledge, state.val)
  | .pure _, _state => .nil _
  | .read command next, state =>
      .cons (lower label allocation state command)
        (admitted label knowledge consistent allocation state command)
        (realization allocation
          (next (target label knowledge consistent allocation state command).1)
          (target label knowledge consistent allocation state command).2)

theorem realization_last (allocation : Allocation label) {Answer : Type}
    (program : Program Command Reply Answer) (state : State O) :
    (realization label knowledge consistent allocation program state).last =
      (knowledge, (QueryState.run (target label knowledge consistent allocation) program state).state.val) := by
  induction program generalizing state with
  | pure => rfl
  | read command next ih =>
      simpa [realization, Step.Run.last, QueryState.run, target, lower,
        OrderedStore.step, OrderedStore.effect, Step.result] using
        ih (target label knowledge consistent allocation state command).1
          (target label knowledge consistent allocation state command).2

theorem realization_length (allocation : Allocation label) {Answer : Type}
    (program : Program Command Reply Answer) (state : State O) :
    (realization label knowledge consistent allocation program state).word.length =
      (QueryState.run (target label knowledge consistent allocation) program state).reads.length := by
  induction program generalizing state with
  | pure => rfl
  | read command next ih =>
      simpa [realization, Step.Run.word, QueryState.run, target, lower,
        OrderedStore.step, OrderedStore.effect, Step.result] using
        ih (target label knowledge consistent allocation state command).1
          (target label knowledge consistent allocation state command).2

/-- The independently run source's final store is the decoded end of the
actual target run. No reordering or answer-bag quotient is used. -/
theorem source_ends_at_realization (allocation : Allocation label) {Answer : Type}
    (program : Program Command Reply Answer) (state : State O) :
    (QueryState.run source program (decode label state)).state =
      ((realization label knowledge consistent allocation program state).last.2.map label) := by
  rw [realization_last, adaptive_exact]
  rfl

end Mettapedia.Languages.MeTTa.ContextualTransform.AdaptiveStorePrograms
