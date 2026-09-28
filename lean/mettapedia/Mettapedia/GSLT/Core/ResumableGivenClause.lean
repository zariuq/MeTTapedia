import Mettapedia.GSLT.Core.GivenClauseLoop
import Mettapedia.Machines.Cursor.Fold

/-!
# A given-clause instance of ordinary resumable cursor work

The general executor is `Cursor.advance/resume`; no GCL operation is added to
it. This adapter gives the existing finite given-clause model an incremental
realization: retain the selected occurrence and processed snapshot, consume its
generated occurrences privately, and publish one completed activation.

Lists are the reference denotation of this existing GCL model. A provider hom
admits other implementations, including the independently implemented array
slice provider. A native indexed generator would prove its local step law to
use the same result; it need not materialize the reference list at runtime.

Publication is a boundary of THIS snapshot/batch policy. Other work programs
can fold directly into a sink. Interleaving mutations of the processed context
is not licensed by this adapter, nor does it impose this policy on all PLN,
rewriting, or saturation algorithms. Simplification and deletion are algorithm
operations, not hidden cursor operations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ResumableGivenClause

open Mettapedia.Machines.Cursor
open Mettapedia.TypeTheory
open GivenClauseLoop
open WeightedOccurrenceControl

variable {Node Answer : Type} {count : Nat} [NeZero count] [DecidableEq Node]

/-- Retain the selection justification against the activation's source state. -/
abbrev Selected (snapshot : Snapshot Node Answer count) :=
  {given : Node // snapshot.passive.selected snapshot.cursor = some given}

def collect (generated : List Node) (item : Node) : List Node := generated ++ [item]

omit [DecidableEq Node] in
theorem collect_fold (items initial : List Node) :
    items.foldl collect initial = initial ++ items := by
  induction items generalizing initial with
  | nil => simp
  | cons item rest ih => simp [List.foldl_cons, collect, ih, List.append_assoc]

abbrev Collector := Fold.client (collect (Node := Node))

/-- Opening work captures the current processed context. It does not select
again when a later quantum resumes. -/
def referenceStart (system : System Node Answer)
    (snapshot : Snapshot Node Answer count) (selected : Selected snapshot) :
    Packet (Sequence.tails Node) (Collector (Node := Node)) () :=
  Fold.start _ collect (system.generate selected.val snapshot.processed) []

def publish (system : System Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (snapshot : Snapshot Node Answer count) (selected : Selected snapshot)
    {provider : Provider (Sequence.protocol Node)} :
    Outcome provider (Collector (Node := Node)) () → Option (Snapshot Node Answer count)
  | .paused _ => none
  | .done result => some {
      events := snapshot.events ++
        match system.observe selected.val snapshot.processed with
        | none => []
        | some answer => [⟨selected.val, answer⟩]
      selections := snapshot.selections ++ [selected.val]
      processed := snapshot.processed ++ [selected.val]
      passive := snapshot.passive.advance disciplines selected.val result.2.1
      cursor := nextIndex snapshot.cursor }

/-- Exhausting the quantum is not an empty generation result or saturation. -/
@[simp] theorem paused_cannot_publish (system : System Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (snapshot : Snapshot Node Answer count) (selected : Selected snapshot)
    {provider : Provider (Sequence.protocol Node)}
    (packet : Packet provider (Collector (Node := Node)) ()) :
    publish system disciplines snapshot selected (.paused packet) = none := rfl

/-- The incremental request/reply machine implements the original whole
activation, including observation, selected occurrence, processed context,
duplicate children, and every scheduling view. -/
theorem reference_complete (system : System Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (snapshot : Snapshot Node Answer count) (selected : Selected snapshot) :
    publish system disciplines snapshot selected
      (advance (Sequence.tails Node) Collector (fun _ _ => 1)
        ((system.generate selected.val snapshot.processed).length + 2)
        (referenceStart system snapshot selected)).2 =
      some (Snapshot.tick system disciplines snapshot) := by
  unfold referenceStart Collector
  rw [Fold.complete_exact]
  simp [publish, collect_fold, Snapshot.tick, selected.property]
  cases system.observe selected.val snapshot.processed <;> rfl

theorem reference_resume_complete (system : System Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (snapshot : Snapshot Node Answer count) (selected : Selected snapshot)
    (first rest : Nat)
    (enough : first + rest = (system.generate selected.val snapshot.processed).length + 2) :
    publish system disciplines snapshot selected
      (resume (Sequence.tails Node) Collector (fun _ _ => 1) rest
        (advance (Sequence.tails Node) Collector (fun _ _ => 1) first
          (referenceStart system snapshot selected))).2 =
      some (Snapshot.tick system disciplines snapshot) := by
  rw [← advance_add, enough]
  exact reference_complete system disciplines snapshot selected

/-- Publication observes only the completed generated occurrences; changing
the provider representation cannot change them. -/
theorem publish_hom (system : System Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (snapshot : Snapshot Node Answer count) (selected : Selected snapshot)
    {provider : Provider (Sequence.protocol Node)}
    (realization : Hom provider (Sequence.tails Node))
    (outcome : Outcome provider (Collector (Node := Node)) ()) :
    publish system disciplines snapshot selected outcome =
      publish system disciplines snapshot selected (realization.outcome Collector outcome) := by
  cases outcome <;> rfl

/-- A local reply/state refinement suffices for the complete GCL result.
The implementation charge is independent: this theorem promises no speedup. -/
theorem realization_complete (system : System Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (snapshot : Snapshot Node Answer count) (selected : Selected snapshot)
    {provider : Provider (Sequence.protocol Node)}
    (realization : Hom provider (Sequence.tails Node)) (charge : Charge provider)
    (state : provider.State () ())
    (represents : realization.map state = system.generate selected.val snapshot.processed) :
    publish system disciplines snapshot selected
      (advance provider Collector charge
        ((system.generate selected.val snapshot.processed).length + 2)
        (Fold.start provider collect state [])).2 =
      some (Snapshot.tick system disciplines snapshot) := by
  rw [publish_hom system disciplines snapshot selected realization]
  rw [realization.advance Collector charge (fun _ _ => 1)]
  have packet : realization.packet Collector (Fold.start provider collect state []) =
      referenceStart system snapshot selected := by
    simp [Hom.packet, Fold.start, referenceStart, represents]
  rw [packet]
  exact reference_complete system disciplines snapshot selected

namespace Controls

def system : System Nat Nat where
  observe given processed := if given = 4 then some processed.length else none
  generate given processed := if given = 4 then [processed.length, processed.length] else []

def initial : Snapshot Nat Nat 1 :=
  Snapshot.initial Snapshot.breadthOnly [4, 9] 0

def selected : Selected initial := ⟨4, rfl⟩

theorem one_pull_is_not_completion :
    publish system Snapshot.breadthOnly initial selected
      (advance (Sequence.tails Nat) Collector (fun _ _ => 1) 1
        (referenceStart system initial selected)).2 = none := rfl

theorem completed_keeps_duplicates :
    (Snapshot.tick system Snapshot.breadthOnly initial).passive.live = [9, 0, 0] ∧
    (Snapshot.tick system Snapshot.breadthOnly initial).processed = [4] := by
  constructor <;> rfl

/-- The array provider uses an offset into retained backing storage. -/
theorem array_slice_realizes_same_activation :
    publish system Snapshot.breadthOnly initial selected
      (advance (Sequence.slices Nat) Collector (fun _ _ => 1) 4
        (Fold.start _ collect ⟨#[99, 0, 0, 88], 1, 2⟩ [])).2 =
      some (Snapshot.tick system Snapshot.breadthOnly initial) := by
  exact realization_complete system Snapshot.breadthOnly initial selected
    (Sequence.sliceHom Nat) (fun _ _ => 1) ⟨#[99, 0, 0, 88], 1, 2⟩ rfl

theorem processed_snapshot_matters :
    system.generate 4 [] ≠ system.generate 4 [9] := by decide

end Controls

#print axioms reference_complete
#print axioms reference_resume_complete
#print axioms realization_complete
#print axioms Controls.array_slice_realizes_same_activation

end Mettapedia.GSLT.Core.ResumableGivenClause
