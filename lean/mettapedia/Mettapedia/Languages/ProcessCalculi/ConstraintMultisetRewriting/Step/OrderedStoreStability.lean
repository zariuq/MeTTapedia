import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.OrderedStore
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Exactness
import Mettapedia.Machines.PreparedStoreStability
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PublicationProtocol

/-!
# Dependency-preserving changes in the actual ordered transform step

Occurrence-commit exactness lifts to the ordered step without weakening its
shape or knowledge obligations. Complete predicate regions cover absence,
uniqueness and count dependencies as well as kept occurrences. The theorem
licenses reusing admission in the stated order, not changing source scheduling.
Its predicate-region profile observes exact occurrence sets. It is stronger
than a count-only observer; that distinction is retained in the controls.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.OrderedStoreStability

open MeTTaCalculus.OccurrenceCommits
open Mettapedia.Machines

universe uO uT uH
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) (a : Obj) {O : Type} [DecidableEq O]
  (label : O → Tm a)

theorem admitted_after_iff (state : OrderedStore.State (Tm := Tm) a O)
    (waiting writer : OrderedStore.Publication (Tm a) O)
    (waitingReady : (OrderedStore.step X a label).Admits (s := state) waiting)
    (writerReady : (OrderedStore.step X a label).Admits (s := state) writer) :
    (OrderedStore.step X a label).Admits
        (s := (OrderedStore.step X a label).result writer writerReady) waiting ↔
      ¬ Clash waiting.commit writer.commit ∧ ¬ Spoils label writer.commit waiting.commit := by
  have shaped : OrderedStore.Shapes ((OrderedStore.step X a label).result writer writerReady).2
      waiting.selection := ⟨OrderedStore.result_nodup X a label writerReady, waitingReady.1.2⟩
  rw [OrderedStore.admits_exact]
  have physical : ((OrderedStore.step X a label).result writer writerReady).2.toFinset =
      fire state.2.toFinset writer.commit := by
    rw [OrderedStore.result_rows, OrderedStore.publish_present]
    rfl
  rw [physical, OrderedStore.result_knowledge]
  simpa only [shaped, waitingReady.2.2, true_and, and_true] using
    enabled_fire_iff waitingReady.2.1 writerReady.2.1

variable [DecidableEq (Tm a)]

/-- The primitive profile derives its later tcalc admission from actual
earlier preparation and writer footprints, without assuming later readiness. -/
theorem prepared_after_change (world : PreparedStoreProtocol.World O)
    (waiting writer : PreparedStoreProtocol.Plan O (Tm a))
    (waitingReady : PreparedStoreProtocol.Ready label world waiting)
    (writerReady : PreparedStoreProtocol.Ready label world writer)
    (preserved : PreparedStoreStability.Preserves label waiting writer)
    (knowledge : EquationStore (Tm a)) (consistent : X.Solvable knowledge) :
    (OrderedStore.step X a label).Admits
      (s := (knowledge, (PreparedStoreStability.after label world writer writerReady).rows))
      (PublicationProtocol.request (a := a) waiting) :=
  PublicationProtocol.ready_admitted X a label _ waiting
    (PreparedStoreStability.ready_after label world waiting writer waitingReady writerReady preserved)
    knowledge consistent

namespace Controls

def store : Finset Nat := {0, 1}
def waitingAbsent : Commit Nat Nat := ⟨{0}, ∅, ∅, [⟨(· == 2), ∅⟩]⟩
def makesObserved : Commit Nat Nat := ⟨{1}, ∅, {2}, []⟩
def waitingKeep : Commit Nat Nat := ⟨{0}, {1}, ∅, []⟩

theorem disjoint_takes_can_spoil_absence :
    Enabled id store waitingAbsent ∧ Enabled id store makesObserved ∧
      Disjoint waitingAbsent.taken makesObserved.taken ∧
      ¬ Enabled id (fire store makesObserved) waitingAbsent := by decide

theorem disjoint_takes_can_lose_a_keep :
    Enabled id store waitingKeep ∧ Enabled id store makesObserved ∧
      Disjoint waitingKeep.taken makesObserved.taken ∧
      ¬ Enabled id (fire store makesObserved) waitingKeep := by decide

def capturedRegion : Commit Nat Nat := ⟨{0}, ∅, ∅, [⟨(· != 0), {1}⟩]⟩

theorem unchanged_count_can_change_captured_identity :
    (regionOf id store (· != 0)).card = (regionOf id (fire store makesObserved) (· != 0)).card ∧
      Enabled id store capturedRegion ∧ ¬ Enabled id (fire store makesObserved) capturedRegion := by decide

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.OrderedStoreStability
