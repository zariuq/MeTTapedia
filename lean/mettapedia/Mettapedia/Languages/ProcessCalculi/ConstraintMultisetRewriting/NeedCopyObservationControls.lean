import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedCopyObservation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachineProjectionControls

/-!
# Actual copy modalities and the boundary of name reuse

Three selected transform firings witness a native least-fixed-point
reachability formula. The same initial world separates OSLF's past box
from a universal future box. Local continuation decoding admits source-name
reuse, but an additional source-level reader can distinguish that placement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedCopyObservation.Controls

open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice (Store Suspension)
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.BackwardSearch
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary
open NeedControl

def protocol : Protocol := ⟨1,0,NeedMachine.Controls.intent.plan.input,NeedMachine.Controls.intent.plan.reads,
  .memo 0 (.done (.sym 42)),NeedMachine.Controls.resume⟩

def starting : Controlled protocol :=
  ⟨NeedMachine.Controls.started,(show Step NeedMachine.action NeedMachine.label NeedMachine.Controls.beginRule NeedMachine.Controls.initial NeedMachine.Controls.started
    from ⟨NeedMachine.Controls.beginSelection,NeedMachine.Controls.begin_valid,rfl⟩).consistent,
    ⟨(5,.waiting 1 NeedMachine.Controls.intent.plan),by decide +kernel,rfl⟩⟩

def preparation : HeapEdge protocol :=
  ⟨NeedMachine.heapWorld NeedMachine.Controls.started,NeedMachine.heapWorld NeedMachine.Controls.prepared,.begin 1 [3],
    NeedMachine.ProjectionControls.actual_preparation_projects⟩

def copying : HeapEdge protocol :=
  ⟨NeedMachine.heapWorld NeedMachine.Controls.prepared,NeedMachine.heapWorld NeedMachine.Controls.copied,.copy 0 0 NeedMachine.Controls.cached,
    NeedMachine.copy_projects 1 NeedMachine.Controls.intent.plan.input NeedMachine.Controls.intent.plan.reads 0
      (.memo 0 (.done (.sym 42))) NeedMachine.Controls.resume (.copy 0 0 NeedMachine.Controls.cached) ⟨NeedMachine.Controls.copyCellSelection,NeedMachine.Controls.copy_valid,rfl⟩⟩

def completion : HeapEdge protocol :=
  ⟨NeedMachine.heapWorld NeedMachine.Controls.copied,NeedMachine.heapWorld NeedMachine.Controls.finished,.finish 1 [3],
    NeedMachine.copy_projects 1 NeedMachine.Controls.intent.plan.input NeedMachine.Controls.intent.plan.reads 0
      (.memo 0 (.done (.sym 42))) NeedMachine.Controls.resume (.finish 1 [3]) ⟨NeedMachine.Controls.finishSelection,NeedMachine.Controls.finish_valid,rfl⟩⟩

def readyEnvironment : Env (SnapshotCopy.World Suspension) 1 :=
  fun _ => {world | SnapshotCopy.Has world.present (.ready 1)}

theorem actual_heap_reaches_ready :
    Reaches (heapSpan protocol) (fun world => SnapshotCopy.Has world.present (.ready 1))
      (NeedMachine.heapWorld starting.val) := by
  apply Reaches.step (span := heapSpan protocol) preparation
  apply Reaches.step (span := heapSpan protocol) copying
  apply Reaches.step (span := heapSpan protocol) completion
  exact Reaches.goal ⟨(12,.ready 1),by decide +kernel,rfl⟩

/-- A real three-firing execution inhabits the transported least-fixed-point
formula, rather than merely assuming its satisfaction. -/
theorem native_reachability_for_the_controlled_copy :
    satisfies (transitionSystem (controlledSpan protocol))
      (pullEnvironment (projection protocol).states readyEnvironment) reachFormula starting := by
  apply (future_formula_iff protocol reachFormula (by simp [FutureOnly,reachFormula])
    (fixedPointsPositive_of_existential reachFormula reachFormula_existential) readyEnvironment starting).mp
  apply (satisfies_reach_iff (heapSpan protocol) readyEnvironment _).mpr
  exact actual_heap_reaches_ready

theorem starting_is_fresh : SnapshotCopy.Fresh (NeedMachine.heapWorld starting.val).present 1 := by
  change ∀ occurrence ∈ (NeedMachine.heapWorld starting.val).present,
    1 ∉ (SnapshotCopy.label occurrence).mentions
  decide +kernel

theorem no_incoming_copy_at_start (event : HeapEdge protocol) :
    event.after ≠ NeedMachine.heapWorld starting.val := by
  intro ends
  obtain ⟨token,⟨firing⟩⟩ := SnapshotCopy.firing_of_step event.event event.firing
  have produced : ∃ row ∈ (event.event.rule 1 0 1).produce, 1 ∈ row.mentions := by
    cases event.event with
    | begin count trace =>
        exact ⟨.allocated 1,by simp [SnapshotCopy.Event.rule,SnapshotCopy.beginRule],by simp [SnapshotCopy.Row.mentions]⟩
    | copy index remaining value =>
        exact ⟨.cell 1 index value,by simp [SnapshotCopy.Event.rule,SnapshotCopy.copyRule],by simp [SnapshotCopy.Row.mentions]⟩
    | finish count trace =>
        exact ⟨.ready 1,by simp [SnapshotCopy.Event.rule,SnapshotCopy.finishRule],by simp [SnapshotCopy.Row.mentions]⟩
  obtain ⟨row,made,mentions⟩ := produced
  have present := firing.output_rows row made
  rw [ends] at present
  exact starting_is_fresh.not_has row mentions present

/-- On this actual initial copy world, the past box is vacuously true
whereas the future box is false because preparation can really fire. -/
theorem past_and_future_boxes_differ :
    derivedBox (heapSpan protocol) (fun _ => False) (NeedMachine.heapWorld starting.val) ∧
      ¬ derivedForwardBox (heapSpan protocol) (fun _ => False) (NeedMachine.heapWorld starting.val) := by
  refine ⟨?_,?_⟩
  · intro event ends
    exact no_incoming_copy_at_start event ends
  · intro allSuccessors
    exact allSuccessors preparation rfl

def unshared : Intent [] := .commitOk 0 (.sym 42) 0 [] []
def unsharedResume : Resume := .task (.forceVal none (.sym 42)) [.later (.commitK 0 [])]
def stores : Nat → Store := fun _ => NeedMachine.Controls.oldStore
def reused := (resumeAt 0 unsharedResume).decode (Function.update stores 0 NeedMachine.Controls.newStore)
def freshened := (resumeAt 1 unsharedResume).decode (Function.update stores 1 NeedMachine.Controls.newStore)

theorem source_name_is_not_retained : unshared.plan.action.oldNames = [] := by decide +kernel

theorem reuse_has_the_intended_source_meaning : reused = unshared.plan.action.decode stores := by
  exact Intent.reuse_interpretation unshared stores 0 (.memo 0 (.done (.sym 42))) unsharedResume rfl
    (by simp [source_name_is_not_retained])

theorem reused_and_freshened_controls_agree : reused = freshened := by
  apply resume_targets_decode_eq
  all_goals simp [unsharedResume,Control.names,Goal.names,Frame.names]

def externalReader : Control Nat := .task (.forceVal 0 (.need 0)) []

/-- The local resumption footprint does not include another reader.
Its independent source execution distinguishes overwriting from copying. -/
theorem an_external_reader_distinguishes_placement :
    NeedMachine.ProjectionControls.runSource (externalReader.decode (Function.update stores 0 NeedMachine.Controls.newStore)) =
      some [(.ok (.sym 42),[3])] ∧
    NeedMachine.ProjectionControls.runSource (externalReader.decode (Function.update stores 1 NeedMachine.Controls.newStore)) =
      some [(.ok (.sym 7),[3])] := by decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedCopyObservation.Controls
