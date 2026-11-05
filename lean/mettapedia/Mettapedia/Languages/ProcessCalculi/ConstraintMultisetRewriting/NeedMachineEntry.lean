import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachineInvariant

/-!
# Ordinary program entry for the per-cell machine

The initial world contains the independently specified source store and one
running control. No copy request is preinstalled. Every source derivation
then corresponds to an actual finite path of generated ordinary rules,
including all intermediate states and retained equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachine

open NeedControl
open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice (Store Program Comp Val Result Derives)

def initialData (store : Store) : Finset (SnapshotCopy.Occurrence Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Suspension) :=
  (NeedSnapshots.encode 1 0 store).present.erase (store.cells.length+3,.request 1 0)

def initialWorld (store : Store) (control : Control Nat) : World :=
  ⟨[],insert (store.cells.length+3,.control 1 control) ((initialData store).image embedHeap)⟩

theorem initial_heap (store : Store) (control : Control Nat) :
    (heapWorld (initialWorld store control)).present = initialData store := by
  ext occurrence
  simp only [initialWorld,heapWorld,mem_heapPresent,Finset.mem_insert]
  constructor
  · rintro (same | present)
    · have impossible := congrArg label same
      cases impossible
    · obtain ⟨original,member,same⟩ := Finset.mem_image.mp present
      exact embedHeap_injective same ▸ member
  · intro member
    exact Or.inr (Finset.mem_image.mpr ⟨occurrence,member,rfl⟩)

theorem initial_snapshot (store : Store) (control : Control Nat) :
    SnapshotCopy.Snapshot (heapWorld (initialWorld store control)).present 0 store.cells store.trace := by
  rw [initial_heap]
  apply snapshot_transfer ?_ (NeedSnapshots.encoded_snapshot 1 0 store)
  intro occurrence stored
  change occurrence ∈ (NeedSnapshots.encode 1 0 store).present ↔
    occurrence ∈ (NeedSnapshots.encode 1 0 store).present.erase (store.cells.length+3,.request 1 0)
  have different : occurrence ≠ (store.cells.length+3,.request 1 0) := by
    rintro rfl
    exact stored
  simp [different]

theorem initial_frame (store : Store) (control : Control Nat) :
    NeedHeapFrames.Frame 1 none (heapWorld (initialWorld store control)).present := by
  rw [initial_heap]
  intro occurrence present
  obtain ⟨notRequest,old⟩ := Finset.mem_erase.mp present
  rcases NeedSnapshots.mem_encoded.mp old with rfl | rfl | rfl | rfl | ⟨index,rfl⟩
  · exact Or.inl (Nat.zero_lt_succ 0)
  · exact Or.inl (Nat.zero_lt_succ 0)
  · exact Or.inl (Nat.zero_lt_succ 0)
  · exact False.elim (notRequest rfl)
  · exact Or.inl (Nat.zero_lt_succ 0)

theorem initial_single (store : Store) (control : Control Nat) :
    controllerCount (initialWorld store control) = 1 := by
  have filtered : (initialWorld store control).present.filter (fun occurrence => (label occurrence).isController) =
      {(store.cells.length+3,.control 1 control)} := by
    ext occurrence
    simp only [Finset.mem_filter,initialWorld,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨same | heap,kind⟩
      · exact same
      · obtain ⟨original,_,rfl⟩ := Finset.mem_image.mp heap
        cases kind
    · rintro rfl
      exact ⟨Or.inl rfl,rfl⟩
  change (_ : Finset Occurrence).card = 1
  rw [filtered]
  rfl

theorem initial_running (store : Store) (control : Control Nat)
    (bounded : ∀ name ∈ control.names, name = 0) :
    Running (initialWorld store control) 1 (fun _ => store) control := by
  refine ⟨⟨(),by simp [initialWorld,SubstitutionAction.Models]⟩,initial_single store control,
    ⟨(store.cells.length+3,.control 1 control),Finset.mem_insert_self ..,rfl⟩,?_,?_,initial_frame store control⟩
  · intro name member
    rw [bounded name member]
    decide
  · intro name less
    have same : name = 0 := by omega
    subst name
    exact initial_snapshot store control

def entry (store : Store) (environment : List (Val Nat)) (code : Comp) : World :=
  initialWorld store (.task (.eval 0 environment code) [])

theorem entry_running (store : Store) (environment : List (Val Nat)) (code : Comp) :
    Running (entry store environment code) 1 (fun _ => store) (.task (.eval 0 environment code) []) :=
  initial_running store _ (by simp [Control.names,Goal.names])

/-- The complete existing source derivation judgment agrees with actual
finite ordinary-rule execution from program entry, preserving the ordered
results and their complete stores. -/
theorem source_derivation_iff (program : Program) (store : Store) (environment : List (Val Nat))
    (code : Comp) (results : List Result) :
    Derives program (.eval store environment code) results ↔
      ∃ after next stores control, Path program (entry store environment code) after ∧
        Running after next stores control ∧ control.decode stores =
          Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Control.returned results [] := by
  exact (Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.source_iff_instruction_path
    program (.eval store environment code) results).trans
    ((entry_running store environment code).source_path_iff _)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachine
