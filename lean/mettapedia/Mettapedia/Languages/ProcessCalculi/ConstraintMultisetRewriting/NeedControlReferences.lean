import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedControl

/-!
# Snapshot support of controls and edit continuations

Every stored alternative and result contributes its snapshot name. Cell
indices inside values are relative to that snapshot and are not themselves
snapshot names. Decoding depends only on this finite support. Filling the
new-store marker preserves all old references when its name is fresh.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedControl

open Mettapedia.Machines.BranchLocalNeed
open CallTimeChoice (Store Program Outcome)

variable {A B : Type}

def Goal.names : Goal A → List A
  | .eval name _ _ | .alts name _ | .forceVal name _ => [name]
  | .seqK _ _ results | .commitK _ results | .followK results => results.map Prod.snd

def Frame.names : Frame A → List A
  | .sequence _ _ | .commit _ | .follow => []
  | .later goal => goal.names
  | .append results => results.map Prod.snd
  | .cons result => [result.2]

def Control.names : Control A → List A
  | .task goal stack => goal.names ++ stack.flatMap Frame.names
  | .returned results stack => results.map Prod.snd ++ stack.flatMap Frame.names

@[simp] theorem Goal.names_map (change : A → B) (goal : Goal A) :
    (goal.map change).names = goal.names.map change := by
  cases goal <;> simp [Goal.names,Goal.map,List.map_map,resultMap,Function.comp_def]

@[simp] theorem Frame.names_map (change : A → B) (frame : Frame A) :
    (frame.map change).names = frame.names.map change := by
  cases frame <;> simp [Frame.names,Frame.map,List.map_map,resultMap,Function.comp_def]

@[simp] theorem Frame.names_list_map (change : A → B) (stack : List (Frame A)) :
    (stack.map (Frame.map change)).flatMap Frame.names = (stack.flatMap Frame.names).map change := by
  simp only [List.flatMap_map,Frame.names_map,List.map_flatMap]

@[simp] theorem Control.names_map (change : A → B) (control : Control A) :
    (control.map change).names = control.names.map change := by
  cases control <;> simp [Control.names,Control.map,List.map_map,resultMap,Function.comp_def]

private theorem results_decode_congr (left right : A → Store) (results : List (Result A))
    (agree : ∀ name ∈ results.map Prod.snd, left name = right name) :
    results.map (resultMap left) = results.map (resultMap right) := by
  apply List.map_congr_left
  intro result member
  exact Prod.ext rfl (agree result.2 (List.mem_map.mpr ⟨result,member,rfl⟩))

theorem Goal.decode_congr (left right : A → Store) (goal : Goal A)
    (agree : ∀ name ∈ goal.names, left name = right name) : goal.decode left = goal.decode right := by
  cases goal with
  | eval name env code => exact congrArg (fun store => CallTimeChoice.Goal.eval store env code) (agree name (by simp [Goal.names]))
  | alts name branches => exact congrArg (fun store => CallTimeChoice.Goal.alts store branches) (agree name (by simp [Goal.names]))
  | forceVal name value => exact congrArg (fun store => CallTimeChoice.Goal.forceVal store value) (agree name (by simp [Goal.names]))
  | seqK code env results => exact congrArg (CallTimeChoice.Goal.seqK code env) (results_decode_congr left right results agree)
  | commitK cell results => exact congrArg (CallTimeChoice.Goal.commitK cell) (results_decode_congr left right results agree)
  | followK results => exact congrArg CallTimeChoice.Goal.followK (results_decode_congr left right results agree)

theorem Frame.decode_congr (left right : A → Store) (frame : Frame A)
    (agree : ∀ name ∈ frame.names, left name = right name) : frame.decode left = frame.decode right := by
  cases frame with
  | sequence | commit | follow => rfl
  | later goal => exact congrArg CallTimeChoiceInstructions.Frame.later (goal.decode_congr left right agree)
  | append results => exact congrArg CallTimeChoiceInstructions.Frame.append (results_decode_congr left right results agree)
  | cons result =>
      apply congrArg CallTimeChoiceInstructions.Frame.cons
      exact Prod.ext rfl (agree result.2 (by simp [Frame.names]))

private theorem stack_decode_congr (left right : A → Store) (stack : List (Frame A))
    (agree : ∀ name ∈ stack.flatMap Frame.names, left name = right name) :
    stack.map (Frame.decode left) = stack.map (Frame.decode right) := by
  apply List.map_congr_left
  intro frame member
  apply frame.decode_congr left right
  intro name present
  exact agree name (List.mem_flatMap.mpr ⟨frame,member,present⟩)

/-- Only names actually present in the control need interpretation
agreement; no infinite family of allocated snapshots is assumed. -/
theorem Control.decode_congr (left right : A → Store) (control : Control A)
    (agree : ∀ name ∈ control.names, left name = right name) : control.decode left = control.decode right := by
  cases control with
  | task goal stack =>
      apply congrArg₂ CallTimeChoiceInstructions.Control.task
      · exact goal.decode_congr left right (fun name member => agree name (List.mem_append_left _ member))
      · exact stack_decode_congr left right stack (fun name member => agree name (List.mem_append_right _ member))
  | returned results stack =>
      apply congrArg₂ CallTimeChoiceInstructions.Control.returned
      · exact results_decode_congr left right results (fun name member => agree name (List.mem_append_left _ member))
      · exact stack_decode_congr left right stack (fun name member => agree name (List.mem_append_right _ member))

def Action.oldNames : Action → List Nat
  | .direct control => control.names
  | .edit _ _ resume => resume.names.filterMap id

attribute [local simp] Frame.names.eq_1 Frame.names.eq_2 Frame.names.eq_3
  Frame.names.eq_4 Frame.names.eq_5 Frame.names.eq_6

set_option maxHeartbeats 1000000 in
theorem Intent.old_names_subset {program : Program} (intent : Intent program) :
    ∀ name ∈ intent.plan.action.oldNames, name ∈ intent.plan.input.names := by
  cases intent <;> simp [Intent.plan,Action.oldNames,Control.names,Goal.names,
    List.mem_append,List.map_map,List.filterMap_append,List.filterMap_map,Function.comp_def,resultMap]
  all_goals intro name member; aesop

theorem Intent.edit_source_in {program : Program} (intent : Intent program) (source : Nat)
    (operation : NeedStoreOperations.Operation) (resume : Resume)
    (edit : intent.plan.action = .edit source operation resume) : source ∈ intent.plan.input.names := by
  cases intent <;> simp_all [Intent.plan,Control.names,Goal.names]

/-- Updating the fresh snapshot interpretation leaves every saved old
store unchanged. No literal equality of private allocation histories is
required; the continuation's finite support determines the comparison. -/
theorem resumeAt_decode_update (stores : Nat → Store) (fresh : Nat) (nextStore : Store) (resume : Resume)
    (apart : ∀ old, some old ∈ resume.names → old ≠ fresh) :
    (resumeAt fresh resume).decode (Function.update stores fresh nextStore) =
      resume.decode (fun name => match name with | none => nextStore | some old => stores old) := by
  rw [resumeAt,Control.decode_map]
  apply Control.decode_congr
  intro name member
  cases name with
  | none => simp
  | some old => simp [Function.update_of_ne (apart old member)]

theorem Intent.resume_below {program : Program} (intent : Intent program) (fresh source : Nat)
    (operation : NeedStoreOperations.Operation) (resume : Resume)
    (edit : intent.plan.action = .edit source operation resume)
    (bounded : ∀ old ∈ intent.plan.input.names, old < fresh) :
    source < fresh ∧ ∀ old, some old ∈ resume.names → old < fresh := by
  refine ⟨bounded source (intent.edit_source_in source operation resume edit),?_⟩
  intro old member
  apply bounded old
  apply intent.old_names_subset old
  rw [edit]
  exact List.mem_filterMap.mpr ⟨some old,member,rfl⟩

theorem Intent.resume_interpretation {program : Program} (intent : Intent program) (stores : Nat → Store)
    (fresh source : Nat) (operation : NeedStoreOperations.Operation) (resume : Resume)
    (edit : intent.plan.action = .edit source operation resume)
    (bounded : ∀ old ∈ intent.plan.input.names, old < fresh) :
    (resumeAt fresh resume).decode (Function.update stores fresh (operation.apply (stores source))) =
      intent.plan.action.decode stores := by
  rw [edit]
  exact resumeAt_decode_update stores fresh _ resume
    (fun old member => Nat.ne_of_lt ((intent.resume_below fresh source operation resume edit bounded).2 old member))

set_option maxHeartbeats 1000000 in
theorem Intent.read_names_subset {program : Program} (intent : Intent program)
    (row : SnapshotCopy.Row CallTimeChoice.Suspension) (read : row ∈ intent.plan.reads)
    (name : Nat) (mentioned : name ∈ row.mentions) : name ∈ intent.plan.input.names := by
  cases intent <;> simp_all [Intent.plan,Control.names,Goal.names]
  all_goals rcases read with rfl | rfl <;> simp_all [SnapshotCopy.Row.mentions]

theorem resumeAt_names_bounded (fresh : Nat) (resume : Resume)
    (bounded : ∀ old, some old ∈ resume.names → old < fresh) :
    ∀ name ∈ (resumeAt fresh resume).names, name < fresh+1 := by
  intro name member
  rw [resumeAt,Control.names_map] at member
  obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
  cases original with
  | none => simp
  | some old => exact Nat.lt_succ_of_lt (bounded old present)

theorem Intent.direct_names_bounded {program : Program} (intent : Intent program)
    (fresh : Nat) (control : Control Nat) (direct : intent.plan.action = .direct control)
    (bounded : ∀ old ∈ intent.plan.input.names, old < fresh) :
    ∀ name ∈ control.names, name < fresh := by
  intro name member
  apply bounded name
  apply intent.old_names_subset name
  simpa only [direct,Action.oldNames] using member

theorem Intent.resumed_names_bounded {program : Program} (intent : Intent program)
    (fresh source : Nat) (operation : NeedStoreOperations.Operation) (resume : Resume)
    (edit : intent.plan.action = .edit source operation resume)
    (bounded : ∀ old ∈ intent.plan.input.names, old < fresh) :
    ∀ name ∈ (resumeAt fresh resume).names, name < fresh+1 :=
  resumeAt_names_bounded fresh resume (intent.resume_below fresh source operation resume edit bounded).2

/-- Reusing a source name gives the intended source continuation when that
name is absent from all retained old references. This is a decoding law;
physical exclusivity and other observers are separate obligations. -/
theorem Intent.reuse_interpretation {program : Program} (intent : Intent program) (stores : Nat → Store)
    (source : Nat) (operation : NeedStoreOperations.Operation) (resume : Resume)
    (edit : intent.plan.action = .edit source operation resume)
    (notRetained : source ∉ intent.plan.action.oldNames) :
    (resumeAt source resume).decode (Function.update stores source (operation.apply (stores source))) =
      intent.plan.action.decode stores := by
  rw [edit]
  apply resumeAt_decode_update
  intro old member same
  apply notRetained
  rw [edit]
  exact List.mem_filterMap.mpr ⟨some old,member,congrArg some same⟩

/-- Two placements agree on the complete decoded continuation if both
avoid its saved references. The physical store maps may still differ. -/
theorem resume_targets_decode_eq (stores : Nat → Store) (nextStore : Store) (resume : Resume)
    (first second : Nat)
    (firstApart : ∀ old, some old ∈ resume.names → old ≠ first)
    (secondApart : ∀ old, some old ∈ resume.names → old ≠ second) :
    (resumeAt first resume).decode (Function.update stores first nextStore) =
      (resumeAt second resume).decode (Function.update stores second nextStore) :=
  (resumeAt_decode_update stores first nextStore resume firstApart).trans
    (resumeAt_decode_update stores second nextStore resume secondApart).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedControl
