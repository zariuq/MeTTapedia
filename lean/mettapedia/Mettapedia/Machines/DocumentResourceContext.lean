import Std

/-!
# Lexical document resources over a borrowed import-directory stack

The reference carries only an immutable work base and its own local imports.
The implementation uses the session array and the depth captured at activation.
Entries at or below that marker belong to an ambient caller and cannot change
the work's base. A nested activation hides its caller's prefix in the same way.

This models directory selection, not filename resolution, canonical paths,
ancestor-import suppression, module lookup or evaluation. Module inventory,
relative policy and runner working directory remain live session state. Native
array/pointer lifetime, immutable snapshot ownership and synchronization remain
separate obligations. Import pushes/pops are synchronous, balanced extents;
there is no claim of asynchronously suspending a loader with a live suffix.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.DocumentResourceContext

variable {Directory Inventory : Type}

structure Snapshot (Directory : Type) where
  directory : Directory
  entryDirectory : Option Directory
  deriving DecidableEq, Repr

inductive Policy where
  | lexical
  | workingDirectoryOnly
  deriving DecidableEq, Repr

namespace Reference

structure Frame (Directory : Type) where
  resource : Snapshot Directory
  imports : List Directory
  deriving DecidableEq, Repr

def currentDirectory (frame : Frame Directory) : Directory :=
  frame.imports.head?.getD frame.resource.directory

def select (policy : Policy) (working : Option Directory) (frame : Frame Directory) : Directory :=
  match policy with
  | .lexical => currentDirectory frame
  | .workingDirectoryOnly =>
      (frame.resource.entryDirectory.or working).getD (currentDirectory frame)

end Reference

namespace Native

structure Frame (Directory : Type) where
  resource : Snapshot Directory
  marker : Nat
  deriving DecidableEq, Repr

/-- The size marker and array access correspond to stored native metadata.
No physical complexity theorem about the backing array is asserted here. -/
def currentDirectory (stack : Array Directory) (frame : Frame Directory) : Directory :=
  if frame.marker < stack.size then stack.back?.getD frame.resource.directory
  else frame.resource.directory

def select (policy : Policy) (working : Option Directory)
    (stack : Array Directory) (frame : Frame Directory) : Directory :=
  match policy with
  | .workingDirectoryOnly =>
      match frame.resource.entryDirectory with
      | some directory => directory
      | none => match working with
          | some directory => directory
          | none => currentDirectory stack frame
  | .lexical => currentDirectory stack frame

end Native

theorem local_directory_refines (resource : Snapshot Directory) (imports ambient : List Directory)
    (stack : Array Directory) (represented : stack.toList = ambient ++ imports.reverse) :
    Reference.currentDirectory ⟨resource, imports⟩ =
      Native.currentDirectory stack ⟨resource, ambient.length⟩ := by
  have sameArray : stack = (ambient ++ imports.reverse).toArray := by
    rw [← represented]
  cases imports with
  | nil => simp [Reference.currentDirectory, Native.currentDirectory, sameArray]
  | cons first rest =>
      have above : ambient.length < stack.size := by
        rw [sameArray]
        simp only [List.size_toArray, List.length_append, List.length_reverse, List.length_cons]
        omega
      rw [Native.currentDirectory, if_pos above]
      simp [Reference.currentDirectory, sameArray, List.reverse_cons]

theorem directory_selection_refines (policy : Policy) (working : Option Directory)
    (resource : Snapshot Directory) (imports ambient : List Directory)
    (stack : Array Directory) (represented : stack.toList = ambient ++ imports.reverse) :
    Reference.select policy working ⟨resource, imports⟩ =
      Native.select policy working stack ⟨resource, ambient.length⟩ := by
  have selected := local_directory_refines resource imports ambient stack represented
  cases policy with
  | lexical => exact selected
  | workingDirectoryOnly =>
      cases entry : resource.entryDirectory <;> cases working <;>
        simp [Reference.select, Native.select, entry, selected]

/-- Every nested frame describes a suffix above the prefix borrowed from
its caller. The reference never stores that ambient prefix. -/
inductive Frames : List (Reference.Frame Directory) → List (Native.Frame Directory) → Array Directory → Prop where
  | outside (ambient : Array Directory) : Frames [] [] ambient
  | active {source : List (Reference.Frame Directory)} {target : List (Native.Frame Directory)}
      {ambient : Array Directory} (resource : Snapshot Directory) (imports : List Directory)
      (parent : Frames source target ambient) :
      Frames (⟨resource, imports⟩ :: source) (⟨resource, ambient.size⟩ :: target)
        (ambient ++ imports.reverse.toArray)

theorem activate_frame (source : List (Reference.Frame Directory)) (target : List (Native.Frame Directory))
    (stack : Array Directory) (represented : Frames source target stack)
    (resource : Snapshot Directory) :
    Frames (⟨resource, []⟩ :: source) (⟨resource, stack.size⟩ :: target) stack := by
  simpa using Frames.active resource [] represented

theorem push_local_frame {source : List (Reference.Frame Directory)} {target : List (Native.Frame Directory)}
    {ambient : Array Directory} (resource : Snapshot Directory) (imports : List Directory)
    (parent : Frames source target ambient) (directory : Directory) :
    Frames (⟨resource, directory :: imports⟩ :: source) (⟨resource, ambient.size⟩ :: target)
      ((ambient ++ imports.reverse.toArray).push directory) := by
  simpa [List.reverse_cons, List.append_toArray] using Frames.active resource (directory :: imports) parent

theorem pop_stack (ambient : Array Directory) (imports : List Directory) (directory : Directory) :
    (ambient ++ (directory :: imports).reverse.toArray).pop = ambient ++ imports.reverse.toArray := by
  apply Array.toList_inj.mp
  simp [List.reverse_cons]

theorem active_selection_refines (policy : Policy) (working : Option Directory)
    (resource : Snapshot Directory) (imports : List Directory) (ambient : Array Directory) :
    Reference.select policy working ⟨resource, imports⟩ =
      Native.select policy working (ambient ++ imports.reverse.toArray) ⟨resource, ambient.size⟩ := by
  simpa only [Array.length_toList] using directory_selection_refines policy working resource imports
    ambient.toList (ambient ++ imports.reverse.toArray) (by simp)

inductive Action (Directory Inventory : Type) where
  | activate (owned : Snapshot Directory)
  | leave
  | push (directory : Directory)
  | pop
  | ambientStack (stack : Array Directory)
  | callerEntry (directory : Option Directory)
  | workingDirectory (directory : Option Directory)
  | policy (policy : Policy)
  | inventory (inventory : Inventory)
  | selectDirectory
  | inspectEntry
  | inspectInventory

inductive Event (Directory Inventory : Type) where
  | activated (owned : Snapshot Directory)
  | left
  | pushed (directory : Directory)
  | popped
  | ambientChanged
  | callerChanged
  | workingChanged
  | policyChanged
  | inventoryChanged
  | selected (directory : Directory)
  | entry (directory : Option Directory)
  | modules (inventory : Inventory)
  | protocolFault
  deriving DecidableEq, Repr

structure Transition (State Directory Inventory : Type) where
  next : State
  events : List (Event Directory Inventory)

namespace Reference

structure State (Directory Inventory : Type) where
  frames : List (Frame Directory)
  working : Option Directory
  policy : Policy
  inventory : Inventory

/-- Scoped import operations may pop only their own entries. An activation
leaves only after its synchronous local import suffix has been balanced. -/
def Permitted (state : State Directory Inventory) : Action Directory Inventory → Prop
  | .leave => match state.frames with | frame :: _ => frame.imports = [] | [] => False
  | .push _ | .selectDirectory | .inspectEntry => state.frames ≠ []
  | .pop => match state.frames with | frame :: _ => frame.imports ≠ [] | [] => False
  | .ambientStack _ => state.frames = []
  | _ => True

def step (state : State Directory Inventory) : Action Directory Inventory → Transition (State Directory Inventory) Directory Inventory
  | .activate owned => ⟨{state with frames := ⟨owned, []⟩ :: state.frames}, [.activated owned]⟩
  | .leave => match state.frames with
      | ⟨_, []⟩ :: rest => ⟨{state with frames := rest}, [.left]⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .push directory => match state.frames with
      | frame :: rest =>
          ⟨{state with frames := {frame with imports := directory :: frame.imports} :: rest}, [.pushed directory]⟩
      | [] => ⟨state, [.protocolFault]⟩
  | .pop => match state.frames with
      | ⟨resource, _ :: imports⟩ :: rest =>
          ⟨{state with frames := ⟨resource, imports⟩ :: rest}, [.popped]⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .ambientStack _ => match state.frames with
      | [] => ⟨state, [.ambientChanged]⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .callerEntry _ => ⟨state, [.callerChanged]⟩
  | .workingDirectory directory => ⟨{state with working := directory}, [.workingChanged]⟩
  | .policy policy => ⟨{state with policy := policy}, [.policyChanged]⟩
  | .inventory inventory => ⟨{state with inventory := inventory}, [.inventoryChanged]⟩
  | .selectDirectory => match state.frames with
      | frame :: _ => ⟨state, [.selected (select state.policy state.working frame)]⟩
      | [] => ⟨state, [.protocolFault]⟩
  | .inspectEntry => match state.frames with
      | frame :: _ => ⟨state, [.entry frame.resource.entryDirectory]⟩
      | [] => ⟨state, [.protocolFault]⟩
  | .inspectInventory => ⟨state, [.modules state.inventory]⟩

def ValidTrace : State Directory Inventory → List (Action Directory Inventory) → Prop
  | _, [] => True
  | state, action :: rest => Permitted state action ∧ ValidTrace (step state action).next rest

end Reference

namespace Native

structure State (Directory Inventory : Type) where
  frames : List (Frame Directory)
  stack : Array Directory
  working : Option Directory
  policy : Policy
  inventory : Inventory
  callerEntry : Option Directory

def step (state : State Directory Inventory) : Action Directory Inventory → Transition (State Directory Inventory) Directory Inventory
  | .activate owned =>
      ⟨{state with frames := ⟨owned, state.stack.size⟩ :: state.frames}, [.activated owned]⟩
  | .leave => match state.frames with
      | _ :: rest => ⟨{state with frames := rest}, [.left]⟩
      | [] => ⟨state, [.protocolFault]⟩
  | .push directory => match state.frames with
      | _ :: _ => ⟨{state with stack := state.stack.push directory}, [.pushed directory]⟩
      | [] => ⟨state, [.protocolFault]⟩
  | .pop => match state.frames with
      | _ :: _ => ⟨{state with stack := state.stack.pop}, [.popped]⟩
      | [] => ⟨state, [.protocolFault]⟩
  | .ambientStack stack => match state.frames with
      | [] => ⟨{state with stack := stack}, [.ambientChanged]⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .callerEntry directory => ⟨{state with callerEntry := directory}, [.callerChanged]⟩
  | .workingDirectory directory => ⟨{state with working := directory}, [.workingChanged]⟩
  | .policy policy => ⟨{state with policy := policy}, [.policyChanged]⟩
  | .inventory inventory => ⟨{state with inventory := inventory}, [.inventoryChanged]⟩
  | .selectDirectory => match state.frames with
      | frame :: _ => ⟨state, [.selected (select state.policy state.working state.stack frame)]⟩
      | [] => ⟨state, [.protocolFault]⟩
  | .inspectEntry => match state.frames with
      | frame :: _ => ⟨state, [.entry frame.resource.entryDirectory]⟩
      | [] => ⟨state, [.protocolFault]⟩
  | .inspectInventory => ⟨state, [.modules state.inventory]⟩

end Native

def Represents (reference : Reference.State Directory Inventory) (native : Native.State Directory Inventory) : Prop :=
  Frames reference.frames native.frames native.stack ∧ reference.working = native.working ∧
    reference.policy = native.policy ∧ reference.inventory = native.inventory

theorem step_refines (reference : Reference.State Directory Inventory) (native : Native.State Directory Inventory)
    (represented : Represents reference native) (action : Action Directory Inventory)
    (permitted : Reference.Permitted reference action) :
    Represents (Reference.step reference action).next (Native.step native action).next ∧
      (Reference.step reference action).events = (Native.step native action).events := by
  rcases reference with ⟨source, sourceWorking, sourcePolicy, sourceInventory⟩
  rcases native with ⟨target, stack, working, policy, inventory, caller⟩
  change Frames source target stack ∧ sourceWorking = working ∧ sourcePolicy = policy ∧
    sourceInventory = inventory at represented
  obtain ⟨frames, rfl, rfl, rfl⟩ := represented
  cases action with
  | activate owned => exact ⟨⟨activate_frame _ _ _ frames owned, rfl, rfl, rfl⟩, rfl⟩
  | leave =>
      cases frames with
      | outside ambient => cases permitted
      | active resource imports parent =>
          change imports = [] at permitted
          subst imports
          refine ⟨⟨?_, rfl, rfl, rfl⟩, rfl⟩
          simpa [Reference.step, Native.step] using parent
  | push directory =>
      cases frames with
      | outside ambient => exact False.elim (permitted rfl)
      | active resource imports parent =>
          exact ⟨⟨push_local_frame resource imports parent directory, rfl, rfl, rfl⟩, rfl⟩
  | pop =>
      cases frames with
      | outside ambient => cases permitted
      | active resource imports parent =>
          cases imports with
          | nil => exact False.elim (permitted rfl)
          | cons first rest =>
              refine ⟨⟨?_, rfl, rfl, rfl⟩, rfl⟩
              simpa only [Reference.step, Native.step, pop_stack] using Frames.active resource rest parent
  | ambientStack replacement =>
      cases frames with
      | outside ambient => exact ⟨⟨Frames.outside replacement, rfl, rfl, rfl⟩, rfl⟩
      | active resource imports parent => cases permitted
  | callerEntry directory => exact ⟨⟨frames, rfl, rfl, rfl⟩, rfl⟩
  | workingDirectory directory => exact ⟨⟨frames, rfl, rfl, rfl⟩, rfl⟩
  | policy replacement => exact ⟨⟨frames, rfl, rfl, rfl⟩, rfl⟩
  | inventory replacement => exact ⟨⟨frames, rfl, rfl, rfl⟩, rfl⟩
  | selectDirectory =>
      cases frames with
      | outside ambient => exact False.elim (permitted rfl)
      | active resource imports parent =>
          refine ⟨⟨Frames.active resource imports parent, rfl, rfl, rfl⟩, ?_⟩
          simp only [Reference.step, Native.step, List.cons.injEq, and_true]
          exact congrArg Event.selected (active_selection_refines _ _ _ _ _)
  | inspectEntry =>
      cases frames with
      | outside ambient => exact False.elim (permitted rfl)
      | active resource imports parent => exact ⟨⟨Frames.active resource imports parent, rfl, rfl, rfl⟩, rfl⟩
  | inspectInventory => exact ⟨⟨frames, rfl, rfl, rfl⟩, rfl⟩

def run {State : Type} (step : State → Action Directory Inventory → Transition State Directory Inventory) :
    State → List (Action Directory Inventory) → Transition State Directory Inventory
  | state, [] => ⟨state, []⟩
  | state, action :: rest =>
      let first := step state action
      let later := run step first.next rest
      ⟨later.next, first.events ++ later.events⟩

theorem finite_trace_refines (reference : Reference.State Directory Inventory) (native : Native.State Directory Inventory)
    (represented : Represents reference native) (actions : List (Action Directory Inventory))
    (valid : Reference.ValidTrace reference actions) :
    Represents (run Reference.step reference actions).next (run Native.step native actions).next ∧
      (run Reference.step reference actions).events = (run Native.step native actions).events := by
  induction actions generalizing reference native with
  | nil => exact ⟨represented, rfl⟩
  | cons action rest ih =>
      obtain ⟨allowed, remaining⟩ := valid
      obtain ⟨next, events⟩ := step_refines reference native represented action allowed
      obtain ⟨final, later⟩ := ih _ _ next remaining
      exact ⟨final, by simp only [run, events, later]⟩

/-- The same immutable work base can be reactivated under different callers.
Only entries subsequently pushed by this activation are visible. -/
theorem ambient_prefix_independent (policy : Policy) (working : Option Directory)
    (resource : Snapshot Directory) (imports : List Directory) (first second : Array Directory) :
    Native.select policy working (first ++ imports.reverse.toArray) ⟨resource, first.size⟩ =
      Native.select policy working (second ++ imports.reverse.toArray) ⟨resource, second.size⟩ := by
  exact (active_selection_refines policy working resource imports first).symm.trans
    (active_selection_refines policy working resource imports second)

theorem working_only_entry_priority (resource : Snapshot Directory) (entry : Directory)
    (established : resource.entryDirectory = some entry) (working : Option Directory)
    (stack : Array Directory) (marker : Nat) :
    Native.select .workingDirectoryOnly working stack ⟨resource, marker⟩ = entry := by
  simp [Native.select, established]

theorem working_only_runner_fallback (directory runner : Directory)
    (stack : Array Directory) (marker : Nat) :
    Native.select .workingDirectoryOnly (some runner) stack ⟨⟨directory, none⟩, marker⟩ = runner := by
  rfl

theorem working_only_without_entries_uses_lexical (directory : Directory)
    (stack : Array Directory) (marker : Nat) :
    Native.select .workingDirectoryOnly none stack ⟨⟨directory, none⟩, marker⟩ =
      Native.currentDirectory stack ⟨⟨directory, none⟩, marker⟩ := by
  rfl

theorem entry_observation_is_captured (state : Native.State Directory Inventory)
    (resource : Snapshot Directory) (marker : Nat) (rest : List (Native.Frame Directory))
    (active : state.frames = ⟨resource, marker⟩ :: rest) :
    (Native.step state .inspectEntry).events = [.entry resource.entryDirectory] := by
  simp [Native.step, active]

theorem balanced_nested_restore (state : Native.State Directory Inventory)
    (child : Snapshot Directory) (directory : Directory) :
    (run Native.step state [.activate child, .push directory, .pop, .leave]).next = state := by
  cases state
  simp [run, Native.step]

/-- Returning to the outer resource scope must not restore obsolete session
policy, runner directory or module inventory. -/
theorem live_updates_survive_scope (state : Native.State Directory Inventory)
    (child : Snapshot Directory) (inventory : Inventory) (working : Option Directory) (policy : Policy) :
    (run Native.step state [.activate child, .inventory inventory, .workingDirectory working,
      .policy policy, .leave]).next = {state with inventory := inventory, working := working, policy := policy} := by
  cases state
  rfl

theorem balanced_nested_trace_permitted (state : Reference.State Directory Inventory)
    (child : Snapshot Directory) (directory : Directory) :
    Reference.ValidTrace state [.activate child, .push directory, .pop, .leave] := by
  simp [Reference.ValidTrace, Reference.Permitted, Reference.step]

namespace Controls

def outer : Snapshot Nat := ⟨10, some 11⟩
def inner : Snapshot Nat := ⟨20, some 21⟩
def noEntry : Snapshot Nat := ⟨10, none⟩

def reference : Reference.State Nat (List Nat) := ⟨[], some 70, .lexical, [1]⟩
def native : Native.State Nat (List Nat) := ⟨[], #[90], some 70, .lexical, [1], some 91⟩

def selections (events : List (Event Nat (List Nat))) : List Nat :=
  events.filterMap fun event => match event with | .selected directory => some directory | _ => none

def inventories (events : List (Event Nat (List Nat))) : List (List Nat) :=
  events.filterMap fun event => match event with | .modules inventory => some inventory | _ => none

theorem initial_states_represent : Represents reference native := by
  exact ⟨Frames.outside #[90], rfl, rfl, rfl⟩

/-- Ignoring the captured marker exposes a caller's directory. -/
theorem ignored_marker_is_observable :
    Native.currentDirectory #[90] ⟨outer, 1⟩ = 10 ∧
      Native.currentDirectory #[90] ⟨outer, 0⟩ = 90 := by
  decide

def nested : List (Action Nat (List Nat)) :=
  [.activate outer, .selectDirectory, .push 30, .selectDirectory,
   .activate inner, .selectDirectory, .push 40, .selectDirectory,
   .pop, .selectDirectory, .leave, .selectDirectory, .pop, .selectDirectory, .leave]

theorem nested_trace_permitted : Reference.ValidTrace reference nested := by
  simp [Reference.ValidTrace, Reference.Permitted, Reference.step, nested]

theorem nested_local_selection_and_restoration :
    selections (run Native.step native nested).events = [10, 30, 20, 40, 20, 30, 10] ∧
      (run Native.step native nested).next = native := by
  constructor
  · decide
  · rfl

def resumed : List (Action Nat (List Nat)) :=
  [.activate outer, .selectDirectory, .leave,
   .ambientStack #[80, 81], .callerEntry (some 82),
   .activate outer, .selectDirectory, .inspectEntry, .leave]

theorem resumed_trace_permitted : Reference.ValidTrace reference resumed := by
  simp [Reference.ValidTrace, Reference.Permitted, Reference.step, resumed, reference]

theorem resumed_base_ignores_new_caller :
    selections (run Native.step native resumed).events = [10, 10] ∧
      (run Native.step native resumed).next.callerEntry = some 82 := by
  decide

/-- A live caller-entry mutant disagrees with the work's captured entry. -/
theorem live_caller_entry_is_not_owned_entry :
    Native.select .workingDirectoryOnly (some 70) #[90, 30] ⟨outer, 1⟩ = 11 ∧
      ((run Native.step native resumed).next.callerEntry).getD 70 = 82 := by
  decide

theorem missing_entry_is_not_runner_entry :
    (Native.step {native with frames := [⟨noEntry, 1⟩]} .inspectEntry).events = [.entry none] ∧
      Native.select .workingDirectoryOnly (some 70) #[90] ⟨noEntry, 1⟩ = 70 := by
  decide

theorem missing_runner_uses_owned_lexical_base :
    Native.select .workingDirectoryOnly none #[90] ⟨noEntry, 1⟩ = 10 ∧
      Native.select .workingDirectoryOnly none #[90, 30] ⟨noEntry, 1⟩ = 30 := by
  decide

theorem policy_and_runner_remain_live :
    selections (run Native.step native
      [.activate noEntry, .workingDirectory (some 71), .policy .workingDirectoryOnly,
       .selectDirectory, .push 30, .selectDirectory, .policy .lexical,
       .selectDirectory, .pop, .leave]).events = [71, 71, 30] := by
  decide

theorem module_inventory_remains_live :
    inventories (run Native.step native
      [.activate outer, .inspectInventory, .inventory [2, 3],
       .inspectInventory, .leave, .inspectInventory]).events = [[1], [2, 3], [2, 3]] := by
  decide

theorem unbalanced_import_extents_are_excluded :
    ¬ Reference.Permitted (Reference.step reference (.activate outer)).next .pop ∧
      ¬ Reference.Permitted
        (Reference.step (Reference.step reference (.activate outer)).next (.push 30)).next .leave := by
  simp [Reference.Permitted, Reference.step]

/-- A directory-keyed table witnesses why selecting the right base matters;
this is not a filesystem resolution algorithm. -/
def lookup (directory : Nat) (basename : String) : Option Nat :=
  if basename = "late.metta" then
    if directory = 10 then some 111 else if directory = 90 then some 222 else none
  else none

theorem same_basename_different_directories :
    lookup (Native.currentDirectory #[90] ⟨outer, 1⟩) "late.metta" = some 111 ∧
      lookup (#[90].back?.getD 10) "late.metta" = some 222 := by
  decide

end Controls

end Mettapedia.Machines.DocumentResourceContext
