import Mettapedia.Languages.MeTTa.SpaceTheory.HEReturnEntry

/-!
# Binding snapshots in a live HE space

A snapshot is of the activation's bindings, not a former program world.
Capture may extend the world with a handle. Restore reads a handle in
the reached world and merges with the current activation. A rejected
merge consumes that alternative without replacing the world.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HESnapshotEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
  (Frame Policy Result WorldEnvironment WorldServices)
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation (LogicalMergeRel)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Continuation Task)
open HEFocused (Focus Leaf Parent)

def isInstruction : Entry.Value → Bool
  | .expression _ [.symbol "collapse-bind", _] => true
  | .expression _ [.symbol "superpose-bind", .expression _ _] => true
  | _ => false

theorem instruction_embedded (value : Entry.Value) (known : isInstruction value = true) :
    Minimal.embeddedInstruction value.erase = true := by
  unfold isInstruction at known
  split at known <;> simp_all [Minimal.embeddedInstruction, Entry.Value.erase]

def covered : Task → Bool
  | .minimal _ _ _ value _ => isInstruction value
  | .capture .. | .restore .. => true
  | _ => false

variable {Context World : Type}

inductive Plan (services : WorldServices Context World) (p : Policy)
    (world : World) (active : Context) : Task → World → Leaf → List Continuation → Prop where
  | openCollapse {live scope caller status operand activation snapshots} :
      services.snapshots = some snapshots →
      Plan services p world active
        (.minimal live scope caller (.expression status [.symbol "collapse-bind", operand]) activation)
        world (.work (.minimal live scope caller operand activation)) [.collect activation]
  | packed {saved activation snapshots} :
      services.snapshots = some snapshots →
      Plan services p world active (.capture [] saved activation)
        world (.returning [(.expression .active saved.reverse, activation)]) []
  | skipEmpty {first rest saved activation snapshots} :
      services.snapshots = some snapshots → first.1.erase = Atom.empty →
      Plan services p world active (.capture (first :: rest) saved activation)
        world (.work (.capture rest saved activation)) []
  | capture {first rest saved activation snapshots payload next} :
      services.snapshots = some snapshots → first.1.erase ≠ Atom.empty →
      snapshots.capture active world first.2 payload next →
      Plan services p world active (.capture (first :: rest) saved activation)
        next (.work (.capture rest (.expression .active [first.1, .grounded payload] :: saved) activation)) []
  | openSuperpose {live scope caller status tupleStatus pairs activation snapshots} :
      services.snapshots = some snapshots →
      Plan services p world active (.minimal live scope caller
        (.expression status [.symbol "superpose-bind", .expression tupleStatus pairs]) activation)
        world (.work (.restore pairs [] activation)) []
  | exhausted {saved activation snapshots} :
      services.snapshots = some snapshots →
      Plan services p world active (.restore [] saved activation) world (.returning saved.reverse) []
  | restore {status value payload captured output rest saved activation snapshots} :
      services.snapshots = some snapshots → snapshots.restore active world payload captured →
      Frame.SnapshotMergeRel p captured activation output →
      Plan services p world active (.restore (.expression status [value, .grounded payload] :: rest) saved activation)
        world (.work (.restore rest ((value, output) :: saved) activation)) []
  | reject {status value payload captured rest saved activation snapshots} :
      services.snapshots = some snapshots → snapshots.restore active world payload captured →
      (¬ ∃ output, LogicalMergeRel captured.bindings activation.bindings output) →
      Plan services p world active (.restore (.expression status [value, .grounded payload] :: rest) saved activation)
        world (.work (.restore rest saved activation)) []

theorem Plan.covered {services : WorldServices Context World} {p w active task next body frames}
    (plan : Plan services p w active task next body frames) : covered task = true := by
  cases plan <;> rfl

theorem Plan.frames_bound {services : WorldServices Context World} {p w active task next body frames}
    (plan : Plan services p w active task next body frames) : frames.length ≤ 1 := by
  cases plan <;> simp

/-- No case uses the current space to reconstruct the captured activation.
Only capture itself may install a world supplied by the snapshot service. -/
theorem step_iff (env : WorldEnvironment Context World) (p : Policy)
    (task : Task) (supported : covered task = true) (world : World) (active : Context)
    (stack : List Continuation) (parents : List (Parent Context)) (seen : List Result)
    (target : Focus Context World) :
    HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup p
        ⟨world, active, .work task, stack, parents, seen⟩ target ↔
      ∃ next body frames, Plan env.services p world active task next body frames ∧
        target = ⟨next, active, body, frames ++ stack, parents, seen⟩ := by
  constructor
  · intro moved
    cases task <;> simp only [covered, Bool.false_eq_true] at supported
    all_goals
      cases moved with
      | perform edge =>
        cases edge
        case core incoming _ stepped outgoing =>
          cases incoming
          cases stepped <;> cases outgoing
          all_goals first
            | cases supported
            | rename_i bare
              exact False.elim ((Bool.false_ne_true) (bare.symm.trans (instruction_embedded _ supported)))
        all_goals first
          | exact ⟨_, _, _, .openCollapse (by assumption), rfl⟩
          | exact ⟨_, _, _, .packed (by assumption), rfl⟩
          | exact ⟨_, _, _, .skipEmpty (by assumption) (by assumption), rfl⟩
          | exact ⟨_, _, _, .capture (by assumption) (by assumption) (by assumption), rfl⟩
          | exact ⟨_, _, _, .openSuperpose (by assumption), rfl⟩
          | exact ⟨_, _, _, .exhausted (by assumption), rfl⟩
          | exact ⟨_, _, _, .restore (by assumption) (by assumption) (by assumption), rfl⟩
          | exact ⟨_, _, _, .reject (by assumption) (by assumption) (by assumption), rfl⟩
          | cases supported
  · rintro ⟨next, body, frames, planned, rfl⟩
    let before : Focus Context World := ⟨world, active, .work task, stack, parents, seen⟩
    cases planned with
    | openCollapse enabled => exact .perform (before := before) (.collapseEnter enabled)
    | packed enabled => exact .perform (before := before) (.captureNil enabled)
    | skipEmpty enabled empty => exact .perform (before := before) (.captureEmpty enabled empty)
    | capture enabled nonempty saved => exact .perform (before := before) (.captureOne enabled nonempty saved)
    | openSuperpose enabled => exact .perform (before := before) (.superposeEnter enabled)
    | exhausted enabled => exact .perform (before := before) (.restoreNil enabled)
    | restore enabled bound merged => exact .perform (before := before) (.restoreOne enabled bound merged)
    | reject enabled bound failed => exact .perform (before := before) (.restoreRejected enabled bound failed)

/-- Collection consumes exactly its own continuation. It cannot capture
any frame before the child has returned its entire batch. -/
theorem collect_iff (env : WorldEnvironment Context World) (p : Policy)
    (activation : Frame) (answers : List Result) (world : World) (active : Context)
    (stack : List Continuation) (parents : List (Parent Context)) (seen : List Result)
    (target : Focus Context World) :
    HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup p
        ⟨world, active, .returning answers, .collect activation :: stack, parents, seen⟩ target ↔
      (∃ snapshots, env.services.snapshots = some snapshots) ∧
        target = ⟨world, active, .work (.capture answers [] activation), stack, parents, seen⟩ := by
  constructor
  · intro stepped
    cases stepped with
    | perform step =>
      cases step with
      | core input _ stepped output =>
        cases input
        cases stepped
      | collectEnter available => exact ⟨⟨_, available⟩, rfl⟩
  · rintro ⟨⟨snapshots, enabled⟩, rfl⟩
    exact .perform (before := ⟨world, active, .returning answers, .collect activation :: stack, parents, seen⟩)
      (.collectEnter (snapshots := snapshots) enabled)

/-- The answer phase has one local return law. Ordinary frames consume a
batch independently of snapshot services; collection additionally requires
the snapshot operation to be provided. Neither case changes the world. -/
inductive ReturnPlan (services : WorldServices Context World) (p : Policy) :
    Continuation → List Result → Leaf → List Continuation → Prop where
  | ordinary {frame answers body front} : HEReturnEntry.Plan p frame answers body front →
      ReturnPlan services p frame answers body front
  | collect {activation answers} : (∃ snapshots, services.snapshots = some snapshots) →
      ReturnPlan services p (.collect activation) answers (.work (.capture answers [] activation)) []

theorem ReturnPlan.frames_bound {services : WorldServices Context World} {p frame answers body front}
    (planned : ReturnPlan services p frame answers body front) : front.length ≤ 1 := by
  cases planned with
  | ordinary local' => exact local'.frames_bound
  | collect _ => simp

theorem return_iff (env : WorldEnvironment Context World) (p : Policy) (frame : Continuation)
    (answers : List Result) (world : World) (active : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (seen : List Result) (target : Focus Context World) :
    HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup p
        ⟨world, active, .returning answers, frame :: stack, parents, seen⟩ target ↔
      ∃ body front, ReturnPlan env.services p frame answers body front ∧
        target = ⟨world, active, body, front ++ stack, parents, seen⟩ := by
  by_cases ordinary : HEReturnEntry.covered frame = true
  · rw [HEReturnEntry.step_iff env p frame ordinary answers world active stack parents seen]
    constructor
    · rintro ⟨body, front, plan, result⟩
      exact ⟨body, front, .ordinary plan, result⟩
    · rintro ⟨body, front, plan, result⟩
      cases plan with
      | ordinary plan => exact ⟨_, _, plan, result⟩
      | collect _ => cases ordinary
  · have collection : ∃ activation, frame = .collect activation := by
      cases frame <;> simp_all [HEReturnEntry.covered]
    obtain ⟨activation, rfl⟩ := collection
    rw [collect_iff]
    constructor
    · rintro ⟨available, result⟩
      exact ⟨_, [], .collect available, result⟩
    · rintro ⟨body, front, plan, result⟩
      cases plan with
      | ordinary impossible => cases impossible
      | collect available => exact ⟨available, result⟩

end Mettapedia.Languages.MeTTa.SpaceTheory.HESnapshotEntry
