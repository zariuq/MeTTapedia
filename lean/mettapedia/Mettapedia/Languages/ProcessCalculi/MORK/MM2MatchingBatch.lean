import Mettapedia.Languages.ProcessCalculi.MORK.MM2MatchingCursor
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveExecution
import Mettapedia.Languages.ProcessCalculi.MORK.MM2ResumableExecution

/-!
# Resumable matching and atomic MM2 batch publication

Selection consumes the live exec and captures a read snapshot containing that
exec. The structural cursor client collects matching rows privately. A paused
activation publishes no sink batch. A completed activation invokes the
existing reflective sink implementation exactly once, agreeing with the
independently defined finite-support firing on its admitted fragment.

This is suspension within matching, not interleaving mutations of the captured
workspace. Sink finalization remains a finite whole-batch operation here.
Foreign source/sink effects and output-local binder extensions are separate
contracts. No equality with an arbitrary Rust or C execution is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2MatchingBatch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.Cursor
open Mettapedia.GSLT.LanguageDef
open HostCalls (collect)
open MM2MatchingCursor
open ReflectiveComputable WQComputable

def live (space : List Atom) (directive : SourceExecFact) : List Atom :=
  space.erase directive.atom

def snapshot (space : List Atom) (directive : SourceExecFact) : List Atom :=
  directive.atom :: live space directive

def initial (space : List Atom) (directive : SourceExecFact) : MM2MatchingCursor.StructuralQuanta.State :=
  StructuralQuanta.start (snapshot space directive) directive.rule.input

abbrev packet (space : List Atom) (directive : SourceExecFact) :=
  NativeControlCursor.packet (StructuralQuanta.pull (entries (snapshot space directive)))
    (initial space directive) []

abbrev Result (space : List Atom) (directive : SourceExecFact) :=
  Outcome (StructuralQuanta.provider (entries (snapshot space directive))) (NativeControlCursor.client Row) ()

def finalize (space : List Atom) (directive : SourceExecFact) (rows : List Row) : List Atom :=
  cApplyReflectiveTemplate (live space directive) (rows.map Prod.fst) directive.rule.tmpl

def publish (space : List Atom) (directive : SourceExecFact) :
    Result space directive → Option (List Atom) :=
  fun outcome => (NativeControlCursor.published _ outcome).map (finalize space directive)

def run (space : List Atom) (directive : SourceExecFact) (fuel : Nat) :
    Nat × Result space directive :=
  advance (StructuralQuanta.provider (entries (snapshot space directive))) (NativeControlCursor.client Row)
    (fun _ _ => 1) fuel (packet space directive)

@[simp] theorem paused_cannot_commit (space : List Atom) (directive : SourceExecFact)
    (residual : Packet (StructuralQuanta.provider (entries (snapshot space directive)))
      (NativeControlCursor.client Row) ()) :
    publish space directive (.paused residual) = none := rfl

/-- The one extra client inspection publishes a ready result; it is not an
additional committed MM2 firing or a discarded matcher quantum. -/
theorem run_observation (space : List Atom) (directive : SourceExecFact) (fuel : Nat) :
    publish space directive (run space directive (fuel + 1)).2 =
      (collect (StructuralQuanta.pull (entries (snapshot space directive))) fuel
        (initial space directive)).map (finalize space directive) := by
  unfold publish run packet
  rw [NativeControlCursor.advance_collect]
  simp

/-- A first grant cannot publish an unfinished input match or its sink batch. -/
theorem first_grant_cannot_commit (space : List Atom) (directive : SourceExecFact) :
    publish space directive (run space directive 1).2 = none := by
  rw [show 1 = 0 + 1 from rfl, run_observation]
  rfl

theorem finalize_reference (space : List Atom) (directive : SourceExecFact) :
    finalize space directive
      (StructuralQuanta.residualRows (entries (snapshot space directive)) (initial space directive)) =
        cFireReflectiveSourceExecFact space directive := by
  have erased := StructuralQuanta.start_rows_erase (snapshot space directive) directive.rule.input []
  have substitutions := congrArg (List.map Prod.fst) erased
  simp only [List.map_map, eraseRow, Function.comp_def] at substitutions
  unfold finalize initial
  rw [substitutions]
  rfl

/-- Every actual completed cursor run reflects to the independently coded
whole firing; no premise asserts the desired run correspondence. -/
theorem commit_sound (space : List Atom) (directive : SourceExecFact)
    (fuel : Nat) (target : List Atom)
    (committed : publish space directive (run space directive fuel).2 = some target) :
    target = cFireReflectiveSourceExecFact space directive := by
  cases fuel with
  | zero => simp [run, advance, publish, NativeControlCursor.published] at committed
  | succ fuel =>
      rw [run_observation] at committed
      cases collected : collect (StructuralQuanta.pull (entries (snapshot space directive))) fuel
          (initial space directive) with
      | none => simp [collected] at committed
      | some rows =>
          simp only [collected, Option.map_some, Option.some.injEq] at committed
          rw [← committed, StructuralQuanta.collect_sound _ _ _ _ collected]
          exact finalize_reference _ _

noncomputable def allowance (space : List Atom) (directive : SourceExecFact) : Nat :=
  StructuralQuanta.remainingCost (entries (snapshot space directive)) (initial space directive) + 2

theorem commit_complete (space : List Atom) (directive : SourceExecFact) :
    publish space directive (run space directive (allowance space directive)).2 =
      some (cFireReflectiveSourceExecFact space directive) := by
  unfold allowance
  rw [show StructuralQuanta.remainingCost (entries (snapshot space directive)) (initial space directive) + 2 =
      (StructuralQuanta.remainingCost (entries (snapshot space directive)) (initial space directive) + 1) + 1
      from rfl, run_observation]
  rw [StructuralQuanta.collect_complete _ _ _ (Nat.lt_succ_self _)]
  simp only [Option.map_some, finalize_reference]

theorem commit_exists_iff (space : List Atom) (directive : SourceExecFact)
    (target : List Atom) :
    (∃ fuel, publish space directive (run space directive fuel).2 = some target) ↔
      target = cFireReflectiveSourceExecFact space directive := by
  constructor
  · rintro ⟨fuel, committed⟩
    exact commit_sound _ _ _ _ committed
  · rintro rfl
    exact ⟨allowance space directive, commit_complete _ _⟩

/-- Add/remove batching is independent of list enumeration order after the
actual finite input matcher has closed. -/
theorem commit_support (space : List Atom) (directive : SourceExecFact)
    (nodup : space.Nodup) (supported : ReflectiveSupportSetTemplate directive.rule.tmpl)
    (fuel : Nat) (target : List Atom)
    (committed : publish space directive (run space directive fuel).2 = some target) :
    target.toFinset = fireReflectiveSourceExecFact space.toFinset directive := by
  rw [commit_sound _ _ _ _ committed]
  exact reflectiveSourceFiringAgreement_of_supportAlignment space directive nodup supported
    (reflectiveSourceRowSupportAlignment_of_nodup space directive nodup)

def SelectedFor (policy : UnsupportedExecPolicy) (space : List Atom)
    (directive : SourceExecFact) : Prop :=
  match policy with
  | .leaveInert => selectNextScheduled (cSupportedSourceExecFacts space) = some directive
  | .consume => ∃ raw, selectNextScheduled (cRawExecFacts space) = some raw ∧
      decodeSupportedSourceExec raw = some directive

def UnsupportedSelected (policy : UnsupportedExecPolicy) (space target : List Atom) : Prop :=
  match policy with
  | .leaveInert => False
  | .consume => ∃ raw, selectNextScheduled (cRawExecFacts space) = some raw ∧
      decodeSupportedSourceExec raw = none ∧ target = space.erase raw.atom

/-- A source step is either the declared raw-shell refusal or a selected
directive whose retained matcher and sink batch have actually completed. -/
def CompletedStep (policy : UnsupportedExecPolicy) (space target : List Atom) : Prop :=
  UnsupportedSelected policy space target ∨
    ∃ directive, SelectedFor policy space directive ∧
      ∃ fuel, publish space directive (run space directive fuel).2 = some target

theorem completed_step_iff (policy : UnsupportedExecPolicy) (space target : List Atom) :
    CompletedStep policy space target ↔
      cReflectiveSourceWorkQueueStep policy space = some target := by
  unfold CompletedStep
  simp only [commit_exists_iff]
  cases policy with
  | leaveInert =>
      unfold UnsupportedSelected SelectedFor cReflectiveSourceWorkQueueStep
      cases selected : selectNextScheduled (cSupportedSourceExecFacts space) <;>
        simp [eq_comm]
  | consume =>
      unfold UnsupportedSelected SelectedFor cReflectiveSourceWorkQueueStep
      cases selected : selectNextScheduled (cRawExecFacts space) with
      | none => simp
      | some raw =>
          cases decoded : decodeSupportedSourceExec raw <;> simp [decoded, eq_comm]

/-- Forward and backward correspondence to the independent support transition,
under the existing physical representation invariant. -/
theorem completed_support_step_iff (policy : UnsupportedExecPolicy) (space : List Atom)
    (target : Space) (invariant : ReflectiveWorkQueueInvariant space) :
    reflectiveSourceWorkQueueStep policy space.toFinset = some target ↔
      ∃ concrete, CompletedStep policy space concrete ∧ concrete.toFinset = target := by
  have agreement := cReflectiveSourceWorkQueueStep_toFinset policy space invariant.nodup
    invariant.supportedKeyInj invariant.rawKeyInj invariant.supportedAgreement invariant.rawAgreement
  rw [← agreement]
  simp only [Option.map_eq_some_iff, completed_step_iff]

theorem read_snapshot_contains_selected (space : List Atom) (directive : SourceExecFact) :
    directive.atom ∈ snapshot space directive := by simp [snapshot]

namespace Controls

def symbol (name : String) : Atom := .symbol name
def term (name : String) (args : List Atom) : Atom := .expression (symbol name :: args)
def exec (key : String) (patterns outputs : List Atom) : Atom :=
  term "exec" [symbol key, term "," patterns, term "," outputs]

def second : Atom := exec "b" [term "seed" [symbol "a"]] [term "done" [symbol "a"]]
def first : Atom := exec "a" [term "seed" [symbol "a"]] [second]
def initialSpace : List Atom := [first, term "seed" [symbol "a"]]

theorem created_exec_is_next_eligible_work :
    cReflectiveSourceWorkQueueRunN .leaveInert 2 initialSpace =
      ([term "seed" [symbol "a"], term "done" [symbol "a"]], 2) := by decide

def selfReader : Atom := exec "a"
  [term "exec" [symbol "a", .var "input", .var "output"]] [term "read-self" []]

theorem selected_exec_can_read_itself :
    cReflectiveSourceWorkQueueRunN .leaveInert 1 [selfReader] =
      ([term "read-self" []], 1) := by decide

def destructive : Atom := term "exec" [symbol "a", term "," [term "fact" []],
  term "O" [term "-" [term "fact" []], term "+" [term "gone" []]]]
def laterReader : Atom := exec "b" [term "fact" []] [term "late" []]

theorem destructive_updates_change_future_matches :
    cReflectiveSourceWorkQueueRunN .leaveInert 2
      [destructive, laterReader, term "fact" []] = ([term "gone" []], 2) := by decide

end Controls

#print axioms commit_sound
#print axioms commit_complete
#print axioms commit_support
#print axioms completed_support_step_iff

end Mettapedia.Languages.ProcessCalculi.MORK.MM2MatchingBatch
