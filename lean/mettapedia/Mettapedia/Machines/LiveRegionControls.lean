import Mettapedia.Machines.LiveRegionRenaming
import Mettapedia.Machines.InterleavedProtocolRegions
import Mettapedia.Machines.RegionDependencyStability

/-!
# Dynamic region entry, exit, re-entry and contextual controls

The finite worked client is an actual reply-dependent free protocol tree.
Its first arithmetic operation requires unbounded naturals. A computed reply
then enables word operations; an overflowing result returns to the reference
and a later subtraction permits re-entry. The mode log is an optimization
receipt, not a source answer. Generic client and interleaving laws are imported,
not inferred from these finite examples.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.LiveWordRegions.Controls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Cursor Cursor.LiveAdmission Cursor.InterleavedRegions

structure TraceState where
  registers : Nat → Nat
  modes : List Bool

def traced : Provider (protocol Nat) where
  State _ _ := TraceState
  step state request :=
    let selected := (worker Nat).attempt state.registers request
    let result := selected.getD ((reference Nat).step state.registers request)
    ⟨result.1, result.2, state.modes ++ [selected.isSome]⟩

def tracedHom : Hom traced (reference Nat) where
  map state := state.registers
  step {base index} state request := by
    cases base
    cases index
    change TraceState at state
    change Request Nat at request
    change (worker Nat).execute (base := ()) (index := ()) state.registers request =
      (reference Nat).step state.registers request
    exact (worker Nat).execute_exact state.registers request

abbrev Answers := fun (_ : Unit) (_ : Unit) => List Nat

def client : Client (P := protocol Nat) (Return := Answers) := CoalgebraicPlans.retainedPlanRealizer

/-- The fourth request is constructed from the third reply. The original
input does not fit the word region and no whole-program gate admits it. -/
def scenario : (protocol Nat).Free Answers () () :=
  Free.node (protocol Nat) (.load 0 (UInt64.size + 7)) fun first =>
  Free.node (protocol Nat) (.load 1 (UInt64.size + 3)) fun second =>
  Free.node (protocol Nat) (.subtract 0 0 1) fun difference =>
  Free.node (protocol Nat) (.load 2 difference) fun copied =>
  Free.node (protocol Nat) (.add 0 0 2) fun doubled =>
  Free.node (protocol Nat) (.load 1 (UInt64.size - 1)) fun boundary =>
  Free.node (protocol Nat) (.add 0 0 1) fun overflowing =>
  Free.node (protocol Nat) (.subtract 0 0 1) fun returned =>
  Free.node (protocol Nat) (.add 0 0 2) fun final =>
  Free.pure (protocol Nat) [first, second, difference, copied, doubled, boundary, overflowing, returned, final]

def startingRegisters : Nat → Nat := fun coordinate => if coordinate = 99 then UInt64.size + 99 else 0

def initialReceipt : Receipt client traced () := (0, .paused ⟨(), scenario, ⟨startingRegisters, []⟩⟩)

def runTraced (allowance : Nat) : Receipt client traced () :=
  resume traced client (operations traced) allowance initialReceipt

def answersOf : Outcome traced client () → Option (List Nat)
  | .paused _ => none
  | .done result => some result.2.1

def modesOf : Outcome traced client () → List Bool
  | .paused packet => packet.2.2.modes
  | .done result => result.2.2.modes

def valueOf (coordinate : Nat) : Outcome traced client () → Nat
  | .paused packet => packet.2.2.registers coordinate
  | .done result => result.2.2.registers coordinate

theorem actual_dynamic_entry_exit_reentry :
    (runTraced 10).1 = 9 ∧
    modesOf (runTraced 10).2 = [false, false, false, true, true, true, false, false, true] ∧
    answersOf (runTraced 10).2 =
      some [UInt64.size + 7, UInt64.size + 3, 4, 4, 8, UInt64.size - 1, UInt64.size + 7, 8, 12] := by decide

theorem suspended_at_newly_admissible_state :
    answersOf (runTraced 3).2 = none ∧ valueOf 0 (runTraced 3).2 = 4 ∧
      modesOf (runTraced 3).2 = [false, false, false] := by decide

theorem resumes_into_fast_region :
    modesOf (resume traced client (operations traced) 1 (runTraced 3)).2 = [false, false, false, true] := by decide

theorem large_unread_register_is_retained : valueOf 99 (runTraced 10).2 = UInt64.size + 99 := by decide

theorem paused_is_not_complete : answersOf (runTraced 0).2 = none := rfl

theorem actual_residual_matches_reference (allowance : Nat) :
    (runTraced allowance).1 =
      (resume (reference Nat) client (operations (reference Nat)) allowance
        (mapReceipt client tracedHom initialReceipt)).1 ∧
    tracedHom.outcome client (runTraced allowance).2 =
      (resume (reference Nat) client (operations (reference Nat)) allowance
        (mapReceipt client tracedHom initialReceipt)).2 := by
  have exactRun := tracedHom.resume_account client (operations traced) (operations (reference Nat))
    (fun _ _ => rfl) allowance initialReceipt
  exact ⟨congrArg Prod.fst exactRun, congrArg Prod.snd exactRun⟩

def changeBoundary (change : (Nat → Nat) → Nat → Nat) : Boundary tracedHom where
  changeActual state := {state with registers := change state.registers}
  changeReference := change
  commutes _ := rfl

def interference : Event tracedHom := .environment (changeBoundary fun state => Function.update state 0 (UInt64.size + 20))

def unrelated : Event tracedHom := .environment (changeBoundary fun state => Function.update state 99 17)

theorem relevant_interference_changes_next_admission :
    let result := actualHistory client [.page 3, interference, .page 2] initialReceipt
    modesOf result.2 = [false, false, false, true, false] ∧
      valueOf 0 result.2 = UInt64.size + 24 := by decide

theorem unrelated_interference_keeps_answers_and_choices :
    let result := actualHistory client [.page 3, unrelated, .page 7] initialReceipt
    answersOf result.2 = answersOf (runTraced 10).2 ∧
      modesOf result.2 = modesOf (runTraced 10).2 ∧ valueOf 99 result.2 = 17 := by decide

theorem interleaved_run_keeps_full_reference (history : List (Event tracedHom)) :
    mapReceipt client tracedHom (actualHistory client history initialReceipt) =
      referenceHistory client history (mapReceipt client tracedHom initialReceipt) :=
  history_exact client tracedHom history initialReceipt

theorem arbitrary_zero_pages_do_not_complete (count : Nat) :
    actualHistory client (List.replicate count (Event.page (decode := tracedHom) 0)) initialReceipt =
      initialReceipt := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa [List.replicate_succ, actualHistory, actualEvent] using ih

def addRequest : Request Nat := .add 2 0 1
def subtractRequest : Request Nat := .subtract 2 0 1
def small : Nat → Nat := fun coordinate => if coordinate = 0 then 3 else if coordinate = 1 then 5 else 0
def changedSmall : Nat → Nat := Function.update small 1 6
def tooLarge : Nat → Nat := Function.update small 1 UInt64.size
def smallTicket : (planner Nat).Ticket (base := ()) (index := ()) addRequest :=
  (planner Nat).prepare small addRequest
def largeTicket : (planner Nat).Ticket (base := ()) (index := ()) addRequest :=
  (planner Nat).prepare tooLarge addRequest

theorem cached_admission_retains_operand_dependencies :
    smallTicket.observed.reads = [(0, 3), (1, 5)] ∧
    ReadOnlyQuery.checkReads changedSmall smallTicket.observed.reads = false := by decide

/-- Both worlds remain eligible; reusing old captured operands would still be wrong. -/
theorem eligibility_alone_does_not_validate_code :
    ((worker Nat).attempt (base := ()) (index := ()) small addRequest).isSome = true ∧
    ((worker Nat).attempt (base := ()) (index := ()) changedSmall addRequest).isSome = true ∧
    (execute changedSmall addRequest (.add 3 5)).1 = 8 ∧
    ((reference Nat).step (base := ()) (index := ()) changedSmall addRequest).1 = 9 := by decide

theorem validated_replanning_updates_code :
    (planner Nat).replay changedSmall addRequest smallTicket = some (.add 3 6) := by decide

theorem relevant_overflow_exits_region :
    (planner Nat).replay tooLarge addRequest smallTicket = none ∧
    ((worker Nat).execute (base := ()) (index := ()) tooLarge addRequest).1 = UInt64.size + 3 := by decide

/-- An earlier refusal is not permanently cached across changed dependencies. -/
theorem stale_negative_does_not_block_entry :
    largeTicket.observed.answer = none ∧
    (planner Nat).replay small addRequest largeTicket = some (.add 3 5) := by decide

theorem unrelated_update_reuses_same_code :
    ReadOnlyQuery.checkReads (Function.update small 99 UInt64.size) smallTicket.observed.reads = true ∧
      (planner Nat).replay (Function.update small 99 UInt64.size) addRequest smallTicket = some (.add 3 5) := by decide

theorem planner_keeps_repeated_reads :
    (ReadOnlyQuery.run small (query (.add 2 0 0))).reads = [(0, 3), (0, 3)] := by decide

theorem discarding_request_identity_changes_result :
    (execute small subtractRequest (.add 3 5)).1 = 8 ∧
      ((reference Nat).step (base := ()) (index := ()) small subtractRequest).1 = 0 := by decide

theorem unchecked_live_word_addition_wraps :
    (UInt64.ofNat 3 + UInt64.ofNat UInt64.size).toNat = 3 ∧ UInt64.size + 3 ≠ 3 := by decide

end Mettapedia.Machines.LiveWordRegions.Controls
