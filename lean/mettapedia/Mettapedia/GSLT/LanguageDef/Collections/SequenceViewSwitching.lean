import Mettapedia.GSLT.LanguageDef.Collections.SequenceViewCosts

/-!
# Changing sequence views while retaining meaning, position and cost

An explicit materialization GSLT reads cells and writes an array. Its selected
path accounts for both classes of work. Semantic conservation comes from the
actual read/push operations. A resumed array view retains the old logical
position instead of restarting the sequence.

The final comparison concerns a declared workload of repeated last-element
reads. Its setup price includes allocation and any work to learn uncached
metadata. It is not an online policy with foreknowledge of future requests.
Transition counts do not establish the cost of a native allocator, array
growth, cache behavior or C dispatch.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.SequenceViewSwitching

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open CArray0SequenceHosting
open CellSequenceHosting
open SequenceViewCosts

variable {α : Type}

inductive CopyState (α : Type) where
  | read (source : Cell α) (output : Array α)
  | write (value : α) (rest : Cell α) (output : Array α)
  | done (output : Array α)

inductive CopyStep : CopyState α → CopyState α → Prop where
  | stop (ending : Layouts.Terminal α Empty) (output : Array α) :
      CopyStep (.read (.stop ending) output) (.done output)
  | read (value : α) (rest : Cell α) (output : Array α) :
      CopyStep (.read (.cell value rest) output) (.write value rest output)
  | write (value : α) (rest : Cell α) (output : Array α) :
      CopyStep (.write value rest output) (.read rest (output.push value))

@[reducible] def copySystem (α : Type) : GSLT where
  Term := CopyState α
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := CopyStep
  rewrites_resp_left := by
    rintro first first' last equal step
    subst first'
    exact ⟨last, step, rfl⟩
  rewrites_resp_right := by
    rintro first last last' step equal
    subst last'
    exact step

def materialize : Cell α → Array α → Array α
  | .stop _, output => output
  | .cell value rest, output => materialize rest (output.push value)

def copyPath (source : Cell α) (output : Array α) :
    ExecutionPath (copySystem α) (.read source output) (.done (materialize source output)) :=
  match source with
  | .stop ending => .cons ⟨.stop ending output⟩ (.refl _)
  | .cell value rest =>
      .cons ⟨.read value rest output⟩
        (.cons ⟨.write value rest output⟩ (copyPath rest (output.push value)))

def copyMeaning : CopyState α → List α
  | .read source output => output.toList ++ elements source
  | .write value rest output => output.toList ++ value :: elements rest
  | .done output => output.toList

theorem copy_conserves {first last : CopyState α} (step : CopyStep first last) :
    copyMeaning first = copyMeaning last := by
  cases step <;> simp [copyMeaning, elements, Layouts.Cells.abs, List.append_assoc]

def copyInvariant : SemanticInvariant (copySystem α) (List α) where
  denote := copyMeaning
  equation := fun equal => congrArg copyMeaning equal
  rewrite := copy_conserves

theorem materialize_spec (source : Cell α) (output : Array α) :
    (materialize source output).toList = output.toList ++ elements source :=
  (copyInvariant.executionPath_eq (copyPath source output)).symm

theorem copyPath_length (source : Cell α) (output : Array α) :
    (copyPath source output).length = 2 * (elements source).length + 1 := by
  induction source generalizing output with
  | stop ending => rfl
  | cell value rest ih =>
      change (copyPath rest (output.push value)).length + 1 + 1 =
        2 * ((elements rest).length + 1) + 1
      have tail := ih (output.push value)
      omega

def conversionWork (source : Cell α) : Nat := (copyPath source #[]).length

theorem conversionWork_exact (source : Cell α) :
    conversionWork source = 2 * (elements source).length + 1 := copyPath_length source #[]

def flatView (source : Cell α) : StackSlice α :=
  StackSlice.ofArray (materialize source #[])

theorem flatView_spec (source : Cell α) : (flatView source).toList = elements source := by
  simp [flatView, materialize_spec]

/-- A cursor is a suffix view of retained backing storage. Constructing it
does not extract or copy the suffix. The semantic observer may extract it. -/
def resume (backing : Array α) (position : Nat) : StackSlice α where
  cells := backing
  start := min position backing.size
  count := backing.size - position
  inBounds := by omega

theorem resume_keeps_backing (backing : Array α) (position : Nat) :
    (resume backing position).cells = backing := rfl

theorem resume_toList (backing : Array α) (position : Nat) :
    (resume backing position).toList = backing.toList.drop position := by
  have stop : min position backing.size + (backing.size - position) = backing.size := by omega
  simp only [resume, StackSlice.toList, StackSlice.toArray, stop, Array.toList_extract]
  by_cases within : position ≤ backing.size
  · rw [Nat.min_eq_left within, List.extract_eq_take_drop]
    simp
  · have past : backing.size ≤ position := by omega
    rw [Nat.min_eq_right past]
    simp only [List.extract_eq_take_drop, Nat.sub_self, List.take_zero]
    symm
    exact List.drop_eq_nil_of_le (by simpa using past)

theorem materialization_keeps_residual (source : Cell α) (position : Nat) :
    (resume (materialize source #[]) position).toList = (elements source).drop position := by
  rw [resume_toList, materialize_spec]
  simp

/-- Direct execution reads the retained backing array at the transported
position. The reference suffix is used only to specify the answer. -/
theorem resumed_load_agrees (source : Cell α) (position index : Nat) :
    DirectSequenceArray.load (resume (materialize source #[]) position) index =
      ((elements source).drop position)[index]? := by
  rw [DirectSequenceArray.load_eq_reference]
  have same := congrArg (fun values : List α => values[index]?)
    (materialization_keeps_residual source position)
  simpa only [StackSlice.toList, Array.getElem?_toList] using same

/-- Observations of the remaining sequence transport through a view change.
The position is retained even when the new physical cursor uses array offsets. -/
theorem resumed_operation_agrees (source : Cell α) (position : Nat) (operation : SequenceOp) :
    sequenceSem operation (resume (materialize source #[]) position).toList =
      sequenceSem operation ((elements source).drop position) := by
  rw [materialization_keeps_residual]

/-- Old holders keep their cells; the produced flat value and every residual
observer are justified by the conversion, rather than by assuming a new value. -/
theorem conversion_and_holders_agree (source : Cell α) (positions : List Nat) :
    (flatView source).toList = elements source ∧
      positions.map (fun position => (resume (materialize source #[]) position).toList) =
        positions.map (fun position => (elements source).drop position) := by
  constructor
  · exact flatView_spec source
  · apply List.map_congr_left
    intro position _
    exact materialization_keeps_residual source position

def stayWork (length requests : Nat) : Nat := requests * max 1 length

def switchWork (setup length requests : Nat) : Nat := setup + (2 * length + 1) + requests

theorem stayWork_is_last_lookup (values : List α) (nonempty : 0 < values.length) (requests : Nat) :
    stayWork values.length requests =
      requests * cellWork (.at (values.length - 1)) values := by
  unfold stayWork
  rw [Nat.max_eq_right (by omega), valid_lookup_cost _ _ (by omega)]
  congr 1
  omega

theorem switchWork_is_converted_execution (values : List α) (setup requests : Nat) :
    switchWork setup values.length requests = setup + conversionWork (ofList values) +
      requests * arrayWork (.at (values.length - 1)) values := by
  simp [switchWork, conversionWork_exact, arrayWork_eq_one]

theorem one_request_does_not_pay (setup length : Nat) :
    stayWork length 1 < switchWork setup length 1 := by
  simp only [stayWork, switchWork, Nat.one_mul]
  omega

theorem zero_demand_should_not_materialize (setup length : Nat) :
    stayWork length 0 = 0 ∧ 0 < switchWork setup length 0 := by
  simp [stayWork, switchWork]

/-- The break-even condition includes conversion and setup. It applies to
this fixed workload, not to a planner that knows an unknown future horizon. -/
theorem switch_pays_iff (setup length requests : Nat) (positive : 0 < length) :
    switchWork setup length requests ≤ stayWork length requests ↔
      setup + 2 * length + 1 ≤ requests * (length - 1) := by
  have decomposed : requests * length = requests * (length - 1) + requests := by
    calc
      requests * length = requests * ((length - 1) + 1) := by congr 1; omega
      _ = requests * (length - 1) + requests := by rw [Nat.mul_add, Nat.mul_one]
  simp only [switchWork, stayWork]
  rw [Nat.max_eq_right (by omega)]
  rw [decomposed]
  omega

/-- Obtaining an uncached length is itself a complete cell traversal. -/
theorem uncached_metadata_is_paid (values : List α) :
    cellWork .length values + conversionWork (ofList values) = 3 * values.length + 2 := by
  rw [cellWork_length, conversionWork_exact, ofList_elements]
  omega

namespace Controls

example (requests : Nat) : stayWork 0 requests = requests := by simp [stayWork]

example : switchWork 0 4096 4 < stayWork 4096 4 := by decide

example : stayWork 4096 1 < switchWork 0 4096 1 := by decide

/-- Resetting position observes the full sequence again, although its value
was correctly retained by the representation conversion. -/
theorem restart_replays_prefix :
    (resume (materialize (ofList ([1, 2, 3] : List Nat)) #[]) 1).toList = [2, 3] ∧
      (flatView (ofList ([1, 2, 3] : List Nat))).toList = [1, 2, 3] := by
  simp [materialization_keeps_residual, flatView_spec]

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.SequenceViewSwitching
