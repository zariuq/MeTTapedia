import Mettapedia.GSLT.LanguageDef.Collections.Layouts
import Mettapedia.GSLT.LanguageDef.CArray0SequenceHosting
import Mettapedia.GSLT.Core.SemanticInvariant

/-!
# Cell and array interfaces to the same finite sequence

The source is the existing finite-sequence GSLT, already hosted by bounded
array slices. This second realization executes over the existing cons-cell
layout. Indexed access and length walk the cells; first and rest inspect one
cell. Rest returns the retained suffix, not a materialized list.

Both preservation and no-invention are established at the existing source
observation. The semantic observer may read a whole suffix; execution need
not construct that observation. Closedness is an admission condition of this
finite-sequence interface, not a restriction on the general list layout.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.CellSequenceHosting

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LanguageDef.OperationalAdmission
open Mettapedia.GSLT.LanguageDef.ObservationRefinement
open Mettapedia.GSLT.LanguageDef.GSLTHosting
open CArray0SequenceHosting

abbrev Cell (α : Type) := Layouts.Cells α Empty

variable {α : Type}

def ofList : List α → Cell α
  | [] => .stop .nil
  | x :: xs => .cell x (ofList xs)

def elements (cells : Cell α) : List α := (Layouts.Cells.abs cells).1

def Closed (cells : Cell α) : Prop := (Layouts.Cells.abs cells).2 = .nil

@[simp] theorem ofList_elements (values : List α) : elements (ofList values) = values := by
  induction values with
  | nil => rfl
  | cons x xs ih => simpa [ofList, elements, Layouts.Cells.abs] using congrArg (x :: ·) ih

@[simp] theorem ofList_closed (values : List α) : Closed (ofList values) := by
  induction values with
  | nil => rfl
  | cons x xs ih => exact ih

inductive Outcome (α : Type) where
  | element (value : Option α)
  | count (value : Nat)
  | suffix (cells : Cell α)

def observeOutcome : Outcome α → SequenceObservation α
  | .element none => .declined
  | .element (some value) => .element value
  | .count value => .count value
  | .suffix cells => .sequence (elements cells)

inductive State (α : Type) where
  | lookup (index : Nat) (cells : Cell α)
  | count (accumulator : Nat) (cells : Cell α)
  | first (cells : Cell α)
  | rest (cells : Cell α)
  | halted (result : Outcome α)

inductive Step : State α → State α → Prop where
  | lookup_stop (index : Nat) (ending : Layouts.Terminal α Empty) :
      Step (.lookup index (.stop ending)) (.halted (.element none))
  | lookup_zero (x : α) (xs : Cell α) :
      Step (.lookup 0 (.cell x xs)) (.halted (.element (some x)))
  | lookup_next (index : Nat) (x : α) (xs : Cell α) :
      Step (.lookup (index + 1) (.cell x xs)) (.lookup index xs)
  | count_stop (accumulator : Nat) (ending : Layouts.Terminal α Empty) :
      Step (.count accumulator (.stop ending)) (.halted (.count accumulator))
  | count_next (accumulator : Nat) (x : α) (xs : Cell α) :
      Step (.count accumulator (.cell x xs)) (.count (accumulator + 1) xs)
  | first_stop (ending : Layouts.Terminal α Empty) :
      Step (.first (.stop ending)) (.halted (.element none))
  | first_cell (x : α) (xs : Cell α) :
      Step (.first (.cell x xs)) (.halted (.element (some x)))
  | rest_stop (ending : Layouts.Terminal α Empty) :
      Step (.rest (.stop ending)) (.halted (.element none))
  | rest_cell (x : α) (xs : Cell α) :
      Step (.rest (.cell x xs)) (.halted (.suffix xs))

@[reducible] def system (α : Type) : GSLT where
  Term := State α
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step
  rewrites_resp_left := by
    rintro first first' last equal step
    subst first'
    exact ⟨last, step, rfl⟩
  rewrites_resp_right := by
    rintro first last last' step equal
    subst last'
    exact step

def countResult : Nat → Cell α → Nat
  | n, .stop _ => n
  | n, .cell _ xs => countResult (n + 1) xs

theorem countResult_eq (n : Nat) (cells : Cell α) :
    countResult n cells = n + (elements cells).length := by
  induction cells generalizing n with
  | stop ending => simp [countResult, elements, Layouts.Cells.abs]
  | cell x xs ih =>
      simp only [countResult, ih, elements, Layouts.Cells.abs, List.length_cons]
      omega

def finish : SequenceOp → Cell α → Outcome α
  | .length, cells => .count (countResult 0 cells)
  | .first, .stop _ => .element none
  | .first, .cell x _ => .element (some x)
  | .rest, .stop _ => .element none
  | .rest, .cell _ xs => .suffix xs
  | .at index, cells => .element (Layouts.Cells.nth cells index)

def begin : SequenceOp → Cell α → State α
  | .length, cells => .count 0 cells
  | .first, cells => .first cells
  | .rest, cells => .rest cells
  | .at index, cells => .lookup index cells

def lookupPath (index : Nat) : (cells : Cell α) →
    ExecutionPath (system α) (.lookup index cells)
      (.halted (.element (Layouts.Cells.nth cells index)))
  | .stop ending => .cons ⟨.lookup_stop index ending⟩ (.refl _)
  | .cell x xs => match index with
    | 0 => .cons ⟨.lookup_zero x xs⟩ (.refl _)
    | n + 1 => .cons ⟨.lookup_next n x xs⟩ (lookupPath n xs)

def countPath (n : Nat) : (cells : Cell α) →
    ExecutionPath (system α) (.count n cells) (.halted (.count (countResult n cells)))
  | .stop ending => .cons ⟨.count_stop n ending⟩ (.refl _)
  | .cell x xs => .cons ⟨.count_next n x xs⟩ (countPath (n + 1) xs)

def requestPath (operation : SequenceOp) (cells : Cell α) :
    ExecutionPath (system α) (begin operation cells) (.halted (finish operation cells)) := by
  cases operation with
  | length => exact countPath 0 cells
  | «at» index => exact lookupPath index cells
  | first =>
      cases cells with
      | stop ending => exact .cons ⟨.first_stop ending⟩ (.refl _)
      | cell x xs => exact .cons ⟨.first_cell x xs⟩ (.refl _)
  | rest =>
      cases cells with
      | stop ending => exact .cons ⟨.rest_stop ending⟩ (.refl _)
      | cell x xs => exact .cons ⟨.rest_cell x xs⟩ (.refl _)

theorem finish_spec (operation : SequenceOp) (cells : Cell α) :
    observeOutcome (finish operation cells) = sequenceSem operation (elements cells) := by
  cases operation with
  | length => simp [finish, observeOutcome, sequenceSem, countResult_eq]
  | «at» index =>
      rw [finish, Layouts.Cells.nth_spec]
      change observeOutcome (.element ((elements cells)[index]?)) = _
      cases found : (elements cells)[index]? <;> simp [observeOutcome, sequenceSem, found]
  | first => cases cells <;> rfl
  | rest => cases cells <;> rfl

def meaning : State α → SequenceObservation α
  | .lookup index cells => observeOutcome (.element (Layouts.Cells.nth cells index))
  | .count n cells => .count (n + (elements cells).length)
  | .first cells => sequenceSem .first (elements cells)
  | .rest cells => sequenceSem .rest (elements cells)
  | .halted result => observeOutcome result

theorem step_conserves {first last : State α} (step : Step first last) :
    meaning first = meaning last := by
  cases step <;> simp [meaning, observeOutcome, Layouts.Cells.nth,
    elements, Layouts.Cells.abs, sequenceSem, Nat.add_assoc, Nat.add_comm]

def invariant : SemanticInvariant (system α) (SequenceObservation α) where
  denote := meaning
  equation := fun equal => congrArg meaning equal
  rewrite := step_conserves

inductive Formed : State α → Prop where
  | lookup (index : Nat) (cells : Cell α) : Closed cells → Formed (.lookup index cells)
  | count (n : Nat) (cells : Cell α) : Closed cells → Formed (.count n cells)
  | first (cells : Cell α) : Closed cells → Formed (.first cells)
  | rest (cells : Cell α) : Closed cells → Formed (.rest cells)
  | element (value : Option α) : Formed (.halted (.element value))
  | size (value : Nat) : Formed (.halted (.count value))
  | suffix (cells : Cell α) : Closed cells → Formed (.halted (.suffix cells))

theorem begin_formed (operation : SequenceOp) (cells : Cell α) (closed : Closed cells) :
    Formed (begin operation cells) := by
  cases operation <;> constructor <;> exact closed

theorem finish_formed (operation : SequenceOp) (cells : Cell α) (closed : Closed cells) :
    Formed (.halted (finish operation cells)) := by
  cases operation with
  | length => exact .size _
  | «at» index => exact .element _
  | first => cases cells <;> exact .element _
  | rest =>
      cases cells with
      | stop ending => exact .element _
      | cell x xs => exact .suffix xs closed

theorem formed_preserved {first last : State α} (step : Step first last)
    (formed : Formed first) : Formed last := by
  cases step <;> cases formed <;> constructor <;> assumption

def observe : State α → Option (SequenceObservation α)
  | .halted result => some (observeOutcome result)
  | _ => none

def targetObject (α : Type) : ObservedOperationalObject (SequenceObservation α) where
  operational := ⟨system α, Formed⟩
  observe := fun {_ last} _ => observe last

def compile : SequenceTerm α → State α
  | .request operation values => begin operation (ofList values)
  | .done operation values => .halted (finish operation (ofList values))

def realization : OperationalRealization (sequenceGSLT α) (system α) where
  mapTerm := compile
  mapEquiv := fun equal => congrArg compile equal
  mapStep := by
    intro first last step
    cases first with
    | done operation values => exact (no_sequence_step_from_done step).elim
    | request operation values =>
        have equal := sequence_step_from_request step
        subst last
        exact requestPath _ _

def refinement : Refinement (sourceObject α).operational (targetObject α).operational where
  realization := realization
  preservesMeaning := by
    intro term _
    cases term with
    | request operation values => exact begin_formed _ _ (ofList_closed values)
    | done operation values => exact finish_formed _ _ (ofList_closed values)

theorem observation_compiles (term : SequenceTerm α) :
    observe (compile term) = sequenceObserve term := by
  cases term with
  | request operation values => cases operation <;> rfl
  | done operation values => simp [compile, observe, sequenceObserve, finish_spec]

def forward : ObservedRefinement (sourceObject α) (targetObject α) where
  refinement := refinement
  commutes := by
    intro first last path
    exact observation_compiles last

theorem meaning_compile (term : SequenceTerm α) :
    meaning (compile term) = match term with
      | .request operation values | .done operation values => sequenceSem operation values := by
  cases term with
  | request operation values =>
      have same := invariant.executionPath_eq (requestPath operation (ofList values))
      change meaning (begin operation (ofList values)) =
        meaning (.halted (finish operation (ofList values))) at same
      exact same.trans (by rw [meaning, finish_spec, ofList_elements])
  | done operation values => simp [compile, meaning, finish_spec]

theorem observation_has_meaning {state : State α} {value : SequenceObservation α}
    (observed : observe state = some value) : meaning state = value := by
  cases state <;> simp_all [observe, meaning]

def hosting : BehavioralHosting (sourceObject α) (targetObject α) where
  forward := forward
  noInvention := by
    intro initial value produced
    change SequenceTerm α at initial
    obtain ⟨⟨final, path, observed⟩⟩ := produced
    have same := invariant.executionPath_eq path
    have actual := observation_has_meaning observed
    have expected := same.trans actual
    change meaning (compile initial) = value at expected
    rw [meaning_compile] at expected
    cases initial with
    | request operation values =>
        exact ⟨⟨.done operation values,
          .cons ⟨SequenceStep.run operation values⟩ (.refl _),
          congrArg some expected⟩⟩
    | done operation values =>
        exact ⟨⟨.done operation values, .refl _, congrArg some expected⟩⟩

theorem hosting_exact (initial : SequenceTerm α) (value : SequenceObservation α) :
    ProducesObservation (targetObject α) (compile initial) value ↔
      ProducesObservation (sourceObject α) initial value := hosting.produces_iff initial value

/-- Two operational interfaces share the existing source observation. This
does not identify their execution paths, representations or resource costs. -/
theorem cells_and_arrays_agree (initial : SequenceTerm α) (value : SequenceObservation α) :
    ProducesObservation (targetObject α) (compile initial) value ↔
      ProducesObservation (CArray0SequenceHosting.targetObject α)
        (compileTerm initial) value :=
  (hosting_exact initial value).trans (CArray0SequenceHosting.hosting_exact initial value).symm

end Mettapedia.GSLT.LanguageDef.Collections.CellSequenceHosting
