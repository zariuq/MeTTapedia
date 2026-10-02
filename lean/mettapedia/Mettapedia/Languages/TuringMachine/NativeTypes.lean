import Mettapedia.Languages.TuringMachine.ClassicMachines
import Mettapedia.Languages.TuringMachine.OneSort
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.FormulaFixpoint

/-!
# The native types of a Turing machine

The OSLF construction turns a language definition into a type system:
predicates on its terms, the modality `◇` of one step into a predicate, and
its right adjoint `□` of every one-step predecessor.  This module reads that
type system off for a transition table.  What it sees is small.

* **No constructor leads from one sort to another by itself.**  States,
  symbols, half-tapes, tapes and configurations are five sorts, and the
  signature has no unary constructor between two of them
  (`unaryCrossings_eq_nil`).  The rho calculus has two: quote and drop.
* **"Can step" is a union of constructor types, one for each row.**  A
  configuration can step exactly when it is in the state of some row and
  scans the symbol of that row (`canStep_term_iff`).  For patterns that are
  not configurations only one direction holds: the rules must see whether
  the neighbouring cell is written (`atRow_open_not_canStep`).
* **Each row is a typing rule.**  From its state and symbol, one step leads
  into its next state (`diamond_inState_of_row`).
* **Read through `□`, the table runs backwards.**  Whatever steps into a
  state was at a row that leads to it (`inState_le_box_rows`); a state that no
  row leads to has no predecessor (`inState_le_box_false`); and the blank
  tape of Turing's first example has none, since every step of that machine
  writes a cell (`alternating_blank_no_predecessor`).
* **Turing's automatic machines are those whose `◇` preserves conjunction**
  (`deterministic_iff_diamond_and`).  A table with a choice fails the law
  (`choice_fails_diamond_and`).
* **Halting is a least fixed point**, of `X ↦ halted ∨ ◇ X`
  (`haltsFrom_eq_lfp`).  Radó's table on the blank tape has that type;
  Turing's first example does not, and has the greatest fixed point of `◇`
  instead (`alternating_runs_forever`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.FormulaFixpoint

variable {machine : Machine}

/-! ## The generated type system -/

/-- The step that the generated type system consumes is the step of the
machine: the presentation has no equation. -/
theorem semanticStep_iff (machine : Machine) (source target : Pattern) :
    langSemanticReduces (turingMachine machine) source target ↔
      Step base (turingMachine machine) source target :=
  langSemanticReduces_iff_langReduces_of_equation_free (turingMachine_equationFree machine)
    source target

/-- A predicate on patterns, as a predicate of the generated type system.
Every predicate is one, since no equation has to be respected. -/
def asType (machine : Machine) (predicate : Pattern → Prop) :
    EquationPredicate (langGSLT (turingMachine machine)) :=
  equationPredicateOfEquationFree (turingMachine_equationFree machine) predicate

/-- `◇`: some step leads into the predicate. -/
theorem diamond_iff (predicate : Pattern → Prop) (source : Pattern) :
    langDiamond (turingMachine machine) (asType machine predicate) source ↔
      ∃ target, Step base (turingMachine machine) source target ∧ predicate target := by
  rw [langDiamond_spec]
  constructor
  · rintro ⟨target, step, holds⟩
    exact ⟨target, (semanticStep_iff machine source target).mp step, holds⟩
  · rintro ⟨target, step, holds⟩
    exact ⟨target, (semanticStep_iff machine source target).mpr step, holds⟩

/-- `□`: every one-step predecessor is in the predicate. -/
theorem box_iff (predicate : Pattern → Prop) (target : Pattern) :
    langBox (turingMachine machine) (asType machine predicate) target ↔
      ∀ source, Step base (turingMachine machine) source target → predicate source := by
  rw [langBox_spec]
  constructor
  · intro holds source step
    exact holds source ((semanticStep_iff machine source target).mpr step)
  · intro holds source step
    exact holds source ((semanticStep_iff machine source target).mp step)

/-- The two modalities are adjoint, as for every language definition. -/
theorem diamond_box_galois (machine : Machine) :
    GaloisConnection (langDiamond (turingMachine machine)) (langBox (turingMachine machine)) :=
  langGalois (turingMachine machine)

/-! ## The constructors -/

/-- **No unary constructor leads from one sort to another.** -/
theorem unaryCrossings_eq_nil (machine : Machine) :
    unaryCrossings (turingMachine machine) = [] := by
  show unaryCrossings
    { name := "TuringMachine", types := ["State", "Symbol", "Cells", "Tape", "Config"],
      terms := terms, equations := [], rewrites := [] } = []
  decide

/-- The rho calculus has such a constructor in each direction. -/
theorem rhoCalc_crossings :
    ("NQuote", "Proc", "Name") ∈ unaryCrossings rhoCalc ∧
      ("PDrop", "Name", "Proc") ∈ unaryCrossings rhoCalc := by
  decide

/-- The configurations in a given state. -/
def InState (state : Nat) (pattern : Pattern) : Prop :=
  ∃ tape, pattern = run (stateTerm state) tape

/-- The configurations that scan a given symbol. -/
def Scanning (symbol : Nat) (pattern : Pattern) : Prop :=
  ∃ control left right, pattern = run control (tapeAt left (symbolTerm symbol) right)

/-- The configurations at a row of the table: in its state, scanning its
symbol. -/
def AtRow (entry : Transition) (pattern : Pattern) : Prop :=
  InState entry.state pattern ∧ Scanning entry.read pattern

theorem inState_term_iff {state : Nat} {configuration : Configuration} :
    InState state configuration.term ↔ configuration.state = state := by
  constructor
  · rintro ⟨tape, same⟩
    simp only [Configuration.term, run, Pattern.apply.injEq, List.cons.injEq, and_true,
      true_and] at same
    exact stateTerm_injective same.1
  · rintro rfl
    exact ⟨_, rfl⟩

theorem scanning_term_iff {symbol : Nat} {configuration : Configuration} :
    Scanning symbol configuration.term ↔ configuration.scanned = symbol := by
  constructor
  · rintro ⟨control, left, right, same⟩
    simp only [Configuration.term, run, tapeAt, Pattern.apply.injEq, List.cons.injEq, and_true,
      true_and] at same
    exact symbolTerm_injective same.2.2.1
  · rintro rfl
    exact ⟨_, _, _, rfl⟩

theorem atRow_term_iff {entry : Transition} {configuration : Configuration} :
    AtRow entry configuration.term ↔ entry.Applies configuration := by
  unfold AtRow Transition.Applies
  rw [inState_term_iff, scanning_term_iff]
  constructor <;> rintro ⟨states, symbols⟩ <;> exact ⟨states.symm, symbols.symm⟩

/-- The source of a step is at a row of the table. -/
theorem MachineStep.atRow {source target : Pattern} (step : MachineStep machine source target) :
    ∃ entry ∈ machine.transitions, AtRow entry source ∧ InState entry.next target := by
  cases step with
  | @interiorRight entry member move left current right =>
      exact ⟨entry, member, ⟨⟨_, rfl⟩, ⟨_, _, _, rfl⟩⟩, ⟨_, rfl⟩⟩
  | @interiorLeft entry member move left current right =>
      exact ⟨entry, member, ⟨⟨_, rfl⟩, ⟨_, _, _, rfl⟩⟩, ⟨_, rfl⟩⟩
  | @edgeRight entry member move left =>
      exact ⟨entry, member, ⟨⟨_, rfl⟩, ⟨_, _, _, rfl⟩⟩, ⟨_, rfl⟩⟩
  | @edgeLeft entry member move right =>
      exact ⟨entry, member, ⟨⟨_, rfl⟩, ⟨_, _, _, rfl⟩⟩, ⟨_, rfl⟩⟩

/-! ## One step forward -/

/-- Whatever can step is at a row of the table. -/
theorem canStep_le_rows :
    langDiamond (turingMachine machine) (asType machine fun _ => True) ≤
      asType machine fun source => ∃ entry ∈ machine.transitions, AtRow entry source := by
  intro source canStep
  obtain ⟨target, step, -⟩ := (diamond_iff _ source).mp canStep
  obtain ⟨entry, member, atRow, -⟩ := (machineStep_of_step step).atRow
  exact ⟨entry, member, atRow⟩

/-- **A configuration can step exactly when it is at a row of the table.** -/
theorem canStep_term_iff {configuration : Configuration} :
    langDiamond (turingMachine machine) (asType machine fun _ => True) configuration.term ↔
      ∃ entry ∈ machine.transitions, AtRow entry configuration.term := by
  constructor
  · exact fun canStep => canStep_le_rows _ canStep
  · rintro ⟨entry, member, atRow⟩
    exact (diamond_iff _ _).mpr
      ⟨_, step_term_iff.mpr ⟨entry, member, atRow_term_iff.mp atRow, rfl⟩, trivial⟩

/-- **Each row is a typing rule**: a configuration at the row has a step into
the next state of the row. -/
theorem diamond_inState_of_row {entry : Transition} (member : entry ∈ machine.transitions)
    {configuration : Configuration} (applies : entry.Applies configuration) :
    langDiamond (turingMachine machine) (asType machine (InState entry.next))
      configuration.term := by
  refine (diamond_iff _ _).mpr ⟨_, step_term_iff.mpr ⟨entry, member, applies, rfl⟩, ?_⟩
  refine inState_term_iff.mpr ?_
  unfold Configuration.after
  split <;> split <;> rfl

/-- A tape whose neighbouring cell is a variable is at the row of
`appendOne` for a one, and cannot step: the rules must see whether that cell
is written. -/
theorem atRow_open_not_canStep :
    AtRow ⟨0, 1, 1, .right, 0⟩
        (run (stateTerm 0) (tapeAt emptyCells (symbolTerm 1) (.fvar "r"))) ∧
      ¬ langDiamond (turingMachine appendOne) (asType appendOne fun _ => True)
        (run (stateTerm 0) (tapeAt emptyCells (symbolTerm 1) (.fvar "r"))) := by
  refine ⟨⟨⟨_, rfl⟩, ⟨_, _, _, rfl⟩⟩, ?_⟩
  intro canStep
  obtain ⟨target, step, -⟩ := (diamond_iff _ _).mp canStep
  have shape := machineStep_of_step step
  generalize sourceEq :
    run (stateTerm 0) (tapeAt emptyCells (symbolTerm 1) (.fvar "r")) = source at shape
  cases shape with
  | @interiorRight entry member move left current right =>
      simp [run, tapeAt, cell] at sourceEq
  | @interiorLeft entry member move left current right =>
      simp [run, tapeAt, cell, emptyCells] at sourceEq
  | @edgeRight entry member move left =>
      simp [run, tapeAt, emptyCells] at sourceEq
  | @edgeLeft entry member move right =>
      simp only [appendOne, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> cases move

/-! ## One step backward -/

/-- **The table read backwards.**  Whatever steps into a configuration in a
given state was at a row that leads to that state. -/
theorem inState_le_box_rows (state : Nat) :
    asType machine (InState state) ≤
      langBox (turingMachine machine)
        (asType machine fun source =>
          ∃ entry ∈ machine.transitions, entry.next = state ∧ AtRow entry source) := by
  rintro target ⟨tape, rfl⟩
  refine (box_iff _ _).mpr fun source step => ?_
  obtain ⟨entry, member, atRow, ⟨otherTape, same⟩⟩ := (machineStep_of_step step).atRow
  simp only [run, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
  exact ⟨entry, member, (stateTerm_injective same.1).symm, atRow⟩

/-- The same fact through the adjunction: what can step into a state is at a
row that leads to it. -/
theorem diamond_inState_le_rows (state : Nat) :
    langDiamond (turingMachine machine) (asType machine (InState state)) ≤
      asType machine fun source =>
        ∃ entry ∈ machine.transitions, entry.next = state ∧ AtRow entry source :=
  (diamond_box_galois machine _ _).mpr (inState_le_box_rows state)

/-- **A state that no row leads to has no predecessor.** -/
theorem inState_le_box_false {state : Nat}
    (unentered : ∀ entry ∈ machine.transitions, entry.next ≠ state) :
    asType machine (InState state) ≤
      langBox (turingMachine machine) (asType machine fun _ => False) := by
  intro target inState
  refine (box_iff _ _).mpr fun source step => ?_
  obtain ⟨entry, member, leads, -⟩ :=
    (box_iff _ _).mp (inState_le_box_rows state target inState) source step
  exact unentered entry member leads

/-- Radó's table halts in one way: every predecessor of a configuration in
its halting state was in state one scanning a one. -/
theorem busyBeaver2_halting_row :
    asType busyBeaver2 (InState 2) ≤
      langBox (turingMachine busyBeaver2)
        (asType busyBeaver2 (AtRow ⟨1, 1, 1, .right, 2⟩)) := by
  intro target inState
  refine (box_iff _ _).mpr fun source step => ?_
  obtain ⟨entry, member, leads, atRow⟩ :=
    (box_iff _ _).mp (inState_le_box_rows 2 target inState) source step
  simp only [busyBeaver2, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · cases leads
  · cases leads
  · cases leads
  · exact atRow

/-- The blank tape of Turing's first example has no predecessor: every step
of that machine writes a cell to the left of the head. -/
theorem alternating_blank_no_predecessor :
    langBox (turingMachine alternating) (asType alternating fun _ => False)
      Configuration.blank.term := by
  refine (box_iff _ _).mpr fun source step => ?_
  have shape := machineStep_of_step step
  generalize targetEq : Configuration.blank.term = target at shape
  cases shape with
  | @interiorRight entry member move left current right =>
      simp [Configuration.blank, Configuration.term, cellsTerm, run, tapeAt, cell, emptyCells]
        at targetEq
  | @edgeRight entry member move left =>
      simp [Configuration.blank, Configuration.term, cellsTerm, run, tapeAt, cell, emptyCells]
        at targetEq
  | @interiorLeft entry member move left current right =>
      simp only [alternating, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> cases move
  | @edgeLeft entry member move right =>
      simp only [alternating, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> cases move

/-- The configuration at which Radó's table stops does have one. -/
theorem busyBeaver2_final_has_predecessor :
    ¬ langBox (turingMachine busyBeaver2) (asType busyBeaver2 fun _ => False)
      busyBeaver2Final.term := by
  intro none
  have stepped : busyBeaver2.next? (busyBeaver2.runFor 5 Configuration.blank) =
      some busyBeaver2Final := by decide +kernel
  exact (box_iff _ _).mp none _ (Machine.step_of_next? stepped)

/-! ## Automatic and choice machines -/

/-- **A table has one row for each state and symbol exactly when `◇`
preserves conjunction.**  Turing's automatic machine, as a law of the
generated type system. -/
theorem deterministic_iff_diamond_and :
    machine.Deterministic ↔
      ∀ (first second : Pattern → Prop) (source : Pattern),
        langDiamond (turingMachine machine) (asType machine first) source →
          langDiamond (turingMachine machine) (asType machine second) source →
            langDiamond (turingMachine machine)
              (asType machine fun target => first target ∧ second target) source := by
  constructor
  · intro deterministic first second source firstHolds secondHolds
    obtain ⟨target, step, holds⟩ := (diamond_iff _ _).mp firstHolds
    obtain ⟨other, otherStep, otherHolds⟩ := (diamond_iff _ _).mp secondHolds
    obtain rfl := step_unique deterministic step otherStep
    exact (diamond_iff _ _).mpr ⟨target, step, holds, otherHolds⟩
  · intro law
    refine deterministic_of_step_unique fun source first second firstStep secondStep => ?_
    obtain ⟨target, -, isFirst, isSecond⟩ := (diamond_iff _ _).mp
      (law (· = first) (· = second) source ((diamond_iff _ _).mpr ⟨first, firstStep, rfl⟩)
        ((diamond_iff _ _).mpr ⟨second, secondStep, rfl⟩))
    exact isFirst.symm.trans isSecond

/-- A table with a choice: on a blank it may write a one or leave the blank. -/
def choice : Machine where
  transitions :=
    [ { state := 0, read := 0, write := 1, move := .right, next := 1 },
      { state := 0, read := 0, write := 0, move := .right, next := 1 } ]

theorem choice_not_deterministic : ¬ choice.Deterministic := by decide

/-- No row of that table leads to its first state, so a configuration in the
first state has no predecessor. -/
theorem choice_start_no_predecessor :
    asType choice (InState 0) ≤
      langBox (turingMachine choice) (asType choice fun _ => False) :=
  inState_le_box_false (by decide)

/-- For the table with a choice, `◇` does not preserve conjunction. -/
theorem choice_fails_diamond_and :
    ¬ ∀ (first second : Pattern → Prop) (source : Pattern),
        langDiamond (turingMachine choice) (asType choice first) source →
          langDiamond (turingMachine choice) (asType choice second) source →
            langDiamond (turingMachine choice)
              (asType choice fun target => first target ∧ second target) source :=
  fun law => choice_not_deterministic (deterministic_iff_diamond_and.mpr law)

/-- The classic tables are automatic machines, so the law holds for them. -/
theorem busyBeaver4_diamond_and (first second : Pattern → Prop) (source : Pattern) :
    langDiamond (turingMachine busyBeaver4) (asType busyBeaver4 first) source →
      langDiamond (turingMachine busyBeaver4) (asType busyBeaver4 second) source →
        langDiamond (turingMachine busyBeaver4)
          (asType busyBeaver4 fun target => first target ∧ second target) source :=
  deterministic_iff_diamond_and.mp (by decide) first second source

/-! ## Halting as a fixed point -/

/-- The predicate transformer `X ↦ halted ∨ ◇ X`. -/
def haltingTransformer (machine : Machine) : Pred →o Pred :=
  comp (orWith (Halted machine)) (diaOf (Step base (turingMachine machine)))

/-- The transformer `◇` of the fixed-point layer is the generated modality. -/
theorem diaOf_iff_diamond (predicate : Pattern → Prop) (source : Pattern) :
    diaOf (Step base (turingMachine machine)) predicate source ↔
      langDiamond (turingMachine machine) (asType machine predicate) source :=
  (diamond_iff predicate source).symm

/-- **Halting is the least fixed point of `X ↦ halted ∨ ◇ X`.** -/
theorem haltsFrom_eq_lfp (machine : Machine) :
    HaltsFrom machine = lfp (haltingTransformer machine) := by
  funext source
  apply propext
  constructor
  · rintro ⟨final, reaches, halted⟩
    induction reaches using Relation.ReflTransGen.head_induction_on with
    | refl => exact mem_lfp_of_mem_apply (Or.inl halted)
    | head step _ recurse => exact mem_lfp_of_mem_apply (Or.inr ⟨_, step, recurse⟩)
  · refine lfp_le (p := HaltsFrom machine) ?_ source
    rintro term (halted | ⟨successor, step, final, reaches, halted⟩)
    · exact ⟨term, .refl, halted⟩
    · exact ⟨final, .head step reaches, halted⟩

/-- Radó's table on the blank tape has the type of halting. -/
theorem busyBeaver2_halts :
    lfp (haltingTransformer busyBeaver2) Configuration.blank.term := by
  rw [← haltsFrom_eq_lfp]
  exact Machine.haltsFrom_of_haltsAfter busyBeaver2_haltsAfter

/-- Turing's first example on the blank tape does not. -/
theorem alternating_not_halts :
    ¬ lfp (haltingTransformer alternating) Configuration.blank.term := by
  rw [← haltsFrom_eq_lfp]
  exact alternating_never_halts

/-- **Turing's first example has the greatest fixed point of `◇`**: from the
blank tape there is a run that never ends. -/
theorem alternating_runs_forever :
    OrderHom.gfp (diaOf (Step base (turingMachine alternating)))
      Configuration.blank.term := by
  let scanningBlankAtEnd : Pred := fun pattern =>
    ∃ configuration : Configuration, pattern = configuration.term ∧
      configuration.state < 4 ∧ configuration.scanned = 0 ∧ configuration.right = []
  have postFixed : scanningBlankAtEnd ≤
      diaOf (Step base (turingMachine alternating)) scanningBlankAtEnd := by
    rintro pattern ⟨⟨state, left, scanned, right⟩, rfl, bound, rfl, rfl⟩
    simp only at bound
    have stepsTo : ∀ entry ∈ alternating.transitions,
        entry.Applies ⟨state, left, 0, []⟩ → entry.move = .right → entry.next < 4 →
          diaOf (Step base (turingMachine alternating)) scanningBlankAtEnd
            (⟨state, left, 0, []⟩ : Configuration).term := by
      intro entry member applies move small
      refine ⟨_, step_term_iff.mpr ⟨entry, member, applies, rfl⟩, _, rfl, ?_⟩
      simp [Configuration.after, move, small]
    interval_cases state
    · exact stepsTo ⟨0, 0, 1, .right, 1⟩ (by decide) ⟨rfl, rfl⟩ rfl (by decide)
    · exact stepsTo ⟨1, 0, 0, .right, 2⟩ (by decide) ⟨rfl, rfl⟩ rfl (by decide)
    · exact stepsTo ⟨2, 0, 2, .right, 3⟩ (by decide) ⟨rfl, rfl⟩ rfl (by decide)
    · exact stepsTo ⟨3, 0, 0, .right, 0⟩ (by decide) ⟨rfl, rfl⟩ rfl (by decide)
  exact OrderHom.le_gfp _ postFixed _ ⟨Configuration.blank, rfl, by decide, rfl, rfl⟩

end Mettapedia.Languages.TuringMachine
