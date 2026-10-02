import Mettapedia.Languages.TuringMachine.Steps
import Mathlib.Computability.TuringMachine.Tape
import Mathlib.Logic.Relation

/-!
# Configurations of a Turing machine

Turing's complete configuration is the state of the control, the scanned
symbol, and what is written on the rest of the tape.  With finitely many
written cells it is four pieces of data: a state, the written cells to the
left of the head (nearest first), the scanned symbol, and the written cells
to the right.

On the terms of such configurations a step of the language definition is the
textbook step and nothing else (`step_term_iff`): some table entry is for the
current state and scanned symbol, and the configuration becomes the one in
which that entry has written its symbol, moved the head, and changed the
state.  Moving past the last written cell scans a blank.

Three consequences are recorded.

* A table with at most one entry for each state and symbol has at most one
  step from each pattern, and only such a table has (`step_unique`,
  `deterministic_of_step_unique`).
* The run that takes the first entry that applies is a function on
  configurations, so a concrete run of a concrete table is a computation
  (`reaches_runFor`, `haltsAfter_spec`).
* A configuration is a tape in the sense of Mathlib's `Turing.Tape`, and a
  step writes and then moves on that tape (`tape_after`).  Trailing blanks are
  identified there; the terms keep them apart.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-! ## Configurations and their terms -/

/-- A configuration with finitely many written cells. -/
structure Configuration where
  /-- The state of the control. -/
  state : Nat
  /-- The written cells to the left of the head, nearest first. -/
  left : List Nat
  /-- The scanned symbol. -/
  scanned : Nat
  /-- The written cells to the right of the head, nearest first. -/
  right : List Nat
deriving DecidableEq, Repr

/-- State zero scanning a blank tape. -/
def Configuration.blank : Configuration := ⟨0, [], 0, []⟩

/-- A list of symbols as a half-tape. -/
def cellsTerm : List Nat → Pattern
  | [] => emptyCells
  | symbol :: rest => cell (symbolTerm symbol) (cellsTerm rest)

/-- The term of a configuration. -/
def Configuration.term (configuration : Configuration) : Pattern :=
  run (stateTerm configuration.state)
    (tapeAt (cellsTerm configuration.left) (symbolTerm configuration.scanned)
      (cellsTerm configuration.right))

theorem stateTerm_injective : Function.Injective stateTerm :=
  Pattern.unary_injective (by decide)

theorem symbolTerm_injective : Function.Injective symbolTerm :=
  Pattern.unary_injective (by decide)

theorem cellsTerm_injective : Function.Injective cellsTerm := by
  intro first
  induction first with
  | nil =>
      intro second same
      cases second with
      | nil => rfl
      | cons symbol rest => simp [cellsTerm, emptyCells, cell] at same
  | cons symbol rest recurse =>
      intro second same
      cases second with
      | nil => simp [cellsTerm, emptyCells, cell] at same
      | cons otherSymbol otherRest =>
          simp only [cellsTerm, cell, Pattern.apply.injEq, List.cons.injEq, and_true,
            true_and] at same
          rw [symbolTerm_injective same.1, recurse same.2]

/-- Distinct configurations have distinct terms. -/
theorem Configuration.term_injective : Function.Injective Configuration.term := by
  rintro ⟨state, left, scanned, right⟩ ⟨otherState, otherLeft, otherScanned, otherRight⟩ same
  simp only [Configuration.term, run, tapeAt, Pattern.apply.injEq, List.cons.injEq, and_true,
    true_and] at same
  obtain ⟨states, lefts, symbols, rights⟩ := same
  rw [stateTerm_injective states, cellsTerm_injective lefts, symbolTerm_injective symbols,
    cellsTerm_injective rights]

/-! ## The textbook step -/

/-- A table entry applies to a configuration when it is the entry for the
current state and the scanned symbol. -/
def Transition.Applies (entry : Transition) (configuration : Configuration) : Prop :=
  entry.state = configuration.state ∧ entry.read = configuration.scanned

instance (entry : Transition) (configuration : Configuration) :
    Decidable (entry.Applies configuration) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The configuration after a table entry has written its symbol, moved the
head and changed the state.  Past the last written cell the head scans a
blank. -/
def Configuration.after (configuration : Configuration) (entry : Transition) : Configuration :=
  match entry.move with
  | .right =>
      match configuration.right with
      | [] =>
          { state := entry.next, left := entry.write :: configuration.left, scanned := 0,
            right := [] }
      | symbol :: rest =>
          { state := entry.next, left := entry.write :: configuration.left, scanned := symbol,
            right := rest }
  | .left =>
      match configuration.left with
      | [] =>
          { state := entry.next, left := [], scanned := 0,
            right := entry.write :: configuration.right }
      | symbol :: rest =>
          { state := entry.next, left := rest, scanned := symbol,
            right := entry.write :: configuration.right }

/-- The four shapes of a step, read on a configuration. -/
theorem machineStep_term_iff {machine : Machine} {configuration : Configuration}
    {target : Pattern} :
    MachineStep machine configuration.term target ↔
      ∃ entry ∈ machine.transitions,
        entry.Applies configuration ∧ target = (configuration.after entry).term := by
  obtain ⟨state, left, scanned, right⟩ := configuration
  constructor
  · intro shape
    generalize sourceEq : Configuration.term ⟨state, left, scanned, right⟩ = source at shape
    cases shape with
    | @interiorRight entry member move leftPattern current rightPattern =>
        simp only [Configuration.term, run, tapeAt, Pattern.apply.injEq, List.cons.injEq,
          and_true, true_and] at sourceEq
        obtain ⟨states, lefts, symbols, rights⟩ := sourceEq
        cases right with
        | nil => simp [cellsTerm, emptyCells, cell] at rights
        | cons symbol rest =>
            simp only [cellsTerm, cell, Pattern.apply.injEq, List.cons.injEq, and_true,
              true_and] at rights
            refine ⟨entry, member, ⟨(stateTerm_injective states).symm,
              (symbolTerm_injective symbols).symm⟩, ?_⟩
            simp only [Configuration.after, move, Configuration.term, cellsTerm, lefts,
              rights.1, rights.2]
    | @interiorLeft entry member move leftPattern current rightPattern =>
        simp only [Configuration.term, run, tapeAt, Pattern.apply.injEq, List.cons.injEq,
          and_true, true_and] at sourceEq
        obtain ⟨states, lefts, symbols, rights⟩ := sourceEq
        cases left with
        | nil => simp [cellsTerm, emptyCells, cell] at lefts
        | cons symbol rest =>
            simp only [cellsTerm, cell, Pattern.apply.injEq, List.cons.injEq, and_true,
              true_and] at lefts
            refine ⟨entry, member, ⟨(stateTerm_injective states).symm,
              (symbolTerm_injective symbols).symm⟩, ?_⟩
            simp only [Configuration.after, move, Configuration.term, cellsTerm, rights,
              lefts.1, lefts.2]
    | @edgeRight entry member move leftPattern =>
        simp only [Configuration.term, run, tapeAt, Pattern.apply.injEq, List.cons.injEq,
          and_true, true_and] at sourceEq
        obtain ⟨states, lefts, symbols, rights⟩ := sourceEq
        cases right with
        | cons symbol rest => simp [cellsTerm, emptyCells, cell] at rights
        | nil =>
            refine ⟨entry, member, ⟨(stateTerm_injective states).symm,
              (symbolTerm_injective symbols).symm⟩, ?_⟩
            simp only [Configuration.after, move, Configuration.term, cellsTerm, lefts]
    | @edgeLeft entry member move rightPattern =>
        simp only [Configuration.term, run, tapeAt, Pattern.apply.injEq, List.cons.injEq,
          and_true, true_and] at sourceEq
        obtain ⟨states, lefts, symbols, rights⟩ := sourceEq
        cases left with
        | cons symbol rest => simp [cellsTerm, emptyCells, cell] at lefts
        | nil =>
            refine ⟨entry, member, ⟨(stateTerm_injective states).symm,
              (symbolTerm_injective symbols).symm⟩, ?_⟩
            simp only [Configuration.after, move, Configuration.term, cellsTerm, rights]
  · rintro ⟨entry, member, ⟨states, symbols⟩, rfl⟩
    simp only at states symbols
    subst states symbols
    cases move : entry.move with
    | right =>
        cases right with
        | nil =>
            simp only [Configuration.after, move, Configuration.term, cellsTerm]
            exact .edgeRight member move _
        | cons symbol rest =>
            simp only [Configuration.after, move, Configuration.term, cellsTerm]
            exact .interiorRight member move _ _ _
    | left =>
        cases left with
        | nil =>
            simp only [Configuration.after, move, Configuration.term, cellsTerm]
            exact .edgeLeft member move _
        | cons symbol rest =>
            simp only [Configuration.after, move, Configuration.term, cellsTerm]
            exact .interiorLeft member move _ _ _

/-- **On configurations, a step of the language definition is the textbook
step**: an entry for the current state and scanned symbol writes, moves and
changes the state. -/
theorem step_term_iff {machine : Machine} {configuration : Configuration} {target : Pattern} :
    Step base (turingMachine machine) configuration.term target ↔
      ∃ entry ∈ machine.transitions,
        entry.Applies configuration ∧ target = (configuration.after entry).term :=
  step_iff_machineStep.trans machineStep_term_iff

/-- A step between the terms of two configurations. -/
theorem step_term_term_iff {machine : Machine} {configuration next : Configuration} :
    Step base (turingMachine machine) configuration.term next.term ↔
      ∃ entry ∈ machine.transitions,
        entry.Applies configuration ∧ next = configuration.after entry := by
  rw [step_term_iff]
  constructor
  · rintro ⟨entry, member, applies, same⟩
    exact ⟨entry, member, applies, Configuration.term_injective same⟩
  · rintro ⟨entry, member, applies, rfl⟩
    exact ⟨entry, member, applies, rfl⟩

/-! ## Halting -/

/-- No rule of the machine applies to the pattern. -/
def Halted (machine : Machine) (pattern : Pattern) : Prop :=
  ∀ target, ¬ Step base (turingMachine machine) pattern target

/-- Reduction in the language definition of a machine, in any number of
steps. -/
abbrev Reaches (machine : Machine) : Pattern → Pattern → Prop :=
  Relation.ReflTransGen (Step base (turingMachine machine))

/-- The machine can reach a pattern to which no rule applies. -/
def HaltsFrom (machine : Machine) (pattern : Pattern) : Prop :=
  ∃ final, Reaches machine pattern final ∧ Halted machine final

/-- A configuration is halted exactly when the table has no entry for its
state and scanned symbol. -/
theorem halted_term_iff {machine : Machine} {configuration : Configuration} :
    Halted machine configuration.term ↔
      ∀ entry ∈ machine.transitions, ¬ entry.Applies configuration := by
  constructor
  · intro halted entry member applies
    exact halted _ (step_term_iff.mpr ⟨entry, member, applies, rfl⟩)
  · intro none target step
    obtain ⟨entry, member, applies, -⟩ := step_term_iff.mp step
    exact none entry member applies

/-- Everything a configuration reduces to is the term of a configuration, and
it has every property that the entries of the table preserve. -/
theorem reaches_term_invariant {machine : Machine} (invariant : Configuration → Prop)
    (preserved : ∀ configuration, invariant configuration → ∀ entry ∈ machine.transitions,
      entry.Applies configuration → invariant (configuration.after entry))
    {start : Configuration} (holds : invariant start) {target : Pattern}
    (reaches : Reaches machine start.term target) :
    ∃ configuration, target = configuration.term ∧ invariant configuration := by
  induction reaches with
  | refl => exact ⟨start, rfl, holds⟩
  | tail _ step recurse =>
      obtain ⟨configuration, rfl, kept⟩ := recurse
      obtain ⟨entry, member, applies, rfl⟩ := step_term_iff.mp step
      exact ⟨_, rfl, preserved configuration kept entry member applies⟩

/-- A machine does not halt from a configuration with a property that the
entries preserve and that always leaves an entry to apply. -/
theorem not_haltsFrom_of_invariant {machine : Machine} (invariant : Configuration → Prop)
    (preserved : ∀ configuration, invariant configuration → ∀ entry ∈ machine.transitions,
      entry.Applies configuration → invariant (configuration.after entry))
    (live : ∀ configuration, invariant configuration →
      ∃ entry ∈ machine.transitions, entry.Applies configuration)
    {start : Configuration} (holds : invariant start) : ¬ HaltsFrom machine start.term := by
  rintro ⟨final, reaches, halted⟩
  obtain ⟨configuration, rfl, kept⟩ := reaches_term_invariant invariant preserved holds reaches
  obtain ⟨entry, member, applies⟩ := live configuration kept
  exact halted_term_iff.mp halted entry member applies

/-! ## Tables with one entry for each state and symbol -/

/-- The table has at most one entry for each state and scanned symbol.  This
is Turing's automatic machine; a table with a choice is his choice machine. -/
def Machine.Deterministic (machine : Machine) : Prop :=
  ∀ first ∈ machine.transitions, ∀ second ∈ machine.transitions,
    first.state = second.state → first.read = second.read → first = second

instance (machine : Machine) : Decidable machine.Deterministic :=
  inferInstanceAs (Decidable (∀ first ∈ machine.transitions, ∀ second ∈ machine.transitions,
    first.state = second.state → first.read = second.read → first = second))

/-- Two entries of a deterministic table at the head of one pattern are one
entry, with the same half-tapes on both sides. -/
private theorem sides_eq {machine : Machine} (deterministic : machine.Deterministic)
    {entry other : Transition} (member : entry ∈ machine.transitions)
    (otherMember : other ∈ machine.transitions) {left right otherLeft otherRight : Pattern}
    (same : run (stateTerm entry.state) (tapeAt left (symbolTerm entry.read) right) =
      run (stateTerm other.state) (tapeAt otherLeft (symbolTerm other.read) otherRight)) :
    entry = other ∧ left = otherLeft ∧ right = otherRight := by
  simp only [run, tapeAt, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
  obtain ⟨states, lefts, symbols, rights⟩ := same
  exact ⟨deterministic entry member other otherMember (stateTerm_injective states)
    (symbolTerm_injective symbols), lefts, rights⟩

private theorem MachineStep.unique_of_eq {machine : Machine}
    (deterministic : machine.Deterministic) {source other first second : Pattern}
    (firstStep : MachineStep machine source first)
    (secondStep : MachineStep machine other second) (same : source = other) :
    first = second := by
  cases firstStep with
  | @interiorRight entry member move left current right =>
      cases secondStep with
      | @interiorRight entry' member' move' left' current' right' =>
          obtain ⟨rfl, rfl, rights⟩ := sides_eq deterministic member member' same
          simp only [cell, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at rights
          rw [rights.1, rights.2]
      | @interiorLeft entry' member' move' left' current' right' =>
          obtain ⟨rfl, -, -⟩ := sides_eq deterministic member member' same
          exact absurd (move.symm.trans move') (by decide)
      | @edgeRight entry' member' move' left' =>
          obtain ⟨rfl, -, rights⟩ := sides_eq deterministic member member' same
          simp [cell, emptyCells] at rights
      | @edgeLeft entry' member' move' right' =>
          obtain ⟨rfl, -, -⟩ := sides_eq deterministic member member' same
          exact absurd (move.symm.trans move') (by decide)
  | @interiorLeft entry member move left current right =>
      cases secondStep with
      | @interiorRight entry' member' move' left' current' right' =>
          obtain ⟨rfl, -, -⟩ := sides_eq deterministic member member' same
          exact absurd (move.symm.trans move') (by decide)
      | @interiorLeft entry' member' move' left' current' right' =>
          obtain ⟨rfl, lefts, rfl⟩ := sides_eq deterministic member member' same
          simp only [cell, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at lefts
          rw [lefts.1, lefts.2]
      | @edgeRight entry' member' move' left' =>
          obtain ⟨rfl, -, -⟩ := sides_eq deterministic member member' same
          exact absurd (move.symm.trans move') (by decide)
      | @edgeLeft entry' member' move' right' =>
          obtain ⟨rfl, lefts, -⟩ := sides_eq deterministic member member' same
          simp [cell, emptyCells] at lefts
  | @edgeRight entry member move left =>
      cases secondStep with
      | @interiorRight entry' member' move' left' current' right' =>
          obtain ⟨rfl, -, rights⟩ := sides_eq deterministic member member' same
          simp [cell, emptyCells] at rights
      | @interiorLeft entry' member' move' left' current' right' =>
          obtain ⟨rfl, -, -⟩ := sides_eq deterministic member member' same
          exact absurd (move.symm.trans move') (by decide)
      | @edgeRight entry' member' move' left' =>
          obtain ⟨rfl, rfl, -⟩ := sides_eq deterministic member member' same
          rfl
      | @edgeLeft entry' member' move' right' =>
          obtain ⟨rfl, -, -⟩ := sides_eq deterministic member member' same
          exact absurd (move.symm.trans move') (by decide)
  | @edgeLeft entry member move right =>
      cases secondStep with
      | @interiorRight entry' member' move' left' current' right' =>
          obtain ⟨rfl, -, -⟩ := sides_eq deterministic member member' same
          exact absurd (move.symm.trans move') (by decide)
      | @interiorLeft entry' member' move' left' current' right' =>
          obtain ⟨rfl, lefts, -⟩ := sides_eq deterministic member member' same
          simp [cell, emptyCells] at lefts
      | @edgeRight entry' member' move' left' =>
          obtain ⟨rfl, -, -⟩ := sides_eq deterministic member member' same
          exact absurd (move.symm.trans move') (by decide)
      | @edgeLeft entry' member' move' right' =>
          obtain ⟨rfl, -, rfl⟩ := sides_eq deterministic member member' same
          rfl

/-- **A deterministic table has at most one step from each pattern**, a
configuration or not. -/
theorem step_unique {machine : Machine} (deterministic : machine.Deterministic)
    {source first second : Pattern}
    (firstStep : Step base (turingMachine machine) source first)
    (secondStep : Step base (turingMachine machine) source second) : first = second :=
  MachineStep.unique_of_eq deterministic (machineStep_of_step firstStep)
    (machineStep_of_step secondStep) rfl

/-- **A table with two entries for one state and symbol has a pattern with
two steps.**  With a written cell on each side the two entries give different
configurations. -/
theorem deterministic_of_step_unique {machine : Machine}
    (unique : ∀ source first second : Pattern,
      Step base (turingMachine machine) source first →
        Step base (turingMachine machine) source second → first = second) :
    machine.Deterministic := by
  intro entry member other otherMember states symbols
  let configuration : Configuration := ⟨entry.state, [0], entry.read, [0]⟩
  have firstStep : Step base (turingMachine machine) configuration.term
      (configuration.after entry).term :=
    step_term_iff.mpr ⟨entry, member, ⟨rfl, rfl⟩, rfl⟩
  have secondStep : Step base (turingMachine machine) configuration.term
      (configuration.after other).term :=
    step_term_iff.mpr ⟨other, otherMember, ⟨states.symm, symbols.symm⟩, rfl⟩
  have same : configuration.after entry = configuration.after other :=
    Configuration.term_injective (unique _ _ _ firstStep secondStep)
  obtain ⟨state, read, write, move, next⟩ := entry
  obtain ⟨otherState, otherRead, otherWrite, otherMove, otherNext⟩ := other
  simp only at states symbols
  subst states symbols
  cases move <;> cases otherMove <;>
    simp_all [configuration, Configuration.after]

/-! ## Running a table -/

/-- The first entry of the table for the state and scanned symbol of the
configuration. -/
def Machine.entryFor (machine : Machine) (configuration : Configuration) : Option Transition :=
  machine.transitions.find? fun entry =>
    entry.state == configuration.state && entry.read == configuration.scanned

/-- One step by the first entry that applies. -/
def Machine.next? (machine : Machine) (configuration : Configuration) : Option Configuration :=
  (machine.entryFor configuration).map configuration.after

/-- Take up to the given number of steps, stopping at a halted configuration. -/
def Machine.runFor (machine : Machine) : Nat → Configuration → Configuration
  | 0, configuration => configuration
  | count + 1, configuration =>
      match machine.next? configuration with
      | some next => machine.runFor count next
      | none => configuration

theorem Machine.entryFor_eq_some {machine : Machine} {configuration : Configuration}
    {entry : Transition} (found : machine.entryFor configuration = some entry) :
    entry ∈ machine.transitions ∧ entry.Applies configuration := by
  refine ⟨List.mem_of_find?_eq_some found, ?_⟩
  have holds := List.find?_some found
  simp only [Bool.and_eq_true, beq_iff_eq] at holds
  exact holds

theorem Machine.entryFor_eq_none {machine : Machine} {configuration : Configuration}
    (none : machine.entryFor configuration = none) :
    ∀ entry ∈ machine.transitions, ¬ entry.Applies configuration := by
  intro entry member applies
  have fails := List.find?_eq_none.mp none entry member
  simp only [Bool.and_eq_true, beq_iff_eq] at fails
  exact fails applies

/-- A step of the run is a step of the language definition. -/
theorem Machine.step_of_next? {machine : Machine} {configuration next : Configuration}
    (stepped : machine.next? configuration = some next) :
    Step base (turingMachine machine) configuration.term next.term := by
  unfold Machine.next? at stepped
  cases found : machine.entryFor configuration with
  | none => simp [found] at stepped
  | some entry =>
      rw [found] at stepped
      obtain rfl : configuration.after entry = next := by simpa using stepped
      obtain ⟨member, applies⟩ := Machine.entryFor_eq_some found
      exact step_term_iff.mpr ⟨entry, member, applies, rfl⟩

/-- Where the run stops, the language definition has no step. -/
theorem Machine.halted_of_next?_eq_none {machine : Machine} {configuration : Configuration}
    (stopped : machine.next? configuration = none) : Halted machine configuration.term := by
  unfold Machine.next? at stopped
  cases found : machine.entryFor configuration with
  | some entry => simp [found] at stopped
  | none => exact halted_term_iff.mpr (Machine.entryFor_eq_none found)

/-- The run is a reduction in the language definition. -/
theorem Machine.reaches_runFor (machine : Machine) (count : Nat) (configuration : Configuration) :
    Reaches machine configuration.term (machine.runFor count configuration).term := by
  induction count generalizing configuration with
  | zero => exact .refl
  | succ count recurse =>
      unfold Machine.runFor
      cases stepped : machine.next? configuration with
      | none => exact .refl
      | some next => exact .head (Machine.step_of_next? stepped) (recurse next)

/-- The run takes exactly `count` steps from `start` and stops at `final`. -/
def Machine.HaltsAfter (machine : Machine) (count : Nat) (start final : Configuration) : Prop :=
  machine.runFor count start = final ∧ machine.next? final = none ∧
    ∀ earlier < count, machine.next? (machine.runFor earlier start) ≠ none

instance (machine : Machine) (count : Nat) (start final : Configuration) :
    Decidable (machine.HaltsAfter count start final) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- What a halting run says in the language definition: the start reduces to
the final configuration, and no rule applies there. -/
theorem Machine.haltsAfter_spec {machine : Machine} {count : Nat} {start final : Configuration}
    (halts : machine.HaltsAfter count start final) :
    Reaches machine start.term final.term ∧ Halted machine final.term := by
  obtain ⟨ran, stopped, -⟩ := halts
  exact ⟨ran ▸ machine.reaches_runFor count start, Machine.halted_of_next?_eq_none stopped⟩

theorem Machine.haltsFrom_of_haltsAfter {machine : Machine} {count : Nat}
    {start final : Configuration} (halts : machine.HaltsAfter count start final) :
    HaltsFrom machine start.term :=
  ⟨final.term, Machine.haltsAfter_spec halts⟩

/-! ## The tape of Mathlib -/

/-- The direction of a move, as Mathlib names it. -/
def Move.dir : Move → Turing.Dir
  | .left => .left
  | .right => .right

/-- The tape of a configuration: blank beyond the written cells. -/
def Configuration.tape (configuration : Configuration) : Turing.Tape Nat :=
  Turing.Tape.mk₂ configuration.left (configuration.scanned :: configuration.right)

/-- The head of the tape is the scanned symbol. -/
theorem Configuration.tape_head (configuration : Configuration) :
    configuration.tape.head = configuration.scanned := by
  simp [Configuration.tape, Turing.Tape.mk₂]

/-- A written blank at the end of a half-tape is no cell of Mathlib's tape. -/
theorem listBlank_mk_blank :
    Turing.ListBlank.mk [(0 : Nat)] = Turing.ListBlank.mk [] := by
  simpa using Turing.ListBlank.cons_head_tail (Turing.ListBlank.mk ([] : List Nat))

/-- **A step writes and then moves on Mathlib's tape.**  The two rules of an
entry, one for a written neighbour and one for the edge, are one move there:
the tape is blank beyond the written cells. -/
theorem Configuration.tape_after (configuration : Configuration) (entry : Transition) :
    (configuration.after entry).tape =
      (configuration.tape.write entry.write).move entry.move.dir := by
  obtain ⟨state, left, scanned, right⟩ := configuration
  cases move : entry.move with
  | right =>
      cases right with
      | nil =>
          simp [Configuration.after, move, Configuration.tape, Move.dir, Turing.Tape.mk₂,
            listBlank_mk_blank]
      | cons symbol rest =>
          simp [Configuration.after, move, Configuration.tape, Move.dir, Turing.Tape.mk₂]
  | left =>
      cases left with
      | nil =>
          simp [Configuration.after, move, Configuration.tape, Move.dir, Turing.Tape.mk₂]
      | cons symbol rest =>
          simp [Configuration.after, move, Configuration.tape, Move.dir, Turing.Tape.mk₂]

/-- Two configurations that differ only in a written blank at the end of a
half-tape have distinct terms and one tape. -/
theorem trailing_blank_same_tape :
    (⟨0, [], 1, [0]⟩ : Configuration).tape = (⟨0, [], 1, []⟩ : Configuration).tape ∧
      (⟨0, [], 1, [0]⟩ : Configuration).term ≠ (⟨0, [], 1, []⟩ : Configuration).term := by
  constructor
  · have blank := congrArg (Turing.ListBlank.cons 1) listBlank_mk_blank
    simp only [Turing.ListBlank.cons_mk] at blank
    simp [Configuration.tape, Turing.Tape.mk₂, blank]
  · intro same
    have equal := Configuration.term_injective same
    simp at equal

end Mettapedia.Languages.TuringMachine
