import Mettapedia.Languages.TuringMachine.MathlibBridge
import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite Mathlib machines compiled to authored transition tables

Labels and symbols have injective numberings; the symbol map preserves the
blank. Even states represent native labels. A native move takes one row. A
native write takes two rows through an odd state, moving right and returning
left. The comparison retains an explicit finite alphabet invariant and proves
both output-tape correspondence and termination equivalence. It does not
identify raw terms which differ only in trailing blanks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine.FinitePostCompiler

open Turing Mettapedia.OSLF.MeTTaIL.ContextualStep

variable {Γ Λ : Type} [Inhabited Γ]

/-- An injective numbering of labels and blank-preserving numbering of symbols. -/
structure Encoding (Γ Λ : Type) [Inhabited Γ] where
  label : Λ ↪ Nat
  symbol : PointedMap Γ Nat
  symbol_injective : Function.Injective symbol

variable (encoding : Encoding Γ Λ)

def moveOfDir : Dir → Move
  | .left => .left
  | .right => .right

@[simp] theorem dir_moveOfDir (direction : Dir) : (moveOfDir direction).dir = direction := by
  cases direction <;> rfl

def primary (state : Λ) (read : Γ) (next : Λ) (command : TM0.Stmt Γ) : Transition :=
  match command with
  | .move direction =>
      ⟨2 * encoding.label state, encoding.symbol read, encoding.symbol read,
        moveOfDir direction, 2 * encoding.label next⟩
  | .write symbol =>
      ⟨2 * encoding.label state, encoding.symbol read, encoding.symbol symbol,
        .right, 2 * encoding.label next + 1⟩

def restore (next : Λ) (read : Γ) : Transition :=
  ⟨2 * encoding.label next + 1, encoding.symbol read, encoding.symbol read,
    .left, 2 * encoding.label next⟩

@[simp] theorem primary_state (state : Λ) (read : Γ) (next : Λ) (command : TM0.Stmt Γ) :
    (primary encoding state read next command).state = 2 * encoding.label state := by
  cases command <;> rfl

@[simp] theorem primary_read (state : Λ) (read : Γ) (next : Λ) (command : TM0.Stmt Γ) :
    (primary encoding state read next command).read = encoding.symbol read := by
  cases command <;> rfl

section Table

variable [Inhabited Λ] [Fintype Γ] [Fintype Λ]

def rowsFor (source : TM0.Machine Γ Λ) (state : Λ) (read : Γ) : List Transition :=
  match source state read with
  | none => []
  | some (next, command) => [primary encoding state read next command]

noncomputable def table (source : TM0.Machine Γ Λ) : Machine :=
  ⟨(Finset.univ.toList.flatMap fun state =>
      Finset.univ.toList.flatMap fun read => rowsFor encoding source state read) ++
    (Finset.univ.toList.flatMap fun next =>
      Finset.univ.toList.map fun read => restore encoding next read)⟩

theorem mem_table (source : TM0.Machine Γ Λ) (entry : Transition) :
    entry ∈ (table encoding source).transitions ↔
      (∃ state read next command, source state read = some (next, command) ∧
        entry = primary encoding state read next command) ∨
      (∃ next read, entry = restore encoding next read) := by
  simp only [table, List.mem_append, List.mem_flatMap, Finset.mem_toList,
    Finset.mem_univ, true_and, List.mem_map]
  constructor
  · rintro (⟨state, read, member⟩ | ⟨next, read, rfl⟩)
    · cases found : source state read with
      | none => simp [rowsFor, found] at member
      | some result =>
          obtain ⟨next, command⟩ := result
          have same : entry = primary encoding state read next command := by
            simpa [rowsFor, found] using member
          exact Or.inl ⟨state, read, next, command, found, same⟩
    · exact Or.inr ⟨next, read, rfl⟩
  · rintro (⟨state, read, next, command, found, rfl⟩ | ⟨next, read, rfl⟩)
    · exact Or.inl ⟨state, read, by simp [rowsFor, found]⟩
    · exact Or.inr ⟨next, read, rfl⟩

theorem deterministic (source : TM0.Machine Γ Λ) : (table encoding source).Deterministic := by
  intro first firstMember second secondMember sameState sameRead
  rcases (mem_table encoding source first).mp firstMember with
    ⟨state, read, next, command, found, rfl⟩ | ⟨next, read, rfl⟩
  · rcases (mem_table encoding source second).mp secondMember with
      ⟨state', read', next', command', found', rfl⟩ | ⟨next', read', rfl⟩
    · have states : state = state' := encoding.label.injective (by
        simp only [primary_state] at sameState
        omega)
      have reads : read = read' := encoding.symbol_injective (by
        simpa only [primary_read] using sameRead)
      subst state' read'
      have results := Option.some.inj (found.symm.trans found')
      cases results
      rfl
    · simp only [primary_state, restore] at sameState
      omega
  · rcases (mem_table encoding source second).mp secondMember with
      ⟨state', read', next', command', found', rfl⟩ | ⟨next', read', rfl⟩
    · simp only [primary_state, restore] at sameState
      omega
    · have states : next = next' := encoding.label.injective (by
        simp only [restore] at sameState
        omega)
      have reads : read = read' := encoding.symbol_injective sameRead
      subst next' read'
      rfl

end Table

def UsesAlphabet (configuration : Configuration) : Prop :=
  configuration.left.Forall (fun symbol => ∃ value, encoding.symbol value = symbol) ∧
  (∃ value, encoding.symbol value = configuration.scanned) ∧
  configuration.right.Forall (fun symbol => ∃ value, encoding.symbol value = symbol)

theorem after_usesAlphabet {configuration : Configuration}
    (valid : UsesAlphabet encoding configuration) (entry : Transition)
    (write : ∃ value, encoding.symbol value = entry.write) :
    UsesAlphabet encoding (configuration.after entry) := by
  obtain ⟨state, left, scanned, right⟩ := configuration
  obtain ⟨lefts, head, rights⟩ := valid
  have blank : ∃ value, encoding.symbol value = 0 := ⟨default, encoding.symbol.map_pt⟩
  cases move : entry.move
  · cases left <;> simp_all [UsesAlphabet, Configuration.after, List.Forall]
  · cases right <;> simp_all [UsesAlphabet, Configuration.after, List.Forall]

def Represents (native : TM0.Cfg Γ Λ) (configuration : Configuration) : Prop :=
  configuration.state = 2 * encoding.label native.q ∧
  configuration.tape = native.Tape.map encoding.symbol ∧
  UsesAlphabet encoding configuration

theorem scanned_of_represents {native : TM0.Cfg Γ Λ} {configuration : Configuration}
    (represented : Represents encoding native configuration) :
    configuration.scanned = encoding.symbol native.Tape.head := by
  simpa only [Configuration.tape_head, Tape.map_fst] using
    congrArg Tape.head represented.2.1

theorem primary_applies {native : TM0.Cfg Γ Λ} {configuration : Configuration}
    (represented : Represents encoding native configuration)
    (next : Λ) (command : TM0.Stmt Γ) :
    (primary encoding native.q native.Tape.head next command).Applies configuration := by
  exact ⟨(primary_state _ _ _ _ _).trans represented.1.symm,
    (primary_read _ _ _ _ _).trans (scanned_of_represents encoding represented).symm⟩


/-- A configuration representing a native tape initially containing `input`. -/
def initial [Inhabited Λ] (input : List Γ) : Configuration :=
  ⟨2 * encoding.label default, [], encoding.symbol input.headI,
    input.tail.map encoding.symbol⟩

theorem initial_represents [Inhabited Λ] (input : List Γ) :
    Represents encoding (TM0.init input) (initial encoding input) := by
  refine ⟨rfl, ?_, ?_⟩
  · change Tape.mk₂ [] (encoding.symbol input.headI :: input.tail.map encoding.symbol) =
      (Tape.mk₁ input).map encoding.symbol
    rw [Tape.map_mk₁]
    cases input with
    | nil =>
        simp only [List.headI_nil, List.tail_nil, List.map_nil, encoding.symbol.map_pt]
        change Tape.mk₂ [] [0] = Tape.mk₂ [] []
        simp only [Tape.mk₂, listBlank_mk_blank]
    | cons head tail => rfl
  · refine ⟨by simp [initial, List.Forall], ⟨input.headI, rfl⟩, ?_⟩
    apply List.forall_iff_forall_mem.mpr
    intro symbol member
    obtain ⟨value, _, same⟩ := List.mem_map.mp member
    exact ⟨value, same⟩

/-- Every finite alphabet admits a blank-preserving numbering, independently of
how its native `Inhabited` instance chooses the blank. -/
noncomputable def finiteEncoding [Fintype Γ] [Fintype Λ] [Inhabited Λ] : Encoding Γ Λ where
  label := ⟨fun state => Equiv.swap (Fintype.equivFin Λ default).val 0
      (Fintype.equivFin Λ state).val,
    fun _ _ same => (Fintype.equivFin Λ).injective
      (Fin.ext ((Equiv.swap _ _).injective same))⟩
  symbol :=
    { f := fun value => Equiv.swap (Fintype.equivFin Γ default).val 0
        (Fintype.equivFin Γ value).val
      map_pt' := Equiv.swap_apply_left _ _ }
  symbol_injective := fun _ _ same => (Fintype.equivFin Γ).injective
    (Fin.ext ((Equiv.swap _ _).injective same))

@[simp] theorem finiteEncoding_label_default [Fintype Γ] [Fintype Λ] [Inhabited Λ] :
    (finiteEncoding (Γ := Γ) (Λ := Λ)).label default = 0 :=
  Equiv.swap_apply_left _ _

section Simulation

variable [Inhabited Λ] [Fintype Γ] [Fintype Λ]

theorem primary_member (source : TM0.Machine Γ Λ) {state : Λ} {read : Γ}
    {next : Λ} {command : TM0.Stmt Γ} (found : source state read = some (next, command)) :
    primary encoding state read next command ∈ (table encoding source).transitions :=
  (mem_table encoding source _).mpr (Or.inl ⟨state, read, next, command, found, rfl⟩)

theorem restore_member (source : TM0.Machine Γ Λ) (next : Λ) (read : Γ) :
    restore encoding next read ∈ (table encoding source).transitions :=
  (mem_table encoding source _).mpr (Or.inr ⟨next, read, rfl⟩)

theorem next_of_entry (source : TM0.Machine Γ Λ) {configuration : Configuration}
    {entry : Transition} (member : entry ∈ (table encoding source).transitions)
    (applies : entry.Applies configuration) :
    (table encoding source).next? configuration = some (configuration.after entry) :=
  (MathlibBridge.next_some_iff_step _ (deterministic encoding source) _ _).mpr
    (step_term_iff.mpr ⟨entry, member, applies, rfl⟩)

theorem simulate_step (source : TM0.Machine Γ Λ)
    {native next : TM0.Cfg Γ Λ} {configuration : Configuration}
    (represented : Represents encoding native configuration)
    (stepped : TM0.step source native = some next) :
    ∃ target, Represents encoding next target ∧
      StateTransition.Reaches₁ (table encoding source).next? configuration target := by
  cases found : source native.q native.Tape.head with
  | none => simp [TM0.step, found] at stepped
  | some result =>
      obtain ⟨nextState, command⟩ := result
      have scanned := scanned_of_represents encoding represented
      have applies := primary_applies encoding represented nextState command
      have member := primary_member encoding source found
      have firstStep := next_of_entry encoding source member applies
      cases command with
      | move direction =>
          have nextEq : next = ⟨nextState, native.Tape.move direction⟩ := by
            simpa [TM0.step, found] using stepped.symm
          subst next
          let entry := primary encoding native.q native.Tape.head nextState (.move direction)
          refine ⟨configuration.after entry, ⟨?_, ?_, ?_⟩, .single firstStep⟩
          · simp only [MathlibBridge.after_state, entry, primary]
          · rw [Configuration.tape_after]
            simp only [entry, primary, dir_moveOfDir]
            rw [← scanned, ← Configuration.tape_head, Tape.write_self,
              represented.2.1, ← Tape.map_move]
          · exact after_usesAlphabet encoding represented.2.2 entry
              ⟨native.Tape.head, rfl⟩
      | write symbol =>
          have nextEq : next = ⟨nextState, native.Tape.write symbol⟩ := by
            simpa [TM0.step, found] using stepped.symm
          subst next
          let entry := primary encoding native.q native.Tape.head nextState (.write symbol)
          let middle := configuration.after entry
          have middleValid : UsesAlphabet encoding middle :=
            after_usesAlphabet encoding represented.2.2 entry ⟨symbol, rfl⟩
          obtain ⟨neighbour, neighbourEq⟩ := middleValid.2.1
          let returnEntry := restore encoding nextState neighbour
          have returnApplies : returnEntry.Applies middle :=
            ⟨by simp only [returnEntry, restore, middle, MathlibBridge.after_state,
                entry, primary], neighbourEq⟩
          have returnStep := next_of_entry encoding source
            (restore_member encoding source nextState neighbour) returnApplies
          have firstPath : StateTransition.Reaches₁ (table encoding source).next?
              configuration middle := .single firstStep
          refine ⟨middle.after returnEntry, ⟨?_, ?_, ?_⟩, firstPath.tail returnStep⟩
          · simp only [MathlibBridge.after_state, returnEntry, restore]
          · rw [Configuration.tape_after]
            simp only [returnEntry, restore, Move.dir]
            rw [neighbourEq, ← Configuration.tape_head, Tape.write_self]
            dsimp only [middle]
            rw [Configuration.tape_after]
            simp only [entry, primary, Move.dir, Tape.move_right_left]
            rw [represented.2.1, ← Tape.map_write]
          · exact after_usesAlphabet encoding middleValid returnEntry ⟨neighbour, rfl⟩

theorem reflects_halt (source : TM0.Machine Γ Λ)
    {native : TM0.Cfg Γ Λ} {configuration : Configuration}
    (represented : Represents encoding native configuration)
    (halted : TM0.step source native = none) :
    (table encoding source).next? configuration = none := by
  have noRow : source native.q native.Tape.head = none := by
    simpa only [TM0.step, Option.map_eq_none_iff] using halted
  apply (MathlibBridge.next_none_iff_halted _ _).mpr
  apply halted_term_iff.mpr
  intro entry member applies
  rcases (mem_table encoding source entry).mp member with
    ⟨state, read, next, command, found, rfl⟩ | ⟨next, read, rfl⟩
  · have sameState : state = native.q := encoding.label.injective (by
      have stateEq := applies.1
      simp only [primary_state, represented.1] at stateEq
      omega)
    have sameRead : read = native.Tape.head := encoding.symbol_injective (by
      have readEq := applies.2
      simpa only [primary_read, scanned_of_represents encoding represented] using readEq)
    subst state read
    rw [noRow] at found
    contradiction
  · have stateEq := applies.1
    simp only [restore, represented.1] at stateEq
    omega

/-- A write instruction becomes two rows and a move instruction one row.
Every source step is a nonempty finite path; halting is preserved exactly. -/
theorem respects (source : TM0.Machine Γ Λ) :
    StateTransition.Respects (TM0.step source) (table encoding source).next?
      (Represents encoding) := by
  intro native configuration represented
  cases stepped : TM0.step source native with
  | none => exact reflects_halt encoding source represented stepped
  | some next => exact simulate_step encoding source represented stepped

theorem eval_dom_iff (source : TM0.Machine Γ Λ)
    {native : TM0.Cfg Γ Λ} {configuration : Configuration}
    (represented : Represents encoding native configuration) :
    (StateTransition.eval (table encoding source).next? configuration).Dom ↔
      (StateTransition.eval (TM0.step source) native).Dom :=
  StateTransition.tr_eval_dom (respects encoding source) represented

theorem halts_iff (source : TM0.Machine Γ Λ) (input : List Γ) :
    HaltsFrom (table encoding source) (initial encoding input).term ↔
      (TM0.eval source input).Dom := by
  change _ ↔ (StateTransition.eval (TM0.step source) (TM0.init input)).Dom
  rw [← eval_dom_iff encoding source (initial_represents encoding input),
    MathlibBridge.next_eval_dom_iff_halts _ (deterministic encoding source)]

end Simulation

end Mettapedia.Languages.TuringMachine.FinitePostCompiler
