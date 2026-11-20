import Mettapedia.Languages.MeTTa.PeTTa.Resumption
import Mathlib.Data.List.Chain

/-!
# Finite evidence for original PeTTa configurations and execution

Replay follows the existing executable `Eval.step`, whose transition
correspondence is proved against the independent declarative semantics. Exact
budget composition retains every control, continuation, store and I/O field.

Finite snapshots reconstruct the actual named-space prefix and an earned
finite cell support. Dynamic cell writes and allocation preserve that support
through the original dispatcher. Accepted raw steps and finite paths are exact
for the original recursive/effectful transition judgment on represented
configurations; every finite source path has constructed accepted evidence.

Completed public answers are observed as multisets, retaining multiplicity
without imposing a language-wide order. Internal configuration order remains
the original machine's scheduling and effect policy. Success, faults and
unfinished prefixes remain distinct. The earlier read-only reconstruction
lemmas are retained as special cases.

This is an executable-model evidence layer. Parser/native implementation
refinement, a whole Prime dialect adapter and executed resource bounds are
separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program)
open Eval

/-- Retain the actual configuration reached after at most the supplied number
of existing machine transitions. A terminal configuration has no next step. -/
def advance (program : Program) : Nat → Configuration → Configuration
  | 0, configuration => configuration
  | fuel + 1, configuration =>
      match step program configuration with
      | none => configuration
      | some next => advance program fuel next

theorem advance_stopped (program : Program) (fuel : Nat) (configuration : Configuration)
    (stopped : step program configuration = none) :
    advance program fuel configuration = configuration := by
  cases fuel <;> simp [advance, stopped]

/-- The observer does not replace the evaluator: its readout agrees with the
actual fuel runner for completion, exhaustion and primitive faults. -/
theorem run_advance (program : Program) (fuel : Nat) (configuration : Configuration) :
    run program 0 (advance program fuel configuration) = run program fuel configuration := by
  induction fuel generalizing configuration with
  | zero => rfl
  | succ fuel ih =>
      cases next : step program configuration with
      | some target =>
          simp only [advance, next]
          exact (ih target).trans (run_succ_of_step program fuel configuration target next).symm
      | none =>
          simp only [advance, next]
          cases configuration with
          | mk state control frames input output =>
              cases control <;> cases frames <;> simp_all [run]

theorem advance_split (program : Program) (first second : Nat) (configuration : Configuration) :
    advance program second (advance program first configuration) =
      advance program (first + second) configuration := by
  induction first generalizing configuration with
  | zero => simp [advance]
  | succ first ih =>
      cases next : step program configuration with
      | none =>
          rw [advance_stopped program (first + 1) configuration next,
            advance_stopped program second configuration next,
            advance_stopped program (first + 1 + second) configuration next]
      | some target => simpa [advance, next, Nat.succ_add] using ih target

def checkpoints (program : Program) : List Nat → Configuration → List Configuration
  | [], _ => []
  | fuel :: rest, configuration =>
      let reached := advance program fuel configuration
      reached :: checkpoints program rest reached

def chunks (program : Program) : List Nat → Configuration → Configuration
  | [], configuration => configuration
  | fuel :: rest, configuration => chunks program rest (advance program fuel configuration)

theorem chunks_eq_advance_sum (program : Program) (fuels : List Nat) (configuration : Configuration) :
    chunks program fuels configuration = advance program fuels.sum configuration := by
  induction fuels generalizing configuration with
  | nil => rfl
  | cons fuel rest ih =>
      rw [chunks, ih, advance_split]
      rfl

def resumeChunks (program : Program) : List Nat → Outcome → Outcome
  | [], outcome => outcome
  | fuel :: rest, outcome => resumeChunks program rest (resume program fuel outcome)

theorem resumeChunks_run (program : Program) (fuels : List Nat) (paid : Nat)
    (configuration : Configuration) :
    resumeChunks program fuels (run program paid configuration) =
      run program (paid + fuels.sum) configuration := by
  induction fuels generalizing paid with
  | nil => simp [resumeChunks]
  | cons fuel rest ih =>
      rw [resumeChunks, resume_run, ih]
      simp [Nat.add_assoc]

theorem chunks_readout (program : Program) (fuels : List Nat) (configuration : Configuration) :
    run program 0 (chunks program fuels configuration) =
      resumeChunks program fuels (run program 0 configuration) := by
  rw [chunks_eq_advance_sum, run_advance, resumeChunks_run, Nat.zero_add]

theorem advance_path (program : Program) (fuel : Nat) (configuration : Configuration) :
    (theory program).MultiStep configuration (advance program fuel configuration) := by
  induction fuel generalizing configuration with
  | zero => exact .refl _
  | succ fuel ih =>
      cases next : step program configuration with
      | none =>
          simp only [advance, next]
          exact .refl _
      | some target =>
          exact .step (step_transition next) (by simpa [advance, next] using ih target)

/-- Only the four state-mutating primitives can alter the loaded store.
Dynamic source execution and parsing are also excluded from this profile. -/
def readOnlyHead (head : String) : Bool :=
  !(head ∈ ["new-space", "add-atom", "remove-atom", "change-state!", "eval", "parse", "readln!"])

theorem primitive_preserves_state {state after : Effects.State} {head : String}
    {arguments answers : List Atom} (allowed : readOnlyHead head = true)
    (returned : StdLib.apply state head arguments = .ok (after, answers)) : after = state := by
  have notNew : head ≠ "new-space" := by
    intro same
    have forbidden : readOnlyHead head = false := by rw [same]; decide
    exact Bool.noConfusion (allowed.symm.trans forbidden)
  have notAdd : head ≠ "add-atom" := by
    intro same
    have forbidden : readOnlyHead head = false := by rw [same]; decide
    exact Bool.noConfusion (allowed.symm.trans forbidden)
  have notRemove : head ≠ "remove-atom" := by
    intro same
    have forbidden : readOnlyHead head = false := by rw [same]; decide
    exact Bool.noConfusion (allowed.symm.trans forbidden)
  have notChange : head ≠ "change-state!" := by
    intro same
    have forbidden : readOnlyHead head = false := by rw [same]; decide
    exact Bool.noConfusion (allowed.symm.trans forbidden)
  exact StdLib.successful_apply_state notNew notAdd notRemove notChange returned

def readOnlyProgram (program : Program) : Bool :=
  program.equations.all (fun equation => codeWithin readOnlyHead equation.body)

theorem checked_program_closed (program : Program) (checked : readOnlyProgram program = true) :
    ProgramClosed readOnlyHead program := by
  constructor
  · decide
  · intro equation member _
    exact List.all_eq_true.mp checked equation member

theorem transition_preserves_state {program : Program} {source target : Configuration}
    (within : configurationWithin readOnlyHead source)
    (transition : DeclarativeSpec.Transition program source target) :
    target.state = source.state := by
  cases transition
  all_goals try rfl
  rename_i bindings head index values after answers control _ _ returned
  have allowed := within.1
  rw [control] at allowed
  simp only [controlWithin, targetWithin, atomsWithin, Bool.and_true,
    Bool.and_eq_true] at allowed
  exact primitive_preserves_state allowed.1 returned

theorem advance_preserves_state (program : Program) (fuel : Nat) (source : Configuration)
    (closed : ProgramClosed readOnlyHead program)
    (within : configurationWithin readOnlyHead source) :
    (advance program fuel source).state = source.state := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
      cases next : step program source with
      | none => simp [advance, next]
      | some target =>
          have transition := step_transition next
          simpa only [advance, next] using
            (ih target (transition_within closed transition within)).trans
              (transition_preserves_state within transition)

theorem chunks_preserve_state (program : Program) (fuels : List Nat) (source : Configuration)
    (closed : ProgramClosed readOnlyHead program)
    (within : configurationWithin readOnlyHead source) :
    (chunks program fuels source).state = source.state := by
  rw [chunks_eq_advance_sum]
  exact advance_preserves_state program fuels.sum source closed within

/-- Finite readout reconstructs all store fields, including the entire
unallocated private-space tail and every absent named cell. -/
theorem loaded_store_reconstruction (program : Program) :
    NamedSpaces.Store.reconstruct (Effects.loaded program).core []
      (Effects.loaded program).spacesPrefix ((Effects.loaded program).cellRows [])
        (Effects.loaded program).namedSpaces (Effects.loaded program).namedEmpty =
      Effects.loaded program := by
  apply NamedSpaces.Store.reconstruct_exact
  · exact Effects.loaded_empty_tail program
  · intro _ _
    rfl

theorem chunks_loaded_store_reconstruction (program : Program) (fuels : List Nat)
    (expression : Atom) (input : List Atom)
    (checked : readOnlyProgram program = true)
    (code : codeWithin readOnlyHead expression = true) :
    let initial : Configuration :=
      { state := Effects.loaded program
        control := .evaluate [] expression
        input }
    let reached := chunks program fuels initial
    NamedSpaces.Store.reconstruct reached.state.core [] reached.state.spacesPrefix
      (reached.state.cellRows []) reached.state.namedSpaces reached.state.namedEmpty = reached.state := by
  dsimp only
  have same := chunks_preserve_state program fuels
    { state := Effects.loaded program, control := .evaluate [] expression, input }
    (checked_program_closed program checked) ⟨code, rfl⟩
  rw [same]
  exact loaded_store_reconstruction program

namespace Examples

def program : Program :=
  { equations := [{ head := "dup", arguments := [.var "x"], body := .var "x" },
                  { head := "dup", arguments := [.var "x"], body := .var "x" }]
    declarations := []
    layout := [.equation, .equation] }

def seven : Atom := .grounded (.int 7)

def call : Atom := .expression [.symbol "dup", seven]

def answerView : Outcome → Option (List Atom)
  | .complete _ answers _ _ => some answers
  | _ => none

def faultView : Outcome → Option Effects.Fault
  | .fault reason _ => some reason
  | _ => none

theorem authored_equation_atoms_retained :
    SpaceSemantics.loadedAtoms program =
      [.expression [.symbol "=", .expression [.symbol "dup", .var "x"], .var "x"],
       .expression [.symbol "=", .expression [.symbol "dup", .var "x"], .var "x"]] := by
  rfl

theorem authored_program_admitted : readOnlyProgram program = true := by decide

theorem duplicate_answers_retained :
    answerView (run program 15 (start (Effects.loaded program) call)) =
      some [seven, seven] := by
  rw [← run_advance]
  with_unfolding_all rfl

def correlated : Atom := .expression
  [.symbol "let", .var "held", seven,
   .expression [.symbol "superpose", .expression [.var "held", .var "held"]]]

theorem binding_frame_retained :
    (advance program 2 (start (Effects.loaded program) correlated)).frames =
      [.bind [] (.var "held")
        (.expression [.symbol "superpose", .expression [.var "held", .var "held"]])] := by rfl

theorem correlated_answers_after_chunks :
    answerView (run program 0 (chunks program [0, 2, 12] (start (Effects.loaded program) correlated))) =
      some [seven, seven] := by decide +kernel

def message : Atom := .grounded (.string "once")

def effectThenFault : Atom := .expression
  [.symbol "let", .var "ignored", .expression [.symbol "println!", message],
   .expression [.symbol "%", seven, .grounded (.int 0)]]

theorem output_before_pause :
    (advance program 7 (start (Effects.loaded program) effectThenFault)).output = [message] := by rfl

theorem output_before_fault_retained :
    (chunks program [7, 10] (start (Effects.loaded program) effectThenFault)).output = [message] := by
  decide +kernel

theorem terminal_fault_distinct_from_exhaustion :
    faultView (run program 0 (chunks program [7, 14] (start (Effects.loaded program) effectThenFault))) =
      some .zeroDivisor := by with_unfolding_all rfl

theorem erasing_performed_output_changes_configuration :
    (advance program 7 (start (Effects.loaded program) effectThenFault)).output ≠ [] := by
  decide +kernel

def batching : Configuration :=
  { state := Effects.loaded program
    control := .sequence
      [.arguments [] (.function "println!") [] [.symbol "a"] 1,
       .arguments [] (.function "println!") [] [.symbol "b"] 1] []
    frames := [.bind [] (.var "held") (.expression [.symbol "println!", .var "held"])] }

/-- The existing list-valued machine completes inner alternatives before the
binding continuation executes. The native source oracle tests that boundary. -/
theorem sequence_delays_binding_continuation :
    (advance program 5 batching).output = [.symbol "a", .symbol "b"] := by rfl

theorem sequence_prefix_is_not_interleaved :
    (advance program 5 batching).output ≠ [.symbol "a", Effects.boolean true] := by
  decide +kernel

theorem mutable_heads_refused :
    readOnlyHead "new-space" = false ∧ readOnlyHead "add-atom" = false ∧
      readOnlyHead "remove-atom" = false ∧ readOnlyHead "change-state!" = false := by decide

theorem dynamic_heads_refused :
    readOnlyHead "eval" = false ∧ readOnlyHead "parse" = false ∧ readOnlyHead "readln!" = false := by
  decide

end Examples


/-! ## Dynamic support for the original effectful machine -/

/-- Only the actual cell-writing dispatch form can introduce a cell name.
The value and the state update still come from the original dispatcher. -/
def introducedCell (configuration : Configuration) : Option String :=
  match configuration.control with
  | .arguments _ (.function "change-state!") [] [.symbol name, _] _ => some name
  | _ => none

def supportAfter (names : List String) (configuration : Configuration) : List String :=
  (introducedCell configuration).toList ++ names

theorem supportAfter_contains_old (names : List String) (configuration : Configuration)
    (name : String) (member : name ∈ names) : name ∈ supportAfter names configuration := by
  simp [supportAfter, member]

/-- Every primitive step earns the support update from the source dispatcher
and the existing store frame laws. No purity or read-only guard is assumed. -/
theorem transition_cell_support {program : Program} {source target : Configuration}
    (names : List String)
    (covers : ∀ name, name ∉ names → source.state.cells name = none)
    (transition : DeclarativeSpec.Transition program source target) :
    ∀ name, name ∉ supportAfter names source → target.state.cells name = none := by
  have preserved : ∀ name, name ∉ supportAfter names source → source.state.cells name = none := by
    intro name absent
    exact covers name (fun member => absent (supportAfter_contains_old names source name member))
  cases transition
  all_goals first
    | exact preserved
    | skip
  case primitive bindings head index values answers after control ordinary native result =>
    rcases StdLib.successful_apply_cell_update result with same | ⟨name, value, headEq, valuesEq, afterEq⟩
    · intro other absent
      rw [same]
      exact preserved other absent
    · subst head
      subst values
      subst after
      intro other absent
      have different : other ≠ name := by
        intro equal
        subst other
        apply absent
        simp [supportAfter, introducedCell, control]
      rw [NamedSpaces.Store.cell_read_other _ name other value different]
      exact preserved other absent

/-- Advance the existing machine while retaining a finite name support for
its reached state. This observer does not define any evaluation rule. -/
def advanceSupported (program : Program) : Nat → List String → Configuration →
    List String × Configuration
  | 0, names, configuration => (names, configuration)
  | fuel + 1, names, configuration =>
      match step program configuration with
      | none => (names, configuration)
      | some next => advanceSupported program fuel (supportAfter names configuration) next

theorem advanceSupported_configuration (program : Program) (fuel : Nat)
    (names : List String) (configuration : Configuration) :
    (advanceSupported program fuel names configuration).2 = advance program fuel configuration := by
  induction fuel generalizing names configuration with
  | zero => rfl
  | succ fuel ih =>
    cases next : step program configuration with
    | none => simp [advanceSupported, advance, next]
    | some target => simpa [advanceSupported, advance, next] using ih (supportAfter names configuration) target

theorem advanceSupported_cell_support (program : Program) (fuel : Nat)
    (names : List String) (configuration : Configuration)
    (covers : ∀ name, name ∉ names → configuration.state.cells name = none) :
    ∀ name, name ∉ (advanceSupported program fuel names configuration).1 →
      (advanceSupported program fuel names configuration).2.state.cells name = none := by
  induction fuel generalizing names configuration with
  | zero => exact covers
  | succ fuel ih =>
    cases next : step program configuration with
    | none => simpa [advanceSupported, next] using covers
    | some target =>
      simpa [advanceSupported, next] using ih (supportAfter names configuration) target
        (transition_cell_support names covers (step_transition next))

theorem advanceSupported_empty_tail (program : Program) (fuel : Nat)
    (names : List String) (configuration : Configuration)
    (vacant : NamedSpaces.Store.EmptyTail configuration.state []) :
    NamedSpaces.Store.EmptyTail
      (advanceSupported program fuel names configuration).2.state [] := by
  induction fuel generalizing names configuration with
  | zero => exact vacant
  | succ fuel ih =>
    cases next : step program configuration with
    | none => simpa [advanceSupported, next] using vacant
    | some target =>
      simpa [advanceSupported, next] using ih (supportAfter names configuration) target
        (DeclarativeSpec.transition_empty_tail vacant (step_transition next))

theorem advanceSupported_stopped (program : Program) (fuel : Nat) (names : List String)
    (configuration : Configuration) (stopped : step program configuration = none) :
    advanceSupported program fuel names configuration = (names, configuration) := by
  cases fuel <;> simp [advanceSupported, stopped]

/-- Pausing and resuming composes both the exact reached configuration and
the dynamically earned finite support. Nothing is replayed or skipped. -/
theorem advanceSupported_split (program : Program) (first second : Nat)
    (names : List String) (configuration : Configuration) :
    let reached := advanceSupported program first names configuration
    advanceSupported program second reached.1 reached.2 =
      advanceSupported program (first + second) names configuration := by
  induction first generalizing names configuration with
  | zero => simp [advanceSupported]
  | succ first ih =>
    dsimp only
    cases next : step program configuration with
    | none => simp [advanceSupported_stopped program _ _ _ next]
    | some target =>
      simpa [advanceSupported, next, Nat.succ_add] using
        (ih (supportAfter names configuration) target)


/-! ## Finite physical configurations and exact store reconstruction -/

deriving instance DecidableEq for Target
mutual
private def controlDecEq : (first second : Control) → Decidable (first = second)
  | .evaluate bindings expression, .evaluate otherBindings otherExpression =>
      if same : bindings = otherBindings ∧ expression = otherExpression then
        isTrue (by obtain ⟨rfl, rfl⟩ := same; rfl)
      else isFalse (by intro equal; cases equal; exact same ⟨rfl, rfl⟩)
  | .arguments bindings target remaining values index,
      .arguments otherBindings otherTarget otherRemaining otherValues otherIndex =>
      if same : bindings = otherBindings ∧ target = otherTarget ∧
          remaining = otherRemaining ∧ values = otherValues ∧ index = otherIndex then
        isTrue (by obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := same; rfl)
      else isFalse (by intro equal; cases equal; exact same ⟨rfl, rfl, rfl, rfl, rfl⟩)
  | .sequence remaining answers, .sequence otherRemaining otherAnswers =>
      match controlsDecEq remaining otherRemaining with
      | isFalse different => isFalse (by intro equal; exact different (Control.sequence.inj equal).1)
      | isTrue sameRemaining =>
          if sameAnswers : answers = otherAnswers then
            isTrue (by rw [sameRemaining, sameAnswers])
          else isFalse (by intro equal; exact sameAnswers (Control.sequence.inj equal).2)
  | .returned answers, .returned otherAnswers =>
      if same : answers = otherAnswers then isTrue (by rw [same])
      else isFalse (by intro equal; exact same (Control.returned.inj equal))
  | .fault reason, .fault otherReason =>
      if same : reason = otherReason then isTrue (by rw [same])
      else isFalse (by intro equal; exact same (Control.fault.inj equal))
  | .evaluate _ _, .arguments _ _ _ _ _
  | .evaluate _ _, .sequence _ _
  | .evaluate _ _, .returned _
  | .evaluate _ _, .fault _
  | .arguments _ _ _ _ _, .evaluate _ _
  | .arguments _ _ _ _ _, .sequence _ _
  | .arguments _ _ _ _ _, .returned _
  | .arguments _ _ _ _ _, .fault _
  | .sequence _ _, .evaluate _ _
  | .sequence _ _, .arguments _ _ _ _ _
  | .sequence _ _, .returned _
  | .sequence _ _, .fault _
  | .returned _, .evaluate _ _
  | .returned _, .arguments _ _ _ _ _
  | .returned _, .sequence _ _
  | .returned _, .fault _
  | .fault _, .evaluate _ _
  | .fault _, .arguments _ _ _ _ _
  | .fault _, .sequence _ _
  | .fault _, .returned _ => isFalse (by intro equal; cases equal)
termination_by first _ => sizeOf first

private def controlsDecEq : (first second : List Control) → Decidable (first = second)
  | [], [] => isTrue rfl
  | [], _ :: _ | _ :: _, [] => isFalse (by intro equal; cases equal)
  | first :: rest, second :: others =>
      match controlDecEq first second with
      | isFalse different => isFalse (by intro equal; exact different (List.cons.inj equal).1)
      | isTrue sameFirst =>
          match controlsDecEq rest others with
          | isFalse different => isFalse (by intro equal; exact different (List.cons.inj equal).2)
          | isTrue sameRest => isTrue (by rw [sameFirst, sameRest])
termination_by first _ => sizeOf first
end

instance : DecidableEq Control := controlDecEq

deriving instance DecidableEq for Frame

/-- Finite evidence stores actual Atom rows, allocated private spaces and
named cells. Source control, continuations, remaining input and performed
output retain their existing carriers. This is a representation of the
original machine configuration, not another source machine. -/
structure Snapshot where
  core : List Atom
  spaces : List (List Atom)
  cells : List (String × Option Atom)
  control : Control
  frames : List Frame
  input : List Atom
  output : List Atom
  namedSpaces : List (String × List Atom) := []
  namedEmpty : List Atom := []
deriving Repr, DecidableEq

namespace Snapshot

/-- The existing generic store reconstruction supplies every function field. -/
def decode (snapshot : Snapshot) : Configuration :=
  { state := NamedSpaces.Store.reconstruct snapshot.core [] snapshot.spaces snapshot.cells
      snapshot.namedSpaces snapshot.namedEmpty
    control := snapshot.control
    frames := snapshot.frames
    input := snapshot.input
    output := snapshot.output }

def cellNames (snapshot : Snapshot) : List String := snapshot.cells.map Prod.fst

theorem decode_cell_support (snapshot : Snapshot) :
    ∀ name, name ∉ snapshot.cellNames → snapshot.decode.state.cells name = none := by
  intro name absent
  change ((snapshot.cells.lookup name).join) = none
  have missing : snapshot.cells.lookup name = none := by
    apply List.lookup_eq_none_iff.mpr
    intro entry member
    have different : name ≠ entry.1 := by
      intro equal
      exact absent (List.mem_map.mpr ⟨entry, member, equal.symm⟩)
    simpa only [bne_iff_ne] using different
  simp [missing]

theorem decode_empty_tail (snapshot : Snapshot) :
    NamedSpaces.Store.EmptyTail snapshot.decode.state [] := by
  intro index outside
  change snapshot.spaces.length ≤ index at outside
  change (snapshot.spaces[index]?).getD [] = []
  rw [List.getElem?_eq_none (by omega)]
  rfl

end Snapshot

/-- Read finite rows and the dynamically retained cell support from the
actual reached configuration. -/
def snapshot (names : List String) (configuration : Configuration) : Snapshot :=
  { core := configuration.state.core
    spaces := configuration.state.spacesPrefix
    cells := configuration.state.cellRows names
    control := configuration.control
    frames := configuration.frames
    input := configuration.input
    output := configuration.output
    namedSpaces := configuration.state.namedSpaces
    namedEmpty := configuration.state.namedEmpty }

/-- Every retained cell and the entire allocated/unallocated space function
are reconstructed. This law includes effectful configurations and faults. -/
theorem snapshot_decode (names : List String) (configuration : Configuration)
    (covers : ∀ name, name ∉ names → configuration.state.cells name = none)
    (vacant : NamedSpaces.Store.EmptyTail configuration.state []) :
    (snapshot names configuration).decode = configuration := by
  have stateExact := NamedSpaces.Store.reconstruct_exact configuration.state [] names vacant covers
  cases configuration with
  | mk state control frames input output =>
    simp only [snapshot, Snapshot.decode] at *
    rw [stateExact]

/-- The native observer records the actual effectful run after the requested
budget, including completion, fault and unfinished continuation states. -/
def retainedSnapshot (program : Program) (fuel : Nat) (initial : Snapshot) : Snapshot :=
  let reached := advanceSupported program fuel initial.cellNames initial.decode
  snapshot reached.1 reached.2

/-- Every retained snapshot denotes exactly the original reached machine
configuration; no purity hypothesis is used. -/
theorem retainedSnapshot_decode (program : Program) (fuel : Nat) (initial : Snapshot) :
    (retainedSnapshot program fuel initial).decode = advance program fuel initial.decode := by
  unfold retainedSnapshot
  rw [snapshot_decode _ _
    (advanceSupported_cell_support program fuel initial.cellNames initial.decode initial.decode_cell_support)
    (advanceSupported_empty_tail program fuel initial.cellNames initial.decode initial.decode_empty_tail)]
  exact advanceSupported_configuration program fuel initial.cellNames initial.decode

/-- Exact original run observations for every finite budget, including stores
changed before a fault or an exhausted continuation. -/
theorem retainedSnapshot_run (program : Program) (fuel : Nat) (initial : Snapshot) :
    run program 0 (retainedSnapshot program fuel initial).decode =
      run program fuel initial.decode := by
  rw [retainedSnapshot_decode, run_advance]

/-- Splitting a budget preserves the entire decoded state and continuation.
Physical support lists may contain harmless redundant keys, so this is exact
configuration equality rather than an invented canonical row ordering. -/
theorem retainedSnapshot_split (program : Program) (first second : Nat) (initial : Snapshot) :
    (retainedSnapshot program second (retainedSnapshot program first initial)).decode =
      (retainedSnapshot program (first + second) initial).decode := by
  rw [retainedSnapshot_decode, retainedSnapshot_decode,
    retainedSnapshot_decode, advance_split]


namespace Snapshot

@[simp] theorem decode_spacesPrefix (packet : Snapshot) :
    packet.decode.state.spacesPrefix = packet.spaces := by
  apply List.ext_getElem?
  intro index
  rw [← NamedSpaces.Store.read_private_from_prefix]
  simp only [decode, NamedSpaces.Store.reconstruct, NamedSpaces.Store.read]
  by_cases bounded : index < packet.spaces.length
  · simp [bounded]
  · simp [bounded]

/-- Physical tables are compared by their complete finite lookup meaning.
Neither reordered support rows nor redundant absent-cell rows alter the
represented store. Control, continuation and I/O fields remain exact. -/
def Equivalent (first second : Snapshot) : Prop :=
  first.core = second.core ∧ first.spaces = second.spaces ∧
    first.control = second.control ∧ first.frames = second.frames ∧
    first.input = second.input ∧ first.output = second.output ∧
    first.namedSpaces = second.namedSpaces ∧ first.namedEmpty = second.namedEmpty ∧
    ∀ name ∈ first.cellNames ++ second.cellNames,
      (first.cells.lookup name).join = (second.cells.lookup name).join

instance (first second : Snapshot) : Decidable (Equivalent first second) := by
  unfold Equivalent
  infer_instance

/-- This finite comparison is equality of the entire original configuration,
including all cells and unallocated space slots; no function equality
algorithm is assumed. -/
theorem equivalent_iff_decode (first second : Snapshot) :
    Equivalent first second ↔ first.decode = second.decode := by
  constructor
  · rintro ⟨core, spaces, control, frames, input, output, namedRows, namedEmpty, cells⟩
    have cellsEqual : first.decode.state.cells = second.decode.state.cells := by
      funext name
      by_cases member : name ∈ first.cellNames ++ second.cellNames
      · exact cells name member
      · have missingFirst : name ∉ first.cellNames := by simp_all
        have missingSecond : name ∉ second.cellNames := by simp_all
        rw [first.decode_cell_support name missingFirst,
          second.decode_cell_support name missingSecond]
    simp only [decode, Configuration.mk.injEq]
    refine ⟨?_, control, frames, input, output⟩
    simp only [NamedSpaces.Store.reconstruct, NamedSpaces.Store.mk.injEq]
    exact ⟨core, congrArg List.length spaces, by simp [spaces], cellsEqual, namedRows, namedEmpty⟩
  · intro equal
    refine ⟨congrArg (fun c : Configuration => c.state.core) equal, ?_,
      congrArg Configuration.control equal, congrArg Configuration.frames equal,
      congrArg Configuration.input equal, congrArg Configuration.output equal,
      congrArg (fun c : Configuration => c.state.namedSpaces) equal,
      congrArg (fun c : Configuration => c.state.namedEmpty) equal, ?_⟩
    · have actual := congrArg (fun c : Configuration => c.state.spacesPrefix) equal
      simpa using actual
    · intro name _
      exact congrArg (fun c : Configuration => c.state.cells name) equal

def same (first second : Snapshot) : Bool := decide (Equivalent first second)

@[simp] theorem same_exact (first second : Snapshot) :
    same first second = true ↔ first.decode = second.decode := by
  simp only [same, decide_eq_true_eq, equivalent_iff_decode]

end Snapshot

/-- One original executable transition, reified into finite physical fields.
The only observer computation beyond the original step is retaining its
actual finite support and reading finite store prefixes. -/
def nativeStep (program : Program) (source : Snapshot) : Option Snapshot :=
  match step program source.decode with
  | none => none
  | some target => some (snapshot (supportAfter source.cellNames source.decode) target)

theorem nativeStep_of_transition (program : Program) (source : Snapshot)
    (target : Configuration) (transition : DeclarativeSpec.Transition program source.decode target) :
    nativeStep program source =
        some (snapshot (supportAfter source.cellNames source.decode) target) ∧
      (snapshot (supportAfter source.cellNames source.decode) target).decode = target := by
  have actual := transition_step transition
  refine ⟨by simp [nativeStep, actual], ?_⟩
  exact snapshot_decode _ target
    (transition_cell_support source.cellNames source.decode_cell_support transition)
    (DeclarativeSpec.transition_empty_tail source.decode_empty_tail transition)

theorem nativeStep_sound (program : Program) (source target : Snapshot)
    (computed : nativeStep program source = some target) :
    DeclarativeSpec.Transition program source.decode target.decode := by
  cases actual : step program source.decode with
  | none => simp [nativeStep, actual] at computed
  | some next =>
    have sourceStep := step_transition actual
    have readback := (nativeStep_of_transition program source next sourceStep).2
    have selected : snapshot (supportAfter source.cellNames source.decode) next = target := by
      simpa [nativeStep, actual] using computed
    rw [← selected, readback]
    exact sourceStep

/-- The raw endpoint checker observes decoded source meaning, so physically
different finite representations are accepted exactly when the independent
original transition relates them. -/
def checkStep (program : Program) (source target : Snapshot) : Bool :=
  match nativeStep program source with
  | none => false
  | some actual => actual.same target

theorem checkStep_exact (program : Program) (source target : Snapshot) :
    checkStep program source target = true ↔
      DeclarativeSpec.Transition program source.decode target.decode := by
  constructor
  · intro accepted
    cases actual : nativeStep program source with
    | none => simp [checkStep, actual] at accepted
    | some emitted =>
      have equal : emitted.decode = target.decode := by
        exact (Snapshot.same_exact emitted target).mp (by simpa [checkStep, actual] using accepted)
      rw [← equal]
      exact nativeStep_sound program source emitted actual
  · intro transition
    obtain ⟨actual, readback⟩ := nativeStep_of_transition program source target.decode transition
    simp only [checkStep, actual, Snapshot.same_exact, readback]


/-! ## Explicit finite evidence for the whole original transition judgment -/

def checkTrace (program : Program) : Snapshot → List Snapshot → Bool
  | _, [] => true
  | source, target :: rest => checkStep program source target && checkTrace program target rest

/-- Raw trace acceptance is exactly the independently defined source
transition chain. Every stored snapshot occurrence is retained. -/
theorem checkTrace_exact (program : Program) (source : Snapshot) (trace : List Snapshot) :
    checkTrace program source trace = true ↔
      List.IsChain (DeclarativeSpec.Transition program)
        (source.decode :: trace.map Snapshot.decode) := by
  induction trace generalizing source with
  | nil => simp [checkTrace]
  | cons target rest ih =>
    simp only [checkTrace, Bool.and_eq_true, List.map_cons,
      List.isChain_cons_cons, checkStep_exact, ih]

def traceEnd : Snapshot → List Snapshot → Snapshot
  | source, [] => source
  | _, target :: rest => traceEnd target rest

theorem checkedTrace_path (program : Program) (source : Snapshot) (trace : List Snapshot)
    (checked : checkTrace program source trace = true) :
    (theory program).MultiStep source.decode (traceEnd source trace).decode := by
  induction trace generalizing source with
  | nil => exact .refl _
  | cons target rest ih =>
    simp only [checkTrace, Bool.and_eq_true] at checked
    obtain ⟨head, tail⟩ := checked
    exact .step ((checkStep_exact program source target).mp head) (ih target tail)

/-- The trace producer follows only the original transition implementation.
Budget exhaustion leaves a finite prefix rather than claiming absence. -/
def emitTrace (program : Program) : Nat → Snapshot → List Snapshot
  | 0, _ => []
  | fuel + 1, source =>
      match nativeStep program source with
      | none => []
      | some target => target :: emitTrace program fuel target

theorem emitTrace_checked (program : Program) (fuel : Nat) (source : Snapshot) :
    checkTrace program source (emitTrace program fuel source) = true := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
    cases next : nativeStep program source with
    | none => simp [emitTrace, next, checkTrace]
    | some target =>
      have head := (checkStep_exact program source target).mpr
        (nativeStep_sound program source target next)
      simp [emitTrace, next, checkTrace, head, ih]

theorem emitTrace_length (program : Program) (fuel : Nat) (source : Snapshot) :
    (emitTrace program fuel source).length ≤ fuel := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
    cases next : nativeStep program source with
    | none => simp [emitTrace, next]
    | some target => simpa [emitTrace, next] using Nat.succ_le_succ (ih target)

theorem nativeStep_eq_none_iff (program : Program) (source : Snapshot) :
    nativeStep program source = none ↔ step program source.decode = none := by
  cases next : step program source.decode <;> simp [nativeStep, next]

/-- The emitted proof's endpoint is the original exact budgeted endpoint,
including a changed store or unfinished continuation. -/
theorem emitTrace_endpoint (program : Program) (fuel : Nat) (source : Snapshot) :
    (traceEnd source (emitTrace program fuel source)).decode =
      advance program fuel source.decode := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
    cases next : nativeStep program source with
    | none =>
      have stopped := (nativeStep_eq_none_iff program source).mp next
      simp [emitTrace, next, traceEnd, advance, stopped]
    | some target =>
      have actual := transition_step (nativeStep_sound program source target next)
      simpa [emitTrace, next, traceEnd, advance, actual] using ih target

/-- Completion, primitive fault and unfinished readout are all the original
fuelled machine's outcomes. Native snapshotting supplies no new theorem. -/
theorem emitTrace_readout (program : Program) (fuel : Nat) (source : Snapshot) :
    run program 0 (traceEnd source (emitTrace program fuel source)).decode =
      run program fuel source.decode := by
  rw [emitTrace_endpoint, run_advance]

/-- Every finite independently specified successful or faulting source run
has a constructed accepted trace. This covers recursive equation execution
and supported state effects, not just the read-only source fragment. -/
theorem source_run_has_checked_trace (program : Program) (source : Snapshot)
    (result : Outcome) (derivation : DeclarativeSpec.Runs program source.decode result) :
    ∃ trace, checkTrace program source trace = true ∧
      run program 0 (traceEnd source trace).decode = result := by
  obtain ⟨fuel, actual⟩ := derivation_has_run derivation
  exact ⟨emitTrace program fuel source, emitTrace_checked program fuel source,
    (emitTrace_readout program fuel source).trans actual⟩


/-- Every original finite source path from a represented configuration has
finite checked evidence. Intermediate configurations are constructed from
the actual source transitions and their earned dynamic support. -/
theorem path_has_checked_trace (program : Program) {source target : Configuration}
    (path : (theory program).MultiStep source target) :
    ∀ initial : Snapshot, initial.decode = source →
      ∃ trace, checkTrace program initial trace = true ∧
        (traceEnd initial trace).decode = target := by
  have lift {system : Mettapedia.GSLT.GSLT}
      {property : system.Term → system.Term → Prop}
      (atSelf : ∀ term, property term term)
      (prepend : ∀ {first middle last}, system.Step first middle →
        property middle last → property first last)
      {first last} (steps : system.MultiStep first last) : property first last := by
    induction steps with
    | refl term => exact atSelf term
    | step transition _ ih => exact prepend transition ih
  apply lift (system := theory program)
    (property := fun first last => ∀ initial : Snapshot, initial.decode = first →
      ∃ trace, checkTrace program initial trace = true ∧
        (traceEnd initial trace).decode = last)
    (steps := path)
  · intro configuration initial represents
    exact ⟨[], rfl, represents⟩
  · intro first middle last transition ih initial represents
    change DeclarativeSpec.Transition program first middle at transition
    have actual : DeclarativeSpec.Transition program initial.decode middle := by
      rw [represents]
      exact transition
    let next := snapshot (supportAfter initial.cellNames initial.decode) middle
    obtain ⟨_, readback⟩ := nativeStep_of_transition program initial middle actual
    have nextReadback : next.decode = middle := readback
    obtain ⟨tail, checkedTail, endpoint⟩ := ih next nextReadback
    have checkedHead := (checkStep_exact program initial next).mpr
      (by rw [nextReadback]; exact actual)
    exact ⟨next :: tail, by simp [checkTrace, checkedHead, checkedTail], endpoint⟩

/-- The endpoint is part of the checked judgment. Its raw representation may
vary, but its whole original configuration must agree. -/
def checkPath (program : Program) (source target : Snapshot) (trace : List Snapshot) : Bool :=
  checkTrace program source trace && (traceEnd source trace).same target

theorem checkPath_exact (program : Program) (source target : Snapshot) (trace : List Snapshot) :
    checkPath program source target trace = true ↔
      List.IsChain (DeclarativeSpec.Transition program)
        (source.decode :: trace.map Snapshot.decode) ∧
      (traceEnd source trace).decode = target.decode := by
  simp only [checkPath, Bool.and_eq_true, checkTrace_exact, Snapshot.same_exact]

/-- Acceptance has exactly original finite source reachability as its
existential closure. No equation-only, read-only or termination assumption
replaces the original recursive/effectful transition judgment. -/
theorem accepted_path_iff_source_reachable (program : Program) (source target : Snapshot) :
    (∃ trace, checkPath program source target trace = true) ↔
      (theory program).MultiStep source.decode target.decode := by
  constructor
  · rintro ⟨trace, accepted⟩
    have both : checkTrace program source trace = true ∧
        (traceEnd source trace).decode = target.decode := by
      simpa only [checkPath, Bool.and_eq_true, Snapshot.same_exact] using accepted
    rw [← both.2]
    exact checkedTrace_path program source trace both.1
  · intro path
    obtain ⟨trace, accepted, endpoint⟩ := path_has_checked_trace program path source rfl
    exact ⟨trace, by simp only [checkPath, accepted, Bool.true_and, Snapshot.same_exact, endpoint]⟩


/-- Completed answers are observed only after the original continuation is
empty. An unfinished or faulting configuration never denotes an empty answer
bag merely because it has no next transition. -/
def Snapshot.completedAnswers (packet : Snapshot) : Option (List Atom) :=
  match packet.control, packet.frames with
  | .returned answers, [] => some answers
  | _, _ => none

theorem Snapshot.completedAnswers_returns (program : Program) (packet : Snapshot)
    (answers : List Atom) (observed : packet.completedAnswers = some answers) :
    run program 0 packet.decode =
      .complete packet.decode.state answers packet.input packet.output := by
  cases packet with
  | mk core spaces cells control frames input output =>
    cases control <;> cases frames <;>
      simp_all [Snapshot.completedAnswers, Snapshot.decode]

theorem Snapshot.completedAnswers_of_run (program : Program) (packet : Snapshot)
    (state : Effects.State) (answers input output : List Atom)
    (completed : run program 0 packet.decode = .complete state answers input output) :
    packet.completedAnswers = some answers := by
  cases packet with
  | mk core spaces cells control frames pending printed =>
    cases control <;> cases frames <;>
      simp_all [Snapshot.completedAnswers, Snapshot.decode, run]

/-- Public completed answers form a bag. The retained trace still checks each
original state and continuation, including their causal scheduling policy;
permuting a claimed answer list does not change this judgment. -/
def checkCompletedBag (program : Program) (source : Snapshot)
    (trace : List Snapshot) (claimed : List Atom) : Bool :=
  checkTrace program source trace &&
    match (traceEnd source trace).completedAnswers with
    | none => false
    | some answers => decide ((answers : Multiset Atom) = (claimed : Multiset Atom))

theorem checkCompletedBag_exact (program : Program) (source : Snapshot)
    (trace : List Snapshot) (claimed : List Atom) :
    checkCompletedBag program source trace claimed = true ↔
      checkTrace program source trace = true ∧
      ∃ answers, (traceEnd source trace).completedAnswers = some answers ∧
        (answers : Multiset Atom) = (claimed : Multiset Atom) := by
  cases observed : (traceEnd source trace).completedAnswers <;>
    simp [checkCompletedBag, observed]

theorem checkCompletedBag_permutation (program : Program) (source : Snapshot)
    (trace : List Snapshot) (first second : List Atom)
    (sameBag : (first : Multiset Atom) = (second : Multiset Atom)) :
    checkCompletedBag program source trace first =
      checkCompletedBag program source trace second := by
  simp only [checkCompletedBag, sameBag]

/-- Exact finite-evidence coverage of the original completed source runs,
with unordered public answers and their multiplicity intact. This theorem is
about the existing Atom machine, not a complete Prime or HE dialect adapter. -/
theorem accepted_bag_iff_source_completed (program : Program) (source : Snapshot)
    (claimed : List Atom) :
    (∃ trace, checkCompletedBag program source trace claimed = true) ↔
      ∃ state answers input output,
        DeclarativeSpec.Runs program source.decode (.complete state answers input output) ∧
        (answers : Multiset Atom) = (claimed : Multiset Atom) := by
  constructor
  · rintro ⟨trace, checked⟩
    obtain ⟨accepted, answers, observed, bag⟩ :=
      (checkCompletedBag_exact program source trace claimed).mp checked
    let final := traceEnd source trace
    have completed := Snapshot.completedAnswers_returns program final answers observed
    obtain ⟨fuel, original⟩ := path_lifts_completed_run program
      (checkedTrace_path program source trace accepted) 0
      final.decode.state answers final.input final.output completed
    exact ⟨final.decode.state, answers, final.input, final.output,
      (completed_run_iff_derivation program source.decode _ _ _ _).mp ⟨fuel, original⟩, bag⟩
  · rintro ⟨state, answers, input, output, derivation, bag⟩
    obtain ⟨trace, accepted, original⟩ :=
      source_run_has_checked_trace program source (.complete state answers input output) derivation
    have observed := Snapshot.completedAnswers_of_run program
      (traceEnd source trace) state answers input output original
    exact ⟨trace, (checkCompletedBag_exact program source trace claimed).mpr
      ⟨accepted, answers, observed, bag⟩⟩

/-! ## Static program agreement and its dynamic-activation boundary -/

/-- Agreement is checked against the original source program interface.
The observer adds no new dispatch, demand or clause-equivalence condition. -/
theorem nativeStep_eq_of_program_agreement {first second : Program} (source : Snapshot)
    (agreement : ProgramAgreementAt first second source.decode) :
    nativeStep first source = nativeStep second source := by
  simp only [nativeStep, step_eq_of_program_agreement agreement]

/-- A closed supported program has exactly the same constructed finite trace
under an agreeing program. Store mutations are still performed by the original
machine; the guard constrains code dispatch, not mutable data values. -/
theorem emitTrace_of_closed_agreement {allowed : String → Bool} {first second : Program}
    (closed : ProgramClosed allowed first) (agreement : ProgramAgreementOn allowed first second)
    (fuel : Nat) (source : Snapshot) (within : configurationWithin allowed source.decode) :
    emitTrace first fuel source = emitTrace second fuel source := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
    have same := nativeStep_eq_of_program_agreement source
      (configuration_agreement_on agreement within)
    cases next : nativeStep first source with
    | none => simp [emitTrace, ← same, next]
    | some target =>
      have targetWithin := transition_within closed (nativeStep_sound first source target next) within
      simp [emitTrace, ← same, next, ih target targetWithin]

/-- A fresh static-code extension earns the original source agreement guard,
then preserves the exact finite native trace. Reflection of unrelated stored
rows and activation of freshly inserted code remain different observations. -/
theorem emitTrace_append_fresh {allowed : String → Bool} (program extension : Program)
    (closed : ProgramClosed allowed program)
    (freshEquations : ∀ equation ∈ extension.equations, allowed equation.head = false)
    (freshDeclarations : ∀ name types,
      .expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)] ∈
        extension.declarations → allowed name = false)
    (fuel : Nat) (source : Snapshot) (within : configurationWithin allowed source.decode) :
    emitTrace program fuel source = emitTrace (program.append extension) fuel source :=
  emitTrace_of_closed_agreement closed
    (appended_program_agreement allowed program extension freshEquations freshDeclarations)
    fuel source within

namespace Examples

/-- The same equation is already reflectively present in both source stores.
Only the executable program table differs in the paired executions below. -/
def storedFreshEquation : Snapshot :=
  { core := [.expression [.symbol "=", .expression [.symbol "fresh-function"], seven]]
    spaces := []
    cells := []
    control := .evaluate [] (.expression [.symbol "fresh-function"])
    frames := []
    input := []
    output := [] }

def freshProgram : Program :=
  { equations := [⟨"fresh-function", [], seven⟩]
    declarations := []
    layout := [.equation] }

theorem stored_equation_without_reindex_stays_data :
    (traceEnd storedFreshEquation
      (emitTrace { equations := [], declarations := [] } 20 storedFreshEquation)).completedAnswers =
        some [.expression [.symbol "fresh-function"]] := by decide +kernel

theorem program_reindex_activates_the_stored_equation :
    (traceEnd storedFreshEquation
      (emitTrace freshProgram 20 storedFreshEquation)).completedAnswers = some [seven] := by
  decide +kernel

theorem reflective_storage_does_not_imply_code_activation :
    (traceEnd storedFreshEquation
      (emitTrace { equations := [], declarations := [] } 20 storedFreshEquation)).completedAnswers ≠
    (traceEnd storedFreshEquation
      (emitTrace freshProgram 20 storedFreshEquation)).completedAnswers := by
  rw [stored_equation_without_reindex_stays_data, program_reindex_activates_the_stored_equation]
  decide

end Examples

end Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay.LiveRegistry
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program Indexes index)
open Eval

/-- Every source transition consults the declarations currently stored in
self. Index evidence is independent of the native indexer. This live policy
is distinct from the original pinned program and from code-entry refresh. -/
inductive Transition : Configuration → Configuration → Prop where
  | indexed {source target : Configuration} (program : Program)
      (declarations : Indexes source.state.core program)
      (execution : DeclarativeSpec.Transition program source target) :
      Transition source target

/-- Execute the original dispatcher after indexing the actual current store. -/
def step (source : Configuration) : Option Configuration :=
  Eval.step (index source.state.core) source

theorem step_exact (source target : Configuration) :
    step source = some target ↔ Transition source target := by
  constructor
  · intro actual
    exact .indexed _ (SpaceSemantics.index_exact source.state.core)
      ((Eval.step_iff_transition _ _ _).mp actual)
  · intro transition
    cases transition with
    | indexed program declarations execution =>
        have same := declarations.unique (SpaceSemantics.index_exact source.state.core)
        subst same
        exact (Eval.step_iff_transition _ _ _).mpr execution

/-- The source graph is generated from the indexed source transitions. -/
def theory : Mettapedia.GSLT.GSLT where
  Term := Configuration
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Transition
  rewrites_resp_left := by
    intro first other last same transition
    subst other
    exact ⟨last, transition, rfl⟩
  rewrites_resp_right := by
    intro first last other transition same
    subst other
    exact transition

def nativeStep (source : Snapshot) : Option Snapshot :=
  ProgramReplay.nativeStep (index source.core) source

theorem nativeStep_source (source target : Snapshot)
    (computed : nativeStep source = some target) : Transition source.decode target.decode := by
  exact .indexed _ (SpaceSemantics.index_exact source.core)
    (ProgramReplay.nativeStep_sound _ source target computed)

theorem nativeStep_of_source (source : Snapshot) (target : Configuration)
    (transition : Transition source.decode target) :
    nativeStep source = some (snapshot (supportAfter source.cellNames source.decode) target) ∧
      (snapshot (supportAfter source.cellNames source.decode) target).decode = target := by
  cases transition with
  | indexed program declarations execution =>
      have same := declarations.unique (SpaceSemantics.index_exact source.core)
      subst same
      exact ProgramReplay.nativeStep_of_transition _ source target execution

def checkStep (source target : Snapshot) : Bool :=
  ProgramReplay.checkStep (index source.core) source target

theorem checkStep_exact (source target : Snapshot) :
    checkStep source target = true ↔ Transition source.decode target.decode := by
  rw [checkStep, ProgramReplay.checkStep_exact]
  constructor
  · intro execution
    exact .indexed _ (SpaceSemantics.index_exact source.core) execution
  · intro execution
    cases execution with
    | indexed program declarations execution =>
        have same := declarations.unique (SpaceSemantics.index_exact source.core)
        subst same
        exact execution

/-- A finite proof retains every transition occurrence and whole snapshot. -/
def checkTrace : Snapshot → List Snapshot → Bool
  | _, [] => true
  | source, target :: rest => checkStep source target && checkTrace target rest

theorem checkTrace_exact (source : Snapshot) (trace : List Snapshot) :
    checkTrace source trace = true ↔
      List.IsChain Transition (source.decode :: trace.map Snapshot.decode) := by
  induction trace generalizing source with
  | nil => simp [checkTrace]
  | cons target rest ih =>
      simp only [checkTrace, Bool.and_eq_true, List.map_cons,
        List.isChain_cons_cons, checkStep_exact, ih]

theorem checkedTrace_path (source : Snapshot) (trace : List Snapshot)
    (checked : checkTrace source trace = true) :
    theory.MultiStep source.decode (traceEnd source trace).decode := by
  induction trace generalizing source with
  | nil => exact .refl _
  | cons target rest ih =>
      simp only [checkTrace, Bool.and_eq_true] at checked
      exact .step ((checkStep_exact source target).mp checked.1) (ih target checked.2)

def emitTrace : Nat → Snapshot → List Snapshot
  | 0, _ => []
  | fuel + 1, source =>
      match nativeStep source with
      | none => []
      | some target => target :: emitTrace fuel target

theorem emitTrace_checked (fuel : Nat) (source : Snapshot) :
    checkTrace source (emitTrace fuel source) = true := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
      cases next : nativeStep source with
      | none => simp [emitTrace, next, checkTrace]
      | some target =>
          have head := (checkStep_exact source target).mpr (nativeStep_source _ _ next)
          simp [emitTrace, next, checkTrace, head, ih]

theorem emitTrace_length (fuel : Nat) (source : Snapshot) :
    (emitTrace fuel source).length ≤ fuel := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
      cases next : nativeStep source with
      | none => simp [emitTrace, next]
      | some target => simpa [emitTrace, next] using Nat.succ_le_succ (ih target)

/-- Budgets count original dispatcher transitions; repeated registry indexing
is real work for a later executed resource account. -/
def advance : Nat → Configuration → Configuration
  | 0, source => source
  | fuel + 1, source =>
      match step source with
      | none => source
      | some target => advance fuel target

theorem advance_stopped (fuel : Nat) (source : Configuration) (stopped : step source = none) :
    advance fuel source = source := by
  cases fuel <;> simp [advance, stopped]

theorem advance_split (first second : Nat) (source : Configuration) :
    advance second (advance first source) = advance (first + second) source := by
  induction first generalizing source with
  | zero => simp [advance]
  | succ first ih =>
      cases next : step source with
      | none => rw [advance_stopped _ _ next, advance_stopped _ _ next,
          advance_stopped _ _ next]
      | some target => simpa [advance, next, Nat.succ_add] using ih target

theorem emitTrace_endpoint (fuel : Nat) (source : Snapshot) :
    (traceEnd source (emitTrace fuel source)).decode = advance fuel source.decode := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
      cases next : nativeStep source with
      | none =>
          have stopped : step source.decode = none := by
            change ProgramReplay.nativeStep (index source.core) source = none at next
            exact (ProgramReplay.nativeStep_eq_none_iff _ source).mp next
          simp [emitTrace, next, traceEnd, advance, stopped]
      | some target =>
          have actual := (step_exact _ _).mpr (nativeStep_source _ _ next)
          simpa [emitTrace, next, traceEnd, advance, actual] using ih target

/-- Direct native computation consumes a transition budget and retains the
whole physical result, without accepting or replaying a submitted proof. -/
def nativeAdvance : Nat → Snapshot → Snapshot
  | 0, source => source
  | fuel + 1, source =>
      match nativeStep source with
      | none => source
      | some target => nativeAdvance fuel target

theorem nativeAdvance_traceEnd (fuel : Nat) (source : Snapshot) :
    nativeAdvance fuel source = traceEnd source (emitTrace fuel source) := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
      cases next : nativeStep source with
      | none => simp [nativeAdvance, emitTrace, traceEnd, next]
      | some target => simpa [nativeAdvance, emitTrace, traceEnd, next] using ih target

theorem nativeAdvance_decode (fuel : Nat) (source : Snapshot) :
    (nativeAdvance fuel source).decode = advance fuel source.decode := by
  rw [nativeAdvance_traceEnd, emitTrace_endpoint]

theorem nativeAdvance_split (first second : Nat) (source : Snapshot) :
    (nativeAdvance second (nativeAdvance first source)).decode =
      (nativeAdvance (first + second) source).decode := by
  rw [nativeAdvance_decode, nativeAdvance_decode, nativeAdvance_decode, advance_split]

/-- A schedule is an implementation policy for retaining and resuming the
same actual native configuration. It creates no extra source event. -/
def nativeChunks : List Nat → Snapshot → Snapshot
  | [], source => source
  | fuel :: rest, source => nativeChunks rest (nativeAdvance fuel source)

theorem nativeChunks_decode (budgets : List Nat) (source : Snapshot) :
    (nativeChunks budgets source).decode = advance budgets.sum source.decode := by
  induction budgets generalizing source with
  | nil => rfl
  | cons fuel rest ih =>
      rw [nativeChunks, ih, nativeAdvance_decode, advance_split]
      rfl

theorem nativeChunks_same_budget (budgets : List Nat) (source : Snapshot) :
    (nativeChunks budgets source).decode = (nativeAdvance budgets.sum source).decode := by
  rw [nativeChunks_decode, nativeAdvance_decode]

/-- Outcome inspection uses zero original transitions. Its program argument
cannot alter completion, faults or the retained unfinished configuration. -/
def readout (source : Configuration) : Outcome :=
  Eval.run {equations := [], declarations := []} 0 source

theorem readout_eq (program : Program) (source : Configuration) :
    readout source = Eval.run program 0 source := by
  cases source with
  | mk state control frames input output =>
      cases control <;> cases frames <;> rfl

/-- Every finite independently specified live-registry path has accepted
snapshot evidence; no arbitrary-world equality decision is assumed. -/
theorem path_has_checked_trace {source target : Configuration}
    (path : theory.MultiStep source target) :
    ∀ initial : Snapshot, initial.decode = source →
      ∃ trace, checkTrace initial trace = true ∧ (traceEnd initial trace).decode = target := by
  have lift {system : Mettapedia.GSLT.GSLT}
      {property : system.Term → system.Term → Prop}
      (atSelf : ∀ term, property term term)
      (prepend : ∀ {first middle last}, system.Step first middle →
        property middle last → property first last)
      {first last} (steps : system.MultiStep first last) : property first last := by
    induction steps with
    | refl term => exact atSelf term
    | step transition _ ih => exact prepend transition ih
  apply lift (system := theory)
    (property := fun first last => ∀ initial : Snapshot, initial.decode = first →
      ∃ trace, checkTrace initial trace = true ∧ (traceEnd initial trace).decode = last)
    (steps := path)
  · intro configuration initial represents
    exact ⟨[], rfl, represents⟩
  · intro first middle last transition ih initial represents
    change Transition first middle at transition
    have actual : Transition initial.decode middle := by rw [represents]; exact transition
    let next := snapshot (supportAfter initial.cellNames initial.decode) middle
    have readback : next.decode = middle := (nativeStep_of_source initial middle actual).2
    obtain ⟨tail, accepted, endpoint⟩ := ih next readback
    have checkedHead := (checkStep_exact initial next).mpr (by rw [readback]; exact actual)
    exact ⟨next :: tail, by simp [checkTrace, checkedHead, accepted], endpoint⟩

def checkPath (source target : Snapshot) (trace : List Snapshot) : Bool :=
  checkTrace source trace && (traceEnd source trace).same target

theorem checkPath_exact (source target : Snapshot) (trace : List Snapshot) :
    checkPath source target trace = true ↔
      List.IsChain Transition (source.decode :: trace.map Snapshot.decode) ∧
      (traceEnd source trace).decode = target.decode := by
  simp only [checkPath, Bool.and_eq_true, checkTrace_exact, Snapshot.same_exact]

theorem accepted_path_iff_source_reachable (source target : Snapshot) :
    (∃ trace, checkPath source target trace = true) ↔
      theory.MultiStep source.decode target.decode := by
  constructor
  · rintro ⟨trace, accepted⟩
    have both : checkTrace source trace = true ∧
        (traceEnd source trace).decode = target.decode := by
      simpa only [checkPath, Bool.and_eq_true, Snapshot.same_exact] using accepted
    rw [← both.2]
    exact checkedTrace_path source trace both.1
  · intro path
    obtain ⟨trace, accepted, endpoint⟩ := path_has_checked_trace path source rfl
    exact ⟨trace, by simp only [checkPath, accepted, Bool.true_and, Snapshot.same_exact, endpoint]⟩

/-- The original pinned machine and live registry agree at a source state
only when their actual dispatch, argument demand and selected bodies agree. -/
theorem step_eq_pinned (program : Program) (source : Configuration)
    (agreement : ProgramAgreementAt (index source.state.core) program source) :
    step source = Eval.step program source :=
  step_eq_of_program_agreement agreement


/-- Completed answers are public bags; the proof still retains every causal
source transition, whole store and continuation. -/
def checkCompletedBag (source : Snapshot) (trace : List Snapshot)
    (claimed : List Atom) : Bool :=
  checkTrace source trace &&
    match (traceEnd source trace).completedAnswers with
    | none => false
    | some answers => decide ((answers : Multiset Atom) = (claimed : Multiset Atom))

theorem checkCompletedBag_exact (source : Snapshot) (trace : List Snapshot)
    (claimed : List Atom) :
    checkCompletedBag source trace claimed = true ↔
      checkTrace source trace = true ∧
      ∃ answers, (traceEnd source trace).completedAnswers = some answers ∧
        (answers : Multiset Atom) = (claimed : Multiset Atom) := by
  cases observed : (traceEnd source trace).completedAnswers <;>
    simp [checkCompletedBag, observed]

theorem checkCompletedBag_permutation (source : Snapshot) (trace : List Snapshot)
    (first second : List Atom) (sameBag : (first : Multiset Atom) = (second : Multiset Atom)) :
    checkCompletedBag source trace first = checkCompletedBag source trace second := by
  simp only [checkCompletedBag, sameBag]

/-- A source completion requires a finite indexed source path to an actual
returned control with no pending continuation, independently of any checker. -/
def Completed (source : Configuration) (claimed : List Atom) : Prop :=
  ∃ target answers, theory.MultiStep source target ∧
    target.control = .returned answers ∧ target.frames = [] ∧
    (answers : Multiset Atom) = (claimed : Multiset Atom)

theorem Snapshot.completedAnswers_exact (packet : Snapshot) (answers : List Atom) :
    packet.completedAnswers = some answers ↔
      packet.decode.control = .returned answers ∧ packet.decode.frames = [] := by
  cases packet with
  | mk core spaces cells control frames input output =>
    cases control <;> cases frames <;>
      simp [ProgramReplay.Snapshot.completedAnswers, ProgramReplay.Snapshot.decode]

theorem checkCompletedBag_sourceExact (source : Snapshot) (trace : List Snapshot)
    (claimed : List Atom) :
    checkCompletedBag source trace claimed = true ↔
      List.IsChain Transition (source.decode :: trace.map Snapshot.decode) ∧
      ∃ answers, (traceEnd source trace).decode.control = .returned answers ∧
        (traceEnd source trace).decode.frames = [] ∧
        (answers : Multiset Atom) = (claimed : Multiset Atom) := by
  rw [checkCompletedBag_exact, checkTrace_exact]
  simp only [Snapshot.completedAnswers_exact, and_assoc]

theorem accepted_bag_iff_source_completed (source : Snapshot) (claimed : List Atom) :
    (∃ trace, checkCompletedBag source trace claimed = true) ↔ Completed source.decode claimed := by
  constructor
  · rintro ⟨trace, accepted⟩
    obtain ⟨checked, answers, observed, bag⟩ :=
      (checkCompletedBag_exact source trace claimed).mp accepted
    obtain ⟨control, frames⟩ := (Snapshot.completedAnswers_exact _ _).mp observed
    exact ⟨_, answers, checkedTrace_path source trace checked, control, frames, bag⟩
  · rintro ⟨target, answers, path, control, frames, bag⟩
    obtain ⟨trace, checked, endpoint⟩ := path_has_checked_trace path source rfl
    have observed : (traceEnd source trace).completedAnswers = some answers := by
      apply (Snapshot.completedAnswers_exact _ _).mpr
      rw [endpoint]
      exact ⟨control, frames⟩
    exact ⟨trace, (checkCompletedBag_exact source trace claimed).mpr
      ⟨checked, answers, observed, bag⟩⟩

/-- Exact budgeted agreement can be justified by the original program
observations along its reachable states. Dynamic mutation is not erased. -/
theorem advance_eq_pinned (program : Program) (fuel : Nat) (source : Configuration)
    (agreement : ∀ current, (Eval.theory program).MultiStep source current →
      ProgramAgreementAt (index current.state.core) program current) :
    advance fuel source = ProgramReplay.advance program fuel source := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
    have atSource := step_eq_pinned program source (agreement source (.refl _))
    cases next : Eval.step program source with
    | none => simp [advance, ProgramReplay.advance, atSource, next]
    | some target =>
      have inherited : ∀ current, (Eval.theory program).MultiStep target current →
          ProgramAgreementAt (index current.state.core) program current := by
        intro current path
        exact agreement current (.step ((Eval.step_iff_transition _ _ _).mp next) path)
      simpa [advance, ProgramReplay.advance, atSource, next] using ih target inherited

theorem advance_eq_pinned_of_closed (program : Program) (fuel : Nat)
    (allowed : String → Bool) (source : Configuration)
    (closed : ProgramClosed allowed program) (within : configurationWithin allowed source)
    (agreement : ∀ current, (Eval.theory program).MultiStep source current →
      ProgramAgreementOn allowed (index current.state.core) program) :
    advance fuel source = ProgramReplay.advance program fuel source := by
  apply advance_eq_pinned program fuel source
  intro current path
  exact configuration_agreement_on (agreement current path) (path_within closed path within)

end Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay.LiveRegistry

namespace Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay.CodeEntryRegistry
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program Indexes index)
open Eval

/-- Only an actual explicit code-evaluation control refreshes this profile's
registry. Ordinary equation bodies and captured continuations keep the cache.
A top-level request starts with its current stored rows as the initial cache. -/
def AtEntry (source : Configuration) : Prop :=
  match source.control with
  | .arguments _ (.function "eval") [] [_] _ => True
  | _ => False

instance (source : Configuration) : Decidable (AtEntry source) := by
  unfold AtEntry
  split <;> infer_instance

abbrev State := List Atom × Configuration
abbrev Packet := List Atom × Snapshot

inductive Transition : State → State → Prop where
  | retained {rows : List Atom} {source target : Configuration} (program : Program)
      (declarations : Indexes rows program) (ordinary : ¬ AtEntry source)
      (execution : DeclarativeSpec.Transition program source target) :
      Transition (rows, source) (rows, target)
  | entered {rows : List Atom} {source target : Configuration} (program : Program)
      (declarations : Indexes source.state.core program) (entry : AtEntry source)
      (execution : DeclarativeSpec.Transition program source target) :
      Transition (rows, source) (source.state.core, target)

def activeRows (source : State) : List Atom :=
  if AtEntry source.2 then source.2.state.core else source.1

def step (source : State) : Option State :=
  (Eval.step (index (activeRows source)) source.2).map fun target => (activeRows source, target)

theorem step_exact (source target : State) : step source = some target ↔ Transition source target := by
  constructor
  · intro actual
    cases computed : Eval.step (index (activeRows source)) source.2 with
    | none => simp [step, computed] at actual
    | some reached =>
      have targetEq : (activeRows source, reached) = target := by simpa [step, computed] using actual
      rw [← targetEq]
      have execution := (Eval.step_iff_transition _ _ _).mp computed
      by_cases entry : AtEntry source.2
      · simp only [activeRows, if_pos entry] at execution ⊢
        exact .entered _ (SpaceSemantics.index_exact _) entry execution
      · simp only [activeRows, if_neg entry] at execution ⊢
        exact .retained _ (SpaceSemantics.index_exact _) entry execution
  · intro actual
    cases actual with
    | retained program declarations ordinary execution =>
      have same := declarations.unique (SpaceSemantics.index_exact _)
      subst same
      simp only [step, activeRows, if_neg ordinary, transition_step execution, Option.map_some]
    | entered program declarations entry execution =>
      have same := declarations.unique (SpaceSemantics.index_exact _)
      subst same
      simp only [step, activeRows, if_pos entry, transition_step execution, Option.map_some]

def decode (packet : Packet) : State := (packet.1, packet.2.decode)

def nativeStep (source : Packet) : Option Packet :=
  let rows := activeRows (decode source)
  (ProgramReplay.nativeStep (index rows) source.2).map fun target => (rows, target)

def checkStep (source target : Packet) : Bool :=
  match nativeStep source with
  | none => false
  | some actual => actual.1 == target.1 && actual.2.same target.2

theorem nativeStep_source (source target : Packet) (computed : nativeStep source = some target) :
    Transition (decode source) (decode target) := by
  dsimp only [nativeStep] at computed
  obtain ⟨emitted, produced, targetEq⟩ := Option.map_eq_some_iff.mp computed
  rw [← targetEq]
  apply (step_exact _ _).mp
  apply Option.map_eq_some_iff.mpr
  exact ⟨emitted.decode, transition_step (ProgramReplay.nativeStep_sound _ _ _ produced), rfl⟩

theorem checkStep_exact (source target : Packet) :
    checkStep source target = true ↔ Transition (decode source) (decode target) := by
  constructor
  · intro accepted
    cases produced : nativeStep source with
    | none => simp [checkStep, produced] at accepted
    | some emitted =>
      have equal : decode emitted = decode target := by
        simp only [checkStep, produced, Bool.and_eq_true, beq_iff_eq,
          ProgramReplay.Snapshot.same_exact] at accepted
        exact Prod.ext accepted.1 accepted.2
      rw [← equal]
      exact nativeStep_source source emitted produced
  · intro actual
    have reached := (step_exact _ _).mpr actual
    dsimp only [step] at reached
    obtain ⟨configuration, original, pairEq⟩ := Option.map_eq_some_iff.mp reached
    have rowsEq := congrArg Prod.fst pairEq
    have configurationEq := congrArg Prod.snd pairEq
    have sourceTransition := (Eval.step_iff_transition _ _ _).mp original
    obtain ⟨produced, readback⟩ := ProgramReplay.nativeStep_of_transition _ source.2 _ sourceTransition
    have result : nativeStep source =
        some (activeRows (decode source),
          snapshot (supportAfter source.2.cellNames source.2.decode) configuration) := by
      dsimp only [nativeStep]
      rw [produced]
      rfl
    simp only [checkStep, result, Bool.and_eq_true, beq_iff_eq,
      ProgramReplay.Snapshot.same_exact]
    exact ⟨rowsEq, readback.trans configurationEq⟩

def advance : Nat → State → State
  | 0, source => source
  | fuel + 1, source =>
      match step source with
      | none => source
      | some target => advance fuel target


/-- Every source step from a finite packet has a constructed packet for its
complete target store and exact retained source cache. -/
theorem source_step_represented (source : Packet) (target : State)
    (actual : Transition (decode source) target) :
    ∃ packet, nativeStep source = some packet ∧ decode packet = target := by
  have reached := (step_exact _ _).mpr actual
  dsimp only [step] at reached
  obtain ⟨configuration, original, pairEq⟩ := Option.map_eq_some_iff.mp reached
  have transition := (Eval.step_iff_transition _ _ _).mp original
  obtain ⟨produced, readback⟩ := ProgramReplay.nativeStep_of_transition _ source.2 _ transition
  refine ⟨(activeRows (decode source), snapshot
    (supportAfter source.2.cellNames source.2.decode) configuration), ?_, ?_⟩
  · dsimp only [nativeStep]
    rw [produced]
    rfl
  · change (activeRows (decode source),
      (snapshot (supportAfter source.2.cellNames source.2.decode) configuration).decode) = target
    rw [readback]
    exact pairEq

theorem advance_stopped (fuel : Nat) (source : State) (stopped : step source = none) :
    advance fuel source = source := by
  cases fuel <;> simp [advance, stopped]

/-- Resumption retains the actual code-entry cache as well as every original
configuration field; no code-entry or store effect is replayed. -/
theorem advance_split (first second : Nat) (source : State) :
    advance second (advance first source) = advance (first + second) source := by
  induction first generalizing source with
  | zero => simp [advance]
  | succ first ih =>
      cases next : step source with
      | none => rw [advance_stopped _ _ next, advance_stopped _ _ next,
          advance_stopped _ _ next]
      | some target => simpa [advance, next, Nat.succ_add] using ih target

/-- Equality of the observed transitions requires actual agreement of
current-store and retained-cache dispatch, demand and selected clauses. -/
theorem step_projection_eq_live (source : State)
    (agreement : ProgramAgreementAt (index (activeRows source))
      (index source.2.state.core) source.2) :
    (step source).map Prod.snd = LiveRegistry.step source.2 := by
  have actual := step_eq_of_program_agreement agreement
  simpa [step, LiveRegistry.step, Option.map_map, Function.comp_def] using actual

theorem step_projection_eq_live_on (source : State) (allowed : String → Bool)
    (within : configurationWithin allowed source.2)
    (agreement : ProgramAgreementOn allowed (index (activeRows source))
      (index source.2.state.core)) :
    (step source).map Prod.snd = LiveRegistry.step source.2 :=
  step_projection_eq_live source (configuration_agreement_on agreement within)

end Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay.CodeEntryRegistry
