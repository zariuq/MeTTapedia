import Mettapedia.Languages.MeTTa.PeTTa.OperationalGSLT
import Mettapedia.Languages.MeTTa.OSLFCore.Bridge

/-!
# Finite representations of the existing PeTTa configurations

The wire carries the existing control, continuation, substitution, store and
I/O fields. Atom payloads use the lossless ground-data Pattern codec. Store
decoding reconstructs every allocated space and every finitely supported cell;
it does not introduce a second evaluator or state carrier. A supplied support
list and the empty unallocated tail justify exact reconstruction.

This module supplies the configuration representation needed by a LanguageDef
transition simulation. The representation theorem alone is not that simulation.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.ConfigurationEncoding

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open SpaceSemantics (Cases Program)
open Effects (State Fault)
open Eval (Target Control Frame Configuration)
open NamedSpaces.Store

def text (value : String) : Atom := .grounded (.string value)

def index (value : Nat) : Atom := .grounded (.int value)

def readIndex : Atom → Option Nat
  | .grounded (.int value) => if 0 ≤ value then some value.toNat else none
  | _ => none

@[simp] theorem readIndex_index (value : Nat) :
    readIndex (index value) = some value := by
  simp [readIndex, index]

def bindingsData (bindings : Subst) : Atom :=
  .expression (bindings.map fun (name, value) => .expression [text name, value])

def readBinding : Atom → Option (String × Atom)
  | .expression [.grounded (.string name), value] => some (name, value)
  | _ => none

def readBindings : Atom → Option Subst
  | .expression rows => rows.mapM readBinding
  | _ => none

@[simp] theorem readBindings_bindingsData (bindings : Subst) :
    readBindings (bindingsData bindings) = some bindings := by
  induction bindings with
  | nil => rfl
  | cons first rest ih =>
      rcases first with ⟨name, value⟩
      simp_all [readBindings, bindingsData, readBinding, text]

def casesData (rows : Cases) : Atom :=
  .expression (rows.map fun (pattern, body) => .expression [pattern, body])

def readCase : Atom → Option (Atom × Atom)
  | .expression [pattern, body] => some (pattern, body)
  | _ => none

def readCases : Atom → Option Cases
  | .expression rows => rows.mapM readCase
  | _ => none

@[simp] theorem readCases_casesData (rows : Cases) :
    readCases (casesData rows) = some rows := by
  induction rows with
  | nil => rfl
  | cons first rest ih =>
      rcases first with ⟨pattern, body⟩
      simp_all [readCases, casesData, readCase]

def targetData : Target → Atom
  | .data => .symbol "petta-target-data-v1"
  | .function head => .expression [.symbol "petta-target-function-v1", text head]

def readTarget : Atom → Option Target
  | .symbol "petta-target-data-v1" => some .data
  | .expression [.symbol "petta-target-function-v1", .grounded (.string head)] =>
      some (.function head)
  | _ => none

@[simp] theorem readTarget_targetData (target : Target) :
    readTarget (targetData target) = some target := by
  cases target <;> rfl

def faultData : Fault → Atom
  | .invalidSpace => .symbol "petta-fault-space-v1"
  | .zeroDivisor => .symbol "petta-fault-zero-v1"
  | .missingCell name => .expression [.symbol "petta-fault-cell-v1", text name]
  | .invalidArguments head => .expression [.symbol "petta-fault-arguments-v1", text head]

def readFault : Atom → Option Fault
  | .symbol "petta-fault-space-v1" => some .invalidSpace
  | .symbol "petta-fault-zero-v1" => some .zeroDivisor
  | .expression [.symbol "petta-fault-cell-v1", .grounded (.string name)] =>
      some (.missingCell name)
  | .expression [.symbol "petta-fault-arguments-v1", .grounded (.string head)] =>
      some (.invalidArguments head)
  | _ => none

@[simp] theorem readFault_faultData (fault : Fault) :
    readFault (faultData fault) = some fault := by
  cases fault <;> rfl

mutual
  /-- All control constructors, including recursively pending alternatives. -/
  def controlData : Control → Atom
    | .evaluate bindings expression =>
        .expression [.symbol "petta-control-evaluate-v1", bindingsData bindings, expression]
    | .arguments bindings target remaining values position =>
        .expression [.symbol "petta-control-arguments-v1", bindingsData bindings,
          targetData target, .expression remaining, .expression values, index position]
    | .sequence remaining answers =>
        .expression [.symbol "petta-control-sequence-v1",
          .expression (controlsData remaining), .expression answers]
    | .returned answers =>
        .expression [.symbol "petta-control-returned-v1", .expression answers]
    | .fault reason => .expression [.symbol "petta-control-fault-v1", faultData reason]
  termination_by control => sizeOf control

  def controlsData : List Control → List Atom
    | [] => []
    | first :: rest => controlData first :: controlsData rest
  termination_by controls => sizeOf controls
end

mutual
  def readControl : Atom → Option Control
    | .expression [.symbol "petta-control-evaluate-v1", bindings, expression] => do
        return .evaluate (← readBindings bindings) expression
    | .expression [.symbol "petta-control-arguments-v1", bindings, target,
        .expression remaining, .expression values, position] => do
        return .arguments (← readBindings bindings) (← readTarget target)
          remaining values (← readIndex position)
    | .expression [.symbol "petta-control-sequence-v1", .expression remaining,
        .expression answers] => do
        return .sequence (← readControls remaining) answers
    | .expression [.symbol "petta-control-returned-v1", .expression answers] =>
        some (.returned answers)
    | .expression [.symbol "petta-control-fault-v1", reason] =>
        Control.fault <$> readFault reason
    | _ => none
  termination_by value => sizeOf value

  def readControls : List Atom → Option (List Control)
    | [] => some []
    | first :: rest => do
        return (← readControl first) :: (← readControls rest)
  termination_by values => sizeOf values
end

mutual
  @[simp] theorem readControl_controlData (control : Control) :
      readControl (controlData control) = some control := by
    cases control with
    | evaluate bindings expression => simp [controlData, readControl]
    | arguments bindings target remaining values position => simp [controlData, readControl]
    | sequence remaining answers =>
        simp only [controlData, readControl, readControls_controlsData remaining]
        rfl
    | returned answers => simp [controlData, readControl]
    | fault reason => simp [controlData, readControl]
  termination_by sizeOf control

  @[simp] theorem readControls_controlsData (controls : List Control) :
      readControls (controlsData controls) = some controls := by
    cases controls with
    | nil => simp [controlsData, readControls]
    | cons first rest =>
        simp only [controlsData, readControls, readControl_controlData first,
          readControls_controlsData rest]
        rfl
  termination_by sizeOf controls
end

def frameData : Frame → Atom
  | .bind bindings pattern body =>
      .expression [.symbol "petta-frame-bind-v1", bindingsData bindings, pattern, body]
  | .select bindings rows =>
      .expression [.symbol "petta-frame-select-v1", bindingsData bindings, casesData rows]
  | .branch bindings yes no =>
      .expression [.symbol "petta-frame-branch-v1", bindingsData bindings, yes, no]
  | .collect => .symbol "petta-frame-collect-v1"
  | .argument bindings target remaining values position =>
      .expression [.symbol "petta-frame-argument-v1", bindingsData bindings,
        targetData target, .expression remaining, .expression values, index position]
  | .sequence remaining answers =>
      .expression [.symbol "petta-frame-sequence-v1", .expression (controlsData remaining),
        .expression answers]

def readFrame : Atom → Option Frame
  | .expression [.symbol "petta-frame-bind-v1", bindings, pattern, body] => do
      return .bind (← readBindings bindings) pattern body
  | .expression [.symbol "petta-frame-select-v1", bindings, rows] => do
      return .select (← readBindings bindings) (← readCases rows)
  | .expression [.symbol "petta-frame-branch-v1", bindings, yes, no] => do
      return .branch (← readBindings bindings) yes no
  | .symbol "petta-frame-collect-v1" => some .collect
  | .expression [.symbol "petta-frame-argument-v1", bindings, target,
      .expression remaining, .expression values, position] => do
      return .argument (← readBindings bindings) (← readTarget target)
        remaining values (← readIndex position)
  | .expression [.symbol "petta-frame-sequence-v1", .expression remaining,
      .expression answers] => do
      return .sequence (← readControls remaining) answers
  | _ => none

@[simp] theorem readFrame_frameData (frame : Frame) :
    readFrame (frameData frame) = some frame := by
  cases frame <;> simp [frameData, readFrame]

private def readFrames (values : List Atom) : Option (List Frame) := values.mapM readFrame

@[simp] private theorem readFrames_map (frames : List Frame) :
    readFrames (frames.map frameData) = some frames := by
  induction frames with
  | nil => rfl
  | cons first rest ih => simp_all [readFrames]

def cellData : String × Option Atom → Atom
  | (name, none) => .expression [text name, .symbol "petta-cell-none-v1"]
  | (name, some value) =>
      .expression [text name, .expression [.symbol "petta-cell-some-v1", value]]

def readCell : Atom → Option (String × Option Atom)
  | .expression [.grounded (.string name), .symbol "petta-cell-none-v1"] =>
      some (name, none)
  | .expression [.grounded (.string name),
      .expression [.symbol "petta-cell-some-v1", value]] => some (name, some value)
  | _ => none

@[simp] private theorem readCell_cellData (cell : String × Option Atom) :
    readCell (cellData cell) = some cell := by
  rcases cell with ⟨name, value⟩
  cases value <;> rfl

def readCells (values : List Atom) : Option (List (String × Option Atom)) :=
  values.mapM readCell

@[simp] theorem readCells_map (cells : List (String × Option Atom)) :
    readCells (cells.map cellData) = some cells := by
  induction cells with
  | nil => rfl
  | cons first rest ih => simp_all [readCells]

def readSpace : Atom → Option (List Atom)
  | .expression values => some values
  | _ => none

def readSpaces (values : List Atom) : Option (List (List Atom)) :=
  values.mapM readSpace

@[simp] theorem readSpaces_map (spaces : List (List Atom)) :
    readSpaces (spaces.map Atom.expression) = some spaces := by
  induction spaces with
  | nil => rfl
  | cons first rest ih => simp_all [readSpaces, readSpace]

/-- Finite store fields; cell support remains explicit representation evidence. -/
def stateData (state : State) (names : List String) : Atom :=
  .expression [.symbol "petta-store-v1", .expression state.core,
    .expression (state.spacesPrefix.map Atom.expression),
    .expression ((state.cellRows names).map cellData)]

def readState : Atom → Option State
  | .expression [.symbol "petta-store-v1", .expression core,
      .expression spaces, .expression cells] => do
      return reconstruct core [] (← readSpaces spaces) (← readCells cells)
  | _ => none

theorem readState_stateData (state : State) (names : List String)
    (vacant : EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    readState (stateData state names) = some state := by
  simp only [stateData, readState, readSpaces_map, readCells_map]
  simpa using congrArg some (reconstruct_exact state [] names vacant covers)

def configurationData (configuration : Configuration) (names : List String) : Atom :=
  .expression [.symbol "petta-configuration-v1", stateData configuration.state names,
    controlData configuration.control, .expression (configuration.frames.map frameData),
    .expression configuration.input, .expression configuration.output]

def readConfiguration : Atom → Option Configuration
  | .expression [.symbol "petta-configuration-v1", state, control, .expression frames,
      .expression input, .expression output] => do
      return ⟨← readState state, ← readControl control, ← readFrames frames, input, output⟩
  | _ => none

theorem readConfiguration_configurationData (configuration : Configuration)
    (names : List String) (vacant : EmptyTail configuration.state [])
    (covers : ∀ name, name ∉ names → configuration.state.cells name = none) :
    readConfiguration (configurationData configuration names) = some configuration := by
  simp only [configurationData, readConfiguration,
    readState_stateData _ _ vacant covers, readControl_controlData, readFrames_map]
  rfl

/-- Existing ground-data codec protects all guest variables from Pattern binding. -/
def encode (configuration : Configuration) (names : List String) : Pattern :=
  OSLFCore.Bridge.GroundData.encode (configurationData configuration names)

def decode (pattern : Pattern) : Option Configuration := do
  readConfiguration (← OSLFCore.Bridge.GroundData.decode pattern)

theorem decode_encode (configuration : Configuration) (names : List String)
    (vacant : EmptyTail configuration.state [])
    (covers : ∀ name, name ∉ names → configuration.state.cells name = none) :
    decode (encode configuration names) = some configuration := by
  simp [decode, encode, readConfiguration_configurationData configuration names vacant covers]

theorem encode_isGround (configuration : Configuration) (names : List String) :
    (encode configuration names).isGround = true :=
  OSLFCore.Bridge.GroundData.encode_isGround _

theorem encode_checked (configuration : Configuration) (names : List String)
    (free : Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext)
    (bound : List Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr) :
    Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType
      OSLFCore.Bridge.GroundData.dataLanguage free bound
        (encode configuration names) (.base "GroundAtom") = true :=
  OSLFCore.Bridge.GroundData.encode_checked _ free bound

theorem encoded_equal_implies_configuration_equal
    (first second : Configuration) (firstNames secondNames : List String)
    (firstVacant : EmptyTail first.state []) (secondVacant : EmptyTail second.state [])
    (firstCovers : ∀ name, name ∉ firstNames → first.state.cells name = none)
    (secondCovers : ∀ name, name ∉ secondNames → second.state.cells name = none)
    (same : encode first firstNames = encode second secondNames) : first = second := by
  have decoded := congrArg decode same
  rw [decode_encode first firstNames firstVacant firstCovers,
    decode_encode second secondNames secondVacant secondCovers] at decoded
  exact Option.some.inj decoded

theorem loaded_configuration_representable (program : Program) (control : Control)
    (frames : List Frame) (input output : List Atom) :
    decode (encode ⟨Effects.loaded program, control, frames, input, output⟩ []) =
      some ⟨Effects.loaded program, control, frames, input, output⟩ := by
  apply decode_encode
  · exact Effects.loaded_empty_tail program
  · intro name _
    rfl

theorem completed_configuration_representable
    (program : Program) (initialControl : Control)
    (initialFrames : List Frame) (initialInput initialOutput : List Atom)
    (after : State) (answers finalInput finalOutput : List Atom)
    (running : DeclarativeSpec.Runs program
      ⟨Effects.loaded program, initialControl, initialFrames, initialInput, initialOutput⟩
      (.complete after answers finalInput finalOutput)) :
    ∃ names, decode (encode ⟨after, .returned answers, [], finalInput, finalOutput⟩ names) =
      some ⟨after, .returned answers, [], finalInput, finalOutput⟩ := by
  obtain ⟨names, covers⟩ := DeclarativeSpec.completed_finite_cells running
    (Effects.loaded_finite_cells program)
  exact ⟨names, decode_encode _ names
    (DeclarativeSpec.completed_empty_tail running (Effects.loaded_empty_tail program)) covers⟩

/-- Only the actual cell-writing primitive adds a name to the support. -/
def primitiveCellSupport (head : String) (arguments : List Atom) (names : List String) :
    List String :=
  match head, arguments with
  | "change-state!", [.symbol name, _] => name :: names
  | _, _ => names

theorem primitiveCellSupport_of_not_writer (head : String) (arguments : List Atom)
    (names : List String) (notWriter : head ≠ "change-state!") :
    primitiveCellSupport head arguments names = names := by
  unfold primitiveCellSupport
  split <;> simp_all

/-- A failed primitive has not allocated a cell-support entry. -/
theorem failed_primitive_support {state : State} {head : String}
    {arguments : List Atom} {reason : Effects.Fault} (names : List String)
    (failed : StdLib.apply state head arguments = .error reason) :
    primitiveCellSupport head arguments names = names := by
  unfold primitiveCellSupport
  split
  · simp_all [StdLib.apply]
  · rfl

theorem primitiveCellSupport_contains (head : String) (arguments : List Atom)
    (names : List String) {name : String} (member : name ∈ names) :
    name ∈ primitiveCellSupport head arguments names := by
  unfold primitiveCellSupport
  split <;> simp_all

theorem successful_primitive_support {state after : State} {head : String}
    {arguments answers : List Atom} (names : List String)
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (returned : StdLib.apply state head arguments = .ok (after, answers)) :
    ∀ name, name ∉ primitiveCellSupport head arguments names → after.cells name = none := by
  rcases StdLib.successful_apply_cell_update returned with same |
    ⟨writtenName, value, rfl, rfl, rfl⟩
  · intro name absent
    rw [same]
    apply covers name
    exact fun member => absent (primitiveCellSupport_contains head arguments names member)
  · intro other absent
    have missing : other ≠ writtenName ∧ other ∉ names := by
      simpa [primitiveCellSupport] using absent
    rw [cell_read_other state writtenName other value missing.1]
    exact covers other missing.2

/-- A computable support update determined by the existing source control. -/
def cellSupportAfter (configuration : Configuration) (names : List String) : List String :=
  match configuration.control with
  | .arguments _ (.function head) [] arguments _ =>
      primitiveCellSupport head arguments names
  | _ => names

theorem cellSupportAfter_contains (configuration : Configuration) (names : List String)
    {name : String} (member : name ∈ names) :
    name ∈ cellSupportAfter configuration names := by
  unfold cellSupportAfter
  split
  · exact primitiveCellSupport_contains _ _ _ member
  · exact member

private theorem cover_enlarged (state : State) (names more : List String)
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (contains : ∀ name, name ∈ names → name ∈ more) :
    ∀ name, name ∉ more → state.cells name = none := by
  intro name absent
  exact covers name (fun member => absent (contains name member))

theorem transition_support {program : Program} {source target : Configuration}
    (names : List String) (covers : ∀ name, name ∉ names → source.state.cells name = none)
    (transition : DeclarativeSpec.Transition program source target) :
    ∀ name, name ∉ cellSupportAfter source names → target.state.cells name = none := by
  cases transition
  all_goals first
    | exact cover_enlarged _ _ _ covers (fun _ member => cellSupportAfter_contains _ _ member)
    | have updated := successful_primitive_support names covers (by assumption)
      simpa only [cellSupportAfter, (by assumption : source.control = _)] using updated

theorem transition_representation {program : Program} {source target : Configuration}
    (names : List String) (vacant : EmptyTail source.state [])
    (covers : ∀ name, name ∉ names → source.state.cells name = none)
    (transition : DeclarativeSpec.Transition program source target) :
    decode (encode target (cellSupportAfter source names)) = some target :=
  decode_encode target _ (DeclarativeSpec.transition_empty_tail vacant transition)
    (transition_support names covers transition)

theorem path_support {program : Program} {source target : Configuration}
    (names : List String) (vacant : EmptyTail source.state [])
    (covers : ∀ name, name ∉ names → source.state.cells name = none)
    (path : Relation.ReflTransGen (DeclarativeSpec.Transition program) source target) :
    ∃ finalNames : List String, EmptyTail target.state [] ∧
      (∀ name, name ∉ finalNames → target.state.cells name = none) := by
  induction path with
  | refl => exact ⟨names, vacant, covers⟩
  | @tail middle target _ transition ih =>
      obtain ⟨previousNames, previousVacant, previousCovers⟩ := ih
      exact ⟨cellSupportAfter middle previousNames,
        DeclarativeSpec.transition_empty_tail previousVacant transition,
        transition_support previousNames previousCovers transition⟩

theorem loaded_path_representable {program : Program} {source target : Configuration}
    (initial : source.state = Effects.loaded program)
    (path : Relation.ReflTransGen (DeclarativeSpec.Transition program) source target) :
    ∃ names, decode (encode target names) = some target := by
  have vacant : EmptyTail source.state [] := by
    rw [initial]
    exact Effects.loaded_empty_tail program
  have covers : ∀ name, name ∉ ([] : List String) → source.state.cells name = none := by
    intro name _
    rw [initial]
    rfl
  obtain ⟨names, targetVacant, targetCovers⟩ := path_support [] vacant covers path
  exact ⟨names, decode_encode target names targetVacant targetCovers⟩

theorem primitive_support_write (names : List String) (name : String) (value : Atom) :
    primitiveCellSupport "change-state!" [.symbol name, value] names = name :: names := rfl

theorem primitive_support_other (names : List String) (name : String) :
    primitiveCellSupport "get-state" [.symbol name] names = names := rfl

theorem omitted_cell_support_loses_cell (name : String) (value : Atom) :
    readState (stateData (Effects.empty.putCell name value) []) ≠
      some (Effects.empty.putCell name value) := by
  have decoded : readState (stateData (Effects.empty.putCell name value) []) =
      some Effects.empty := rfl
  rw [decoded]
  intro same
  have cells := congrArg (fun state : State => state.cells name) (Option.some.inj same)
  simp [Effects.empty, new, putCell] at cells

theorem malformed_configuration_refused :
    readConfiguration (.expression [.symbol "petta-configuration-v1"]) = none := rfl

theorem negative_argument_index_refused (bindings : Subst) (target : Target)
    (remaining values : List Atom) :
    readControl (.expression [.symbol "petta-control-arguments-v1", bindingsData bindings,
      targetData target, .expression remaining, .expression values, .grounded (.int (-1))]) =
      none := by
  simp [readControl, readIndex]

theorem pattern_variable_refused (name : String) : decode (.fvar name) = none := by
  simp [decode, OSLFCore.Bridge.GroundData.pattern_variable_rejected]

theorem controlData_injective : Function.Injective controlData := by
  intro first second same
  have decoded := congrArg readControl same
  simpa using decoded

theorem frameData_injective : Function.Injective frameData := by
  intro first second same
  have decoded := congrArg readFrame same
  simpa using decoded

theorem fault_is_not_empty_answers (reason : Fault) :
    controlData (.fault reason) ≠ controlData (.returned []) := by
  intro same
  have controls := controlData_injective same
  cases controls

theorem false_is_not_empty_answers :
    controlData (.returned [Effects.boolean false]) ≠ controlData (.returned []) := by
  intro same
  have controls := controlData_injective same
  cases controls

theorem symbol_is_not_nullary_expression (bindings : Subst) (name : String) :
    controlData (.evaluate bindings (.symbol name)) ≠
      controlData (.evaluate bindings (.expression [.symbol name])) := by
  intro same
  have controls := controlData_injective same
  cases controls

theorem named_cell_configuration_representable (name : String) (value : Atom)
    (control : Control) (frames : List Frame) (input output : List Atom) :
    decode (encode ⟨Effects.empty.putCell name value, control, frames, input, output⟩ [name]) =
      some ⟨Effects.empty.putCell name value, control, frames, input, output⟩ := by
  apply decode_encode
  · exact putCell_emptyTail Effects.empty_empty_tail _ _
  · intro other missing
    have different : other ≠ name := by simpa using missing
    rw [cell_read_other Effects.empty name other value different]
    rfl

end Mettapedia.Languages.MeTTa.PeTTa.ConfigurationEncoding
