import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompiler
import Mathlib.Data.List.ReduceOption
import Std.Data.String.ToInt

/-! The preparer's definitions are the proved program. The emitted text is
the rendering of the machine followed by the port; the source reader reads
it back as exactly that program. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompiler

open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics (Program Equation FormKind collect loadedAtoms)
open Lean (Json)
open SourceCompilerProtocol (entryValid)

/-- A form `collect` files as a declaration. -/
def DeclarationShape (atom : Atom) : Prop := ∃ name type, atom = .expression [.symbol ":", name, type]

/-- A form `collect` files as neither an equation nor a declaration. -/
def FactShape (atom : Atom) : Prop :=
  (∀ head arguments body, atom ≠ .expression [.symbol "=", .expression (.symbol head :: arguments), body]) ∧
    ∀ name type, atom ≠ .expression [.symbol ":", name, type]

theorem collect_go :
    ∀ (kinds : List FormKind) (equations : List Equation) (declarations facts : List Atom),
      kinds.count .equation = equations.length → kinds.count .declaration = declarations.length →
      kinds.count .fact = facts.length →
      (∀ declaration ∈ declarations, DeclarationShape declaration) → (∀ fact ∈ facts, FactShape fact) →
      collect (loadedAtoms.go kinds equations declarations facts) =
        .ok { equations, declarations, facts, layout := kinds }
  | [], equations, declarations, facts, equationCount, declarationCount, factCount, _, _ => by
    have noEquations : equations = [] := List.eq_nil_of_length_eq_zero (by simpa using equationCount.symm)
    have noDeclarations : declarations = [] := List.eq_nil_of_length_eq_zero (by simpa using declarationCount.symm)
    have noFacts : facts = [] := List.eq_nil_of_length_eq_zero (by simpa using factCount.symm)
    subst noEquations noDeclarations noFacts
    rfl
  | .equation :: kinds, equations, declarations, facts, equationCount, declarationCount, factCount,
      declared, factual => by
    cases equations with
    | nil => simp at equationCount
    | cons equation rest =>
      simp only [List.count_cons_self, List.length_cons, Nat.add_right_cancel_iff] at equationCount
      have declarationCount' : kinds.count .declaration = declarations.length := by
        simpa [List.count_cons] using declarationCount
      have factCount' : kinds.count .fact = facts.length := by simpa [List.count_cons] using factCount
      simp only [loadedAtoms.go, collect, Equation.toAtom,
        collect_go kinds rest declarations facts equationCount declarationCount' factCount' declared factual,
        bind, Except.bind]
  | .declaration :: kinds, equations, declarations, facts, equationCount, declarationCount, factCount,
      declared, factual => by
    cases declarations with
    | nil => simp at declarationCount
    | cons declaration rest =>
      simp only [List.count_cons_self, List.length_cons, Nat.add_right_cancel_iff] at declarationCount
      have equationCount' : kinds.count .equation = equations.length := by
        simpa [List.count_cons] using equationCount
      have factCount' : kinds.count .fact = facts.length := by simpa [List.count_cons] using factCount
      obtain ⟨name, type, rfl⟩ := declared declaration List.mem_cons_self
      simp only [loadedAtoms.go, collect,
        collect_go kinds equations rest facts equationCount' declarationCount factCount'
          (fun other member => declared other (List.mem_cons_of_mem _ member)) factual,
        bind, Except.bind]
  | .fact :: kinds, equations, declarations, facts, equationCount, declarationCount, factCount,
      declared, factual => by
    cases facts with
    | nil => simp at factCount
    | cons fact rest =>
      simp only [List.count_cons_self, List.length_cons, Nat.add_right_cancel_iff] at factCount
      have equationCount' : kinds.count .equation = equations.length := by
        simpa [List.count_cons] using equationCount
      have declarationCount' : kinds.count .declaration = declarations.length := by
        simpa [List.count_cons] using declarationCount
      obtain ⟨notEquation, notDeclaration⟩ := factual fact List.mem_cons_self
      simp only [loadedAtoms.go, collect,
        collect_go kinds equations declarations rest equationCount' declarationCount' factCount declared
          (fun other member => factual other (List.mem_cons_of_mem _ member)),
        bind, Except.bind]

/-- Collecting a balanced program's loaded forms gives the program back. -/
theorem collect_loadedAtoms (program : Program) (balanced : SpaceSemantics.Balanced program)
    (declared : ∀ declaration ∈ program.declarations, DeclarationShape declaration)
    (factual : ∀ fact ∈ program.facts, FactShape fact) :
    collect (loadedAtoms program) = .ok { program with initializers := [] } := by
  obtain ⟨equations, declarations, facts⟩ := balanced
  have collected := collect_go program.layout program.equations program.declarations program.facts
    equations declarations facts declared factual
  simpa only [loadedAtoms] using collected

theorem loadedAtoms_go_shapes :
    ∀ (kinds : List FormKind) (equations : List Equation) (declarations facts : List Atom) (atom : Atom),
      atom ∈ loadedAtoms.go kinds equations declarations facts →
        (∃ equation ∈ equations, atom = equation.toAtom) ∨ atom ∈ declarations ∨ atom ∈ facts
  | .equation :: kinds, equation :: equations, declarations, facts, atom, member => by
    simp only [loadedAtoms.go, List.mem_cons] at member
    rcases member with rfl | later
    · exact .inl ⟨equation, List.mem_cons_self, rfl⟩
    · rcases loadedAtoms_go_shapes kinds equations declarations facts atom later with
        ⟨found, inside, same⟩ | inDeclarations | inFacts
      · exact .inl ⟨found, List.mem_cons_of_mem _ inside, same⟩
      · exact .inr (.inl inDeclarations)
      · exact .inr (.inr inFacts)
  | .declaration :: kinds, equations, declaration :: declarations, facts, atom, member => by
    simp only [loadedAtoms.go, List.mem_cons] at member
    rcases member with rfl | later
    · exact .inr (.inl List.mem_cons_self)
    · rcases loadedAtoms_go_shapes kinds equations declarations facts atom later with
        found | inDeclarations | inFacts
      · exact .inl found
      · exact .inr (.inl (List.mem_cons_of_mem _ inDeclarations))
      · exact .inr (.inr inFacts)
  | .fact :: kinds, equations, declarations, fact :: facts, atom, member => by
    simp only [loadedAtoms.go, List.mem_cons] at member
    rcases member with rfl | later
    · exact .inr (.inr List.mem_cons_self)
    · rcases loadedAtoms_go_shapes kinds equations declarations facts atom later with
        found | inDeclarations | inFacts
      · exact .inl found
      · exact .inr (.inl inDeclarations)
      · exact .inr (.inr (List.mem_cons_of_mem _ inFacts))
  | [], _, _, _, _, member => by simp [loadedAtoms.go] at member
  | .equation :: _, [], _, _, _, member => by simp [loadedAtoms.go] at member
  | .declaration :: _, _, [], _, _, member => by simp [loadedAtoms.go] at member
  | .fact :: _, _, _, [], _, member => by simp [loadedAtoms.go] at member

theorem machine_shape : SpaceSemantics.Balanced CHRMachineSource.source.program ∧
    CHRMachineSource.source.program.declarations = [] ∧ CHRMachineSource.source.program.facts = [] ∧
    CHRMachineSource.source.program.initializers = [] := by
  refine ⟨CHRMachineExecution.machine_balanced, ?_, ?_, ?_⟩ <;> decide +kernel

theorem prepared_balanced (entry : String) (program : CHR.Program) (seeds : List CHR.Constraint) :
    SpaceSemantics.Balanced (preparedProgram entry program seeds) := by
  obtain ⟨⟨equations, declarations, facts⟩, _, _, _⟩ := machine_shape
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [preparedProgram, SpaceSemantics.Program.append, CHRMachineExecution.portProgramFor, List.count_append,
      equations, declarations, facts]

/-- **The emitted definitions are the prepared program.** When the preparer
renders them, the source reader reads exactly the machine followed by the
port. -/
theorem definitions_read (entry : String) (program : CHR.Program) (seeds : List CHR.Constraint) (text : String)
    (rendered : definitions? entry program seeds = some text) :
    SpaceSemantics.readProgram text = .ok (preparedProgram entry program seeds) := by
  obtain ⟨_, noDeclarations, noFacts, noInitializers⟩ := machine_shape
  have declared : ∀ declaration ∈ (preparedProgram entry program seeds).declarations,
      DeclarationShape declaration := by
    intro declaration member
    simp only [preparedProgram, SpaceSemantics.Program.append, noDeclarations, List.nil_append,
      CHRMachineExecution.portProgramFor, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
  have factual : ∀ fact ∈ (preparedProgram entry program seeds).facts, FactShape fact := by
    intro fact member
    simp [preparedProgram, SpaceSemantics.Program.append, noFacts, CHRMachineExecution.portProgramFor] at member
  have expressions : ReadAfterRender.AllExpressions (loadedAtoms (preparedProgram entry program seeds)) := by
    intro atom member
    rcases loadedAtoms_go_shapes _ _ _ _ atom member with ⟨equation, _, rfl⟩ | inDeclarations | inFacts
    · exact ⟨_, rfl⟩
    · obtain ⟨name, type, rfl⟩ := declared atom inDeclarations
      exact ⟨_, rfl⟩
    · exact absurd inFacts (by
        simp [preparedProgram, SpaceSemantics.Program.append, noFacts, CHRMachineExecution.portProgramFor])
  rw [ReadAfterRender.read_render rendered expressions,
    collect_loadedAtoms _ (prepared_balanced entry program seeds) declared factual]
  have initial : (preparedProgram entry program seeds).initializers = [] := by
    simp [preparedProgram, SpaceSemantics.Program.append, noInitializers, CHRMachineExecution.portProgramFor]
  cases prepared : preparedProgram entry program seeds
  rw [prepared] at initial
  simp only at initial
  subst initial
  rfl

theorem append_assoc (first second third : Program) :
    (first.append second).append third = first.append (second.append third) := by
  simp only [Program.append, List.append_assoc]

/-- **The lang path loads the proved runtime.** The definitions emitted for
the lang library's `lang:compiled` entry, read and loaded over the machine's
base, are exactly the port runtime whose `begin`, `advance` and `outcome`
`CHRMachineExecution.port_runs` proves against the refined CHR relation. -/
theorem definitions_runtime (program : CHR.Program) (seeds : List CHR.Constraint) (text : String)
    (rendered : definitions? "lang:compiled" program seeds = some text) :
    (SpaceSemantics.readProgram text).map (CHRMachineSource.library.base.append ·) =
      .ok (CHRMachineExecution.portRuntime (CHR.Machine.table program) (seeds.map CHR.Constraint.asHead)
        ticksPerUnit) := by
  rw [definitions_read "lang:compiled" program seeds text rendered]
  change Except.ok (CHRMachineSource.library.base.append (preparedProgram "lang:compiled" program seeds)) = _
  rw [preparedProgram, CHRMachineExecution.portProgramFor_compiled, ← append_assoc]
  rfl

/-! ## What a successful preparation establishes -/

theorem c0Values_length : ∀ (shapes : List HostShape) (values : List CHR.Value),
    c0Values? shapes = .ok values → values.length = shapes.length
  | [], values, decoded => by
    simp only [c0Values?, pure, Except.pure, Except.ok.injEq] at decoded
    subst decoded
    rfl
  | first :: rest, values, decoded => by
    simp only [c0Values?, bind, Except.bind] at decoded
    cases one : c0Value? first with
    | error message => simp [one] at decoded
    | ok value =>
      cases others : c0Values? rest with
      | error message => simp [one, others] at decoded
      | ok rest' =>
        simp only [one, others, pure, Except.pure, Except.ok.injEq] at decoded
        subst decoded
        simp [c0Values_length rest rest' others]

/-- A captured row is a declared constraint. -/
theorem captureRow_declared (program : CHR.Program) (row : HostShape) (constraint : CHR.Constraint)
    (captured : captureRow program row = .ok (some constraint)) :
    declared program constraint.name constraint.arguments.length = true := by
  have fromArguments : ∀ (name : String) (arguments : List HostShape),
      declared program name arguments.length = true →
      (do pure (some ⟨name, ← c0Values? arguments⟩) : Except String (Option CHR.Constraint)) =
        .ok (some constraint) →
      declared program constraint.name constraint.arguments.length = true := by
    intro name arguments known produced
    cases decoded : c0Values? arguments with
    | error message => simp [decoded, bind, Except.bind] at produced
    | ok values =>
      simp only [decoded, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at produced
      subst produced
      simp only [c0Values_length arguments values decoded]
      exact known
  unfold captureRow at captured
  split at captured
  · split at captured
    · exact fromArguments _ _ (by assumption) captured
    · simp [pure, Except.pure] at captured
  · split at captured
    · exact fromArguments _ _ (by assumption) captured
    · simp [pure, Except.pure] at captured
  · split at captured
    · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at captured
      subst captured
      assumption
    · simp [pure, Except.pure] at captured
  · split at captured
    · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at captured
      subst captured
      assumption
    · simp [pure, Except.pure] at captured
  · simp [pure, Except.pure] at captured

theorem mapM_ok_mem {α β ε : Type} (f : α → Except ε β) :
    ∀ (inputs : List α) (outputs : List β), inputs.mapM f = .ok outputs →
      ∀ output ∈ outputs, ∃ input ∈ inputs, f input = .ok output
  | [], outputs, mapped => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at mapped
    subst mapped
    intro output member
    simp at member
  | first :: rest, outputs, mapped => by
    rw [List.mapM_cons] at mapped
    cases one : f first with
    | error message => simp [one, bind, Except.bind] at mapped
    | ok value =>
      cases others : rest.mapM f with
      | error message => simp [one, others, bind, Except.bind] at mapped
      | ok values =>
        simp only [one, others, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at mapped
        subst mapped
        intro output member
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨first, List.mem_cons_self, one⟩
        · obtain ⟨input, inside, same⟩ := mapM_ok_mem f rest values others output later
          exact ⟨input, List.mem_cons_of_mem _ inside, same⟩

/-- Every captured constraint is declared. -/
theorem capture_declared (program : CHR.Program) (rows : List HostShape) (captured : List (Nat × CHR.Constraint))
    (taken : capture program rows = .ok captured) :
    ∀ entry ∈ captured, declared program entry.2.name entry.2.arguments.length = true := by
  unfold capture at taken
  simp only [bind, Except.bind] at taken
  split at taken
  · cases taken
  · rename_i results mapped
    simp only [pure, Except.pure, Except.ok.injEq] at taken
    subst taken
    intro entry member
    rw [List.reduceOption_mem_iff] at member
    obtain ⟨⟨row, ordinal⟩, _, produced⟩ := mapM_ok_mem _ _ _ mapped (some entry) member
    obtain ⟨entryOrdinal, entryConstraint⟩ := entry
    simp only at produced
    cases row' : captureRow program row with
    | error message => simp [row'] at produced
    | ok option =>
      cases option with
      | none => simp [row', pure, Except.pure] at produced
      | some constraint =>
        simp [row', pure, Except.pure] at produced
        obtain ⟨rfl, rfl⟩ := produced
        exact captureRow_declared program row constraint row'

/-- **What a successful preparation establishes.** A ready preparation
decoded an admitted program, every seed it posts (captured, then queried) is
declared, and its definitions are the rendering of the machine followed by
the port of that program and those seeds. -/
theorem prepareRun_ready (wire rows entry : String) (lowered : CHRPrologLowering.Program)
    (captured : List (Nat × CHR.Constraint)) (definitions : String)
    (ready : prepareRun wire rows entry = .ok (.ready lowered captured definitions)) :
    program? wire = .ok lowered ∧ CHR.Admission.diagnose lowered.program = none ∧
      (∀ constraint ∈ seedsOf lowered captured,
        declared lowered.program constraint.name constraint.arguments.length = true) ∧
      definitions? entry lowered.program (seedsOf lowered captured) = some definitions ∧
      ∃ shapes, captured? rows = .ok shapes ∧ capture lowered.program shapes = .ok captured := by
  unfold prepareRun at ready
  by_cases valid : entryValid entry = true
  · rw [dif_pos valid] at ready
    cases read : program? wire with
    | error message => simp [read, bind, Except.bind] at ready
    | ok decoded =>
      cases admitted : CHR.Admission.diagnose decoded.program with
      | some reason => simp [read, admitted, bind, Except.bind] at ready
      | none =>
        cases inputs : decoded.inputs.all
            (fun constraint => declared decoded.program constraint.name constraint.arguments.length)
        · simp [read, admitted, inputs, bind, Except.bind] at ready
        · cases shaped : captured? rows with
          | error message => simp [read, admitted, inputs, shaped, bind, Except.bind] at ready
          | ok shapes =>
            cases taken : capture decoded.program shapes with
            | error message =>
              simp [read, admitted, inputs, shaped, taken, bind, Except.bind] at ready
            | ok taken' =>
              simp [read, admitted, inputs, shaped, taken, bind, Except.bind, pure, Except.pure] at ready
              obtain ⟨sameProgram, sameCaptured, sameText⟩ := ready
              subst sameProgram
              subst sameCaptured
              subst sameText
              refine ⟨rfl, admitted, ?_, (Option.some_get _).symm, shapes, rfl, taken⟩
              intro constraint member
              rcases List.mem_append.mp member with fromCapture | fromQuery
              · obtain ⟨entry, inside, rfl⟩ := List.mem_map.mp fromCapture
                exact capture_declared _ _ _ taken entry inside
              · exact List.all_eq_true.mp inputs constraint fromQuery
  · rw [dif_neg valid] at ready
    cases ready

/-! ## The host transport is lossless

Every C0 value has one host form: integers, symbols for the names a host
symbol carries, strings for the others, and expressions for tuples. The
observer's records of that form decode, through the capture decoders, to
exactly the value. -/

mutual
  /-- The host form of a C0 value. -/
  def hostValue : CHR.Value → HostShape
    | .integer number => .integer number
    | .atom name => if hostSymbolSupported name then .symbol name else .string name
    | .tuple fields => .expression (hostValues fields)
  def hostValues : List CHR.Value → List HostShape
    | [] => []
    | first :: rest => hostValue first :: hostValues rest
end

mutual
  /-- Tuple nesting depth, the decoder's fuel. -/
  def valueDepth : CHR.Value → Nat
    | .tuple fields => valuesDepth fields + 1
    | _ => 0
  def valuesDepth : List CHR.Value → Nat
    | [] => 0
    | first :: rest => max (valueDepth first) (valuesDepth rest)
end

mutual
  theorem c0Value_hostValue : ∀ value : CHR.Value, c0Value? (hostValue value) = .ok value
    | .integer _ => rfl
    | .atom name => by
      by_cases supported : hostSymbolSupported name = true
      · simp [hostValue, supported, c0Value?, pure, Except.pure]
      · simp [hostValue, supported, c0Value?, pure, Except.pure]
    | .tuple fields => by
      simp only [hostValue, c0Value?, c0Values_hostValues fields]
      rfl
  theorem c0Values_hostValues : ∀ values : List CHR.Value, c0Values? (hostValues values) = .ok values
    | [] => rfl
    | first :: rest => by
      simp only [hostValues, c0Values?, c0Value_hostValue first, c0Values_hostValues rest]
      rfl
end

/-- Distinct C0 values have distinct host forms. -/
theorem hostValue_injective {first second : CHR.Value} (same : hostValue first = hostValue second) :
    first = second := by
  have decoded := c0Value_hostValue first
  rw [same, c0Value_hostValue second] at decoded
  exact (Except.ok.inj decoded).symm

theorem nameJson_shape (name : String) (fuel : Nat) :
    hostShape? (fuel + 1) (nameJson name) =
      some (if hostSymbolSupported name then .symbol name else .string name) := by
  unfold nameJson
  split <;> rfl

mutual
  theorem hostShape_valueJson : ∀ (value : CHR.Value) (fuel : Nat), valueDepth value ≤ fuel →
      hostShape? (fuel + 1) (valueJson value) = some (hostValue value)
    | .integer number, fuel, _ => by
      show HostShape.integer <$> number.repr.toInt? = some (HostShape.integer number)
      rw [Int.toInt?_repr]
      rfl
    | .atom name, fuel, _ => by
      simp only [valueJson, hostValue]
      exact nameJson_shape name fuel
    | .tuple fields, fuel + 1, deep => by
      have inner : valuesDepth fields ≤ fuel := by simp only [valueDepth] at deep; omega
      show HostShape.expression <$> (valuesJson fields).toArray.toList.mapM (hostShape? (fuel + 1)) =
        some (HostShape.expression (hostValues fields))
      rw [List.toList_toArray, hostShape_valuesJson fields fuel inner]
      rfl
    | .tuple fields, 0, deep => by simp [valueDepth] at deep
  theorem hostShape_valuesJson : ∀ (values : List CHR.Value) (fuel : Nat), valuesDepth values ≤ fuel →
      (valuesJson values).mapM (hostShape? (fuel + 1)) = some (hostValues values)
    | [], _, _ => rfl
    | first :: rest, fuel, deep => by
      have bounds : valueDepth first ≤ fuel ∧ valuesDepth rest ≤ fuel := by
        simp only [valuesDepth] at deep; omega
      simp only [valuesJson, hostValues, List.mapM_cons, hostShape_valueJson first fuel bounds.1,
        hostShape_valuesJson rest fuel bounds.2]
      rfl
end

/-- **Lossless transport.** The observer's record of a value decodes, through
the capture decoders, to that value. -/
theorem value_transport (value : CHR.Value) (fuel : Nat) (deep : valueDepth value ≤ fuel) :
    ((hostShape? (fuel + 1) (valueJson value)).map c0Value?) = some (.ok value) := by
  rw [hostShape_valueJson value fuel deep]
  simp [c0Value_hostValue]

theorem hostValues_length : ∀ values : List CHR.Value, (hostValues values).length = values.length
  | [] => rfl
  | _ :: rest => by simp [hostValues, hostValues_length rest]

/-- A published constraint, captured again, is the same declared constraint. -/
theorem constraint_transport (program : CHR.Program) (constraint : CHR.Constraint) (fuel : Nat)
    (deep : valuesDepth constraint.arguments ≤ fuel)
    (known : declared program constraint.name constraint.arguments.length = true) :
    ((hostShape? (fuel + 2) (constraintJson constraint)).map (captureRow program)) =
      some (.ok (some constraint)) := by
  obtain ⟨name, values⟩ := constraint
  simp only at deep known
  have head := nameJson_shape name fuel
  have arguments := hostShape_valuesJson values fuel deep
  have shaped : hostShape? (fuel + 2) (constraintJson ⟨name, values⟩) = some (.expression
      ((if hostSymbolSupported name then .symbol name else .string name) :: hostValues values)) := by
    show HostShape.expression <$> (nameJson name :: valuesJson values).toArray.toList.mapM
      (hostShape? (fuel + 1)) = _
    rw [List.toList_toArray, List.mapM_cons, head, arguments]
    rfl
  rw [shaped]
  by_cases supported : hostSymbolSupported name = true
  · simp [supported, captureRow, hostValues_length, known, c0Values_hostValues, bind, Except.bind, pure,
      Except.pure]
  · simp [supported, captureRow, hostValues_length, known, c0Values_hostValues, bind, Except.bind, pure,
      Except.pure]

/-! Examples: the host form of names. -/

example : hostValue (.atom "word") = .symbol "word" := by
  simp [hostValue, show hostSymbolSupported "word" = true by decide_cbv]
example : hostValue (.atom "True") = .string "True" := by
  simp [hostValue, show hostSymbolSupported "True" = false by decide_cbv]
example : hostValue (.atom "") = .string "" := by
  simp [hostValue, show hostSymbolSupported "" = false by decide_cbv]
example : (c0Value? (.string "True")).toOption = some (.atom "True") := by
  simp [c0Value?, pure, Except.pure, Except.toOption]
/-- Input spelling is flexible even when output has a canonical form. -/
theorem c0Value_string (text : String) : c0Value? (.string text) = .ok (.atom text) := rfl


/-- Canonicalize a host observation, without mutating any captured occurrence. -/
def normalizeHost (shape : HostShape) : Except String HostShape :=
  (c0Value? shape).map hostValue

theorem atom_input_spellings (name : String) :
    c0Value? (.symbol name) = c0Value? (.string name) := rfl

/-- Choosing a canonical host spelling preserves the guest interpretation. -/
theorem normalizeHost_preserves (shape : HostShape) :
    (normalizeHost shape >>= c0Value?) = c0Value? shape := by
  cases decoded : c0Value? shape with
  | error reason => simp [normalizeHost, decoded, Except.map, bind, Except.bind]
  | ok value => simp [normalizeHost, decoded, c0Value_hostValue, Except.map, bind, Except.bind]

/-- Normalizing the representation twice has the same result as once.
This is a codec law, not idempotence of running a CHR program twice. -/
theorem normalizeHost_idempotent (shape : HostShape) :
    (normalizeHost shape >>= normalizeHost) = normalizeHost shape := by
  cases decoded : c0Value? shape with
  | error reason => simp [normalizeHost, decoded, Except.map, bind, Except.bind]
  | ok value => simp [normalizeHost, decoded, c0Value_hostValue, Except.map, bind, Except.bind]

#print axioms normalizeHost_preserves
#print axioms normalizeHost_idempotent

example : (c0Value? (.string "word")).toOption = some (.atom "word") := by
  simp [c0Value?, pure, Except.pure, Except.toOption]

#print axioms definitions_read
#print axioms definitions_runtime
#print axioms prepareRun_ready
#print axioms value_transport
#print axioms constraint_transport
#print axioms hostValue_injective

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompiler
