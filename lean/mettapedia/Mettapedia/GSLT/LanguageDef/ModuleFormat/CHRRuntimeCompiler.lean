import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCompilerProtocol
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxNativePlan
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologFrontend
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologPrinter
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRProgramCodec
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRProgram
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachinePortExecution
import Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender
import Mettapedia.Languages.CHR.Operational

/-! Pure preparation for the ground CHR language package. Source reading,
captured-occurrence interpretation, preparation and final-store observation
are separate stages. These functions prepare MeTTa code and decode data;
the refined CHR execution itself runs in MeTTa, on the CHR machine of
`gslt_chr_machine.metta`, through the package port.

Posting order is the captured occurrences in their capture order, then the
source query in source order. The observation names the captured
occurrences that the run consumed and the final occurrences it created. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompiler

open Lean
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open SourceCompilerProtocol

/-- Lean creates some closed constants on first use. Forcing them during
provider initialization keeps them out of per-request allocation. -/
@[export cetta_chr_force_constants_v1]
def forceConstants (word : UInt64) : String :=
  toString (Int.ofNat word.toNat - Int.ofNat (2 ^ 70)) ++ toString ("-18446744073709551616".toInt?)

/-! ## Source reading -/

/-- The retained ambiguity policy: every selected whole-input interpretation
is read, and all of them must lower to the same independent IR. -/
def readProgram (source catalogue : String) : Except String CHRPrologLowering.Program := do
  let .ok [.expression (.symbol "SourceValuesV1" :: packets)] := SpaceSemantics.readSource catalogue
    | .error "expected the selected whole-input source catalogue"
  let readings ← packets.mapM fun packet => do
    let .expression [.symbol "result", tree, .symbol "nil"] := packet
      | .error "expected an explicitly selected whole-input parser result"
    (·.lowered) <$> CHRPrologFrontend.read source tree
  match readings with
  | [] => .error "no selected source interpretation"
  | first :: rest =>
    if rest.all (fun reading => decide (reading = first)) then pure first
    else .error "CHR source alternatives have different IR interpretations"

def groundArgument? : CHR.Term → Option CHR.Value
  | .value datum => some datum
  | _ => none

def groundConstraint? (head : CHR.Head) : Option CHR.Constraint := do
  pure ⟨head.name, ← head.arguments.mapM groundArgument?⟩

def programValue (lowered : CHRPrologLowering.Program) : Value :=
  CHRProgramCodec.node "ChrLangProgram" [CHRProgramCodec.program lowered.program,
    .list (lowered.inputs.map fun constraint => CHRProgramCodec.head constraint.asHead)]

def programOfValue? (value : Value) : Option CHRPrologLowering.Program := do
  let ("ChrLangProgram", [program, .list inputs]) ← CHRProgramCodec.node? value | none
  let program ← CHRProgramCodec.program? program
  let heads ← inputs.mapM CHRProgramCodec.head?
  pure ⟨program, ← heads.mapM groundConstraint?⟩

def program? (wire : String) : Except String CHRPrologLowering.Program := do
  let some program := programOfValue? (← SourceCompilerProtocol.value? wire)
    | .error "invalid CHR program payload"
  pure program

/-- The constraint names a capture selects. Arity is checked per occurrence. -/
def inputNames (program : CHR.Program) : List String :=
  (program.declarations.map (·.name)).eraseDups

def read (source catalogue _separator : String) : Except String Json := do
  let lowered ← readProgram source catalogue
  pure (Json.mkObj [
    ("program", .str (renderValue (programValue lowered))),
    ("canonical", .str (CHRPrologPrinter.program lowered.program lowered.inputs)),
    ("inputs", toJson (inputNames lowered.program))])

/-! ## Captured occurrences

The engine lends each selected occurrence as a structural record that keeps
its host kind. Integers and expressions denote integer and tuple values.
Symbols and strings are two input spellings of C0 atom names. Output chooses
one canonical host spelling; surviving captured occurrences are not rewritten. -/

/-- The established output codec uses string carriers for empty,
NUL-bearing and uppercase truth names. Input also accepts strings for ordinary
atom names; one canonical output does not restrict input to that image. -/
def hostSymbolSupported (name : String) : Bool :=
  !name.isEmpty && !name.contains '\u0000' && name != "True" && name != "False"

inductive HostShape where
  | symbol (name : String)
  | string (value : String)
  | integer (value : Int)
  | expression (items : List HostShape)
  | other (kind : String)
  deriving Repr

def hostShape? : Nat → Json → Option HostShape
  | 0, _ => none
  | fuel + 1, json =>
    match json.getObjVal? "symbol", json.getObjVal? "integer", json.getObjVal? "expression" with
    | .ok (.str name), _, _ => some (.symbol name)
    | _, .ok (.str digits), _ => HostShape.integer <$> digits.toInt?
    | _, _, .ok (.arr items) => HostShape.expression <$> items.toList.mapM (hostShape? fuel)
    | _, _, _ =>
      match json.getObjVal? "string" with
      | .ok (.str text) => some (.string text)
      | _ =>
      if (json.getObjVal? "bool").toOption.isSome then some (.other "Boolean")
      else if (json.getObjVal? "float").toOption.isSome then some (.other "float")
      else if (json.getObjVal? "variable").toOption.isSome then some (.other "variable")
      else match json.getObjVal? "grounded" with
        | .ok (.str kind) => some (.other kind)
        | _ => none

mutual
  def c0Value? : HostShape → Except String CHR.Value
    | .integer number => pure (.integer number)
    | .symbol name => pure (.atom name)
    | .string text => pure (.atom text)
    | .expression items => CHR.Value.tuple <$> c0Values? items
    | .other kind => .error s!"a C0 constraint argument is an integer, atom name (symbol or string), or tuple, not a {kind}"
  def c0Values? : List HostShape → Except String (List CHR.Value)
    | [] => pure []
    | first :: rest => do pure ((← c0Value? first) :: (← c0Values? rest))
end

def declared (program : CHR.Program) (name : String) (arity : Nat) : Bool :=
  program.declarations.any fun declaration => declaration.name == name && declaration.arity == arity

/-- Name and arity identify a constraint. Rows that declare no constraint are
not captured; a declared row with a non-C0 argument refuses the run. -/
def captureRow (program : CHR.Program) : HostShape → Except String (Option CHR.Constraint)
  | .expression (.symbol name :: arguments) =>
    if declared program name arguments.length then do
      pure (some ⟨name, ← c0Values? arguments⟩)
    else pure none
  | .expression (.string name :: arguments) =>
    if declared program name arguments.length then do
      pure (some ⟨name, ← c0Values? arguments⟩)
    else pure none
  | .symbol name =>
    if declared program name 0 then pure (some ⟨name, []⟩)
    else pure none
  | .string name =>
    if declared program name 0 then pure (some ⟨name, []⟩)
    else pure none
  | _ => pure none

/-- Captured constraints in capture order, each with its selection ordinal. -/
def capture (program : CHR.Program) (rows : List HostShape) :
    Except String (List (Nat × CHR.Constraint)) := do
  let read ← rows.zipIdx.mapM fun (row, ordinal) => do
    pure ((fun constraint => (ordinal, constraint)) <$> (← captureRow program row))
  pure read.reduceOption

def captured? (text : String) : Except String (List HostShape) := do
  let .arr rows ← Json.parse text | .error "expected an array of captured rows"
  let some shapes := rows.toList.mapM (hostShape? (text.length + 1))
    | .error "invalid captured row record"
  pure shapes

/-! ## Preparation

The prepared program is plain data for the refined CHR machine: for each
constraint key, its rule occurrences in the refined visit order, each with its
rule's heads, guards and ordered body. Integers are numbers, atoms are
strings and tuples are `ChrTuple` lists, so no guest value is read as a host
truth value or evaluated. -/

/-- Machine ticks per port unit; each tick is one bounded machine step. -/
def ticksPerUnit : Nat := 2000

/-- The program a prepared CHR program loads: the machine, then the port of
the program's occurrence table and seeds. -/
def preparedProgram (entry : String) (program : CHR.Program) (seeds : List CHR.Constraint) :
    SpaceSemantics.Program :=
  CHRMachineSource.source.program.append
    (CHRMachineExecution.portProgramFor entry (CHR.Machine.table program) (seeds.map CHR.Constraint.asHead)
      ticksPerUnit)

/-- The prepared program's source text. Every prepared program under a valid
entry prefix has one (`definitions?_isSome`). -/
def definitions? (entry : String) (program : CHR.Program) (seeds : List CHR.Constraint) : Option String :=
  ReadAfterRender.renderProgram? (preparedProgram entry program seeds)

/-! ## Entry names

An entry prefix that `entryValid` admits, followed by `:begin`, `:advance` or
`:outcome`, is a symbol the source reader keeps. -/

private theorem toNat_of_eq {c d : Char} (same : c = d) : c.toNat = d.toNat := by rw [same]

/-- The characters `entryValid` admits lie in printable ASCII, away from `;`
and `\`, and the first is a letter or `_`. -/
private theorem entryValid_chars {entry : String} (valid : entryValid entry = true) :
    ∃ first rest, entry.toList = first :: rest ∧ 65 ≤ first.toNat ∧
      ∀ c ∈ first :: rest, 45 ≤ c.toNat ∧ c.toNat ≤ 122 ∧ c.toNat ≠ 59 ∧ c.toNat ≠ 92 := by
  simp only [entryValid] at valid
  cases listed : entry.toList with
  | nil => rw [listed] at valid; exact absurd valid (by decide)
  | cons first rest =>
    rw [listed] at valid
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq, Char.le_def,
      UInt32.le_iff_toNat_le, beq_iff_eq] at valid
    obtain ⟨firstLetter, restCharacters⟩ := valid
    have first_range : 65 ≤ first.toNat ∧ first.toNat ≤ 122 ∧ first.toNat ≠ 59 ∧ first.toNat ≠ 92 := by
      rcases firstLetter with (⟨low, high⟩ | ⟨low, high⟩) | same
      · change 97 ≤ first.toNat at low; change first.toNat ≤ 122 at high; omega
      · change 65 ≤ first.toNat at low; change first.toNat ≤ 90 at high; omega
      · have := toNat_of_eq same; simp only [Char.reduceToNat] at this; omega
    refine ⟨first, rest, rfl, first_range.1, ?_⟩
    intro c member
    rcases List.mem_cons.mp member with rfl | later
    · omega
    · rcases restCharacters c later with
        ((((⟨low, high⟩ | ⟨low, high⟩) | same) | ⟨low, high⟩) | same) | same
      · change 97 ≤ c.toNat at low; change c.toNat ≤ 122 at high; omega
      · change 65 ≤ c.toNat at low; change c.toNat ≤ 90 at high; omega
      · have := toNat_of_eq same; simp only [Char.reduceToNat] at this; omega
      · change 48 ≤ c.toNat at low; change c.toNat ≤ 57 at high; omega
      · have := toNat_of_eq same; simp only [Char.reduceToNat] at this; omega
      · have := toNat_of_eq same; simp only [Char.reduceToNat] at this; omega

private theorem symbolChar_of_range {c : Char}
    (range : 45 ≤ c.toNat ∧ c.toNat ≤ 122 ∧ c.toNat ≠ 59 ∧ c.toNat ≠ 92) :
    ReadAfterRender.symbolChar c = true := by
  obtain ⟨low, high, notSemicolon, notBackslash⟩ := range
  simp only [ReadAfterRender.symbolChar, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  refine ⟨⟨⟨⟨⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
    intro same <;> have := toNat_of_eq same <;> simp only [Char.reduceToNat] at this <;> omega

private theorem decimalDigit_letter {c : Char} (letter : 65 ≤ c.toNat) :
    Mettapedia.GSLT.Parsing.ExactDecimalLexeme.decimalDigit? c = none := by
  unfold Mettapedia.GSLT.Parsing.ExactDecimalLexeme.decimalDigit?
  split <;> first | rfl | (simp only [Char.reduceToNat] at letter; omega)

private theorem parseInteger_letter {c : Char} (letter : 65 ≤ c.toNat) (tail : List Char) :
    Mettapedia.GSLT.Parsing.ExactDecimalLexeme.parseIntegerChars? (c :: tail) = none := by
  have notPlus : c ≠ '+' := fun same => by
    have := toNat_of_eq same; simp only [Char.reduceToNat] at this; omega
  have notMinus : c ≠ '-' := fun same => by
    have := toNat_of_eq same; simp only [Char.reduceToNat] at this; omega
  have notZero : c ≠ '0' := fun same => by
    have := toNat_of_eq same; simp only [Char.reduceToNat] at this; omega
  unfold Mettapedia.GSLT.Parsing.ExactDecimalLexeme.parseIntegerChars?
  split
  · rename_i heq; injection heq with h; exact absurd h notPlus
  · rename_i heq; injection heq with h; exact absurd h notMinus
  · unfold Mettapedia.GSLT.Parsing.ExactDecimalLexeme.parseUnsignedChars?
    split
    · rename_i heq; cases heq
    · rename_i heq; injection heq with h; exact absurd h notZero
    · rename_i heq; injection heq with h; exact absurd h notZero
    · simp [Mettapedia.GSLT.Parsing.ExactDecimalLexeme.parseDigits?, decimalDigit_letter letter]

/-- An entry prefix followed by a suffix of symbol characters that contains
`:` is a symbol the source reader keeps. -/
theorem entry_symbolSafe {entry suffix : String} (valid : entryValid entry = true)
    (colon : ':' ∈ suffix.toList) (plain : suffix.toList.all ReadAfterRender.symbolChar = true) :
    ReadAfterRender.symbolSafe (entry ++ suffix) = true := by
  obtain ⟨first, rest, listed, letter, characters⟩ := entryValid_chars valid
  have whole : (entry ++ suffix).toList = first :: (rest ++ suffix.toList) := by
    rw [String.toList_append, listed, List.cons_append]
  have notWord : ∀ word ∈ (["True", "true", "False", "false"] : List String), entry ++ suffix ≠ word := by
    intro word member same
    have inside : ':' ∈ (entry ++ suffix).toList := by
      rw [String.toList_append]; exact List.mem_append_right _ colon
    rw [same] at inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> exact absurd inside (by decide)
  unfold ReadAfterRender.symbolSafe Mettapedia.GSLT.Parsing.ExactDecimalLexeme.parseInteger?
  rw [whole]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_cons, List.all_append, Bool.not_eq_true',
    parseInteger_letter letter, Option.isNone_none, and_true]
  refine ⟨⟨⟨?_, ?_⟩, symbolChar_of_range (characters first List.mem_cons_self),
    List.all_eq_true.mpr fun c inside => symbolChar_of_range (characters c (List.mem_cons_of_mem _ inside)),
    plain⟩, ?_⟩
  · intro same; have := toNat_of_eq same; simp only [Char.reduceToNat] at this; omega
  · intro same; have := toNat_of_eq same; simp only [Char.reduceToNat] at this; omega
  · cases contained : (["True", "true", "False", "false"] : List String).contains (entry ++ suffix)
    · rfl
    · exact absurd rfl (notWord _ (List.contains_iff_mem.mp contained))

private theorem entrySuffixes : ∀ suffix ∈ [":begin", ":advance", ":outcome"],
    ':' ∈ suffix.toList ∧ suffix.toList.all ReadAfterRender.symbolChar = true := by
  decide

/-- **Every prepared program has source text.** The machine renders, and so
does the port of any program and seeds under a valid entry prefix. -/
theorem definitions?_isSome {entry : String} (valid : entryValid entry = true) (program : CHR.Program)
    (seeds : List CHR.Constraint) : (definitions? entry program seeds).isSome = true := by
  unfold definitions? preparedProgram
  rw [ReadAfterRender.renderProgram?_append CHRMachineExecution.machine_balanced]
  exact ⟨CHRMachineExecution.machine_renders, CHRMachineExecution.portProgramFor_renders _ _ _
    fun suffix member => entry_symbolSafe valid (entrySuffixes suffix member).1 (entrySuffixes suffix member).2⟩

def dictionaryValue (captured : List Nat) (queries : Nat) : Value :=
  CHRProgramCodec.node "ChrLangDictionary" [.list (captured.map fun ordinal => Value.integer ordinal), .integer queries]

structure Dictionary where
  captured : List Nat
  queries : Nat

def dictionary? (text : String) : Except String Dictionary := do
  let some ("ChrLangDictionary", [.list captured, queries]) :=
      CHRProgramCodec.node? (← SourceCompilerProtocol.value? text)
    | .error "invalid CHR result dictionary"
  let some captured := captured.mapM CHRProgramCodec.natural? | .error "invalid captured ordinals"
  let some queries := CHRProgramCodec.natural? queries | .error "invalid query count"
  pure ⟨captured, queries⟩

/-- What preparation produces: the decoded program, the captured occurrences
with their selection ordinals and the definitions text. -/
structure Preparation where
  ready ::
  lowered : CHRPrologLowering.Program
  captured : List (Nat × CHR.Constraint)
  definitions : String

/-- The seeds a prepared run posts: the captured occurrences in capture
order, then the source query in source order. -/
def seedsOf (lowered : CHRPrologLowering.Program) (captured : List (Nat × CHR.Constraint)) : List CHR.Constraint :=
  captured.map Prod.snd ++ lowered.inputs

def prepareRun (wire rows entry : String) : Except String Preparation :=
  if valid : entryValid entry = true then do
    let lowered ← program? wire
    -- The wire crosses the host boundary: admit only what the frontend admits.
    if let some reason := CHR.Admission.diagnose lowered.program then
      .error s!"C0 admission refused: {reprStr reason}"
    unless lowered.inputs.all (fun constraint => declared lowered.program constraint.name constraint.arguments.length) do
      .error "initial C0 constraint has no matching name/arity declaration"
    let captured ← capture lowered.program (← captured? rows)
    pure (.ready lowered captured ((definitions? entry lowered.program (seedsOf lowered captured)).get
      (definitions?_isSome valid _ _)))
  else .error "invalid execution entry prefix"

def prepare (wire rows _separator entry : String) : Except String Json := do
  let ⟨lowered, captured, definitions⟩ ← prepareRun wire rows entry
  pure (Json.mkObj [
    ("definitions", .str definitions),
    ("dictionary", .str (renderValue (dictionaryValue (captured.map Prod.fst) lowered.inputs.length))),
    ("entry", .str entry), ("captured", toJson (captured.map Prod.fst)),
    ("seedCount", toJson (seedsOf lowered captured).length)])

/-! ## Observation

The outcome is the machine's final status, store slots and seed identifiers,
read back as ordinary atoms. -/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

mutual
  /-- Nodes of an atom; decoding fuel. -/
  def atomSize : Atom → Nat
    | .expression items => 1 + atomsSize items
    | _ => 1
  def atomsSize : List Atom → Nat
    | [] => 1
    | first :: rest => atomSize first + atomsSize rest
end

def listAtoms? : Nat → Atom → Option (List Atom)
  | 0, _ => none
  | _ + 1, .symbol "ChrNil" => some []
  | fuel + 1, .expression [.symbol "ChrCons", first, rest] => (first :: ·) <$> listAtoms? fuel rest
  | _ + 1, _ => none

def natural? : Atom → Option Nat
  | .grounded (.int number) => if number < 0 then none else some number.toNat
  | _ => none

def machineValue? : Nat → Atom → Option CHR.Value
  | 0, _ => none
  | _ + 1, .grounded (.int number) => some (.integer number)
  | _ + 1, .grounded (.string name) => some (.atom name)
  | fuel + 1, .expression [.symbol "ChrTuple", fields] => do
    let items ← listAtoms? (fuel + 1) fields
    CHR.Value.tuple <$> items.mapM (machineValue? fuel)
  | _ + 1, _ => none

def occurrence? (fuel : Nat) (name : String) (arity : Nat) : Atom → Option (Nat × CHR.Constraint)
  | .expression [.symbol "ChrOcc", id, values] => do
    let items ← listAtoms? fuel values
    let arguments ← items.mapM (machineValue? fuel)
    if arguments.length == arity then pure (← natural? id, ⟨name, arguments⟩) else none
  | _ => none

def slot? (fuel : Nat) : Atom → Option (List (Nat × CHR.Constraint))
  | .expression [.symbol "ChrSlot", .expression [.symbol "ChrKey", .grounded (.string name), arity], occurrences] => do
    let arity ← natural? arity
    (← listAtoms? fuel occurrences).mapM (occurrence? fuel name arity)
  | _ => none

/-- An atom name in its host form: a symbol, or a string for the names no
host symbol can hold. -/
def nameJson (name : String) : Json :=
  if hostSymbolSupported name then Json.mkObj [("symbol", .str name)] else Json.mkObj [("string", .str name)]

mutual
  def valueJson : CHR.Value → Json
    | .integer number => Json.mkObj [("integer", .str (toString number))]
    | .atom name => nameJson name
    | .tuple fields => Json.mkObj [("expression", .arr (valuesJson fields).toArray)]
  def valuesJson : List CHR.Value → List Json
    | [] => []
    | first :: rest => valueJson first :: valuesJson rest
end

def constraintJson (constraint : CHR.Constraint) : Json :=
  Json.mkObj [("expression", .arr (nameJson constraint.name :: valuesJson constraint.arguments).toArray)]

/-- Captured occurrence `ordinal` survives exactly when its CHR identifier is
in the final store; final occurrences with no captured identifier are new. -/
def consumed (captured : List (Nat × Nat)) (final : List (Nat × CHR.Constraint)) : List Nat :=
  captured.filterMap fun (ordinal, id) => if (final.map Prod.fst).contains id then none else some ordinal

def additions (captured : List (Nat × Nat)) (final : List (Nat × CHR.Constraint)) :
    List (Nat × CHR.Constraint) :=
  final.filter fun (id, _) => !(captured.map Prod.snd).contains id

/-- The complete observation: the final constraints ordered by identifier,
and the publication that consumes the captured occurrences that are gone and
adds the occurrences that are new. -/
def completeJson (dictionary : Dictionary) (posted : List Nat) (ordered : List (Nat × CHR.Constraint)) : Json :=
  let captured := dictionary.captured.zip (posted.take dictionary.captured.length)
  Json.mkObj [("status", .str "complete"),
    ("values", .arr (ordered.map fun entry => constraintJson entry.2).toArray),
    ("publication", Json.mkObj [("kind", .str "transform"), ("mode", .str "multiset"),
      ("consume", toJson (consumed captured ordered)),
      ("additions", .arr ((additions captured ordered).map fun entry => constraintJson entry.2).toArray)])]

/-- A completed run's observation from its decoded store and its posted
identifiers, after the checks a completed run must pass. -/
def completeObservation (lowered : CHRPrologLowering.Program) (dictionary : Dictionary)
    (stored : List (Nat × CHR.Constraint)) (seedIds : List Nat) : Except String Json :=
  let ordered := stored.mergeSort fun first second => first.1 ≤ second.1
  if seedIds.length ≠ dictionary.captured.length + dictionary.queries then
    .error "a completed run must have posted every seed"
  else if ¬ (ordered.map Prod.fst).Nodup then .error "final store identifiers are not distinct"
  else if ¬ ordered.all (fun entry => declared lowered.program entry.2.name entry.2.arguments.length) then
    .error "final store holds an undeclared constraint"
  else .ok (completeJson dictionary seedIds ordered)

/-- The observation of the machine's result atom. -/
def observeResult (lowered : CHRPrologLowering.Program) (dictionary : Dictionary) : Atom → Except String Json
  | .expression [.symbol "ChrMachineResult", status, store, seeds] => do
    let fuel := atomSize store + atomSize seeds + 1
    match status with
    | .symbol "ChrFailed" => pure (Json.mkObj [("status", .str "failed")])
    | .expression [.symbol "ChrFaulted", reason] =>
      pure (Json.mkObj [("status", .str "fault"), ("reason", .str reason.toString)])
    | .symbol "ChrComplete" =>
      let some slots := listAtoms? fuel store | .error "invalid final store"
      let some decoded := slots.mapM (slot? fuel) | .error "invalid final occurrence"
      let some seedAtoms := listAtoms? fuel seeds | .error "invalid seed identifiers"
      let some seedIds := seedAtoms.mapM natural? | .error "invalid seed identifiers"
      completeObservation lowered dictionary decoded.flatten seedIds
    | _ => .error "invalid CHR outcome phase"
  | _ => .error "invalid CHR outcome payload"

def observe (wire dictionary data _separator : String) : Except String Json := do
  let lowered ← program? wire
  let dictionary ← dictionary? dictionary
  let .ok [result] := SpaceSemantics.readSource data | .error "invalid CHR outcome payload"
  observeResult lowered dictionary result

/-! ## Package components -/

structure Components where
  sourceSyntax : Value
  core : Value
  parserPlan : Value
  execution : Value
  deriving DecidableEq

def compilerRecord (uri : String) : Value := .record [
  ("resource", .string uri), ("verify", .string "verify"), ("read", .string "read"),
  ("prepare", .string "prepare"), ("observe", .string "observe"), ("namespaceSeparator", .string ":")]

def executionRecord : Value := .record [("profile", .string "prepared-port-v1"),
  ("language", .string "petta"), ("hostProfile", .string "extended"),
  ("observation", .string "final-constraint-multiset")]

def components : Except String Components := do
  let description := CHRPrologSyntax.description
  let some plan := SourceSyntaxExport.plan? description | .error "source parser compilation failed"
  let lines := fun terms => String.intercalate "\n" (SourceSyntaxNativePlan.canonicalRows terms) ++ "\n"
  let parserPlan : Value := .record [
    ("productions", .string (lines (SourceSyntaxNativePlan.productions plan))),
    ("classes", .string (lines (plan.lexical.classes.flatMap SourceSyntaxExport.classClauses))),
    ("start", .string (SourceSyntaxExport.state plan.lexical.startSort).render),
    ("selection", .string ((CettaWire.Term.application "source-selection-v1"
      [CettaWire.encodeList SourceSyntaxNativePlan.directFilter CHRPrologSyntax.selection]).render))]
  pure ⟨(Portable.syntaxExport "syntax" description).spec,
    Value.Wire.quoteTerm (Portable.coreCodec.encode CHRProgram.language), parserPlan, executionRecord⟩

def compilerCompatible (compiler : Value) : Bool :=
  match compiler with
  | .record fields => match Value.field? fields "resource" with
    | some (.string uri) => decide (compiler = compilerRecord uri)
    | _ => false
  | _ => false

def admitComponents (supplied : Components) (compiler : Value) : Except String Components := do
  let expected ← components
  if compilerCompatible compiler && decide (supplied = expected) then .ok expected
  else .error "source, core, parser plan or execution does not match this compiler"

@[export cetta_chr_admit_v1]
def nativeAdmit (source core plan execution compiler : String) : String :=
  let result := do
    let supplied : Components := ⟨← SourceCompilerProtocol.value? source, ← SourceCompilerProtocol.value? core,
      ← SourceCompilerProtocol.value? plan, ← SourceCompilerProtocol.value? execution⟩
    admitComponents supplied (← SourceCompilerProtocol.value? compiler)
  match result with
  | .ok _ => "SourceBindingAcceptedV1"
  | .error reason => answer (.error reason)

/-- The package's compiler when CeTTa runs ground CHR in MeTTa: libraries
shipped beside the package (paths relative to it) and their entry functions.
No native provider is involved. -/
private def specifierName : Mettapedia.Logic.Prolog.ReaderOperator.Specifier → String
  | .fx => "fx" | .fy => "fy" | .xf => "xf" | .yf => "yf"
  | .xfx => "xfx" | .xfy => "xfy" | .yfx => "yfx"

/-- A MeTTa string literal for an operator name: only `"` and `\` need escapes. -/
private def mettaString (name : String) : String :=
  "\"" ++ String.join (name.toList.map fun c =>
    if c = '"' then "\\\"" else if c = '\\' then "\\\\" else c.toString) ++ "\""

/-- The source profile's operator table as MeTTa equations. Packet labels
`pl:apply:N` index this table: `(c0:operator N) = (name specifier priority)`. -/
def operatorDefinitions : String :=
  String.intercalate "\n" (CHRPrologSyntax.profile.operators.zipIdx.map fun (op, index) =>
    s!"(= (c0:operator {index}) ({mettaString op.name} {specifierName op.specifier} {op.priority.value}))") ++ "\n"

/-- The grammar's layout labels: `(c0:layout? LABEL)` holds exactly for them,
since layout nodes carry no meaning. -/
def layoutDefinition : String :=
  let labels := (CHRPrologSyntax.description.grammar.terms.filter (·.category == "PlLayout")).map (·.label)
  "(= (c0:layout? $label)\n   (case $label (" ++
    String.join (labels.map fun label => s!"({label} True) ") ++ "($other False))))\n"

/-- MeTTa definitions generated from the package's own syntax profile. They
travel in the package beside the grammar they describe. -/
def profileDefinitions : String := operatorDefinitions ++ layoutDefinition

/-- A compiler written in MeTTa and shipped beside the package. The package
carries the definitions generated from its own syntax profile; the
libraries are ordinary MeTTa in the engine. -/
def mettaCompilerRecord : Value := .record [
  ("kind", .string "metta-v1"),
  ("definitions", .string profileDefinitions),
  ("libraries", .string "chr/reader.metta chr/lowering.metta chr/compiler.metta chr/machine.metta"),
  ("read", .string "c0:compiler-read"), ("inputs", .string "c0:compiler-inputs"),
  ("prepare", .string "c0:compiler-prepare"), ("observe", .string "c0:compiler-observe"),
  ("namespaceSeparator", .string ":")]

/-- A closed module/1 package with the given compiler record. -/
def packageWith (compiler : Value) : Except String Json := do
  let bound ← components
  let envelope : RawModule := ⟨"CHR", [], [
    ⟨"syntax", bound.sourceSyntax⟩, ⟨"parserPlan", bound.parserPlan⟩, ⟨"core", bound.core⟩,
    ⟨"compiler", compiler⟩, ⟨"execution", bound.execution⟩,
    ⟨"regions", .record [("preferredRawFenceDepth", .integer 1)]⟩]⟩
  let some checked := decode? upstreamLimits (encodeRaw envelope) | .error "invalid package envelope"
  pure (Json.mkObj [("module", .str ("(module:document " ++
    CettaWireData.render (Value.Wire.encode (encodeRaw checked.val)) ++ ")"))])

/-- The package for the native provider; the compiler URI is relative to the package. -/
def package (compilerURI : String) : Except String Json := packageWith (compilerRecord compilerURI)

/-- The package CeTTa ships: ground CHR read, prepared and observed in MeTTa. -/
def mettaPackage : Except String Json := packageWith mettaCompilerRecord

@[export cetta_chr_package_v1]
def nativePackage (compilerURI : String) : String := answer (package compilerURI)

@[export cetta_chr_read_v1]
def nativeRead (source catalogue separator : String) : String := answer (read source catalogue separator)

@[export cetta_chr_verify_v1]
def nativeVerify (source packet forest identity allowance : String) : String :=
  answer (verifySource CHRPrologSyntax.description CHRPrologSyntax.selection source packet forest identity allowance)

@[export cetta_chr_prepare_v1]
def nativePrepare (wire rows separator entry : String) : String := answer (prepare wire rows separator entry)

@[export cetta_chr_observe_v1]
def nativeObserve (wire dictionary data separator : String) : String :=
  answer (observe wire dictionary data separator)

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompiler
