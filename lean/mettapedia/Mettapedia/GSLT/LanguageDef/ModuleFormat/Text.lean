import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CettaWireAtom
import Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender

/-!
# Portable module text through the shared MeTTa reader

The source is a data declaration `(module:document payload)`. Ordinary symbols,
quoted strings, natural numbers and constructor applications keep their MeTTa
spellings. Strings use the shared Unicode-preserving literal codec; unsafe
symbols and constructor heads are escaped without interpreting them as code.

Lexing, S-expression parsing and atom reading are the existing verified reader.
The decoder below runs on its actual result, and rejects commands or additional
declarations. It does not invoke the renderer. This canonical data surface is
distinct from the historical BNFC and upstream Rust theory-builder grammars.
It supplies textual transport, not execution authority or a claim that those
other grammars have been implemented.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.Text

open Mettapedia.GSLT.LanguageDef.CettaWire (Term encodeList decodeList decodeList_encodeList)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

mutual
  def atom? : Atom → Option Term
    | .symbol name => some (.symbol name)
    | .grounded (.string value) => some (.string value)
    | .grounded (.int (.ofNat value)) => some (.natural value)
    | .expression (.symbol head :: arguments) =>
        .application head <$> atoms? arguments
    | _ => none

  def atoms? : List Atom → Option (List Term)
    | [] => some []
    | first :: rest => do pure ((← atom? first) :: (← atoms? rest))
end

mutual
  @[simp] theorem atom_encode (value : Term) :
      atom? (CettaWireAtom.encode value) = some value := by
    cases value with
    | symbol name => rfl
    | string value => rfl
    | natural value => rfl
    | application head arguments =>
        simp only [CettaWireAtom.encode, atom?, atoms_encode arguments]
        rfl

  @[simp] theorem atoms_encode (values : List Term) :
      atoms? (CettaWireAtom.encodeMany values) = some values := by
    cases values with
    | nil => rfl
    | cons first rest =>
        simp only [CettaWireAtom.encodeMany, atoms?, atom_encode first, atoms_encode rest]
        rfl
end

private def codepoint? : Term → Option Char
  | .natural value =>
      if (Char.ofNat value).toNat = value then some (Char.ofNat value) else none
  | _ => none

/-- Every Unicode string has an ordinary quoted spelling. Codepoint lists
remain a readable data representation, but are not required for printing. -/
def string (value : String) : Term := .string value

def string? : Term → Option String
  | .string value => some value
  | .application "module:codepoints" [characters] =>
      String.ofList <$> decodeList codepoint? characters
  | _ => none

@[simp] theorem string_roundtrip (value : String) : string? (string value) = some value := by
  rfl

private def reserved (head : String) : Bool :=
  ["module:codepoints", "module:symbol", "module:application"].contains head

mutual
  def escape : Term → Term
    | .symbol name =>
        if ReadAfterRender.symbolSafe name then .symbol name
        else .application "module:symbol" [string name]
    | .string value => string value
    | .natural value => .natural value
    | .application head arguments =>
        if ReadAfterRender.symbolSafe head && !reserved head then
          .application head (escapeMany arguments)
        else .application "module:application" [string head, escapeList arguments]

  def escapeMany : List Term → List Term
    | [] => []
    | first :: rest => escape first :: escapeMany rest

  def escapeList : List Term → Term
    | [] => .symbol "LNil"
    | first :: rest => .application "LCons" [escape first, escapeList rest]
end

mutual
  def unescape? : Term → Option Term
    | .symbol name => some (.symbol name)
    | .string value => some (.string value)
    | .natural value => some (.natural value)
    | .application head arguments =>
        if head = "module:codepoints" then
          .string <$> string? (.application head arguments)
        else if head = "module:symbol" then
          match arguments with
          | [name] => .symbol <$> string? name
          | _ => none
        else if head = "module:application" then
          match arguments with
          | [head, arguments] => do
              pure (.application (← string? head) (← unescapeList? arguments))
          | _ => none
        else .application head <$> unescapeMany? arguments
  termination_by value => sizeOf value

  def unescapeMany? : List Term → Option (List Term)
    | [] => some []
    | first :: rest => do pure ((← unescape? first) :: (← unescapeMany? rest))
  termination_by values => sizeOf values

  def unescapeList? : Term → Option (List Term)
    | .symbol "LNil" => some []
    | .application "LCons" [first, rest] => do
        pure ((← unescape? first) :: (← unescapeList? rest))
    | _ => none
  termination_by value => sizeOf value
end

private theorem unescape_string (value : String) :
    unescape? (string value) = some (.string value) := by
  simp [string, unescape?]

mutual
  @[simp] theorem unescape_escape (value : Term) :
      unescape? (escape value) = some value := by
    cases value with
    | symbol name =>
        simp only [escape]
        split <;> simp [unescape?]
    | string value => exact unescape_string value
    | natural value => simp [escape, unescape?]
    | application head arguments =>
        simp only [escape]
        split
        next safe =>
          have notReserved : reserved head = false := by
            cases h : reserved head <;> simp_all
          have different : head ≠ "module:codepoints" ∧ head ≠ "module:symbol" ∧
              head ≠ "module:application" := by
            simpa [reserved, List.contains_cons, List.contains_nil] using notReserved
          unfold unescape?
          simp [different.1, different.2.1, different.2.2,
            unescapeMany_escapeMany arguments]
        next => simp [unescape?, unescapeList_escapeList arguments]
  termination_by sizeOf value

  @[simp] theorem unescapeMany_escapeMany (values : List Term) :
      unescapeMany? (escapeMany values) = some values := by
    cases values with
    | nil => simp [escapeMany, unescapeMany?]
    | cons first rest =>
        simp [escapeMany, unescapeMany?, unescape_escape first, unescapeMany_escapeMany rest]
  termination_by sizeOf values

  @[simp] theorem unescapeList_escapeList (values : List Term) :
      unescapeList? (escapeList values) = some values := by
    cases values with
    | nil => simp [escapeList, unescapeList?]
    | cons first rest =>
        simp [escapeList, unescapeList?, unescape_escape first, unescapeList_escapeList rest]
  termination_by sizeOf values
end

private def Printable (value : Term) : Prop :=
  (ReadAfterRender.chars? (CettaWireAtom.encode value)).isSome = true

private theorem printable_symbol (name : String)
    (safe : ReadAfterRender.symbolSafe name = true) : Printable (.symbol name) := by
  simp [Printable, CettaWireAtom.encode, ReadAfterRender.chars?, safe]

private theorem printable_natural (value : Nat) : Printable (.natural value) := rfl

private theorem printable_arguments (values : List Term)
    (valid : ∀ value ∈ values, Printable value) :
    (ReadAfterRender.charsList? (CettaWireAtom.encodeMany values)).isSome = true := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      have head := valid first (by simp)
      have tail := ih (fun value member => valid value (by simp [member]))
      unfold Printable at head
      cases firstChars : ReadAfterRender.chars? (CettaWireAtom.encode first) <;>
        cases restChars : ReadAfterRender.charsList? (CettaWireAtom.encodeMany rest) <;>
        simp_all [CettaWireAtom.encodeMany, ReadAfterRender.charsList?]

private theorem printable_application (head : String) (arguments : List Term)
    (safe : ReadAfterRender.symbolSafe head = true)
    (valid : ∀ value ∈ arguments, Printable value) : Printable (.application head arguments) := by
  have children := printable_arguments arguments valid
  cases parts : ReadAfterRender.charsList? (CettaWireAtom.encodeMany arguments) <;>
    simp_all [Printable, CettaWireAtom.encode, ReadAfterRender.chars?, ReadAfterRender.charsList?]

private theorem printable_string (value : String) : Printable (string value) := rfl

mutual
  private theorem escape_printable (value : Term) : Printable (escape value) := by
    cases value with
    | symbol name =>
        simp only [escape]
        split
        next safe => exact printable_symbol name safe
        next =>
          apply printable_application "module:symbol" _ (by decide)
          intro item member
          rcases List.mem_singleton.mp member with rfl
          exact printable_string name
    | string value => exact printable_string value
    | natural value => exact printable_natural value
    | application head arguments =>
        simp only [escape]
        split
        next safe =>
          simp only [Bool.and_eq_true] at safe
          apply printable_application head _ safe.1
          exact escapeMany_printable arguments
        next =>
          apply printable_application "module:application" _ (by decide)
          intro item member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact printable_string head
          · exact escapeList_printable arguments
  termination_by sizeOf value

  private theorem escapeMany_printable (values : List Term) :
      ∀ value ∈ escapeMany values, Printable value := by
    cases values with
    | nil => simp [escapeMany]
    | cons first rest =>
        intro value member
        simp only [escapeMany, List.mem_cons] at member
        rcases member with rfl | member
        · exact escape_printable first
        · exact escapeMany_printable rest value member
  termination_by sizeOf values

  private theorem escapeList_printable (values : List Term) : Printable (escapeList values) := by
    cases values with
    | nil => exact printable_symbol "LNil" (by decide)
    | cons first rest =>
        apply printable_application "LCons" _ (by decide)
        intro value member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact escape_printable first
        · exact escapeList_printable rest
  termination_by sizeOf values
end

def document (value : Term) : Atom :=
  .expression [.symbol "module:document", CettaWireAtom.encode (escape value)]

private def program (value : Term) : SpaceSemantics.Program :=
  { equations := [], declarations := [], facts := [document value], layout := [.fact] }

/-- Rendering uses the ordinary, independently implemented MeTTa text renderer. -/
def render? (value : Term) : Option String := ReadAfterRender.renderProgram? (program value)

/-- Reading is inert: a command or an extra form cannot be hidden in a module. -/
def read? (source : String) : Option Term := do
  let parsed ← (SpaceSemantics.readProgram source).toOption
  if !parsed.initializers.isEmpty || !parsed.equations.isEmpty || !parsed.declarations.isEmpty then none
  else match parsed.facts with
    | [.expression [.symbol "module:document", payload]] => do
        unescape? (← atom? payload)
    | _ => none

theorem render_defined (value : Term) : (render? value).isSome = true := by
  have printable : Printable (.application "module:document" [escape value]) := by
    apply printable_application _ _ (by decide)
    intro item member
    rcases List.mem_singleton.mp member with rfl
    exact escape_printable value
  change (ReadAfterRender.chars? (document value)).isSome = true at printable
  change ((ReadAfterRender.charsList? [document value]).map _).isSome = true
  cases chars : ReadAfterRender.chars? (document value) <;>
    simp_all [ReadAfterRender.charsList?]

/-- Canonical module text exists for every finite physical value, including
Unicode, quote and newline payloads. -/
def render (value : Term) : String := (render? value).get (render_defined value)

@[simp] theorem render_eq_some (value : Term) : render? value = some (render value) :=
  (Option.some_get (render_defined value)).symm

theorem read_render_of_some (value : Term) (source : String)
    (rendered : render? value = some source) : read? source = some value := by
  have parsed := ReadAfterRender.read_render rendered (by
    simp [program, SpaceSemantics.loadedAtoms, SpaceSemantics.loadedAtoms.go,
      ReadAfterRender.AllExpressions, document])
  change SpaceSemantics.readProgram source = .ok (program value) at parsed
  simp [read?, parsed, program, document, Except.toOption]


@[simp] theorem read_render (value : Term) : read? (render value) = some value :=
  read_render_of_some value _ (render_eq_some value)

theorem render_injective : Function.Injective render := by
  intro first second same
  have := congrArg read? same
  simpa only [read_render, Option.some.injEq] using this

/-- UTF-8 validation precedes the source lexer; malformed byte sequences are
never replaced by a repair character. -/
def readBytes? (bytes : ByteArray) : Option Term := do
  read? (← String.fromUTF8? bytes)

def renderBytes (value : Term) : ByteArray := (render value).toUTF8

@[simp] theorem readBytes_renderBytes (value : Term) :
    readBytes? (renderBytes value) = some value := by
  have utf8 (source : String) : String.fromUTF8? source.toUTF8 = some source := by
    rw [String.toUTF8_eq_toByteArray]
    simp only [String.fromUTF8?, dif_pos source.isValidUTF8]
    cases source
    rfl
  unfold readBytes? renderBytes
  rw [utf8]
  exact read_render value

end Mettapedia.GSLT.LanguageDef.ModuleFormat.Text
