import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionReference
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogCorePrinter
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSelectedReader
import Mettapedia.Languages.Datalog.IRCodec
import Mettapedia.Languages.Datalog.NumericSpelling
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-! The shared packed reader's semantic constructor packet is interpreted
once into independent Datalog IR. Source constructors remain in the frontend.
Full source readback is checked before semantic projection. The basic numeric
profile admits decimal, binary and hexadecimal integers and rejects floating
values explicitly. -/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.Frontend

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog
abbrev SourceAtom := Mettapedia.Languages.MeTTa.OSLFCore.Atom

def sourceText? : Pattern → Option String
  | source@(.apply label _) => do
      let declaration ← SourceViews.grammar.terms.find? (·.label == label)
      CorePrinter.printText? declaration.category source
  | _ => none

def escape? : Pattern → Option Char
  | .apply "dl-src:escape-quote" [] => some '"'
  | .apply "dl-src:escape-apostrophe" [] => some '\''
  | .apply "dl-src:escape-slash" [] => some '\\'
  | .apply "dl-src:escape-bell" [] => some (Char.ofNat 7)
  | .apply "dl-src:escape-backspace" [] => some (Char.ofNat 8)
  | .apply "dl-src:escape-formfeed" [] => some (Char.ofNat 12)
  | .apply "dl-src:escape-newline" [] => some '\n'
  | .apply "dl-src:escape-return" [] => some '\r'
  | .apply "dl-src:escape-tab" [] => some '\t'
  | .apply "dl-src:escape-vertical-tab" [] => some (Char.ofNat 11)
  | _ => none

def symbolBody? : Pattern → Option (List Char)
  | .apply "dl-src:symbol-empty" [] => some []
  | .apply "dl-src:symbol-body" [head,tail] => do
      let text ← CorePrinter.printText? "DlStringScalar" head
      let [character] := text.toList | none
      pure (character :: (← symbolBody? tail))
  | .apply "dl-src:symbol-escape" [head,tail] => do
      let character ← escape? head
      pure (character :: (← symbolBody? tail))
  | _ => none

def value? (label : String) (source : Pattern) : Option Pattern := do
  match label,source with
  | "SymbolValue",.apply "dl-src:symbol" [body] =>
      pure (IRCodec.value (.symbol (String.ofList (← symbolBody? body))))
  | "IntegerValue",_ =>
      let spelling ← sourceText? source
      let value ← NumericSpelling.readInteger? spelling
      if Value.fits64 (.number value) then
        some (IRCodec.value (.number value)) else none
  | "UnsignedValue",_ =>
      let spelling ← sourceText? source
      let value ← NumericSpelling.readUnsigned? spelling
      if Value.fits64 (.unsigned value) then
        some (IRCodec.value (.unsigned value)) else none
  | _,_ => none

def qualifiedName? : Pattern → Option QualifiedName
  | .apply "dl-src:qualified-name-one" [identifier] => do
      pure [← CorePrinter.printText? "DlIdentifier" identifier]
  | .apply "dl-src:qualified-name-more" [identifier,rest] => do
      pure ((← CorePrinter.printText? "DlIdentifier" identifier) :: (← qualifiedName? rest))
  | _ => none

mutual
  def normalize? : Pattern → Option Pattern
    | .apply "SymbolValue" [source] => value? "SymbolValue" source
    | .apply "IntegerValue" [source] => value? "IntegerValue" source
    | .apply "UnsignedValue" [source] => value? "UnsignedValue" source
    | .apply "FloatValue" _ => none
    | .apply "Relation" [source] => do
        pure (IRCodec.relation (← qualifiedName? source))
    | .apply "Variable" [source] => do
        let name ← sourceText? source
        pure (.apply "Variable" [IRCodec.atom name])
    | .apply "Attribute" [source,type] => do
        let name ← sourceText? source
        let kind ← normalize? type
        pure (.apply "Attribute" [IRCodec.atom name,kind])
    | .apply label children => Pattern.apply label <$> normalizeChildren? children
    | .collection .vec children none => do
        pure (.collection .vec (← normalizeChildren? children) none)
    | _ => none

  def normalizeChildren? : List Pattern → Option (List Pattern)
    | [] => some []
    | child :: rest => do pure ((← normalize? child) :: (← normalizeChildren? rest))
end

def selectedSource? (input : String) (tree : SourceAtom) : Bool :=
  (SelectedReader.core? input tree).isSome

def read (input : String) (packet : SourceAtom) : Except String Program := do
  let .expression [.symbol "result",tree,.symbol "nil"] := packet
    | .error "expected one explicitly selected whole-input parser result"
  let some source := SelectedReader.core? input tree
    | .error "source packet violates checked grammar or declared selection"
  let some projected := ProgramProjection.Reference.projectProgram? source
    | .error "source is outside the positive function-free grammar"
  let some normalized := normalize? projected
    | .error "literal is outside the symbol/integer/unsigned profile"
  let some program := IRCodec.program? normalized | .error "invalid independent program payload"
  pure program

theorem read_preserves_input (input : String) (tree : SourceAtom) (program : Program)
    (accepted : read input (.expression [.symbol "result",tree,.symbol "nil"]) = .ok program) :
    ∃ source, SelectedReader.core? input tree = some source ∧
      CorePrinter.printText? "DlProgram" source = some input := by
  cases decoded : SelectedReader.core? input tree with
  | none => simp [read, decoded] at accepted
  | some source => exact ⟨source, rfl, SelectedReader.core?_prints decoded⟩

theorem read_selectedSource (input : String) (tree : SourceAtom) (program : Program)
    (accepted : read input (.expression [.symbol "result",tree,.symbol "nil"]) = .ok program) :
    selectedSource? input tree = true := by
  obtain ⟨source, decoded, _⟩ := read_preserves_input input tree program accepted
  simp only [selectedSource?, decoded, Option.isSome_some]

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.Frontend
