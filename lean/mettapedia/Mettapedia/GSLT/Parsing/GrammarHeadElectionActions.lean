import Mettapedia.GSLT.Parsing.GrammarHeadElection
import Mettapedia.GSLT.Parsing.MeTTaAtomConstruction

/-!
# Typed actions from grammar-derived head-election plans

This module compiles a structural head-election plan to the existing typed
MeTTa-atom construction algebra.  It is grammar-generic: language-specific
content is confined to a leaf/notation policy.  Compilation fails when a
plan attempts an invalid child access, crosses a semantic sort without a
declared conversion, or requests an unlicensed structural quotient.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GrammarHeadElectionActions

open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted
open GrammarHeadElection
open MeTTaAtomConstruction
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- Declared conversions from grammar text leaves to host atoms. -/
inductive TextAtomMode where
  | symbol
  | string
  | tagged (head : String)
  | prefixedSymbol (prefixText : String)
  | reject
  deriving DecidableEq, Repr

inductive ChainMode where
  | nested
  | reject
  deriving DecidableEq, Repr

/-- The authored part of the generic compiler: category-level leaf policy
and notation for fixed structural heads.  It contains no production index or
production body. -/
structure Policy where
  textAtomMode : String → TextAtomMode
  fixedAtom : String → Atom
  chainMode : ChainMode

def asciiPolicy : Policy where
  textAtomMode := fun _ => .symbol
  fixedAtom := .symbol
  chainMode := .reject

/-- Locate one exact typed child.  Out-of-range and kind-mismatched lookups
fail; there is no default value or fallback slot. -/
def variableAt? : (context : List Kind) → (index : Nat) → (kind : Kind) →
    Option (ConstructionVariable context kind)
  | [], _, _ => none
  | actual :: _, 0, expected =>
      if same : actual = expected then
        match same with
        | rfl => some .here
      else none
  | _ :: rest, index + 1, expected =>
      (variableAt? rest index expected).map .there

def inputAt? (context : List Kind) (index : Nat) (kind : Kind) :
    Option (Action context kind) :=
  (variableAt? context index kind).map .input

def fixedText {context : List Kind} (text : String) : Action context .text :=
  .source text

def fixedAtom {context : List Kind} (atom : Atom) : Action context .atom :=
  .source atom

def symbolOf {context : List Kind} (text : Action context .text) :
    Action context .atom :=
  .apply .symbol (.cons text .nil)

def stringOf {context : List Kind} (text : Action context .text) :
    Action context .atom :=
  .apply .string (.cons text .nil)

def appendText {context : List Kind} (left right : Action context .text) :
    Action context .text :=
  .apply .textAppend (.cons left (.cons right .nil))

def emptyAtoms {context : List Kind} : Action context .atoms :=
  .apply .empty .nil

def singleton {context : List Kind} (atom : Action context .atom) :
    Action context .atoms :=
  .apply .cons (.cons atom (.cons emptyAtoms .nil))

def appendAtoms {context : List Kind} (left right : Action context .atoms) :
    Action context .atoms :=
  .apply .append (.cons left (.cons right .nil))

def applyAtom {context : List Kind} (head : Action context .atom)
    (arguments : Action context .atoms) : Action context .atom :=
  .apply .application (.cons head (.cons arguments .nil))

def expressionOf {context : List Kind} (arguments : Action context .atoms) :
    Action context .atom :=
  .apply .expression (.cons arguments .nil)

def textAsAtom? {context : List Kind} (mode : TextAtomMode)
    (text : Action context .text) : Option (Action context .atom) :=
  match mode with
  | .symbol => some (symbolOf text)
  | .string => some (stringOf text)
  | .tagged head =>
      some (applyAtom (fixedAtom (.symbol head)) (singleton (stringOf text)))
  | .prefixedSymbol prefixText =>
      some (symbolOf (appendText (fixedText prefixText) text))
  | .reject => none

def childText? (context : List Kind) (child : Reference) :
    Option (Action context .text) :=
  inputAt? context child.childIndex .text

def childAtom? (policy : Policy) (context : List Kind) (child : Reference) :
    Option (Action context .atom) :=
  match inputAt? context child.childIndex .atom with
  | some input => some input
  | none => match inputAt? context child.childIndex .text with
    | some input => textAsAtom? (policy.textAtomMode child.name) input
    | none => match inputAt? context child.childIndex .integer with
      | some input => some (.apply .integer (.cons input .nil))
      | none => none

def childAtoms? (policy : Policy) (context : List Kind) (child : Reference) :
    Option (Action context .atoms) :=
  match inputAt? context child.childIndex .atoms with
  | some input => some input
  | none => (childAtom? policy context child).map singleton

def tokenPieceText? (context : List Kind) : TokenPiece →
    Option (Action context .text)
  | .fixed text _ => some (fixedText text)
  | .child child => childText? context child

def tokenText? (context : List Kind) : List TokenPiece →
    Option (Action context .text)
  | [] => some (fixedText "")
  | piece :: rest => do
      let first ← tokenPieceText? context piece
      let suffix ← tokenText? context rest
      return appendText first suffix

def arguments? (policy : Policy) (context : List Kind) :
    List Reference → Option (Action context .atoms)
  | [] => some emptyAtoms
  | child :: rest => do
      let first ← childAtoms? policy context child
      let suffix ← arguments? policy context rest
      return appendAtoms first suffix

def head? (policy : Policy) (context : List Kind) : Head →
    Option (Action context .atom)
  | .fixed text _ => some (fixedAtom (policy.fixedAtom text))
  | .child child => childAtom? policy context child

/-- Compile a plan at one exact child context and declared result kind.
`chain` remains unavailable until a language supplies the representation law
that licenses flattening or an alternative nesting interpretation. -/
def compilePlan? (policy : Policy) (context : List Kind) (output : Kind) :
    Plan → Option (Action context output)
  | .empty => match output with
      | .atoms => some emptyAtoms
      | .atom => some (expressionOf emptyAtoms)
      | _ => none
  | .passthrough child =>
      match inputAt? context child.childIndex output with
      | some input => some input
      | none => match output with
        | .atom => childAtom? policy context child
        | _ => none
  | .grouped _ _ child =>
      match inputAt? context child.childIndex output with
      | some input => some input
      | none => match output with
        | .atom =>
            (inputAt? context child.childIndex .atoms).map expressionOf
        | _ => none
  | .literal text => match output with
      | .text => some (fixedText text)
      | .atom => some (fixedAtom (policy.fixedAtom text))
      | _ => none
  | .token pieces => match output with
      | .text => tokenText? context pieces
      | .atom => do
          let text ← tokenText? context pieces
          textAsAtom? (policy.textAtomMode "#operator") text
      | _ => none
  | .singleton child => match output with
      | .atoms => childAtoms? policy context child
      | _ => none
  | .sequence children => match output with
      | .atoms => arguments? policy context children
      | _ => none
  | .tuple children => match output with
      | .atom => (arguments? policy context children).map expressionOf
      | _ => none
  | .apply elected arguments => match output with
      | .atom => do
          let head ← head? policy context elected
          let arguments ← arguments? policy context arguments
          return applyAtom head arguments
      | _ => none
  | .chain elected arguments => match policy.chainMode, output with
      | .nested, .atom => do
          let head ← head? policy context elected
          let arguments ← arguments? policy context arguments
          return applyAtom head arguments
      | _, _ => none
  | .unresolved _ => none

def compileAlternative? (policy : Policy) (sortMap : String → Kind)
    (classified : ClassifiedAlternative) :
    Option (Action (classified.alternative.referenceNames.map sortMap)
      (sortMap classified.category)) :=
  compilePlan? policy (classified.alternative.referenceNames.map sortMap)
    (sortMap classified.category) classified.plan

/-! ## Controls -/

private def atomContext : List Kind := [.atom]
private def textContext : List Kind := [.text]

example : (compilePlan? asciiPolicy atomContext .atom
    (.passthrough ⟨"value", 0, 0⟩)).isSome = true := rfl

/-- Transparent wrappers cannot cross a semantic sort boundary. -/
example : compilePlan? asciiPolicy textContext .atom
    (.passthrough ⟨"raw", 0, 0⟩) ≠ none := by decide

private def rejectingPolicy : Policy where
  textAtomMode := fun _ => .reject
  fixedAtom := .symbol
  chainMode := .reject

/-- A text/atom boundary remains closed unless the leaf policy declares it. -/
example : compilePlan? rejectingPolicy textContext .atom
    (.passthrough ⟨"raw", 0, 0⟩) = none := rfl

example : (compilePlan? asciiPolicy [.text, .atoms, .text] .atom
    (.grouped "[" "]" ⟨"items", 2, 1⟩)).isSome = true := rfl

/-- Delimiters do not license arbitrary text-to-atom conversion. -/
example : compilePlan? asciiPolicy [.text] .atom
    (.grouped "(" ")" ⟨"raw", 0, 0⟩) = none := rfl

example : (compilePlan? asciiPolicy textContext .atom
    (.token [.fixed "~" 0, .child ⟨"vline", 1, 0⟩])).isSome = true := rfl

/-- A token plan cannot silently consume an atom child as text. -/
example : compilePlan? asciiPolicy atomContext .atom
    (.token [.child ⟨"not-text", 0, 0⟩]) = none := rfl

/-- Flattening a recursive chain requires an explicit representation law. -/
example : compilePlan? asciiPolicy [.atom, .atom] .atom
    (.chain (.fixed "&" 1) [⟨"formula", 0, 0⟩, ⟨"formula", 2, 1⟩]) = none := rfl

end Mettapedia.GSLT.Parsing.GrammarHeadElectionActions
