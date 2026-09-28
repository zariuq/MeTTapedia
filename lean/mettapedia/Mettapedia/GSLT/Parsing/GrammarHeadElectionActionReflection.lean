import Mettapedia.GSLT.Parsing.GrammarHeadElectionActions
import Mettapedia.GSLT.Parsing.MeTTaAtomActionReflection

/-!
# First-order compilation of grammar head-election plans

This compiler evaluates a head-election plan directly into the established
untyped action wire.  It has the same category-level policy and fail-closed
sort checks as the intrinsically typed compiler, but it does not allocate a
dependent route for every grammar production.  The generic correspondence
with the typed compiler is established below; grammar instances therefore
remain ordinary first-order computation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GrammarHeadElectionActionReflection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open GrammarHeadElection
open GrammarHeadElectionActions (TextAtomMode ChainMode)
open MeTTaAtomConstruction (Kind)
open MeTTaAtomActionCompiler (CompiledAction Primitive)
open GrammarConstructorActions

abbrev ActionPolicy := GrammarHeadElectionActions.Policy

def inputAt? (context : List Kind) (index : Nat) (kind : Kind) :
    Option CompiledAction :=
  if context[index]? = some kind then some (.slot index) else none

def fixedText (text : String) : CompiledAction :=
  .constant (.grounded (.string text))

def fixedAtom (atom : Atom) : CompiledAction := .constant atom

def symbolOf (text : CompiledAction) : CompiledAction :=
  .primitive .symbol [text]

/-- String construction is a representation-preserving identity in the
existing action compiler. -/
def stringOf (text : CompiledAction) : CompiledAction := text

def appendText (left right : CompiledAction) : CompiledAction :=
  .primitive .textAppend [left, right]

def emptyAtoms : CompiledAction := .constant (.expression [])

def singleton (atom : CompiledAction) : CompiledAction :=
  .primitive .cons [atom, emptyAtoms]

def appendAtoms (left right : CompiledAction) : CompiledAction :=
  .primitive .append [left, right]

def applyAtom (head arguments : CompiledAction) : CompiledAction :=
  .primitive .cons [head, arguments]

/-- Expression construction is also representation-preserving. -/
def expressionOf (arguments : CompiledAction) : CompiledAction := arguments

def textAsAtom? (mode : TextAtomMode) (text : CompiledAction) :
    Option CompiledAction :=
  match mode with
  | .symbol => some (symbolOf text)
  | .string => some (stringOf text)
  | .tagged head =>
      some (applyAtom (fixedAtom (.symbol head)) (singleton (stringOf text)))
  | .prefixedSymbol prefixText =>
      some (symbolOf (appendText (fixedText prefixText) text))
  | .reject => none

def childText? (context : List Kind) (child : Reference) :
    Option CompiledAction :=
  inputAt? context child.childIndex .text

def childAtom? (policy : ActionPolicy) (context : List Kind) (child : Reference) :
    Option CompiledAction :=
  match inputAt? context child.childIndex .atom with
  | some input => some input
  | none => match inputAt? context child.childIndex .text with
    | some input => textAsAtom? (policy.textAtomMode child.name) input
    | none => inputAt? context child.childIndex .integer

def childAtoms? (policy : ActionPolicy) (context : List Kind) (child : Reference) :
    Option CompiledAction :=
  match inputAt? context child.childIndex .atoms with
  | some input => some input
  | none => (childAtom? policy context child).map singleton

def tokenPieceText? (context : List Kind) : TokenPiece → Option CompiledAction
  | .fixed text _ => some (fixedText text)
  | .child child => childText? context child

def tokenText? (context : List Kind) : List TokenPiece → Option CompiledAction
  | [] => some (fixedText "")
  | piece :: rest => do
      let first ← tokenPieceText? context piece
      let suffix ← tokenText? context rest
      return appendText first suffix

def arguments? (policy : ActionPolicy) (context : List Kind) :
    List Reference → Option CompiledAction
  | [] => some emptyAtoms
  | child :: rest => do
      let first ← childAtoms? policy context child
      let suffix ← arguments? policy context rest
      return appendAtoms first suffix

def head? (policy : ActionPolicy) (context : List Kind) : Head → Option CompiledAction
  | .fixed text _ => some (fixedAtom (policy.fixedAtom text))
  | .child child => childAtom? policy context child

/-- Direct first-order compilation of one structural plan. -/
def compilePlan? (policy : ActionPolicy) (context : List Kind) (output : Kind) :
    Plan → Option CompiledAction
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
      | ChainMode.nested, .atom => do
          let head ← head? policy context elected
          let arguments ← arguments? policy context arguments
          return applyAtom head arguments
      | _, _ => none
  | .unresolved _ => none

def compileAlternative? (policy : ActionPolicy) (sortMap : String → Kind)
    (classified : ClassifiedAlternative) : Option CompiledAction :=
  compilePlan? policy (classified.alternative.referenceNames.map sortMap)
    (sortMap classified.category) classified.plan

/-! ## Reflected typing soundness -/

open MeTTaAtomActionReflection

/-- Every admitted auxiliary representation is also a valid host atom.  This
is the reflected counterpart of `encodeValue`, whose codomain is `Atom` for
every construction kind. -/
theorem checkAction_to_atom {context : List Kind} {source : Kind}
    {action : CompiledAction}
    (accepted : checkAction context source action = true) :
    checkAction context .atom action = true := by
  cases action with
  | slot index =>
      cases actual : context[index]? <;>
        simp [checkAction, actual, representationEmbeds] at accepted ⊢
  | constant value => rfl
  | apply head arguments =>
      cases source <;> simp_all [checkAction]
  | primitive operation arguments =>
      cases operation <;> cases source <;>
        simp_all [checkAction, primitiveInputs?]

theorem inputAt?_checked {context : List Kind} {index : Nat} {kind : Kind}
    {action : CompiledAction} (compiled : inputAt? context index kind = some action) :
    checkAction context kind action = true := by
  simp only [inputAt?] at compiled
  split at compiled
  next exact =>
    simp only [Option.some.injEq] at compiled
    subst action
    simp only [checkAction, exact]
    cases kind <;> rfl
  next => contradiction

theorem fixedText_checked {context : List Kind} (text : String) :
    checkAction context .text (fixedText text) = true := rfl

theorem fixedAtom_checked {context : List Kind} (atom : Atom) :
    checkAction context .atom (fixedAtom atom) = true := rfl

theorem symbolOf_checked {context : List Kind} {text : CompiledAction}
    (checked : checkAction context .text text = true) :
    checkAction context .atom (symbolOf text) = true := by
  simp [symbolOf, checkAction, checkArguments, primitiveInputs?, checked]

theorem stringOf_checked {context : List Kind} {text : CompiledAction}
    (checked : checkAction context .text text = true) :
    checkAction context .atom (stringOf text) = true :=
  checkAction_to_atom checked

theorem appendText_checked {context : List Kind} {left right : CompiledAction}
    (leftChecked : checkAction context .text left = true)
    (rightChecked : checkAction context .text right = true) :
    checkAction context .text (appendText left right) = true := by
  simp [appendText, checkAction, checkArguments, primitiveInputs?,
    leftChecked, rightChecked]

theorem emptyAtoms_checked {context : List Kind} :
    checkAction context .atoms emptyAtoms = true := rfl

theorem singleton_checked {context : List Kind} {atom : CompiledAction}
    (checked : checkAction context .atom atom = true) :
    checkAction context .atoms (singleton atom) = true := by
  simp [singleton, checkAction, checkArguments, primitiveInputs?, checked,
    emptyAtoms_checked]

theorem appendAtoms_checked {context : List Kind} {left right : CompiledAction}
    (leftChecked : checkAction context .atoms left = true)
    (rightChecked : checkAction context .atoms right = true) :
    checkAction context .atoms (appendAtoms left right) = true := by
  simp [appendAtoms, checkAction, checkArguments, primitiveInputs?,
    leftChecked, rightChecked]

theorem applyAtom_checked {context : List Kind} {head arguments : CompiledAction}
    (headChecked : checkAction context .atom head = true)
    (argumentsChecked : checkAction context .atoms arguments = true) :
    checkAction context .atom (applyAtom head arguments) = true := by
  simp [applyAtom, checkAction, checkArguments, primitiveInputs?,
    headChecked, argumentsChecked]

theorem expressionOf_checked {context : List Kind} {arguments : CompiledAction}
    (checked : checkAction context .atoms arguments = true) :
    checkAction context .atom (expressionOf arguments) = true :=
  checkAction_to_atom checked

theorem textAsAtom?_checked {context : List Kind} {mode : TextAtomMode}
    {text action : CompiledAction}
    (textChecked : checkAction context .text text = true)
    (compiled : textAsAtom? mode text = some action) :
    checkAction context .atom action = true := by
  cases mode with
  | symbol =>
      simp only [textAsAtom?, Option.some.injEq] at compiled
      subst action
      exact symbolOf_checked textChecked
  | string =>
      simp only [textAsAtom?, Option.some.injEq] at compiled
      subst action
      exact stringOf_checked textChecked
  | tagged head =>
      simp only [textAsAtom?, Option.some.injEq] at compiled
      subst action
      exact applyAtom_checked (fixedAtom_checked _)
        (singleton_checked (stringOf_checked textChecked))
  | prefixedSymbol prefixText =>
      simp only [textAsAtom?, Option.some.injEq] at compiled
      subst action
      exact symbolOf_checked
        (appendText_checked (fixedText_checked _) textChecked)
  | reject => simp [textAsAtom?] at compiled

theorem childText?_checked {context : List Kind} {child : Reference}
    {action : CompiledAction} (compiled : childText? context child = some action) :
    checkAction context .text action = true :=
  inputAt?_checked compiled

theorem childAtom?_checked {policy : ActionPolicy} {context : List Kind}
    {child : Reference} {action : CompiledAction}
    (compiled : childAtom? policy context child = some action) :
    checkAction context .atom action = true := by
  unfold childAtom? at compiled
  cases atomInput : inputAt? context child.childIndex .atom with
  | some input =>
      simp only [atomInput, Option.some.injEq] at compiled
      subst action
      exact inputAt?_checked atomInput
  | none =>
      simp only [atomInput] at compiled
      cases textInput : inputAt? context child.childIndex .text with
      | some text =>
          simp only [textInput] at compiled
          exact textAsAtom?_checked (inputAt?_checked textInput) compiled
      | none =>
          simp only [textInput] at compiled
          exact checkAction_to_atom (inputAt?_checked compiled)

theorem childAtoms?_checked {policy : ActionPolicy} {context : List Kind}
    {child : Reference} {action : CompiledAction}
    (compiled : childAtoms? policy context child = some action) :
    checkAction context .atoms action = true := by
  unfold childAtoms? at compiled
  cases atomsInput : inputAt? context child.childIndex .atoms with
  | some input =>
      simp only [atomsInput, Option.some.injEq] at compiled
      subst action
      exact inputAt?_checked atomsInput
  | none =>
      simp only [atomsInput] at compiled
      cases atomResult : childAtom? policy context child with
      | none => simp [atomResult] at compiled
      | some atom =>
          simp only [atomResult, Option.map_some, Option.some.injEq] at compiled
          subst action
          exact singleton_checked (childAtom?_checked atomResult)

theorem tokenPieceText?_checked {context : List Kind} {piece : TokenPiece}
    {action : CompiledAction}
    (compiled : tokenPieceText? context piece = some action) :
    checkAction context .text action = true := by
  cases piece with
  | fixed text index =>
      simp only [tokenPieceText?, Option.some.injEq] at compiled
      subst action
      exact fixedText_checked _
  | child child => exact childText?_checked compiled

theorem tokenText?_checked {context : List Kind} {pieces : List TokenPiece}
    {action : CompiledAction} (compiled : tokenText? context pieces = some action) :
    checkAction context .text action = true := by
  induction pieces generalizing action with
  | nil =>
      simp only [tokenText?, Option.some.injEq] at compiled
      subst action
      exact fixedText_checked _
  | cons piece pieces ih =>
      simp only [tokenText?] at compiled
      cases firstResult : tokenPieceText? context piece with
      | none => simp [firstResult] at compiled
      | some first =>
          simp only [firstResult] at compiled
          cases suffixResult : tokenText? context pieces with
          | none => simp [suffixResult] at compiled
          | some suffix =>
              simp [suffixResult] at compiled
              subst action
              exact appendText_checked (tokenPieceText?_checked firstResult)
                (ih suffixResult)

theorem arguments?_checked {policy : ActionPolicy} {context : List Kind}
    {children : List Reference} {action : CompiledAction}
    (compiled : arguments? policy context children = some action) :
    checkAction context .atoms action = true := by
  induction children generalizing action with
  | nil =>
      simp only [arguments?, Option.some.injEq] at compiled
      subst action
      exact emptyAtoms_checked
  | cons child children ih =>
      simp only [arguments?] at compiled
      cases firstResult : childAtoms? policy context child with
      | none => simp [firstResult] at compiled
      | some first =>
          simp only [firstResult] at compiled
          cases suffixResult : arguments? policy context children with
          | none => simp [suffixResult] at compiled
          | some suffix =>
              simp [suffixResult] at compiled
              subst action
              exact appendAtoms_checked (childAtoms?_checked firstResult)
                (ih suffixResult)

theorem head?_checked {policy : ActionPolicy} {context : List Kind}
    {head : Head} {action : CompiledAction}
    (compiled : head? policy context head = some action) :
    checkAction context .atom action = true := by
  cases head with
  | fixed text index =>
      simp only [head?, Option.some.injEq] at compiled
      subst action
      exact fixedAtom_checked _
  | child child => exact childAtom?_checked compiled

/-- The direct first-order compiler can emit only actions accepted by the
reflected sort checker.  This theorem is grammar-independent and is the
reason a grammar instance need not normalize hundreds of dependent routes. -/
theorem compilePlan?_checked {policy : ActionPolicy} {context : List Kind}
    {output : Kind} {plan : Plan} {action : CompiledAction}
    (compiled : compilePlan? policy context output plan = some action) :
    checkAction context output action = true := by
  cases plan with
  | empty =>
      cases output <;> simp [compilePlan?] at compiled
      case atom =>
        subst action
        exact expressionOf_checked emptyAtoms_checked
      case atoms =>
        subst action
        exact emptyAtoms_checked
  | passthrough child =>
      simp only [compilePlan?] at compiled
      cases direct : inputAt? context child.childIndex output with
      | some input =>
          simp only [direct, Option.some.injEq] at compiled
          subst action
          exact inputAt?_checked direct
      | none =>
          simp only [direct] at compiled
          cases output <;> simp at compiled
          exact childAtom?_checked compiled
  | grouped opening closing child =>
      simp only [compilePlan?] at compiled
      cases direct : inputAt? context child.childIndex output with
      | some input =>
          simp only [direct, Option.some.injEq] at compiled
          subst action
          exact inputAt?_checked direct
      | none =>
          simp only [direct] at compiled
          cases output <;> simp at compiled
          cases grouped : inputAt? context child.childIndex .atoms with
          | none => simp [grouped] at compiled
          | some arguments =>
              simp only [grouped, Option.some.injEq] at compiled
              rcases compiled with ⟨value, rfl, equality⟩
              rw [← equality]
              exact expressionOf_checked (inputAt?_checked grouped)
  | literal text =>
      cases output <;> simp [compilePlan?] at compiled
      case atom =>
        subst action
        exact fixedAtom_checked _
      case text =>
        subst action
        exact fixedText_checked _
  | token pieces =>
      cases output <;> simp [compilePlan?] at compiled
      case text => exact tokenText?_checked compiled
      case atom =>
        cases textResult : tokenText? context pieces with
        | none => simp [textResult] at compiled
        | some text =>
            simp only [textResult] at compiled
            exact textAsAtom?_checked (tokenText?_checked textResult) compiled
  | singleton child =>
      cases output <;> simp [compilePlan?] at compiled
      exact childAtoms?_checked compiled
  | sequence children =>
      cases output <;> simp [compilePlan?] at compiled
      exact arguments?_checked compiled
  | tuple children =>
      cases output <;> simp [compilePlan?] at compiled
      cases argumentsResult : arguments? policy context children with
      | none => simp [argumentsResult] at compiled
      | some arguments =>
          simp only [argumentsResult, Option.some.injEq] at compiled
          rcases compiled with ⟨value, rfl, equality⟩
          rw [← equality]
          exact expressionOf_checked (arguments?_checked argumentsResult)
  | apply elected arguments =>
      cases output <;> simp [compilePlan?] at compiled
      cases headResult : head? policy context elected with
      | none => simp [headResult] at compiled
      | some head =>
          simp only [headResult] at compiled
          cases argumentsResult : arguments? policy context arguments with
          | none => simp [argumentsResult] at compiled
          | some values =>
              simp [argumentsResult] at compiled
              subst action
              exact applyAtom_checked (head?_checked headResult)
                (arguments?_checked argumentsResult)
  | chain elected arguments =>
      cases chainMode : policy.chainMode <;> cases output <;>
        simp [compilePlan?, chainMode] at compiled
      cases headResult : head? policy context elected with
      | none => simp [headResult] at compiled
      | some head =>
          simp only [headResult] at compiled
          cases argumentsResult : arguments? policy context arguments with
          | none => simp [argumentsResult] at compiled
          | some values =>
              simp [argumentsResult] at compiled
              subst action
              exact applyAtom_checked (head?_checked headResult)
                (arguments?_checked argumentsResult)
  | unresolved reason => simp [compilePlan?] at compiled

theorem compileAlternative?_checked {policy : ActionPolicy}
    {sortMap : String → Kind} {classified : ClassifiedAlternative}
    {action : CompiledAction}
    (compiled : compileAlternative? policy sortMap classified = some action) :
    checkAction (classified.alternative.referenceNames.map sortMap)
      (sortMap classified.category) action = true :=
  compilePlan?_checked compiled

/-! ## Agreement with the intrinsically typed compiler -/

private def typedSlot? (context : List Kind) (index : Nat) (kind : Kind) :
    Option Nat :=
  (GrammarHeadElectionActions.variableAt? context index kind).map
    GrammarConstructorActions.slotIndex

private theorem typedSlot?_eq (context : List Kind) (index : Nat) (kind : Kind) :
    typedSlot? context index kind =
      if context[index]? = some kind then some index else none := by
  induction context generalizing index with
  | nil => simp [typedSlot?, GrammarHeadElectionActions.variableAt?]
  | cons actual rest ih =>
      cases index with
      | zero =>
          by_cases same : actual = kind
          · subst kind
            simp [typedSlot?, GrammarHeadElectionActions.variableAt?,
              GrammarConstructorActions.slotIndex]
          · simp [typedSlot?, GrammarHeadElectionActions.variableAt?, same]
      | succ index =>
          have restExact := ih index
          unfold typedSlot? at restExact ⊢
          simp only [GrammarHeadElectionActions.variableAt?, Option.map_map]
          change Option.map (fun position :
                Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted.ConstructionVariable
                  rest kind =>
              GrammarConstructorActions.slotIndex
                (Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted.ConstructionVariable.there
                  (other := actual) position))
              (GrammarHeadElectionActions.variableAt? rest index kind) =
            if rest[index]? = some kind then some (index + 1) else none
          have functionExact :
              (fun position :
                  Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted.ConstructionVariable
                    rest kind =>
                GrammarConstructorActions.slotIndex
                  (Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted.ConstructionVariable.there
                    (other := actual) position)) =
              (fun position => GrammarConstructorActions.slotIndex position + 1) := by
            funext position
            rfl
          rw [functionExact]
          have shifted := congrArg (Option.map (fun slot => slot + 1)) restExact
          by_cases found : rest[index]? = some kind <;>
            simpa [found, Option.map_map, Function.comp_def] using shifted

theorem inputAt?_agrees (context : List Kind) (index : Nat) (kind : Kind) :
    (GrammarHeadElectionActions.inputAt? context index kind).map
      MeTTaAtomActionCompiler.compile = inputAt? context index kind := by
  calc
    _ = (typedSlot? context index kind).map
        (fun slot => (Action.slot slot : CompiledAction)) := by
      unfold GrammarHeadElectionActions.inputAt?
      unfold typedSlot?
      cases found : GrammarHeadElectionActions.variableAt? context index kind with
      | none => rfl
      | some position => rfl
    _ = inputAt? context index kind := by
      rw [typedSlot?_eq]
      simp [inputAt?]

theorem fixedText_agrees {context : List Kind} (text : String) :
    MeTTaAtomActionCompiler.compile
        (GrammarHeadElectionActions.fixedText (context := context) text) =
      fixedText text := rfl

theorem fixedAtom_agrees {context : List Kind} (atom : Atom) :
    MeTTaAtomActionCompiler.compile
        (GrammarHeadElectionActions.fixedAtom (context := context) atom) =
      fixedAtom atom := rfl

theorem symbolOf_agrees {context : List Kind}
    (text : MeTTaAtomConstruction.Action context .text) :
    MeTTaAtomActionCompiler.compile (GrammarHeadElectionActions.symbolOf text) =
      symbolOf (MeTTaAtomActionCompiler.compile text) := rfl

theorem stringOf_agrees {context : List Kind}
    (text : MeTTaAtomConstruction.Action context .text) :
    MeTTaAtomActionCompiler.compile (GrammarHeadElectionActions.stringOf text) =
      stringOf (MeTTaAtomActionCompiler.compile text) := rfl

theorem appendText_agrees {context : List Kind}
    (left right : MeTTaAtomConstruction.Action context .text) :
    MeTTaAtomActionCompiler.compile
        (GrammarHeadElectionActions.appendText left right) =
      appendText (MeTTaAtomActionCompiler.compile left)
        (MeTTaAtomActionCompiler.compile right) := rfl

theorem emptyAtoms_agrees {context : List Kind} :
    MeTTaAtomActionCompiler.compile
        (GrammarHeadElectionActions.emptyAtoms (context := context)) =
      emptyAtoms := rfl

theorem singleton_agrees {context : List Kind}
    (atom : MeTTaAtomConstruction.Action context .atom) :
    MeTTaAtomActionCompiler.compile (GrammarHeadElectionActions.singleton atom) =
      singleton (MeTTaAtomActionCompiler.compile atom) := rfl

theorem appendAtoms_agrees {context : List Kind}
    (left right : MeTTaAtomConstruction.Action context .atoms) :
    MeTTaAtomActionCompiler.compile
        (GrammarHeadElectionActions.appendAtoms left right) =
      appendAtoms (MeTTaAtomActionCompiler.compile left)
        (MeTTaAtomActionCompiler.compile right) := rfl

theorem applyAtom_agrees {context : List Kind}
    (head : MeTTaAtomConstruction.Action context .atom)
    (arguments : MeTTaAtomConstruction.Action context .atoms) :
    MeTTaAtomActionCompiler.compile
        (GrammarHeadElectionActions.applyAtom head arguments) =
      applyAtom (MeTTaAtomActionCompiler.compile head)
        (MeTTaAtomActionCompiler.compile arguments) := rfl

theorem expressionOf_agrees {context : List Kind}
    (arguments : MeTTaAtomConstruction.Action context .atoms) :
    MeTTaAtomActionCompiler.compile
        (GrammarHeadElectionActions.expressionOf arguments) =
      expressionOf (MeTTaAtomActionCompiler.compile arguments) := rfl

theorem textAsAtom?_agrees {context : List Kind} (mode : TextAtomMode)
    (text : MeTTaAtomConstruction.Action context .text) :
    (GrammarHeadElectionActions.textAsAtom? mode text).map
        MeTTaAtomActionCompiler.compile =
      textAsAtom? mode (MeTTaAtomActionCompiler.compile text) := by
  cases mode <;> rfl

theorem childText?_agrees (context : List Kind) (child : Reference) :
    (GrammarHeadElectionActions.childText? context child).map
        MeTTaAtomActionCompiler.compile = childText? context child := by
  exact inputAt?_agrees context child.childIndex .text

theorem childAtom?_agrees (policy : ActionPolicy)
    (context : List MeTTaAtomConstruction.algebra.Kind)
    (child : Reference) :
    (GrammarHeadElectionActions.childAtom? policy context child).map
        MeTTaAtomActionCompiler.compile = childAtom? policy context child := by
  unfold GrammarHeadElectionActions.childAtom? childAtom?
  cases atomInput : GrammarHeadElectionActions.inputAt?
      context child.childIndex .atom with
  | some atom =>
      have agreement := inputAt?_agrees context child.childIndex .atom
      simp only [atomInput, Option.map_some] at agreement
      simp only [Option.map_some]
      rw [← agreement]
  | none =>
      have atomAgreement := inputAt?_agrees context child.childIndex .atom
      simp only [atomInput, Option.map_none] at atomAgreement
      rw [← atomAgreement]
      cases textInput : GrammarHeadElectionActions.inputAt?
          context child.childIndex .text with
      | some text =>
          have textAgreement := inputAt?_agrees context child.childIndex .text
          simp only [textInput, Option.map_some] at textAgreement
          rw [← textAgreement]
          exact textAsAtom?_agrees (policy.textAtomMode child.name) text
      | none =>
          have textAgreement := inputAt?_agrees context child.childIndex .text
          simp only [textInput, Option.map_none] at textAgreement
          rw [← textAgreement]
          cases integerInput : GrammarHeadElectionActions.inputAt?
              context child.childIndex .integer with
          | none =>
              have integerAgreement :=
                inputAt?_agrees context child.childIndex .integer
              simp only [integerInput, Option.map_none] at integerAgreement
              simp [integerAgreement]
          | some integer =>
              have integerAgreement :=
                inputAt?_agrees context child.childIndex .integer
              simp only [integerInput, Option.map_some] at integerAgreement
              simp only [Option.map_some]
              rw [← integerAgreement]
              rfl

theorem childAtoms?_agrees (policy : ActionPolicy)
    (context : List MeTTaAtomConstruction.algebra.Kind)
    (child : Reference) :
    (GrammarHeadElectionActions.childAtoms? policy context child).map
        MeTTaAtomActionCompiler.compile = childAtoms? policy context child := by
  unfold GrammarHeadElectionActions.childAtoms? childAtoms?
  cases atomsInput : GrammarHeadElectionActions.inputAt?
      context child.childIndex .atoms with
  | some atoms =>
      have agreement := inputAt?_agrees context child.childIndex .atoms
      simp only [atomsInput, Option.map_some] at agreement
      simp only [Option.map_some]
      rw [← agreement]
  | none =>
      have atomsAgreement := inputAt?_agrees context child.childIndex .atoms
      simp only [atomsInput, Option.map_none] at atomsAgreement
      rw [← atomsAgreement]
      cases atomResult : GrammarHeadElectionActions.childAtom?
          policy context child with
      | none =>
          have agreement := childAtom?_agrees policy context child
          simp only [atomResult, Option.map_none] at agreement
          have directNone : childAtom? policy context child = none := agreement.symm
          simp only [directNone, Option.map_none]
      | some atom =>
          have agreement := childAtom?_agrees policy context child
          simp only [atomResult, Option.map_some] at agreement
          rw [← agreement]
          rfl

theorem tokenPieceText?_agrees (context : List Kind) (piece : TokenPiece) :
    (GrammarHeadElectionActions.tokenPieceText? context piece).map
        MeTTaAtomActionCompiler.compile = tokenPieceText? context piece := by
  cases piece with
  | fixed text index => rfl
  | child child => exact childText?_agrees context child

theorem tokenText?_agrees (context : List Kind) (pieces : List TokenPiece) :
    (GrammarHeadElectionActions.tokenText? context pieces).map
        MeTTaAtomActionCompiler.compile = tokenText? context pieces := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih =>
      simp only [GrammarHeadElectionActions.tokenText?, tokenText?]
      cases firstResult : GrammarHeadElectionActions.tokenPieceText? context piece with
      | none =>
          have firstAgreement := tokenPieceText?_agrees context piece
          simp only [firstResult, Option.map_none] at firstAgreement
          have directNone : tokenPieceText? context piece = none := firstAgreement.symm
          rw [directNone]
          rfl
      | some first =>
          have firstAgreement := tokenPieceText?_agrees context piece
          simp only [firstResult, Option.map_some] at firstAgreement
          rw [← firstAgreement]
          cases suffixResult : GrammarHeadElectionActions.tokenText? context pieces with
          | none =>
              have suffixAgreement := ih
              simp only [suffixResult, Option.map_none] at suffixAgreement
              have directNone : tokenText? context pieces = none := suffixAgreement.symm
              rw [directNone]
              rfl
          | some suffix =>
              have suffixAgreement := ih
              simp only [suffixResult, Option.map_some] at suffixAgreement
              rw [← suffixAgreement]
              rfl

theorem arguments?_agrees (policy : ActionPolicy) (context : List Kind)
    (children : List Reference) :
    (GrammarHeadElectionActions.arguments? policy context children).map
        MeTTaAtomActionCompiler.compile = arguments? policy context children := by
  induction children with
  | nil => rfl
  | cons child children ih =>
      simp only [GrammarHeadElectionActions.arguments?, arguments?]
      cases firstResult : GrammarHeadElectionActions.childAtoms? policy context child with
      | none =>
          have firstAgreement := childAtoms?_agrees policy context child
          simp only [firstResult, Option.map_none] at firstAgreement
          have directNone : childAtoms? policy context child = none := firstAgreement.symm
          rw [directNone]
          rfl
      | some first =>
          have firstAgreement := childAtoms?_agrees policy context child
          simp only [firstResult, Option.map_some] at firstAgreement
          rw [← firstAgreement]
          cases suffixResult : GrammarHeadElectionActions.arguments?
              policy context children with
          | none =>
              have suffixAgreement := ih
              simp only [suffixResult, Option.map_none] at suffixAgreement
              have directNone : arguments? policy context children = none :=
                suffixAgreement.symm
              rw [directNone]
              rfl
          | some suffix =>
              have suffixAgreement := ih
              simp only [suffixResult, Option.map_some] at suffixAgreement
              rw [← suffixAgreement]
              rfl

theorem head?_agrees (policy : ActionPolicy) (context : List Kind) (head : Head) :
    (GrammarHeadElectionActions.head? policy context head).map
        MeTTaAtomActionCompiler.compile = head? policy context head := by
  cases head with
  | fixed text index => rfl
  | child child => exact childAtom?_agrees policy context child

/-- Erasing the intrinsically typed compiler produces exactly the direct
first-order compiler.  This is a theorem about the generic compiler, not a
comparison of two separately authored language tables. -/
theorem compilePlan?_agrees (policy : ActionPolicy) (context : List Kind)
    (output : Kind) (plan : Plan) :
    (GrammarHeadElectionActions.compilePlan? policy context output plan).map
        MeTTaAtomActionCompiler.compile =
      compilePlan? policy context output plan := by
  cases plan with
  | empty => cases output <;> rfl
  | passthrough child =>
      simp only [GrammarHeadElectionActions.compilePlan?, compilePlan?]
      cases inputResult : GrammarHeadElectionActions.inputAt?
          context child.childIndex output with
      | some input =>
          have agreement := inputAt?_agrees context child.childIndex output
          simp only [inputResult, Option.map_some] at agreement
          rw [← agreement]
          rfl
      | none =>
          have agreement := inputAt?_agrees context child.childIndex output
          simp only [inputResult, Option.map_none] at agreement
          have directNone : inputAt? context child.childIndex output = none :=
            agreement.symm
          rw [directNone]
          cases output with
          | atom => exact childAtom?_agrees policy context child
          | atoms | text | integer | integerLexeme | rationalLexeme => rfl
  | grouped opening closing child =>
      simp only [GrammarHeadElectionActions.compilePlan?, compilePlan?]
      cases inputResult : GrammarHeadElectionActions.inputAt?
          context child.childIndex output with
      | some input =>
          have agreement := inputAt?_agrees context child.childIndex output
          simp only [inputResult, Option.map_some] at agreement
          rw [← agreement]
          rfl
      | none =>
          have agreement := inputAt?_agrees context child.childIndex output
          simp only [inputResult, Option.map_none] at agreement
          have directNone : inputAt? context child.childIndex output = none :=
            agreement.symm
          rw [directNone]
          cases output with
          | atom =>
              cases argumentsResult : GrammarHeadElectionActions.inputAt?
                  context child.childIndex .atoms with
              | none =>
                  have argumentsAgreement :=
                    inputAt?_agrees context child.childIndex .atoms
                  simp only [argumentsResult, Option.map_none] at argumentsAgreement
                  have argumentsNone :
                      inputAt? context child.childIndex .atoms = none :=
                    argumentsAgreement.symm
                  rw [argumentsNone]
                  rfl
              | some arguments =>
                  have argumentsAgreement :=
                    inputAt?_agrees context child.childIndex .atoms
                  simp only [argumentsResult, Option.map_some] at argumentsAgreement
                  rw [← argumentsAgreement]
                  rfl
          | atoms | text | integer | integerLexeme | rationalLexeme => rfl
  | literal text => cases output <;> rfl
  | token pieces =>
      cases output with
      | atom =>
          simp only [GrammarHeadElectionActions.compilePlan?, compilePlan?]
          cases textResult : GrammarHeadElectionActions.tokenText? context pieces with
          | none =>
              have textAgreement := tokenText?_agrees context pieces
              simp only [textResult, Option.map_none] at textAgreement
              have directNone : tokenText? context pieces = none := textAgreement.symm
              rw [directNone]
              rfl
          | some text =>
              have textAgreement := tokenText?_agrees context pieces
              simp only [textResult, Option.map_some] at textAgreement
              rw [← textAgreement]
              exact textAsAtom?_agrees (policy.textAtomMode "#operator") text
      | text => exact tokenText?_agrees context pieces
      | atoms | integer | integerLexeme | rationalLexeme => rfl
  | singleton child =>
      cases output with
      | atoms => exact childAtoms?_agrees policy context child
      | atom | text | integer | integerLexeme | rationalLexeme => rfl
  | sequence children =>
      cases output with
      | atoms => exact arguments?_agrees policy context children
      | atom | text | integer | integerLexeme | rationalLexeme => rfl
  | tuple children =>
      cases output with
      | atom =>
          simp only [GrammarHeadElectionActions.compilePlan?, compilePlan?]
          cases argumentsResult : GrammarHeadElectionActions.arguments?
              policy context children with
          | none =>
              have argumentsAgreement := arguments?_agrees policy context children
              simp only [argumentsResult, Option.map_none] at argumentsAgreement
              have directNone : arguments? policy context children = none :=
                argumentsAgreement.symm
              rw [directNone]
              rfl
          | some arguments =>
              have argumentsAgreement := arguments?_agrees policy context children
              simp only [argumentsResult, Option.map_some] at argumentsAgreement
              rw [← argumentsAgreement]
              rfl
      | atoms | text | integer | integerLexeme | rationalLexeme => rfl
  | apply elected children =>
      cases output with
      | atom =>
          simp only [GrammarHeadElectionActions.compilePlan?, compilePlan?]
          cases headResult : GrammarHeadElectionActions.head? policy context elected with
          | none =>
              have headAgreement := head?_agrees policy context elected
              simp only [headResult, Option.map_none] at headAgreement
              have directNone : head? policy context elected = none :=
                headAgreement.symm
              rw [directNone]
              rfl
          | some head =>
              have headAgreement := head?_agrees policy context elected
              simp only [headResult, Option.map_some] at headAgreement
              rw [← headAgreement]
              cases argumentsResult : GrammarHeadElectionActions.arguments?
                  policy context children with
              | none =>
                  have argumentsAgreement := arguments?_agrees policy context children
                  simp only [argumentsResult, Option.map_none] at argumentsAgreement
                  have directNone : arguments? policy context children = none :=
                    argumentsAgreement.symm
                  rw [directNone]
                  rfl
              | some arguments =>
                  have argumentsAgreement := arguments?_agrees policy context children
                  simp only [argumentsResult, Option.map_some] at argumentsAgreement
                  rw [← argumentsAgreement]
                  rfl
      | atoms | text | integer | integerLexeme | rationalLexeme => rfl
  | chain elected children =>
      cases chainMode : policy.chainMode with
      | reject => cases output <;> simp [GrammarHeadElectionActions.compilePlan?,
          compilePlan?, chainMode]
      | nested =>
          cases output with
          | atom =>
              simp only [GrammarHeadElectionActions.compilePlan?, compilePlan?, chainMode]
              cases headResult : GrammarHeadElectionActions.head? policy context elected with
              | none =>
                  have headAgreement := head?_agrees policy context elected
                  simp only [headResult, Option.map_none] at headAgreement
                  have directNone : head? policy context elected = none :=
                    headAgreement.symm
                  rw [directNone]
                  rfl
              | some head =>
                  have headAgreement := head?_agrees policy context elected
                  simp only [headResult, Option.map_some] at headAgreement
                  rw [← headAgreement]
                  cases argumentsResult : GrammarHeadElectionActions.arguments?
                      policy context children with
                  | none =>
                      have argumentsAgreement :=
                        arguments?_agrees policy context children
                      simp only [argumentsResult, Option.map_none] at argumentsAgreement
                      have directNone : arguments? policy context children = none :=
                        argumentsAgreement.symm
                      rw [directNone]
                      rfl
                  | some arguments =>
                      have argumentsAgreement :=
                        arguments?_agrees policy context children
                      simp only [argumentsResult, Option.map_some] at argumentsAgreement
                      rw [← argumentsAgreement]
                      rfl
          | atoms | text | integer | integerLexeme | rationalLexeme =>
              simp [GrammarHeadElectionActions.compilePlan?, compilePlan?, chainMode]
  | unresolved reason => rfl

theorem compileAlternative?_agrees (policy : ActionPolicy)
    (sortMap : String → Kind) (classified : ClassifiedAlternative) :
    (GrammarHeadElectionActions.compileAlternative? policy sortMap classified).map
        MeTTaAtomActionCompiler.compile =
      compileAlternative? policy sortMap classified := by
  exact compilePlan?_agrees policy
    (classified.alternative.referenceNames.map sortMap)
    (sortMap classified.category) classified.plan

/-- A successful first-order compilation retains an intrinsically typed
witness.  No per-production transport term is stored in the generated table. -/
theorem compilePlan?_typed_witness {policy : ActionPolicy} {context : List Kind}
    {output : Kind} {plan : Plan} {action : CompiledAction}
    (compiled : compilePlan? policy context output plan = some action) :
    ∃ route : MeTTaAtomConstruction.Action context output,
      GrammarHeadElectionActions.compilePlan? policy context output plan = some route ∧
      MeTTaAtomActionCompiler.compile route = action := by
  have agreement := compilePlan?_agrees policy context output plan
  rw [compiled] at agreement
  cases typedResult : GrammarHeadElectionActions.compilePlan?
      policy context output plan with
  | none => simp [typedResult] at agreement
  | some route =>
      simp only [typedResult, Option.map_some, Option.some.injEq] at agreement
      exact ⟨route, rfl, agreement⟩

/-- The direct compiler inherits the operational theorem of the typed
construction algebra.  The witness identifies the source-level route whose
meaning the emitted action executes. -/
theorem compilePlan?_executes {policy : ActionPolicy} {context : List Kind}
    {output : Kind} {plan : Plan} {action : CompiledAction}
    (compiled : compilePlan? policy context output plan = some action)
    (values :
      Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted.FamilyList
        MeTTaAtomConstruction.Value context) :
    ∃ route : MeTTaAtomConstruction.Action context output,
      GrammarHeadElectionActions.compilePlan? policy context output plan = some route ∧
      MeTTaAtomActionCompiler.execute
          (MeTTaAtomActionCompiler.encodeValues values) action =
        some (MeTTaAtomActionCompiler.encodeValue output
          (MeTTaAtomConstruction.Action.run route values)) := by
  rcases compilePlan?_typed_witness compiled with
    ⟨route, routeCompiled, actionExact⟩
  refine ⟨route, routeCompiled, ?_⟩
  rw [← actionExact]
  exact MeTTaAtomActionCompiler.compile_executes route values

theorem compileAlternative?_typed_witness {policy : ActionPolicy}
    {sortMap : String → Kind} {classified : ClassifiedAlternative}
    {action : CompiledAction}
    (compiled : compileAlternative? policy sortMap classified = some action) :
    ∃ route : MeTTaAtomConstruction.Action
        (classified.alternative.referenceNames.map sortMap)
        (sortMap classified.category),
      GrammarHeadElectionActions.compileAlternative?
          policy sortMap classified = some route ∧
      MeTTaAtomActionCompiler.compile route = action := by
  exact compilePlan?_typed_witness compiled

/-! ## Local controls -/

private def atomContext : List Kind := [.atom]
private def textContext : List Kind := [.text]

example : compilePlan? GrammarHeadElectionActions.asciiPolicy atomContext .atom
    (.passthrough ⟨"value", 0, 0⟩) = some (.slot 0) := rfl

example : compilePlan? GrammarHeadElectionActions.asciiPolicy textContext .atom
    (.passthrough ⟨"raw", 0, 0⟩) ≠ none := by decide

private def rejectingPolicy : ActionPolicy where
  textAtomMode := fun _ => .reject
  fixedAtom := .symbol
  chainMode := .reject

example : compilePlan? rejectingPolicy textContext .atom
    (.passthrough ⟨"raw", 0, 0⟩) = none := rfl

example : compilePlan? GrammarHeadElectionActions.asciiPolicy [.text, .atoms, .text] .atom
    (.grouped "[" "]" ⟨"items", 2, 1⟩) = some (.slot 1) := rfl

/-- An atom slot cannot be reinterpreted as text. -/
example : compilePlan? GrammarHeadElectionActions.asciiPolicy atomContext .text
    (.passthrough ⟨"value", 0, 0⟩) = none := rfl

#print axioms compilePlan?_checked
#print axioms compilePlan?_agrees
#print axioms compilePlan?_executes

end Mettapedia.GSLT.Parsing.GrammarHeadElectionActionReflection
