import Mettapedia.GSLT.Parsing.MeTTaAtomConstruction
import Mettapedia.GSLT.Parsing.SourceSExprPatternInstantiation
import Mettapedia.GSLT.Parsing.ParserActionSlotTransport
import Mettapedia.GSLT.Parsing.ParserActionSubstitution

/-!
# Typed MeTTa construction action compilation

The action boundary uses ordinary host atoms. Auxiliary sequences are bare
expressions, text uses grounded strings, and integers retain their exact
model value. Decoding is indexed by the declared construction sort: an atom
and an argument sequence may share an expression representation without
identifying their roles in a well-sorted action.

Typed actions compile to the existing action datatype parameterized by these
values and four generic primitives. A separate partial executor and exact
action codec establish correspondence with the typed source on every input.

The `pa-primitive` / `pbc-primitive` wire specifies the generic native extension.
This module establishes its model, codec and compilation correspondence; the
native implementation connection and its integer representation are separate
obligations, not consequences of the Lean model alone.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.MeTTaAtomActionCompiler

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.GSLT.Parsing.MeTTaAtomConstruction
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted


/-- Encode a typed intermediate value as an ordinary host atom. -/
def encodeValue : (kind : Kind) → Value kind → Atom
  | .atom, value => value
  | .atoms, values => .expression values
  | .text, text => .grounded (.string text)
  | .integer, integer => .grounded (.int integer)
  | .integerLexeme, lexeme => .grounded (.string lexeme.text)
  | .rationalLexeme, lexeme => .grounded (.string lexeme.text)

/-- Decode only the representation admitted by the requested sort. -/
def decodeValue : (kind : Kind) → Atom → Option (Value kind)
  | .atom, value => some value
  | .atoms, .expression values => some values
  | .text, .grounded (.string text) => some text
  | .integer, .grounded (.int integer) => some integer
  | .integerLexeme, .grounded (.string text) =>
      ExactDecimalLexeme.decodeInteger? text
  | .rationalLexeme, .grounded (.string text) =>
      ExactDecimalLexeme.decodeRational? text
  | .atoms, _ | .text, _ | .integer, _ | .integerLexeme, _ |
      .rationalLexeme, _ => none

theorem decodeValue_encodeValue (kind : Kind) (value : Value kind) :
    decodeValue kind (encodeValue kind value) = some value := by
  cases kind with
  | atom | atoms | text | integer => rfl
  | integerLexeme => exact ExactDecimalLexeme.decodeInteger?_text value
  | rationalLexeme => exact ExactDecimalLexeme.decodeRational?_text value

/-- Encoding is lossless at each declared sort, including arbitrary integers. -/
theorem encodeValue_injective (kind : Kind) (left right : Value kind) :
    encodeValue kind left = encodeValue kind right ↔ left = right := by
  constructor
  · intro equality
    have decoded := congrArg (decodeValue kind) equality
    simpa only [decodeValue_encodeValue, Option.some.injEq] using decoded
  · exact congrArg (encodeValue kind)

def encodeValues : {kinds : List Kind} → FamilyList Value kinds → List Atom
  | [], .nil => []
  | kind :: _, .cons head tail => encodeValue kind head :: encodeValues tail

/-- Both the sorts and the complete argument count are enforced. -/
def decodeValues : (kinds : List Kind) → List Atom → Option (FamilyList Value kinds)
  | [], [] => some .nil
  | kind :: kinds, head :: tail => do
      let value ← decodeValue kind head
      let values ← decodeValues kinds tail
      some (.cons value values)
  | [], _ :: _ | _ :: _, [] => none

theorem decodeValues_encodeValues {kinds : List Kind} (values : FamilyList Value kinds) :
    decodeValues kinds (encodeValues values) = some values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp only [encodeValues, decodeValues, decodeValue_encodeValue, ih]
      rfl

theorem decodeValues_length {kinds : List Kind} {atoms : List Atom}
    {values : FamilyList Value kinds} (decoded : decodeValues kinds atoms = some values) :
    atoms.length = kinds.length := by
  induction kinds generalizing atoms with
  | nil =>
      cases atoms with
      | nil => rfl
      | cons head tail => cases decoded
  | cons kind kinds ih =>
      cases atoms with
      | nil => cases decoded
      | cons head tail =>
          cases first : decodeValue kind head with
          | none => simp [decodeValues, first] at decoded
          | some value =>
              cases rest : decodeValues kinds tail with
              | none => simp [decodeValues, first, rest] at decoded
              | some values => exact congrArg Nat.succ (ih rest)

theorem text_rejects_symbol (text : String) :
    decodeValue .text (.symbol text) = none := rfl

theorem integer_rejects_string (text : String) :
    decodeValue .integer (.grounded (.string text)) = none := rfl

theorem atoms_rejects_scalar (integer : Int) :
    decodeValue .atoms (.grounded (.int integer)) = none := rfl

theorem no_extra_argument (value : Atom) : decodeValues [] [value] = none := rfl

/-- Generic operations missing from the current native fixed-head executor.
These are host value operations, not source-language production identifiers. -/
inductive Primitive where
  | symbol
  | cons
  | append
  | textAppend
  | integerValue
  | rationalComponents
  deriving DecidableEq, Repr

/-- An independent untyped specification of the required native operations.
Wrong argument shapes and wrong arity fail rather than producing defaults. -/
def executePrimitive : Primitive → List Atom → Option Atom
  | .symbol, [.grounded (.string text)] => some (.symbol text)
  | .cons, [head, .expression tail] => some (.expression (head :: tail))
  | .append, [.expression left, .expression right] => some (.expression (left ++ right))
  | .textAppend, [.grounded (.string left), .grounded (.string right)] =>
      some (.grounded (.string (left ++ right)))
  | .integerValue, [.grounded (.string text)] =>
      (ExactDecimalLexeme.decodeInteger? text).map fun lexeme =>
        .grounded (.int lexeme.value)
  | .rationalComponents, [.grounded (.string text)] =>
      (ExactDecimalLexeme.decodeRational? text).map fun lexeme =>
        .expression [.grounded (.int lexeme.numerator),
          .grounded (.int lexeme.denominator)]
  | _, _ => none

theorem primitive_symbol_exact (text : String) :
    executePrimitive .symbol [encodeValue .text text] =
      some (encodeValue .atom (interpretOperation .symbol (.cons text .nil))) := rfl

theorem primitive_cons_exact (head : Atom) (tail : List Atom) :
    executePrimitive .cons [encodeValue .atom head, encodeValue .atoms tail] =
      some (encodeValue .atoms (interpretOperation .cons (.cons head (.cons tail .nil)))) := rfl

theorem primitive_application_exact (head : Atom) (arguments : List Atom) :
    executePrimitive .cons [encodeValue .atom head, encodeValue .atoms arguments] =
      some (encodeValue .atom
        (interpretOperation .application (.cons head (.cons arguments .nil)))) := rfl

theorem primitive_append_exact (left right : List Atom) :
    executePrimitive .append [encodeValue .atoms left, encodeValue .atoms right] =
      some (encodeValue .atoms (interpretOperation .append (.cons left (.cons right .nil)))) := rfl

theorem primitive_textAppend_exact (left right : String) :
    executePrimitive .textAppend [encodeValue .text left, encodeValue .text right] =
      some (encodeValue .text (interpretOperation .textAppend (.cons left (.cons right .nil)))) := rfl

theorem primitive_integerValue_exact (lexeme : ExactDecimalLexeme.Integer) :
    executePrimitive .integerValue [encodeValue .integerLexeme lexeme] =
      some (encodeValue .integer
        (interpretOperation .integerValue (.cons lexeme .nil))) := by
  simp [executePrimitive, encodeValue, ExactDecimalLexeme.decodeInteger?_text,
    interpretOperation]

theorem primitive_rationalComponents_exact
    (lexeme : ExactDecimalLexeme.Rational) :
    executePrimitive .rationalComponents [encodeValue .rationalLexeme lexeme] =
      some (encodeValue .atoms
        (interpretOperation .rationalComponents (.cons lexeme .nil))) := by
  simp [executePrimitive, encodeValue, ExactDecimalLexeme.decodeRational?_text,
    interpretOperation]

/-- A text value already has the exact host-string representation. -/
theorem string_encoding_identity (text : String) :
    encodeValue .atom (interpretOperation .string (.cons text .nil)) = encodeValue .text text := rfl

/-- An exact integer value needs no conversion at this model boundary. -/
theorem integer_encoding_identity (integer : Int) :
    encodeValue .atom (interpretOperation .integer (.cons integer .nil)) =
      encodeValue .integer integer := rfl

/-- A typed argument sequence is already stored as an ordinary expression. -/
theorem expression_encoding_identity (values : List Atom) :
    encodeValue .atom (interpretOperation .expression (.cons values .nil)) =
      encodeValue .atoms values := rfl

theorem empty_encoding :
    encodeValue .atoms (interpretOperation .empty .nil) = Atom.expression [] := rfl

theorem primitive_symbol_rejects_symbol (name : String) :
    executePrimitive .symbol [.symbol name] = none := rfl

theorem primitive_append_rejects_text (text : String) (values : List Atom) :
    executePrimitive .append [.grounded (.string text), .expression values] = none := rfl

theorem primitive_cons_rejects_extra (head extra : Atom) (tail : List Atom) :
    executePrimitive .cons [head, .expression tail, extra] = none := rfl

/-- The existing action datatype, with host atoms and the required generic
value primitives. This is not a second action IR. -/
abbrev CompiledAction := GrammarConstructorActions.Action Atom Primitive

private def construct (head : String) (arguments : List Atom) : Option Atom :=
  some (.expression (.symbol head :: arguments))

def execute (slots : List Atom) (action : CompiledAction) : Option Atom :=
  action.executeWith some construct executePrimitive slots

/-- Successful slot transport preserves this compiler's actual atom-action
executor, including generic primitives. The relation between two parser
slot lists is supplied by the grammar-specific specialization boundary. -/
theorem transported_execute (slot : Nat → Option Nat)
    (source target : List Atom)
    (matching : ∀ index mapped, slot index = some mapped →
      source[index]? = target[mapped]?)
    (action transported : CompiledAction)
    (transportedEq : ParserActionSlotTransport.transport? slot action =
      some transported) :
    execute target transported = execute source action :=
  ParserActionSlotTransport.transport_executes some construct executePrimitive
    slot source target matching action transported transportedEq

/-- A prepared token action may replace a source child slot. The relation
between source child values and prepared token values is explicit, so this
does not assume that a raw token already is an interpreted name. -/
theorem substituted_execute (replacement : Nat → Option CompiledAction)
    (source target : List Atom)
    (matching : ∀ index action, replacement index = some action →
      source[index]? = execute target action)
    (action substituted : CompiledAction)
    (substitutedEq : ParserActionSubstitution.substitute? replacement action =
      some substituted) :
    execute target substituted = execute source action :=
  ParserActionSubstitution.substitute_executes some construct executePrimitive
    replacement source target matching action substituted substitutedEq

def executeArguments (slots : List Atom) (actions : List CompiledAction) : Option (List Atom) :=
  GrammarConstructorActions.executeArgumentsWith some construct executePrimitive slots actions

theorem execute_primitive (slots : List Atom) (primitive : Primitive)
    (arguments : List CompiledAction) :
    execute slots (.primitive primitive arguments) =
      (executeArguments slots arguments).bind (executePrimitive primitive) := rfl

theorem executeArguments_nil (slots : List Atom) : executeArguments slots [] = some [] := rfl

theorem executeArguments_cons (slots : List Atom) (head : CompiledAction)
    (tail : List CompiledAction) :
    executeArguments slots (head :: tail) = (do
      let value ← execute slots head
      let values ← executeArguments slots tail
      some (value :: values)) := rfl

/-- Lower each intrinsically typed operation. Identity cases are justified by
the encoding identities above; application retains its entire head. -/
def lowerOperation : {inputs : List Kind} → {output : Kind} →
    Operation inputs output → FamilyList (fun _ : Kind => CompiledAction) inputs → CompiledAction
  | _, _, .symbol, .cons text .nil => .primitive .symbol [text]
  | _, _, .string, .cons text .nil => text
  | _, _, .integer, .cons integer .nil => integer
  | _, _, .integerValue, .cons lexeme .nil => .primitive .integerValue [lexeme]
  | _, _, .rationalComponents, .cons lexeme .nil =>
      .primitive .rationalComponents [lexeme]
  | _, _, .empty, .nil => .constant (.expression [])
  | _, _, .cons, .cons head (.cons tail .nil) => .primitive .cons [head, tail]
  | _, _, .append, .cons left (.cons right .nil) => .primitive .append [left, right]
  | _, _, .expression, .cons values .nil => values
  | _, _, .application, .cons head (.cons arguments .nil) => .primitive .cons [head, arguments]
  | _, _, .textAppend, .cons left (.cons right .nil) => .primitive .textAppend [left, right]

/-- Pointwise correspondence of the ordered, typed child actions. -/
def ArgumentsExecute (slots : List Atom) : {kinds : List Kind} →
    FamilyList (fun _ : Kind => CompiledAction) kinds → FamilyList Value kinds → Prop
  | [], .nil, .nil => True
  | kind :: _, .cons action actions, .cons value values =>
      execute slots action = some (encodeValue kind value) ∧ ArgumentsExecute slots actions values

theorem lowerOperation_executes (slots : List Atom) {inputs : List Kind} {output : Kind}
    (operation : Operation inputs output)
    (actions : FamilyList (fun _ : Kind => CompiledAction) inputs)
    (values : FamilyList Value inputs) (correct : ArgumentsExecute slots actions values) :
    execute slots (lowerOperation operation actions) =
      some (encodeValue output (interpretOperation operation values)) := by
  match operation, actions, values with
  | .symbol, .cons action .nil, .cons text .nil =>
      simp only [lowerOperation, execute_primitive, executeArguments_cons,
        executeArguments_nil, correct.1]
      rfl
  | .string, .cons action .nil, .cons text .nil => exact correct.1
  | .integer, .cons action .nil, .cons integer .nil => exact correct.1
  | .integerValue, .cons action .nil, .cons lexeme .nil =>
      simp only [lowerOperation, execute_primitive, executeArguments_cons,
        executeArguments_nil, correct.1]
      exact primitive_integerValue_exact lexeme
  | .rationalComponents, .cons action .nil, .cons lexeme .nil =>
      simp only [lowerOperation, execute_primitive, executeArguments_cons,
        executeArguments_nil, correct.1]
      exact primitive_rationalComponents_exact lexeme
  | .empty, .nil, .nil => rfl
  | .cons, .cons head (.cons tail .nil), .cons first (.cons rest .nil) =>
      simp only [lowerOperation, execute_primitive, executeArguments_cons,
        executeArguments_nil, correct.1, correct.2.1]
      rfl
  | .append, .cons left (.cons right .nil), .cons first (.cons rest .nil) =>
      simp only [lowerOperation, execute_primitive, executeArguments_cons,
        executeArguments_nil, correct.1, correct.2.1]
      rfl
  | .expression, .cons action .nil, .cons values .nil => exact correct.1
  | .application, .cons head (.cons arguments .nil), .cons first (.cons rest .nil) =>
      simp only [lowerOperation, execute_primitive, executeArguments_cons,
        executeArguments_nil, correct.1, correct.2.1]
      rfl
  | .textAppend, .cons left (.cons right .nil), .cons first (.cons rest .nil) =>
      simp only [lowerOperation, execute_primitive, executeArguments_cons,
        executeArguments_nil, correct.1, correct.2.1]
      rfl

mutual
  /-- Compilation is total on typed routes, including arbitrary-headed
  applications and ordered sequences. Slot locations may be parser-layout-derived. -/
  def compileWithSlots {context : List Kind}
      (location : ∀ {kind}, ConstructionVariable context kind → Nat) {output : Kind} :
      MeTTaAtomConstruction.Action context output → CompiledAction
    | .input position => .slot (location position)
    | .source value => .constant (encodeValue _ value)
    | .apply operation arguments =>
        lowerOperation operation (compileArgumentsWithSlots location arguments)

  def compileArgumentsWithSlots {context : List Kind}
      (location : ∀ {kind}, ConstructionVariable context kind → Nat) {inputs : List Kind} :
      OpenConstructionArguments algebra context inputs →
      FamilyList (fun _ : Kind => CompiledAction) inputs
    | .nil => .nil
    | .cons head tail =>
        .cons (compileWithSlots location head) (compileArgumentsWithSlots location tail)
end

mutual
  theorem compileWithSlots_executes {context : List Kind}
      (location : ∀ {kind}, ConstructionVariable context kind → Nat)
      (slots : List Atom) (values : FamilyList Value context)
      (lookup : ∀ {kind} (position : ConstructionVariable context kind),
        slots[location position]? = some (encodeValue kind (position.lookup values)))
      {output : Kind} (route : MeTTaAtomConstruction.Action context output) :
      execute slots (compileWithSlots location route) =
        some (encodeValue output (MeTTaAtomConstruction.Action.run route values)) := by
    match route with
    | .input position => exact lookup position
    | .source value => rfl
    | .apply operation arguments =>
        exact lowerOperation_executes slots operation _ _
          (compileArgumentsWithSlots_execute location slots values lookup arguments)
    termination_by structural route

  theorem compileArgumentsWithSlots_execute {context : List Kind}
      (location : ∀ {kind}, ConstructionVariable context kind → Nat)
      (slots : List Atom) (values : FamilyList Value context)
      (lookup : ∀ {kind} (position : ConstructionVariable context kind),
        slots[location position]? = some (encodeValue kind (position.lookup values)))
      {inputs : List Kind} (arguments : OpenConstructionArguments algebra context inputs) :
      ArgumentsExecute slots (compileArgumentsWithSlots location arguments)
        (OpenConstructionRoute.OpenConstructionArguments.evaluate algebra values arguments) := by
    match arguments with
    | .nil => trivial
    | .cons head tail =>
        exact ⟨compileWithSlots_executes location slots values lookup head,
          compileArgumentsWithSlots_execute location slots values lookup tail⟩
    termination_by structural arguments
end

theorem lookup_encoded {context : List Kind} {kind : Kind}
    (position : ConstructionVariable context kind) (values : FamilyList Value context) :
    (encodeValues values)[GrammarConstructorActions.slotIndex position]? =
      some (encodeValue kind (position.lookup values)) := by
  induction position with
  | here => cases values; rfl
  | there position ih =>
      cases values with
      | cons head tail => exact ih tail

def compile {context : List Kind} {output : Kind}
    (route : MeTTaAtomConstruction.Action context output) : CompiledAction :=
  compileWithSlots GrammarConstructorActions.slotIndex route

theorem compile_executes {context : List Kind} {output : Kind}
    (route : MeTTaAtomConstruction.Action context output) (values : FamilyList Value context) :
    execute (encodeValues values) (compile route) =
      some (encodeValue output (MeTTaAtomConstruction.Action.run route values)) :=
  compileWithSlots_executes GrammarConstructorActions.slotIndex _ values
    (fun position => lookup_encoded position values) route

/-- Structural parser slots include terminals, whereas a typed action's
context contains only nonterminal children. The terminal carrier is supplied
by the lexical boundary and cannot alter a child lookup. -/
def parserAtomValues
    (sortMap : String → Kind) (terminalValue : String → String → Atom) :
    (atoms : List LanguageDefSyntaxCompiler.StructuralAtom) →
    FamilyList Value
      ((LanguageDefGrammarAlgebra.childSorts atoms).map sortMap) →
    List Atom
  | [], .nil => []
  | .terminal token reference :: rest, values =>
      terminalValue token reference :: parserAtomValues sortMap terminalValue rest values
  | .nonterminal _ sort _ :: rest, .cons head tail =>
      encodeValue (sortMap sort) head ::
        parserAtomValues sortMap terminalValue rest tail

theorem parserAtomSlot_lookup (sortMap : String → Kind)
    (terminalValue : String → String → Atom)
    (atoms : List LanguageDefSyntaxCompiler.StructuralAtom)
    (values : FamilyList Value
      ((LanguageDefGrammarAlgebra.childSorts atoms).map sortMap))
    {kind : Kind}
    (position : ConstructionVariable
      ((LanguageDefGrammarAlgebra.childSorts atoms).map sortMap) kind) :
    (parserAtomValues sortMap terminalValue atoms values)[
      GrammarConstructorActions.parserSlot sortMap atoms position]? =
      some (encodeValue kind (position.lookup values)) := by
  induction atoms with
  | nil => nomatch position
  | cons atom rest ih =>
      cases atom with
      | terminal token reference => exact ih values position
      | nonterminal parameter sort reference =>
          cases values with
          | cons head tail =>
              cases position with
              | here => rfl
              | there position => exact ih tail position

/-- The compiled action uses the parser row's actual terminal-inclusive slot
layout and computes the typed source result for all admitted child values. -/
theorem compile_parserAtomSlots_executes (sortMap : String → Kind)
    (terminalValue : String → String → Atom)
    (atoms : List LanguageDefSyntaxCompiler.StructuralAtom)
    (values : FamilyList Value
      ((LanguageDefGrammarAlgebra.childSorts atoms).map sortMap))
    {output : Kind}
    (route : MeTTaAtomConstruction.Action
      ((LanguageDefGrammarAlgebra.childSorts atoms).map sortMap) output) :
    execute (parserAtomValues sortMap terminalValue atoms values)
      (compileWithSlots
        (GrammarConstructorActions.parserSlot sortMap atoms) route) =
      some (encodeValue output (MeTTaAtomConstruction.Action.run route values)) :=
  compileWithSlots_executes (GrammarConstructorActions.parserSlot sortMap atoms)
    _ values (fun position => parserAtomSlot_lookup sortMap terminalValue atoms values position)
    route

/-- Check the complete external slot context even when an operation lowers to
an encoded-value identity. Incorrect sorts cannot bypass that boundary. -/
def executeChecked (context : List Kind) (slots : List Atom) (action : CompiledAction) : Option Atom := do
  let _ ← decodeValues context slots
  execute slots action

theorem compile_executes_checked {context : List Kind} {output : Kind}
    (route : MeTTaAtomConstruction.Action context output) (values : FamilyList Value context) :
    executeChecked context (encodeValues values) (compile route) =
      some (encodeValue output (MeTTaAtomConstruction.Action.run route values)) := by
  simp only [executeChecked, decodeValues_encodeValues]
  exact compile_executes route values

theorem checked_string_identity_rejects_symbol (name : String) :
    executeChecked [.text] [.symbol name] (compile stringAction) = none := rfl

/-! ## Action wire

Slots, constants, fixed-head application and argument lists use the existing
action notation. `pa-primitive` is the explicit extension point; its decoder
accepts exactly this finite primitive inventory. These are internal action
operations, not operators added to the public imported formulas.
-/

def Primitive.encode : Primitive → Atom
  | .symbol => .symbol "atom-symbol"
  | .cons => .symbol "expression-cons"
  | .append => .symbol "expression-append"
  | .textAppend => .symbol "text-append"
  | .integerValue => .symbol "decimal-integer-value"
  | .rationalComponents => .symbol "decimal-rational-components"

def Primitive.decode : Atom → Option Primitive
  | .symbol "atom-symbol" => some .symbol
  | .symbol "expression-cons" => some .cons
  | .symbol "expression-append" => some .append
  | .symbol "text-append" => some .textAppend
  | .symbol "decimal-integer-value" => some .integerValue
  | .symbol "decimal-rational-components" => some .rationalComponents
  | _ => none

theorem Primitive.decode_encode (primitive : Primitive) :
    Primitive.decode primitive.encode = some primitive := by cases primitive <;> rfl

/-- The established `q-zero` / `q-succ` slot-index notation, in host atoms. -/
def encodeIndex : Nat → Atom
  | 0 => .symbol "q-zero"
  | index + 1 => .expression [.symbol "q-succ", encodeIndex index]

def decodeIndex : Atom → Option Nat
  | .symbol "q-zero" => some 0
  | .expression [.symbol "q-succ", rest] => (decodeIndex rest).map Nat.succ
  | _ => none

theorem decodeIndex_encodeIndex (index : Nat) :
    decodeIndex (encodeIndex index) = some index := by
  induction index with
  | zero => rfl
  | succ index ih => simp [encodeIndex, decodeIndex, ih]

mutual
  def encodeAction : CompiledAction → Atom
    | .slot index => .expression [.symbol "pa-slot", encodeIndex index]
    | .constant value => .expression [.symbol "pa-const", value]
    | .apply head arguments =>
        .expression [.symbol "pa-apply", .symbol head, encodeArguments arguments]
    | .primitive primitive arguments =>
        .expression [.symbol "pa-primitive", primitive.encode, encodeArguments arguments]

  def encodeArguments : List CompiledAction → Atom
    | [] => .symbol "pa-nil"
    | head :: tail => .expression [.symbol "pa-cons", encodeAction head, encodeArguments tail]
end

mutual
  def decodeAction : Atom → Option CompiledAction
    | .expression [.symbol "pa-slot", index] =>
        (decodeIndex index).map GrammarConstructorActions.Action.slot
    | .expression [.symbol "pa-const", value] => some (.constant value)
    | .expression [.symbol "pa-apply", .symbol head, arguments] =>
        (decodeArguments arguments).map (GrammarConstructorActions.Action.apply head)
    | .expression [.symbol "pa-primitive", primitive, arguments] => do
        let operation ← Primitive.decode primitive
        let actions ← decodeArguments arguments
        some (.primitive operation actions)
    | _ => none
  termination_by atom => sizeOf atom

  def decodeArguments : Atom → Option (List CompiledAction)
    | .symbol "pa-nil" => some []
    | .expression [.symbol "pa-cons", head, tail] => do
        let action ← decodeAction head
        let actions ← decodeArguments tail
        some (action :: actions)
    | _ => none
  termination_by atom => sizeOf atom
end

mutual
  theorem decodeAction_encodeAction (action : CompiledAction) :
      decodeAction (encodeAction action) = some action := by
    match action with
    | .slot index => simp [encodeAction, decodeAction, decodeIndex_encodeIndex]
    | .constant value => simp [encodeAction, decodeAction]
    | .apply head arguments =>
        simp only [encodeAction, decodeAction, decodeArguments_encodeArguments arguments]
        rfl
    | .primitive primitive arguments =>
        simp only [encodeAction, decodeAction, Primitive.decode_encode,
          decodeArguments_encodeArguments arguments]
        rfl
    termination_by structural action

  theorem decodeArguments_encodeArguments (arguments : List CompiledAction) :
      decodeArguments (encodeArguments arguments) = some arguments := by
    match arguments with
    | [] => simp [encodeArguments, decodeArguments]
    | head :: tail =>
        simp only [encodeArguments, decodeArguments, decodeAction_encodeAction head,
          decodeArguments_encodeArguments tail]
        rfl
    termination_by structural arguments
end

/-- The emitted action has exactly the typed source's observation when
decoded and executed with its admitted input sorts. -/
theorem exported_action_executes {context : List Kind} {output : Kind}
    (route : MeTTaAtomConstruction.Action context output) (values : FamilyList Value context) :
    ((decodeAction (encodeAction (compile route))).bind
      (executeChecked context (encodeValues values))) =
      some (encodeValue output (MeTTaAtomConstruction.Action.run route values)) := by
  rw [decodeAction_encodeAction]
  exact compile_executes_checked route values

/-! ## Existing postfix wire and its stack execution

The program is the physical `pbc-cons` list, not another intermediate syntax.
The stack evaluator decodes each instruction, checks indices and primitive
arity, and never calls a host expression evaluator.
-/

mutual
  def encodeCodeWithTail : CompiledAction → Atom → Atom
    | .slot index, tail => .expression [.symbol "pbc-cons",
        .expression [.symbol "pbc-push-slot", encodeIndex index], tail]
    | .constant value, tail => .expression [.symbol "pbc-cons",
        .expression [.symbol "pbc-push-const", value], tail]
    | .apply head arguments, tail => encodeArgumentCode arguments
        (.expression [.symbol "pbc-cons",
          .expression [.symbol "pbc-apply", .symbol head, encodeIndex arguments.length], tail])
    | .primitive primitive arguments, tail => encodeArgumentCode arguments
        (.expression [.symbol "pbc-cons",
          .expression [.symbol "pbc-primitive", primitive.encode, encodeIndex arguments.length], tail])

  def encodeArgumentCode : List CompiledAction → Atom → Atom
    | [], tail => tail
    | head :: rest, tail => encodeCodeWithTail head (encodeArgumentCode rest tail)
end

def encodeCode (action : CompiledAction) : Atom :=
  encodeCodeWithTail action (.symbol "pbc-nil")

/-- Pop in stack order, restoring the source argument order. -/
def popValues : Nat → List Atom → Option (List Atom × List Atom)
  | 0, stack => some ([], stack)
  | count + 1, head :: tail => do
      let (values, rest) ← popValues count tail
      some (values ++ [head], rest)
  | _ + 1, [] => none

theorem popValues_prefix (initial stack : List Atom) :
    popValues initial.length (initial ++ stack) = some (initial.reverse, stack) := by
  induction initial with
  | nil => rfl
  | cons head tail ih => simp [popValues, ih]

theorem popValues_arguments (values stack : List Atom) :
    popValues values.length (values.reverse ++ stack) = some (values, stack) := by
  simpa using popValues_prefix values.reverse stack

def executeInstruction (slots : List Atom) : Atom → List Atom → Option (List Atom)
  | .expression [.symbol "pbc-push-slot", index], stack => do
      let slot ← decodeIndex index
      let value ← slots[slot]?
      some (value :: stack)
  | .expression [.symbol "pbc-push-const", value], stack => some (value :: stack)
  | .expression [.symbol "pbc-apply", .symbol head, arity], stack => do
      let count ← decodeIndex arity
      let (arguments, rest) ← popValues count stack
      let value ← construct head arguments
      some (value :: rest)
  | .expression [.symbol "pbc-primitive", operation, arity], stack => do
      let primitive ← Primitive.decode operation
      let count ← decodeIndex arity
      let (arguments, rest) ← popValues count stack
      let value ← executePrimitive primitive arguments
      some (value :: rest)
  | _, _ => none

def executeCode (slots : List Atom) : Atom → List Atom → Option (List Atom)
  | .symbol "pbc-nil", stack => some stack
  | .expression [.symbol "pbc-cons", instruction, tail], stack => do
      let next ← executeInstruction slots instruction stack
      executeCode slots tail next
  | _, _ => none
termination_by code => sizeOf code

theorem executeCode_cons (slots : List Atom) (instruction tail : Atom) (stack : List Atom) :
    executeCode slots (.expression [.symbol "pbc-cons", instruction, tail]) stack =
      (executeInstruction slots instruction stack).bind (executeCode slots tail) := by
  rw [executeCode]
  rfl

theorem executeInstruction_apply (slots values stack : List Atom) (head : String) :
    executeInstruction slots
      (.expression [.symbol "pbc-apply", .symbol head, encodeIndex values.length])
      (values.reverse ++ stack) =
      (construct head values).map (· :: stack) := by
  simp [executeInstruction, decodeIndex_encodeIndex, popValues_arguments]
  rfl

theorem executeInstruction_primitive (slots values stack : List Atom) (primitive : Primitive) :
    executeInstruction slots
      (.expression [.symbol "pbc-primitive", primitive.encode, encodeIndex values.length])
      (values.reverse ++ stack) =
      (executePrimitive primitive values).map (· :: stack) := by
  simp [executeInstruction, Primitive.decode_encode, decodeIndex_encodeIndex, popValues_arguments]
  cases executePrimitive primitive values <;> rfl

theorem executeArguments_length (slots : List Atom) (actions : List CompiledAction)
    (values : List Atom) (executed : executeArguments slots actions = some values) :
    values.length = actions.length := by
  induction actions generalizing values with
  | nil => simp [executeArguments_nil] at executed; subst values; rfl
  | cons action actions ih =>
      rw [executeArguments_cons] at executed
      cases first : execute slots action with
      | none => simp [first] at executed
      | some value =>
          cases rest : executeArguments slots actions with
          | none => simp [first, rest] at executed
          | some more =>
              simp [first, rest] at executed
              subst values
              exact congrArg Nat.succ (ih more rest)

mutual
  /-- Continuation-level preservation and reflection, including failed actions. -/
  theorem encodeCodeWithTail_executes (slots stack : List Atom) (tail : Atom)
      (action : CompiledAction) :
      executeCode slots (encodeCodeWithTail action tail) stack =
        (execute slots action).bind (fun value => executeCode slots tail (value :: stack)) := by
    match action with
    | .slot index =>
        simp [encodeCodeWithTail, executeCode_cons, executeInstruction, decodeIndex_encodeIndex,
          execute, GrammarConstructorActions.Action.executeWith]
        cases slots[index]? <;> rfl
    | .constant value =>
        simp [encodeCodeWithTail, executeCode_cons, executeInstruction,
          execute, GrammarConstructorActions.Action.executeWith]
    | .apply head arguments =>
        rw [encodeCodeWithTail, encodeArgumentCode_executes]
        change _ = ((executeArguments slots arguments).bind (construct head)).bind _
        cases executed : executeArguments slots arguments with
        | none => rfl
        | some values =>
            have length := executeArguments_length slots arguments values executed
            simp only [Option.bind_some]
            rw [← length, executeCode_cons, executeInstruction_apply]
            rfl
    | .primitive primitive arguments =>
        rw [encodeCodeWithTail, encodeArgumentCode_executes]
        change _ = ((executeArguments slots arguments).bind (executePrimitive primitive)).bind _
        cases executed : executeArguments slots arguments with
        | none => rfl
        | some values =>
            have length := executeArguments_length slots arguments values executed
            simp only [Option.bind_some]
            rw [← length, executeCode_cons, executeInstruction_primitive]
            cases executePrimitive primitive values <;> rfl
    termination_by structural action

  theorem encodeArgumentCode_executes (slots stack : List Atom) (tail : Atom)
      (arguments : List CompiledAction) :
      executeCode slots (encodeArgumentCode arguments tail) stack =
        (executeArguments slots arguments).bind
          (fun values => executeCode slots tail (values.reverse ++ stack)) := by
    match arguments with
    | [] => simp [encodeArgumentCode, executeArguments_nil]
    | head :: rest =>
        rw [encodeArgumentCode, encodeCodeWithTail_executes]
        simp only [executeArguments_cons]
        cases first : execute slots head with
        | none => rfl
        | some value =>
            simp only [Option.bind_some]
            rw [encodeArgumentCode_executes]
            cases executeArguments slots rest with
            | none => rfl
            | some values => simp [List.reverse_cons, List.append_assoc]
    termination_by structural arguments
end

def executeCodeResult (slots : List Atom) (code : Atom) : Option Atom := do
  let stack ← executeCode slots code []
  match stack with
  | [value] => some value
  | _ => none

theorem encodeCode_executes (slots : List Atom) (action : CompiledAction) :
    executeCodeResult slots (encodeCode action) = execute slots action := by
  simp only [executeCodeResult, encodeCode, encodeCodeWithTail_executes]
  cases execute slots action <;> simp [executeCode]

def executeCodeChecked (context : List Kind) (slots : List Atom) (code : Atom) : Option Atom := do
  let _ ← decodeValues context slots
  executeCodeResult slots code

theorem compiled_code_executes_checked {context : List Kind} {output : Kind}
    (route : MeTTaAtomConstruction.Action context output) (values : FamilyList Value context) :
    executeCodeChecked context (encodeValues values) (encodeCode (compile route)) =
      some (encodeValue output (MeTTaAtomConstruction.Action.run route values)) := by
  simp only [executeCodeChecked, decodeValues_encodeValues, encodeCode_executes]
  exact compile_executes route values

/-! ## Connection to the authored primitive lowering rule

The new rule is selected from the actual source file, then instantiated by
the existing source substitution operation. Its premise is exactly the
argument-list continuation used above. This connects the rule schema; it
does not assert a complete Horn-search or native-runner correspondence.
-/

namespace AuthoredSource

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Rewrite rawRewriteAt?)
open SourceSExprPatternInstantiation (Env instantiate? instantiateList?)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def authoredSyntax : SExpr :=
  metta_sexpr_file% petta "../../../../../../hyperon/cetta-prime-nik-20260811/experiments/gslt2parse_foundation/presentations/compiler/parser_action_bytecode_compiler_v1.metta"

private def app (head : String) (arguments : List SExpr) : SExpr :=
  .list (.atom head :: arguments)

private def primitiveRow : Rewrite :=
  { name := "lower-pack-action-primitive",
    head := app "lower-pack-action-dl"
      [app "pa-primitive" [.atom "?operation", .atom "?arguments"],
        .atom "?tail", .atom "?code"],
    body := [app "lower-pack-action-list-dl"
      [.atom "?arguments",
        app "pbc-cons" [app "pbc-primitive" [.atom "?operation", .atom "?arity"],
          .atom "?tail"], .atom "?code", .atom "?arity"]] }

private theorem primitive_row_exact : rawRewriteAt? authoredSyntax 7 = some primitiveRow := rfl

def instantiatePrimitive? (environment : Env) : Option (SExpr × List SExpr) := do
  let row ← rawRewriteAt? authoredSyntax 7
  let head ← instantiate? environment row.head
  let body ← instantiateList? environment row.body
  some (head, body)

/-- The actual authored rule preserves the argument list and continuation
for every inert source payload; its primitive instruction is after the args. -/
theorem primitive_rule_exact (operation arguments tail code arity : SExpr) :
    instantiatePrimitive?
      [("?operation", operation), ("?arguments", arguments), ("?tail", tail),
        ("?code", code), ("?arity", arity)] =
    some (app "lower-pack-action-dl" [app "pa-primitive" [operation, arguments], tail, code],
      [app "lower-pack-action-list-dl"
        [arguments, app "pbc-cons" [app "pbc-primitive" [operation, arity], tail], code, arity]]) := by
  unfold instantiatePrimitive?
  rw [primitive_row_exact]
  simp [primitiveRow, app, instantiate?, instantiateList?, SourceIntegerProvider.sourceVariableToken]

/-- The encoder realizes exactly that argument-list continuation shape.
The postfix execution theorem separately establishes its resulting value. -/
theorem primitive_encoder_continuation (operation : Primitive)
    (arguments : List CompiledAction) (tail : Atom) :
    encodeCodeWithTail (.primitive operation arguments) tail =
      encodeArgumentCode arguments
        (.expression [.symbol "pbc-cons",
          .expression [.symbol "pbc-primitive", operation.encode, encodeIndex arguments.length],
          tail]) := rfl

end AuthoredSource

namespace Examples

theorem compiled_expression_head (function argument : Atom) :
    executeChecked [.atom, .atoms]
      [.expression [function], .expression [argument]] (compile applicationAction) =
        some (.expression [.expression [function], argument]) :=
  compile_executes_checked applicationAction
    (.cons (.expression [function]) (.cons [argument] .nil))

theorem compiled_nested_application :
    executeChecked [.atom, .atom, .atom]
      [.symbol "f", .symbol "g", .symbol "x"]
      (compile MeTTaAtomConstruction.Examples.nestedApplication) =
        some (.expression [.symbol "f", .expression [.symbol "g", .symbol "x"]]) :=
  compile_executes_checked MeTTaAtomConstruction.Examples.nestedApplication
    (.cons (.symbol "f") (.cons (.symbol "g") (.cons (.symbol "x") .nil)))

theorem compiled_wrong_association_rejected :
    executeChecked [.atom, .atom, .atom]
      [.symbol "f", .symbol "g", .symbol "x"]
      (compile MeTTaAtomConstruction.Examples.nestedApplication) ≠
        some (.expression [.expression [.symbol "f", .symbol "g"], .symbol "x"]) := by
  rw [compiled_nested_application]
  intro equality
  cases equality

theorem compiled_order_and_duplicates (first second : Atom) :
    executeChecked [.atoms, .atoms]
      [.expression [first, second], .expression [first]] (compile appendAction) =
        some (.expression [first, second, first]) :=
  compile_executes_checked appendAction (.cons [first, second] (.cons [first] .nil))

theorem compiled_missing_argument_rejected :
    executeChecked [.atom, .atoms] [.symbol "f"] (compile applicationAction) = none := rfl

theorem malformed_primitive_rejected :
    decodeAction (.expression [.symbol "pa-primitive", .symbol "unknown", .symbol "pa-nil"]) =
      none := by simp [decodeAction, Primitive.decode]

theorem compiled_bytecode_nested_application :
    executeCodeChecked [.atom, .atom, .atom]
      [.symbol "f", .symbol "g", .symbol "x"]
      (encodeCode (compile MeTTaAtomConstruction.Examples.nestedApplication)) =
        some (.expression [.symbol "f", .expression [.symbol "g", .symbol "x"]]) :=
  compiled_code_executes_checked MeTTaAtomConstruction.Examples.nestedApplication
    (.cons (.symbol "f") (.cons (.symbol "g") (.cons (.symbol "x") .nil)))

theorem bytecode_wrong_association_rejected :
    executeCodeChecked [.atom, .atom, .atom]
      [.symbol "f", .symbol "g", .symbol "x"]
      (encodeCode (compile MeTTaAtomConstruction.Examples.nestedApplication)) ≠
        some (.expression [.expression [.symbol "f", .symbol "g"], .symbol "x"]) := by
  rw [compiled_bytecode_nested_application]
  intro equality
  cases equality

theorem primitive_bytecode_underflow_rejected :
    executeInstruction []
      (.expression [.symbol "pbc-primitive", Primitive.cons.encode, encodeIndex 2])
      [.symbol "f"] = none := by
  simp [executeInstruction, Primitive.decode_encode, decodeIndex_encodeIndex, popValues]

theorem primitive_bytecode_wrong_operand_rejected :
    executeInstruction []
      (.expression [.symbol "pbc-primitive", Primitive.symbol.encode, encodeIndex 1])
      [.symbol "not-text"] = none := by
  simp [executeInstruction, Primitive.decode_encode, decodeIndex_encodeIndex,
    popValues, executePrimitive]

theorem primitive_bytecode_unknown_rejected :
    executeInstruction []
      (.expression [.symbol "pbc-primitive", .symbol "unknown", encodeIndex 0]) [] = none := by
  simp [executeInstruction, Primitive.decode]

theorem bytecode_extra_result_rejected :
    executeCodeResult [] (encodeCodeWithTail (.constant (.symbol "first"))
      (encodeCode (.constant (.symbol "second")))) = none := by
  simp [executeCodeResult, encodeCode, encodeCodeWithTail_executes, execute,
    GrammarConstructorActions.Action.executeWith, executeCode]

theorem bytecode_typed_identity_rejects_wrong_sort :
    executeCodeChecked [.text] [.symbol "not-text"]
      (encodeCode (compile stringAction)) = none := rfl

end Examples

#print axioms compileWithSlots_executes
#print axioms parserAtomSlot_lookup
#print axioms compile_parserAtomSlots_executes
#print axioms compile_executes_checked
#print axioms exported_action_executes
#print axioms encodeCodeWithTail_executes
#print axioms encodeCode_executes
#print axioms compiled_code_executes_checked
#print axioms AuthoredSource.primitive_rule_exact
#print axioms Examples.bytecode_wrong_association_rejected
#print axioms Examples.compiled_wrong_association_rejected

#print axioms encodeValue_injective
#print axioms decodeValues_encodeValues
#print axioms decodeValues_length

end Mettapedia.GSLT.Parsing.MeTTaAtomActionCompiler
