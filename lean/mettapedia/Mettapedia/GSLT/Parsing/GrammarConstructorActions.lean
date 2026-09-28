import Mettapedia.GSLT.Parsing.LanguageDefGrammarNativeType
import Mettapedia.GSLT.LanguageDef.ConstructionProvenance.RouteComposition
import Mettapedia.GSLT.LanguageDef.CettaWireTerm

/-!
# Grammar-indexed constructor actions

An interpretation is supplied as open construction routes over the existing
many-sorted algebra, one route at every source production's exact child type.
These routes use positional, intrinsically sorted inputs rather than child
names. This is a construction interface, not a witness-coverage test.

The constructor-only fragment is compiled to the existing ParserPack `pa-*`
action language. Its partial, untyped execution is proved to agree with the
typed route for every well-typed environment. Dynamic application, lexical
decoding, and list splicing require further supported operations; they are
not approximated by this constructor-only fragment. Native C execution and
the concrete whole-TPTP interpretation are separate remaining connections.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GrammarConstructorActions

open Mettapedia.GSLT.LanguageDef.ConstructionProvenance
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted
open Mettapedia.GSLT.Parsing.LanguageDefGrammarAlgebra
open Mettapedia.GSLT.Parsing.LanguageDefGrammarNativeType
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.LanguageDef.CettaWire

/-- Reindex a family along a map of sorts, retaining every occurrence. -/
def reindexValues {Kind : Type} {Value : Kind → Type}
    (sortMap : String → Kind) : {sorts : List String} →
    FamilyList (fun sort => Value (sortMap sort)) sorts →
    FamilyList Value (sorts.map sortMap)
  | [], .nil => .nil
  | _ :: _, .cons head tail => .cons head (reindexValues sortMap tail)

/-- A whole grammar interpretation is a dependent family of source actions.
There is no optional action or default production in this interface. -/
structure Templates (rules : List CompiledRule)
    (target : ManySortedConstructionAlgebra.{0, 0, 0, 0}) where
  sortMap : String → target.Kind
  action : (index : Fin rules.length) →
    OpenConstructionRoute target
      ((childSorts rules[index].atoms).map sortMap)
      (sortMap rules[index].source.category)

def Templates.interpretation {rules : List CompiledRule}
    {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
    (templates : Templates rules target) : Interpretation rules where
  Carrier := fun sort => target.Object (templates.sortMap sort)
  operation := fun (.at index) values =>
    OpenConstructionRoute.evaluate target
      (reindexValues templates.sortMap values) (templates.action index)

/-- The generic operational OSLF proof admits this particular structural
interpreter. The generated action compiler below has its own preservation
theorem; admission does not assert correctness of arbitrary native code. -/
def Templates.interpreter {rules : List CompiledRule}
    {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
    (templates : Templates rules target) :
    AdmittedInterpreter templates.interpretation :=
  directInterpreter templates.interpretation

/-- Positional erasure of a sorted variable. -/
def slotIndex {Kind : Type} : {context : List Kind} → {kind : Kind} →
    ConstructionVariable context kind → Nat
  | _, _, .here => 0
  | _, _, .there position => slotIndex position + 1

def encodeValues {Kind : Type} {Value : Kind → Type}
    (encode : ∀ kind, Value kind → Term) : {kinds : List Kind} →
    FamilyList Value kinds → List Term
  | [], .nil => []
  | kind :: _, .cons head tail => encode kind head :: encodeValues encode tail

theorem lookup_encoded {Kind : Type} {Value : Kind → Type}
    (encode : ∀ kind, Value kind → Term) {context : List Kind} {kind : Kind}
    (position : ConstructionVariable context kind)
    (values : FamilyList Value context) :
    (encodeValues encode values)[slotIndex position]? =
      some (encode kind (position.lookup values)) := by
  induction position with
  | here => cases values; rfl
  | there position ih =>
      cases values with
      | cons head tail => exact ih tail

/-- The physical constructor law needed to lower one target operation to
`pa-apply`. It is deliberately stronger than knowing an operation's name. -/
structure ConstructorEncoding
    (target : ManySortedConstructionAlgebra.{0, 0, 0, 0}) where
  value : ∀ kind, target.Object kind → Term
  head : {inputs : List target.Kind} → {output : target.Kind} →
    target.Operation inputs output → String
  operation_exact : ∀ {inputs output}
    (operation : target.Operation inputs output)
    (arguments : FamilyList target.Object inputs),
    value output (target.interpretOperation operation arguments) =
      .application (head operation) (encodeValues value arguments)

/-- The compiler's internal action syntax, not a public formula carrier.
The defaults describe exactly the existing `pa-slot`, `pa-const`, `pa-apply`
wire. A nonempty primitive family requires an explicitly supplied executor
and wire implementation; the legacy encoders cannot emit such actions. -/
inductive Action (Constant : Type := Term) (Primitive : Type := Empty) where
  | slot (index : Nat)
  | constant (value : Constant)
  | apply (head : String) (arguments : List (Action Constant Primitive))
  | primitive (operation : Primitive) (arguments : List (Action Constant Primitive))

mutual
  /-- Execute this action language with explicit meanings for its constants,
  fixed-head constructors and generic primitives. No host evaluation is called. -/
  def Action.executeWith {Constant Primitive Value : Type}
      (constant : Constant → Option Value)
      (constructor : String → List Value → Option Value)
      (primitive : Primitive → List Value → Option Value)
      (slots : List Value) : Action Constant Primitive → Option Value
    | .slot index => slots[index]?
    | .constant value => constant value
    | .apply head arguments => do
        let values ← executeArgumentsWith constant constructor primitive slots arguments
        constructor head values
    | .primitive operation arguments => do
        let values ← executeArgumentsWith constant constructor primitive slots arguments
        primitive operation values

  def executeArgumentsWith {Constant Primitive Value : Type}
      (constant : Constant → Option Value)
      (constructor : String → List Value → Option Value)
      (primitive : Primitive → List Value → Option Value)
      (slots : List Value) : List (Action Constant Primitive) → Option (List Value)
    | [] => some []
    | head :: tail => do
        let value ← head.executeWith constant constructor primitive slots
        let values ← executeArgumentsWith constant constructor primitive slots tail
        some (value :: values)
end

mutual
  def Action.execute (slots : List Term) : Action → Option Term
    | .slot index => slots[index]?
    | .constant value => some value
    | .apply head arguments =>
        (executeArguments slots arguments).map (Term.application head)
    | .primitive impossible _ => nomatch impossible

  def executeArguments (slots : List Term) : List Action → Option (List Term)
    | [] => some []
    | head :: tail => do
        let value ← head.execute slots
        let values ← executeArguments slots tail
        some (value :: values)
end

mutual
  /-- The parameterized executor preserves the legacy action language exactly. -/
  theorem Action.executeWith_legacy (slots : List Term) (action : Action) :
      action.executeWith some (fun head values => some (.application head values))
        (fun impossible _ => nomatch impossible) slots = action.execute slots := by
    match action with
    | .slot index => rfl
    | .constant value => rfl
    | .apply head arguments =>
        simp only [Action.executeWith, Action.execute, executeArgumentsWith_legacy]
        cases executeArguments slots arguments <;> rfl
    | .primitive impossible _ => nomatch impossible
    termination_by structural action

  theorem executeArgumentsWith_legacy (slots : List Term) (arguments : List Action) :
      executeArgumentsWith some (fun head values => some (.application head values))
        (fun impossible _ => nomatch impossible) slots arguments = executeArguments slots arguments := by
    match arguments with
    | [] => rfl
    | head :: tail =>
        simp only [executeArgumentsWith, executeArguments, Action.executeWith_legacy,
          executeArgumentsWith_legacy]
    termination_by structural arguments
end

mutual
  def compileWithSlots {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
      (encoding : ConstructorEncoding target)
      {context : List target.Kind}
      (location : ∀ {kind}, ConstructionVariable context kind → Nat)
      {output : target.Kind} :
      OpenConstructionRoute target context output → Action
    | .input position => .slot (location position)
    | .source value => .constant (encoding.value _ (target.interpretSource value))
    | .apply operation arguments =>
        .apply (encoding.head operation) (compileArgumentsWithSlots encoding location arguments)

  def compileArgumentsWithSlots {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
      (encoding : ConstructorEncoding target)
      {context : List target.Kind}
      (location : ∀ {kind}, ConstructionVariable context kind → Nat)
      {inputs : List target.Kind} :
      OpenConstructionArguments target context inputs → List Action
    | .nil => []
    | .cons head tail => compileWithSlots encoding location head ::
        compileArgumentsWithSlots encoding location tail
end

mutual
  theorem compileWithSlots_executes {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
      (encoding : ConstructorEncoding target)
      {context : List target.Kind}
      (location : ∀ {kind}, ConstructionVariable context kind → Nat)
      (slots : List Term) (values : FamilyList target.Object context)
      (lookup : ∀ {kind} (position : ConstructionVariable context kind),
        slots[location position]? = some (encoding.value kind (position.lookup values)))
      {output : target.Kind} (route : OpenConstructionRoute target context output) :
      (compileWithSlots encoding location route).execute slots =
        some (encoding.value output (OpenConstructionRoute.evaluate target values route)) := by
    match route with
    | .input position => exact lookup position
    | .source value => rfl
    | .apply operation arguments =>
        change (executeArguments _ (compileArgumentsWithSlots encoding location arguments)).map
          (Term.application (encoding.head operation)) = _
        rw [compileArgumentsWithSlots_execute encoding location slots values lookup arguments]
        change some (.application _ _) = some (encoding.value _
          (target.interpretOperation operation
            (OpenConstructionRoute.OpenConstructionArguments.evaluate target values arguments)))
        rw [encoding.operation_exact]
    termination_by structural route

  theorem compileArgumentsWithSlots_execute
      {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
      (encoding : ConstructorEncoding target)
      {context : List target.Kind}
      (location : ∀ {kind}, ConstructionVariable context kind → Nat)
      (slots : List Term) (values : FamilyList target.Object context)
      (lookup : ∀ {kind} (position : ConstructionVariable context kind),
        slots[location position]? = some (encoding.value kind (position.lookup values)))
      {inputs : List target.Kind}
      (arguments : OpenConstructionArguments target context inputs) :
      executeArguments slots (compileArgumentsWithSlots encoding location arguments) =
        some (encodeValues encoding.value
          (OpenConstructionRoute.OpenConstructionArguments.evaluate target values arguments)) := by
    match arguments with
    | .nil => rfl
    | .cons head tail =>
        simp only [compileArgumentsWithSlots, executeArguments,
          compileWithSlots_executes encoding location slots values lookup head,
          compileArgumentsWithSlots_execute encoding location slots values lookup tail]
        rfl
    termination_by structural arguments
end

/-- Child-only slots are one realization of the general typed slot binding. -/
def compile {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
    (encoding : ConstructorEncoding target)
    {context : List target.Kind} {output : target.Kind}
    (route : OpenConstructionRoute target context output) : Action :=
  compileWithSlots encoding slotIndex route

theorem compile_executes {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
    (encoding : ConstructorEncoding target)
    {context : List target.Kind} {output : target.Kind}
    (route : OpenConstructionRoute target context output)
    (values : FamilyList target.Object context) :
    (compile encoding route).execute (encodeValues encoding.value values) =
      some (encoding.value output (OpenConstructionRoute.evaluate target values route)) :=
  compileWithSlots_executes encoding slotIndex _ values
    (fun position => lookup_encoded encoding.value position values) route

/-- Locate a semantic child in a parser row that also contains terminals.
The impossible empty case has no default index. -/
def parserSlot {Kind : Type} (sortMap : String → Kind) :
    (atoms : List StructuralAtom) → {kind : Kind} →
    ConstructionVariable ((childSorts atoms).map sortMap) kind → Nat
  | [], _, position => nomatch position
  | .terminal _ _ :: rest, _, position => parserSlot sortMap rest position + 1
  | .nonterminal _ _ _ :: _, _, .here => 0
  | .nonterminal _ _ _ :: rest, _, .there position =>
      parserSlot sortMap rest position + 1

/-- The reference row layout leaves terminal payloads to the lexical boundary;
their values have no effect on constructor-child lookup. -/
def parserValues {Kind : Type} {Value : Kind → Type}
    (sortMap : String → Kind) (encode : ∀ kind, Value kind → Term)
    (terminalValue : String → String → Term) :
    (atoms : List StructuralAtom) →
    FamilyList Value ((childSorts atoms).map sortMap) → List Term
  | [], .nil => []
  | .terminal token reference :: rest, values =>
      terminalValue token reference :: parserValues sortMap encode terminalValue rest values
  | .nonterminal _ sort _ :: rest, .cons head tail =>
      encode (sortMap sort) head :: parserValues sortMap encode terminalValue rest tail

theorem parserValues_length {Kind : Type} {Value : Kind → Type}
    (sortMap : String → Kind) (encode : ∀ kind, Value kind → Term)
    (terminalValue : String → String → Term) (atoms : List StructuralAtom)
    (values : FamilyList Value ((childSorts atoms).map sortMap)) :
    (parserValues sortMap encode terminalValue atoms values).length = atoms.length := by
  induction atoms with
  | nil => cases values; rfl
  | cons atom rest ih =>
      cases atom with
      | terminal token reference => exact congrArg Nat.succ (ih values)
      | nonterminal parameter sort reference =>
          cases values with
          | cons head tail => simp only [parserValues, List.length_cons, ih]

theorem parserSlot_lookup {Kind : Type} {Value : Kind → Type}
    (sortMap : String → Kind) (encode : ∀ kind, Value kind → Term)
    (terminalValue : String → String → Term) (atoms : List StructuralAtom)
    (values : FamilyList Value ((childSorts atoms).map sortMap))
    {kind : Kind} (position : ConstructionVariable ((childSorts atoms).map sortMap) kind) :
    (parserValues sortMap encode terminalValue atoms values)[parserSlot sortMap atoms position]? =
      some (encode kind (position.lookup values)) := by
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

/-- Relocation is generated from the structural row, not handwritten child
offsets. Lexical payload extraction and prepared-pack normalization remain
separate obligations when binding this row to a concrete parser artifact. -/
theorem compile_parserSlots_executes
    {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
    (encoding : ConstructorEncoding target) (sortMap : String → target.Kind)
    (terminalValue : String → String → Term) (atoms : List StructuralAtom)
    (values : FamilyList target.Object ((childSorts atoms).map sortMap))
    {output : target.Kind}
    (route : OpenConstructionRoute target ((childSorts atoms).map sortMap) output) :
    (compileWithSlots encoding (parserSlot sortMap atoms) route).execute
        (parserValues sortMap encoding.value terminalValue atoms values) =
      some (encoding.value output (OpenConstructionRoute.evaluate target values route)) :=
  compileWithSlots_executes encoding (parserSlot sortMap atoms) _ values
    (parserSlot_lookup sortMap encoding.value terminalValue atoms values) route

/-- Existing ParserPack natural-number notation. -/
def encodeIndex : Nat → Term
  | 0 => .symbol "q-zero"
  | index + 1 => .application "q-succ" [encodeIndex index]

mutual
  def Action.encode : Action → Term
    | .slot index => .application "pa-slot" [encodeIndex index]
    | .constant value => .application "pa-const" [value]
    | .apply head arguments =>
        .application "pa-apply" [.symbol head, encodeArguments arguments]
    | .primitive impossible _ => nomatch impossible

  def encodeArguments : List Action → Term
    | [] => .symbol "pa-nil"
    | head :: tail => .application "pa-cons" [head.encode, encodeArguments tail]
end

/-- Decode the exact index notation accepted by the native action loader. -/
def decodeIndex : Term → Option Nat
  | .symbol "q-zero" => some 0
  | .application "q-succ" [rest] => (decodeIndex rest).map Nat.succ
  | _ => none

theorem decodeIndex_encodeIndex (index : Nat) :
    decodeIndex (encodeIndex index) = some index := by
  induction index with
  | zero => rfl
  | succ index ih => simp [encodeIndex, decodeIndex, ih]

mutual
  def Action.decode : Term → Option Action
    | .application "pa-slot" [index] => (decodeIndex index).map Action.slot
    | .application "pa-const" [value] => some (.constant value)
    | .application "pa-apply" [.symbol head, arguments] =>
        (decodeArguments arguments).map (Action.apply head)
    | _ => none
  termination_by term => sizeOf term

  def decodeArguments : Term → Option (List Action)
    | .symbol "pa-nil" => some []
    | .application "pa-cons" [head, tail] => do
        let action ← Action.decode head
        let actions ← decodeArguments tail
        some (action :: actions)
    | _ => none
  termination_by term => sizeOf term
end

mutual
  theorem Action.decode_encode (action : Action) :
      Action.decode action.encode = some action := by
    match action with
    | .slot index => simp [Action.encode, Action.decode, decodeIndex_encodeIndex]
    | .constant value => simp [Action.encode, Action.decode]
    | .apply head arguments =>
        simp only [Action.encode, Action.decode, decodeArguments_encode arguments]
        rfl
    | .primitive impossible _ => nomatch impossible
    termination_by structural action

  theorem decodeArguments_encode (arguments : List Action) :
      decodeArguments (encodeArguments arguments) = some arguments := by
    match arguments with
    | [] => simp [encodeArguments, decodeArguments]
    | head :: tail =>
        simp only [encodeArguments, decodeArguments,
          Action.decode_encode head, decodeArguments_encode tail]
        rfl
    termination_by structural arguments
end

/-- Every source production exports an action at precisely its typed input
context. `exportParserAction` additionally includes source terminal slots. -/
def Templates.exportAction {rules : List CompiledRule}
    {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
    (templates : Templates rules target) (encoding : ConstructorEncoding target)
    (index : Fin rules.length) : Term :=
  (compile encoding (templates.action index)).encode

/-- Derive the full structural-row slot layout from this very production.
Binding a normalized or lexicalized pack requires its further layout law. -/
def Templates.exportParserAction {rules : List CompiledRule}
    {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
    (templates : Templates rules target) (encoding : ConstructorEncoding target)
    (index : Fin rules.length) : Term :=
  (compileWithSlots encoding (parserSlot templates.sortMap rules[index].atoms)
    (templates.action index)).encode

theorem Templates.exported_parser_operation_agrees {rules : List CompiledRule}
    {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
    (templates : Templates rules target) (encoding : ConstructorEncoding target)
    (terminalValue : String → String → Term) (index : Fin rules.length)
    (values : FamilyList templates.interpretation.Carrier
      (childSorts rules[index].atoms)) :
    ((Action.decode (templates.exportParserAction encoding index)).bind
      (fun action => action.execute
        (parserValues templates.sortMap encoding.value terminalValue rules[index].atoms
          (reindexValues templates.sortMap values)))) =
      some (encoding.value _
        (templates.interpretation.operation (.at index) values)) := by
  rw [Templates.exportParserAction, Action.decode_encode]
  exact compile_parserSlots_executes encoding templates.sortMap terminalValue
    rules[index].atoms _ (templates.action index)

theorem Templates.compiled_operation_agrees {rules : List CompiledRule}
    {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
    (templates : Templates rules target) (encoding : ConstructorEncoding target)
    (index : Fin rules.length)
    (values : FamilyList templates.interpretation.Carrier
      (childSorts rules[index].atoms)) :
    (compile encoding (templates.action index)).execute
        (encodeValues encoding.value (reindexValues templates.sortMap values)) =
      some (encoding.value _
        (templates.interpretation.operation (.at index) values)) :=
  compile_executes encoding (templates.action index) _

theorem Templates.exported_operation_agrees {rules : List CompiledRule}
    {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
    (templates : Templates rules target) (encoding : ConstructorEncoding target)
    (index : Fin rules.length)
    (values : FamilyList templates.interpretation.Carrier
      (childSorts rules[index].atoms)) :
    ((Action.decode (templates.exportAction encoding index)).bind
      (fun action => action.execute
        (encodeValues encoding.value (reindexValues templates.sortMap values)))) =
      some (encoding.value _
        (templates.interpretation.operation (.at index) values)) := by
  rw [Templates.exportAction, Action.decode_encode]
  exact templates.compiled_operation_agrees encoding index values

theorem encode_reindexed {Kind : Type} {Value : Kind → Type}
    (sortMap : String → Kind) (encode : ∀ kind, Value kind → Term)
    {sorts : List String}
    (values : FamilyList (fun sort => Value (sortMap sort)) sorts) :
    encodeValues encode (reindexValues sortMap values) =
      encodeValues (fun sort => encode (sortMap sort)) values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp only [reindexValues, encodeValues, ih]

mutual
  /-- Execute prepared actions bottom-up in the grammar's own constructor
  routes. This model uses the partial untyped action evaluator; totality on
  source routes follows from compilation, not an arbitrary error fallback. -/
  def executeCompiled {rules : List CompiledRule}
      {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
      (templates : Templates rules target) (encoding : ConstructorEncoding target)
      {sort : String} : ConstructionTree (syntaxAlgebra rules) sort → Option Term
    | .source impossible => Empty.elim impossible
    | .apply (.at index) arguments => do
        let values ← executeCompiledArguments templates encoding arguments
        (compile encoding (templates.action index)).execute values

  def executeCompiledArguments {rules : List CompiledRule}
      {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
      (templates : Templates rules target) (encoding : ConstructorEncoding target)
      {sorts : List String} :
      ConstructionArguments (syntaxAlgebra rules) sorts → Option (List Term)
    | .nil => some []
    | .cons head tail => do
        let value ← executeCompiled templates encoding head
        let values ← executeCompiledArguments templates encoding tail
        some (value :: values)
end

mutual
  theorem executeCompiled_agrees {rules : List CompiledRule}
      {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
      (templates : Templates rules target) (encoding : ConstructorEncoding target)
      {sort : String} (route : ConstructionTree (syntaxAlgebra rules) sort) :
      executeCompiled templates encoding route =
        some (encoding.value (templates.sortMap sort)
          (interpret templates.interpretation route)) := by
    match route with
    | .source impossible => exact Empty.elim impossible
    | .apply (.at index) arguments =>
        simp only [executeCompiled,
          executeCompiledArguments_agree templates encoding arguments]
        let values : FamilyList (fun sort => target.Object (templates.sortMap sort))
            (childSorts rules[index].atoms) :=
          interpretArguments templates.interpretation arguments
        change (compile encoding (templates.action index)).execute
          (encodeValues (fun sort => encoding.value (templates.sortMap sort)) values) =
            some (encoding.value _
              (templates.interpretation.operation (.at index) values))
        rw [← encode_reindexed]
        exact templates.compiled_operation_agrees encoding index _
    termination_by structural route

  theorem executeCompiledArguments_agree {rules : List CompiledRule}
      {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
      (templates : Templates rules target) (encoding : ConstructorEncoding target)
      {sorts : List String}
      (arguments : ConstructionArguments (syntaxAlgebra rules) sorts) :
      executeCompiledArguments templates encoding arguments =
        some (encodeValues (fun sort => encoding.value (templates.sortMap sort))
          (interpretArguments templates.interpretation arguments)) := by
    match arguments with
    | .nil => rfl
    | .cons head tail =>
        simp only [executeCompiledArguments,
          executeCompiled_agrees templates encoding head,
          executeCompiledArguments_agree templates encoding tail]
        rfl
    termination_by structural arguments
end

/-- The compiled result is exactly the encoding of an operationally admitted
result of the original interpreting GSLT. This is per derivation route and
does not select one parse of an ambiguous source. -/
theorem compiled_result_native_iff {rules : List CompiledRule}
    {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
    (templates : Templates rules target) (encoding : ConstructorEncoding target)
    {sort : String} (route : ConstructionTree (syntaxAlgebra rules) sort)
    (result : Term) :
    executeCompiled templates encoding route = some result ↔
      ∃ value : templates.interpretation.Carrier sort,
        (Mettapedia.OSLF.Framework.PathTypeSynthesis.pathOSLF
          (ManySortedEvaluation.evaluationGSLT templates.interpretation.algebra sort)).satisfies
          (initialState templates.interpretation route)
          (ManySortedEvaluation.resultNativeType templates.interpretation.algebra value).pred ∧
        encoding.value (templates.sortMap sort) value = result := by
  rw [executeCompiled_agrees]
  constructor
  · intro equal
    exact ⟨interpret templates.interpretation route,
      (result_native_iff templates.interpretation route _).mpr rfl, Option.some.inj equal⟩
  · rintro ⟨value, native, encoded⟩
    rw [(result_native_iff templates.interpretation route value).mp native, encoded]

/- Emit postfix code in the same continuation order as the authored
`lower-pack-action-dl` relation. Native admission checks this code against
the exported action; native execution is tested separately. -/
mutual
  def Action.encodeCodeWithTail : Action → Term → Term
    | .slot index, tail => .application "pbc-cons"
        [.application "pbc-push-slot" [encodeIndex index], tail]
    | .constant value, tail => .application "pbc-cons"
        [.application "pbc-push-const" [value], tail]
    | .apply head arguments, tail => encodeArgumentCode arguments
        (.application "pbc-cons"
          [.application "pbc-apply" [.symbol head, encodeIndex arguments.length], tail])
    | .primitive impossible _, _ => nomatch impossible

  def encodeArgumentCode : List Action → Term → Term
    | [], tail => tail
    | head :: rest, tail => head.encodeCodeWithTail (encodeArgumentCode rest tail)
end

def Action.encodeCode (action : Action) : Term :=
  action.encodeCodeWithTail (.symbol "pbc-nil")

theorem out_of_bounds_slot_rejected :
    (Action.slot 1).execute [.symbol "X"] = none := rfl

theorem malformed_action_rejected :
    Action.decode (.application "pa-slot" [.natural 0]) = none := by
  simp [Action.decode, decodeIndex]

#print axioms compile_executes
#print axioms Action.executeWith_legacy
#print axioms compile_parserSlots_executes
#print axioms Templates.compiled_operation_agrees
#print axioms Templates.exported_operation_agrees
#print axioms Templates.exported_parser_operation_agrees
#print axioms executeCompiled_agrees
#print axioms compiled_result_native_iff

end Mettapedia.GSLT.Parsing.GrammarConstructorActions
