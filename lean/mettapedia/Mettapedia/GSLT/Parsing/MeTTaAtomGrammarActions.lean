import Mettapedia.GSLT.Parsing.ClassAwareGrammarActions
import Mettapedia.GSLT.Parsing.MeTTaAtomActionCompiler

/-!
# Grammar-row realization of typed MeTTa atom actions

The complete dependent template family is an explicit input. Physical child
slots are derived from each source row, including its terminal positions;
there is no independently authored child-offset table. The same actions
compile to the existing postfix wire and execute over ordinary host atoms.

Exact lexical routes remain those of `ClassAwareGrammarConstruction`.
This module connects their declared interpretation to the partial action
executor, with result preservation and reflection through the operational
OSLF result type. It neither supplies a whole TPTP interpretation nor proves
that a native parser table implements the supplied source rows.

Applying this model theorem to native execution additionally requires complete
row-context admission, exact slot realization and value-representation
correspondence. Checking only the operands of invoked primitives does not
establish the complete input-context admission used here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.MeTTaAtomGrammarActions

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySortedEvaluation
open Mettapedia.OSLF.Framework.PathTypeSynthesis
open LanguageDefSyntaxCompiler (StructuralAtom CompiledRule)
open LanguageDefGrammarAlgebra (childSorts)
open MeTTaAtomConstruction (Kind Value Action)
open MeTTaAtomActionCompiler (CompiledAction encodeValue decodeValue)
open GrammarConstructorActions (parserSlot)

abbrev Templates (rules : List CompiledRule) :=
  GrammarConstructorActions.Templates rules MeTTaAtomConstruction.algebra

/-! ## Exact row-slot construction and admission -/

/-- Insert terminal payloads while preserving the typed semantic child order.
Literal recognition belongs to the exact source layout, not this value codec. -/
def parserValues (sortMap : String → Kind) (terminalValue : String → String → Atom) :
    (atoms : List StructuralAtom) →
    FamilyList Value ((childSorts atoms).map sortMap) → List Atom
  | [], .nil => []
  | .terminal token reference :: rest, values =>
      terminalValue token reference :: parserValues sortMap terminalValue rest values
  | .nonterminal _ sort _ :: rest, .cons head tail =>
      encodeValue (sortMap sort) head :: parserValues sortMap terminalValue rest tail

theorem parserValues_length (sortMap : String → Kind)
    (terminalValue : String → String → Atom) (atoms : List StructuralAtom)
    (values : FamilyList Value ((childSorts atoms).map sortMap)) :
    (parserValues sortMap terminalValue atoms values).length = atoms.length := by
  induction atoms with
  | nil => cases values; rfl
  | cons atom rest ih =>
      cases atom with
      | terminal token reference => exact congrArg Nat.succ (ih values)
      | nonterminal parameter sort reference =>
          cases values with
          | cons head tail => exact congrArg Nat.succ (ih tail)

theorem parserSlot_lookup (sortMap : String → Kind)
    (terminalValue : String → String → Atom) (atoms : List StructuralAtom)
    (values : FamilyList Value ((childSorts atoms).map sortMap))
    {kind : Kind} (position : ConstructionVariable ((childSorts atoms).map sortMap) kind) :
    (parserValues sortMap terminalValue atoms values)[parserSlot sortMap atoms position]? =
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

/-- Recover exactly the declared typed children from a full parser row.
Extra or missing slots and wrong child sorts fail closed. Terminal payloads
are inert, because this boundary already receives source recognition evidence. -/
def decodeParserValues (sortMap : String → Kind) : (atoms : List StructuralAtom) →
    List Atom → Option (FamilyList Value ((childSorts atoms).map sortMap))
  | [], slots => match slots with
      | [] => some .nil
      | _ :: _ => none
  | .terminal _ _ :: rest, slots => match slots with
      | _ :: slots => decodeParserValues sortMap rest slots
      | [] => none
  | .nonterminal _ sort _ :: rest, slots => match slots with
      | head :: slots => do
          let value ← decodeValue (sortMap sort) head
          let values ← decodeParserValues sortMap rest slots
          some (.cons value values)
      | [] => none

theorem decodeParserValues_parserValues (sortMap : String → Kind)
    (terminalValue : String → String → Atom) (atoms : List StructuralAtom)
    (values : FamilyList Value ((childSorts atoms).map sortMap)) :
    decodeParserValues sortMap atoms (parserValues sortMap terminalValue atoms values) =
      some values := by
  induction atoms with
  | nil => cases values; rfl
  | cons atom rest ih =>
      cases atom with
      | terminal token reference => exact ih values
      | nonterminal parameter sort reference =>
          cases values with
          | cons head tail =>
              simp only [parserValues, decodeParserValues,
                MeTTaAtomActionCompiler.decodeValue_encodeValue, ih]
              rfl

/-- Compile the supplied row action using positions computed from that row. -/
def rowAction {rules : List CompiledRule} (templates : Templates rules)
    (row : Fin rules.length) : CompiledAction :=
  MeTTaAtomActionCompiler.compileWithSlots
    (parserSlot templates.sortMap rules[row].atoms) (templates.action row)

def rowCode {rules : List CompiledRule} (templates : Templates rules)
    (row : Fin rules.length) : Atom :=
  MeTTaAtomActionCompiler.encodeCode (rowAction templates row)

def executeRow {rules : List CompiledRule} (templates : Templates rules)
    (row : Fin rules.length) (slots : List Atom) : Option Atom := do
  let _ ← decodeParserValues templates.sortMap rules[row].atoms slots
  MeTTaAtomActionCompiler.executeCodeResult slots (rowCode templates row)

theorem rowAction_executes {rules : List CompiledRule} (templates : Templates rules)
    (terminalValue : String → String → Atom) (row : Fin rules.length)
    (values : FamilyList Value ((childSorts rules[row].atoms).map templates.sortMap)) :
    MeTTaAtomActionCompiler.execute (parserValues templates.sortMap terminalValue
        rules[row].atoms values) (rowAction templates row) =
      some (encodeValue (templates.sortMap rules[row].source.category)
        (Action.run (templates.action row) values)) :=
  MeTTaAtomActionCompiler.compileWithSlots_executes
    (parserSlot templates.sortMap rules[row].atoms) _ values
    (parserSlot_lookup templates.sortMap terminalValue rules[row].atoms values)
    (templates.action row)

theorem executeRow_parserValues {rules : List CompiledRule} (templates : Templates rules)
    (terminalValue : String → String → Atom) (row : Fin rules.length)
    (values : FamilyList Value ((childSorts rules[row].atoms).map templates.sortMap)) :
    executeRow templates row (parserValues templates.sortMap terminalValue
        rules[row].atoms values) =
      some (encodeValue (templates.sortMap rules[row].source.category)
        (Action.run (templates.action row) values)) := by
  rw [executeRow, decodeParserValues_parserValues templates.sortMap terminalValue
    rules[row].atoms values]
  change MeTTaAtomActionCompiler.executeCodeResult _ (rowCode templates row) = _
  rw [rowCode, MeTTaAtomActionCompiler.encodeCode_executes]
  exact rowAction_executes templates terminalValue row values

/-! ## Source-connected bottom-up execution -/

open ClassAwareGrammarConstruction (Index Layout)

variable {literalScalars? : String → Option (List Nat)}
  {profile : ParserProfileSemantics.ParserProfileLayer}
  {rules : List CompiledRule} {input : List Nat}

def encodeChildren (sortMap : String → Kind) : {indices : List Index} →
    FamilyList (fun index : Index => Value (sortMap index.sort)) indices → List Atom
  | [], .nil => []
  | index :: _, .cons head tail =>
      encodeValue (sortMap index.sort) head :: encodeChildren sortMap tail

/-- Assemble raw parser slots using only the structural row. Child count is
checked in both directions; no failed read supplies a default value. -/
def scatterChildren (terminalValue : String → String → Atom) :
    List StructuralAtom → List Atom → Option (List Atom)
  | [], [] => some []
  | .terminal token reference :: rest, children =>
      (scatterChildren terminalValue rest children).map (terminalValue token reference :: ·)
  | .nonterminal _ _ _ :: rest, child :: children =>
      (scatterChildren terminalValue rest children).map (child :: ·)
  | [], _ :: _ | .nonterminal _ _ _ :: _, [] => none

theorem scatterChildren_layout (sortMap : String → Kind)
    (terminalValue : String → String → Atom)
    {atoms : List StructuralAtom} {start stop : Nat} {indices : List Index}
    (layout : Layout literalScalars? input atoms start stop indices)
    (values : FamilyList (fun index : Index => Value (sortMap index.sort)) indices) :
    scatterChildren terminalValue atoms (encodeChildren sortMap values) =
      some (parserValues sortMap terminalValue atoms
        (ClassAwareGrammarActions.targetChildren
          (target := MeTTaAtomConstruction.algebra) sortMap layout values)) := by
  induction layout with
  | nil => cases values; rfl
  | terminal decoded matched rest ih =>
      simp only [scatterChildren, parserValues]
      rw [ih values]
      rfl
  | nonterminal rest ih =>
      cases values with
      | cons head tail =>
          simp only [encodeChildren, scatterChildren]
          rw [ih tail]
          rfl

mutual
  /-- Independent bottom-up execution uses raw atom results, row assembly,
  input-sort admission and the postfix machine. Lexical decoding is the
  explicitly supplied interpretation boundary, not a hidden name dispatcher. -/
  def executeRoute (templates : Templates rules)
      (lexical : ClassAwareGrammarActions.LexicalInterpretation templates profile input)
      (terminalValue : String → String → Atom) {index : Index} :
      ConstructionTree (ClassAwareGrammarConstruction.algebra
        literalScalars? profile rules input) index → Option Atom
    | .source leaf => some (encodeValue (templates.sortMap index.sort) (lexical leaf))
    | .apply (.at row _layout) arguments => do
        let children ← executeArguments templates lexical terminalValue arguments
        let slots ← scatterChildren terminalValue rules[row].atoms children
        executeRow templates row slots

  def executeArguments (templates : Templates rules)
      (lexical : ClassAwareGrammarActions.LexicalInterpretation templates profile input)
      (terminalValue : String → String → Atom) {indices : List Index} :
      ConstructionArguments (ClassAwareGrammarConstruction.algebra
        literalScalars? profile rules input) indices → Option (List Atom)
    | .nil => some []
    | .cons head tail => do
        let value ← executeRoute templates lexical terminalValue head
        let values ← executeArguments templates lexical terminalValue tail
        some (value :: values)
end

mutual
  /-- Every admitted source route executes to precisely its declared fold.
  This theorem quantifies over a complete supplied template family. -/
  theorem executeRoute_agrees (templates : Templates rules)
      (lexical : ClassAwareGrammarActions.LexicalInterpretation templates profile input)
      (terminalValue : String → String → Atom) {index : Index}
      (route : ConstructionTree (ClassAwareGrammarConstruction.algebra
        literalScalars? profile rules input) index) :
      executeRoute templates lexical terminalValue route =
        some (encodeValue (templates.sortMap index.sort)
          (ClassAwareGrammarActions.fold templates lexical route)) := by
    match route with
    | .source leaf => rfl
    | .apply (.at row layout) arguments =>
        rw [executeRoute, executeArguments_agree templates lexical terminalValue arguments]
        change (scatterChildren terminalValue rules[row].atoms
          (encodeChildren templates.sortMap
            (ClassAwareGrammarActions.foldArguments templates lexical arguments))).bind
              (executeRow templates row) = _
        exact (congrArg (fun slots => slots.bind (executeRow templates row))
          (scatterChildren_layout templates.sortMap terminalValue layout
            (ClassAwareGrammarActions.foldArguments templates lexical arguments))).trans
          (executeRow_parserValues templates terminalValue row _)
    termination_by structural route

  theorem executeArguments_agree (templates : Templates rules)
      (lexical : ClassAwareGrammarActions.LexicalInterpretation templates profile input)
      (terminalValue : String → String → Atom) {indices : List Index}
      (arguments : ConstructionArguments (ClassAwareGrammarConstruction.algebra
        literalScalars? profile rules input) indices) :
      executeArguments templates lexical terminalValue arguments =
        some (encodeChildren templates.sortMap
          (ClassAwareGrammarActions.foldArguments templates lexical arguments)) := by
    match arguments with
    | .nil => rfl
    | .cons head tail =>
        rw [executeArguments, executeRoute_agrees, executeArguments_agree]
        rfl
    termination_by structural arguments
end

/-- Result preservation and reflection through the existing operational OSLF
judgment. No result is licensed merely by passing a sample corpus. -/
theorem executeRoute_result_native_iff (templates : Templates rules)
    (lexical : ClassAwareGrammarActions.LexicalInterpretation templates profile input)
    (terminalValue : String → String → Atom) {index : Index}
    (route : ConstructionTree (ClassAwareGrammarConstruction.algebra
      literalScalars? profile rules input) index) (result : Atom) :
    executeRoute templates lexical terminalValue route = some result ↔
      ∃ value : Value (templates.sortMap index.sort),
        (pathOSLF (evaluationGSLT
          (ClassAwareGrammarActions.interpretationAlgebra templates lexical) index)).satisfies
          (enterState (ClassAwareGrammarActions.interpretationAlgebra templates lexical)
            (ClassAwareGrammarActions.interpretationRoute templates lexical route))
          (resultNativeType (ClassAwareGrammarActions.interpretationAlgebra templates lexical)
            value).pred ∧ encodeValue (templates.sortMap index.sort) value = result := by
  rw [executeRoute_agrees]
  constructor
  · intro equal
    exact ⟨ClassAwareGrammarActions.fold templates lexical route,
      (ClassAwareGrammarActions.result_native_iff templates lexical route _).mpr rfl,
      Option.some.inj equal⟩
  · rintro ⟨value, native, encoded⟩
    rw [(ClassAwareGrammarActions.result_native_iff templates lexical route value).mp native,
      encoded]

/-- A source derivation retains its exact CST witness while its compiled
value is characterized by the interpretation's operational native type. -/
theorem source_derivation_has_compiled_result (templates : Templates rules)
    (lexical : ClassAwareGrammarActions.LexicalInterpretation templates profile input)
    (terminalValue : String → String → Atom)
    {sort : String} {start stop : Nat} {tree : PresentationExprSemantics.CST}
    (derivation : ClassAwareParserPackCorrespondence.SourcePlanDerivesAt
      literalScalars? profile rules input sort start stop tree) :
    ∃ route : ConstructionTree (ClassAwareGrammarConstruction.algebra
        literalScalars? profile rules input) ⟨sort, start, stop⟩,
      (ClassAwareGrammarConstruction.algebra literalScalars? profile rules input).evaluate route = tree ∧
      executeRoute templates lexical terminalValue route =
        some (encodeValue (templates.sortMap sort)
          (ClassAwareGrammarActions.fold templates lexical route)) := by
  let route := ClassAwareGrammarConstruction.sourceRoute derivation
  exact ⟨route.val, route.property, executeRoute_agrees templates lexical terminalValue route.val⟩

/-! ## Independent row controls

These two rows exercise relocation and heterogeneous child sorts. They are
not a replacement TPTP grammar or a whole-language interpretation claim.
-/

namespace Examples

def binaryRow : List StructuralAtom :=
  [.terminal "(" "open", .nonterminal "left" "Formula" "formula",
    .terminal "!=" "unequal", .nonterminal "right" "Formula" "formula",
    .terminal ")" "close"]

def binderRow : List StructuralAtom :=
  [.terminal "!" "forall", .terminal "[" "open",
    .nonterminal "variables" "Binders" "binders", .terminal "]" "close",
    .terminal ":" "colon", .nonterminal "body" "Formula" "formula"]

private def fixtureRule (label : String) (atoms : List StructuralAtom) : CompiledRule :=
  { source := {
      label := label
      category := "Formula"
      params := atoms.filterMap (fun
        | .terminal _ _ => none
        | .nonterminal parameter sort _ => some (.simple parameter (.base sort)))
      syntaxPattern := atoms.map StructuralAtom.sourceSyntax }
    atoms := atoms
    body := .node label (LanguageDefSyntaxCompiler.compileSequence atoms) }

abbrev fixtureRows : List CompiledRule :=
  [fixtureRule "binary" binaryRow, fixtureRule "binder" binderRow]

def sortMap (sort : String) : Kind := if sort = "Binders" then .atoms else .atom

def binaryAction : Action [.atom, .atom] .atom :=
  .apply .application (.cons (.source (.symbol "≉"))
    (.cons (.apply .cons (.cons (.input .here)
      (.cons (.apply .cons (.cons (.input (.there .here))
        (.cons (.apply .empty .nil) .nil))) .nil))) .nil))

def binderAction : Action [.atoms, .atom] .atom :=
  .apply .application (.cons (.source (.symbol "∀"))
    (.cons (.apply .cons (.cons (.apply .expression (.cons (.input .here) .nil))
      (.cons (.apply .cons (.cons (.input (.there .here))
        (.cons (.apply .empty .nil) .nil))) .nil))) .nil))

/-- A complete family for these exact two fixture rows. -/
def templates : Templates fixtureRows where
  sortMap := sortMap
  action := by
    intro row
    refine Fin.cases ?_ ?_ row
    · exact binaryAction
    · intro row
      refine Fin.cases ?_ ?_ row
      · exact binderAction
      · exact fun impossible => Fin.elim0 impossible

def terminalValue (token _reference : String) : Atom := .grounded (.string token)

theorem punctuated_binary (left right : Atom) :
    executeRow templates 0 (parserValues sortMap terminalValue binaryRow
      (.cons left (.cons right .nil))) =
      some (.expression [.symbol "≉", left, right]) :=
  executeRow_parserValues templates terminalValue 0 (.cons left (.cons right .nil))

theorem punctuated_binder (boundVariables : List Atom) (body : Atom) :
    executeRow templates 1 (parserValues sortMap terminalValue binderRow
      (.cons boundVariables (.cons body .nil))) =
      some (.expression [.symbol "∀", .expression boundVariables, body]) :=
  executeRow_parserValues templates terminalValue 1 (.cons boundVariables (.cons body .nil))

/-- Dense semantic indices are not physical parser indices. The first raw
slot here is the opening parenthesis, not the left operand. -/
theorem unrelocated_binary_is_wrong :
    MeTTaAtomActionCompiler.executeCodeResult
      (parserValues sortMap terminalValue binaryRow
        (.cons (.symbol "X") (.cons (.symbol "Y") .nil)))
      (MeTTaAtomActionCompiler.encodeCode (MeTTaAtomActionCompiler.compile binaryAction)) ≠
      some (.expression [.symbol "≉", .symbol "X", .symbol "Y"]) := by
  rw [MeTTaAtomActionCompiler.encodeCode_executes]
  change some (Atom.expression [.symbol "≉", .grounded (.string "("), .symbol "X"]) ≠ _
  intro equal
  cases equal

theorem binder_wrong_child_sort_rejected :
    executeRow templates 1
      [.grounded (.string "!"), .grounded (.string "["), .symbol "X",
        .grounded (.string "]"), .grounded (.string ":"), .symbol "p"] = none := rfl

theorem missing_terminal_slot_rejected :
    executeRow templates 0 [.symbol "X", .symbol "Y"] = none := rfl

theorem extra_child_rejected :
    scatterChildren terminalValue binaryRow [.symbol "X", .symbol "Y", .symbol "Z"] = none := rfl

end Examples

#print axioms parserSlot_lookup
#print axioms executeRow_parserValues
#print axioms executeRoute_agrees
#print axioms executeRoute_result_native_iff
#print axioms source_derivation_has_compiled_result
#print axioms Examples.punctuated_binary
#print axioms Examples.punctuated_binder
#print axioms Examples.unrelocated_binary_is_wrong

end Mettapedia.GSLT.Parsing.MeTTaAtomGrammarActions
