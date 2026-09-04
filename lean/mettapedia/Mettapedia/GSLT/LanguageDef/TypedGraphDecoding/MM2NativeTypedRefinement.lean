import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2NativeActionCodec
import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2TGADCursorWire
import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.TypedFrontier
import Mettapedia.Languages.ProcessCalculi.MORK.MM2ExecutionProfileWire
import Mettapedia.Languages.ProcessCalculi.MORK.MM2RuleScopedExecution
import Mathlib.Tactic

/-!
# Source-derived typed refinement for MM2 native actions

The MM2 reader grammar and the neural action code live at different levels.
The reader grammar recognizes bytes and lowers them to atoms; the neural code
constructs those atoms directly.  This module supplies the missing typed
refinement at the neural level without inventing a second MM2 vocabulary.

Known executable and addressed heads are projected from the maintained MM2
execution and cursor presentations.  A list-opening action first creates a
typed head obligation.  The following head action then determines the exact
argument obligations.  Consequently a known head with the wrong arity is
absent from legal support.  Unknown heads remain open-world in the declared
fragment.  Reflective worker tags use a separate staged rule: their nested
`(step key)` head opens pattern and template obligations without asserting
that a producer must already occur in the source program.

`Classifies` is the declarative judgment.  `compileChildren?` is an
independently defined executable checker, and the adequacy theorem proves the
two equivalent.  The prefix machine then inherits non-stranding for every
trace carrying a derivation of the declarative judgment.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2NativeTypedRefinement

open Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2NativeActionCodec

namespace Execution

abbrev Presentation :=
  Mettapedia.Languages.ProcessCalculi.MORK.MM2ExecutionProfileWire.ExecutionPresentation

def source : Presentation :=
  Mettapedia.Languages.ProcessCalculi.MORK.MM2ExecutionProfileWire.presentation

end Execution

namespace Cursor

abbrev Presentation := MM2TGADCursorWire.CursorPresentation
abbrev AddressedRelation := MM2TGADCursorWire.AddressedRelation

def source : Presentation := MM2TGADCursorWire.presentation

end Cursor

/-- Semantic role of an atom obligation in the admitted MM2/OEIS fragment.
Roles are generated from source positions; they are not language-mode flags. -/
inductive Role where
  | atom
  | key
  | pattern
  | template
  | inputSpec
  | inputFactor
  | outputSpec
  | outputSink
  deriving Repr, DecidableEq

/-- Typed obligations encountered by the native preorder action code. -/
inductive Expected where
  | program
  | atom (role : Role)
  | listHead (role : Role) (totalArity : Nat)
  | literal (name : String)
  deriving Repr, DecidableEq

/-- One known expression head and the roles of its arguments after the head.
`totalArity` counts the head, matching the native list action. -/
structure FormSchema where
  head : String
  totalArity : Nat
  argumentRoles : List Role
  arityExact : argumentRoles.length + 1 = totalArity
  deriving Repr

private def roleAtWorkPosition
    (work : Mettapedia.Languages.ProcessCalculi.MORK.MM2ExecutionProfileWire.WorkShell)
    (position : Nat) : Role :=
  if position = work.locationPosition then .key
  else if position = work.inputPosition then .inputSpec
  else if position = work.outputPosition then .outputSpec
  else .atom

/-- The executable work schema is a projection of the maintained execution
presentation. -/
def workSchemaFrom (source : Execution.Presentation) : FormSchema where
  head := source.workShell.head
  totalArity := source.workShell.arity + 1
  argumentRoles :=
    (List.range source.workShell.arity).map
      (roleAtWorkPosition source.workShell)
  arityExact := by simp

def workSchema : FormSchema := workSchemaFrom Execution.source

private def addressedRole
    (relation : Cursor.AddressedRelation) (childPosition : Nat) : Role :=
  if childPosition = relation.addressPosition then .key else .atom

/-- Addressed cursor relations count their head in `arity`; child positions
therefore begin at one. -/
def addressedSchema (relation : Cursor.AddressedRelation)
    (positive : 0 < relation.arity) : FormSchema where
  head := relation.head
  totalArity := relation.arity
  argumentRoles :=
    (List.range (relation.arity - 1)).map fun position =>
      addressedRole relation (position + 1)
  arityExact := by simp [Nat.sub_add_cancel positive]

/-- The reflective tag is source-derived independently of the enclosing
quoted-worker arity. -/
def quotedTagSchemaFrom (source : Cursor.Presentation)
    (binaryTag : source.quotedTagArity = 2) : FormSchema where
  head := source.quotedRuleHead
  totalArity := source.quotedTagArity
  argumentRoles := [.key]
  arityExact := by simp [binaryTag]

def quotedTagSchema : FormSchema :=
  quotedTagSchemaFrom Cursor.source (by decide)

abbrev OperatorDecl :=
  Mettapedia.Languages.ProcessCalculi.MORK.MM2ExecutionProfileWire.OperatorDecl

/-- Exact-arity provider form projected from one execution-profile
declaration.  The role records whether its operands are source patterns or
output templates. -/
def providerSchema (argumentRole : Role)
    (declaration : OperatorDecl) : FormSchema where
  head := declaration.interface
  totalArity := declaration.arity + 1
  argumentRoles := List.replicate declaration.arity argumentRole
  arityExact := by simp

def inputProviderSchemasFrom (source : Execution.Presentation) :
    List FormSchema :=
  source.input.explicitSources.map (providerSchema .pattern)

def outputProviderSchemasFrom (source : Execution.Presentation) :
    List FormSchema :=
  (source.output.coreSinks ++ source.output.extensionSinks).map
    (providerSchema .template)

def inputProviderSchemas : List FormSchema :=
  inputProviderSchemasFrom Execution.source

def outputProviderSchemas : List FormSchema :=
  outputProviderSchemasFrom Execution.source

/-- Finite heads whose arities are hard constraints in the declared
fragment.  Provider existence and eventual saturation success are not in this
inventory. -/
def schemasFrom (execution : Execution.Presentation)
    (cursor : Cursor.Presentation)
    (demandPositive : 0 < cursor.demand.arity)
    (producerPositive : 0 < cursor.producer.arity)
    (queryPositive : 0 < cursor.query.arity)
    (resultPositive : 0 < cursor.result.arity)
    (binaryTag : cursor.quotedTagArity = 2) : List FormSchema :=
  [ workSchemaFrom execution
  , addressedSchema cursor.demand demandPositive
  , addressedSchema cursor.producer producerPositive
  , addressedSchema cursor.query queryPositive
  , addressedSchema cursor.result resultPositive
  , quotedTagSchemaFrom cursor binaryTag ]

def schemas : List FormSchema :=
  schemasFrom Execution.source Cursor.source
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem schemas_are_compiled_from_maintained_sources :
    schemas =
      [ workSchema
  , addressedSchema Cursor.source.demand (by decide)
  , addressedSchema Cursor.source.producer (by decide)
  , addressedSchema Cursor.source.query (by decide)
  , addressedSchema Cursor.source.result (by decide)
  , quotedTagSchema ] := by
  rfl

def schemaFor? (name : String) : Option FormSchema :=
  schemas.find? fun schema => schema.head = name

def inputProviderSchemaFor? (name : String) : Option FormSchema :=
  inputProviderSchemas.find? fun schema => schema.head = name

def outputProviderSchemaFor? (name : String) : Option FormSchema :=
  outputProviderSchemas.find? fun schema => schema.head = name

/-- The maintained schema inventory has no ambiguous head spelling. -/
theorem schema_heads_pairwise_distinct :
    (schemas.map FormSchema.head).Pairwise (fun first second => first ≠ second) := by
  decide +kernel

/-- Every executable schema lookup returns an item from the source-derived
inventory with exactly the requested head. -/
theorem schemaFor?_some_exact (name : String) (schema : FormSchema)
    (found : schemaFor? name = some schema) :
    schema ∈ schemas ∧ schema.head = name := by
  unfold schemaFor? at found
  exact ⟨List.mem_of_find?_eq_some found,
    by simpa using List.find?_some found⟩

private def roleExpected (role : Role) : Expected := .atom role
private def genericArguments (role : Role) (totalArity : Nat) : List Expected :=
  List.replicate (totalArity - 1) (.atom role)
private def schemaArguments (schema : FormSchema) : List Expected :=
  schema.argumentRoles.map roleExpected

/-! ## Declarative source classification -/

/-- Roles whose nested expressions are ordinary MM2 data.  In these roles a
word such as `exec` is data rather than an executable shell, so no global
head table may reinterpret it. -/
inductive DataRole : Role → Prop where
  | key : DataRole .key
  | pattern : DataRole .pattern
  | template : DataRole .template

/-- Roles that permit atomic leaves.  Structured execution positions require
an expression and therefore are deliberately absent. -/
inductive LeafRole : Role → Prop where
  | atom : LeafRole .atom
  | key : LeafRole .key
  | pattern : LeafRole .pattern
  | template : LeafRole .template

/-- Declarative action classification.  Its constructors expose every
accepted case and keep source lookup evidence in the proposition. -/
inductive Classifies (symbols : List String) :
    Action → Expected → List Expected → Prop where
  | program {formCount : Nat} (nonempty : 0 < formCount) :
      Classifies symbols (.program formCount) .program
        (List.replicate formCount (.atom .atom))
  | emptyExpression {role : Role} (leaf : LeafRole role) :
      Classifies symbols (.list 0) (.atom role) []
  | openExpression (role : Role) (arity : Nat) :
      Classifies symbols (.list (arity + 1)) (.atom role)
        [.listHead role (arity + 1)]
  | atomicReference {role : Role} (leaf : LeafRole role)
      {index : Nat} {name : String}
      (present : symbols[index]? = some name) :
      Classifies symbols (.reference index) (.atom role) []
  | atomicVariable {role : Role} (leaf : LeafRole role) (index : Nat) :
      Classifies symbols (.var index) (.atom role) []
  | knownHead {totalArity index : Nat}
      {name : String} {schema : FormSchema}
      (present : symbols[index]? = some name)
      (known : schemaFor? name = some schema)
      (arity : schema.totalArity = totalArity) :
      Classifies symbols (.reference index) (.listHead .atom totalArity)
        (schemaArguments schema)
  | unknownHead {totalArity index : Nat} {name : String}
      (present : symbols[index]? = some name)
      (unknown : schemaFor? name = none) :
      Classifies symbols (.reference index) (.listHead .atom totalArity)
        (genericArguments .atom totalArity)
  | dataReferenceHead {role : Role} (data : DataRole role)
      {totalArity index : Nat} {name : String}
      (present : symbols[index]? = some name) :
      Classifies symbols (.reference index) (.listHead role totalArity)
        (genericArguments role totalArity)
  | variableAtomHead (totalArity index : Nat) :
      Classifies symbols (.var index) (.listHead .atom totalArity)
        (genericArguments .atom totalArity)
  | variableDataHead {role : Role} (data : DataRole role)
      (totalArity index : Nat) :
      Classifies symbols (.var index) (.listHead role totalArity)
        (genericArguments role totalArity)
  | inputCompatibilityHead {totalArity index : Nat}
      (present : symbols[index]? =
        some Execution.source.input.compatibility.interface) :
      Classifies symbols (.reference index) (.listHead .inputSpec totalArity)
        (genericArguments .pattern totalArity)
  | explicitInputHead {totalArity index : Nat}
      (present : symbols[index]? = some Execution.source.input.explicitHead) :
      Classifies symbols (.reference index) (.listHead .inputSpec totalArity)
        (genericArguments .inputFactor totalArity)
  | inputProviderHead {totalArity index : Nat}
      {name : String} {schema : FormSchema}
      (present : symbols[index]? = some name)
      (known : inputProviderSchemaFor? name = some schema)
      (arity : schema.totalArity = totalArity) :
      Classifies symbols (.reference index) (.listHead .inputFactor totalArity)
        (schemaArguments schema)
  | outputCompatibilityHead {totalArity index : Nat}
      (present : symbols[index]? =
        some Execution.source.output.compatibility.interface) :
      Classifies symbols (.reference index) (.listHead .outputSpec totalArity)
        (genericArguments .template totalArity)
  | explicitOutputHead {totalArity index : Nat}
      (present : symbols[index]? = some Execution.source.output.explicitHead) :
      Classifies symbols (.reference index) (.listHead .outputSpec totalArity)
        (genericArguments .outputSink totalArity)
  | outputProviderHead {totalArity index : Nat}
      {name : String} {schema : FormSchema}
      (present : symbols[index]? = some name)
      (known : outputProviderSchemaFor? name = some schema)
      (arity : schema.totalArity = totalArity) :
      Classifies symbols (.reference index) (.listHead .outputSink totalArity)
        (schemaArguments schema)
  | dataEmptyHead {role : Role} (data : DataRole role)
      (outerTotal : Nat) :
      Classifies symbols (.list 0) (.listHead role outerTotal)
        (genericArguments role outerTotal)
  | dataNestedHead {role : Role} (data : DataRole role)
      (outerTotal nestedArity : Nat) :
      Classifies symbols (.list (nestedArity + 1)) (.listHead role outerTotal)
        (.listHead role (nestedArity + 1) :: genericArguments role outerTotal)
  | atomEmptyHead (outerTotal : Nat) :
      Classifies symbols (.list 0) (.listHead .atom outerTotal)
        (genericArguments .atom outerTotal)
  | atomNestedHead (outerTotal nestedArity : Nat)
      (notQuoted : ¬ (Cursor.source.quotedRuleArity = outerTotal ∧
        Cursor.source.quotedTagArity = nestedArity + 1)) :
      Classifies symbols (.list (nestedArity + 1))
        (.listHead .atom outerTotal)
        (.listHead .atom (nestedArity + 1) ::
          genericArguments .atom outerTotal)
  | quotedWorkerHead {outerTotal nestedArity : Nat}
      (outerMatches : Cursor.source.quotedRuleArity = outerTotal)
      (tagArity : Cursor.source.quotedTagArity = nestedArity) :
      Classifies symbols (.list nestedArity) (.listHead .atom outerTotal)
        ([.literal Cursor.source.quotedRuleHead, .atom .key,
          .atom .pattern, .atom .template])
  | literalReference {expected : String} {index : Nat}
      (present : symbols[index]? = some expected) :
      Classifies symbols (.reference index) (.literal expected) []

/-! ## Executable compiler and adequacy -/

/-- Compile one raw action against the current typed obligation. -/
def compileChildren? (symbols : List String) (expected : Expected)
    (action : Action) : Option (List Expected) :=
  match expected, action with
  | .program, .program formCount =>
      if 0 < formCount then
        some (List.replicate formCount (.atom .atom))
      else none
  | .atom .atom, .list 0 => some []
  | .atom .key, .list 0 => some []
  | .atom .pattern, .list 0 => some []
  | .atom .template, .list 0 => some []
  | .atom role, .list (arity + 1) =>
      some [.listHead role (arity + 1)]
  | .atom .atom, .reference index =>
      if (symbols[index]?).isSome then some [] else none
  | .atom .key, .reference index =>
      if (symbols[index]?).isSome then some [] else none
  | .atom .pattern, .reference index =>
      if (symbols[index]?).isSome then some [] else none
  | .atom .template, .reference index =>
      if (symbols[index]?).isSome then some [] else none
  | .atom .atom, .var _ => some []
  | .atom .key, .var _ => some []
  | .atom .pattern, .var _ => some []
  | .atom .template, .var _ => some []
  | .listHead .atom totalArity, .reference index => do
      let name ← symbols[index]?
      match schemaFor? name with
      | some schema =>
          if schema.totalArity = totalArity then
            some (schemaArguments schema)
          else none
      | none => some (genericArguments .atom totalArity)
  | .listHead .key totalArity, .reference index => do
      let _name ← symbols[index]?
      some (genericArguments .key totalArity)
  | .listHead .pattern totalArity, .reference index => do
      let _name ← symbols[index]?
      some (genericArguments .pattern totalArity)
  | .listHead .template totalArity, .reference index => do
      let _name ← symbols[index]?
      some (genericArguments .template totalArity)
  | .listHead .inputSpec totalArity, .reference index => do
      let name ← symbols[index]?
      if name = Execution.source.input.compatibility.interface then
        some (genericArguments .pattern totalArity)
      else if name = Execution.source.input.explicitHead then
        some (genericArguments .inputFactor totalArity)
      else none
  | .listHead .inputFactor totalArity, .reference index => do
      let name ← symbols[index]?
      let schema ← inputProviderSchemaFor? name
      if schema.totalArity = totalArity then
        some (schemaArguments schema)
      else none
  | .listHead .outputSpec totalArity, .reference index => do
      let name ← symbols[index]?
      if name = Execution.source.output.compatibility.interface then
        some (genericArguments .template totalArity)
      else if name = Execution.source.output.explicitHead then
        some (genericArguments .outputSink totalArity)
      else none
  | .listHead .outputSink totalArity, .reference index => do
      let name ← symbols[index]?
      let schema ← outputProviderSchemaFor? name
      if schema.totalArity = totalArity then
        some (schemaArguments schema)
      else none
  | .listHead .atom totalArity, .var _ =>
      some (genericArguments .atom totalArity)
  | .listHead .key totalArity, .var _ =>
      some (genericArguments .key totalArity)
  | .listHead .pattern totalArity, .var _ =>
      some (genericArguments .pattern totalArity)
  | .listHead .template totalArity, .var _ =>
      some (genericArguments .template totalArity)
  | .listHead .key totalArity, .list 0 =>
      some (genericArguments .key totalArity)
  | .listHead .key totalArity, .list (nestedArity + 1) =>
      some (.listHead .key (nestedArity + 1) ::
        genericArguments .key totalArity)
  | .listHead .pattern totalArity, .list 0 =>
      some (genericArguments .pattern totalArity)
  | .listHead .pattern totalArity, .list (nestedArity + 1) =>
      some (.listHead .pattern (nestedArity + 1) ::
        genericArguments .pattern totalArity)
  | .listHead .template totalArity, .list 0 =>
      some (genericArguments .template totalArity)
  | .listHead .template totalArity, .list (nestedArity + 1) =>
      some (.listHead .template (nestedArity + 1) ::
        genericArguments .template totalArity)
  | .listHead .atom totalArity, .list nestedArity =>
      if Cursor.source.quotedRuleArity = totalArity ∧
          Cursor.source.quotedTagArity = nestedArity then
        some [.literal Cursor.source.quotedRuleHead, .atom .key,
          .atom .pattern, .atom .template]
      else match nestedArity with
        | 0 => some (genericArguments .atom totalArity)
        | arity + 1 => some (.listHead .atom (arity + 1) ::
            genericArguments .atom totalArity)
  | .literal expected, .reference index =>
      if symbols[index]? = some expected then some [] else none
  | _, _ => none

/-- Executable classification is sound for the independent declarative
judgment. -/
theorem compileChildren?_sound (symbols : List String) (expected : Expected)
    (action : Action) (children : List Expected)
    (compiled : compileChildren? symbols expected action = some children) :
    Classifies symbols action expected children := by
  cases expected with
  | program =>
      cases action with
      | program formCount =>
          simp only [compileChildren?] at compiled
          split at compiled
          next positive =>
            cases Option.some.inj compiled
            exact .program positive
          next _ => simp at compiled
      | list _ | reference _ | var _ => simp [compileChildren?] at compiled
  | atom role =>
      cases role with
      | atom =>
          cases action with
          | program _ => simp [compileChildren?] at compiled
          | list arity =>
              cases arity with
              | zero => cases Option.some.inj compiled; exact .emptyExpression .atom
              | succ arity => cases Option.some.inj compiled; exact .openExpression .atom arity
          | reference index =>
              cases lookup : symbols[index]? with
              | none => simp [compileChildren?, lookup] at compiled
              | some name =>
                  cases Option.some.inj (by simpa [compileChildren?, lookup] using compiled)
                  exact .atomicReference .atom lookup
          | var index => cases Option.some.inj compiled; exact .atomicVariable .atom index
      | key =>
          cases action with
          | program _ => simp [compileChildren?] at compiled
          | list arity =>
              cases arity with
              | zero => cases Option.some.inj compiled; exact .emptyExpression .key
              | succ arity => cases Option.some.inj compiled; exact .openExpression .key arity
          | reference index =>
              cases lookup : symbols[index]? with
              | none => simp [compileChildren?, lookup] at compiled
              | some name =>
                  cases Option.some.inj (by simpa [compileChildren?, lookup] using compiled)
                  exact .atomicReference .key lookup
          | var index => cases Option.some.inj compiled; exact .atomicVariable .key index
      | pattern =>
          cases action with
          | program _ => simp [compileChildren?] at compiled
          | list arity =>
              cases arity with
              | zero => cases Option.some.inj compiled; exact .emptyExpression .pattern
              | succ arity => cases Option.some.inj compiled; exact .openExpression .pattern arity
          | reference index =>
              cases lookup : symbols[index]? with
              | none => simp [compileChildren?, lookup] at compiled
              | some name =>
                  cases Option.some.inj (by simpa [compileChildren?, lookup] using compiled)
                  exact .atomicReference .pattern lookup
          | var index => cases Option.some.inj compiled; exact .atomicVariable .pattern index
      | template =>
          cases action with
          | program _ => simp [compileChildren?] at compiled
          | list arity =>
              cases arity with
              | zero => cases Option.some.inj compiled; exact .emptyExpression .template
              | succ arity => cases Option.some.inj compiled; exact .openExpression .template arity
          | reference index =>
              cases lookup : symbols[index]? with
              | none => simp [compileChildren?, lookup] at compiled
              | some name =>
                  cases Option.some.inj (by simpa [compileChildren?, lookup] using compiled)
                  exact .atomicReference .template lookup
          | var index => cases Option.some.inj compiled; exact .atomicVariable .template index
      | inputSpec =>
          cases action with
          | list arity =>
              cases arity with
              | zero => simp [compileChildren?] at compiled
              | succ arity =>
                  cases Option.some.inj compiled
                  exact .openExpression .inputSpec arity
          | program _ | reference _ | var _ => simp [compileChildren?] at compiled
      | inputFactor =>
          cases action with
          | list arity =>
              cases arity with
              | zero => simp [compileChildren?] at compiled
              | succ arity =>
                  cases Option.some.inj compiled
                  exact .openExpression .inputFactor arity
          | program _ | reference _ | var _ => simp [compileChildren?] at compiled
      | outputSpec =>
          cases action with
          | list arity =>
              cases arity with
              | zero => simp [compileChildren?] at compiled
              | succ arity =>
                  cases Option.some.inj compiled
                  exact .openExpression .outputSpec arity
          | program _ | reference _ | var _ => simp [compileChildren?] at compiled
      | outputSink =>
          cases action with
          | list arity =>
              cases arity with
              | zero => simp [compileChildren?] at compiled
              | succ arity =>
                  cases Option.some.inj compiled
                  exact .openExpression .outputSink arity
          | program _ | reference _ | var _ => simp [compileChildren?] at compiled
  | listHead role totalArity =>
      cases role with
      | atom =>
          cases action with
          | program _ => simp [compileChildren?] at compiled
          | list nestedArity =>
              simp only [compileChildren?] at compiled
              split at compiled
              next matchProof =>
                cases Option.some.inj compiled
                exact .quotedWorkerHead matchProof.1 matchProof.2
              next notQuoted =>
                cases nestedArity with
                | zero =>
                    cases Option.some.inj compiled
                    exact .atomEmptyHead totalArity
                | succ nestedArity =>
                    cases Option.some.inj compiled
                    exact .atomNestedHead totalArity nestedArity notQuoted
          | reference index =>
              cases lookup : symbols[index]? with
              | none => simp [compileChildren?, lookup] at compiled
              | some name =>
                  cases known : schemaFor? name with
                  | none =>
                      have reduced :
                          some (genericArguments .atom totalArity) =
                            some children := by
                        simpa [compileChildren?, lookup, known] using compiled
                      cases Option.some.inj reduced
                      exact .unknownHead lookup known
                  | some schema =>
                      by_cases arity : schema.totalArity = totalArity
                      · have reduced :
                            some (schemaArguments schema) = some children := by
                          simpa [compileChildren?, lookup, known, arity] using compiled
                        cases Option.some.inj reduced
                        exact .knownHead lookup known arity
                      · simp [compileChildren?, lookup, known, arity] at compiled
          | var index =>
              cases Option.some.inj compiled
              exact .variableAtomHead totalArity index
      | key =>
          cases action with
          | program _ => simp [compileChildren?] at compiled
          | list nestedArity =>
              cases nestedArity with
              | zero =>
                  cases Option.some.inj compiled
                  exact .dataEmptyHead .key totalArity
              | succ nestedArity =>
                  cases Option.some.inj compiled
                  exact .dataNestedHead .key totalArity nestedArity
          | reference index =>
              cases lookup : symbols[index]? with
              | none => simp [compileChildren?, lookup] at compiled
              | some name =>
                  cases Option.some.inj
                    (by simpa [compileChildren?, lookup] using compiled)
                  exact .dataReferenceHead .key lookup
          | var index =>
              cases Option.some.inj compiled
              exact .variableDataHead .key totalArity index
      | pattern =>
          cases action with
          | program _ => simp [compileChildren?] at compiled
          | list nestedArity =>
              cases nestedArity with
              | zero =>
                  cases Option.some.inj compiled
                  exact .dataEmptyHead .pattern totalArity
              | succ nestedArity =>
                  cases Option.some.inj compiled
                  exact .dataNestedHead .pattern totalArity nestedArity
          | reference index =>
              cases lookup : symbols[index]? with
              | none => simp [compileChildren?, lookup] at compiled
              | some name =>
                  cases Option.some.inj
                    (by simpa [compileChildren?, lookup] using compiled)
                  exact .dataReferenceHead .pattern lookup
          | var index =>
              cases Option.some.inj compiled
              exact .variableDataHead .pattern totalArity index
      | template =>
          cases action with
          | program _ => simp [compileChildren?] at compiled
          | list nestedArity =>
              cases nestedArity with
              | zero =>
                  cases Option.some.inj compiled
                  exact .dataEmptyHead .template totalArity
              | succ nestedArity =>
                  cases Option.some.inj compiled
                  exact .dataNestedHead .template totalArity nestedArity
          | reference index =>
              cases lookup : symbols[index]? with
              | none => simp [compileChildren?, lookup] at compiled
              | some name =>
                  cases Option.some.inj
                    (by simpa [compileChildren?, lookup] using compiled)
                  exact .dataReferenceHead .template lookup
          | var index =>
              cases Option.some.inj compiled
              exact .variableDataHead .template totalArity index
      | inputSpec =>
          cases action with
          | reference index =>
              cases lookup : symbols[index]? with
              | none => simp [compileChildren?, lookup] at compiled
              | some name =>
                  by_cases compatibility :
                      name = Execution.source.input.compatibility.interface
                  · cases Option.some.inj
                      (by simpa [compileChildren?, lookup, compatibility] using compiled)
                    exact .inputCompatibilityHead (by simpa [compatibility] using lookup)
                  · by_cases explicit :
                        name = Execution.source.input.explicitHead
                    · cases Option.some.inj
                        (by simpa [compileChildren?, lookup, compatibility, explicit]
                          using compiled)
                      exact .explicitInputHead (by simpa [explicit] using lookup)
                    · simp [compileChildren?, lookup, compatibility, explicit] at compiled
          | program _ | list _ | var _ => simp [compileChildren?] at compiled
      | inputFactor =>
          cases action with
          | reference index =>
              cases lookup : symbols[index]? with
              | none => simp [compileChildren?, lookup] at compiled
              | some name =>
                  cases known : inputProviderSchemaFor? name with
                  | none => simp [compileChildren?, lookup, known] at compiled
                  | some schema =>
                      by_cases arity : schema.totalArity = totalArity
                      · cases Option.some.inj
                          (by simpa [compileChildren?, lookup, known, arity]
                            using compiled)
                        exact .inputProviderHead lookup known arity
                      · simp [compileChildren?, lookup, known, arity] at compiled
          | program _ | list _ | var _ => simp [compileChildren?] at compiled
      | outputSpec =>
          cases action with
          | reference index =>
              cases lookup : symbols[index]? with
              | none => simp [compileChildren?, lookup] at compiled
              | some name =>
                  by_cases compatibility :
                      name = Execution.source.output.compatibility.interface
                  · cases Option.some.inj
                      (by simpa [compileChildren?, lookup, compatibility] using compiled)
                    exact .outputCompatibilityHead (by simpa [compatibility] using lookup)
                  · by_cases explicit :
                        name = Execution.source.output.explicitHead
                    · cases Option.some.inj
                        (by simpa [compileChildren?, lookup, compatibility, explicit]
                          using compiled)
                      exact .explicitOutputHead (by simpa [explicit] using lookup)
                    · simp [compileChildren?, lookup, compatibility, explicit] at compiled
          | program _ | list _ | var _ => simp [compileChildren?] at compiled
      | outputSink =>
          cases action with
          | reference index =>
              cases lookup : symbols[index]? with
              | none => simp [compileChildren?, lookup] at compiled
              | some name =>
                  cases known : outputProviderSchemaFor? name with
                  | none => simp [compileChildren?, lookup, known] at compiled
                  | some schema =>
                      by_cases arity : schema.totalArity = totalArity
                      · cases Option.some.inj
                          (by simpa [compileChildren?, lookup, known, arity]
                            using compiled)
                        exact .outputProviderHead lookup known arity
                      · simp [compileChildren?, lookup, known, arity] at compiled
          | program _ | list _ | var _ => simp [compileChildren?] at compiled
  | literal expected =>
      cases action with
      | reference index =>
          by_cases present : symbols[index]? = some expected
          · cases Option.some.inj
              (by simpa [compileChildren?, present] using compiled)
            exact .literalReference present
          · simp [compileChildren?, present] at compiled
      | program _ | list _ | var _ => simp [compileChildren?] at compiled

/-- Every declaratively classified action is accepted by the executable
compiler with exactly the declared child obligations. -/
theorem compileChildren?_complete (symbols : List String) (expected : Expected)
    (action : Action) (children : List Expected)
    (classified : Classifies symbols action expected children) :
    compileChildren? symbols expected action = some children := by
  cases classified with
  | program positive => simp [compileChildren?, positive]
  | emptyExpression leaf => cases leaf <;> rfl
  | openExpression role arity => cases role <;> rfl
  | atomicReference leaf present => cases leaf <;> simp [compileChildren?, present]
  | atomicVariable leaf index => cases leaf <;> rfl
  | knownHead present known arity =>
      simp [compileChildren?, present, known, arity]
  | unknownHead present unknown =>
      simp [compileChildren?, present, unknown]
  | dataReferenceHead data present =>
      cases data <;> simp [compileChildren?, present]
  | variableAtomHead totalArity index => rfl
  | variableDataHead data totalArity index => cases data <;> rfl
  | inputCompatibilityHead present =>
      simp [compileChildren?, present]
  | explicitInputHead present =>
      simp [compileChildren?, present,
        show Execution.source.input.explicitHead ≠
          Execution.source.input.compatibility.interface by decide]
  | inputProviderHead present known arity =>
      simp [compileChildren?, present, known, arity]
  | outputCompatibilityHead present =>
      simp [compileChildren?, present]
  | explicitOutputHead present =>
      simp [compileChildren?, present,
        show Execution.source.output.explicitHead ≠
          Execution.source.output.compatibility.interface by decide]
  | outputProviderHead present known arity =>
      simp [compileChildren?, present, known, arity]
  | dataEmptyHead data outerTotal => cases data <;> rfl
  | dataNestedHead data outerTotal nestedArity => cases data <;> rfl
  | atomEmptyHead outerTotal =>
      simp [compileChildren?,
        show Cursor.source.quotedTagArity ≠ 0 by decide]
  | atomNestedHead outerTotal nestedArity notQuoted =>
      simp [compileChildren?, notQuoted]
  | quotedWorkerHead outerArity tagArity =>
      simp [compileChildren?, outerArity, tagArity]
  | literalReference present => simp [compileChildren?, present]

/-- The runtime checker and declarative source judgment agree exactly. -/
theorem compileChildren?_eq_some_iff (symbols : List String)
    (expected : Expected) (action : Action) (children : List Expected) :
    compileChildren? symbols expected action = some children ↔
      Classifies symbols action expected children := by
  exact ⟨compileChildren?_sound symbols expected action children,
    compileChildren?_complete symbols expected action children⟩

/-! ## Source-certified typed-frontier instance -/

/-- A typed head contains a raw native action and its source-classification
certificate. -/
structure Head (symbols : List String) where
  raw : Action
  result : Expected
  children : List Expected
  classified : Classifies symbols raw result children

def signature (symbols : List String) : TypedFrontier.Signature where
  SortType := Expected
  Head := Head symbols
  resultSort := Head.result
  childSorts := Head.children

instance signatureSortDecidableEq (symbols : List String) :
    DecidableEq (signature symbols).SortType :=
  inferInstanceAs (DecidableEq Expected)

def expectedHoles (symbols : List String)
    (state : TypedFrontier.State (signature symbols)) : List Expected :=
  state.holes

def firstExpected? (symbols : List String)
    (state : TypedFrontier.State (signature symbols)) : Option Expected :=
  match expectedHoles symbols state with
  | [] => none
  | expected :: _ => some expected

def compileHead? (symbols : List String) (expected : Expected)
    (action : Action) : Option (Head symbols) :=
  match childrenExact : compileChildren? symbols expected action with
  | none => none
  | some children =>
      some ⟨action, expected, children,
        compileChildren?_sound symbols expected action children childrenExact⟩

/-- Every compiled head is definitionally tied to the raw action, expected
sort, and source classification used to construct it. -/
theorem compileHead?_some_exact (symbols : List String) (expected : Expected)
    (action : Action) (head : Head symbols)
    (compiled : compileHead? symbols expected action = some head) :
    head.raw = action ∧ head.result = expected ∧
      Classifies symbols action expected head.children := by
  unfold compileHead? at compiled
  split at compiled
  next noChildren => simp at compiled
  next children childrenExact =>
    cases Option.some.inj compiled
    exact ⟨rfl, rfl,
      compileChildren?_sound symbols expected action children childrenExact⟩

/-- Unit lower bound used by the semantic layer.  The ordinary structural
cursor retains the stronger exact open-hole budget; this layer only charges
that every typed obligation needs at least one action. -/
def unitCost : Expected → Nat := fun _ => 1

/-- Source-compiled native refinement expressed through the generic checked
typed-frontier transition. -/
def refine? (symbols : List String)
    (state : TypedFrontier.State (signature symbols)) (action : Action) :
    Option (TypedFrontier.State (signature symbols)) :=
  match firstExpected? symbols state with
  | none => none
  | some expected => do
      let head ← compileHead? symbols expected action
      (signature symbols).refine? unitCost state
        { holeIndex := 0, head := head }

/-- A successful native refinement carries a source-classification witness
and is exactly a successful generic typed-frontier transition. -/
theorem refine?_some_source_typed (symbols : List String)
    (state next : TypedFrontier.State (signature symbols))
    (action : Action) (refined : refine? symbols state action = some next) :
    ∃ expected head,
      firstExpected? symbols state = some expected ∧
        compileHead? symbols expected action = some head ∧
        Classifies symbols action expected head.children ∧
        (signature symbols).refine? unitCost state
          { holeIndex := 0, head := head } = some next := by
  unfold refine? at refined
  cases lookup : firstExpected? symbols state with
  | none => simp [lookup] at refined
  | some expected =>
      simp only [lookup] at refined
      cases compiled : compileHead? symbols expected action with
      | none => simp [compiled] at refined
      | some head =>
          simp only [compiled, Option.bind_eq_bind, Option.bind_some] at refined
          have exactHead :=
            compileHead?_some_exact symbols expected action head compiled
          exact ⟨expected, head, rfl, compiled, exactHead.2.2, refined⟩

/-- The generic typed-frontier theorem therefore supplies sort and budget
safety for the actual source-compiled native transition. -/
theorem refine?_some_preserves_typed_budget (symbols : List String)
    (state next : TypedFrontier.State (signature symbols))
    (action : Action) (refined : refine? symbols state action = some next) :
    ∃ expected head,
      Classifies symbols action expected head.children ∧
        next.holes =
          (signature symbols).nextHoles state
            ({ holeIndex := 0, head := head } :
              TypedFrontier.Action (signature symbols)) ∧
        (signature symbols).required unitCost next.holes ≤ next.remaining := by
  rcases refine?_some_source_typed symbols state next action refined with
    ⟨expected, head, _lookup, _compiled, classified, typed⟩
  rcases (signature symbols).refine?_some_typed_and_budget_safe
      unitCost state next
      ({ holeIndex := 0, head := head } :
        TypedFrontier.Action (signature symbols)) typed with
    ⟨_typedExpected, _typedLookup, _result, holes, _remaining, budget⟩
  exact ⟨expected, head, classified, holes, budget⟩

/-- The semantic prefix state is the exact ordered typed frontier. -/
abbrev PrefixState := List Expected

def initial : PrefixState := [.program]

/-- Fill the next preorder obligation with one compiled native action. -/
def step? (symbols : List String) (state : PrefixState)
    (action : Action) : Option PrefixState :=
  match state with
  | [] => none
  | expected :: rest => do
      let children ← compileChildren? symbols expected action
      pure (children ++ rest)

/-- The lightweight prefix step exposes the same declarative classification
as the proof-bearing typed-frontier instance. -/
theorem step?_some_classified (symbols : List String)
    (state next : PrefixState) (action : Action)
    (stepped : step? symbols state action = some next) :
    ∃ expected rest children,
      state = expected :: rest ∧
        Classifies symbols action expected children ∧
        next = children ++ rest := by
  cases state with
  | nil => simp [step?] at stepped
  | cons expected rest =>
      simp only [step?] at stepped
      cases compiled : compileChildren? symbols expected action with
      | none => simp [compiled] at stepped
      | some children =>
          simp only [compiled, Option.bind_eq_bind, Option.bind_some] at stepped
          exact ⟨expected, rest, children, rfl,
            compileChildren?_sound symbols expected action children compiled,
            (Option.some.inj stepped).symm⟩

def run? (symbols : List String) :
    PrefixState → List Action → Option PrefixState
  | state, [] => some state
  | state, action :: actions => do
      let next ← step? symbols state action
      run? symbols next actions

theorem run?_append (symbols : List String) (state : PrefixState)
    (first second : List Action) :
    run? symbols state (first ++ second) =
      (run? symbols state first).bind fun middle =>
        run? symbols middle second := by
  induction first generalizing state with
  | nil => rfl
  | cons action actions induction =>
      simp only [List.cons_append, run?]
      cases step : step? symbols state action with
      | none => simp
      | some next => simpa [step] using induction next

/-- Any prefix of a successful semantic trace is itself accepted and reaches
an explicit intermediate typed frontier. -/
theorem successful_run_preserves_prefix (symbols : List String)
    (state finalState : PrefixState) (actions leading : List Action)
    (isPrefix : leading <+: actions)
    (success : run? symbols state actions = some finalState) :
    ∃ middle, run? symbols state leading = some middle := by
  rcases isPrefix with ⟨suffix, rfl⟩
  rw [run?_append] at success
  cases firstRun : run? symbols state leading with
  | none => simp [firstRun] at success
  | some middle => exact ⟨middle, rfl⟩

/-! ## Independent derivations and non-stranding -/

/-- A source-classified forest.  Descendants of the first node and its
following siblings are separate witnesses, so no completeness claim is
smuggled in through the executable prefix machine. -/
inductive DerivesFrontier (symbols : List String) :
    List Expected → List Action → Prop where
  | nil : DerivesFrontier symbols [] []
  | cons {sort : Expected} {sorts children : List Expected}
      {action : Action} {childActions siblingActions : List Action}
      (classified : Classifies symbols action sort children)
      (descendants : DerivesFrontier symbols children childActions)
      (siblings : DerivesFrontier symbols sorts siblingActions) :
      DerivesFrontier symbols (sort :: sorts)
        (action :: (childActions ++ siblingActions))

/-- A derivation of exactly one root obligation. -/
abbrev Derives (symbols : List String) (sort : Expected)
    (actions : List Action) : Prop :=
  DerivesFrontier symbols [sort] actions

/-- A declaratively derived forest consumes exactly its frontier and leaves
any caller-supplied tail unchanged. -/
theorem DerivesFrontier.run_exact {symbols : List String}
    {sorts : List Expected} {actions : List Action}
    (derivation : DerivesFrontier symbols sorts actions)
    (tail : List Expected) :
    run? symbols (sorts ++ tail) actions = some tail := by
  induction derivation generalizing tail with
  | nil => rfl
  | cons classified descendants siblings descendantsInduction
      siblingsInduction =>
      simp only [List.cons_append, run?, step?,
        compileChildren?_complete symbols _ _ _ classified,
        Option.bind_eq_bind, Option.bind_some, pure_bind]
      rw [run?_append]
      rw [descendantsInduction]
      exact siblingsInduction tail

/-- Every source-derived root trace completes the semantic frontier. -/
theorem derived_program_completes {symbols : List String}
    {actions : List Action} (derivation : Derives symbols .program actions) :
    run? symbols initial actions = some [] := by
  exact derivation.run_exact []

/-- Every prefix of a source-derived root trace survives the hard semantic
mask. -/
theorem derived_program_prefix_non_stranding {symbols : List String}
    {actions leading : List Action}
    (derivation : Derives symbols .program actions)
    (isPrefix : leading <+: actions) :
    ∃ state, run? symbols initial leading = some state := by
  exact successful_run_preserves_prefix symbols initial [] actions leading
    isPrefix (derived_program_completes derivation)

/-! ## Positive and negative controls -/

private def fixtureSymbols : List String :=
  ["exec", "location", ",", "g", "step", "worker", "I", "BTM",
    "==", "O", "+", "count", "unknown"]

/-- The work head is accepted only at its source-derived total arity. -/
theorem exec_head_correct_arity_fixture :
    compileChildren? fixtureSymbols (.listHead .atom 4)
      (.reference 0) =
        some [.atom .key, .atom .inputSpec, .atom .outputSpec] := by
  decide +kernel

/-- The same known work head is rejected at an incorrect arity. -/
theorem exec_head_wrong_arity_fixture :
    compileChildren? fixtureSymbols (.listHead .atom 3)
      (.reference 0) = none := by
  decide +kernel

/-- An unknown head remains open-world and receives generic atom arguments. -/
theorem unknown_head_remains_admissible_fixture :
    compileChildren? fixtureSymbols (.listHead .atom 3)
      (.reference 1) = some [.atom .atom, .atom .atom] := by
  decide +kernel

/-- Compatibility input is variadic and places every child in pattern
context. -/
theorem compatibility_input_roles_fixture :
    compileChildren? fixtureSymbols (.listHead .inputSpec 3)
      (.reference 2) = some [.atom .pattern, .atom .pattern] := by
  decide +kernel

/-- The explicit input wrapper is variadic but each child must itself be a
source-profile provider form. -/
theorem explicit_input_roles_fixture :
    compileChildren? fixtureSymbols (.listHead .inputSpec 3)
      (.reference 6) = some [.atom .inputFactor, .atom .inputFactor] := by
  decide +kernel

/-- Provider arity is projected from the execution presentation. -/
theorem btm_provider_exact_arity_fixture :
    compileChildren? fixtureSymbols (.listHead .inputFactor 2)
      (.reference 7) = some [.atom .pattern] := by
  decide +kernel

/-- The same provider spelling at the wrong arity fails closed. -/
theorem btm_provider_wrong_arity_fixture :
    compileChildren? fixtureSymbols (.listHead .inputFactor 3)
      (.reference 7) = none := by
  decide +kernel

/-- Explicit output children are typed as source-declared sink forms. -/
theorem explicit_output_roles_fixture :
    compileChildren? fixtureSymbols (.listHead .outputSpec 3)
      (.reference 9) = some [.atom .outputSink, .atom .outputSink] := by
  decide +kernel

/-- Extension-provider syntax is retained even though its semantic contract
is separately classified by the execution presentation. -/
theorem count_sink_exact_arity_fixture :
    compileChildren? fixtureSymbols (.listHead .outputSink 4)
      (.reference 11) =
        some [.atom .template, .atom .template, .atom .template] := by
  decide +kernel

/-- An undeclared provider cannot enter a typed output-sink position. -/
theorem unknown_output_sink_is_rejected_fixture :
    compileChildren? fixtureSymbols (.listHead .outputSink 2)
      (.reference 12) = none := by
  decide +kernel

/-- Structured input positions require an expression, not an atomic symbol. -/
theorem atomic_input_spec_is_rejected_fixture :
    compileChildren? fixtureSymbols (.atom .inputSpec)
      (.reference 2) = none := by
  decide +kernel

/-- A source-known word inside pattern data remains data and preserves its
pattern context rather than acquiring executable-head meaning. -/
theorem executable_word_in_pattern_remains_data_fixture :
    compileChildren? fixtureSymbols (.listHead .pattern 3)
      (.reference 0) = some [.atom .pattern, .atom .pattern] := by
  decide +kernel

/-- An empty list used as a data head is already a complete child.  It must
not manufacture an impossible zero-arity head obligation. -/
theorem empty_data_head_consumes_exactly_one_outer_child_fixture :
    compileChildren? fixtureSymbols (.listHead .pattern 2) (.list 0) =
      some [.atom .pattern] := by
  decide +kernel

theorem empty_data_head_does_not_strand_zero_arity_head_fixture :
    compileChildren? fixtureSymbols (.listHead .pattern 2) (.list 0) ≠
      some [.listHead .pattern 0, .atom .pattern] := by
  decide +kernel

/-- The declared reflective worker shape acquires staged key, pattern, and
template roles. -/
theorem quoted_worker_shape_fixture :
    compileChildren? fixtureSymbols
      (.listHead .atom Cursor.source.quotedRuleArity)
      (.list Cursor.source.quotedTagArity) =
        some [.literal Cursor.source.quotedRuleHead, .atom .key,
          .atom .pattern, .atom .template] := by
  decide +kernel

/-- Ordinary nested expressions remain legal data when they do not have the
reserved reflective worker shape. -/
theorem ordinary_nested_head_remains_data_fixture :
    compileChildren? fixtureSymbols (.listHead .atom 7) (.list 2) =
      some [.listHead .atom 2, .atom .atom, .atom .atom, .atom .atom,
        .atom .atom, .atom .atom, .atom .atom] := by
  decide +kernel

/-- An empty list in head position consumes that child before the remaining
outer arguments are visited. -/
theorem empty_atom_head_remains_data_fixture :
    compileChildren? fixtureSymbols (.listHead .atom 3) (.list 0) =
      some [.atom .atom, .atom .atom] := by
  decide +kernel

/-! ## Exact MM2 binding boundary -/

open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Languages.ProcessCalculi.MORK

private def noInputVariables : InputSpec :=
  .compat (mkPattern [])

private def inheritedInputVariable : InputSpec :=
  .compat (mkPattern [.var "x"])

/-- A variable absent from the input is a lawful output-local binder under
the maintained MM2 rule-scoped semantics.  A global range-restriction mask
would reject this admitted case. -/
theorem output_local_variable_is_rule_scoped_lawful :
    ruleTemplateCovered noInputVariables [] (.var "fresh") = true := by
  rfl

/-- A name inherited from the input does require a matcher substitution at
execution time. -/
theorem inherited_variable_requires_matcher_binding :
    ruleTemplateCovered inheritedInputVariable [] (.var "x") = false := by
  rfl

/-- Once the input matcher supplies the inherited name, the same output is
covered. -/
theorem inherited_variable_is_covered_after_match :
    ruleTemplateCovered inheritedInputVariable
      [("x", .symbol "value")] (.var "x") = true := by
  rfl

#print axioms schema_heads_pairwise_distinct
#print axioms schemaFor?_some_exact
#print axioms compileChildren?_sound
#print axioms compileChildren?_complete
#print axioms compileChildren?_eq_some_iff
#print axioms compileHead?_some_exact
#print axioms refine?_some_source_typed
#print axioms refine?_some_preserves_typed_budget
#print axioms step?_some_classified
#print axioms successful_run_preserves_prefix
#print axioms DerivesFrontier.run_exact
#print axioms derived_program_completes
#print axioms derived_program_prefix_non_stranding
#print axioms exec_head_correct_arity_fixture
#print axioms exec_head_wrong_arity_fixture
#print axioms unknown_head_remains_admissible_fixture
#print axioms compatibility_input_roles_fixture
#print axioms explicit_input_roles_fixture
#print axioms btm_provider_exact_arity_fixture
#print axioms btm_provider_wrong_arity_fixture
#print axioms explicit_output_roles_fixture
#print axioms count_sink_exact_arity_fixture
#print axioms unknown_output_sink_is_rejected_fixture
#print axioms atomic_input_spec_is_rejected_fixture
#print axioms executable_word_in_pattern_remains_data_fixture
#print axioms empty_data_head_consumes_exactly_one_outer_child_fixture
#print axioms empty_data_head_does_not_strand_zero_arity_head_fixture
#print axioms quoted_worker_shape_fixture
#print axioms ordinary_nested_head_remains_data_fixture
#print axioms empty_atom_head_remains_data_fixture
#print axioms output_local_variable_is_rule_scoped_lawful
#print axioms inherited_variable_requires_matcher_binding
#print axioms inherited_variable_is_covered_after_match

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2NativeTypedRefinement
