import Mettapedia.Languages.MeTTa.OSLFCore.RewriteRules
import Mettapedia.Languages.MeTTa.OSLFCore.Types
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.GSLT.Parsing.SourceSExprPatternCodec
import Std.Data.String.ToInt
import Mettapedia.GSLT.LanguageDef.CarrierWellSorted

/-!
# MeTTaCore ↔ MeTTaIL Bridge

Integration between MeTTaCore (interpreter specification) and MeTTaIL
(process calculus meta-language). This bridge enables:

1. Converting MeTTaIL language definitions to MeTTaCore atomspaces
2. Converting MeTTaIL patterns to MeTTaCore atoms
3. Proving that MeTTaCore evaluation respects MeTTaIL semantics

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│  MeTTaIL: Language definitions (ρ-calculus, π-calculus, etc.)  │
│    - Pattern syntax                                             │
│    - Equations (bidirectional)                                  │
│    - Rewrite rules (directional)                                │
├─────────────────────────────────────────────────────────────────┤
│                    ↓ patternToAtom ↓                            │
│                    ↓ equationToAtom ↓                           │
├─────────────────────────────────────────────────────────────────┤
│  MeTTaCore: Interpreter specification                           │
│    - Atoms (symbol, var, grounded, expression)                  │
│    - Atomspace (knowledge base)                                 │
│    - Evaluation (rewrite rules)                                 │
└─────────────────────────────────────────────────────────────────┘
```

## References

* Meta-MeTTa paper: "MeTTa evaluates LanguageDefs"
* MeTTaIL Rust implementation
-/

namespace Mettapedia.Languages.MeTTa.OSLFCore.Bridge

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Pattern to Atom Conversion -/

/-- Convert a collection type to its symbol representation -/
def collTypeToSymbol : CollType → String
  | .vec => "Vec"
  | .hashBag => "Bag"
  | .hashSet => "Set"

/-- Convert a MeTTaIL Pattern to a MeTTaCore Atom.

    This is the core bridge function. The mapping is:
    - Pattern.var v → Atom.var v
    - Pattern.apply c args → Atom.expression (symbol c :: args.map patternToAtom)
    - Pattern.lambda x body → Atom.expression [symbol "λ", var x, patternToAtom body]
    - Pattern.collection ct elems rest → Atom.expression (collType :: elems ++ [rest])
    - Pattern.subst body x repl → (patternToAtom body)[x := patternToAtom repl]
-/
def patternToAtom : Pattern → Atom
  | .bvar n => .var ("#b" ++ toString n)
  | .fvar name => .var name
  | .apply constructor args =>
      .expression (.symbol constructor :: args.map patternToAtom)
  | .lambda _nm body =>
      .expression [.symbol "λ", patternToAtom body]
  | .multiLambda n _nms body =>
      .expression [.symbol "λ*", .symbol (toString n), patternToAtom body]
  | .subst body repl =>
      .expression [.symbol "subst", patternToAtom body, patternToAtom repl]
  | .collection ct elems rest =>
      let elemAtoms := elems.map patternToAtom
      let restAtom := rest.map (fun r => [.var r]) |>.getD []
      .expression (.symbol (collTypeToSymbol ct) :: elemAtoms ++ restAtom)

/-- Convert a MeTTaCore Atom back to a MeTTaIL Pattern (if possible).
    This is a partial inverse of patternToAtom. -/
def atomToPattern : Atom → Option Pattern
  | .var name => some (.fvar name)
  | .symbol s => some (.apply s [])  -- Treat symbols as nullary constructors
  | .expression (.symbol constructor :: args) =>
      if constructor == "λ" then
        match args with
        | [body] => atomToPattern body |>.map (.lambda none)
        | _ => none
      else if constructor == "subst" then
        match args with
        | [body, repl] => do
            let body' ← atomToPattern body
            let repl' ← atomToPattern repl
            return .subst body' repl'
        | _ => none
      else
        let patArgs := args.filterMap atomToPattern
        if patArgs.length == args.length then
          some (.apply constructor patArgs)
        else
          none
  | _ => none

/-! ## Faithful ground-data encoding

The projection above interprets selected Pattern forms and is not an
injective Atom codec: it merges symbols with nullary expressions. The tagged
data encoding below uses the existing lossless S-expression literal codec.
Every Atom constructor remains distinct and guest variables remain ground
data. This is a representation theorem, not a rewrite or evaluation simulation.
-/

namespace GroundData

open Mettapedia.OSLF.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple.Parser (SExpr)

private def literal (value : String) : Pattern :=
  Mettapedia.GSLT.Parsing.SourceSExprPatternCodec.encode (.atom value)

private def readLiteral (pattern : Pattern) : Option String :=
  match Mettapedia.GSLT.Parsing.SourceSExprPatternCodec.decode pattern with
  | some (.atom value) => some value
  | _ => none

@[simp] private theorem readLiteral_literal (value : String) :
    readLiteral (literal value) = some value := by
  simp [readLiteral, literal]

private theorem literal_isGroundAt (value : String) (depth : Nat) :
    (literal value).isGroundAt depth = true :=
  Mettapedia.GSLT.Parsing.SourceSExprPatternCodec.encode_isGroundAt (.atom value) depth

mutual
  /-- Tagged Atom data in Pattern. Guest variables and symbol spellings are
  inert literal payloads; expressions retain ordered child occurrences. -/
  def encode : Atom → Pattern
    | .symbol name => .apply "ground-atom-symbol-v1" [literal name]
    | .var name => .apply "ground-atom-variable-v1" [literal name]
    | .grounded (.int value) => .apply "ground-atom-integer-v1" [literal (toString value)]
    | .grounded (.string value) => .apply "ground-atom-string-v1" [literal value]
    | .grounded (.bool false) => .apply "ground-atom-boolean-false-v1" []
    | .grounded (.bool true) => .apply "ground-atom-boolean-true-v1" []
    | .grounded (.custom typeName data) =>
        .apply "ground-atom-custom-v1" [literal typeName, literal data]
    | .expression values => .apply "ground-atom-expression-v1"
        [.collection .vec (encodeList values) none]
  termination_by atom => sizeOf atom

  def encodeList : List Atom → List Pattern
    | [] => []
    | value :: values => encode value :: encodeList values
  termination_by values => sizeOf values
end

mutual
  private def decodeRaw : Pattern → Option Atom
    | .apply "ground-atom-symbol-v1" [name] => .symbol <$> readLiteral name
    | .apply "ground-atom-variable-v1" [name] => .var <$> readLiteral name
    | .apply "ground-atom-integer-v1" [value] => do
        let spelling ← readLiteral value
        return .grounded (.int (← spelling.toInt?))
    | .apply "ground-atom-string-v1" [value] =>
        (fun value => .grounded (.string value)) <$> readLiteral value
    | .apply "ground-atom-boolean-false-v1" [] => some (.grounded (.bool false))
    | .apply "ground-atom-boolean-true-v1" [] => some (.grounded (.bool true))
    | .apply "ground-atom-custom-v1" [typeName, data] => do
        return .grounded (.custom (← readLiteral typeName) (← readLiteral data))
    | .apply "ground-atom-expression-v1" [.collection .vec values none] =>
        .expression <$> decodeListRaw values
    | _ => none
  termination_by pattern => sizeOf pattern

  private def decodeListRaw : List Pattern → Option (List Atom)
    | [] => some []
    | value :: values => do
        return (← decodeRaw value) :: (← decodeListRaw values)
  termination_by values => sizeOf values
end

mutual
  private theorem decodeRaw_encode (atom : Atom) : decodeRaw (encode atom) = some atom := by
    cases atom with
    | symbol name => simp [encode, decodeRaw]
    | var name => simp [encode, decodeRaw]
    | grounded value =>
        cases value with
        | int value => simp [encode, decodeRaw, Int.toInt?_repr]
        | string value => simp [encode, decodeRaw]
        | bool value => cases value <;> simp [encode, decodeRaw]
        | custom typeName data => simp [encode, decodeRaw]
    | expression values => simp [encode, decodeRaw, decodeListRaw_encodeList values]
  termination_by sizeOf atom

  private theorem decodeListRaw_encodeList (values : List Atom) :
      decodeListRaw (encodeList values) = some values := by
    cases values with
    | nil => simp [encodeList, decodeListRaw]
    | cons value values =>
        simp [encodeList, decodeListRaw, decodeRaw_encode value, decodeListRaw_encodeList values]
  termination_by sizeOf values
end

/-- Decode exactly the canonical ground-data image, including canonical integer
spelling. A successful decoder never evaluates the represented guest atom. -/
def decode (pattern : Pattern) : Option Atom := do
  let atom ← decodeRaw pattern
  if encode atom = pattern then some atom else none

def decodeList (patterns : List Pattern) : Option (List Atom) := do
  let atoms ← decodeListRaw patterns
  if encodeList atoms = patterns then some atoms else none

@[simp] theorem decode_encode (atom : Atom) : decode (encode atom) = some atom := by
  simp [decode, decodeRaw_encode]

@[simp] theorem decodeList_encodeList (atoms : List Atom) :
    decodeList (encodeList atoms) = some atoms := by
  simp [decodeList, decodeListRaw_encodeList]

theorem encode_of_decode {pattern : Pattern} {atom : Atom}
    (accepted : decode pattern = some atom) : encode atom = pattern := by
  cases raw : decodeRaw pattern with
  | none => simp [decode, raw] at accepted
  | some actual =>
      by_cases canonical : encode actual = pattern
      · have same : actual = atom := by simpa [decode, raw, canonical] using accepted
        simpa [same] using canonical
      · simp [decode, raw, canonical] at accepted

theorem encodeList_of_decodeList {patterns : List Pattern} {atoms : List Atom}
    (accepted : decodeList patterns = some atoms) : encodeList atoms = patterns := by
  cases raw : decodeListRaw patterns with
  | none => simp [decodeList, raw] at accepted
  | some actual =>
      by_cases canonical : encodeList actual = patterns
      · have same : actual = atoms := by simpa [decodeList, raw, canonical] using accepted
        simpa [same] using canonical
      · simp [decodeList, raw, canonical] at accepted

theorem decode_eq_some_iff (pattern : Pattern) (atom : Atom) :
    decode pattern = some atom ↔ encode atom = pattern := by
  constructor
  · exact encode_of_decode
  · rintro rfl
    exact decode_encode atom

theorem decodeList_eq_some_iff (patterns : List Pattern) (atoms : List Atom) :
    decodeList patterns = some atoms ↔ encodeList atoms = patterns := by
  constructor
  · exact encodeList_of_decodeList
  · rintro rfl
    exact decodeList_encodeList atoms

theorem encode_injective : Function.Injective encode := by
  intro left right same
  have decoded := congrArg decode same
  simpa only [decode_encode, Option.some.injEq] using decoded

theorem encodeList_injective : Function.Injective encodeList := by
  intro left right same
  have decoded := congrArg decodeList same
  simpa only [decodeList_encodeList, Option.some.injEq] using decoded

mutual
  theorem encode_isGroundAt (atom : Atom) (depth : Nat) :
      (encode atom).isGroundAt depth = true := by
    cases atom with
    | symbol name =>
        simp only [encode, Pattern.isGroundAt, Pattern.isGroundListAt,
          literal_isGroundAt, Bool.and_self]
    | var name =>
        simp only [encode, Pattern.isGroundAt, Pattern.isGroundListAt,
          literal_isGroundAt, Bool.and_self]
    | grounded value =>
        cases value with
        | bool value => cases value <;> simp [encode, Pattern.isGroundAt, Pattern.isGroundListAt]
        | int _ | string _ | custom _ _ =>
            simp only [encode, Pattern.isGroundAt, Pattern.isGroundListAt,
              literal_isGroundAt, Bool.and_self]
    | expression values =>
        simpa only [encode, Pattern.isGroundAt, Pattern.isGroundListAt,
          Option.isNone, Bool.and_true] using encodeList_isGroundAt values depth
  termination_by sizeOf atom

  theorem encodeList_isGroundAt (values : List Atom) (depth : Nat) :
      Pattern.isGroundListAt depth (encodeList values) = true := by
    cases values with
    | nil => simp [encodeList, Pattern.isGroundListAt]
    | cons value values =>
        simp only [encodeList, Pattern.isGroundListAt, encode_isGroundAt value depth,
          encodeList_isGroundAt values depth, Bool.and_self]
  termination_by sizeOf values
end

theorem encode_isGround (atom : Atom) : (encode atom).isGround = true :=
  encode_isGroundAt atom 0

theorem symbol_and_nullary_expression_distinct (name : String) :
    encode (.symbol name) ≠ encode (.expression [.symbol name]) := by
  intro same
  have := encode_injective same
  cases this

theorem duplicate_occurrences_preserved (atom : Atom) :
    encode (.expression [atom, atom]) ≠ encode (.expression [atom]) := by
  intro same
  have := encode_injective same
  cases this

theorem expression_order_preserved (left right : Atom) (distinct : left ≠ right) :
    encode (.expression [left, right]) ≠ encode (.expression [right, left]) := by
  intro same
  have := encode_injective same
  cases Atom.expression.inj this
  exact distinct rfl

theorem variable_spelling_is_ground_data (name : String) :
    decode (encode (.var name)) = some (.var name) ∧
      (encode (.var name)).isGround = true :=
  ⟨decode_encode _, encode_isGround _⟩

theorem malformed_symbol_arity_rejected :
    decode (.apply "ground-atom-symbol-v1" []) = none := by simp [decode, decodeRaw]

theorem untagged_symbol_rejected : decode (.apply "foo" []) = none := by simp [decode, decodeRaw]

theorem pattern_variable_rejected (name : String) : decode (.fvar name) = none := by simp [decode, decodeRaw]

theorem integer_alias_rejected (spelling : String) (value : Int)
    (parsed : spelling.toInt? = some value) (noncanonical : toString value ≠ spelling) :
    decode (.apply "ground-atom-integer-v1" [literal spelling]) = none := by
  change value.repr ≠ spelling at noncanonical
  simp only [decode, decodeRaw, readLiteral_literal, parsed, bind, Option.bind, pure]
  simp [encode, literal, Mettapedia.GSLT.Parsing.SourceSExprPatternCodec.encode, noncanonical]

theorem noncanonical_integer_rejected :
    decode (.apply "ground-atom-integer-v1" [literal "-0"]) = none := by
  apply integer_alias_rejected "-0" 0
  · change ("-" ++ Nat.repr 0).toInt? = some 0
    simp
  · decide

theorem grounded_integer_and_symbol_distinct (value : Int) :
    encode (.grounded (.int value)) ≠ encode (.symbol (toString value)) := by
  intro same
  have := encode_injective same
  cases this

/-! ### Declared carrier for the ground data codec -/

private def dataConstructor (label category : String) (parameters : List TermParam) :
    GrammarRule :=
  { label, category, params := parameters, syntaxPattern := [] }

/-- The structural data carrier of the Atom codec. Its vector collection
preserves ordered child occurrences. This declares no evaluation rules for
PeTTa programs; those must be connected to the existing operational judgment. -/
def dataLanguage : LanguageDef :=
  { name := "GroundAtomData"
    types := ["GroundAtom", "GroundLiteral", "GroundList",
      { name := "GroundText", carrier := .builtinString }]
    terms := [
      dataConstructor "source-sexpr-atom-v1" "GroundLiteral"
        [.simple "spelling" (.base "GroundText")],
      dataConstructor "ground-atom-symbol-v1" "GroundAtom"
        [.simple "payload" (.base "GroundLiteral")],
      dataConstructor "ground-atom-variable-v1" "GroundAtom"
        [.simple "payload" (.base "GroundLiteral")],
      dataConstructor "ground-atom-integer-v1" "GroundAtom"
        [.simple "payload" (.base "GroundLiteral")],
      dataConstructor "ground-atom-string-v1" "GroundAtom"
        [.simple "payload" (.base "GroundLiteral")],
      dataConstructor "ground-atom-boolean-false-v1" "GroundAtom" [],
      dataConstructor "ground-atom-boolean-true-v1" "GroundAtom" [],
      dataConstructor "ground-atom-custom-v1" "GroundAtom"
        [.simple "type" (.base "GroundLiteral"),
          .simple "data" (.base "GroundLiteral")],
      dataConstructor "ground-atom-expression-v1" "GroundAtom"
        [.simple "payload" (.base "GroundList")],
      dataConstructor "ground-atom-list-v1" "GroundList"
        [.simple "values" (.collection .vec (.base "GroundAtom"))]]
    equations := []
    rewrites := [] }

open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext UsesBareCollection)

private theorem literal_has_type (spelling : String) (free : FreeTypeContext)
    (bound : List TypeExpr) :
    Mettapedia.GSLT.LanguageDef.CarrierWellSorted.HasType dataLanguage free bound (literal spelling) (.base "GroundLiteral") := by
  change Mettapedia.GSLT.LanguageDef.CarrierWellSorted.HasType dataLanguage free bound
    (.apply "source-sexpr-atom-v1" [.apply spelling []]) (.base "GroundLiteral")
  refine .constructor (rule := dataConstructor "source-sexpr-atom-v1" "GroundLiteral"
    [.simple "spelling" (.base "GroundText")]) (by decide) ?_ ?_
  · simp [UsesBareCollection, dataConstructor]
  · refine .cons (by trivial) rfl (.builtinAtom ?_) .nil
    exact ⟨{ name := "GroundText", carrier := .builtinString },
      .tail _ (.tail _ (.tail _ (.head _))), rfl, rfl⟩

private theorem unary_data_has_type (tag sort : String) (payload : Pattern)
    (free : FreeTypeContext) (bound : List TypeExpr)
    (member : dataConstructor tag "GroundAtom" [.simple "payload" (.base sort)] ∈
      dataLanguage.terms)
    (typed : Mettapedia.GSLT.LanguageDef.CarrierWellSorted.HasType dataLanguage free bound payload (.base sort)) :
    Mettapedia.GSLT.LanguageDef.CarrierWellSorted.HasType dataLanguage free bound (.apply tag [payload]) (.base "GroundAtom") := by
  refine .constructor member ?_ ?_
  · simp [UsesBareCollection, dataConstructor]
  · exact .cons (by trivial) rfl typed .nil

mutual
  /-- Every encoded Atom belongs to its declared LanguageDef carrier,
  independently of any variable typing context. Guest variables are data. -/
  theorem encode_has_type (atom : Atom) (free : FreeTypeContext)
      (bound : List TypeExpr) :
      Mettapedia.GSLT.LanguageDef.CarrierWellSorted.HasType dataLanguage free bound (encode atom) (.base "GroundAtom") := by
    cases atom with
    | symbol spelling =>
        simp only [encode]
        exact unary_data_has_type "ground-atom-symbol-v1" "GroundLiteral" _ free bound (by decide)
          (literal_has_type spelling free bound)
    | var spelling =>
        simp only [encode]
        exact unary_data_has_type "ground-atom-variable-v1" "GroundLiteral" _ free bound (by decide)
          (literal_has_type spelling free bound)
    | grounded value =>
        cases value with
        | int value =>
            simp only [encode]
            exact unary_data_has_type "ground-atom-integer-v1" "GroundLiteral" _ free bound (by decide)
              (literal_has_type (toString value) free bound)
        | string value =>
            simp only [encode]
            exact unary_data_has_type "ground-atom-string-v1" "GroundLiteral" _ free bound (by decide)
              (literal_has_type value free bound)
        | bool value =>
            cases value with
            | false =>
                simp only [encode]
                exact .constructor (rule := dataConstructor "ground-atom-boolean-false-v1" "GroundAtom" [])
                  (by decide) (by simp [UsesBareCollection, dataConstructor]) .nil
            | true =>
                simp only [encode]
                exact .constructor (rule := dataConstructor "ground-atom-boolean-true-v1" "GroundAtom" [])
                  (by decide) (by simp [UsesBareCollection, dataConstructor]) .nil
        | custom typeName data =>
            simp only [encode]
            refine .constructor (rule := dataConstructor "ground-atom-custom-v1" "GroundAtom"
              [.simple "type" (.base "GroundLiteral"),
                .simple "data" (.base "GroundLiteral")]) (by decide) ?_ ?_
            · simp [UsesBareCollection, dataConstructor]
            · exact .cons (by trivial) rfl (literal_has_type typeName free bound)
                (.cons (by trivial) rfl (literal_has_type data free bound) .nil)
    | expression values =>
        simp only [encode]
        apply unary_data_has_type "ground-atom-expression-v1" "GroundList" _ free bound (by decide)
        exact .collectionConstructor
          (rule := dataConstructor "ground-atom-list-v1" "GroundList"
            [.simple "values" (.collection .vec (.base "GroundAtom"))])
          (by decide) rfl (encodeList_has_type values free bound)
  termination_by sizeOf atom

  theorem encodeList_has_type (atoms : List Atom) (free : FreeTypeContext)
      (bound : List TypeExpr) :
      Mettapedia.GSLT.LanguageDef.CarrierWellSorted.ElementsHaveTypes dataLanguage free bound (encodeList atoms) (.base "GroundAtom") := by
    cases atoms with
    | nil => simpa only [encodeList] using
        (Mettapedia.GSLT.LanguageDef.CarrierWellSorted.ElementsHaveTypes.nil
          (language := dataLanguage) (free := free) (bound := bound)
          (elementType := .base "GroundAtom"))
    | cons atom atoms =>
        simpa only [encodeList] using
          Mettapedia.GSLT.LanguageDef.CarrierWellSorted.ElementsHaveTypes.cons
            (encode_has_type atom free bound) (encodeList_has_type atoms free bound)
  termination_by sizeOf atoms
end

mutual
  theorem encode_isObject (atom : Atom) :
      Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPattern (encode atom) = true := by
    cases atom with
    | symbol _ | var _ =>
        simp [encode, literal, Mettapedia.GSLT.Parsing.SourceSExprPatternCodec.encode,
          Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPattern,
          Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList]
    | grounded value =>
        cases value with
        | bool value => cases value <;>
            simp [encode, Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPattern,
              Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList]
        | int _ | string _ | custom _ _ =>
            simp [encode, literal, Mettapedia.GSLT.Parsing.SourceSExprPatternCodec.encode,
              Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPattern,
              Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList]
    | expression values =>
        simpa only [encode, Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPattern,
          Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList, Option.isNone,
          Bool.and_true, Bool.true_and] using encodeList_isObject values
  termination_by sizeOf atom

  theorem encodeList_isObject (atoms : List Atom) :
      Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList (encodeList atoms) = true := by
    cases atoms with
    | nil => simp only [encodeList, Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList]
    | cons atom atoms =>
        simp only [encodeList, Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList,
          encode_isObject atom, encodeList_isObject atoms, Bool.and_self]
  termination_by sizeOf atoms
end

theorem encode_checked (atom : Atom) (free : FreeTypeContext) (bound : List TypeExpr) :
    Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType dataLanguage free bound
      (encode atom) (.base "GroundAtom") = true :=
  Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType_complete_of_object
    (encode_has_type atom free bound) (encode_isObject atom)

/-- Structural sorting alone does not imply membership in the canonical
codec image. The decoder additionally checks integer spelling. -/
theorem data_type_does_not_imply_decodable :
    ∃ pattern, Mettapedia.GSLT.LanguageDef.CarrierWellSorted.HasType dataLanguage
        (fun _ => none) [] pattern (.base "GroundAtom") ∧ decode pattern = none := by
  refine ⟨.apply "ground-atom-integer-v1" [literal "-0"], ?_, noncanonical_integer_rejected⟩
  exact unary_data_has_type "ground-atom-integer-v1" "GroundLiteral" _ (fun _ => none) []
    (by decide) (literal_has_type "-0" (fun _ => none) [])

/-- The declared carrier does not accept an unboxed expression spine. -/
theorem unboxed_expression_has_no_data_type :
    Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType dataLanguage (fun _ => none) []
      (.apply "ground-atom-expression-v1" []) (.base "GroundAtom") = false := by
  decide

/-- A host Pattern variable is not a closed guest-variable payload. -/
theorem raw_pattern_variable_has_no_data_type (name : String) :
    Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType dataLanguage (fun _ => none) [] (.fvar name) (.base "GroundAtom") = false := rfl


end GroundData

/-! ## Equation to Atom Conversion -/

/-- Convert a MeTTaIL Equation to a MeTTaCore equality atom: `(= lhs rhs)` -/
def equationToAtom (eq : Equation) : Atom :=
  Atom.equality (patternToAtom eq.left) (patternToAtom eq.right)

/-- Convert a list of equations to atoms -/
def equationsToAtoms (eqs : List Equation) : List Atom :=
  eqs.map equationToAtom

/-! ## Type Expression to Atom Conversion -/

/-- Convert a MeTTaIL TypeExpr to a MeTTaCore type atom -/
def typeExprToAtom : TypeExpr → Atom
  | .base name => .symbol name
  | .arrow dom cod =>
      functionType [typeExprToAtom dom] (typeExprToAtom cod)
  | .multiBinder inner =>
      .expression [.symbol "Multi", typeExprToAtom inner]
  | .collection ct inner =>
      .expression [.symbol (collTypeToSymbol ct), typeExprToAtom inner]

/-! ## Language Definition to Atomspace -/

/-- Create an atomspace from a list of equations.
    This is the core bridge: MeTTaIL equations become MeTTaCore knowledge. -/
def equationsToAtomspace (eqs : List Equation) : Atomspace :=
  Atomspace.ofList (equationsToAtoms eqs)

/-- Add type declarations from grammar rules to atomspace -/
def addGrammarTypes (space : Atomspace) (rules : List GrammarRule) : Atomspace :=
  rules.foldl (fun acc rule =>
    -- Add type annotation for the constructor
    let constructorType := .symbol rule.category
    let constructorAtom := .symbol rule.label
    acc.addType constructorAtom constructorType
  ) space

/-! ## Evaluation Bridge -/

/-- Evaluate a MeTTaIL pattern in a MeTTaCore atomspace.
    This bridges the gap between MeTTaIL reduction and MeTTaCore evaluation. -/
def evaluatePattern (eqs : List Equation) (pat : Pattern) (fuel : Nat) : Multiset Atom :=
  let space := equationsToAtomspace eqs
  let atom := patternToAtom pat
  evaluate fuel space atom

/-! ## Soundness Properties -/

/-- Pattern conversion preserves variable names (concrete example) -/
theorem patternToAtom_var_example :
    patternToAtom (.fvar "x") = .var "x" := by simp [patternToAtom]

/-- Pattern conversion preserves constructor applications (concrete example) -/
theorem patternToAtom_apply_example :
    patternToAtom (.apply "Nil" []) = .expression [.symbol "Nil"] := by
  simp [patternToAtom]

/-- Pattern conversion preserves lambda abstractions (concrete example) -/
theorem patternToAtom_lambda_example :
    patternToAtom (.lambda none (.bvar 0)) =
    .expression [.symbol "λ", .var ("#b" ++ toString 0)] := by
  simp [patternToAtom]

/-- Equation conversion creates proper equality atoms -/
theorem equationToAtom_structure (eq : Equation) :
    ∃ lhs rhs, equationToAtom eq = .expression [.symbol "=", lhs, rhs] :=
  ⟨patternToAtom eq.left, patternToAtom eq.right, rfl⟩

/-- Round-trip check for variable patterns. -/
theorem roundtrip_var_succeeds :
    (atomToPattern (patternToAtom (.fvar "x"))).isSome = true := by
  simp [patternToAtom, atomToPattern]

/-- Round-trip check for nullary applications -/
theorem roundtrip_apply_nullary_succeeds :
    (atomToPattern (patternToAtom (.apply "Nil" []))).isSome = true := by
  simp [patternToAtom, atomToPattern]

/-! ## Example: ρ-calculus Bridge -/

/-- Example: The COMM rule from ρ-calculus as an equation.
    { n!(q) | for(x <- n){p} } ~> { p[@q/x] }

    In MeTTaIL:
    - LHS: PPar [POutput (NQuote q) n, PInput (PVar x) n p]
    - RHS: p[q/x]  (substitution)
-/
def exampleCommLhs : Pattern :=
  .apply "PPar" [
    .apply "POutput" [.apply "NQuote" [.fvar "q"], .fvar "n"],
    .apply "PInput" [.fvar "x", .fvar "n", .fvar "p"]
  ]

def exampleCommRhs : Pattern :=
  .subst (.fvar "p") (.apply "NQuote" [.fvar "q"])

def exampleCommEquation : Equation := {
  name := "COMM"
  typeContext := [("n", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc")]
  premises := []
  left := exampleCommLhs
  right := exampleCommRhs
}

/-- The COMM equation as a MeTTaCore atom -/
example : equationToAtom exampleCommEquation =
    Atom.expression [
      .symbol "=",
      .expression [
        .symbol "PPar",
        .expression [.symbol "POutput", .expression [.symbol "NQuote", Atom.var "q"], Atom.var "n"],
        .expression [.symbol "PInput", Atom.var "x", Atom.var "n", Atom.var "p"]
      ],
      .expression [.symbol "subst", Atom.var "p", .expression [.symbol "NQuote", Atom.var "q"]]
    ] := by simp [equationToAtom, Atom.equality, exampleCommEquation, exampleCommLhs, exampleCommRhs, patternToAtom]

/-! ## Unit Tests -/

section Tests

-- Pattern conversion
example : patternToAtom (.fvar "x") = .var "x" := by simp [patternToAtom]
example : patternToAtom (.apply "Nil" []) = .expression [.symbol "Nil"] := by
  simp [patternToAtom]
example : patternToAtom (.apply "Cons" [.fvar "h", .fvar "t"]) =
          .expression [.symbol "Cons", .var "h", .var "t"] := by
  simp [patternToAtom]

-- Lambda conversion (locally nameless: one arg)
example : patternToAtom (.lambda none (.bvar 0)) =
          .expression [.symbol "λ", .var ("#b" ++ toString 0)] := by
  simp [patternToAtom]

-- Collection conversion
example : patternToAtom (.collection .hashBag [.fvar "a", .fvar "b"] none) =
          .expression [.symbol "Bag", .var "a", .var "b"] := by
  simp [patternToAtom, collTypeToSymbol]

-- Type expression conversion
example : typeExprToAtom (.base "Proc") = .symbol "Proc" := rfl
example : typeExprToAtom (.arrow (.base "Name") (.base "Proc")) =
          .expression [.symbol "->", .symbol "Name", .symbol "Proc"] := rfl

end Tests

end Mettapedia.Languages.MeTTa.OSLFCore.Bridge
