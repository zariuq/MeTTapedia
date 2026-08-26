import Mettapedia.GSLT.LanguageDef.RFC8259SyntaxNTT
import Mettapedia.GSLT.Parsing.ClassAwareNativeForestQualification

/-!
# Occurrence-preserving RFC 8259 value elaboration

This module gives the lossless RFC 8259 CST an independently executable,
pure value semantics.  Numbers retain their exact source lexeme, strings are
Unicode-scalar lists, and objects retain ordered duplicate members with both
object-local occurrence indices and source spans.  Syntactically valid lone
surrogate escapes remain an explicit semantic rejection.

The final equivalences lift the existing complete ParserPack/native-forest
correspondence through this elaborator.  They compare complete occurrence
fibres at a named semantic outcome; equal values do not collapse distinct
parse or production occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RFC8259ValueSemantics

open Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityInventory
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestQualification
open Mettapedia.GSLT.Parsing.ClassAwarePackedForest
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.GSLT.Parsing.PresentationExprSemantics

/-- Half-open source span of an authored syntax occurrence. -/
structure SourceSpan where
  start : Nat
  stop : Nat
  deriving DecidableEq, Repr

/-- An object member before its object-local occurrence number is assigned. -/
structure PendingMember (Value : Type) where
  key : List Nat
  value : Value
  span : SourceSpan
  deriving Repr

/-- Object members retain order, duplicate occurrences, and source spans. -/
structure JSONMember (Value : Type) where
  occurrence : Nat
  key : List Nat
  value : Value
  span : SourceSpan
  deriving Repr

/-- Lossless semantic JSON values.  A number is a codepoint lexeme rather
than a host floating-point approximation. -/
inductive JSONValue where
  | null
  | boolean (value : Bool)
  | string (scalars : List Nat)
  | number (lexeme : List Nat)
  | array (elements : List JSONValue)
  | object (members : List (JSONMember JSONValue))

/-- Semantic failures are distinct from syntax rejection.  In particular,
RFC 8259 admits escaped UTF-16 code units syntactically while this value
profile accepts only Unicode scalar strings. -/
inductive ElaborationOutcome where
  | value (value : JSONValue)
  | invalidUnicodeEscape
  | malformedCST

private inductive ElaborationError where
  | invalidUnicodeEscape
  | malformedCST
  deriving DecidableEq, Repr

private inductive StringPiece where
  | scalar (value : Nat)
  | codeUnit (value : Nat)
  deriving DecidableEq, Repr

private inductive Attribute where
  | terminal (codepoints : List Nat)
  | unit
  | scalar (value : Nat)
  | pieces (values : List StringPiece)
  | string (scalars : List Nat)
  | numberText (codepoints : List Nat)
  | value (value : JSONValue)
  | member (member : PendingMember JSONValue)
  | members (members : List (PendingMember JSONValue))
  | values (values : List JSONValue)
  | object (members : List (JSONMember JSONValue))
  | array (values : List JSONValue)
  | root (value : JSONValue)

private def isUnicodeScalar (codepoint : Nat) : Bool :=
  codepoint ≤ 0x10ffff && !(0xd800 ≤ codepoint && codepoint ≤ 0xdfff)

private def isHighSurrogate (unit : Nat) : Bool :=
  0xd800 ≤ unit && unit ≤ 0xdbff

private def isLowSurrogate (unit : Nat) : Bool :=
  0xdc00 ≤ unit && unit ≤ 0xdfff

private def combineSurrogates (high low : Nat) : Nat :=
  0x10000 + (high - 0xd800) * 0x400 + (low - 0xdc00)

private def hexValue? (codepoint : Nat) : Option Nat :=
  if 48 ≤ codepoint && codepoint ≤ 57 then
    some (codepoint - 48)
  else if 65 ≤ codepoint && codepoint ≤ 70 then
    some (codepoint - 65 + 10)
  else if 97 ≤ codepoint && codepoint ≤ 102 then
    some (codepoint - 97 + 10)
  else
    none

private def simpleEscape? (codepoint : Nat) : Option Nat :=
  match codepoint with
  | 34 => some 34
  | 47 => some 47
  | 92 => some 92
  | 98 => some 8
  | 102 => some 12
  | 110 => some 10
  | 114 => some 13
  | 116 => some 9
  | _ => none

private def unicodeUnit? (digits : List Attribute) : Option Nat :=
  match digits with
  | [.scalar first, .scalar second, .scalar third, .scalar fourth] => do
      let a ← hexValue? first
      let b ← hexValue? second
      let c ← hexValue? third
      let d ← hexValue? fourth
      pure (((a * 16 + b) * 16 + c) * 16 + d)
  | _ => none

private def resolveStringPieces :
    List StringPiece → Except ElaborationError (List Nat)
  | [] => .ok []
  | .scalar codepoint :: rest => do
      if !isUnicodeScalar codepoint then
        throw .malformedCST
      pure (codepoint :: (← resolveStringPieces rest))
  | .codeUnit first :: rest =>
      if isHighSurrogate first then
        match rest with
        | .codeUnit second :: tail =>
            if isLowSurrogate second then do
              pure (combineSurrogates first second ::
                (← resolveStringPieces tail))
            else
              throw .invalidUnicodeEscape
        | _ => throw .invalidUnicodeEscape
      else if isLowSurrogate first then
        throw .invalidUnicodeEscape
      else if first ≤ 0xffff then do
        pure (first :: (← resolveStringPieces rest))
      else
        throw .malformedCST

private def assignMemberOccurrences
    (members : List (PendingMember JSONValue)) :
    List (JSONMember JSONValue) :=
  members.zipIdx.map fun entry => {
    occurrence := entry.2
    key := entry.1.key
    value := entry.1.value
    span := entry.1.span
  }

private def isWhitespace (codepoint : Nat) : Bool :=
  codepoint == 0x20 || codepoint == 0x09 ||
    codepoint == 0x0a || codepoint == 0x0d

private def lexicalScalar? (children : List Attribute) : Option Nat :=
  match children with
  | [.terminal [codepoint]] =>
      if isUnicodeScalar codepoint then some codepoint else none
  | _ => none

private def elaborateNode (label : String) (start stop : Nat)
    (children : List Attribute) : Except ElaborationError Attribute := do
  match label, children with
  | "json:lex-ws", children
  | "json:lex-unescaped", children
  | "json:lex-digit", children
  | "json:lex-digit19", children
  | "json:lex-hexdigit", children
  | "json:lex-simple-escape", children
  | "json:lex-exp-mark", children
  | "json:lex-sign", children =>
      match lexicalScalar? children with
      | some codepoint => pure (.scalar codepoint)
      | none => throw .malformedCST
  | "json:text", [.unit, .value value, .unit] => pure (.root value)
  | "json:ws-empty", [] => pure .unit
  | "json:ws-cons", [.scalar head, .unit] =>
      if isWhitespace head then pure .unit else throw .malformedCST
  | "json:value-false", [] => pure (.value (.boolean false))
  | "json:value-null", [] => pure (.value .null)
  | "json:value-true", [] => pure (.value (.boolean true))
  | "json:value-object", [.object members] =>
      pure (.value (.object members))
  | "json:value-array", [.array values] =>
      pure (.value (.array values))
  | "json:value-number", [.numberText number] =>
      pure (.value (.number number))
  | "json:value-string", [.string scalars] =>
      pure (.value (.string scalars))
  | "json:object", [.unit, .members members, .unit] =>
      pure (.object (assignMemberOccurrences members))
  | "json:members-none", [] => pure (.members [])
  | "json:members-some", [.members members] => pure (.members members)
  | "json:members", [.member member, .members tail] =>
      pure (.members (member :: tail))
  | "json:member-tail-empty", [] => pure (.members [])
  | "json:member-tail-cons", [.unit, .unit, .member member, .members tail] =>
      pure (.members (member :: tail))
  | "json:member", [.string key, .unit, .unit, .value value] =>
      pure (.member { key, value, span := { start, stop } })
  | "json:array", [.unit, .values values, .unit] => pure (.array values)
  | "json:elements-none", [] => pure (.values [])
  | "json:elements-some", [.values values] => pure (.values values)
  | "json:elements", [.value value, .values tail] =>
      pure (.values (value :: tail))
  | "json:element-tail-empty", [] => pure (.values [])
  | "json:element-tail-cons", [.unit, .unit, .value value, .values tail] =>
      pure (.values (value :: tail))
  | "json:string", [.pieces pieces] =>
      pure (.string (← resolveStringPieces pieces))
  | "json:string-chars-empty", [] => pure (.pieces [])
  | "json:string-chars-cons", [.pieces head, .pieces tail] =>
      pure (.pieces (head ++ tail))
  | "json:string-char-plain", [.scalar scalar] =>
      pure (.pieces [.scalar scalar])
  | "json:string-char-escape", [.pieces escape] => pure (.pieces escape)
  | "json:escape-simple", [.scalar codepoint] =>
      match simpleEscape? codepoint with
      | some scalar => pure (.pieces [.scalar scalar])
      | none => throw .malformedCST
  | "json:escape-unicode", digits =>
      match unicodeUnit? digits with
      | some unit => pure (.pieces [.codeUnit unit])
      | none => throw .malformedCST
  | "json:number", [.numberText minus, .numberText integer,
      .numberText fraction, .numberText exponent] =>
      pure (.numberText (minus ++ integer ++ fraction ++ exponent))
  | "json:minus-none", [] => pure (.numberText [])
  | "json:minus-some", [] => pure (.numberText [45])
  | "json:int-zero", [] => pure (.numberText [48])
  | "json:int-nonzero", [.scalar head, .numberText tail] =>
      if 49 ≤ head && head ≤ 57 then
        pure (.numberText (head :: tail))
      else
        throw .malformedCST
  | "json:digits-empty", [] => pure (.numberText [])
  | "json:digits-cons", [.scalar head, .numberText tail] =>
      if 48 ≤ head && head ≤ 57 then
        pure (.numberText (head :: tail))
      else
        throw .malformedCST
  | "json:frac-none", [] => pure (.numberText [])
  | "json:frac-some", [.numberText fraction] =>
      pure (.numberText fraction)
  | "json:frac", [.scalar head, .numberText tail] =>
      if 48 ≤ head && head ≤ 57 then
        pure (.numberText (46 :: head :: tail))
      else
        throw .malformedCST
  | "json:exp-none", [] => pure (.numberText [])
  | "json:exp-some", [.numberText exponent] =>
      pure (.numberText exponent)
  | "json:exp", [.scalar mark, .numberText sign,
      .scalar head, .numberText tail] =>
      if (mark == 69 || mark == 101) && 48 ≤ head && head ≤ 57 then
        pure (.numberText (mark :: sign ++ head :: tail))
      else
        throw .malformedCST
  | "json:sign-none", [] => pure (.numberText [])
  | "json:sign-some", [.scalar sign] =>
      if sign == 43 || sign == 45 then
        pure (.numberText [sign])
      else
        throw .malformedCST
  | _, _ => throw .malformedCST

mutual
  private def elaborateTrees :
      List CST → Except ElaborationError (List Attribute)
    | [] => .ok []
    | tree :: trees => do
        pure ((← elaborateTree tree) :: (← elaborateTrees trees))

  private def elaborateTree : CST → Except ElaborationError Attribute
    | .terminal codepoints _start _stop => pure (.terminal codepoints)
    | .node label start stop children => do
        elaborateNode label start stop (← elaborateTrees children)
end

/-- Total, pure elaboration of one RFC 8259 document CST. -/
def elaborateRootCST (tree : CST) : ElaborationOutcome :=
  match elaborateTree tree with
  | .ok (.root value) => .value value
  | .ok _ => .malformedCST
  | .error .invalidUnicodeEscape => .invalidUnicodeEscape
  | .error .malformedCST => .malformedCST

/-- Elaborating a family is pointwise.  There is no state shared between
alternatives of a packed forest. -/
def elaborateBranches (trees : List CST) : List ElaborationOutcome :=
  trees.map elaborateRootCST

theorem elaborateBranches_append (left right : List CST) :
    elaborateBranches (left ++ right) =
      elaborateBranches left ++ elaborateBranches right := by
  simp [elaborateBranches]

/-- Adding other branches cannot alter an existing branch's outcome. -/
theorem elaborateBranches_branch_local
    (before after : List CST) (tree : CST) :
    ((elaborateBranches (before ++ tree :: after)).drop
        before.length).head? = some (elaborateRootCST tree) := by
  simp [elaborateBranches]

/-! ## Exact semantic-outcome fibres -/

abbrev ParserRootOccurrence
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) :=
  (tree : CST) × ParserPackRootDerives profile plan input tree

abbrev SourceRootOccurrence
    (literalScalars? : String → Option (List Nat))
    (profile : ParserProfileLayer) (rules : List CompiledRule)
    (input : List Nat) :=
  (tree : CST) ×
    SourcePlanRootDerives literalScalars? profile rules input tree

abbrev NativeRootOccurrence
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) :=
  (tree : CST) × NativePackedFibre view inventory.toTable profile plan
    view.codepoints plan.lexical.startSort 0 view.codepoints.length tree

abbrev ParserValueOutcomeFibre
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (outcome : ElaborationOutcome) :=
  { occurrence : ParserRootOccurrence profile plan input //
      elaborateRootCST occurrence.1 = outcome }

abbrev SourceValueOutcomeFibre
    (literalScalars? : String → Option (List Nat))
    (profile : ParserProfileLayer) (rules : List CompiledRule)
    (input : List Nat) (outcome : ElaborationOutcome) :=
  { occurrence :
      SourceRootOccurrence literalScalars? profile rules input //
      elaborateRootCST occurrence.1 = outcome }

abbrev NativeValueOutcomeFibre
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (outcome : ElaborationOutcome) :=
  { occurrence : NativeRootOccurrence view inventory profile plan //
      elaborateRootCST occurrence.1 = outcome }

/-- Complete native qualification preserves the whole parse-occurrence fibre
at every semantic value or rejection outcome. -/
noncomputable def ParserCompleteRepresentation.valueOutcomeEquiv
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {target : Forest}
    (qualification :
      ParserCompleteRepresentation view inventory profile plan target)
    (outcome : ElaborationOutcome) :
    ParserValueOutcomeFibre profile plan view.codepoints outcome ≃
      NativeValueOutcomeFibre view inventory profile plan outcome where
  toFun occurrence :=
    ⟨⟨occurrence.1.1,
      qualification.rootDerivationEquiv occurrence.1.1 occurrence.1.2⟩,
      occurrence.2⟩
  invFun occurrence :=
    ⟨⟨occurrence.1.1,
      (qualification.rootDerivationEquiv occurrence.1.1).symm
        occurrence.1.2⟩,
      occurrence.2⟩
  left_inv := by
    rintro ⟨⟨tree, derivation⟩, property⟩
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq
      ((qualification.rootDerivationEquiv tree).left_inv derivation))
  right_inv := by
    rintro ⟨⟨tree, occurrence⟩, property⟩
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq
      ((qualification.rootDerivationEquiv tree).right_inv occurrence))

/-- The authored source-plan occurrence fibre and the qualified native
forest occurrence fibre agree at every semantic value or rejection outcome.
This composition retains source rule occurrences, ParserPack production
occurrences, and packed alternatives rather than comparing only accepted
values. -/
noncomputable def ParserCompleteRepresentation.sourceValueOutcomeEquiv
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan} {view : ForestView}
    {inventory : Inventory} {target : Forest}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan)
    (qualification :
      ParserCompleteRepresentation view inventory profile plan target)
    (outcome : ElaborationOutcome) :
    SourceValueOutcomeFibre literalScalars? profile rules
        view.codepoints outcome ≃
      NativeValueOutcomeFibre view inventory profile plan outcome where
  toFun occurrence :=
    ⟨⟨occurrence.1.1,
      qualification.sourceRootDerivationEquiv agreement occurrence.1.1
        occurrence.1.2⟩,
      occurrence.2⟩
  invFun occurrence :=
    ⟨⟨occurrence.1.1,
      (qualification.sourceRootDerivationEquiv agreement
        occurrence.1.1).symm occurrence.1.2⟩,
      occurrence.2⟩
  left_inv := by
    rintro ⟨⟨tree, derivation⟩, property⟩
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq
      ((qualification.sourceRootDerivationEquiv agreement tree).left_inv
        derivation))
  right_inv := by
    rintro ⟨⟨tree, occurrence⟩, property⟩
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq
      ((qualification.sourceRootDerivationEquiv agreement tree).right_inv
        occurrence))

/-! ## Executable positive and negative controls -/

private def lexical (label : String) (codepoint start : Nat) : CST :=
  .node label start (start + 1)
    [.terminal [codepoint] start (start + 1)]

private def wsEmpty (cursor : Nat) : CST :=
  .node "json:ws-empty" cursor cursor []

private def nullValue (start stop : Nat) : CST :=
  .node "json:value-null" start stop []

private def textTree (value : CST) (stop : Nat) : CST :=
  .node "json:text" 0 stop [wsEmpty 0, value, wsEmpty stop]

private def duplicateObjectTree : CST :=
  let key := .node "json:string" 1 4
    [.node "json:string-chars-cons" 2 3
      [.node "json:string-char-plain" 2 3
        [lexical "json:lex-unescaped" 120 2],
       .node "json:string-chars-empty" 3 3 []]]
  let first := .node "json:member" 1 9
    [key, wsEmpty 4, wsEmpty 5, nullValue 5 9]
  let secondKey := .node "json:string" 10 13
    [.node "json:string-chars-cons" 11 12
      [.node "json:string-char-plain" 11 12
        [lexical "json:lex-unescaped" 120 11],
       .node "json:string-chars-empty" 12 12 []]]
  let second := .node "json:member" 10 18
    [secondKey, wsEmpty 13, wsEmpty 14, nullValue 14 18]
  let tail := .node "json:member-tail-cons" 9 18
    [wsEmpty 9, wsEmpty 10, second,
      .node "json:member-tail-empty" 18 18 []]
  let members := .node "json:members-some" 1 18
    [.node "json:members" 1 18 [first, tail]]
  textTree
    (.node "json:value-object" 0 19
      [.node "json:object" 0 19 [wsEmpty 1, members, wsEmpty 18]])
    19

theorem duplicate_members_retain_order_occurrence_and_span :
    elaborateRootCST duplicateObjectTree =
      .value (.object [
        { occurrence := 0, key := [120], value := .null,
          span := { start := 1, stop := 9 } },
        { occurrence := 1, key := [120], value := .null,
          span := { start := 10, stop := 18 } }]) := by
  rfl

private def exactNumberTree : CST :=
  let tailTwo := .node "json:digits-cons" 2 3
    [lexical "json:lex-digit" 50 2,
      .node "json:digits-empty" 3 3 []]
  let integer := .node "json:int-nonzero" 1 3
    [lexical "json:lex-digit19" 49 1, tailTwo]
  let fraction := .node "json:frac-some" 3 6
    [.node "json:frac" 3 6
      [lexical "json:lex-digit" 51 4,
        .node "json:digits-cons" 5 6
          [lexical "json:lex-digit" 48 5,
            .node "json:digits-empty" 6 6 []]]]
  let exponent := .node "json:exp-some" 6 9
    [.node "json:exp" 6 9
      [lexical "json:lex-exp-mark" 69 6,
       .node "json:sign-some" 7 8 [lexical "json:lex-sign" 43 7],
       lexical "json:lex-digit" 52 8,
       .node "json:digits-empty" 9 9 []]]
  let number := .node "json:number" 0 9
    [.node "json:minus-some" 0 1 [], integer, fraction, exponent]
  textTree (.node "json:value-number" 0 9 [number]) 9

theorem exact_number_lexeme_is_not_rounded_or_canonicalized :
    elaborateRootCST exactNumberTree =
      .value (.number [45, 49, 50, 46, 51, 48, 69, 43, 52]) := by
  rfl

private def unicodeEscape (digits : List Nat) (start : Nat) : CST :=
  .node "json:escape-unicode" start (start + 6)
    (digits.zipIdx.map fun entry =>
      lexical "json:lex-hexdigit" entry.1 (start + 2 + entry.2))

private def escapedStringTree (first second : List Nat) : CST :=
  let firstEscape := .node "json:string-char-escape" 1 7
    [unicodeEscape first 1]
  let secondEscape := .node "json:string-char-escape" 7 13
    [unicodeEscape second 7]
  let chars := .node "json:string-chars-cons" 1 13
    [firstEscape,
      .node "json:string-chars-cons" 7 13
        [secondEscape, .node "json:string-chars-empty" 13 13 []]]
  textTree (.node "json:value-string" 0 14
    [.node "json:string" 0 14 [chars]]) 14

theorem surrogate_pair_decodes_to_one_scalar :
    elaborateRootCST
      (escapedStringTree [68, 56, 51, 52] [68, 68, 49, 69]) =
      .value (.string [0x1d11e]) := by
  rfl

private def loneSurrogateTree : CST :=
  let escape := .node "json:string-char-escape" 1 7
    [unicodeEscape [68, 56, 48, 48] 1]
  let chars := .node "json:string-chars-cons" 1 7
    [escape, .node "json:string-chars-empty" 7 7 []]
  textTree (.node "json:value-string" 0 8
    [.node "json:string" 0 8 [chars]]) 8

theorem lone_surrogate_is_semantic_rejection :
    elaborateRootCST loneSurrogateTree = .invalidUnicodeEscape := by
  rfl

theorem malformed_root_is_not_silently_accepted :
    elaborateRootCST (.node "json:value-null" 0 4 []) = .malformedCST := by
  rfl

#print axioms ParserCompleteRepresentation.valueOutcomeEquiv
#print axioms ParserCompleteRepresentation.sourceValueOutcomeEquiv
#print axioms duplicate_members_retain_order_occurrence_and_span
#print axioms exact_number_lexeme_is_not_rounded_or_canonicalized
#print axioms surrogate_pair_decodes_to_one_scalar
#print axioms lone_surrogate_is_semantic_rejection

end Mettapedia.GSLT.LanguageDef.RFC8259ValueSemantics
