import Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
import Std.Data.String.ToNat

/-!
# Canonical source syntax for executable GSLTs

This module decodes the existing `gslt-presentation-v1` source schema into
typed data without choosing a runtime, proof-search strategy, or target
language.  It is the direct typed form of that source schema: operator,
equation, and rewrite occurrences retain their authored order and
multiplicity, while malformed or non-canonical field shapes fail closed.

Source terms use the existing reader's S-expression carrier.  Atoms and
singleton lists remain distinct, including inside rule heads and bodies.
The leading `?` convention remains source syntax; conversion to semantic
metavariables belongs to the separate operational elaboration.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT

open Algorithms.MeTTa.Simple.Parser (SExpr)

variable {alpha : Type}

/-- One authored operator occurrence in a canonical GSLT signature. -/
structure Operator where
  name : String
  arity : Nat
deriving Repr, DecidableEq

/-- One authored directed rule.  `body` is the ordered premise list stored in
the source `(body ...)` form. -/
structure Rewrite where
  name : String
  head : SExpr
  body : List SExpr
deriving Repr, DecidableEq

/-- The exact structured contents of one canonical executable GSLT source. -/
structure Source where
  name : String
  operators : List Operator
  equations : List SExpr
  rewrites : List Rewrite
deriving Repr, DecidableEq

/-- Quoted strings and integers retain their token spelling.  A singleton
list is never accepted where the source schema requires an atom. -/
def atomToken? : SExpr -> Option String
  | .atom token => some token
  | _ => none

def encodeAtomToken (token : String) : SExpr :=
  .atom token

@[simp] theorem atomToken?_encodeAtomToken (token : String) :
    atomToken? (encodeAtomToken token) = some token :=
  rfl

def decodeOperator : SExpr -> Option Operator
  | .list [.atom "operator", nameSyntax, aritySyntax] => do
      let name <- atomToken? nameSyntax
      let arityToken <- atomToken? aritySyntax
      let arity <- arityToken.toNat?
      some { name, arity }
  | _ => none

def encodeOperator (operator : Operator) : SExpr :=
  .list [.atom "operator", encodeAtomToken operator.name,
    encodeAtomToken (toString operator.arity)]

@[simp] theorem decodeOperator_encodeOperator (operator : Operator) :
    decodeOperator (encodeOperator operator) = some operator := by
  cases operator with
  | mk name arity =>
      simp [decodeOperator, encodeOperator, Nat.toNat?_repr]

def decodeRewrite : SExpr -> Option Rewrite
  | .list [.atom "rule", nameSyntax, .list [.atom "head", head],
      .list (.atom "body" :: body)] => do
      let name <- atomToken? nameSyntax
      some { name, head, body }
  | _ => none

def encodeRewrite (rewrite : Rewrite) : SExpr :=
  .list [.atom "rule", encodeAtomToken rewrite.name,
    .list [.atom "head", rewrite.head], .list (.atom "body" :: rewrite.body)]

@[simp] theorem decodeRewrite_encodeRewrite (rewrite : Rewrite) :
    decodeRewrite (encodeRewrite rewrite) = some rewrite := by
  cases rewrite
  rfl

def decodeList (decode : SExpr -> Option alpha) :
    List SExpr -> Option (List alpha)
  | [] => some []
  | item :: items => do
      let head <- decode item
      let tail <- decodeList decode items
      some (head :: tail)

theorem decodeList_getElem? (decoder : SExpr → Option alpha)
    {items : List SExpr} {values : List alpha}
    (accepted : decodeList decoder items = some values) (index : Nat) :
    values[index]? = (items[index]?).bind decoder := by
  induction items generalizing values index with
  | nil =>
    simp [decodeList] at accepted
    subst values
    simp
  | cons item items ih =>
    cases first : decoder item with
    | none => simp [decodeList, first] at accepted
    | some value =>
      cases rest : decodeList decoder items with
      | none => simp [decodeList, first, rest] at accepted
      | some tail =>
        have same : value :: tail = values := by simpa [decodeList, first, rest] using accepted
        subst values
        cases index with
        | zero => simp [first]
        | succ index => exact ih rest index

theorem decodeList_map_encode (decode : SExpr -> Option alpha)
    (encode : alpha -> SExpr)
    (roundTrip : forall value, decode (encode value) = some value)
    (values : List alpha) :
    decodeList decode (values.map encode) = some values := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp [decodeList, roundTrip, inductionHypothesis]

/-- Decode the canonical field order emitted and consumed by the current
native GSLT toolchain.  Unknown, repeated, reordered, or malformed fields are
rejected rather than normalized into a different source artifact. -/
def decode : SExpr -> Option Source
  | .list [.atom "gslt-presentation-v1", nameSyntax,
      .list (.atom "signature" :: operatorSyntax),
      .list (.atom "equations" :: equations),
      .list (.atom "rewrites" :: rewriteSyntax)] => do
      let name <- atomToken? nameSyntax
      let operators <- decodeList decodeOperator operatorSyntax
      let rewrites <- decodeList decodeRewrite rewriteSyntax
      some { name, operators, equations, rewrites }
  | _ => none

/-- Projection only: this does not admit a source. The theorem below requires
the complete decoder's acceptance, including the signature. -/
def rawRewriteAt? : SExpr → Nat → Option Rewrite
  | .list [.atom "gslt-presentation-v1", _,
      .list (.atom "signature" :: _), .list (.atom "equations" :: _),
      .list (.atom "rewrites" :: rows)], index =>
      (rows[index]?).bind decodeRewrite
  | _, _ => none

theorem rawRewriteAt?_of_decode {raw : SExpr} {source : Source}
    (accepted : decode raw = some source) (index : Nat) :
    source.rewrites[index]? = rawRewriteAt? raw index := by
  unfold decode at accepted
  split at accepted
  next nameSyntax operatorSyntax equations rewriteSyntax =>
    cases name : atomToken? nameSyntax with
    | none => simp [name] at accepted
    | some nameValue =>
      cases operators : decodeList decodeOperator operatorSyntax with
      | none => simp [name, operators] at accepted
      | some operatorValues =>
        cases rewrites : decodeList decodeRewrite rewriteSyntax with
        | none => simp [name, operators, rewrites] at accepted
        | some rewriteValues =>
          have same : Source.mk nameValue operatorValues equations rewriteValues = source := by
            simpa [name, operators, rewrites] using accepted
          subst source
          exact decodeList_getElem? decodeRewrite rewrites index
  next => simp at accepted

def encode (source : Source) : SExpr :=
  .list [.atom "gslt-presentation-v1", encodeAtomToken source.name,
    .list (.atom "signature" :: source.operators.map encodeOperator),
    .list (.atom "equations" :: source.equations),
    .list (.atom "rewrites" :: source.rewrites.map encodeRewrite)]

/-- Every typed source value has an exact canonical source representation. -/
@[simp] theorem decode_encode (source : Source) :
    decode (encode source) = some source := by
  cases source
  simp [decode, encode, decodeList_map_encode]

/-- Canonical source encodings are collision-free.  Thus no two distinct
typed rule inventories can be hidden behind the same source pattern. -/
theorem encode_injective : Function.Injective encode := by
  intro left right equality
  have decoded := congrArg decode equality
  simpa using decoded

/-- Being canonical means being exactly the encoding of typed GSLT source
data, rather than merely satisfying a collection of shallow shape tests. -/
def Canonical (raw : SExpr) : Prop :=
  exists source, raw = encode source

/-- On canonical inputs, a successful decode re-encodes to the exact input. -/
theorem encode_eq_of_canonical_decode {raw : SExpr} {source : Source}
    (canonical : Canonical raw) (decoded : decode raw = some source) :
    encode source = raw := by
  obtain ⟨original, rfl⟩ := canonical
  rw [decode_encode] at decoded
  cases decoded
  rfl

def operatorKey (operator : Operator) : String × Nat :=
  (operator.name, operator.arity)

def rewriteName (rewrite : Rewrite) : String :=
  rewrite.name

def hasOperator (operators : List Operator) (name : String) (arity : Nat) : Bool :=
  operators.any fun operator =>
    operator.name == name && operator.arity == arity

mutual

  /-- Every application, including arity zero, requires a declared operator.
  Literal atoms do not acquire call semantics from the operator table. -/
  def termSupported (operators : List Operator) : SExpr -> Bool
    | .atom token => token != "?" && token != "?_"
    | .list (.atom head :: arguments) =>
        hasOperator operators head arguments.length &&
          termsSupported operators arguments
    | _ => false
  termination_by term => sizeOf term

  def termsSupported (operators : List Operator) : List SExpr -> Bool
    | [] => true
    | term :: terms =>
        termSupported operators term && termsSupported operators terms
  termination_by terms => sizeOf terms

end

def Rewrite.hasValidShape (rewrite : Rewrite) : Bool :=
  !rewrite.name.isEmpty &&
    match rewrite.head with
    | .list (.atom _ :: _) => true
    | _ => false

/-- Fail-closed schema validity for one open source component.  References to
operators supplied by other components are deliberately not resolved here. -/
def Source.hasValidSchema (source : Source) : Bool :=
  !source.name.isEmpty &&
    (source.operators.all fun operator => !operator.name.isEmpty) &&
    source.rewrites.all Rewrite.hasValidShape

/-- Validate the operator references of one source against the complete,
occurrence-preserving signature of its composition. -/
def Source.termsValidIn (operators : List Operator) (source : Source) : Bool :=
  source.equations.all (termSupported operators) &&
    source.rewrites.all fun rewrite =>
      termSupported operators rewrite.head &&
        termsSupported operators rewrite.body

def compositionOperators (sources : List Source) : List Operator :=
  sources.flatMap Source.operators

def compositionRewriteNames (sources : List Source) : List String :=
  sources.flatMap fun source => source.rewrites.map rewriteName

/-- Closed composition validity.  Source and rule identities are globally
unique; operator occurrences remain ordered and are never deduplicated. -/
def compositionValid (sources : List Source) : Bool :=
  !sources.isEmpty &&
    (sources.map Source.name).Nodup &&
    (compositionRewriteNames sources).Nodup &&
    sources.all Source.hasValidSchema &&
    let operators := compositionOperators sources
    sources.all (Source.termsValidIn operators)

/-! ## Positive and negative controls -/

private def smallRewrite : Rewrite :=
  { name := "edge-reflexive"
    head := .list [.atom "edge", .atom "?x", .atom "?x"]
    body := [] }

private def smallSource : Source :=
  { name := "SmallSource"
    operators := [{ name := "edge", arity := 2 }]
    equations := []
    rewrites := [smallRewrite] }

theorem small_source_round_trip :
    decode (encode smallSource) = some smallSource := by
  exact decode_encode smallSource

theorem small_source_is_valid : compositionValid [smallSource] = true := by
  simp [compositionValid, Source.hasValidSchema, Source.termsValidIn,
    compositionOperators, compositionRewriteNames, smallSource, smallRewrite,
    rewriteName, Rewrite.hasValidShape, termSupported, termsSupported,
    hasOperator]

private def duplicateRuleSource : Source :=
  { smallSource with rewrites := [smallRewrite, smallRewrite] }

/-- Negative: equal-looking rule occurrences are retained by the codec but
source admission refuses ambiguous rule identities. -/
theorem duplicate_rule_names_are_refused :
    compositionValid [duplicateRuleSource] = false := by
  simp [compositionValid, compositionRewriteNames, duplicateRuleSource,
    smallSource, smallRewrite, rewriteName]

/-- Negative: an undeclared positive-arity application is not reinterpreted
as an opaque source atom. -/
theorem undeclared_application_is_refused :
    termSupported smallSource.operators
      (.list [.atom "missing", .atom "x"]) = false := by
  simp [termSupported, termsSupported, hasOperator, smallSource]

theorem undeclared_nullary_application_is_refused :
    termSupported smallSource.operators (.list [.atom "missing"]) = false := by
  simp [termSupported, termsSupported, hasOperator, smallSource]

theorem schema_atom_rejects_singleton_list (token : String) :
    atomToken? (.list [.atom token]) = none := rfl

theorem declared_nullary_application_is_supported :
    termSupported [{ name := "unit", arity := 0 }]
      (.list [.atom "unit"]) = true := by
  simp [termSupported, termsSupported, hasOperator]

#print axioms decodeOperator_encodeOperator
#print axioms decodeRewrite_encodeRewrite
#print axioms decode_encode
#print axioms encode_injective
#print axioms encode_eq_of_canonical_decode
#print axioms small_source_round_trip
#print axioms small_source_is_valid
#print axioms duplicate_rule_names_are_refused
#print axioms undeclared_application_is_refused
#print axioms undeclared_nullary_application_is_refused
#print axioms declared_nullary_application_is_supported

end Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
