import Algorithms.MeTTa.Simple.Parser
import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Lossless source S-expression data in the existing Pattern carrier

This codec embeds the existing source `SExpr` into the existing operational
`Pattern`. Separate atom/list tags retain nullary lists, child order and
duplicate occurrences. An atom's exact string is a nullary payload constructor;
it is never a pattern variable, even if its text starts with `?` or `$`.

These are ground data codecs, not source-rule elaboration or an evaluator.
The inverse rejects every Pattern outside the encoded image.
-/

namespace Mettapedia.GSLT.Parsing.SourceSExprPatternCodec

open Algorithms.MeTTa.Simple.Parser
open Mettapedia.OSLF.MeTTaIL.Syntax

mutual
  /-- Inject source data without interpreting source variable spellings. -/
  def encode : SExpr → Pattern
    | .atom value => .apply "source-sexpr-atom-v1" [.apply value []]
    | .list values => .apply "source-sexpr-list-v1" (encodeList values)

  /-- Preserve the ordered occurrence list directly. -/
  def encodeList : List SExpr → List Pattern
    | [] => []
    | value :: values => encode value :: encodeList values
end

mutual
  /-- Decode only the tagged ground-data image, with no normalization. -/
  def decode : Pattern → Option SExpr
    | .apply "source-sexpr-atom-v1" [.apply value []] => some (.atom value)
    | .apply "source-sexpr-list-v1" values => .list <$> decodeList values
    | _ => none

  def decodeList : List Pattern → Option (List SExpr)
    | [] => some []
    | value :: values => do
        return (← decode value) :: (← decodeList values)
end

mutual
  @[simp] theorem decode_encode (value : SExpr) :
      decode (encode value) = some value := by
    cases value with
    | atom value => rfl
    | list values =>
        change SExpr.list <$> decodeList (encodeList values) = _
        rw [decodeList_encodeList values]
        rfl
  termination_by sizeOf value

  @[simp] theorem decodeList_encodeList (values : List SExpr) :
      decodeList (encodeList values) = some values := by
    cases values with
    | nil => rfl
    | cons value values =>
        change (do return (← decode (encode value)) ::
          (← decodeList (encodeList values))) = _
        rw [decode_encode value, decodeList_encodeList values]
        rfl
  termination_by sizeOf values
end

theorem encode_injective : Function.Injective encode := by
  intro left right equal
  have := congrArg decode equal
  simpa only [decode_encode, Option.some.injEq] using this

theorem encodeList_injective : Function.Injective encodeList := by
  intro left right equal
  have := congrArg decodeList equal
  simpa only [decodeList_encodeList, Option.some.injEq] using this

mutual
  /-- Every accepted target is the exact canonical encoding, not an alias. -/
  theorem encode_of_decode {pattern : Pattern} {value : SExpr}
      (accepted : decode pattern = some value) : encode value = pattern := by
    cases patternEquation : pattern with
    | apply name arguments =>
        rw [patternEquation] at accepted
        unfold decode at accepted
        split at accepted
        next _ atom matched =>
          cases accepted
          exact matched.symm
        next _ values matched =>
          have smaller : sizeOf values < sizeOf pattern := by
            rw [patternEquation, matched]
            simp only [Pattern.apply.sizeOf_spec]
            omega
          cases result : decodeList values with
          | none => simp [result] at accepted
          | some decoded =>
              rw [result] at accepted
              change some (SExpr.list decoded) = some value at accepted
              cases accepted
              exact (congrArg (Pattern.apply "source-sexpr-list-v1")
                (encodeList_of_decodeList result)).trans matched.symm
        next => contradiction
    | bvar _ => simp [patternEquation, decode] at accepted
    | fvar _ => simp [patternEquation, decode] at accepted
    | lambda _ _ => simp [patternEquation, decode] at accepted
    | multiLambda _ _ _ => simp [patternEquation, decode] at accepted
    | subst _ _ => simp [patternEquation, decode] at accepted
    | collection _ _ _ => simp [patternEquation, decode] at accepted
  termination_by sizeOf pattern
  decreasing_by all_goals assumption

  theorem encodeList_of_decodeList {patterns : List Pattern} {values : List SExpr}
      (accepted : decodeList patterns = some values) : encodeList values = patterns := by
    cases patterns with
    | nil =>
        cases accepted
        rfl
    | cons pattern patterns =>
        cases head : decode pattern with
        | none => simp [decodeList, head] at accepted
        | some value =>
            cases tail : decodeList patterns with
            | none => simp [decodeList, head, tail] at accepted
            | some rest =>
                simp only [decodeList, head, tail, bind, Option.bind, pure,
                  Option.some.injEq] at accepted
                cases accepted
                exact congrArg₂ List.cons (encode_of_decode head)
                  (encodeList_of_decodeList tail)
  termination_by sizeOf patterns
end

theorem decode_eq_some_iff (pattern : Pattern) (value : SExpr) :
    decode pattern = some value ↔ encode value = pattern := by
  constructor
  · exact encode_of_decode
  · intro equal
    rw [← equal, decode_encode]

mutual
  theorem encode_isGroundAt (value : SExpr) (depth : Nat) :
      (encode value).isGroundAt depth = true := by
    cases value with
    | atom value => rfl
    | list values => exact encodeList_isGroundAt values depth
  termination_by sizeOf value

  theorem encodeList_isGroundAt (values : List SExpr) (depth : Nat) :
      Pattern.isGroundListAt depth (encodeList values) = true := by
    cases values with
    | nil => rfl
    | cons value values =>
        change ((encode value).isGroundAt depth &&
          Pattern.isGroundListAt depth (encodeList values)) = true
        rw [encode_isGroundAt value depth, encodeList_isGroundAt values depth]
        rfl
  termination_by sizeOf values
end

theorem encode_isGround (value : SExpr) : (encode value).isGround = true :=
  encode_isGroundAt value 0

theorem atom_and_nullary_call_distinct (name : String) :
    encode (.atom name) ≠ encode (.list [.atom name]) := by
  intro equal
  have := encode_injective equal
  cases this

theorem list_order_preserved (left right : SExpr) (distinct : left ≠ right) :
    encode (.list [left, right]) ≠ encode (.list [right, left]) := by
  intro equal
  have := encode_injective equal
  cases SExpr.list.inj this
  exact distinct rfl

theorem duplicate_occurrences_preserved (value : SExpr) :
    encode (.list [value, value]) ≠ encode (.list [value]) := by
  intro equal
  have := encode_injective equal
  cases this

theorem variable_spelling_remains_ground_data :
    decode (encode (.list [.atom "?name", .atom "$name"])) =
      some (.list [.atom "?name", .atom "$name"]) ∧
    (encode (.list [.atom "?name", .atom "$name"])).isGround = true :=
  ⟨decode_encode _, encode_isGround _⟩

theorem empty_list_roundtrip : decode (encode (.list [])) = some (.list []) := rfl

theorem malformed_atom_arity_rejected :
    decode (.apply "source-sexpr-atom-v1" []) = none := rfl

theorem malformed_atom_payload_rejected (name : String) :
    decode (.apply "source-sexpr-atom-v1" [.fvar name]) = none := rfl

theorem malformed_list_child_rejected (name : String) :
    decode (.apply "source-sexpr-list-v1" [.fvar name]) = none := rfl

theorem untagged_nullary_rejected : decode (.apply "a" []) = none := rfl

theorem pattern_variables_rejected (name : String) (index : Nat) :
    decode (.fvar name) = none ∧ decode (.bvar index) = none := ⟨rfl, rfl⟩

#print axioms decode_encode
#print axioms encode_of_decode
#print axioms encode_injective
#print axioms encode_isGround
#print axioms duplicate_occurrences_preserved

end Mettapedia.GSLT.Parsing.SourceSExprPatternCodec
