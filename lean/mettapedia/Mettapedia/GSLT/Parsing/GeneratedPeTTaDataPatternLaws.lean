import Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern

/-!
# Exact checking of emitted structural data patterns

The laws cover arbitrary finite S-expression trees, constructor arities and
leaf spellings. Successful checking establishes the whole canonical emitted
pattern, rather than matching names or a digest. These are syntax and evidence
laws; execution correspondence is a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern

open Algorithms.MeTTa.Simple.Parser (SExpr)

mutual
  @[simp] theorem decode_encode (template : SExpr) :
      decode (encode template) = some template := by
    cases template with
    | atom token => simp only [encode, decode]
    | list values => exact decode_encodeList values
  termination_by sizeOf template

  @[simp] theorem decode_encodeList (values : List SExpr) :
      decode (encodeList values) = some (.list values) := by
    cases values with
    | nil => simp only [encodeList, decode]
    | cons first rest =>
        simp only [encodeList, decode, decode_encode first, decode_encodeList rest]
        rfl
  termination_by sizeOf values
end

theorem encode_injective : Function.Injective encode := by
  intro first second equal
  have read := congrArg decode equal
  simpa only [decode_encode, Option.some.injEq] using read

theorem encodeList_injective : Function.Injective encodeList := by
  intro first second equal
  have read := congrArg decode equal
  simpa only [decode_encodeList, Option.some.injEq, SExpr.list.injEq] using read

/-- Every accepted tree is the canonical structural pattern of its value. -/
theorem encode_of_decode (emitted template : SExpr)
    (accepted : decode emitted = some template) : encode template = emitted := by
  induction emitted using decode.induct generalizing template with
  | case1 token =>
      rw [decode.eq_1] at accepted
      cases accepted
      rfl
  | case2 =>
      rw [decode.eq_2] at accepted
      cases accepted
      rfl
  | case3 first rest firstIH restIH =>
      rw [decode.eq_3] at accepted
      cases firstRead : decode first with
      | none =>
          rw [firstRead] at accepted
          cases accepted
      | some firstValue =>
          rw [firstRead] at accepted
          cases restRead : decode rest with
          | none =>
              rw [restRead] at accepted
              cases accepted
          | some restValue =>
              rw [restRead] at accepted
              cases restValue with
              | atom token => cases accepted
              | list tail =>
                  have same : SExpr.list (firstValue :: tail) = template := Option.some.inj accepted
                  subst template
                  have firstExact := firstIH firstValue firstRead
                  have restExact := restIH (.list tail) restRead
                  change encodeList tail = rest at restExact
                  change SExpr.list [.atom "cons-atom", encode firstValue, encodeList tail] = _
                  rw [firstExact, restExact]
  | case4 other noAtom noEmpty noCons =>
      rw [decode.eq_4 other noAtom noEmpty noCons] at accepted
      cases accepted

theorem decode_eq_some_iff (emitted template : SExpr) :
    decode emitted = some template ↔ emitted = encode template := by
  constructor
  · exact fun accepted => (encode_of_decode emitted template accepted).symm
  · intro equal
    simpa only [equal] using decode_encode template

theorem check_iff (template emitted : SExpr) :
    check template emitted = true ↔ emitted = encode template := by
  simp only [check, decide_eq_true_eq, decode_eq_some_iff]

@[simp] theorem check_encode (template : SExpr) : check template (encode template) = true :=
  (check_iff template (encode template)).2 rfl

theorem atom_and_nullary_are_distinct (name : String) :
    encode (.atom name) ≠ encode (.list [.atom name]) := by
  intro equal
  have source := encode_injective equal
  cases source

theorem arity_preserved (first second : List SExpr)
    (equal : encodeList first = encodeList second) : first.length = second.length :=
  congrArg List.length (encodeList_injective equal)

theorem malformed_tail_refused (first : SExpr) (tail : String) :
    decode (.list [.atom "cons-atom", first, .atom tail]) = none := by
  simp only [decode]
  cases decode first <;> rfl

example :
    check (.list [.atom "cons", .atom "$head", .atom "$tail"])
      (.list [.atom "cons-atom", .atom "cons",
        .list [.atom "cons-atom", .atom "$head",
          .list [.atom "cons-atom", .atom "$tail", .list []]]]) = true := by
  simpa only [encode, encodeList] using
    check_encode (.list [.atom "cons", .atom "$head", .atom "$tail"])

example :
    check (.list [.atom "cons", .atom "$head", .atom "$tail"])
      (.list [.atom "cons", .atom "$head", .atom "$tail"]) = false := by
  simp [check, decode]

#print axioms encode_of_decode
#print axioms check_iff

end Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern
