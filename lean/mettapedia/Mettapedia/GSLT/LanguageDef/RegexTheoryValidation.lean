import Mettapedia.GSLT.LanguageDef.RegexTheory
import Mettapedia.GSLT.LanguageDef.CarrierWellSorted

/-!
# Admission of the authored regex constructor presentation

The fixed declarations pass the existing LanguageDef validator. Native
string letters are checked through the declared Scalar carrier, while regex
and word structure uses the authored constructor rows. This admits structured
input values; it is not a regex-text parser.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexTheory

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Computability.RegularLanguages
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext isObjectPattern isObjectPatternList)
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted

private theorem term_rows_valid :
    ∀ term ∈ theory.terms, LanguageDef.validateTerm theory term = [] := by
  intro term member
  have checked : theory.terms.all (fun term =>
      (LanguageDef.validateTerm theory term).isEmpty) = true := by decide +kernel
  have valid := List.all_eq_true.mp checked term member
  exact List.isEmpty_iff.mp valid

private theorem valid_orFF :
    LanguageDef.validateRewrite theory orFF = [] := by cbv

private theorem valid_orFT :
    LanguageDef.validateRewrite theory orFT = [] := by cbv

private theorem valid_orTF :
    LanguageDef.validateRewrite theory orTF = [] := by cbv

private theorem valid_orTT :
    LanguageDef.validateRewrite theory orTT = [] := by cbv

private theorem valid_andFF :
    LanguageDef.validateRewrite theory andFF = [] := by cbv

private theorem valid_andFT :
    LanguageDef.validateRewrite theory andFT = [] := by cbv

private theorem valid_andTF :
    LanguageDef.validateRewrite theory andTF = [] := by cbv

private theorem valid_andTT :
    LanguageDef.validateRewrite theory andTT = [] := by cbv

private theorem valid_nullableZero :
    LanguageDef.validateRewrite theory nullableZero = [] := by cbv

private theorem valid_nullableEpsilon :
    LanguageDef.validateRewrite theory nullableEpsilon = [] := by cbv

private theorem valid_nullableLiteral :
    LanguageDef.validateRewrite theory nullableLiteral = [] := by cbv

private theorem valid_nullableAny :
    LanguageDef.validateRewrite theory nullableAny = [] := by cbv

private theorem valid_nullableUnion :
    LanguageDef.validateRewrite theory nullableUnion = [] := by cbv

private theorem valid_nullableConcat :
    LanguageDef.validateRewrite theory nullableConcat = [] := by cbv

private theorem valid_nullableStar :
    LanguageDef.validateRewrite theory nullableStar = [] := by cbv

private theorem valid_derivativeZero :
    LanguageDef.validateRewrite theory derivativeZero = [] := by cbv

private theorem valid_derivativeEpsilon :
    LanguageDef.validateRewrite theory derivativeEpsilon = [] := by cbv

private theorem valid_derivativeLiteralEq :
    LanguageDef.validateRewrite theory derivativeLiteralEq = [] := by cbv

private theorem valid_derivativeLiteralNe :
    LanguageDef.validateRewrite theory derivativeLiteralNe = [] := by cbv

private theorem valid_derivativeAny :
    LanguageDef.validateRewrite theory derivativeAny = [] := by cbv

private theorem valid_derivativeUnion :
    LanguageDef.validateRewrite theory derivativeUnion = [] := by cbv

private theorem valid_derivativeConcatNullable :
    LanguageDef.validateRewrite theory derivativeConcatNullable = [] := by cbv

private theorem valid_derivativeConcatNonnullable :
    LanguageDef.validateRewrite theory derivativeConcatNonnullable = [] := by cbv

private theorem valid_derivativeStar :
    LanguageDef.validateRewrite theory derivativeStar = [] := by cbv

private theorem valid_matchNil :
    LanguageDef.validateRewrite theory matchNil = [] := by cbv

private theorem valid_matchCons :
    LanguageDef.validateRewrite theory matchCons = [] := by cbv

private theorem rewrite_rows_valid :
    ∀ selected ∈ theory.rewrites, LanguageDef.validateRewrite theory selected = [] := by
  intro selected member
  simp only [theory, rewrites, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid_orFF
  · exact valid_orFT
  · exact valid_orTF
  · exact valid_orTT
  · exact valid_andFF
  · exact valid_andFT
  · exact valid_andTF
  · exact valid_andTT
  · exact valid_nullableZero
  · exact valid_nullableEpsilon
  · exact valid_nullableLiteral
  · exact valid_nullableAny
  · exact valid_nullableUnion
  · exact valid_nullableConcat
  · exact valid_nullableStar
  · exact valid_derivativeZero
  · exact valid_derivativeEpsilon
  · exact valid_derivativeLiteralEq
  · exact valid_derivativeLiteralNe
  · exact valid_derivativeAny
  · exact valid_derivativeUnion
  · exact valid_derivativeConcatNullable
  · exact valid_derivativeConcatNonnullable
  · exact valid_derivativeStar
  · exact valid_matchNil
  · exact valid_matchCons

theorem theory_valid : theory.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact term_rows_valid
  · intro equation member
    cases member
  · exact rewrite_rows_valid

private theorem terms_notBare (row : GrammarRule) (member : row ∈ theory.terms) :
    ¬ WellSorted.UsesBareCollection row := by
  have checked : theory.terms.all
      (fun row => !WellSorted.usesBareCollection? row) = true := by decide +kernel
  have noBare := List.all_eq_true.mp checked row member
  intro bare
  have yes := (WellSorted.usesBareCollection?_eq_true_iff row).mpr bare
  simp only [yes, Bool.not_true, Bool.false_eq_true] at noBare

theorem scalar_hasType (value : String) (free : FreeTypeContext) (bound : List TypeExpr) :
    HasType theory free bound (scalar value) (.base "Scalar") := by
  apply HasType.builtinAtom
  exact ⟨{ name := "Scalar", carrier := .builtinString }, List.Mem.head _, rfl, rfl⟩

theorem encode_hasType (p : Regex String) (free : FreeTypeContext) (bound : List TypeExpr) :
    HasType theory free bound (encode p) (.base "Regex") := by
  induction p with
  | zero =>
      exact .constructor (rule := theory.terms[0]) (List.getElem_mem _) (terms_notBare _ (List.getElem_mem _)) .nil
  | epsilon =>
      exact .constructor (rule := theory.terms[1]) (List.getElem_mem _) (terms_notBare _ (List.getElem_mem _)) .nil
  | char atom =>
      cases atom with
      | literal value =>
          exact .constructor (rule := theory.terms[2]) (List.getElem_mem _) (terms_notBare _ (List.getElem_mem _))
            (.cons trivial rfl (scalar_hasType value free bound) .nil)
      | any =>
          exact .constructor (rule := theory.terms[3]) (List.getElem_mem _) (terms_notBare _ (List.getElem_mem _)) .nil
  | plus p q hp hq =>
      exact .constructor (rule := theory.terms[4]) (List.getElem_mem _) (terms_notBare _ (List.getElem_mem _))
        (.cons trivial rfl hp (.cons trivial rfl hq .nil))
  | comp p q hp hq =>
      exact .constructor (rule := theory.terms[5]) (List.getElem_mem _) (terms_notBare _ (List.getElem_mem _))
        (.cons trivial rfl hp (.cons trivial rfl hq .nil))
  | star p hp =>
      exact .constructor (rule := theory.terms[6]) (List.getElem_mem _) (terms_notBare _ (List.getElem_mem _))
        (.cons trivial rfl hp .nil)

theorem word_hasType (input : List String) (free : FreeTypeContext) (bound : List TypeExpr) :
    HasType theory free bound (word input) (.base "Word") := by
  induction input with
  | nil =>
      exact .constructor (rule := theory.terms[9]) (List.getElem_mem _) (terms_notBare _ (List.getElem_mem _)) .nil
  | cons a rest ih =>
      exact .constructor (rule := theory.terms[10]) (List.getElem_mem _) (terms_notBare _ (List.getElem_mem _))
        (.cons trivial rfl (scalar_hasType a free bound) (.cons trivial rfl ih .nil))

theorem boolean_hasType (value : Bool) (free : FreeTypeContext) (bound : List TypeExpr) :
    HasType theory free bound (boolean value) (.base "Bool") := by
  cases value with
  | false => exact .constructor (rule := theory.terms[7]) (List.getElem_mem _) (terms_notBare _ (List.getElem_mem _)) .nil
  | true => exact .constructor (rule := theory.terms[8]) (List.getElem_mem _) (terms_notBare _ (List.getElem_mem _)) .nil


theorem encode_isObjectPattern (p : Regex String) : isObjectPattern (encode p) = true := by
  induction p with
  | zero => rfl
  | epsilon => rfl
  | char atom => cases atom <;> rfl
  | plus p q hp hq => simp only [encode, isObjectPattern, isObjectPatternList, hp, hq, Bool.and_true]
  | comp p q hp hq => simp only [encode, isObjectPattern, isObjectPatternList, hp, hq, Bool.and_true]
  | star p hp => simp only [encode, isObjectPattern, isObjectPatternList, hp, Bool.and_true]

theorem word_isObjectPattern (input : List String) : isObjectPattern (word input) = true := by
  induction input with
  | nil => rfl
  | cons a rest ih =>
      simp only [word, scalar, isObjectPattern, isObjectPatternList, ih, Bool.and_true]

/-- The executable admission checker accepts every encoded regex value. -/
theorem check_encode (p : Regex String) (free : FreeTypeContext) (bound : List TypeExpr) :
    checkHasType theory free bound (encode p) (.base "Regex") = true :=
  (checkHasType_eq_true_iff (encode_isObjectPattern p)).mpr (encode_hasType p free bound)

theorem check_word (input : List String) (free : FreeTypeContext) (bound : List TypeExpr) :
    checkHasType theory free bound (word input) (.base "Word") = true :=
  (checkHasType_eq_true_iff (word_isObjectPattern input)).mpr (word_hasType input free bound)

/-- Letters remain data; an undeclared atomic spelling is not a regex constructor. -/
theorem native_letter_not_regex :
    checkHasType theory FreeTypeContext.empty [] (scalar "é") (.base "Regex") = false := by cbv

/-- An unresolved capture is not a scalar value admitted in a closed literal. -/
theorem unresolved_literal_rejected :
    checkHasType theory FreeTypeContext.empty []
      (.apply "rx:literal" [.fvar "a"]) (.base "Regex") = false := by cbv

theorem wrong_union_arity_rejected :
    checkHasType theory FreeTypeContext.empty []
      (.apply "rx:union" [encode any]) (.base "Regex") = false := by cbv


/-- The authored matching request is admitted with its encoded input values. -/
theorem matchRequest_hasType (p : Regex String) (input : List String)
    (free : FreeTypeContext) (bound : List TypeExpr) :
    HasType theory free bound (matchRequest (encode p) (word input)) (.base "Bool") :=
  .constructor (rule := theory.terms[13]) (List.getElem_mem _)
    (terms_notBare _ (List.getElem_mem _))
    (.cons trivial rfl (encode_hasType p free bound)
      (.cons trivial rfl (word_hasType input free bound) .nil))

theorem check_matchRequest (p : Regex String) (input : List String)
    (free : FreeTypeContext) (bound : List TypeExpr) :
    checkHasType theory free bound (matchRequest (encode p) (word input)) (.base "Bool") = true := by
  apply (checkHasType_eq_true_iff ?_).mpr (matchRequest_hasType p input free bound)
  simp only [matchRequest, isObjectPattern, isObjectPatternList, encode_isObjectPattern,
    word_isObjectPattern, Bool.and_true]

end Mettapedia.GSLT.LanguageDef.RegexTheory
