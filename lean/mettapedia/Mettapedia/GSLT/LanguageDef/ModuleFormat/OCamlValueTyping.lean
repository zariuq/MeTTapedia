import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEncodingTyping

/-! All compact source values, including closure environments, inhabit the
declared O0 value sort. No source evaluation or target receipt is used to
justify this representation boundary.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem tag_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (typeId constructor : Nat) :
    HasType language free bound (tag typeId constructor) (.base "MlTag") := by
  exact nonbare_constructor_typed terms
    [("typeDigits", .collection .vec (.base "R16Nibble")), ("constructorDigits", .collection .vec (.base "R16Nibble"))]
    _ (by decide +kernel)
    (.cons (digits_typed language terms free bound typeId) (.cons (digits_typed language terms free bound constructor) .nil))

theorem byte_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (byte : UInt8) :
    HasType language free bound (byteCode byte) (.base "MlByte") := by
  have limit : byte.toNat < 256 := byte.toNat_lt_size
  exact nonbare_constructor_typed terms [("high", .base "R16Nibble"), ("low", .base "R16Nibble")] _
    (by decide +kernel)
    (.cons (nibble_typed language terms free bound (byte.toNat / 16) (by omega))
      (.cons (nibble_typed language terms free bound (byte.toNat % 16) (Nat.mod_lt _ (by decide))) .nil))

theorem literal_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (datum : OCaml.Literal) :
    HasType language free bound (literal datum) (.base "MlValue") := by
  cases datum with
  | integer number =>
      have sign : HasType language free bound (node (if number < 0 then "MlNegative" else "MlNonnegative")) (.base "MlSign") := by
        split <;> exact nonbare_constructor_typed terms [] [] (by decide +kernel) .nil
      exact nonbare_constructor_typed terms [("sign", .base "MlSign"), ("digits", .collection .vec (.base "R16Nibble"))] _
        (by decide +kernel)
        (.cons sign (.cons (digits_typed language terms free bound number.natAbs) .nil))
  | boolean choice =>
      cases choice <;> exact nonbare_constructor_typed terms [] [] (by decide +kernel) .nil
  | unit => exact nonbare_constructor_typed terms [] [] (by decide +kernel) .nil
  | nil => exact nonbare_constructor_typed terms [] [] (by decide +kernel) .nil
  | string bytes =>
      have elements : ElementsHaveType language free bound (bytes.map byteCode) (.base "MlByte") := by
        induction bytes with
        | nil => exact .nil _ _
        | cons first rest ih => exact .cons (byte_typed language terms free bound first) ih
      exact nonbare_constructor_typed terms [("bytes", .collection .vec (.base "MlByte"))] _
        (by decide +kernel) (.cons (HasType.collection (collectionType := .vec) (rest := none) elements) .nil)

theorem value_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (actual : OCaml.Value) :
    HasType language free bound (value actual) (.base "MlValue") := by
  refine OCaml.Value.rec
    (motive_1 := fun actual => HasType language free bound (value actual) (.base "MlValue"))
    (motive_2 := fun actuals =>
      HasType language free bound (valueList actuals) (.base "MlValues") ∧
      HasType language free bound (environment actuals) (.base "MlEnvironment"))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ actual
  · intro datum
    exact literal_typed language terms free bound datum
  · intro fields ih
    exact nonbare_constructor_typed terms [("fields", .base "MlValues")] _
      (by decide +kernel) (.cons ih.1 .nil)
  · intro head tail headTyped tailTyped
    exact nonbare_constructor_typed terms [("head", .base "MlValue"), ("tail", .base "MlValue")] _
      (by decide +kernel) (.cons headTyped (.cons tailTyped .nil))
  · intro typeId constructor fields ih
    exact nonbare_constructor_typed terms [("tag", .base "MlTag"), ("fields", .base "MlValues")] _
      (by decide +kernel)
      (.cons (tag_typed language terms free bound typeId constructor) (.cons ih.1 .nil))
  · intro function captured ih
    cases function with
    | lambda reference =>
        have functionTyped := nonbare_constructor_typed (label := "MlLambdaFunction") (sort := "MlFunction") terms
          [("code", .base "MlCode")] [code reference] (by decide +kernel) (.cons (code_typed language terms free bound reference) .nil)
        exact nonbare_constructor_typed terms [("function", .base "MlFunction"), ("captured", .base "MlEnvironment")] _
          (by decide +kernel) (.cons functionTyped (.cons ih.2 .nil))
    | recursive group slot =>
        have functionTyped := nonbare_constructor_typed (label := "MlRecursiveFunction") (sort := "MlFunction") terms
          [("group", .base "MlCode"), ("slot", .base "MlCode")] [code group, code slot] (by decide +kernel)
          (.cons (code_typed language terms free bound group) (.cons (code_typed language terms free bound slot) .nil))
        exact nonbare_constructor_typed terms [("function", .base "MlFunction"), ("captured", .base "MlEnvironment")] _
          (by decide +kernel) (.cons functionTyped (.cons ih.2 .nil))
  · constructor
    · exact nonbare_constructor_typed terms [] [] (by decide +kernel) .nil
    · exact nonbare_constructor_typed terms [] [] (by decide +kernel) .nil
  · intro head tail headTyped tailTyped
    constructor
    · exact nonbare_constructor_typed terms [("head", .base "MlValue"), ("tail", .base "MlValues")] _
        (by decide +kernel) (.cons headTyped (.cons tailTyped.1 .nil))
    · exact nonbare_constructor_typed terms [("head", .base "MlValue"), ("tail", .base "MlEnvironment")] _
        (by decide +kernel) (.cons headTyped (.cons tailTyped.2 .nil))

theorem valueList_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (items : List OCaml.Value) :
    HasType language free bound (valueList items) (.base "MlValues") := by
  induction items with
  | nil => exact nonbare_constructor_typed terms [] [] (by decide +kernel) .nil
  | cons head tail ih =>
      exact nonbare_constructor_typed terms [("head", .base "MlValue"), ("tail", .base "MlValues")] _
        (by decide +kernel)
        (.cons (value_typed language terms free bound head) (.cons ih .nil))

theorem environment_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (items : List OCaml.Value) :
    HasType language free bound (environment items) (.base "MlEnvironment") := by
  induction items with
  | nil => exact nonbare_constructor_typed terms [] [] (by decide +kernel) .nil
  | cons head tail ih =>
      exact nonbare_constructor_typed terms [("head", .base "MlValue"), ("tail", .base "MlEnvironment")] _
        (by decide +kernel)
        (.cons (value_typed language terms free bound head) (.cons ih .nil))

#print axioms literal_typed
#print axioms value_typed
#print axioms environment_typed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
