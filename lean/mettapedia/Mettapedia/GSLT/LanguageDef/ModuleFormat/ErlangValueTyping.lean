import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangProgramCompilation
import Mettapedia.GSLT.LanguageDef.ConstructorCertificates
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.IntervalCases

/-! Every finite source Erlang value, including captured and recursive
closures, inhabits the actual shared value declarations. The mailbox
language is a consumer of those declarations; no evaluation or successful
receipt is assumed as evidence for typing. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangCompilation

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem constructor_typed {free : FreeTypeContext} {bound : List TypeExpr} {label sort : String}
    (parameters : List (String × TypeExpr)) (arguments : List Pattern)
    (declared : (ErlangMailbox.language.terms.find? (fun row => row.label == label)).map
      (fun row => (row.category, row.params, ConstructorCertificates.ordinary row)) =
      some (sort, parameters.map (fun parameter => .simple parameter.1 parameter.2), true))
    (typed : List.Forall₂ (fun parameter argument => HasType ErlangMailbox.language free bound argument parameter.2)
      parameters arguments) :
    HasType ErlangMailbox.language free bound (node label arguments) (.base sort) :=
  ConstructorCertificates.simple parameters arguments declared typed

theorem nibble_typed (free : FreeTypeContext) (bound : List TypeExpr) (digit : Nat) (bounded : digit < 16) :
    HasType ErlangMailbox.language free bound (node ("R16Nibble" ++ toString digit)) (.base "R16Nibble") := by
  interval_cases digit <;> exact constructor_typed [] [] (by decide +kernel) .nil

theorem word_typed (free : FreeTypeContext) (bound : List TypeExpr) (number : Nat) :
    HasType ErlangMailbox.language free bound (word number) (.collection .vec (.base "R16Nibble")) := by
  apply HasType.collection
  have each : ∀ digit ∈ Nat.digits 16 number, digit < 16 :=
    fun digit member => Nat.digits_lt_base (by decide) member
  generalize Nat.digits 16 number = items at *
  induction items with
  | nil => exact .nil _ _
  | cons first rest ih =>
      exact .cons (nibble_typed free bound first (each first List.mem_cons_self))
        (ih (fun digit member => each digit (List.mem_cons_of_mem first member)))

theorem count_typed (free : FreeTypeContext) (bound : List TypeExpr) (number : Nat) :
    HasType ErlangMailbox.language free bound (count number) (.base "ErCount") := by
  induction number with
  | zero => exact constructor_typed [] [] (by decide +kernel) .nil
  | succ number ih =>
      exact constructor_typed [("count", .base "ErCount")] _ (by decide +kernel) (.cons ih .nil)

theorem code_typed (free : FreeTypeContext) (bound : List TypeExpr) (number : Nat) :
    HasType ErlangMailbox.language free bound (code number) (.base "ErCode") :=
  constructor_typed [("digits", .collection .vec (.base "R16Nibble"))] _ (by decide +kernel)
    (.cons (word_typed free bound number) .nil)

theorem atom_typed (free : FreeTypeContext) (bound : List TypeExpr) (text : String) :
    HasType ErlangMailbox.language free bound (ErlangMailbox.atom text) (.base "ErValue") := by
  have bytes : ∀ items : List UInt8, ElementsHaveType ErlangMailbox.language free bound
      (items.flatMap fun byte => [node ("R16Nibble" ++ toString (byte.toNat / 16)),
        node ("R16Nibble" ++ toString (byte.toNat % 16))]) (.base "R16Nibble") := by
    intro items
    induction items with
    | nil => exact .nil _ _
    | cons byte rest ih =>
        have limit : byte.toNat < 256 := byte.toNat_lt_size
        exact .cons (nibble_typed free bound (byte.toNat / 16) (by omega))
          (.cons (nibble_typed free bound (byte.toNat % 16) (Nat.mod_lt _ (by decide))) ih)
  exact constructor_typed [("utf8", .collection .vec (.base "R16Nibble"))] _ (by decide +kernel)
    (.cons (HasType.collection (collectionType := .vec) (rest := none) (bytes text.toUTF8.toList)) .nil)

theorem literal_typed (free : FreeTypeContext) (bound : List TypeExpr) (datum : Erlang.Literal) :
    HasType ErlangMailbox.language free bound (literal datum) (.base "ErValue") := by
  cases datum with
  | atom text => exact atom_typed free bound text
  | integer number =>
      have sign : HasType ErlangMailbox.language free bound
          (node (if number < 0 then "ErNegative" else "ErNonnegative")) (.base "ErSign") := by
        split <;> exact constructor_typed [] [] (by decide +kernel) .nil
      exact constructor_typed [("sign", .base "ErSign"), ("digits", .collection .vec (.base "R16Nibble"))] _
        (by decide +kernel) (.cons sign (.cons (word_typed free bound number.natAbs) .nil))
  | nil => exact constructor_typed [] [] (by decide +kernel) .nil

theorem function_typed (free : FreeTypeContext) (bound : List TypeExpr) (function : Erlang.FunctionRef) :
    HasType ErlangMailbox.language free bound
      (match function with
        | .lambda reference => node "ErLambdaFunction" [code reference]
        | .recursive group slot => node "ErRecursiveFunction" [code group, count slot]) (.base "ErFunction") := by
  cases function with
  | lambda reference =>
      exact constructor_typed [("code", .base "ErCode")] _ (by decide +kernel)
        (.cons (code_typed free bound reference) .nil)
  | recursive group slot =>
      exact constructor_typed [("group", .base "ErCode"), ("slot", .base "ErCount")] _ (by decide +kernel)
        (.cons (code_typed free bound group) (.cons (count_typed free bound slot) .nil))

theorem value_typed (free : FreeTypeContext) (bound : List TypeExpr) (source : Erlang.Value) :
    HasType ErlangMailbox.language free bound (value source) (.base "ErValue") := by
  refine Erlang.Value.rec
    (motive_1 := fun source => HasType ErlangMailbox.language free bound (value source) (.base "ErValue"))
    (motive_2 := fun values =>
      HasType ErlangMailbox.language free bound (valueList values) (.base "ErValues") ∧
      HasType ErlangMailbox.language free bound (environment values) (.base "ErEnvironment"))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ source
  · exact literal_typed free bound
  · intro identity
    exact constructor_typed [("digits", .collection .vec (.base "R16Nibble"))] _ (by decide +kernel)
      (.cons (word_typed free bound identity) .nil)
  · intro fields ih
    exact constructor_typed [("fields", .base "ErValues")] _ (by decide +kernel) (.cons ih.1 .nil)
  · intro head tail headIH tailIH
    exact constructor_typed [("head", .base "ErValue"), ("tail", .base "ErValue")] _ (by decide +kernel)
      (.cons headIH (.cons tailIH .nil))
  · intro arity function captured ih
    exact constructor_typed [("arity", .base "ErCount"), ("function", .base "ErFunction"), ("captured", .base "ErEnvironment")] _
      (by decide +kernel)
      (.cons (count_typed free bound arity) (.cons (function_typed free bound function) (.cons ih.2 .nil)))
  · exact ⟨constructor_typed [] [] (by decide +kernel) .nil, constructor_typed [] [] (by decide +kernel) .nil⟩
  · intro head tail headIH tailIH
    exact ⟨constructor_typed [("head", .base "ErValue"), ("tail", .base "ErValues")] _ (by decide +kernel)
      (.cons headIH (.cons tailIH.1 .nil)),
      constructor_typed [("head", .base "ErValue"), ("tail", .base "ErEnvironment")] _ (by decide +kernel)
        (.cons headIH (.cons tailIH.2 .nil))⟩

theorem valueList_typed (free : FreeTypeContext) (bound : List TypeExpr) (items : List Erlang.Value) :
    HasType ErlangMailbox.language free bound (valueList items) (.base "ErValues") := by
  induction items with
  | nil => exact constructor_typed [] [] (by decide +kernel) .nil
  | cons head tail ih =>
      exact constructor_typed [("head", .base "ErValue"), ("tail", .base "ErValues")] _ (by decide +kernel)
        (.cons (value_typed free bound head) (.cons ih .nil))

theorem environment_typed (free : FreeTypeContext) (bound : List TypeExpr) (items : List Erlang.Value) :
    HasType ErlangMailbox.language free bound (environment items) (.base "ErEnvironment") := by
  induction items with
  | nil => exact constructor_typed [] [] (by decide +kernel) .nil
  | cons head tail ih =>
      exact constructor_typed [("head", .base "ErValue"), ("tail", .base "ErEnvironment")] _ (by decide +kernel)
        (.cons (value_typed free bound head) (.cons ih .nil))

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangCompilation
