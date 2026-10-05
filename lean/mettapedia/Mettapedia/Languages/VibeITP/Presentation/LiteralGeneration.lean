import Mettapedia.Languages.VibeITP.Presentation.LiteralEncoding
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ComputationLists

/-!
# Completed computations of all seven literal requests

Every successful or refused request is obtained from the authored equations
and generic primitives. The supplied operands are retained in the generated
statement. No independent kernel operation is used as an execution callback.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalLiterals

open ComputationalData ComputationalShift ComputationalSubstitution ComputationalInstantiation ComputationalInference
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => literalProgram
local notation "A" => literalEquations
local notation "H" => productDivisionHost

private theorem app_evaluates (environment : Env) (builtin : Spec.Builtin)
    (expressions : List Term) (arguments : List Spec.Term)
    (children : List.Forall₂ (Evaluates P H environment) expressions (encodeTerms arguments)) :
    Evaluates P H environment
      (.expr [.sym "Vibe:App", encodeSymbol (.builtin builtin), .list expressions])
      (encode (.app (.builtin builtin) arguments)) :=
  Evaluates.call (by simp [Special])
    (.cons (literal_symbol_evaluates _ _) (.cons (Evaluates.list children) .nil)) (literal_app _ _)

private theorem some_evaluates (environment : Env) (expression : Term) (value : Spec.Term)
    (child : Evaluates P H environment expression (encode value)) :
    Evaluates P H environment (.expr [.sym "Some", expression]) (encodeResult (some value)) :=
  Evaluates.call (by simp [Special]) (.cons child .nil) (literal_some _)

private theorem number_evaluates (environment : Env) (name : String) (value : Nat)
    (found : environment.lookup name = some (natural value)) :
    Evaluates P H environment (.expr [.sym "vibe:number-literal", .var name])
      (encode (Spec.Term.natLit value)) :=
  Evaluates.call (by simp [Special]) (.cons (.variable found) .nil) (numberLiteral_computes value)

theorem numericEquation_computes (builtin : Spec.Builtin) (left right result : Nat) :
    Applies P H "vibe:numeric-equation"
      [natural builtin.slot, natural left, natural right, natural result]
      (encodeResult (some (Spec.Term.eq
        (.app (.builtin builtin) [Spec.Term.natLit left, Spec.Term.natLit right])
        (Spec.Term.natLit result)))) := by
  refine literal_equation (equation := A[32])
    (environment := [("code", natural builtin.slot), ("a", natural left), ("b", natural right),
      ("result", natural result)]) (by decide +kernel) (by rfl) (by rfl) ?_
  apply some_evaluates
  apply app_evaluates
  refine .cons ?_ (.cons (number_evaluates _ "result" result (by rfl)) .nil)
  refine Evaluates.call (values := [encodeSymbol (.builtin builtin),
      .list (encodeTerms [Spec.Term.natLit left, Spec.Term.natLit right])]) (by simp [Special])
    (.cons ?_ (.cons ?_ .nil)) (literal_app _ _)
  · exact Evaluates.list (.cons (.symbol _ _ _ _) (.cons (.variable (by rfl)) .nil))
  · exact Evaluates.list (.cons (number_evaluates _ "a" left (by rfl))
      (.cons (number_evaluates _ "b" right (by rfl)) .nil))

private theorem isnat_word (fits : Bool) (value : Nat) :
    Applies P H "vibe:literal-isnat-word" [boolean fits, natural value]
      (encodeResult (if fits then some (Spec.litIsNatStatement value) else none)) := by
  cases fits with
  | false => exact ⟨1, by rw [literal_apply _ (by decide +kernel)]; rfl⟩
  | true =>
      refine literal_equation (equation := A[14]) (environment := [("n", natural value)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      apply some_evaluates
      exact app_evaluates _ .litIsNat _ _ (.cons (number_evaluates _ "n" value (by rfl)) .nil)

theorem literalIsNat_computes (value : Nat) :
    Applies P H "vibe:literal-query" [encodeRequest (.isNat value)]
      (encodeResult (LiteralRequest.isNat value).result) := by
  refine literal_equation (equation := A[12]) (environment := [("n", natural value)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [boolean (decide (value < Spec.wordBound)), natural value])
    (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (literal_natural_evaluates _ _) .nil)) (literal_lt _ _)
  · by_cases fits : value < Spec.wordBound <;>
      simpa only [LiteralRequest.result, fits, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
        using isnat_word (decide (value < Spec.wordBound)) value

private theorem less_order (ordered : Bool) (left right : Nat) :
    Applies P H "vibe:literal-order" [boolean ordered, natural left, natural right]
      (encodeResult (if ordered then some (Spec.litLtStatement left right) else none)) := by
  cases ordered with
  | false => exact ⟨1, by rw [literal_apply _ (by decide +kernel)]; rfl⟩
  | true =>
      refine literal_equation (equation := A[26])
        (environment := [("a", natural left), ("b", natural right)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      apply some_evaluates
      exact app_evaluates _ .litLt _ _
        (.cons (number_evaluates _ "a" left (by rfl)) (.cons (number_evaluates _ "b" right (by rfl)) .nil))

private theorem less_binary (left right : Nat) :
    Applies P H "vibe:literal-binary" [.sym "Literal:Lt", natural left, natural right]
      (encodeResult (if left < right then some (Spec.litLtStatement left right) else none)) := by
  refine literal_equation (equation := A[24])
    (environment := [("a", natural left), ("b", natural right)]) (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [boolean (decide (left < right)), natural left, natural right])
    (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (literal_lt _ _)
  · by_cases ordered : left < right <;>
      simpa only [ordered, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
        using less_order (decide (left < right)) left right

private theorem addition_binary (left right : Nat) :
    Applies P H "vibe:literal-binary" [.sym "Literal:Add", natural left, natural right]
      (encodeResult (some (Spec.litAddStatement left right))) := by
  refine literal_equation (equation := A[27])
    (environment := [("a", natural left), ("b", natural right)]) (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [natural Spec.Builtin.litAdd.slot, natural left, natural right,
      natural ((left + right) % Spec.wordBound)]) (by simp [Special])
    (.cons (literal_natural_evaluates _ _) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons ?_ .nil)))) (numericEquation_computes .litAdd _ _ _)
  refine Evaluates.call (values := [natural (left + right), natural Spec.wordBound])
    (by simp [Special]) (.cons ?_ (.cons (literal_natural_evaluates _ _) .nil))
    (literal_mod _ _ (by decide))
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (literal_add _ _)

private theorem multiplication_binary (left right : Nat) :
    Applies P H "vibe:literal-binary" [.sym "Literal:Mul", natural left, natural right]
      (encodeResult (some (Spec.litMulStatement left right))) := by
  refine literal_equation (equation := A[28])
    (environment := [("a", natural left), ("b", natural right)]) (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [natural Spec.Builtin.litMul.slot, natural left, natural right,
      natural ((left * right) % Spec.wordBound)]) (by simp [Special])
    (.cons (literal_natural_evaluates _ _) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons ?_ .nil)))) (numericEquation_computes .litMul _ _ _)
  refine Evaluates.call (values := [natural (left * right), natural Spec.wordBound])
    (by simp [Special]) (.cons ?_ (.cons (literal_natural_evaluates _ _) .nil))
    (literal_mod _ _ (by decide))
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (literal_mul _ _)

private theorem division_binary (left right : Nat) :
    Applies P H "vibe:literal-binary" [.sym "Literal:Div", natural left, natural right]
      (encodeResult (if right ≠ 0 then some (Spec.litDivStatement left right) else none)) := by
  refine literal_equation (equation := A[29])
    (environment := [("a", natural left), ("b", natural right)]) (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [boolean (decide (right = 0)), natural left, natural right])
    (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (literal_zero right)
  · by_cases zero : right = 0
    · simp only [zero, decide_true, boolean, ↓reduceIte]
      exact ⟨1, by rw [literal_apply _ (by decide +kernel)]; rfl⟩
    · rw [if_pos zero]
      simp only [zero, decide_false, boolean]
      refine literal_equation (equation := A[31])
        (environment := [("a", natural left), ("b", natural right)]) (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [natural Spec.Builtin.litDiv.slot, natural left, natural right,
          natural (left / right)]) (by simp [Special])
        (.cons (literal_natural_evaluates _ _) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons ?_ .nil)))) (numericEquation_computes .litDiv _ _ _)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (literal_div _ _ zero)

private theorem right_word (fits : Bool) (kind : String) (left right : Nat) (result : Option Spec.Term)
    (next : Applies P H "vibe:literal-binary" [.sym kind, natural left, natural right] (encodeResult result)) :
    Applies P H "vibe:literal-right-word" [boolean fits, .sym kind, natural left, natural right]
      (encodeResult (if fits then result else none)) := by
  cases fits with
  | false => exact ⟨1, by rw [literal_apply _ (by decide +kernel)]; rfl⟩
  | true =>
      refine literal_equation (equation := A[23])
        (environment := [("kind", .sym kind), ("a", natural left), ("b", natural right)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) next

private theorem left_word (fits : Bool) (kind : String) (left right : Nat) (result : Option Spec.Term)
    (next : Applies P H "vibe:literal-binary" [.sym kind, natural left, natural right] (encodeResult result)) :
    Applies P H "vibe:literal-left-word" [boolean fits, .sym kind, natural left, natural right]
      (encodeResult (if fits then (if right < Spec.wordBound then result else none) else none)) := by
  cases fits with
  | false => exact ⟨1, by rw [literal_apply _ (by decide +kernel)]; rfl⟩
  | true =>
      refine literal_equation (equation := A[21])
        (environment := [("kind", .sym kind), ("a", natural left), ("b", natural right)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [boolean (decide (right < Spec.wordBound)), .sym kind,
          natural left, natural right]) (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) ?_
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (literal_natural_evaluates _ _) .nil)) (literal_lt _ _)
      · by_cases bound : right < Spec.wordBound <;>
          simpa only [bound, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
            using right_word (decide (right < Spec.wordBound)) kind left right result next

private theorem words_computes (kind : String) (left right : Nat) (result : Option Spec.Term)
    (next : Applies P H "vibe:literal-binary" [.sym kind, natural left, natural right] (encodeResult result)) :
    Applies P H "vibe:literal-words" [.sym kind, natural left, natural right]
      (encodeResult (if left < Spec.wordBound ∧ right < Spec.wordBound then result else none)) := by
  refine literal_equation (equation := A[19])
    (environment := [("kind", .sym kind), ("a", natural left), ("b", natural right)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [boolean (decide (left < Spec.wordBound)), .sym kind,
      natural left, natural right]) (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (literal_natural_evaluates _ _) .nil)) (literal_lt _ _)
  · by_cases first : left < Spec.wordBound <;> by_cases second : right < Spec.wordBound <;>
      simpa only [first, second, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte,
        and_true, true_and, and_false, false_and]
        using left_word (decide (left < Spec.wordBound)) kind left right result next

theorem literalLessThan_computes (left right : Nat) :
    Applies P H "vibe:literal-query" [encodeRequest (.lessThan left right)]
      (encodeResult (LiteralRequest.lessThan left right).result) := by
  refine literal_equation (equation := A[15])
    (environment := [("a", natural left), ("b", natural right)]) (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons (.symbol _ _ _ _) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
  have same : (if left < Spec.wordBound ∧ right < Spec.wordBound then
      (if left < right then some (Spec.litLtStatement left right) else none) else none) =
      (LiteralRequest.lessThan left right).result := by
    by_cases ordered : left < right
    · by_cases second : right < Spec.wordBound
      · have first : left < Spec.wordBound := Nat.lt_trans ordered second
        simp [LiteralRequest.result, first, second, ordered]
      · simp [LiteralRequest.result, second]
    · simp [LiteralRequest.result, ordered]
  rw [← same]
  exact words_computes "Literal:Lt" left right _ (less_binary left right)

theorem literalAddition_computes (left right : Nat) :
    Applies P H "vibe:literal-query" [encodeRequest (.addition left right)]
      (encodeResult (LiteralRequest.addition left right).result) := by
  refine literal_equation (equation := A[16])
    (environment := [("a", natural left), ("b", natural right)]) (by decide +kernel) (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special])
    (.cons (.symbol _ _ _ _) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
    (words_computes "Literal:Add" left right _ (addition_binary left right))

theorem literalMultiplication_computes (left right : Nat) :
    Applies P H "vibe:literal-query" [encodeRequest (.multiplication left right)]
      (encodeResult (LiteralRequest.multiplication left right).result) := by
  refine literal_equation (equation := A[17])
    (environment := [("a", natural left), ("b", natural right)]) (by decide +kernel) (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special])
    (.cons (.symbol _ _ _ _) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
    (words_computes "Literal:Mul" left right _ (multiplication_binary left right))

theorem literalDivision_computes (left right : Nat) :
    Applies P H "vibe:literal-query" [encodeRequest (.division left right)]
      (encodeResult (LiteralRequest.division left right).result) := by
  refine literal_equation (equation := A[18])
    (environment := [("a", natural left), ("b", natural right)]) (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons (.symbol _ _ _ _) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
  have same : (if left < Spec.wordBound ∧ right < Spec.wordBound then
      (if right ≠ 0 then some (Spec.litDivStatement left right) else none) else none) =
      (LiteralRequest.division left right).result := by
    by_cases first : left < Spec.wordBound <;> by_cases second : right < Spec.wordBound <;>
      by_cases nonzero : right ≠ 0 <;> simp [LiteralRequest.result, first, second, nonzero]
  rw [← same]
  exact words_computes "Literal:Div" left right _ (division_binary left right)

private theorem length_applies (items : List Term) :
    Applies P H "vibe:list-length" [.list items] (natural items.length) :=
  reuse_inference_call (by decide +kernel) (reuse_instantiation_call (by decide +kernel)
    (reuse_substitution_call (by decide +kernel) (listLength_computes items)))

private theorem formed_applies (bytes : List UInt8) :
    Applies P H "vibe:well-formed" [.list [], encode (.lit bytes)]
      (boolean (decide (bytes.length + 8 < Spec.wordBound))) :=
  reuse_inference_call (by decide +kernel) (wellFormed_computes [] (.lit bytes))

private theorem length_formed (fits : Bool) (bytes : List UInt8) :
    Applies P H "vibe:literal-length-formed" [boolean fits, .list (bytes.map encodeByte)]
      (encodeResult (if fits then some (Spec.litLengthStatement bytes) else none)) := by
  cases fits with
  | false => exact ⟨1, by rw [literal_apply _ (by decide +kernel)]; rfl⟩
  | true =>
      refine literal_equation (equation := A[36]) (environment := [("bytes", .list (bytes.map encodeByte))])
        (by decide +kernel) (by rfl) (by rfl) ?_
      apply some_evaluates
      apply app_evaluates
      refine .cons ?_ (.cons ?_ .nil)
      · apply app_evaluates
        exact .cons (Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (literal_lit bytes)) .nil
      · refine Evaluates.call (values := [natural bytes.length]) (by simp [Special]) (.cons ?_ .nil)
          (numberLiteral_computes bytes.length)
        exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
          (by simpa only [List.length_map] using length_applies (bytes.map encodeByte))

theorem literalLength_computes (value : Spec.Term) :
    Applies P H "vibe:literal-query" [encodeRequest (.length value)]
      (encodeResult (LiteralRequest.length value).result) := by
  cases value with
  | bvar _ => exact ⟨1, by rw [literal_apply _ (by decide +kernel)]; rfl⟩
  | app _ _ => exact ⟨1, by rw [literal_apply _ (by decide +kernel)]; rfl⟩
  | lit bytes =>
      refine literal_equation (equation := A[33]) (environment := [("bytes", .list (bytes.map encodeByte))])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [boolean (decide (bytes.length + 8 < Spec.wordBound)),
          .list (bytes.map encodeByte)]) (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) ?_
      · exact Evaluates.call (by simp [Special])
          (.cons (Evaluates.list .nil) (.cons
            (Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (literal_lit bytes)) .nil))
          (formed_applies bytes)
      · by_cases bound : bytes.length + 8 < Spec.wordBound <;>
          simpa only [LiteralRequest.result, bound, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
            using length_formed (decide (bytes.length + 8 < Spec.wordBound)) bytes

private theorem get_byte (bytes : List UInt8) (index : Nat) :
    Applies P H "vibe:literal-get-byte"
      [.expr [.sym "Some", encodeByte (bytes.getD index 0)], .list (bytes.map encodeByte), natural index]
      (encodeResult (some (Spec.litGetStatement bytes index))) := by
  refine literal_equation (equation := A[44])
    (environment := [("byte", encodeByte (bytes.getD index 0)), ("bytes", .list (bytes.map encodeByte)),
      ("index", natural index)]) (by decide +kernel) (by rfl) (by rfl) ?_
  apply some_evaluates
  apply app_evaluates
  refine .cons ?_ (.cons (number_evaluates _ "byte" _ (by rfl)) .nil)
  apply app_evaluates
  exact .cons (Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (literal_lit bytes))
    (.cons (number_evaluates _ "index" index (by rfl)) .nil)

private theorem get_bounds (bytes : List UInt8) (index : Nat) :
    Applies P H "vibe:literal-get-bounds"
      [boolean (decide (index < bytes.length)), .list (bytes.map encodeByte), natural index]
      (encodeResult (if index < bytes.length then some (Spec.litGetStatement bytes index) else none)) := by
  by_cases bound : index < bytes.length
  · simp only [bound, decide_true, boolean, ↓reduceIte]
    refine literal_equation (equation := A[42])
      (environment := [("bytes", .list (bytes.map encodeByte)), ("index", natural index)])
      (by decide +kernel) (by rfl) (by rfl) ?_
    refine Evaluates.call (values := [.expr [.sym "Some", encodeByte (bytes.getD index 0)],
        .list (bytes.map encodeByte), natural index]) (by simp [Special])
      (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) (get_byte bytes index)
    exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (byteAt_in_range bytes index bound)
  · simp only [bound, decide_false, boolean, ↓reduceIte]
    exact ⟨1, by rw [literal_apply _ (by decide +kernel)]; rfl⟩

private theorem get_formed (fits : Bool) (bytes : List UInt8) (index : Nat) :
    Applies P H "vibe:literal-get-formed" [boolean fits, .list (bytes.map encodeByte), natural index]
      (encodeResult (if fits then (if index < bytes.length then some (Spec.litGetStatement bytes index) else none)
        else none)) := by
  cases fits with
  | false => exact ⟨1, by rw [literal_apply _ (by decide +kernel)]; rfl⟩
  | true =>
      refine literal_equation (equation := A[40])
        (environment := [("bytes", .list (bytes.map encodeByte)), ("index", natural index)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [boolean (decide (index < bytes.length)),
          .list (bytes.map encodeByte), natural index]) (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) (get_bounds bytes index)
      refine Evaluates.call (values := [natural index, natural bytes.length]) (by simp [Special])
        (.cons (.variable (by rfl)) (.cons ?_ .nil)) (literal_lt _ _)
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
        (by simpa only [List.length_map] using length_applies (bytes.map encodeByte))

theorem literalGet_computes (value : Spec.Term) (index : Nat) :
    Applies P H "vibe:literal-query" [encodeRequest (.get value index)]
      (encodeResult (LiteralRequest.get value index).result) := by
  cases value with
  | bvar _ => exact ⟨1, by rw [literal_apply _ (by decide +kernel)]; rfl⟩
  | app _ _ => exact ⟨1, by rw [literal_apply _ (by decide +kernel)]; rfl⟩
  | lit bytes =>
      refine literal_equation (equation := A[37])
        (environment := [("bytes", .list (bytes.map encodeByte)), ("index", natural index)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [boolean (decide (bytes.length + 8 < Spec.wordBound)),
          .list (bytes.map encodeByte), natural index]) (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
      · exact Evaluates.call (by simp [Special])
          (.cons (Evaluates.list .nil) (.cons
            (Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (literal_lit bytes)) .nil))
          (formed_applies bytes)
      · by_cases formed : bytes.length + 8 < Spec.wordBound <;> by_cases bound : index < bytes.length <;>
          simpa only [LiteralRequest.result, formed, bound, decide_true, decide_false, Bool.false_eq_true,
            ↓reduceIte, and_true, true_and, and_false, false_and]
            using get_formed (decide (bytes.length + 8 < Spec.wordBound)) bytes index

theorem literalQuery_computes (request : LiteralRequest) :
    Applies P H "vibe:literal-query" [encodeRequest request] (encodeResult request.result) := by
  cases request with
  | isNat value => exact literalIsNat_computes value
  | lessThan left right => exact literalLessThan_computes left right
  | addition left right => exact literalAddition_computes left right
  | multiplication left right => exact literalMultiplication_computes left right
  | division left right => exact literalDivision_computes left right
  | length value => exact literalLength_computes value
  | get value index => exact literalGet_computes value index

end Mettapedia.Languages.VibeITP.Presentation.ComputationalLiterals
