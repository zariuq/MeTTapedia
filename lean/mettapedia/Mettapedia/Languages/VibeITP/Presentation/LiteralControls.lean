import Mettapedia.Languages.VibeITP.Presentation.LiteralCorrespondence

/-!
# Literal computation and supplied-witness controls

The controls exercise all seven constructors, unsigned-word boundaries,
little-endian bytes, indexed lookup and refusal. Generic arithmetic or an
unrelated axiom cannot authorize an invalid literal request.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalLiterals.LiteralControls

open ComputationalData ComputationalShift
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => literalProgram
local notation "H" => productDivisionHost

theorem number_255_has_one_byte :
    Applies P H "vibe:number-bytes" [natural 255] (.list [natural 255]) := numberBytes_computes 255

theorem number_256_has_eight_little_endian_bytes :
    Applies P H "vibe:number-bytes" [natural 256]
      (.list [natural 0, natural 1, natural 0, natural 0, natural 0, natural 0, natural 0, natural 0]) :=
  numberBytes_computes 256

theorem number_encoding_preserves_low_byte_order :
    Applies P H "vibe:number-bytes" [natural 66051]
      (.list [natural 3, natural 2, natural 1, natural 0, natural 0, natural 0, natural 0, natural 0]) :=
  numberBytes_computes 66051

theorem raw_large_encoding_does_not_authorize_large_word :
    Applies P H "vibe:number-bytes" [natural Spec.wordBound]
        (.list (List.replicate 8 (natural 0))) ∧
      Applies P H "vibe:literal-query" [encodeRequest (.isNat Spec.wordBound)] (.sym "None") := by
  constructor
  · exact numberBytes_computes Spec.wordBound
  · apply (literalQuery_refuses_iff _).mpr
    simp [LiteralRequest.result]

theorem zero_is_nat_accepts :
    Applies P H "vibe:check-literal" [encodeRequest (.isNat 0), encode (Spec.litIsNatStatement 0)] (.sym "True") :=
  (checkLiteral_accepts_iff _ _).mpr (by decide +kernel)

theorem largest_word_is_nat_accepts :
    Applies P H "vibe:check-literal"
      [encodeRequest (.isNat (Spec.wordBound - 1)), encode (Spec.litIsNatStatement (Spec.wordBound - 1))]
      (.sym "True") :=
  (checkLiteral_accepts_iff _ _).mpr (by decide +kernel)

theorem out_of_word_nat_refuses (value : Nat) (bound : Spec.wordBound ≤ value) :
    Applies P H "vibe:literal-query" [encodeRequest (.isNat value)] (.sym "None") := by
  apply (literalQuery_refuses_iff _).mpr
  simp [LiteralRequest.result, Nat.not_lt.mpr bound]

theorem less_than_255_256_accepts :
    Applies P H "vibe:check-literal"
      [encodeRequest (.lessThan 255 256), encode (Spec.litLtStatement 255 256)] (.sym "True") :=
  (checkLiteral_accepts_iff _ _).mpr (by decide +kernel)

theorem equal_operands_are_not_less_than (value : Nat) :
    Applies P H "vibe:literal-query" [encodeRequest (.lessThan value value)] (.sym "None") := by
  apply (literalQuery_refuses_iff _).mpr
  simp [LiteralRequest.result]

theorem reversed_less_than_refuses :
    Applies P H "vibe:check-literal" [encodeRequest (.lessThan 2 1), encode (Spec.litLtStatement 2 1)] (.sym "False") :=
  (checkLiteral_refuses_iff _ _).mpr (by decide +kernel)

theorem less_than_word_bound_refuses :
    Applies P H "vibe:literal-query" [encodeRequest (.lessThan 0 Spec.wordBound)] (.sym "None") := by
  apply (literalQuery_refuses_iff _).mpr
  simp [LiteralRequest.result]

theorem addition_wraps_at_word_bound :
    Applies P H "vibe:check-literal"
      [encodeRequest (.addition (Spec.wordBound - 1) 1),
        encode (Spec.Term.eq (.app (.builtin .litAdd)
          [Spec.Term.natLit (Spec.wordBound - 1), Spec.Term.natLit 1]) (Spec.Term.natLit 0))] (.sym "True") :=
  (checkLiteral_accepts_iff _ _).mpr (by decide +kernel)

theorem unwrapped_addition_result_refuses :
    Applies P H "vibe:check-literal"
      [encodeRequest (.addition (Spec.wordBound - 1) 1),
        encode (Spec.Term.eq (.app (.builtin .litAdd)
          [Spec.Term.natLit (Spec.wordBound - 1), Spec.Term.natLit 1]) (Spec.Term.natLit Spec.wordBound))] (.sym "False") :=
  (checkLiteral_refuses_iff _ _).mpr (by decide +kernel)

theorem addition_retains_submitted_operands :
    Applies P H "vibe:check-literal"
      [encodeRequest (.addition 1 2), encode (Spec.litAddStatement 2 1)] (.sym "False") :=
  (checkLiteral_refuses_iff _ _).mpr (by decide +kernel)

theorem addition_overflow_operand_refuses :
    Applies P H "vibe:literal-query" [encodeRequest (.addition Spec.wordBound 0)] (.sym "None") := by
  apply (literalQuery_refuses_iff _).mpr
  simp [LiteralRequest.result]

theorem multiplication_wraps_to_one :
    Applies P H "vibe:check-literal"
      [encodeRequest (.multiplication (Spec.wordBound - 1) (Spec.wordBound - 1)),
        encode (Spec.Term.eq (.app (.builtin .litMul)
          [Spec.Term.natLit (Spec.wordBound - 1), Spec.Term.natLit (Spec.wordBound - 1)]) (Spec.Term.natLit 1))]
      (.sym "True") :=
  (checkLiteral_accepts_iff _ _).mpr (by decide +kernel)

theorem wrong_multiplication_result_refuses :
    Applies P H "vibe:check-literal"
      [encodeRequest (.multiplication 255 256),
        encode (Spec.Term.eq (.app (.builtin .litMul) [Spec.Term.natLit 255, Spec.Term.natLit 256])
          (Spec.Term.natLit 65281))] (.sym "False") :=
  (checkLiteral_refuses_iff _ _).mpr (by decide +kernel)

theorem multiplication_out_of_word_operand_refuses :
    Applies P H "vibe:literal-query" [encodeRequest (.multiplication 0 Spec.wordBound)] (.sym "None") := by
  apply (literalQuery_refuses_iff _).mpr
  simp [LiteralRequest.result]

theorem division_uses_floor_result :
    Applies P H "vibe:check-literal" [encodeRequest (.division 17 5), encode (Spec.litDivStatement 17 5)] (.sym "True") :=
  (checkLiteral_accepts_iff _ _).mpr (by decide +kernel)

theorem division_largest_word_by_one_accepts :
    Applies P H "vibe:check-literal"
      [encodeRequest (.division (Spec.wordBound - 1) 1), encode (Spec.litDivStatement (Spec.wordBound - 1) 1)]
      (.sym "True") :=
  (checkLiteral_accepts_iff _ _).mpr (by decide +kernel)

theorem rounded_up_division_refuses :
    Applies P H "vibe:check-literal"
      [encodeRequest (.division 17 5),
        encode (Spec.Term.eq (.app (.builtin .litDiv) [Spec.Term.natLit 17, Spec.Term.natLit 5])
          (Spec.Term.natLit 4))] (.sym "False") :=
  (checkLiteral_refuses_iff _ _).mpr (by decide +kernel)

theorem zero_divisor_is_completed_refusal (value : Nat) :
    Applies P H "vibe:literal-query" [encodeRequest (.division value 0)] (.sym "None") := by
  apply (literalQuery_refuses_iff _).mpr
  simp [LiteralRequest.result]

theorem data_construction_cannot_authorize_division_by_zero :
    Applies P H "vibe:numeric-equation" [natural Spec.Builtin.litDiv.slot, natural 1, natural 0, natural 0]
        (encodeResult (some (Spec.litDivStatement 1 0))) ∧
      Applies P H "vibe:check-literal" [encodeRequest (.division 1 0), encode (Spec.litDivStatement 1 0)]
        (.sym "False") := by
  constructor
  · exact numericEquation_computes .litDiv 1 0 0
  · exact (checkLiteral_refuses_iff _ _).mpr (by decide +kernel)

theorem literal_byte_length_accepts :
    Applies P H "vibe:check-literal"
      [encodeRequest (.length (.lit [0, 255, 0])), encode (Spec.litLengthStatement [0, 255, 0])] (.sym "True") :=
  (checkLiteral_accepts_iff _ _).mpr (by decide +kernel)

theorem empty_literal_length_accepts :
    Applies P H "vibe:check-literal" [encodeRequest (.length (.lit [])), encode (Spec.litLengthStatement [])] (.sym "True") :=
  (checkLiteral_accepts_iff _ _).mpr (by decide +kernel)

theorem wrong_literal_length_refuses :
    Applies P H "vibe:check-literal"
      [encodeRequest (.length (.lit [7, 8])),
        encode (Spec.Term.eq (.app (.builtin .litLength) [.lit [7, 8]]) (Spec.Term.natLit 1))] (.sym "False") :=
  (checkLiteral_refuses_iff _ _).mpr (by decide +kernel)

theorem nonliteral_length_refuses :
    Applies P H "vibe:literal-query" [encodeRequest (.length (.bvar 0))] (.sym "None") :=
  (literalQuery_refuses_iff _).mpr rfl

theorem unrepresentable_literal_length_refuses (bytes : List UInt8)
    (bound : Spec.wordBound ≤ bytes.length + 8) :
    Applies P H "vibe:literal-query" [encodeRequest (.length (.lit bytes))] (.sym "None") := by
  apply (literalQuery_refuses_iff _).mpr
  simp [LiteralRequest.result, Nat.not_lt.mpr bound]

theorem first_byte_accepts :
    Applies P H "vibe:check-literal"
      [encodeRequest (.get (.lit [255, 1, 128]) 0), encode (Spec.litGetStatement [255, 1, 128] 0)] (.sym "True") :=
  (checkLiteral_accepts_iff _ _).mpr (by decide +kernel)

theorem last_byte_accepts :
    Applies P H "vibe:check-literal"
      [encodeRequest (.get (.lit [255, 1, 128]) 2), encode (Spec.litGetStatement [255, 1, 128] 2)] (.sym "True") :=
  (checkLiteral_accepts_iff _ _).mpr (by decide +kernel)

theorem repeated_byte_positions_remain_distinct :
    Applies P H "vibe:check-literal"
      [encodeRequest (.get (.lit [7, 7]) 0), encode (Spec.litGetStatement [7, 7] 1)] (.sym "False") :=
  (checkLiteral_refuses_iff _ _).mpr (by decide +kernel)

theorem byte_lookup_preserves_order :
    Applies P H "vibe:check-literal"
      [encodeRequest (.get (.lit [255, 1, 128]) 0),
        encode (Spec.Term.eq (.app (.builtin .litGet) [.lit [255, 1, 128], Spec.Term.natLit 0])
          (Spec.Term.natLit 128))] (.sym "False") :=
  (checkLiteral_refuses_iff _ _).mpr (by decide +kernel)

theorem index_at_length_refuses (bytes : List UInt8) :
    Applies P H "vibe:literal-query" [encodeRequest (.get (.lit bytes) bytes.length)] (.sym "None") := by
  apply (literalQuery_refuses_iff _).mpr
  simp [LiteralRequest.result]

theorem empty_literal_has_no_byte (index : Nat) :
    Applies P H "vibe:literal-query" [encodeRequest (.get (.lit []) index)] (.sym "None") := by
  apply (literalQuery_refuses_iff _).mpr
  simp [LiteralRequest.result]

theorem nonliteral_get_refuses :
    Applies P H "vibe:literal-query" [encodeRequest (.get (.app (.fresh 0) []) 0)] (.sym "None") :=
  (literalQuery_refuses_iff _).mpr rfl

theorem globally_derivable_claim_does_not_validate_bad_operands (theory : Spec.Theory)
    (asserted : Spec.litDivStatement 1 0 ∈ theory.axioms) :
    Spec.Derives theory (Spec.litDivStatement 1 0) ∧
      Applies P H "vibe:check-literal" [encodeRequest (.division 1 0), encode (Spec.litDivStatement 1 0)]
        (.sym "False") :=
  ⟨.axiom asserted, (checkLiteral_refuses_iff _ _).mpr (by decide +kernel)⟩

theorem no_extra_completed_statement (request : LiteralRequest) (claimed : Spec.Term)
    (wrong : request.result ≠ some claimed) :
    ¬ Applies P H "vibe:literal-query" [encodeRequest request] (encodeResult (some claimed)) := by
  intro invented
  exact wrong ((literalQuery_accepts_iff request claimed).mp invented)

theorem no_extra_check_result (request : LiteralRequest) (claimed : Spec.Term) :
    ¬ Applies P H "vibe:check-literal" [encodeRequest request, encode claimed] (.sym "invented") := by
  rw [checkLiteral_result_exact]
  cases decide (request.result = some claimed) <;> simp [boolean]

theorem exhausted_valid_check_is_not_rejection :
    apply P H 0 "vibe:check-literal" [encodeRequest (.isNat 0), encode (Spec.litIsNatStatement 0)] = .exhausted ∧
      Applies P H "vibe:check-literal" [encodeRequest (.isNat 0), encode (Spec.litIsNatStatement 0)] (.sym "True") := by
  constructor
  · rw [literal_apply _ (by decide +kernel)]
    rfl
  · exact zero_is_nat_accepts

end Mettapedia.Languages.VibeITP.Presentation.ComputationalLiterals.LiteralControls
