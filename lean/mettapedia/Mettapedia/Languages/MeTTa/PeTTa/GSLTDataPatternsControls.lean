import Mettapedia.Languages.MeTTa.PeTTa.GSLTDataPatterns

/-! # Data-pattern controls over constructor, scalar and open-value boundaries -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.GSLTDataPatterns.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open ListView
open Mettapedia.Languages.ProcessCalculi.MORK (atomFreeVars)

def consData : Atom := .expression [.symbol "cons", .symbol "a",
  .expression [.symbol "b", .symbol "c"]]

def appliedData : Atom := .expression [.symbol "a", .symbol "b", .symbol "c"]

theorem constructor_collision_stays_apart :
    encode "cons-atom" consData ≠ encode "cons-atom" appliedData := by
  intro same
  have collapsed := encode_injective "cons-atom" same
  have distinct : consData ≠ appliedData := by decide +kernel
  exact distinct collapsed

theorem constructor_data_reads_exactly :
    readPattern (encode "cons" consData) = spell consData := readPattern_encode _

theorem nullary_is_not_a_symbol :
    encode "cons-atom" (.expression [.symbol "Nil"]) ≠ encode "cons-atom" (.symbol "Nil") := by
  intro same
  cases encode_injective "cons-atom" same

def scalarKinds : Atom := .expression [.symbol "True", .grounded (.bool true),
  .grounded (.string "True"), .grounded (.int 1), .grounded (.custom "value" "λ")]

theorem scalar_kinds_round_trip :
    decode "cons-atom" (encode "cons-atom" scalarKinds) = some scalarKinds := decode_encode _ _

theorem string_and_symbol_stay_apart :
    encode "cons-atom" (.grounded (.string "a")) ≠ encode "cons-atom" (.symbol "a") := by
  intro same
  cases encode_injective "cons-atom" same

theorem unicode_and_unknown_escape_stay_data :
    decode "λ-view" (encode "λ-view" (.expression [.symbol "λ", .grounded (.string "λ\\q")])) =
      some (.expression [.symbol "λ", .grounded (.string "λ\\q")]) := decode_encode _ _

theorem repeated_unknowns_keep_occurrences :
    atomFreeVars (encode "cons-atom"
      (.expression [.symbol "cons", .var "x", .var "x", .var "y"])) = ["x", "x", "y"] := by
  rw [freeVars_encode]
  rfl

theorem unknown_tail_is_not_an_empty_tail :
    decode "cons-atom" (.expression [.symbol "cons-atom", .symbol "a", .var "tail"]) = none := by
  decide +kernel

theorem wrong_primitive_is_not_an_alias :
    retarget "cons-atom" "cons" (encode "cons" consData) = none := by decide +kernel

/-- The same words are valid source data when encoded as such. -/
theorem primitive_named_source_constructor_round_trip :
    decode "cons-atom" (encode "cons-atom"
      (.expression [.symbol "cons-atom", .symbol "a", .var "tail"])) =
      some (.expression [.symbol "cons-atom", .symbol "a", .var "tail"]) := decode_encode _ _

theorem repeated_variable_accepts_equal_values :
    PatternHolds (fun _ => .symbol "a")
      (encode "cons" (.expression [.symbol "cons", .var "x", .var "x"]))
      (.expression [.symbol "cons", .symbol "a", .symbol "a"]) := by
  rw [patternHolds_iff]
  rfl

theorem repeated_variable_refuses_different_values :
    ¬ ∃ valuation : Valuation, PatternHolds valuation
      (encode "cons" (.expression [.symbol "cons", .var "x", .var "x"]))
      (.expression [.symbol "cons", .symbol "a", .symbol "b"]) := by
  rintro ⟨valuation, holds⟩
  rw [patternHolds_iff] at holds
  simp only [instantiate, instantiate.instantiateList, Atom.expression.injEq,
    List.cons.injEq, true_and, and_true] at holds
  have impossible : Atom.symbol "a" = .symbol "b" := holds.1.symm.trans holds.2
  have distinct : Atom.symbol "a" ≠ .symbol "b" := by decide +kernel
  exact distinct impossible

#print axioms decode_encode
#print axioms encode_decode
#print axioms encode_injective
#print axioms retarget_reflects
#print axioms retarget_comp
#print axioms freeVars_encode
#print axioms readPattern_encode
#print axioms patternHolds_iff
#print axioms native_readback
#print axioms repeated_variable_refuses_different_values

end Mettapedia.Languages.MeTTa.PeTTa.GSLTDataPatterns.Controls
