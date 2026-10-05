import Mettapedia.Languages.VibeITP.Presentation.InferenceCorrespondence

/-!
# Static operand and submitted-result controls

The examples distinguish canonical term data, formation, the supplied
inference, and independent derivability. In particular an independently
available conclusion does not validate a wrong premise or an invalid
replacement. These checks do not assert complete recursive proof admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalInference.Controls

open ComputationalData ComputationalShift ComputationalSubstitution ComputationalInstantiation
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => inferenceProgram
local notation "H" => computationalHost

private def F : Spec.SymId := .fresh 13
private def binder : Spec.SymId := .fresh 14
private def pair : Spec.SymId := .fresh 15
private def unknown : Spec.SymId := .fresh 99
private def alpha : Spec.Term := .lit [1]
private def beta : Spec.Term := .lit [2]
private def gamma : Spec.Term := .lit [3]
private def nullary : SignatureTable := [(F, Spec.SymInfo.fvarOf 0)]
private def unary : SignatureTable := [(F, Spec.SymInfo.fvarOf 1)]
private def boundUnary : SignatureTable := [(F, Spec.SymInfo.fvarOf 1), (binder, ⟨.constant, [1]⟩)]

/-- Every ordered argument and repeated occurrence is included. -/
theorem recursive_identity_accepts :
    Applies P H "vibe:term-eq"
      [encode (.app pair [alpha, .app binder [alpha, beta], alpha]),
        encode (.app pair [alpha, .app binder [alpha, beta], alpha])] (.sym "True") :=
  term_equality_computes _ _

theorem later_literal_byte_changes_equality :
    Applies P H "vibe:term-eq" [encode (.lit [1, 2, 3]), encode (.lit [1, 2, 4])] (.sym "False") :=
  term_equality_computes _ _

theorem literal_byte_order_is_significant :
    Applies P H "vibe:term-eq" [encode (.lit [1, 2]), encode (.lit [2, 1])] (.sym "False") :=
  term_equality_computes _ _

theorem argument_order_is_significant :
    Applies P H "vibe:term-eq" [encode (.app pair [alpha, beta]), encode (.app pair [beta, alpha])]
      (.sym "False") := term_equality_computes _ _

theorem repeated_argument_multiplicity_is_significant :
    Applies P H "vibe:term-eq" [encode (.app pair [alpha, alpha]), encode (.app pair [alpha])]
      (.sym "False") := term_equality_computes _ _

theorem bound_and_literal_constructors_are_distinct :
    Applies P H "vibe:term-eq" [encode (.bvar 1), encode (.lit [1])] (.sym "False") :=
  term_equality_computes _ _

theorem builtin_slot_and_fresh_identity_are_distinct :
    Applies P H "vibe:term-eq"
      [encode (.app (.builtin .impl) [alpha, beta]), encode (.app (.fresh 2) [alpha, beta])]
      (.sym "False") := term_equality_computes _ _

theorem fresh_identities_above_word_bound_remain_distinct :
    Applies P H "vibe:term-eq"
      [encode (.app (.fresh 18446744073709551629) []),
        encode (.app (.fresh 18446744073709551630) [])] (.sym "False") :=
  term_equality_computes _ _

/-- Equality of raw terms does not establish formation. -/
theorem raw_large_index_equality_accepts :
    Applies P H "vibe:term-eq" [encode (.bvar Spec.wordBound), encode (.bvar Spec.wordBound)]
      (.sym "True") := term_equality_computes _ _

theorem last_formable_bound_index_accepts :
    Applies P H "vibe:well-formed" [encodeTable [], encode (.bvar (Spec.wordBound - 2))]
      (.sym "True") := wellFormed_computes [] _

theorem next_bound_index_is_refused :
    Applies P H "vibe:well-formed" [encodeTable [], encode (.bvar (Spec.wordBound - 1))]
      (.sym "False") := wellFormed_computes [] _

theorem unknown_application_head_is_refused :
    Applies P H "vibe:well-formed" [encodeTable nullary, encode (.app unknown [])] (.sym "False") :=
  wellFormed_computes nullary _

theorem exact_application_arity_accepts :
    Applies P H "vibe:well-formed" [encodeTable unary, encode (.app F [alpha])] (.sym "True") :=
  wellFormed_computes unary _

theorem missing_application_argument_is_refused :
    Applies P H "vibe:well-formed" [encodeTable unary, encode (.app F [])] (.sym "False") :=
  wellFormed_computes unary _

theorem extra_application_argument_is_refused :
    Applies P H "vibe:well-formed" [encodeTable unary, encode (.app F [alpha, beta])] (.sym "False") :=
  wellFormed_computes unary _

theorem later_malformed_child_refuses_application :
    Applies P H "vibe:well-formed" [encodeTable [(pair, ⟨.constant, [0, 0]⟩)],
      encode (.app pair [alpha, .app unknown []])] (.sym "False") := wellFormed_computes _ _

theorem binder_closes_formable_statement :
    Applies P H "vibe:formed-statement" [encodeTable [(binder, ⟨.constant, [1]⟩)],
      encode (.app binder [.bvar 0])] (.sym "True") := statementFormation_computes _ _

theorem formable_open_term_is_not_a_statement :
    Applies P H "vibe:well-formed" [encodeTable [], encode (.bvar 0)] (.sym "True") ∧
    Applies P H "vibe:formed-statement" [encodeTable [], encode (.bvar 0)] (.sym "False") :=
  ⟨wellFormed_computes [] _, statementFormation_computes [] _⟩

theorem literal_header_guard_refuses (bytes : List UInt8) (tooLong : Spec.wordBound ≤ bytes.length + 8) :
    Applies P H "vibe:well-formed" [encodeTable [], encode (.lit bytes)] (.sym "False") := by
  apply (formation_refuses_iff [] (.lit bytes)).mpr
  simp only [Spec.WellFormed, decide_eq_false_iff_not]
  exact Nat.not_lt.mpr tooLong

/-- Constant-symbol admission is a separate judgment: formation does not
silently impose a new bound on an existing binder declaration. -/
theorem raw_binder_metadata_has_no_added_word_cap :
    Applies P H "vibe:well-formed" [encodeTable [(binder, ⟨.constant, [Spec.wordBound]⟩)],
      encode (.app binder [alpha])] (.sym "True") := wellFormed_computes _ _

theorem first_duplicate_declaration_determines_arity :
    Applies P H "vibe:well-formed" [encodeTable [(F, Spec.SymInfo.fvarOf 0), (F, Spec.SymInfo.fvarOf 1)],
      encode (.app F [alpha])] (.sym "False") := wellFormed_computes _ _

theorem correct_modus_ponens_operands_accept :
    Applies P H "vibe:check-mp" [encode (Spec.Term.impl alpha beta), encode alpha, encode beta]
      (.sym "True") := checkModusPonens_computes _ _ _

theorem wrong_modus_ponens_premise_is_refused :
    Applies P H "vibe:check-mp" [encode (Spec.Term.impl alpha beta), encode gamma, encode beta]
      (.sym "False") := checkModusPonens_computes _ _ _

theorem wrong_modus_ponens_conclusion_is_refused :
    Applies P H "vibe:check-mp" [encode (Spec.Term.impl alpha beta), encode alpha, encode gamma]
      (.sym "False") := checkModusPonens_computes _ _ _

theorem equation_head_is_not_modus_ponens :
    Applies P H "vibe:check-mp" [encode (.app (.builtin .eq) [alpha, beta]), encode alpha, encode beta]
      (.sym "False") := checkModusPonens_computes _ _ _

theorem wrong_implication_arity_is_refused :
    Applies P H "vibe:check-mp" [encode (.app (.builtin .impl) [alpha, beta, gamma]), encode alpha, encode beta]
      (.sym "False") := checkModusPonens_computes _ _ _

theorem fresh_slot_two_does_not_authorize_modus_ponens :
    Applies P H "vibe:check-mp" [encode (.app (.fresh 2) [alpha, beta]), encode alpha, encode beta]
      (.sym "False") := checkModusPonens_computes _ _ _

private def availableConclusion : Spec.Theory :=
  ⟨Spec.sigOf (fun _ => none), [Spec.Term.impl alpha beta, gamma, beta], []⟩

/-- All three submitted terms can be derivable while this particular
modus-ponens witness is invalid. -/
theorem derivable_conclusion_does_not_validate_wrong_premise :
    Spec.Derives availableConclusion (Spec.Term.impl alpha beta) ∧
    Spec.Derives availableConclusion gamma ∧ Spec.Derives availableConclusion beta ∧
    ¬ Applies P H "vibe:check-mp" [encode (Spec.Term.impl alpha beta), encode gamma, encode beta] (.sym "True") := by
  refine ⟨.axiom (by simp [availableConclusion]), .axiom (by simp [availableConclusion]),
    .axiom (by simp [availableConclusion]), ?_⟩
  rw [checkModusPonens_accepts_iff]
  decide

theorem valid_modus_ponens_produces_independent_derivation :
    Spec.Derives (⟨Spec.sigOf (fun _ => none), [Spec.Term.impl alpha beta, alpha], []⟩ : Spec.Theory) beta := by
  apply checkModusPonens_derived _ (Spec.Term.impl alpha beta) alpha beta
  · exact .axiom (by simp)
  · exact .axiom (by simp)
  · exact correct_modus_ponens_operands_accept

theorem nullary_theorem_instantiation_accepts :
    Applies P H "vibe:check-inst" [encodeTable nullary, encodeSymbol F, encode beta, encode (.app F []), encode beta]
      (.sym "True") := checkInstantiation_computes nullary F beta (.app F []) beta

theorem wrong_instantiation_conclusion_is_refused :
    Applies P H "vibe:check-inst" [encodeTable nullary, encodeSymbol F, encode beta, encode (.app F []), encode gamma]
      (.sym "False") := checkInstantiation_computes nullary F beta (.app F []) gamma

theorem unknown_instantiation_target_is_refused :
    Applies P H "vibe:check-inst" [encodeTable [], encodeSymbol F, encode beta, encode alpha, encode alpha]
      (.sym "False") := checkInstantiation_computes [] F beta alpha alpha

theorem constant_instantiation_target_is_refused :
    Applies P H "vibe:check-inst" [encodeTable [(F, ⟨.constant, []⟩)], encodeSymbol F,
      encode beta, encode (.app F []), encode beta] (.sym "False") :=
  checkInstantiation_computes _ F beta (.app F []) beta

theorem value_depth_exceeding_arity_is_refused :
    Applies P H "vibe:check-inst" [encodeTable nullary, encodeSymbol F, encode (.bvar 0), encode alpha, encode alpha]
      (.sym "False") := checkInstantiation_computes nullary F (.bvar 0) alpha alpha

/-- The raw operation prunes an unused replacement; theorem creation still
requires the actual replacement to be well formed. -/
theorem unused_malformed_replacement_is_refused :
    Applies instantiationProgram H "vibe:instantiate"
      [encodeTable nullary, encodeSymbol F, encode (.app unknown []), encode alpha] (encodeResult (some alpha)) ∧
    Applies P H "vibe:check-inst"
      [encodeTable nullary, encodeSymbol F, encode (.app unknown []), encode alpha, encode alpha] (.sym "False") :=
  ⟨instantiation_computes nullary F (.app unknown []) alpha,
    checkInstantiation_computes nullary F (.app unknown []) alpha alpha⟩

theorem unary_parameter_instantiation_accepts :
    Applies P H "vibe:check-inst" [encodeTable unary, encodeSymbol F, encode (.bvar 0),
      encode (.app F [alpha]), encode alpha] (.sym "True") :=
  checkInstantiation_computes unary F (.bvar 0) (.app F [alpha]) alpha

theorem instantiation_preserves_bound_parameter :
    Applies P H "vibe:check-inst" [encodeTable boundUnary, encodeSymbol F, encode (.bvar 0),
      encode (.app binder [.app F [.bvar 0]]), encode (.app binder [.bvar 0])] (.sym "True") :=
  checkInstantiation_computes boundUnary F (.bvar 0) (.app binder [.app F [.bvar 0]]) (.app binder [.bvar 0])

theorem invented_instantiation_result_is_refused :
    Applies P H "vibe:check-inst" [encodeTable boundUnary, encodeSymbol F, encode (.bvar 0),
      encode (.app binder [.app F [.bvar 0]]), encode (.app binder [alpha])] (.sym "False") :=
  checkInstantiation_computes boundUnary F (.bvar 0) (.app binder [.app F [.bvar 0]]) (.app binder [alpha])

private def infiniteSignature : Spec.Sig := Spec.sigOf (fun _ => some (Spec.SymInfo.fvarOf 0))

theorem infinite_reference_signature_has_exact_finite_snapshot :
    Applies P H "vibe:thm-instantiate"
      [encodeTable (instantiationSnapshot infiniteSignature F (.app (.fresh 1000) []) (.app F [])),
        encodeSymbol F, encode (.app (.fresh 1000) []), encode (.app F [])]
      (encodeResult (some (.app (.fresh 1000) []))) :=
  theoremInstantiation_computes_for_signature infiniteSignature F (.app (.fresh 1000) []) (.app F [])

theorem no_extra_modus_ponens_result :
    ¬ Applies P H "vibe:check-mp" [encode (Spec.Term.impl alpha beta), encode alpha, encode beta]
      (.sym "unrelated-result") := by
  rw [checkModusPonens_result_exact]
  change ¬ Term.sym "unrelated-result" = Term.sym "True"
  simp only [Term.sym.injEq]
  decide

/-- Fuel zero is exhaustion, not a completed refusal of a valid inference. -/
theorem valid_inference_is_not_refused_by_fuel_zero :
    apply P H 0 "vibe:check-mp" [encode (Spec.Term.impl alpha beta), encode alpha, encode beta] = .exhausted ∧
    Applies P H "vibe:check-mp" [encode (Spec.Term.impl alpha beta), encode alpha, encode beta] (.sym "True") :=
  ⟨rfl, correct_modus_ponens_operands_accept⟩

end Mettapedia.Languages.VibeITP.Presentation.ComputationalInference.Controls
