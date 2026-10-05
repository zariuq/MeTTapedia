import Mettapedia.Languages.MM0.Presentation.SpecificationCorrespondence

/-! # Fixed-specification, auxiliary declaration and exact payload controls -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalSpecification.Controls

open Kernel ComputationalAdmission
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => specificationProgram
local notation "H" => dataEqualityHost

private instance : DecidableEq Theory := fun left right =>
  decidable_of_iff (encodeTheory left = encodeTheory right) encodeTheory_injective.eq_iff

private def proposition : SortInfo := { provable := true }
private def constant : TermDecl := ⟨[], 0, ∅⟩
private def statement (symbol : Nat) : TheoremDecl := ⟨[], [], .term symbol⟩
private def specification : List SpecificationEntry :=
  [.sort 0 proposition, .term 0 constant, .axiomDecl 0 (statement 0)]
private def admissions : List Admission :=
  [.sort 0 proposition, .term 0 constant, .axiomDecl 0 (statement 0)]
private def declarations : List ProofDeclaration := admissions.map (fun admission => ⟨admission, false⟩)
private def declared : Theory :=
  { sorts := [(0, proposition)], terms := [(0, constant)], theorems := [(0, statement 0)] }
private def derived : Theory := { declared with theorems := [(1, statement 0), (0, statement 0)] }
private def witness : ProofWitness := .theoremApp 0 [] []

private def verified (expected : List SpecificationEntry) (proof : List ProofDeclaration)
    (result : Option Theory) : Prop :=
  Applies P H "mm0:spec-verify" [encodeEntries expected, encodeProofDeclarations proof] (encodeTheoryResult result)

private theorem checked (expected : List SpecificationEntry) (proof : List ProofDeclaration)
    (result : Option Theory) (computed : SpecificationAdmission.verify? expected proof = result) :
    verified expected proof result := by
  simpa only [verified, computed] using verify_computes expected proof

theorem empty_specification_and_proof : verified [] [] (some {}) := checked _ _ _ (by decide +kernel)

theorem exact_public_declarations : verified specification declarations (some declared) :=
  checked _ _ _ (by decide +kernel)

theorem public_theorem_has_checked_proof :
    verified (specification ++ [.theoremDecl 1 (statement 0)])
      (declarations ++ [⟨.theoremDecl 1 (statement 0) [] witness, false⟩]) (some derived) :=
  checked _ _ _ (by decide +kernel)

theorem local_proved_theorem_adds_no_assumption :
    verified specification (declarations ++ [⟨.theoremDecl 1 (statement 0) [] witness, true⟩]) (some derived) :=
  checked _ _ _ (by decide +kernel)

theorem local_definition_is_checked_and_allowed :
    verified specification (declarations ++ [⟨.definition 1 constant ⟨[], .term 0⟩, true⟩])
      (some { declared with terms := [(1, constant), (0, constant)], definitions := [(1, ⟨[], .term 0⟩)] }) :=
  checked _ _ _ (by decide +kernel)

theorem extra_axiom_can_pass_logical_admission :
    Theory.run? {} (admissions ++ [.axiomDecl 1 (statement 0)]) = some derived := by decide +kernel

theorem specification_rejects_that_extra_axiom :
    verified specification (declarations ++ [⟨.axiomDecl 1 (statement 0), false⟩]) none :=
  checked _ _ _ (by decide +kernel)

theorem local_flag_cannot_hide_an_axiom :
    verified specification (declarations ++ [⟨.axiomDecl 1 (statement 0), true⟩]) none :=
  checked _ _ _ (by decide +kernel)

theorem local_flag_cannot_hide_a_sort :
    verified specification (declarations ++ [⟨.sort 1 proposition, true⟩]) none :=
  checked _ _ _ (by decide +kernel)

theorem local_flag_cannot_hide_a_primitive_term :
    verified specification (declarations ++ [⟨.term 1 constant, true⟩]) none :=
  checked _ _ _ (by decide +kernel)

theorem omitted_expected_axiom_refuses :
    verified specification [⟨.sort 0 proposition, false⟩, ⟨.term 0 constant, false⟩] none :=
  checked _ _ _ (by decide +kernel)

theorem matching_prefix_is_not_whole_specification_acceptance :
    verified (specification ++ [.theoremDecl 1 (statement 0)]) declarations none :=
  checked _ _ _ (by decide +kernel)

theorem reordered_expected_declarations_refuse :
    verified [.term 0 constant, .sort 0 proposition, .axiomDecl 0 (statement 0)] declarations none :=
  checked _ _ _ (by decide +kernel)

theorem changed_axiom_identity_refuses :
    verified [.sort 0 proposition, .term 0 constant, .axiomDecl 1 (statement 0)] declarations none :=
  checked _ _ _ (by decide +kernel)

theorem expected_theorem_cannot_be_supplied_as_an_axiom :
    verified (specification ++ [.theoremDecl 1 (statement 0)])
      (declarations ++ [⟨.axiomDecl 1 (statement 0), false⟩]) none := checked _ _ _ (by decide +kernel)

theorem expected_axiom_kind_is_not_silently_changed :
    verified (specification ++ [.axiomDecl 1 (statement 0)])
      (declarations ++ [⟨.theoremDecl 1 (statement 0) [] witness, false⟩]) none :=
  checked _ _ _ (by decide +kernel)

theorem local_theorem_does_not_consume_an_expected_public_theorem :
    verified (specification ++ [.theoremDecl 1 (statement 0)])
      (declarations ++ [⟨.theoremDecl 1 (statement 0) [] witness, true⟩]) none :=
  checked _ _ _ (by decide +kernel)

theorem matching_theorem_payload_cannot_bypass_its_proof :
    verified (specification ++ [.theoremDecl 1 (statement 0)])
      (declarations ++ [⟨.theoremDecl 1 (statement 0) [] (.theoremApp 1 [] []), false⟩]) none :=
  checked _ _ _ (by decide +kernel)

theorem local_theorem_cannot_justify_itself :
    verified specification (declarations ++ [⟨.theoremDecl 1 (statement 0) [] (.theoremApp 1 [] []), true⟩]) none :=
  checked _ _ _ (by decide +kernel)

theorem matching_declaration_does_not_make_an_invalid_term_admissible :
    verified [.term 0 constant] [⟨.term 0 constant, false⟩] none := checked _ _ _ (by decide +kernel)

theorem omitted_definition_body_may_be_filled :
    verified (specification ++ [.definition 1 constant none])
      (declarations ++ [⟨.definition 1 constant ⟨[], .term 0⟩, false⟩])
      (some { declared with terms := [(1, constant), (0, constant)], definitions := [(1, ⟨[], .term 0⟩)] }) :=
  checked _ _ _ (by decide +kernel)

theorem explicit_definition_body_must_match :
    verified (specification ++ [.definition 1 constant (some ⟨[], .term 0⟩)])
      (declarations ++ [⟨.definition 1 constant ⟨[], .term 0⟩, false⟩])
      (some { declared with terms := [(1, constant), (0, constant)], definitions := [(1, ⟨[], .term 0⟩)] }) :=
  checked _ _ _ (by decide +kernel)

theorem another_admissible_body_cannot_replace_the_expected_body :
    verified (specification ++ [.term 2 constant, .definition 1 constant (some ⟨[], .term 0⟩)])
      (declarations ++ [⟨.term 2 constant, false⟩, ⟨.definition 1 constant ⟨[], .term 2⟩, false⟩]) none :=
  checked _ _ _ (by decide +kernel)

theorem omitted_body_does_not_authorize_recursive_self_reference :
    verified (specification ++ [.definition 1 constant none])
      (declarations ++ [⟨.definition 1 constant ⟨[], .term 1⟩, false⟩]) none :=
  checked _ _ _ (by decide +kernel)

theorem sort_flags_are_part_of_the_specification :
    verified [.sort 0 { provable := true, strict := true }] [⟨.sort 0 proposition, false⟩] none :=
  checked _ _ _ (by decide +kernel)

theorem dependencies_are_part_of_the_specification :
    verified (specification ++ [.term 1 ⟨[.bound 0], 0, ∅⟩])
      (declarations ++ [⟨.term 1 ⟨[.bound 0], 0, {0}⟩, false⟩]) none :=
  checked _ _ _ (by decide +kernel)

theorem hypothesis_order_is_part_of_the_specification :
    verified (specification ++ [.term 1 constant,
        .axiomDecl 1 ⟨[], [.term 0, .term 1], .term 0⟩])
      (declarations ++ [⟨.term 1 constant, false⟩,
        ⟨.axiomDecl 1 ⟨[], [.term 1, .term 0], .term 0⟩, false⟩]) none :=
  checked _ _ _ (by decide +kernel)

theorem exact_specification_axioms_survive_auxiliary_proof :
    SpecificationAdmission.declarationAxioms
      (declarations ++ [⟨.theoremDecl 1 (statement 0) [] witness, true⟩]) =
      SpecificationAdmission.specificationAxioms specification :=
  verified_axioms_exact local_proved_theorem_adds_no_assumption

theorem accepted_theory_is_well_formed : Theory.WellFormed derived :=
  verified_wellFormed public_theorem_has_checked_proof

theorem successful_verification_cannot_also_refuse : ¬ verified specification declarations none := by
  intro refused
  have same := encodeTheoryResult_injective (refused.deterministic exact_public_declarations)
  cases same

theorem zero_fuel_is_exhaustion :
    apply P H 0 "mm0:spec-verify" [encodeEntries specification, encodeProofDeclarations declarations] = .exhausted := rfl

theorem direct_empty_verification :
    apply P H 9 "mm0:spec-verify" [encodeEntries [], encodeProofDeclarations []] =
      .value (encodeTheoryResult (some {})) := by
  rw [specification_apply _ (by decide)]
  rfl

end Mettapedia.Languages.MM0.Presentation.ComputationalSpecification.Controls
