import Mettapedia.Languages.MM0.Presentation.AdmissionCorrespondence

/-! # Whole-run admission, previous-theory checking and publication controls -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalAdmission.Controls

open Kernel ComputationalContext ComputationalDeclaration
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => admissionProgram
local notation "H" => dataEqualityHost

private instance : DecidableEq Theory := fun left right =>
  decidable_of_iff (encodeTheory left = encodeTheory right) encodeTheory_injective.eq_iff

private def proposition : SortInfo := { provable := true }
private def constant : TermDecl := ⟨[], 0, ∅⟩
private def statement (symbol : Nat) : TheoremDecl := ⟨[], [], .term symbol⟩
private def declarations : List Admission :=
  [.sort 0 proposition, .term 0 constant, .axiomDecl 0 (statement 0)]
private def declared : Theory :=
  { sorts := [(0, proposition)], terms := [(0, constant)], theorems := [(0, statement 0)] }
private def derived : Theory := { declared with theorems := [(1, statement 0), (0, statement 0)] }
private def witness : ProofWitness := .theoremApp 0 [] []

private def run (admissions : List Admission) (result : Option Theory) : Prop :=
  Applies P H "mm0:admission-start" [encodeAdmissions admissions] (encodeTheoryResult result)

private theorem checked (admissions : List Admission) (result : Option Theory)
    (computed : Theory.run? {} admissions = result) : run admissions result := by
  simpa only [run, computed] using start_computes admissions

theorem empty_run_has_empty_theory : run [] (some {}) := checked _ _ (by decide +kernel)

theorem same_numeric_identity_in_distinct_namespaces : run declarations (some declared) :=
  checked _ _ (by decide +kernel)

theorem supplied_proof_is_checked_before_publishing :
    run (declarations ++ [.theoremDecl 1 (statement 0) [] witness]) (some derived) :=
  checked _ _ (by decide +kernel)

theorem duplicate_sort_refuses :
    run [.sort 0 proposition, .sort 0 proposition] none := checked _ _ (by decide +kernel)

theorem changed_sort_flags_cannot_overwrite :
    run [.sort 0 proposition, .sort 0 { strict := true }] none := checked _ _ (by decide +kernel)

theorem duplicate_term_refuses :
    run (declarations ++ [.term 0 constant]) none := checked _ _ (by decide +kernel)

theorem duplicate_axiom_refuses :
    run (declarations ++ [.axiomDecl 0 (statement 0)]) none := checked _ _ (by decide +kernel)

theorem theorem_cannot_overwrite_axiom :
    run (declarations ++ [.theoremDecl 0 (statement 0) [] witness]) none := checked _ _ (by decide +kernel)

theorem undeclared_sort_refuses : run [.term 0 constant] none := checked _ _ (by decide +kernel)

theorem candidate_update_requires_checked_entrypoint :
    Applies P H "mm0:admission-publish" [encodeTheory {}, encodeAdmission (.term 0 constant)]
      (encodeTheoryResult (some { terms := [(0, constant)] })) ∧ run [.term 0 constant] none :=
  ⟨publish_computes {} (.term 0 constant), undeclared_sort_refuses⟩

theorem later_sort_does_not_repair_earlier_declaration :
    run [.term 0 constant, .sort 0 proposition] none := checked _ _ (by decide +kernel)

theorem empty_theory_has_no_injected_theorem :
    run [.theoremDecl 0 (statement 0) [] witness] none := checked _ _ (by decide +kernel)

theorem theorem_cannot_justify_itself :
    run [.sort 0 proposition, .term 0 constant, .theoremDecl 0 (statement 0) [] witness] none :=
  checked _ _ (by decide +kernel)

theorem later_theorem_is_not_a_prior_premise :
    run (declarations ++ [.theoremDecl 1 (statement 0) [] (.theoremApp 2 [] []),
      .theoremDecl 2 (statement 0) [] witness]) none := checked _ _ (by decide +kernel)

theorem changed_claim_requires_its_own_proof :
    run (declarations ++ [.term 1 constant, .theoremDecl 1 (statement 1) [] witness]) none :=
  checked _ _ (by decide +kernel)

theorem strict_proof_dummy_refuses :
    run (declarations ++ [.sort 1 { strict := true }, .theoremDecl 1 (statement 0) [1] witness]) none :=
  checked _ _ (by decide +kernel)

theorem definition_is_checked_before_its_symbol_exists :
    run [.sort 0 proposition, .definition 0 constant ⟨[], .term 0⟩] none := checked _ _ (by decide +kernel)

theorem admitted_definition_is_available_to_later_conversion :
    run (declarations ++ [.definition 1 constant ⟨[], .term 0⟩,
      .theoremDecl 1 (statement 1) [] (.conversion (.symm (.unfold 1 [] [])) witness)])
      (some { declared with
        terms := [(1, constant), (0, constant)]
        definitions := [(1, ⟨[], .term 0⟩)]
        theorems := [(1, statement 1), (0, statement 0)] }) :=
  checked _ _ (by decide +kernel)

theorem changed_definition_invalidates_the_same_conversion_proof :
    run (declarations ++ [.term 2 constant, .definition 1 constant ⟨[], .term 2⟩,
      .theoremDecl 1 (statement 1) [] (.conversion (.symm (.unfold 1 [] [])) witness)]) none :=
  checked _ _ (by decide +kernel)

theorem well_typed_body_does_not_bypass_declaration_dependencies :
    run (declarations ++ [.definition 1 ⟨[], 0, {99}⟩ ⟨[], .term 0⟩]) none := checked _ _ (by decide +kernel)

theorem definition_cannot_replace_primitive_term :
    run (declarations ++ [.definition 0 constant ⟨[], .term 0⟩]) none := checked _ _ (by decide +kernel)

theorem sort_indices_do_not_wrap_at_machine_word :
    run [.sort 18446744073709551616 proposition, .term 0 ⟨[], 18446744073709551616, ∅⟩]
      (some { sorts := [(18446744073709551616, proposition)], terms := [(0, ⟨[], 18446744073709551616, ∅⟩)] }) :=
  checked _ _ (by decide +kernel)

theorem successful_run_cannot_also_refuse : ¬ run declarations none := by
  intro refused
  have same := encodeTheoryResult_injective (refused.deterministic same_numeric_identity_in_distinct_namespaces)
  cases same

theorem admission_exhaustion_is_not_rejection :
    apply P H 0 "mm0:admission-start" [encodeAdmissions declarations] = .exhausted := rfl

theorem direct_empty_run :
    apply P H 5 "mm0:admission-start" [encodeAdmissions []] = .value (encodeTheoryResult (some {})) := by
  rw [admission_apply _ (by decide)]
  rfl

theorem admitted_example_has_valid_stored_profiles : Theory.WellFormed derived :=
  initial_run_wellFormed supplied_proof_is_checked_before_publishing

end Mettapedia.Languages.MM0.Presentation.ComputationalAdmission.Controls
