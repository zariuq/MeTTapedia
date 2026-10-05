import Mettapedia.Languages.MM0.Kernel.TheoryInvariant
import Mettapedia.Languages.MM0.Kernel.ProofExtension

/-! # Whole-run admission and preservation controls -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.TheoryInvariantControls

private def claim : TheoremDecl := ⟨[], [], .term 7⟩
private def setup : List Admission :=
  [.sort 0 { provable := true }, .term 7 ⟨[], 0, ∅⟩, .axiomDecl 10 claim]
private def initial : Theory :=
  { sorts := [(0, { provable := true })]
    terms := [(7, ⟨[], 0, ∅⟩)]
    theorems := [(10, claim)] }

theorem setup_run : Theory.run? {} setup = some initial := by
  apply (Theory.run_eq_some_iff _ _ _).mpr
  exact .cons (.intro ((Admission.check_iff _ _).mp (by decide +kernel)))
    (.cons (.intro ((Admission.check_iff _ _).mp (by decide +kernel)))
      (.cons (.intro ((Admission.check_iff _ _).mp (by decide +kernel))) (.nil _)))

theorem setup_is_wellFormed : Theory.WellFormed initial :=
  Theory.run_from_empty_wellFormed setup_run

private def extension : Admission := .definition 9 ⟨[], 0, ∅⟩ ⟨[], .term 7⟩
private def extended : Theory := extension.insert initial

theorem definition_admission : Theory.Step initial extension extended :=
  .intro ((Admission.check_iff _ _).mp (by decide +kernel))

theorem extension_is_wellFormed : Theory.WellFormed extended :=
  definition_admission.wellFormed setup_is_wellFormed

theorem earlier_axiom_proof_accepts :
    ProofWitness.check initial.termSignature initial.definitionSignature initial.theoremSignature
      [] [] (.theoremApp 10 [] []) (.term 7) = true := by decide +kernel

theorem same_certificate_survives_extension :
    ProofWitness.check extended.termSignature extended.definitionSignature extended.theoremSignature
      [] [] (.theoremApp 10 [] []) (.term 7) = true :=
  definition_admission.extends.preserves_check earlier_axiom_proof_accepts

theorem checked_run_gives_statement :
    Preterm.IsStatement initial.sortSignature initial.termSignature [] (.term 7) :=
  Theory.checked_run_proof_is_statement setup_run (by simp) earlier_axiom_proof_accepts

theorem admitted_body_remains_typed :
    ∃ declaration, extended.termSignature 9 = some declaration ∧
      Definition.AdmissibleBody extended.sortSignature extended.termSignature declaration ⟨[], .term 7⟩ :=
  extension_is_wellFormed.definitions 9 _ (by rfl)

theorem admitted_unfolding_accepts :
    ConvWitness.conversion? extended.termSignature extended.definitionSignature [] (.unfold 9 [] []) =
      some ⟨.term 9, .term 7, 0⟩ := by decide +kernel

theorem return_dependency_is_unchanged :
    Preterm.freeVariables? initial.termSignature [] (.term 7) = some ∅ ∧
      Preterm.freeVariables? extended.termSignature [] (.term 7) = some ∅ := by decide +kernel

theorem missing_term_previously_refused :
    Preterm.infer initial.termSignature [] (.term 9) = none := by decide +kernel

/-- Preservation of successful evidence does not imply preservation of all refusals. -/
theorem newly_declared_term_now_accepted :
    Preterm.infer extended.termSignature [] (.term 9) = some ([], 0) := by decide +kernel

private def changedSort : Theory := Admission.insert initial (.sort 0 {})

theorem overwriting_sort_is_not_authorized :
    Admission.check initial (.sort 0 {}) = false := by decide +kernel

theorem unchecked_sort_overwrite_breaks_statement :
    Preterm.checkStatement changedSort.sortSignature changedSort.termSignature [] (.term 7) = false :=
  by decide +kernel

theorem unchecked_sort_overwrite_breaks_invariant : ¬ Theory.WellFormed changedSort := by
  intro valid
  have statement := (valid.theorems 10 claim (by rfl)).conclusion
  have accepted := (Preterm.checkStatement_iff _ _ _ _).mpr statement
  change Preterm.checkStatement changedSort.sortSignature changedSort.termSignature [] (.term 7) = true at accepted
  rw [unchecked_sort_overwrite_breaks_statement] at accepted
  contradiction

private def changedBody : Theory :=
  { extended with definitions := [(9, ⟨[], .term 9⟩)] }

theorem body_overwrite_would_change_conversion :
    ConvWitness.conversion? changedBody.termSignature changedBody.definitionSignature [] (.unfold 9 [] []) =
      some ⟨.term 9, .term 9, 0⟩ := by decide +kernel

theorem body_overwrite_fails_extension_contract : ¬ Theory.Extends extended changedBody := by
  intro preserves
  have unchanged := preserves.definitions 9 ⟨[], .term 7⟩ (by rfl)
  have actual : changedBody.definitionSignature 9 = some ⟨[], .term 9⟩ := rfl
  rw [actual] at unchanged
  have expressions := congrArg (fun body : Definition.Body => body.expression) (Option.some.inj unchanged)
  cases expressions

end Mettapedia.Languages.MM0.Kernel.TheoryInvariantControls
