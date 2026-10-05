import Mettapedia.Languages.MM0.Kernel.TheoryAdmission

/-! # Sequential admission: freshness, prior authority and supplied proof evidence -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.TheoryAdmissionControls

private def initial : Theory :=
  { sorts := [(0, { provable := true }), (1, {})]
    terms := [(7, ⟨[], 0, ∅⟩), (8, ⟨[], 0, ∅⟩)] }

private def claim : TheoremDecl := ⟨[], [], .term 7⟩
private def otherClaim : TheoremDecl := ⟨[], [], .term 8⟩

theorem fresh_sort_accepted : Admission.check initial (.sort 2 {}) = true := by decide +kernel

theorem sort_overwrite_refuses :
    Admission.check initial (.sort 0 { strict := true }) = false := by decide +kernel

theorem term_overwrite_refuses :
    Admission.check initial (.term 7 ⟨[], 1, ∅⟩) = false := by decide +kernel

theorem fresh_term_accepted :
    Admission.check initial (.term 9 ⟨[], 1, ∅⟩) = true := by decide +kernel

theorem definition_uses_prior_symbol :
    Admission.check initial (.definition 9 ⟨[], 0, ∅⟩ ⟨[], .term 7⟩) = true := by decide +kernel

theorem self_definition_refuses :
    Admission.check initial (.definition 9 ⟨[], 0, ∅⟩ ⟨[], .term 9⟩) = false := by decide +kernel

theorem forward_definition_refuses :
    Admission.check initial (.definition 9 ⟨[], 0, ∅⟩ ⟨[], .term 10⟩) = false := by decide +kernel

theorem orphan_definition_overwrite_refuses :
    Admission.check { initial with definitions := [(9, ⟨[], .term 7⟩)] }
      (.definition 9 ⟨[], 0, ∅⟩ ⟨[], .term 8⟩) = false := by decide +kernel

theorem theorem_cannot_assume_its_conclusion :
    Admission.check initial (.theoremDecl 10 claim [] (.hyp 0)) = false := by decide +kernel

theorem theorem_cannot_call_itself :
    Admission.check initial (.theoremDecl 10 claim [] (.theoremApp 10 [] [])) = false := by decide +kernel

theorem theorem_cannot_call_future_theorem :
    Admission.check initial (.theoremDecl 10 claim [] (.theoremApp 11 [] [])) = false := by decide +kernel

/-- An explicitly declared axiom changes the assumptions; this is not a proof
that an arbitrary proof file may add it to a fixed specification. -/
theorem axiom_is_explicit_assumption :
    Admission.check initial (.axiomDecl 10 claim) = true := by decide +kernel

private def withAxiom : Theory := Admission.insert initial (.axiomDecl 10 claim)

theorem theorem_uses_prior_axiom :
    Admission.check withAxiom (.theoremDecl 11 claim [] (.theoremApp 10 [] [])) = true := by decide +kernel

theorem wrong_theorem_conclusion_refuses :
    Admission.check withAxiom (.theoremDecl 11 otherClaim [] (.theoremApp 10 [] [])) = false := by decide +kernel

theorem theorem_identifier_overwrite_refuses :
    Admission.check withAxiom (.theoremDecl 10 claim [] (.theoremApp 10 [] [])) = false := by decide +kernel

theorem theorem_local_hypothesis_is_available :
    Admission.check initial (.theoremDecl 11 ⟨[], [.term 7], .term 7⟩ [] (.hyp 0)) = true := by decide +kernel

theorem prior_theorem_used_by_later_theorem :
    (Theory.run? initial [
      .axiomDecl 10 claim,
      .theoremDecl 11 claim [] (.theoremApp 10 [] []),
      .theoremDecl 12 claim [] (.theoremApp 11 [] [])]).isSome = true := by decide +kernel

theorem reversing_admission_order_refuses :
    (Theory.run? initial [
      .theoremDecl 11 claim [] (.theoremApp 10 [] []),
      .axiomDecl 10 claim]).isNone = true := by decide +kernel

theorem duplicate_theorem_in_run_refuses :
    (Theory.run? initial [.axiomDecl 10 claim, .axiomDecl 10 otherClaim]).isNone = true := by decide +kernel

theorem checked_theorem_has_independent_prior_derivation :
    Derives withAxiom.termSignature withAxiom.definitionSignature withAxiom.theoremSignature
      [] [] (.term 7) := by
  apply Theory.Step.theorem_justified
    (index := 11) (declaration := claim) (dummies := [])
    (proof := .theoremApp 10 [] [])
  exact .intro ((Admission.check_iff _ _).mp theorem_uses_prior_axiom)

end Mettapedia.Languages.MM0.Kernel.TheoryAdmissionControls
