import Mettapedia.Languages.MM0.Presentation.AdmissionExecution

/-! # Exact sequential admission and preservation of the admitted theory -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalAdmission

open Kernel ComputationalContext ComputationalTyping ComputationalDefinitions ComputationalArguments
open ComputationalConversion ComputationalProof
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => admissionProgram
local notation "H" => dataEqualityHost

theorem check_result_exact (theory : Theory) (admission : Admission) (result : Term) :
    Applies P H "mm0:admission-check" [encodeTheory theory, encodeAdmission admission] result ↔
      result = boolean (admission.check theory) := by
  constructor
  · exact fun run => run.deterministic (check_computes theory admission)
  · rintro rfl; exact check_computes theory admission

theorem check_refuses_iff (theory : Theory) (admission : Admission) :
    Applies P H "mm0:admission-check" [encodeTheory theory, encodeAdmission admission] (.sym "False") ↔
      ¬ Admission.Authorized theory admission := by
  rw [check_result_exact, ← Admission.check_iff]
  cases admission.check theory <;> simp [boolean]

theorem step_result_exact (theory : Theory) (admission : Admission) (result : Term) :
    Applies P H "mm0:admission-step" [encodeTheory theory, encodeAdmission admission] result ↔
      result = encodeTheoryResult (theory.step? admission) := by
  constructor
  · exact fun run => run.deterministic (step_computes theory admission)
  · rintro rfl; exact step_computes theory admission

theorem step_accepts_iff (before after : Theory) (admission : Admission) :
    Applies P H "mm0:admission-step" [encodeTheory before, encodeAdmission admission]
      (encodeTheoryResult (some after)) ↔ Theory.Step before admission after := by
  rw [step_result_exact, encodeTheoryResult_injective.eq_iff, eq_comm, Theory.step_eq_some_iff]

theorem step_refuses_iff (theory : Theory) (admission : Admission) :
    Applies P H "mm0:admission-step" [encodeTheory theory, encodeAdmission admission] (.sym "None") ↔
      ¬ Admission.Authorized theory admission := by
  change Applies P H _ _ (encodeTheoryResult none) ↔ _
  rw [step_result_exact, encodeTheoryResult_injective.eq_iff, ← Admission.check_iff]
  unfold Theory.step?
  cases admission.check theory <;> simp

theorem run_result_exact (theory : Theory) (admissions : List Admission) (result : Term) :
    Applies P H "mm0:admission-run" [encodeTheory theory, encodeAdmissions admissions] result ↔
      result = encodeTheoryResult (theory.run? admissions) := by
  constructor
  · exact fun run => run.deterministic (run_computes theory admissions)
  · rintro rfl; exact run_computes theory admissions

theorem run_accepts_iff (before after : Theory) (admissions : List Admission) :
    Applies P H "mm0:admission-run" [encodeTheory before, encodeAdmissions admissions]
      (encodeTheoryResult (some after)) ↔ Theory.Runs before admissions after := by
  rw [run_result_exact, encodeTheoryResult_injective.eq_iff, eq_comm, Theory.run_eq_some_iff]

theorem start_result_exact (admissions : List Admission) (result : Term) :
    Applies P H "mm0:admission-start" [encodeAdmissions admissions] result ↔
      result = encodeTheoryResult (Theory.run? {} admissions) := by
  constructor
  · exact fun run => run.deterministic (start_computes admissions)
  · rintro rfl; exact start_computes admissions

theorem start_accepts_iff (admissions : List Admission) (after : Theory) :
    Applies P H "mm0:admission-start" [encodeAdmissions admissions] (encodeTheoryResult (some after)) ↔
      Theory.Runs {} admissions after := by
  rw [start_result_exact, encodeTheoryResult_injective.eq_iff, eq_comm, Theory.run_eq_some_iff]

theorem start_refuses_iff (admissions : List Admission) :
    Applies P H "mm0:admission-start" [encodeAdmissions admissions] (.sym "None") ↔
      ¬ ∃ after, Theory.Runs {} admissions after := by
  change Applies P H _ _ (encodeTheoryResult none) ↔ _
  simp only [start_result_exact, encodeTheoryResult_injective.eq_iff, ← Theory.run_eq_some_iff]
  cases Theory.run? {} admissions <;> simp

theorem step_preserves_entries {before after : Theory} {admission : Admission}
    (accepted : Applies P H "mm0:admission-step" [encodeTheory before, encodeAdmission admission]
      (encodeTheoryResult (some after))) : Theory.Extends before after :=
  ((step_accepts_iff before after admission).mp accepted).extends

theorem theorem_checked_before_publication {before after : Theory} {index : Nat}
    {declaration : TheoremDecl} {dummies : List Nat} {proof : ProofWitness}
    (accepted : Applies P H "mm0:admission-step"
      [encodeTheory before, encodeAdmission (.theoremDecl index declaration dummies proof)]
      (encodeTheoryResult (some after))) :
    Derives before.termSignature before.definitionSignature before.theoremSignature
      (Admission.proofContext declaration dummies) declaration.hypotheses declaration.conclusion :=
  ((step_accepts_iff before after _).mp accepted).theorem_justified

theorem initial_run_wellFormed {admissions : List Admission} {theory : Theory}
    (accepted : Applies P H "mm0:admission-start" [encodeAdmissions admissions]
      (encodeTheoryResult (some theory))) : Theory.WellFormed theory :=
  ((start_accepts_iff admissions theory).mp accepted).wellFormed Theory.empty_wellFormed

theorem admitted_run_preserves_entries {before after : Theory} {admissions : List Admission}
    (accepted : Applies P H "mm0:admission-run" [encodeTheory before, encodeAdmissions admissions]
      (encodeTheoryResult (some after))) : Theory.Extends before after :=
  ((run_accepts_iff before after admissions).mp accepted).extends

theorem supplied_proof_computes (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (proof : ProofWitness) (claim : Preterm) :
    Applies P H "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim]
      (boolean (ProofWitness.check theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses proof claim)) := by
  rw [← theory_signature theory]
  exact proof_suffix_imported _ (by decide) _ _
    (ComputationalProof.check_computes theory.terms theory.definitions theory.theorems context hypotheses proof claim)

theorem supplied_proof_accepts_iff (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (proof : ProofWitness) (claim : Preterm) :
    Applies P H "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim] (.sym "True") ↔
      ProofWitness.Checks theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses proof claim := by
  constructor
  · intro run
    have same := run.deterministic (supplied_proof_computes theory context hypotheses proof claim)
    apply (ProofWitness.check_iff _ _ _ _ _ _ _).mp
    cases checked : ProofWitness.check theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses proof claim with
    | false => simp [checked, boolean] at same
    | true => rfl
  · intro checked
    simpa [(ProofWitness.check_iff _ _ _ _ _ _ _).mpr checked, boolean] using
      supplied_proof_computes theory context hypotheses proof claim

theorem derives_iff_supplied_proof (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (claim : Preterm) :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature context hypotheses claim ↔
      ∃ proof, Applies P H "mm0:check-proof"
        [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
          encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim] (.sym "True") := by
  constructor
  · intro derived
    obtain ⟨proof, checked⟩ := derived.certificate_exists
    exact ⟨proof, (supplied_proof_accepts_iff theory context hypotheses proof claim).mpr checked⟩
  · rintro ⟨proof, checked⟩
    exact ((supplied_proof_accepts_iff theory context hypotheses proof claim).mp checked).derives

theorem admitted_extension_preserves_supplied_proof {before after : Theory} {admissions : List Admission}
    (admitted : Applies P H "mm0:admission-run" [encodeTheory before, encodeAdmissions admissions]
      (encodeTheoryResult (some after)))
    {context : Context} {hypotheses : List Preterm} {proof : ProofWitness} {claim : Preterm}
    (checked : Applies P H "mm0:check-proof"
      [encodeTable before.terms, encodeDefinitions before.definitions, encodeTheorems before.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim] (.sym "True")) :
    Applies P H "mm0:check-proof"
      [encodeTable after.terms, encodeDefinitions after.definitions, encodeTheorems after.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim] (.sym "True") := by
  have extension := admitted_run_preserves_entries admitted
  exact (supplied_proof_accepts_iff after context hypotheses proof claim).mpr
    (((supplied_proof_accepts_iff before context hypotheses proof claim).mp checked).extendSignatures
      extension.terms extension.definitions extension.theorems)

theorem admitted_proof_is_statement {admissions : List Admission} {theory : Theory}
    (admitted : Applies P H "mm0:admission-start" [encodeAdmissions admissions]
      (encodeTheoryResult (some theory)))
    {context : Context} {hypotheses : List Preterm} {proof : ProofWitness} {claim : Preterm}
    (localStatements : ∀ hypothesis ∈ hypotheses,
      Preterm.IsStatement theory.sortSignature theory.termSignature context hypothesis)
    (checked : Applies P H "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim] (.sym "True")) :
    Preterm.IsStatement theory.sortSignature theory.termSignature context claim :=
  (initial_run_wellFormed admitted).derives_statement localStatements
    ((supplied_proof_accepts_iff theory context hypotheses proof claim).mp checked).derives

theorem start_completed_result (admissions : List Admission) (fuel : Nat)
    (finished : apply P H fuel "mm0:admission-start" [encodeAdmissions admissions] ≠ .exhausted) :
    apply P H fuel "mm0:admission-start" [encodeAdmissions admissions] =
      .value (encodeTheoryResult (Theory.run? {} admissions)) :=
  (start_computes admissions).completed fuel finished

theorem start_eventually_stable (admissions : List Admission) :
    ∃ needed, ∀ fuel, needed ≤ fuel → apply P H fuel "mm0:admission-start" [encodeAdmissions admissions] =
      .value (encodeTheoryResult (Theory.run? {} admissions)) :=
  (start_computes admissions).at_least

end Mettapedia.Languages.MM0.Presentation.ComputationalAdmission
