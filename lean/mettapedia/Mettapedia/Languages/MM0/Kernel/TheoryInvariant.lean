import Mettapedia.Languages.MM0.Kernel.TheoryAdmission
import Mettapedia.Languages.MM0.Kernel.SignatureExtension

/-!
# Whole-theory preservation for sequential MM0 admission

The stored declaration profiles and definition bodies remain valid after each
checked extension. This supplies the theorem-signature premise of proof
statement preservation; it is not a claim of consistency of declared axioms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.Theory

structure WellFormed (theory : Theory) : Prop where
  terms : ∀ index declaration, theory.termSignature index = some declaration →
    TermDecl.Admissible theory.sortSignature declaration
  definitions : ∀ index body, theory.definitionSignature index = some body →
    ∃ declaration, theory.termSignature index = some declaration ∧
      Definition.AdmissibleBody theory.sortSignature theory.termSignature declaration body
  theorems : ∀ index declaration, theory.theoremSignature index = some declaration →
    TheoremDecl.Admissible theory.sortSignature theory.termSignature declaration

theorem empty_wellFormed : WellFormed ({} : Theory) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro index entry known <;> cases known

private theorem lookup_cons_cases {α : Type} {entries : List (Nat × α)}
    {index queried : Nat} {entry value : α}
    (known : ((index, entry) :: entries).lookup queried = some value) :
    (queried = index ∧ value = entry) ∨ entries.lookup queried = some value := by
  by_cases same : queried = index
  · subst queried
    have valueEq : entry = value := by simpa [List.lookup_cons] using known
    exact Or.inl ⟨rfl, valueEq.symm⟩
  · have unequal : (queried == index) = false := by simp [same]
    exact Or.inr (by simpa [List.lookup_cons, unequal] using known)

theorem Step.wellFormed {before after : Theory} {admission : Admission}
    (step : Step before admission after) (valid : WellFormed before) : WellFormed after := by
  cases step with
  | intro authorized =>
      have extension := Step.extends (Step.intro authorized)
      have oldTerms : ∀ index declaration, before.termSignature index = some declaration →
          TermDecl.Admissible (admission.insert before).sortSignature declaration :=
        fun index declaration known => (valid.terms index declaration known).extendSorts extension.sorts
      have oldDefinitions : ∀ index body, before.definitionSignature index = some body →
          ∃ declaration, (admission.insert before).termSignature index = some declaration ∧
            Definition.AdmissibleBody (admission.insert before).sortSignature
              (admission.insert before).termSignature declaration body := by
        intro index body known
        obtain ⟨declaration, declared, admitted⟩ := valid.definitions index body known
        exact ⟨declaration, extension.terms _ _ declared,
          admitted.extendSignatures extension.sorts extension.terms⟩
      have oldTheorems : ∀ index declaration, before.theoremSignature index = some declaration →
          TheoremDecl.Admissible (admission.insert before).sortSignature
            (admission.insert before).termSignature declaration :=
        fun index declaration known =>
          (valid.theorems index declaration known).extendSignatures extension.sorts extension.terms
      cases authorized with
      | sort fresh => exact ⟨oldTerms, oldDefinitions, oldTheorems⟩
      | term fresh admitted =>
          refine ⟨?_, oldDefinitions, oldTheorems⟩
          intro index declaration known
          rcases lookup_cons_cases known with ⟨rfl, rfl⟩ | old
          · exact admitted.extendSorts extension.sorts
          · exact oldTerms _ _ old
      | definition fresh freshBody admitted body =>
          refine ⟨?_, ?_, oldTheorems⟩
          · intro index declaration known
            rcases lookup_cons_cases known with ⟨rfl, rfl⟩ | old
            · exact admitted.extendSorts extension.sorts
            · exact oldTerms _ _ old
          · intro index stored known
            rcases lookup_cons_cases known with ⟨rfl, rfl⟩ | old
            · refine ⟨_, ?_, body.extendSignatures extension.sorts extension.terms⟩
              simp [termSignature, Admission.insert]
            · exact oldDefinitions _ _ old
      | axiomDecl fresh admitted =>
          refine ⟨oldTerms, oldDefinitions, ?_⟩
          intro index declaration known
          rcases lookup_cons_cases known with ⟨rfl, rfl⟩ | old
          · exact admitted.extendSignatures extension.sorts extension.terms
          · exact oldTheorems _ _ old
      | theoremDecl fresh admitted dummies proof =>
          refine ⟨oldTerms, oldDefinitions, ?_⟩
          intro index declaration known
          rcases lookup_cons_cases known with ⟨rfl, rfl⟩ | old
          · exact admitted.extendSignatures extension.sorts extension.terms
          · exact oldTheorems _ _ old

theorem Runs.wellFormed {before after : Theory} {admissions : List Admission}
    (runs : Runs before admissions after) (valid : WellFormed before) : WellFormed after := by
  induction runs with
  | nil => exact valid
  | cons step _ ih => exact ih (step.wellFormed valid)

theorem run_preserves_wellFormed {before after : Theory} {admissions : List Admission}
    (valid : WellFormed before) (success : run? before admissions = some after) :
    WellFormed after := ((run_eq_some_iff _ _ _).mp success).wellFormed valid

theorem run_from_empty_wellFormed {after : Theory} {admissions : List Admission}
    (success : run? {} admissions = some after) : WellFormed after :=
  run_preserves_wellFormed empty_wellFormed success

theorem WellFormed.derives_statement {theory : Theory} (valid : WellFormed theory)
    {context : Context} {hypotheses : List Preterm} {expression : Preterm}
    (localStatements : ∀ hypothesis ∈ hypotheses,
      Preterm.IsStatement theory.sortSignature theory.termSignature context hypothesis)
    (derived : Derives theory.termSignature theory.definitionSignature theory.theoremSignature
      context hypotheses expression) :
    Preterm.IsStatement theory.sortSignature theory.termSignature context expression :=
  derived.statement localStatements (fun index declaration known =>
    (valid.theorems index declaration known).conclusion)

/-- Statement validity now follows from an actual checked admission run,
without assuming that every stored theorem declaration has a valid profile. -/
theorem checked_run_proof_is_statement {theory : Theory} {admissions : List Admission}
    (success : run? {} admissions = some theory)
    {context : Context} {hypotheses : List Preterm} {proof : ProofWitness} {expression : Preterm}
    (localStatements : ∀ hypothesis ∈ hypotheses,
      Preterm.IsStatement theory.sortSignature theory.termSignature context hypothesis)
    (checked : ProofWitness.check theory.termSignature theory.definitionSignature
      theory.theoremSignature context hypotheses proof expression = true) :
    Preterm.IsStatement theory.sortSignature theory.termSignature context expression :=
  (run_from_empty_wellFormed success).derives_statement localStatements
    ((ProofWitness.check_iff _ _ _ _ _ _ _).mp checked).derives

end Mettapedia.Languages.MM0.Kernel.Theory
