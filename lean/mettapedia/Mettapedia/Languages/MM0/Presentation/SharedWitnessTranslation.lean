import Mettapedia.Languages.MM0.Presentation.SharedCertificates
import Mettapedia.Languages.MM0.Presentation.CalculusWitness

/-!
# Supplied shared witnesses in the MM0 service

Every saved witness is translated in the hypothesis scope preceding it. The
same claimed conclusion remains attached to it. Preservation and reflection
therefore apply to the submitted initializers and root, including unused
initializers; they do not merely assert existence of some proof of the result.
Raw name resolution and physical MeTTa execution remain separate boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.SharedCertificates

open Kernel Calculus ComputationalCalculus
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

def translatedEntries (theory : Theory) (fuel : Nat) (context : Context)
    (hypotheses : List Preterm) (saved : List (Preterm × ProofWitness)) :
    List (Preterm × Certificate theory) :=
  saved.mapIdx fun index entry => (entry.1, Calculus.Witness.translate theory fuel context
    (hypotheses ++ (saved.take index).map Prod.fst) entry.2)

@[simp] theorem translatedEntries_claims (theory : Theory) (fuel : Nat) (context : Context)
    (hypotheses : List Preterm) (saved : List (Preterm × ProofWitness)) :
    (translatedEntries theory fuel context hypotheses saved).map Prod.fst = saved.map Prod.fst := by
  apply List.ext_getElem?
  intro index
  simp only [translatedEntries, List.getElem?_map, List.getElem?_mapIdx]
  cases saved[index]? <;> rfl

theorem translatedEntries_snoc (theory : Theory) (fuel : Nat) (context : Context)
    (hypotheses : List Preterm) (before : List (Preterm × ProofWitness))
    (expression : Preterm) (witness : ProofWitness) :
    translatedEntries theory fuel context hypotheses (before ++ [(expression, witness)]) =
      translatedEntries theory fuel context hypotheses before ++
        [(expression, Calculus.Witness.translate theory fuel context
          (hypotheses ++ before.map Prod.fst) witness)] := by
  unfold translatedEntries
  rw [List.mapIdx_concat]
  simp only [List.take_append_length]
  congr 1
  apply List.mapIdx_eq_mapIdx_iff.mpr
  intro index bounded
  rw [List.take_append_of_le_length (Nat.le_of_lt bounded)]

theorem translated_witness_iff (theory : Theory) (fuel : Nat) (context : Context)
    (hypotheses : List Preterm) (witness : ProofWitness) (expression : Preterm) :
    Accepted theory context hypotheses expression
        (Calculus.Witness.translate theory fuel context hypotheses witness) ↔
      ProofWitness.Checks theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses witness expression := by
  have called : "mm0:certificate" ∈ calculusProgram.calledHeads := by decide +kernel
  unfold Accepted
  rw [Service.calculus_returns _ called]
  exact (witness_accepted_iff theory fuel context hypotheses witness expression).symm

private theorem store_snoc_iff (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (before : List (Preterm × Certificate theory)) (expression : Preterm)
    (certificate : Certificate theory) :
    StoreChecked theory context hypotheses (before ++ [(expression, certificate)]) ↔
      StoreChecked theory context hypotheses before ∧
        Accepted theory context (hypotheses ++ before.map Prod.fst) expression certificate := by
  constructor
  · intro checked
    generalize same : before ++ [(expression, certificate)] = saved at checked
    cases checked with
    | nil => simp at same
    | record prior accepted =>
        obtain ⟨rfl, pair⟩ := List.append_singleton_inj.mp same
        cases pair
        exact ⟨prior, accepted⟩
  · rintro ⟨prior, accepted⟩
    exact .record prior accepted

private theorem witnesses_snoc_iff (theory : Theory) (context : Context)
    (hypotheses : List Preterm) (before : List (Preterm × ProofWitness))
    (expression : Preterm) (witness : ProofWitness) :
    SavedWitnessesChecked theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses (before ++ [(expression, witness)]) ↔
      SavedWitnessesChecked theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses before ∧
      ProofWitness.check theory.termSignature theory.definitionSignature theory.theoremSignature
        context (hypotheses ++ before.map Prod.fst) witness expression = true := by
  constructor
  · intro checked
    generalize same : before ++ [(expression, witness)] = saved at checked
    cases checked with
    | nil => simp at same
    | record prior accepted =>
        obtain ⟨rfl, pair⟩ := List.append_singleton_inj.mp same
        cases pair
        exact ⟨prior, accepted⟩
  · rintro ⟨prior, accepted⟩
    exact .record prior accepted

theorem translated_store_iff (theory : Theory) (fuel : Nat) (context : Context)
    (hypotheses : List Preterm) (saved : List (Preterm × ProofWitness)) :
    StoreChecked theory context hypotheses (translatedEntries theory fuel context hypotheses saved) ↔
      SavedWitnessesChecked theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses saved := by
  induction saved using List.reverseRecOn with
  | nil =>
      simp only [translatedEntries, List.mapIdx_nil]
      exact ⟨fun _ => .nil, fun _ => .nil⟩
  | @append_singleton before entry ih =>
      obtain ⟨expression, witness⟩ := entry
      rw [translatedEntries_snoc, store_snoc_iff, witnesses_snoc_iff, ih,
        translatedEntries_claims, translated_witness_iff,
        ProofWitness.check_iff]

/-- Exact preservation and reflection for every submitted shared proof. -/
theorem shared_witness_iff (theory : Theory) (fuel : Nat) (declaration : TheoremDecl)
    (dummies : List Nat) (proof : SharedProof) :
    SharedProof.Checks theory declaration dummies proof ↔
      StoreChecked theory (Admission.proofContext declaration dummies) declaration.hypotheses
          (translatedEntries theory fuel (Admission.proofContext declaration dummies)
            declaration.hypotheses proof.saved) ∧
      Accepted theory (Admission.proofContext declaration dummies)
        (declaration.hypotheses ++ proof.saved.map Prod.fst) declaration.conclusion
        (Calculus.Witness.translate theory fuel (Admission.proofContext declaration dummies)
          (declaration.hypotheses ++ proof.saved.map Prod.fst) proof.root) := by
  rw [SharedProof.Checks, translated_store_iff, translated_witness_iff, ProofWitness.check_iff]

end Mettapedia.Languages.MM0.Presentation.SharedCertificates
