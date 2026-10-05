import Mettapedia.Languages.MM0.Kernel.ProofSharing
import Mettapedia.Languages.MM0.Kernel.SpecificationChecking

/-!
# Admitting MM0 theorems with checked local sharing

The local store retains submitted initializers and a submitted root. Admission
checks them in the preceding theory, then discharges saved conclusions by cut.
The resulting theory and public specification entry are exactly the existing
admission system's. The existential ordinary witness below is logical evidence;
the runtime need not construct an expanded proof tree.

This module does not establish a byte decoder or MeTTa execution theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

structure SharedProof where
  saved : List (Preterm × ProofWitness)
  root : ProofWitness

namespace SharedProof

def Checks (theory : Theory) (declaration : TheoremDecl) (dummies : List Nat)
    (proof : SharedProof) : Prop :=
  SavedWitnessesChecked theory.termSignature theory.definitionSignature theory.theoremSignature
      (Admission.proofContext declaration dummies) declaration.hypotheses proof.saved ∧
    ProofWitness.check theory.termSignature theory.definitionSignature theory.theoremSignature
      (Admission.proofContext declaration dummies)
      (declaration.hypotheses ++ proof.saved.map Prod.fst) proof.root declaration.conclusion = true

theorem empty_iff (theory : Theory) (declaration : TheoremDecl) (dummies : List Nat)
    (root : ProofWitness) :
    Checks theory declaration dummies ⟨[], root⟩ ↔
      ProofWitness.Checks theory.termSignature theory.definitionSignature theory.theoremSignature
        (Admission.proofContext declaration dummies) declaration.hypotheses root declaration.conclusion := by
  simp only [Checks, List.map_nil, List.append_nil]
  constructor
  · intro checked
    exact (ProofWitness.check_iff _ _ _ _ _ _ _).mp checked.2
  · intro checked
    exact ⟨.nil, (ProofWitness.check_iff _ _ _ _ _ _ _).mpr checked⟩

theorem Checks.derives {theory : Theory} {declaration : TheoremDecl} {dummies : List Nat}
    {proof : SharedProof} (checked : Checks theory declaration dummies proof) :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature
      (Admission.proofContext declaration dummies) declaration.hypotheses declaration.conclusion :=
  checked.1.root_sound checked.2

/-- Formation reads the preceding theory independently of the proof store. -/
structure Formation (theory : Theory) (index : Nat) (declaration : TheoremDecl)
    (dummies : List Nat) : Prop where
  fresh : theory.theoremSignature index = none
  statement : TheoremDecl.Admissible theory.sortSignature theory.termSignature declaration
  dummySorts : ∀ sort ∈ dummies, ∃ info, theory.sortSignature sort = some info ∧
    info.strict = false ∧ info.free = false

theorem Formation.authorizes {theory : Theory} {index : Nat} {declaration : TheoremDecl}
    {dummies : List Nat} (formed : Formation theory index declaration dummies)
    {proof : SharedProof} (checked : Checks theory declaration dummies proof) :
    ∃ witness, Admission.Authorized theory (.theoremDecl index declaration dummies witness) := by
  obtain ⟨witness, justified⟩ := checked.derives.certificate_exists
  exact ⟨witness, .theoremDecl formed.fresh formed.statement formed.dummySorts justified⟩

/-- Sharing preserves and reflects the original admission relation, including
all formation conditions. The converse uses the very same ordinary witness. -/
theorem authorized_iff (theory : Theory) (index : Nat) (declaration : TheoremDecl)
    (dummies : List Nat) :
    (∃ witness, Admission.Authorized theory (.theoremDecl index declaration dummies witness)) ↔
      Formation theory index declaration dummies ∧
        ∃ proof, Checks theory declaration dummies proof := by
  constructor
  · rintro ⟨witness, authorized⟩
    cases authorized with
    | theoremDecl fresh statement dummySorts checked =>
        exact ⟨⟨fresh, statement, dummySorts⟩,
          ⟨⟨[], witness⟩, (empty_iff theory declaration dummies witness).mpr checked⟩⟩
  · rintro ⟨formed, proof, checked⟩
    exact formed.authorizes checked

def published (theory : Theory) (index : Nat) (declaration : TheoremDecl) : Theory :=
  { theory with theorems := (index, declaration) :: theory.theorems }

theorem Formation.theory_step {theory : Theory} {index : Nat} {declaration : TheoremDecl}
    {dummies : List Nat} (formed : Formation theory index declaration dummies)
    {proof : SharedProof} (checked : Checks theory declaration dummies proof) :
    ∃ witness, Theory.Step theory (.theoremDecl index declaration dummies witness)
      (published theory index declaration) := by
  obtain ⟨witness, authorized⟩ := formed.authorizes checked
  exact ⟨witness, .intro authorized⟩

/-- A public theorem consumes its fixed expected entry after checking. -/
theorem Formation.public_step {theory : Theory} {index : Nat} {declaration : TheoremDecl}
    {dummies : List Nat} {pending : List SpecificationEntry}
    (formed : Formation theory index declaration dummies)
    {proof : SharedProof} (checked : Checks theory declaration dummies proof) :
    ∃ witness, SpecificationAdmission.Step
      ⟨theory, .theoremDecl index declaration :: pending⟩
      ⟨.theoremDecl index declaration dummies witness, false⟩
      ⟨published theory index declaration, pending⟩ := by
  obtain ⟨witness, step⟩ := formed.theory_step checked
  exact ⟨witness, .publicDecl (.theoremDecl index declaration dummies witness) step⟩

/-- A local proved theorem consumes no expected entry and adds no axiom. -/
theorem Formation.local_step {theory : Theory} {index : Nat} {declaration : TheoremDecl}
    {dummies : List Nat} {pending : List SpecificationEntry}
    (formed : Formation theory index declaration dummies)
    {proof : SharedProof} (checked : Checks theory declaration dummies proof) :
    ∃ witness, SpecificationAdmission.Step ⟨theory, pending⟩
      ⟨.theoremDecl index declaration dummies witness, true⟩
      ⟨published theory index declaration, pending⟩ := by
  obtain ⟨witness, step⟩ := formed.theory_step checked
  exact ⟨witness, .auxiliary (.theoremDecl index declaration dummies witness) step⟩

theorem published_preserves_sorts (theory : Theory) (index : Nat) (declaration : TheoremDecl) :
    (published theory index declaration).sorts = theory.sorts := rfl

theorem published_preserves_terms (theory : Theory) (index : Nat) (declaration : TheoremDecl) :
    (published theory index declaration).terms = theory.terms := rfl

theorem published_preserves_definitions (theory : Theory) (index : Nat) (declaration : TheoremDecl) :
    (published theory index declaration).definitions = theory.definitions := rfl

end SharedProof
end Mettapedia.Languages.MM0.Kernel
