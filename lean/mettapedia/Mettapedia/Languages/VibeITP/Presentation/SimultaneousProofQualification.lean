import Mettapedia.Languages.VibeITP.Presentation.SimultaneousProofExecution
import Mettapedia.Languages.VibeITP.Presentation.SimultaneousCompleteness
import Mettapedia.GSLT.LanguageDef.AuthoredComputation
import Mettapedia.GSLT.LanguageDef.SemanticEvidence

/-! The complete authored v2 witness evaluator is a computed leaf of the
actual validated static v2 calculus. Theory dependencies are recovered from
the hosted allocation table. A leaf retains its supplied witness, claimed
answer and execution fuel. Scope equivalence follows from constructed source
derivations, not from an assumed replayability field. -/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalProofsV2

open ComputationalData ComputationalShift ComputationalProofs
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves
open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.LanguageDef.SemanticEvidence
open Mettapedia.GSLT.LanguageDef.KernelAuthority

def suppliedProofSystem (theory : Spec.Theory) : NativeProofSystem Spec.Term where
  ProofObject := SimultaneousProofs.Witness
  Judges := SimultaneousProofs.Witness.Checks theory

def suppliedProofKernel (theory : Spec.Theory) : NativeProofKernel (suppliedProofSystem theory) where
  decide claim witness := SimultaneousProofs.Witness.check theory witness claim
  correct claim witness := SimultaneousProofs.Witness.check_iff theory witness claim

def suppliedProofFibre (theory : Spec.Theory) :
    CertificateEquivalence (suppliedProofKernel theory).toChecker (suppliedProofSystem theory) :=
  (suppliedProofKernel theory).certificateEquivalence

theorem supplied_authority {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated) :
    (suppliedProofKernel theory).toChecker.Authority (Spec.DerivesV2 theory) where
  sound := fun _ _ accepted => SimultaneousProofs.Witness.check_sound accepted
  complete := fun claim derived => (SimultaneousProofs.derives_iff_checked hosted claim).mp derived

def queryArguments (theory : Spec.Theory) (allocated : Nat) (witness : SimultaneousProofs.Witness) : List Term :=
  [encodeTable (allocatedSnapshot theory allocated), encodeAxioms theory.axioms,
    encodeDefinitions theory.definitions, encodeWitness witness]

def authoredComputation {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated) :
    AuthoredComputation SimultaneousProofs.Witness Spec.Term where
  relation := SimultaneousProofs.Witness.Checks theory
  program := wholeProgram
  host := productDivisionHost
  head := "vibe:proof-v2-query"
  encodeQuery := queryArguments theory allocated
  encodeAnswer := encodeResult
  accepts := by
    intro witness answer
    simpa only [queryArguments, theoryOf_allocatedSnapshot hosted] using
      proofQuery_accepts_iff (allocatedSnapshot theory allocated) theory.axioms theory.definitions witness answer
  refuses := by
    intro witness
    simpa only [queryArguments, theoryOf_allocatedSnapshot hosted, encodeResult] using
      proofQuery_refuses_iff (allocatedSnapshot theory allocated) theory.axioms theory.definitions witness

def qualification {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated) :
    Qualification (authoredComputation hosted) (SimultaneousPresentation.validatedV2 theory allocated) where
  judgment := fun _ answer => jThm (encTerm theory.sig answer)
  derivable := by
    intro witness answer checked
    obtain ⟨article, accepted⟩ :=
      (SimultaneousPresentation.derivesV2_iff_checkRaw hosted answer).mp checked.derives
    exact checkRaw_soundness accepted

theorem authored_kernel_exact {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated)
    (witness : SimultaneousProofs.Witness) (claim : Spec.Term) :
    Applies wholeProgram productDivisionHost "vibe:check-proof-v2"
      (queryArguments theory allocated witness ++ [encode claim]) (.sym "True") ↔
      (suppliedProofSystem theory).Judges witness claim := by
  simpa only [queryArguments, List.cons_append, List.nil_append, suppliedProofSystem,
    theoryOf_allocatedSnapshot hosted] using
      checkProof_accepts_iff (allocatedSnapshot theory allocated) theory.axioms theory.definitions witness claim

theorem supplied_leaf_exact {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated)
    (leaf : Leaf SimultaneousProofs.Witness Spec.Term) (goal : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    InferenceComputedLeaves.check (SimultaneousPresentation.validatedV2 theory allocated)
      (qualification hosted).computation.evaluate goal (.computed leaf) = true ↔
      (authoredComputation hosted).runs leaf = true ∧ goal = jThm (encTerm theory.sig leaf.answer) :=
  (qualification hosted).computed_accepted_iff leaf goal

theorem supplied_leaf_derives {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated)
    {leaf : Leaf SimultaneousProofs.Witness Spec.Term} {goal : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (accepted : InferenceComputedLeaves.check (SimultaneousPresentation.validatedV2 theory allocated)
      (qualification hosted).computation.evaluate goal (.computed leaf) = true) :
    SimultaneousProofs.Witness.Checks theory leaf.query leaf.answer ∧
      Spec.DerivesV2 theory leaf.answer ∧ goal = jThm (encTerm theory.sig leaf.answer) := by
  obtain ⟨related, same⟩ := (qualification hosted).computed_accepted_relation accepted
  exact ⟨related, related.derives, same⟩

theorem scope_exact {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated)
    (goal : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    (∃ proof, InferenceComputedLeaves.check (SimultaneousPresentation.validatedV2 theory allocated)
      (qualification hosted).computation.evaluate goal proof = true) ↔
      ∃ article, checkRaw (SimultaneousPresentation.validatedV2 theory allocated) goal article = true :=
  (qualification hosted).accepted_iff_replay goal

theorem checked_witness_has_leaf {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated)
    {witness : SimultaneousProofs.Witness} {answer : Spec.Term}
    (checked : SimultaneousProofs.Witness.Checks theory witness answer) :
    ∃ fuel, InferenceComputedLeaves.check (SimultaneousPresentation.validatedV2 theory allocated)
      (qualification hosted).computation.evaluate (jThm (encTerm theory.sig answer))
      (.computed ⟨witness, answer, fuel⟩) = true :=
  (qualification hosted).computed_complete checked

theorem mixed_proof_derives {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated)
    {answer : Spec.Term} {proof : CompactProof (Leaf SimultaneousProofs.Witness Spec.Term)}
    (accepted : InferenceComputedLeaves.check (SimultaneousPresentation.validatedV2 theory allocated)
      (qualification hosted).computation.evaluate (jThm (encTerm theory.sig answer)) proof = true) :
    Spec.DerivesV2 theory answer := by
  obtain ⟨article, checked⟩ := InferenceComputedLeaves.accepted_has_replay (qualification hosted).computation accepted
  exact SimultaneousPresentation.checkRaw_soundV2 hosted checked

#print axioms qualification
#print axioms scope_exact
#print axioms mixed_proof_derives

end Mettapedia.Languages.VibeITP.Presentation.ComputationalProofsV2
