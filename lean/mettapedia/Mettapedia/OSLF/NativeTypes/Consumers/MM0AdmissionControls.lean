import Mettapedia.OSLF.NativeTypes.Consumers.MM0Admission

/-!
# Supplied MM0 requests: proof validity, permission and physical authority

The same inhabited claim accepts its actual theorem witness and refuses a
submitted missing-hypothesis witness. Theorem publication separately rejects
an occupied declaration identifier, a missing public specification entry and
an undeclared dummy sort. Physical table readiness is supplied explicitly;
it is never used as a replacement for these logical conditions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Consumers.MM0Admission.Controls

open Mettapedia.Languages.MM0 Kernel MeTTa
open Mettapedia.Languages.MeTTa.PeTTa Eval Effects
open SessionInitialization (Spaces)
open AdmissionChecks (Ready)
open Mettapedia.GSLT.Dynamics.RelationalAnswerEvaluation
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

def spaces : Spaces :=
  ⟨.privateSpace 0, .privateSpace 1, .privateSpace 2, .privateSpace 3, .privateSpace 4, .privateSpace 5⟩
def info : SortInfo := {provable := true}
def primitive : TermDecl := ⟨[], 0, ∅⟩
def statement : TheoremDecl := ⟨[], [], .term 1⟩
def declarations : Theory :=
  {sorts := [(0, info)], terms := [(2, primitive), (1, primitive)], theorems := [(10, statement)]}
def logical : SpecificationAdmission.State := ⟨declarations, [.theoremDecl 12 statement]⟩
def initial : State :=
  {core := [], next := 6,
   spaces := fun index =>
     if index = 2 then SortFormation.rows declarations.sorts.reverse
     else if index = 3 then TableAccess.declarationRows declarations.terms.reverse
     else if index = 5 then Proof.theoremRows declarations.theorems.reverse
     else [],
   cells := fun name =>
     if name = InferenceCache.cell then some (handleValue spaces.cache)
     else if name = "mm0-proof-store" then some (handleValue spaces.proofs)
     else none, namedEmpty := [] }

theorem input : SharedService.Input spaces logical initial := by
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide +kernel⟩, ?_⟩, ?_, ?_⟩
  · simp [initial, spaces, logical, NamedSpaces.Store.read]
  · simp [initial, spaces, logical, NamedSpaces.Store.read]
  · simp [initial, spaces, logical, declarations, Unfolding.definitionRows, Store.rows, NamedSpaces.Store.read]
  · simp [initial, spaces, logical, NamedSpaces.Store.read]
  · intro key; by_cases same : 0 = key <;> simp [logical, declarations, same]
  · intro key
    by_cases two : 2 = key
    · subst key; decide +kernel
    · by_cases one : 1 = key
      · subst key; decide +kernel
      · simp [logical, declarations, two, one]
  · intro key; simp [logical, declarations]
  · intro key; by_cases same : 10 = key <;> simp [logical, declarations, same]
  · refine ⟨?_, [], ?_, InferenceCache.empty_valid _ _⟩ <;>
      simp [initial, spaces, NamedSpaces.Store.read]
  · simp [initial, spaces, InferenceCache.cell]
  · exact ⟨[], rfl, by simp [Effects.RowsHaveArity]⟩

def goodProof : ProofRequest := ⟨[], [], .theoremApp 10 [] [], .term 1⟩
def badProof : ProofRequest := {goodProof with witness := .hyp 0}
def wrongClaim : ProofRequest := {goodProof with claim := .term 2}
def submission : TheoremSubmission := ⟨false, 12, statement, [], goodProof.witness⟩
def staleIdentifier : TheoremSubmission := {submission with index := 10}
def illegalDummy : TheoremSubmission := {submission with dummies := [99]}
def badSubmission : TheoremSubmission := {submission with witness := badProof.witness}
def noPermission : SpecificationAdmission.State := ⟨declarations, []⟩

theorem finite_controls :
    proofCheck declarations goodProof = true ∧
    proofCheck declarations badProof = false ∧
    proofCheck declarations wrongClaim = false ∧
    submissionCheck logical submission = true ∧
    submissionCheck logical badSubmission = false ∧
    submissionCheck ⟨declarations, [.theoremDecl 10 statement]⟩ staleIdentifier = false ∧
    submissionCheck logical illegalDummy = false ∧
    submissionCheck noPermission submission = false ∧
    submissionCheck noPermission {submission with isLocal := true} = true := by
  decide +kernel

theorem proof_acceptance_does_not_admit_dummy :
    proofCheck declarations
      ⟨Admission.proofContext statement [99], [], goodProof.witness, statement.conclusion⟩ = true ∧
      submissionCheck logical illegalDummy = false := by
  decide +kernel

theorem good_supplied_witness_native :
    (gsltOSLF (evaluationGSLT (proofSource spaces))).satisfies (S := ()) (.request initial goodProof)
      (proofNativeType spaces declarations true).pred :=
  (proofCheck_native_exact spaces declarations initial input.ready goodProof true).mp finite_controls.1

/-- A valid derivation of the same claim does not rescue the submitted
missing-hypothesis witness. Both native outcomes describe actual source runs. -/
theorem another_derivation_does_not_rescue_submission :
    Derives declarations.termSignature declarations.definitionSignature declarations.theoremSignature
      [] [] (.term 1) ∧
    (gsltOSLF (evaluationGSLT (proofSource spaces))).satisfies (S := ()) (.request initial badProof)
      (proofNativeType spaces declarations false).pred ∧
    ¬ (gsltOSLF (evaluationGSLT (proofSource spaces))).satisfies (S := ()) (.request initial badProof)
      (proofNativeType spaces declarations true).pred := by
  refine ⟨ProofWitness.check_sound finite_controls.1, ?_, ?_⟩
  · exact (proofCheck_native_exact spaces declarations initial input.ready badProof false).mp finite_controls.2.1
  · exact rejected_witness_not_accepted spaces declarations initial input.ready badProof finite_controls.2.1

theorem submitted_theorem_publishes_native :
    (gsltOSLF (evaluationGSLT (serviceSource spaces logical))).satisfies (S := ())
      (.request initial submission) (publicationNativeType spaces logical).pred :=
  (submissionCheck_native_exact spaces logical initial input submission).mp finite_controls.2.2.2.1

theorem bad_submitted_theorem_cannot_publish :
    ¬ (gsltOSLF (evaluationGSLT (serviceSource spaces logical))).satisfies (S := ())
      (.request initial badSubmission) (publicationNativeType spaces logical).pred := by
  intro member
  have accepted := (submissionCheck_native_exact spaces logical initial input badSubmission).mpr member
  have rejected : submissionCheck logical badSubmission = false := by decide +kernel
  rw [rejected] at accepted
  cases accepted

theorem ready_tables_do_not_grant_public_permission :
    Ready spaces noPermission.theory initial ∧ proofCheck declarations goodProof = true ∧
    ¬ SharedService.Accepted spaces noPermission submission.command input.ready := by
  refine ⟨input.ready, finite_controls.1, ?_⟩
  intro accepted
  have checked := (submissionCheck_service spaces noPermission initial input.ready submission).mpr accepted
  have denied : submissionCheck noPermission submission = false := by decide +kernel
  rw [denied] at checked
  cases checked

def run : IO Unit := do
  let checks := [proofCheck declarations goodProof, !proofCheck declarations badProof,
    !proofCheck declarations wrongClaim, submissionCheck logical submission,
    !submissionCheck logical badSubmission,
    !submissionCheck ⟨declarations, [.theoremDecl 10 statement]⟩ staleIdentifier,
    !submissionCheck logical illegalDummy, !submissionCheck noPermission submission,
    submissionCheck noPermission {submission with isLocal := true},
    proofCheck declarations ⟨Admission.proofContext statement [99], [], goodProof.witness, statement.conclusion⟩]
  if !checks.all id then throw (IO.userError "MM0 supplied-request native controls failed")
  IO.println "MM0 native consumer: ten finite supplied-request controls; good witness accepted, bad submitted witness refused; public permission, freshness and dummy formation remain separate"

end Mettapedia.OSLF.NativeTypes.Consumers.MM0Admission.Controls
