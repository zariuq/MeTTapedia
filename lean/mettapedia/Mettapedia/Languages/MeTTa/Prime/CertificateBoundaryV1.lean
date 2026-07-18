import Mettapedia.Languages.MeTTa.Prime.FragmentAdequacyV1

/-!
# Prime certificate-boundary correspondence V1

This module independently reconstructs the certificate serialized and checked
by `prime_certificate_boundary_v1.metta`.  The certificate binds a source-
derived package, exact source snapshot, dialect, inert program pattern,
checked judgment, and raw derivation.  Its semantic theorem reduces accepted
canonical certificates to the independently defined fragment evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.CertificateBoundaryV1

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
open Mettapedia.Languages.MeTTa.Prime.PackageAuthority
open Mettapedia.Languages.MeTTa.Prime.FragmentAdequacyV1

structure SourceSnapshotV1 where
  format : String
  digest : String
deriving Repr, DecidableEq

structure SubjectMaterialV1 where
  format : String
  packageIdentity : PackageIdentityV1
  sourceSnapshot : SourceSnapshotV1
  dialect : String
  program : Pattern
  goal : Pattern
deriving Repr, DecidableEq

structure SubjectRefV1 where
  material : SubjectMaterialV1
  digest : String
  handle : String
deriving Repr, DecidableEq

structure CertificateMaterialV1 where
  format : String
  subject : SubjectRefV1
  goal : Pattern
  proof : RawProof
deriving Repr

structure CertificateV1 where
  material : CertificateMaterialV1
  digest : String
deriving Repr

def renderSourceDecl : SourceDecl → String
  | .equation .addZero => "(WexEquationV1 AddZeroV1)"
  | .equation .addSuccessor => "(WexEquationV1 AddSuccessorV1)"
  | .equation .lengthNil => "(WexEquationV1 LengthNilV1)"
  | .equation .lengthCons => "(WexEquationV1 LengthConsV1)"
  | .equation .pickAlternativeA =>
      "(WexEquationV1 PickAlternativeAV1)"
  | .equation .pickAlternativeB =>
      "(WexEquationV1 PickAlternativeBV1)"
  | .equation .pickAlternativeC =>
      "(WexEquationV1 PickAlternativeCV1)"
  | .equation .addSuccessorWrongSubstitution =>
      "(WexEquationV1 AddSuccessorWrongSubstitutionV1)"
  | .closure .mayEvalMembership =>
      "(WexClosureV1 MayEvalMembershipV1)"

def sourceBytes (source : List SourceDecl) : String :=
  renderList renderSourceDecl source

def sourceDigest (source : List SourceDecl) : String :=
  MeTTailCore.Crypto.SHA256.sha256Hex (sourceBytes source)

def renderPackageIdentity (identity : PackageIdentityV1) : String :=
  s!"(PackageIdentityV1 {quote identity.format} {quote identity.dialect} " ++
    s!"{quote identity.semanticVersion} {quote identity.digest})"

def renderSourceSnapshot (snapshot : SourceSnapshotV1) : String :=
  s!"(PrimeFragmentSourceSnapshotV1 {quote snapshot.format} " ++
    s!"{quote snapshot.digest})"

def renderSubjectMaterial (material : SubjectMaterialV1) : String :=
  s!"(PrimeFragmentSubjectMaterialV1 {quote material.format} " ++
    s!"{renderPackageIdentity material.packageIdentity} " ++
    s!"{renderSourceSnapshot material.sourceSnapshot} " ++
    s!"{quote material.dialect} {renderPattern material.program} " ++
    s!"{renderPattern material.goal})"

def renderSubjectRef (subject : SubjectRefV1) : String :=
  s!"(PrimeFragmentSubjectRefV1 {renderSubjectMaterial subject.material} " ++
    s!"{quote subject.digest} (SubjectLocalHandleV1 {quote subject.handle}))"

def renderCertificateMaterial (material : CertificateMaterialV1) : String :=
  s!"(PrimeFragmentCertificateMaterialV1 {quote material.format} " ++
    s!"{renderSubjectRef material.subject} {renderPattern material.goal} " ++
    s!"{renderRawProof material.proof})"

def renderCertificate (certificate : CertificateV1) : String :=
  s!"(PrimeFragmentCertificateV1 " ++
    s!"{renderCertificateMaterial certificate.material} " ++
    s!"{quote certificate.digest})"

def encodeProgram : {sort : ResultSort} → FragmentExpr sort → Pattern
  | _, .add left right => addP (encodeNat left) (encodeNat right)
  | _, .length value =>
      .apply "wex.length" [encodeList value]
  | _, .pick => pickP

def programGoalAgree : Pattern → Pattern → Bool
  | .apply "wex.add" arguments,
      .apply "wex1.Evals" [.apply "wex.add" goalArguments, _] =>
      arguments == goalArguments
  | .apply "wex.length" [input],
      .apply "wex2.LenIs" [goalInput, _] =>
      input == goalInput
  | .apply "wex.pick" [],
      .apply "wex3.MayEval" [.apply "wex.pick" [], _] => true
  | _, _ => false

@[simp] theorem programGoalAgree_encoded {sort : ResultSort}
    (expression : FragmentExpr sort) (value : FragmentValue sort) :
    programGoalAgree (encodeProgram expression)
      (encodeJudgment expression value) = true := by
  cases expression with
  | add left right =>
      cases value with
      | nat result =>
          change programGoalAgree
            (.apply "wex.add" [encodeNat left, encodeNat right])
            (.apply "wex1.Evals"
              [.apply "wex.add" [encodeNat left, encodeNat right],
               encodeNat result]) = true
          simp [programGoalAgree]
  | length input =>
      cases value with
      | nat result =>
          change programGoalAgree
            (.apply "wex.length" [encodeList input])
            (.apply "wex2.LenIs" [encodeList input, encodeNat result]) = true
          simp [programGoalAgree]
  | pick =>
      cases value with
      | pick result =>
          change programGoalAgree (.apply "wex.pick" [])
            (.apply "wex3.MayEval"
              [.apply "wex.pick" [], encodePick result]) = true
          simp [programGoalAgree]

def makeSourceSnapshot (source : List SourceDecl) : SourceSnapshotV1 :=
  { format := "prime-fragment-source-v1"
    digest := sourceDigest source }

def makeSubjectFromPatterns (source : List SourceDecl)
    (program goal : Pattern) : SubjectRefV1 :=
  let material : SubjectMaterialV1 :=
    { format := "prime-fragment-subject-v1"
      packageIdentity :=
        (packageFromSource source).identity
      sourceSnapshot := makeSourceSnapshot source
      dialect := "prime"
      program
      goal }
  let digest := MeTTailCore.Crypto.SHA256.sha256Hex
    (renderSubjectMaterial material)
  { material, digest, handle := digest }

def makeSubject {sort : ResultSort} (source : List SourceDecl)
    (expression : FragmentExpr sort) (value : FragmentValue sort) :
    SubjectRefV1 :=
  makeSubjectFromPatterns source (encodeProgram expression)
    (encodeJudgment expression value)

def subjectValid (source : List SourceDecl) (subject : SubjectRefV1) : Bool :=
  subject.material.format == "prime-fragment-subject-v1" &&
    subject.material.packageIdentity == (packageFromSource source).identity &&
    subject.material.sourceSnapshot == makeSourceSnapshot source &&
    subject.material.dialect == "prime" &&
    programGoalAgree subject.material.program subject.material.goal &&
    subject.digest == MeTTailCore.Crypto.SHA256.sha256Hex
      (renderSubjectMaterial subject.material) &&
    subject.handle == subject.digest

def makeCertificateFromPatterns (source : List SourceDecl)
    (program goal : Pattern) (proof : RawProof) : CertificateV1 :=
  let subject := makeSubjectFromPatterns source program goal
  let material : CertificateMaterialV1 :=
    { format := "prime-fragment-certificate-v1", subject, goal, proof }
  { material
    digest := MeTTailCore.Crypto.SHA256.sha256Hex
      (renderCertificateMaterial material) }

def makeCertificate {sort : ResultSort} (source : List SourceDecl)
    (expression : FragmentExpr sort) (value : FragmentValue sort)
    (proof : RawProof) : CertificateV1 :=
  makeCertificateFromPatterns source (encodeProgram expression)
    (encodeJudgment expression value) proof

/-- The runtime calibration admits exactly the one source whose package and
companion cache were proved adequate in `FragmentAdequacyV1`. -/
def certificateValid (source : List SourceDecl)
    (certificate : CertificateV1) : Bool :=
  source == canonicalSource &&
    certificate.material.format == "prime-fragment-certificate-v1" &&
    certificate.digest == MeTTailCore.Crypto.SHA256.sha256Hex
      (renderCertificateMaterial certificate.material) &&
    subjectValid source certificate.material.subject &&
    certificate.material.subject.material.goal == certificate.material.goal &&
    checkRaw validated certificate.material.goal certificate.material.proof

@[simp] theorem certificateValid_built {sort : ResultSort}
    (expression : FragmentExpr sort) (value : FragmentValue sort)
    (proof : RawProof) :
    certificateValid canonicalSource
      (makeCertificate canonicalSource expression value proof) =
        checkRaw validated (encodeJudgment expression value) proof := by
  simp [certificateValid, makeCertificate, makeCertificateFromPatterns,
    makeSubjectFromPatterns, subjectValid, makeSourceSnapshot,
    programGoalAgree_encoded]

/-- The checked certificate boundary has exactly the independently defined
source-evaluator semantics on encoded fragment goals. -/
theorem certificate_exists_iff_mem_evalBag {sort : ResultSort}
    (expression : FragmentExpr sort) (value : FragmentValue sort) :
    (∃ proof, certificateValid canonicalSource
      (makeCertificate canonicalSource expression value proof) = true) ↔
      value ∈ evalBag expression := by
  simpa only [certificateValid_built] using
    checked_iff_mem_evalBag expression value

def three : NatValue := .succ two
def four : NatValue := .succ three

def canonicalExpression : FragmentExpr .nat := .add two one
def canonicalValue : FragmentValue .nat := .nat three
def canonicalProof : RawProof :=
  proofCandidate canonicalExpression canonicalValue

def canonicalCertificate : CertificateV1 :=
  makeCertificate canonicalSource canonicalExpression canonicalValue
    canonicalProof

def wrongProgramCertificate : CertificateV1 :=
  makeCertificateFromPatterns canonicalSource
    (encodeProgram (.add one one))
    (encodeJudgment canonicalExpression canonicalValue) canonicalProof

def wrongGoalCertificate : CertificateV1 :=
  makeCertificate canonicalSource canonicalExpression (.nat four)
    canonicalProof

def skippedProof : RawProof :=
  .node
    { ruleId := ⟨"wex1.add-s"⟩
      arguments := [encodeNat one, encodeNat one, encodeNat two] }
    []

def skippedProofCertificate : CertificateV1 :=
  makeCertificate canonicalSource canonicalExpression canonicalValue
    skippedProof

def forgedSubjectCertificate : CertificateV1 :=
  let forgedSubject :=
    { canonicalCertificate.material.subject with
      digest := String.replicate 64 '0'
      handle := String.replicate 64 '0' }
  let material :=
    { canonicalCertificate.material with subject := forgedSubject }
  { material
    digest := MeTTailCore.Crypto.SHA256.sha256Hex
      (renderCertificateMaterial material) }

def forgedCertificateDigest : CertificateV1 :=
  { canonicalCertificate with digest := String.replicate 64 '0' }

theorem canonical_certificate_valid :
    certificateValid canonicalSource canonicalCertificate = true := by
  unfold canonicalCertificate canonicalExpression canonicalValue canonicalProof
  rw [certificateValid_built]
  apply proofOfEvaluation_checked
  apply (evaluates_iff_mem_evalBag).2
  simp [evalBag, addNat, three, two, one]

theorem wrong_result_certificate_rejected :
    certificateValid canonicalSource wrongGoalCertificate = false := by
  unfold wrongGoalCertificate canonicalExpression canonicalProof
  rw [certificateValid_built]
  change checkRaw validated
    (encodeJudgment (.add two one) (.nat four))
    (proofCandidate (.add two one) (.nat three)) = false
  have noCertificate :
      ¬ ∃ proof, checkRaw validated
        (encodeJudgment (.add two one) (.nat four)) proof = true := by
    rw [checked_iff_mem_evalBag]
    simp [evalBag, addNat, four, three, two, one]
  generalize hcheck : checkRaw validated
      (encodeJudgment (.add two one) (.nat four))
      (proofCandidate (.add two one) (.nat three)) = checked
  cases checked with
  | false => rfl
  | true => exact False.elim (noCertificate ⟨_, hcheck⟩)

private def runChecks : IO Unit := do
  unless certificateValid canonicalSource canonicalCertificate do
    throw <| IO.userError "canonical certificate was rejected"
  if certificateValid canonicalSource wrongProgramCertificate then
    throw <| IO.userError "certificate for another program was accepted"
  if certificateValid canonicalSource wrongGoalCertificate then
    throw <| IO.userError "certificate for a wrong result was accepted"
  if certificateValid canonicalSource skippedProofCertificate then
    throw <| IO.userError "certificate with a skipped premise was accepted"
  if certificateValid addDeletedSource canonicalCertificate then
    throw <| IO.userError "certificate crossed a source/package mutation"
  if certificateValid canonicalSource forgedSubjectCertificate then
    throw <| IO.userError "forged subject identity was accepted"
  if certificateValid canonicalSource forgedCertificateDigest then
    throw <| IO.userError "forged certificate digest was accepted"
  if renderCertificate canonicalCertificate ==
      renderCertificate wrongProgramCertificate then
    throw <| IO.userError "program mutation preserved certificate bytes"
  IO.println "PRIME_CERTIFICATE_CANONICAL_BEGIN"
  IO.println (renderCertificate canonicalCertificate)
  IO.println "PRIME_CERTIFICATE_CANONICAL_END"
  IO.println "PRIME_CERTIFICATE_DIGEST_BEGIN"
  IO.println canonicalCertificate.digest
  IO.println "PRIME_CERTIFICATE_DIGEST_END"
  IO.println "(PrimeCertificateBoundaryLeanSummaryV1 8 8 0)"

end Mettapedia.Languages.MeTTa.Prime.CertificateBoundaryV1

#print axioms Mettapedia.Languages.MeTTa.Prime.CertificateBoundaryV1.certificate_exists_iff_mem_evalBag
#print axioms Mettapedia.Languages.MeTTa.Prime.CertificateBoundaryV1.wrong_result_certificate_rejected

#eval Mettapedia.Languages.MeTTa.Prime.CertificateBoundaryV1.runChecks
