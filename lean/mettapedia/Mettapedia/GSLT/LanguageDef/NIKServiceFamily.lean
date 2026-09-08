import Mettapedia.GSLT.LanguageDef.NIK

/-!
# The four NIK service faces as a family over semantic targets

A NIK service serves one independently stated semantic target.  This module
answers what structure the services carry over the category of targets and
admitted operations.

* The four faces are a classifier `Service.face`; they are pairwise disjoint,
  and the external certificate boundary is exactly one of them.  The
  certificate-bearing services form the subtype `CertificateBoundaries`, and
  no native service lies in it.
* Along an equivalence of targets, a bijection of carriers that preserves and
  reflects meaning, every face transports, and the face is preserved.  So the
  family of services carries an action of the groupoid of target
  equivalences.
* Along a general admitted operation, a native operation pushes forward by
  composition. Decision by precomposition with that operation additionally
  needs reflection of meaning; the canary refutes this form of pullback for
  a non-reflecting collapse. It does not rule out source decision procedures
  using additional information or settle the existence of categorical lifts
  for some separately specified category of service morphisms.
* Request-local selection returns a native operation on the same target, and
  its runs preserve the target's declared meaning; the meaning predicate is
  never rewritten by selection.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIK

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus

universe uArtifact uEvidence uIndex uCapability

/-! ## The face classifier -/

/-- The four service faces. -/
inductive Face
  | directDecision
  | nativeProof
  | nativeOperation
  | certificateBoundary
  deriving DecidableEq

namespace Service

variable {target : AdmissionObject.{uArtifact}}

/-- The face of a service. -/
def face : Service.{uArtifact, uEvidence} target → Face
  | .directDecision _ => .directDecision
  | .nativeProof .. => .nativeProof
  | .nativeOperation .. => .nativeOperation
  | .certificateBoundary .. => .certificateBoundary

@[simp] theorem face_directDecision
    (kernel : Checker.DecisionKernel target.Carrier target.Meaning) :
    (Service.directDecision kernel : Service.{uArtifact, uEvidence} target).face =
      Face.directDecision :=
  rfl

@[simp] theorem face_nativeProof
    (guest : NativeProofSystem.{uArtifact, uEvidence} target.Carrier)
    (kernel : NativeProofKernel guest)
    (meaning_exact : ∀ claim, target.Meaning claim ↔ Nonempty (guest.ProofFibre claim)) :
    (Service.nativeProof guest kernel meaning_exact).face = Face.nativeProof :=
  rfl

@[simp] theorem face_nativeOperation
    (source : AdmissionObject.{uArtifact}) (operation : source ⟶ target) :
    (Service.nativeOperation source operation : Service.{uArtifact, uEvidence} target).face =
      Face.nativeOperation :=
  rfl

@[simp] theorem face_certificateBoundary
    (Certificate : Type uEvidence) (checker : Checker target.Carrier Certificate)
    (authority : checker.Authority target.Meaning) :
    (Service.certificateBoundary Certificate checker authority).face =
      Face.certificateBoundary :=
  rfl

/-- The external-boundary discriminator is the certificate face. -/
theorem hasExternalCertificateBoundary_iff_face (service : Service.{uArtifact, uEvidence} target) :
    hasExternalCertificateBoundary service = true ↔ service.face = .certificateBoundary := by
  cases service <;> simp [hasExternalCertificateBoundary, face]

/-- The certificate-boundary services: one substructure of the family. -/
abbrev CertificateBoundaries (target : AdmissionObject.{uArtifact}) :=
  { service : Service.{uArtifact, uEvidence} target // service.face = .certificateBoundary }

/-- No service of another face is a certificate boundary. -/
theorem ne_of_face_ne_certificateBoundary (service : Service.{uArtifact, uEvidence} target)
    (native : service.face ≠ .certificateBoundary)
    (boundary : CertificateBoundaries.{uArtifact, uEvidence} target) :
    service ≠ boundary.1 := by
  intro equal
  exact native (equal ▸ boundary.2)

/-- A service of any other face exposes no external certificate. -/
theorem isEmpty_externalCertificate_of_face_ne (service : Service.{uArtifact, uEvidence} target)
    (native : service.face ≠ .certificateBoundary) :
    IsEmpty service.ExternalCertificate := by
  cases service with
  | certificateBoundary Certificate checker authority => exact absurd rfl native
  | directDecision kernel => exact ⟨fun empty => nomatch empty⟩
  | nativeProof guest kernel meaning_exact => exact ⟨fun empty => nomatch empty⟩
  | nativeOperation source operation => exact ⟨fun empty => nomatch empty⟩

/-! ## Transport along target equivalences -/

end Service

/-- An equivalence of semantic targets: a bijection of carriers that
preserves and reflects meaning. -/
structure TargetEquiv (source target : AdmissionObject.{uArtifact}) where
  toEquiv : source.Carrier ≃ target.Carrier
  meaning_iff : ∀ value, source.Meaning value ↔ target.Meaning (toEquiv value)

namespace TargetEquiv

variable {source target : AdmissionObject.{uArtifact}}

/-- Target equivalences are determined by their carrier equivalences. -/
@[ext] theorem ext {first second : TargetEquiv source target}
    (carriers : first.toEquiv = second.toEquiv) : first = second := by
  cases first
  cases second
  cases carriers
  rfl

/-- The identity equivalence. -/
def refl (object : AdmissionObject.{uArtifact}) : TargetEquiv object object where
  toEquiv := Equiv.refl _
  meaning_iff _ := Iff.rfl

/-- The inverse equivalence. -/
def symm (equivalence : TargetEquiv source target) : TargetEquiv target source where
  toEquiv := equivalence.toEquiv.symm
  meaning_iff value := by
    rw [equivalence.meaning_iff (equivalence.toEquiv.symm value)]
    simp

/-- Composition of equivalences. -/
def trans {third : AdmissionObject.{uArtifact}} (first : TargetEquiv source target)
    (second : TargetEquiv target third) : TargetEquiv source third where
  toEquiv := first.toEquiv.trans second.toEquiv
  meaning_iff value := (first.meaning_iff value).trans (second.meaning_iff _)

@[simp] theorem refl_trans (equivalence : TargetEquiv source target) :
    (refl source).trans equivalence = equivalence := by
  apply ext
  exact Equiv.refl_trans equivalence.toEquiv

@[simp] theorem trans_refl (equivalence : TargetEquiv source target) :
    equivalence.trans (refl target) = equivalence := by
  apply ext
  exact Equiv.trans_refl equivalence.toEquiv

theorem trans_assoc {third fourth : AdmissionObject.{uArtifact}}
    (first : TargetEquiv source target) (second : TargetEquiv target third)
    (thirdMap : TargetEquiv third fourth) :
    (first.trans second).trans thirdMap = first.trans (second.trans thirdMap) := by
  apply ext
  exact Equiv.trans_assoc first.toEquiv second.toEquiv thirdMap.toEquiv

@[simp] theorem symm_symm (equivalence : TargetEquiv source target) :
    equivalence.symm.symm = equivalence := by
  apply ext
  exact Equiv.symm_symm equivalence.toEquiv

@[simp] theorem self_trans_symm (equivalence : TargetEquiv source target) :
    equivalence.trans equivalence.symm = refl source := by
  apply ext
  exact Equiv.self_trans_symm equivalence.toEquiv

@[simp] theorem symm_trans_self (equivalence : TargetEquiv source target) :
    equivalence.symm.trans equivalence = refl target := by
  apply ext
  exact Equiv.symm_trans_self equivalence.toEquiv

/-- An equivalence is in particular an admitted operation. -/
def toAdmissionHom (equivalence : TargetEquiv source target) : source ⟶ target where
  run := equivalence.toEquiv
  preserves value meaningful := (equivalence.meaning_iff value).1 meaningful

theorem meaning_symm_iff (equivalence : TargetEquiv source target) (value : target.Carrier) :
    source.Meaning (equivalence.toEquiv.symm value) ↔ target.Meaning value := by
  rw [equivalence.meaning_iff (equivalence.toEquiv.symm value)]
  simp

end TargetEquiv

namespace Service

variable {source target : AdmissionObject.{uArtifact}}

/-- Transport of a decision kernel along a target equivalence. -/
def transportDecision (equivalence : TargetEquiv source target)
    (kernel : Checker.DecisionKernel source.Carrier source.Meaning) :
    Checker.DecisionKernel target.Carrier target.Meaning where
  decide value := kernel.decide (equivalence.toEquiv.symm value)
  correct value := by
    rw [kernel.correct, equivalence.meaning_symm_iff]

/-- Transport of a native proof system along a target equivalence: the proof
objects are unchanged, and judge the translated claim. -/
def transportProofSystem (equivalence : TargetEquiv source target)
    (guest : NativeProofSystem.{uArtifact, uEvidence} source.Carrier) :
    NativeProofSystem.{uArtifact, uEvidence} target.Carrier where
  ProofObject := guest.ProofObject
  Judges proof value := guest.Judges proof (equivalence.toEquiv.symm value)

/-- Transport of a native proof kernel along a target equivalence. -/
def transportProofKernel (equivalence : TargetEquiv source target)
    {guest : NativeProofSystem.{uArtifact, uEvidence} source.Carrier}
    (kernel : NativeProofKernel guest) :
    NativeProofKernel (transportProofSystem equivalence guest) where
  decide value proof := kernel.decide (equivalence.toEquiv.symm value) proof
  correct _ proof := kernel.correct _ proof

/-- Transport of a checker along a target equivalence. -/
def transportChecker (equivalence : TargetEquiv source target)
    {Certificate : Type uEvidence} (checker : Checker source.Carrier Certificate) :
    Checker target.Carrier Certificate where
  check value certificate := checker.check (equivalence.toEquiv.symm value) certificate

/-- Exactness of a checker transports along a target equivalence. -/
theorem transportChecker_authority (equivalence : TargetEquiv source target)
    {Certificate : Type uEvidence} {checker : Checker source.Carrier Certificate}
    (authority : checker.Authority source.Meaning) :
    (transportChecker equivalence checker).Authority target.Meaning where
  sound value certificate accepted :=
    (equivalence.meaning_symm_iff value).1 (authority.sound _ certificate accepted)
  complete value meaningful :=
    authority.complete _ ((equivalence.meaning_symm_iff value).2 meaningful)

/-- Every face transports along a target equivalence. -/
def transport (equivalence : TargetEquiv source target) :
    Service.{uArtifact, uEvidence} source → Service.{uArtifact, uEvidence} target
  | .directDecision kernel => .directDecision (transportDecision equivalence kernel)
  | .nativeProof guest kernel meaning_exact =>
      .nativeProof (transportProofSystem equivalence guest) (transportProofKernel equivalence kernel)
        (fun value => by
          rw [← equivalence.meaning_symm_iff value]
          exact meaning_exact _)
  | .nativeOperation origin operation =>
      .nativeOperation origin (operation ≫ equivalence.toAdmissionHom)
  | .certificateBoundary Certificate checker authority =>
      .certificateBoundary Certificate (transportChecker equivalence checker)
        (transportChecker_authority equivalence authority)

/-- Transport preserves the face: the four faces are a family over targets,
each stable under target equivalence. -/
@[simp] theorem face_transport (equivalence : TargetEquiv source target)
    (service : Service.{uArtifact, uEvidence} source) :
    (transport equivalence service).face = service.face := by
  cases service <;> rfl

/-- Transport along the identity equivalence is the identity. -/
theorem transport_refl (service : Service.{uArtifact, uEvidence} target) :
    transport (TargetEquiv.refl target) service = service := by
  cases service with
  | directDecision kernel => rfl
  | nativeProof guest kernel meaning_exact => rfl
  | nativeOperation origin operation => rfl
  | certificateBoundary Certificate checker authority => rfl

/-- Successive target transports agree on the complete service, including
its retained native proof objects and certificate carrier. -/
theorem transport_trans {third : AdmissionObject.{uArtifact}}
    (first : TargetEquiv source target) (second : TargetEquiv target third)
    (service : Service.{uArtifact, uEvidence} source) :
    transport (first.trans second) service = transport second (transport first service) := by
  cases service <;> rfl

/-- Transport followed by inverse transport recovers the original service. -/
@[simp] theorem transport_symm_transport (equivalence : TargetEquiv source target)
    (service : Service.{uArtifact, uEvidence} source) :
    transport equivalence.symm (transport equivalence service) = service := by
  rw [← transport_trans, TargetEquiv.self_trans_symm, transport_refl]

/-- Inverse transport followed by transport also recovers the original service. -/
@[simp] theorem transport_transport_symm (equivalence : TargetEquiv source target)
    (service : Service.{uArtifact, uEvidence} target) :
    transport equivalence (transport equivalence.symm service) = service := by
  rw [← transport_trans, TargetEquiv.symm_trans_self, transport_refl]

/-- A target equivalence induces an equivalence of complete service fibres. -/
def transportEquiv (equivalence : TargetEquiv source target) :
    Service.{uArtifact, uEvidence} source ≃ Service.{uArtifact, uEvidence} target where
  toFun := transport equivalence
  invFun := transport equivalence.symm
  left_inv := transport_symm_transport equivalence
  right_inv := transport_transport_symm equivalence

/-! ## Face-dependent reindexing along admitted operations -/

/-- A native operation pushes forward along any admitted operation out of
its target using the composition law of admitted operations. -/
def pushforward {later : AdmissionObject.{uArtifact}} (operation : target ⟶ later)
    (origin : AdmissionObject.{uArtifact}) (native : origin ⟶ target) :
    Service.{uArtifact, uEvidence} later :=
  .nativeOperation origin (native ≫ operation)

theorem pushforward_preserves {later : AdmissionObject.{uArtifact}}
    (operation : target ⟶ later) (origin : AdmissionObject.{uArtifact})
    (native : origin ⟶ target) (input : origin.Carrier) (meaningful : origin.Meaning input) :
    later.Meaning ((native ≫ operation).run input) :=
  (native ≫ operation).preserves input meaningful

/-! ## Selection preserves declared meaning -/

/-- Request-local selection returns a native operation. -/
theorem face_ofStrongest
    {Index : Type uIndex} [PartialOrder Index] [DecidableEq Index]
    {origin : AdmissionObject.{uArtifact}}
    {family : RecognizedFamily.{uIndex, uCapability, uArtifact} Index origin target}
    (request : family.CapabilityRequest)
    (selection : request.StrongestNativeCalculusPrinciple) :
    (ofStrongest request selection : Service.{uArtifact, uEvidence} target).face =
      Face.nativeOperation :=
  rfl

/-- The selected operation preserves the target's declared meaning; selection
rewrites no meaning predicate. -/
theorem ofStrongest_preserves
    {Index : Type uIndex} [PartialOrder Index] [DecidableEq Index]
    {origin : AdmissionObject.{uArtifact}}
    {family : RecognizedFamily.{uIndex, uCapability, uArtifact} Index origin target}
    (request : family.CapabilityRequest)
    (selection : request.StrongestNativeCalculusPrinciple)
    (input : origin.Carrier) (meaningful : origin.Meaning input) :
    target.Meaning ((request.strongestOperation selection).run input) :=
  (request.strongestOperation selection).preserves input meaningful

end Service

/-! ## The obstruction to reindexing decisions along admitted operations -/

namespace ReindexingCanary

/-- Booleans, meaningful exactly at `true`. -/
def source : AdmissionObject.{0} where
  Carrier := Bool
  Meaning value := value = true

/-- The point, always meaningful. -/
def target : AdmissionObject.{0} where
  Carrier := Unit
  Meaning _ := True

/-- The collapse is an admitted operation: it preserves meaning. -/
def collapse : source ⟶ target where
  run _ := ()
  preserves _ _ := trivial

/-- The collapse does not reflect meaning. -/
theorem collapse_not_reflecting :
    ¬ ∀ value, target.Meaning (collapse.run value) → source.Meaning value := by
  intro reflects
  exact Bool.false_ne_true (reflects false trivial)

/-- The target's decision kernel. -/
def targetKernel : Checker.DecisionKernel target.Carrier target.Meaning where
  decide _ := true
  correct _ := by simp [target]

/-- No decision kernel for the source decides by running the target kernel on
the collapsed value: pullback of a decision along a meaning-preserving but
non-reflecting operation is not a service. -/
theorem no_pullback_decision :
    ¬ ∃ kernel : Checker.DecisionKernel source.Carrier source.Meaning,
      ∀ value, kernel.decide value = targetKernel.decide (collapse.run value) := by
  rintro ⟨kernel, pulled⟩
  have accepted : kernel.decide false = true := pulled false
  exact Bool.false_ne_true ((kernel.correct false).1 accepted)

/-- The same operation pushes a native operation forward without
obstruction. -/
example : Service.{0, 0} target :=
  Service.pushforward collapse source (𝟙 source)

end ReindexingCanary

#print axioms Service.face_transport
#print axioms Service.transport_refl
#print axioms TargetEquiv.trans_assoc
#print axioms TargetEquiv.self_trans_symm
#print axioms Service.transport_trans
#print axioms Service.transport_symm_transport
#print axioms Service.transport_transport_symm
#print axioms Service.transportEquiv
#print axioms Service.ofStrongest_preserves
#print axioms Service.isEmpty_externalCertificate_of_face_ne
#print axioms ReindexingCanary.no_pullback_decision

end Mettapedia.GSLT.LanguageDef.NIK
