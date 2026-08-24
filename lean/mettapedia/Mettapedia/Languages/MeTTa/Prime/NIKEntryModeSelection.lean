import Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
import Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
import Mettapedia.Languages.MeTTa.Prime.DataFibration

/-!
# Request-fibred selection for NIK entry modes

The four NIK entry modes are capabilities, not a global numeric ladder.  This
module instantiates maximal-native selection on one exact shared contract:
checking a guest-native proof object against a claim.  A native proof kernel
and an explicit replay boundary decide the same proof judgment, while their
retained route receipts remain distinct.

Requests select inside that common semantic fibre.  A certificate-free native
request has one strongest realization; an explicit-boundary request has a
different strongest realization.  A neutral request retains both incomparable
members and provably has no strongest choice.  Direct theoremhood decision and
admitted flow therefore remain separate request shapes rather than being forced
into this proof-checking order.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NIKEntryModeSelection

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
open Mettapedia.Languages.MeTTa.Prime.DataFibration

universe uClaim uProof

/-! ## One exact proof-checking contract -/

/-- The two operational faces that can implement the same native proof-check
request.  They are deliberately incomparable until a request names the
boundary capability it needs. -/
inductive ProofKernelFace where
  | nativeProof
  | boundaryReplay
  deriving DecidableEq, Repr

/-- No global ordering is smuggled in between native construction/checking and
an explicit replay boundary. -/
instance : PartialOrder ProofKernelFace where
  le := Eq
  le_refl := fun _ => rfl
  le_trans := fun _ _ _ first second => first.trans second
  le_antisymm := fun _ _ forward _ => forward

/-- Capabilities visible to proof-checking requests.  Both faces preserve the
exact native proof fibre, but only one is certificate-free and only one is an
explicit trust boundary. -/
inductive ProofKernelCapability where
  | exactProofFibre
  | certificateFree
  | explicitBoundary
  deriving DecidableEq, Repr

def supports : ProofKernelFace → ProofKernelCapability → Prop
  | _, .exactProofFibre => True
  | .nativeProof, .certificateFree => True
  | .boundaryReplay, .explicitBoundary => True
  | _, _ => False

/-- Runtime input to the shared proof-checking contract. -/
structure ProofCheckInput
    (Claim : Type uClaim) (Proof : Type uProof) where
  claim : Claim
  proof : Proof

/-- The result retains which native-calculus face was exercised.  The route is
not part of theoremhood, but it is operational provenance and must not be
silently collapsed. -/
structure ProofCheckResult
    (Claim : Type uClaim) (Proof : Type uProof) where
  face : ProofKernelFace
  claim : Claim
  proof : Proof
  accepted : Bool

/-- Every finite claim/proof pair is a legitimate query, so the source fibre
is intentionally unrestricted.  The nontrivial invariant is exact judgment
agreement in `proofCheckTarget`, proved by each operation's native kernel. -/
def proofCheckSource
    {Claim : Type uClaim} (guest : NativeProofSystem.{uClaim, uProof} Claim) :
    AdmissionObject.{max uClaim uProof} where
  Carrier := ProofCheckInput Claim guest.ProofObject
  Meaning := fun _ => True

/-- Independent result meaning: the Boolean answer is exact for the guest's
authored proof judgment. -/
def proofCheckTarget
    {Claim : Type uClaim} (guest : NativeProofSystem.{uClaim, uProof} Claim) :
    AdmissionObject.{max uClaim uProof} where
  Carrier := ProofCheckResult Claim guest.ProofObject
  Meaning := fun result =>
    result.accepted = true ↔ guest.Judges result.proof result.claim

/-- Direct native proof-kernel execution. -/
def nativeProofOperation
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (kernel : NativeProofKernel guest) :
    proofCheckSource guest ⟶ proofCheckTarget guest where
  run := fun input =>
    { face := .nativeProof
      claim := input.claim
      proof := input.proof
      accepted := kernel.decide input.claim input.proof }
  preserves := fun input _ => kernel.correct input.claim input.proof

/-- The same guest kernel viewed at an explicit certificate boundary.  The
Boolean judgment agrees, but its route receipt remains `boundaryReplay`. -/
def boundaryReplayOperation
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (kernel : NativeProofKernel guest) :
    proofCheckSource guest ⟶ proofCheckTarget guest where
  run := fun input =>
    { face := .boundaryReplay
      claim := input.claim
      proof := input.proof
      accepted := kernel.toChecker.check input.claim input.proof }
  preserves := fun input _ => kernel.correct input.claim input.proof

/-! ## Connection to the actual four-mode Data boundary -/

def nativeEntry
    {Claim : Type uClaim} (guest : NativeProofSystem.{uClaim, uProof} Claim)
    (kernel : NativeProofKernel guest) : EntryMode.{uClaim, uProof} Claim :=
  .nativeProof guest kernel

def boundaryEntry
    {Claim : Type uClaim} (guest : NativeProofSystem.{uClaim, uProof} Claim)
    (kernel : NativeProofKernel guest) : EntryMode.{uClaim, uProof} Claim :=
  .certificateBoundary guest.ProofObject
    (fun claim => Nonempty (guest.ProofFibre claim))
    kernel.toChecker kernel.authority

/-- The native and boundary faces establish exactly the same theoremhood
fibre.  Their distinction is where checking occurs, not what is true. -/
theorem native_boundary_sameAccepted
    {Claim : Type uClaim} (guest : NativeProofSystem.{uClaim, uProof} Claim)
    (kernel : NativeProofKernel guest) (claim : Claim) :
    EntryMode.Accepted (nativeEntry guest kernel) claim ↔
      EntryMode.Accepted (boundaryEntry guest kernel) claim :=
  Iff.rfl

/-- The same accepted judgment may be exposed through genuinely different
boundary capabilities. -/
theorem native_boundary_certificate_distinction
    {Claim : Type uClaim} (guest : NativeProofSystem.{uClaim, uProof} Claim)
    (kernel : NativeProofKernel guest) :
    EntryMode.requiresCertificate (nativeEntry guest kernel) = false ∧
      EntryMode.requiresCertificate (boundaryEntry guest kernel) = true :=
  ⟨rfl, rfl⟩

/-- Retained operational provenance distinguishes the two realizations even
when their Boolean answer agrees definitionally. -/
theorem proofCheck_receipts_distinct
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (kernel : NativeProofKernel guest)
    (input : (proofCheckSource guest).Carrier) :
    (nativeProofOperation kernel).run input ≠
      (boundaryReplayOperation kernel).run input := by
  intro equal
  have faceEqual := congrArg
    (fun result : (proofCheckTarget guest).Carrier => result.face) equal
  cases faceEqual

/-! ## The recognized proof-kernel family -/

def proofKernelFamily
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (kernel : NativeProofKernel guest) :
    RecognizedFamily ProofKernelFace
      (proofCheckSource guest) (proofCheckTarget guest) where
  package
    | .nativeProof => nativeProofOperation kernel
    | .boundaryReplay => boundaryReplayOperation kernel
  Capability := ProofKernelCapability
  supports := supports
  supports_mono := by
    intro weaker stronger related capability supported
    change weaker = stronger at related
    subst stronger
    exact supported
  strict_support_gain := by
    intro weaker stronger strict
    exact False.elim (strict.2 strict.1.symm)
  recognized := {.nativeProof, .boundaryReplay}
  licensed := {.nativeProof, .boundaryReplay}
  licensed_subset_recognized := Finset.Subset.rfl
  licensed_nonempty := ⟨.nativeProof, by simp⟩

/-- The declared discrete order is exactly capability inclusion for this
family: neither boundary capability contains the other. -/
theorem proofKernel_order_iff_capability_inclusion
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (kernel : NativeProofKernel guest) (first second : ProofKernelFace) :
    first ≤ second ↔
      ∀ capability,
        (proofKernelFamily kernel).supports first capability →
          (proofKernelFamily kernel).supports second capability := by
  constructor
  · intro related
    change first = second at related
    subst second
    exact fun _ supported => supported
  · intro included
    cases first <;> cases second
    · rfl
    · have impossible := included .certificateFree
      simp [proofKernelFamily, supports] at impossible
    · have impossible := included .explicitBoundary
      simp [proofKernelFamily, supports] at impossible
    · rfl

/-! ## Exact request fibres -/

def nativeProofRequest
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (kernel : NativeProofKernel guest) :
    (proofKernelFamily kernel).CapabilityRequest where
  required := {.exactProofFibre, .certificateFree}
  candidates := {.nativeProof}
  candidates_exact := by
    intro candidate
    cases candidate with
    | nativeProof =>
        constructor
        · intro _
          refine ⟨by simp [proofKernelFamily], ?_⟩
          intro capability required
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at required
          rcases required with rfl | rfl <;> trivial
        · intro _
          simp
    | boundaryReplay =>
        constructor
        · intro impossible
          simp at impossible
        · rintro ⟨_, supportsRequired⟩
          have impossible := supportsRequired .certificateFree (by simp)
          simp [proofKernelFamily, supports] at impossible
  candidates_nonempty := by simp

def boundaryReplayRequest
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (kernel : NativeProofKernel guest) :
    (proofKernelFamily kernel).CapabilityRequest where
  required := {.exactProofFibre, .explicitBoundary}
  candidates := {.boundaryReplay}
  candidates_exact := by
    intro candidate
    cases candidate with
    | nativeProof =>
        constructor
        · intro impossible
          simp at impossible
        · rintro ⟨_, supportsRequired⟩
          have impossible := supportsRequired .explicitBoundary (by simp)
          simp [proofKernelFamily, supports] at impossible
    | boundaryReplay =>
        constructor
        · intro _
          refine ⟨by simp [proofKernelFamily], ?_⟩
          intro capability required
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at required
          rcases required with rfl | rfl <;> trivial
        · intro _
          simp
  candidates_nonempty := by simp

/-- With no boundary capability requested, both exact realizations remain in
the fibre. -/
def neutralProofRequest
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (kernel : NativeProofKernel guest) :
    (proofKernelFamily kernel).CapabilityRequest where
  required := ∅
  candidates := {.nativeProof, .boundaryReplay}
  candidates_exact := by
    intro candidate
    cases candidate <;>
      constructor
    · intro _
      refine ⟨by simp [proofKernelFamily], ?_⟩
      intro capability impossible
      simp at impossible
    · intro _
      simp
    · intro _
      refine ⟨by simp [proofKernelFamily], ?_⟩
      intro capability impossible
      simp at impossible
    · intro _
      simp
  candidates_nonempty := ⟨.nativeProof, by simp⟩

theorem nativeProofRequest_directed
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (kernel : NativeProofKernel guest) :
    (nativeProofRequest kernel).restrictedFamily.LicensedDirected := by
  intro first firstMember second secondMember
  have firstEqual : first = .nativeProof := by
    simpa [RecognizedFamily.CapabilityRequest.restrictedFamily,
      nativeProofRequest] using firstMember
  have secondEqual : second = .nativeProof := by
    simpa [RecognizedFamily.CapabilityRequest.restrictedFamily,
      nativeProofRequest] using secondMember
  subst first
  subst second
  exact ⟨.nativeProof, by
      simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
        nativeProofRequest], le_rfl, le_rfl⟩

theorem boundaryReplayRequest_directed
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (kernel : NativeProofKernel guest) :
    (boundaryReplayRequest kernel).restrictedFamily.LicensedDirected := by
  intro first firstMember second secondMember
  have firstEqual : first = .boundaryReplay := by
    simpa [RecognizedFamily.CapabilityRequest.restrictedFamily,
      boundaryReplayRequest] using firstMember
  have secondEqual : second = .boundaryReplay := by
    simpa [RecognizedFamily.CapabilityRequest.restrictedFamily,
      boundaryReplayRequest] using secondMember
  subst first
  subst second
  exact ⟨.boundaryReplay, by
      simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
        boundaryReplayRequest], le_rfl, le_rfl⟩

/-- A certificate-free proof request has one unique strongest realization. -/
theorem nativeProofRequest_uniqueStrongest
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (kernel : NativeProofKernel guest) :
    ∃! chosen,
      (nativeProofRequest kernel).restrictedFamily.IsGreatestLicensed chosen :=
  (nativeProofRequest kernel).existsUnique_strongest_of_restrictedDirected
    (nativeProofRequest_directed kernel)

/-- An explicit trust-boundary request has its own unique strongest
realization rather than losing to a global native-first priority. -/
theorem boundaryReplayRequest_uniqueStrongest
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (kernel : NativeProofKernel guest) :
    ∃! chosen,
      (boundaryReplayRequest kernel).restrictedFamily.IsGreatestLicensed
        chosen :=
  (boundaryReplayRequest kernel).existsUnique_strongest_of_restrictedDirected
    (boundaryReplayRequest_directed kernel)

def nativeProofSelection
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (kernel : NativeProofKernel guest) :
    (nativeProofRequest kernel).StrongestNativeCalculusPrinciple where
  val := .nativeProof
  property := by
    constructor
    · simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
        nativeProofRequest]
    · intro candidate candidateMember
      have candidateEqual : candidate = .nativeProof := by
        simpa [RecognizedFamily.CapabilityRequest.restrictedFamily,
          nativeProofRequest] using candidateMember
      subst candidate
      exact le_rfl

def boundaryReplaySelection
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (kernel : NativeProofKernel guest) :
    (boundaryReplayRequest kernel).StrongestNativeCalculusPrinciple where
  val := .boundaryReplay
  property := by
    constructor
    · simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
        boundaryReplayRequest]
    · intro candidate candidateMember
      have candidateEqual : candidate = .boundaryReplay := by
        simpa [RecognizedFamily.CapabilityRequest.restrictedFamily,
          boundaryReplayRequest] using candidateMember
      subst candidate
      exact le_rfl

/-- The strongest certificate-free request executes the original native
operation; selection inserts no replay call. -/
@[simp] theorem nativeStrongestOperation_run
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (kernel : NativeProofKernel guest)
    (input : (proofCheckSource guest).Carrier) :
    ((nativeProofRequest kernel).strongestOperation
      (nativeProofSelection kernel)).run input =
        (nativeProofOperation kernel).run input :=
  rfl

/-- An explicit boundary request likewise returns the original replay
operation, rather than silently switching to the native face. -/
@[simp] theorem boundaryStrongestOperation_run
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (kernel : NativeProofKernel guest)
    (input : (proofCheckSource guest).Carrier) :
    ((boundaryReplayRequest kernel).strongestOperation
      (boundaryReplaySelection kernel)).run input =
        (boundaryReplayOperation kernel).run input :=
  rfl

/-! ## Revision-current selection -/

/-- A strongest proof-kernel selection stored at one dependency revision and
activated at a current revision with the same selected dependency view.  The
currentness proof guards construction; it is not an input to the operation. -/
structure CurrentProofKernelSelection
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (kernel : NativeProofKernel guest)
    (request : (proofKernelFamily kernel).CapabilityRequest)
    (dependencies : DependencySystem)
    (admittedRevision currentRevision : dependencies.Revision) where
  current : dependencies.SameDependencies admittedRevision currentRevision
  selection : request.StrongestNativeCalculusPrinciple

namespace CurrentProofKernelSelection

def operation
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    {kernel : NativeProofKernel guest}
    {request : (proofKernelFamily kernel).CapabilityRequest}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    (active : CurrentProofKernelSelection kernel request dependencies
      admittedRevision currentRevision) :
    proofCheckSource guest ⟶ proofCheckTarget guest :=
  request.strongestOperation active.selection

/-- Hot execution applies only the retained selected operation. -/
def run
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    {kernel : NativeProofKernel guest}
    {request : (proofKernelFamily kernel).CapabilityRequest}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    (active : CurrentProofKernelSelection kernel request dependencies
      admittedRevision currentRevision) :
    (proofCheckSource guest).Carrier → (proofCheckTarget guest).Carrier :=
  active.operation.run

@[simp] theorem run_eq_selectedOperation
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    {kernel : NativeProofKernel guest}
    {request : (proofKernelFamily kernel).CapabilityRequest}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    (active : CurrentProofKernelSelection kernel request dependencies
      admittedRevision currentRevision)
    (input : (proofCheckSource guest).Carrier) :
    active.run input =
      (request.strongestOperation active.selection).run input :=
  rfl

theorem run_preserves
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    {kernel : NativeProofKernel guest}
    {request : (proofKernelFamily kernel).CapabilityRequest}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    (active : CurrentProofKernelSelection kernel request dependencies
      admittedRevision currentRevision)
    (input : (proofCheckSource guest).Carrier) :
    (proofCheckTarget guest).Meaning (active.run input) :=
  request.strongestOperation_preserves active.selection input trivial

end CurrentProofKernelSelection

namespace RevisionCanary

open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission.Canary

def currentNativeProofSelection :
    CurrentProofKernelSelection EntryMode.booleanProofKernel
      (nativeProofRequest EntryMode.booleanProofKernel)
      dependencySystem (false, false) (false, true) where
  current := irrelevant_change_current
  selection := nativeProofSelection EntryMode.booleanProofKernel

def trueProofInput :
    (proofCheckSource EntryMode.booleanProofSystem).Carrier where
  claim := true
  proof := PUnit.unit

/-- An irrelevant raw revision change preserves the selected dependency view;
the active request still executes the original native proof operation. -/
theorem irrelevant_change_runs_native :
    currentNativeProofSelection.run trueProofInput =
      (nativeProofOperation EntryMode.booleanProofKernel).run trueProofInput :=
  rfl

theorem irrelevant_change_retains_native_receipt_and_acceptance :
    (currentNativeProofSelection.run trueProofInput).face =
        .nativeProof ∧
      (currentNativeProofSelection.run trueProofInput).accepted = true :=
  ⟨rfl, rfl⟩

/-- A relevant dependency change makes the stored strongest selection
unusable.  It cannot silently fall through to another face. -/
theorem relevant_change_has_no_current_selection :
    ¬ Nonempty
      (CurrentProofKernelSelection EntryMode.booleanProofKernel
        (nativeProofRequest EntryMode.booleanProofKernel)
        dependencySystem (false, false) (true, false)) := by
  rintro ⟨active⟩
  exact relevant_change_not_current active.current

end RevisionCanary

/-! ## Negative controls -/

/-- The neutral exact fibre has two incomparable maximal realizations and no
canonical strongest kernel. -/
theorem neutralProofRequest_noStrongest
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (kernel : NativeProofKernel guest) :
    ¬ ∃ chosen,
      (neutralProofRequest kernel).restrictedFamily.IsGreatestLicensed
        chosen := by
  rintro ⟨chosen, strongest⟩
  cases chosen with
  | nativeProof =>
      have boundaryLe : ProofKernelFace.boundaryReplay ≤ .nativeProof :=
        strongest.2 .boundaryReplay (by
          simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
            neutralProofRequest])
      cases boundaryLe
  | boundaryReplay =>
      have nativeLe : ProofKernelFace.nativeProof ≤ .boundaryReplay :=
        strongest.2 .nativeProof (by
          simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
            neutralProofRequest])
      cases nativeLe

/-- Consequently, the neutral request does not admit common upgrades. -/
theorem neutralProofRequest_notDirected
    {Claim : Type uClaim} {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (kernel : NativeProofKernel guest) :
    ¬ (neutralProofRequest kernel).restrictedFamily.LicensedDirected := by
  intro directed
  obtain ⟨strongest⟩ :=
    (neutralProofRequest kernel)
      |>.strongestPrinciple_inhabited_of_restrictedDirected directed
  exact neutralProofRequest_noStrongest kernel ⟨strongest.1, strongest.2⟩

/-- Even on the existing Boolean canary, direct theoremhood decision and
native proof checking have the same accepted claims and the same
certificate-free flag while remaining different entry constructors.  Thus
that flag alone cannot select a native calculus face. -/
theorem direct_native_same_surface_not_same_face :
    (∀ claim,
      EntryMode.Accepted EntryMode.directWitness claim ↔
        EntryMode.Accepted EntryMode.nativeProofWitness claim) ∧
      EntryMode.requiresCertificate EntryMode.directWitness =
        EntryMode.requiresCertificate EntryMode.nativeProofWitness ∧
      EntryMode.directWitness ≠ EntryMode.nativeProofWitness := by
  constructor
  · intro claim
    change claim = true ↔
      Nonempty (EntryMode.booleanProofSystem.ProofFibre claim)
    constructor
    · intro accepted
      exact ⟨⟨PUnit.unit, accepted⟩⟩
    · rintro ⟨⟨_, accepted⟩⟩
      exact accepted
  constructor
  · rfl
  · intro equal
    cases equal

#print axioms native_boundary_sameAccepted
#print axioms proofCheck_receipts_distinct
#print axioms proofKernel_order_iff_capability_inclusion
#print axioms nativeProofRequest_uniqueStrongest
#print axioms boundaryReplayRequest_uniqueStrongest
#print axioms nativeStrongestOperation_run
#print axioms boundaryStrongestOperation_run
#print axioms CurrentProofKernelSelection.run_preserves
#print axioms RevisionCanary.irrelevant_change_runs_native
#print axioms RevisionCanary.relevant_change_has_no_current_selection
#print axioms neutralProofRequest_noStrongest
#print axioms neutralProofRequest_notDirected
#print axioms direct_native_same_surface_not_same_face

end Mettapedia.Languages.MeTTa.Prime.NIKEntryModeSelection
