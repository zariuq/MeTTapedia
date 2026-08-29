import Mettapedia.CognitiveArchitecture.Agent.RevisionLineage
import Mettapedia.Enactive.ProtectedFreedom

/-!
# Protected-family whole-mind revision

A lineage edge is not by itself a safe self-revision.  This module requires a
current, source-scoped execution receipt and an explicit map for each protected
evidence family: capabilities, commitments, reproducibility obligations, and
selected ethical obligations.

The interface is intentionally sufficient rather than universal.  It proves
preservation only for family-mapped revisions and does not identify parent and
child minds.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Agent.ProtectedSelfRevision

open Mettapedia.Enactive.ProtectedFreedom
open Mettapedia.CognitiveArchitecture.Agent.RevisionLineage

universe uState uEvidence uProof uSource uAuthority

/-- The initial protected whole-mind evidence families.  New obligation kinds
may be added explicitly; none is hidden inside a generic Boolean. -/
inductive ObligationKind where
  | capability
  | commitment
  | reproducibility
  | ethical
  deriving DecidableEq, Repr

/-- A proof-erased profile says which evidence type is required at each
protected index.  It does not bundle evidence inhabitants. -/
structure ProtectedProfile where
  Evidence : ObligationKind → Type uEvidence

/-- Full certification is an inhabitant of every protected evidence fibre. -/
def Certified (profile : ProtectedProfile.{uEvidence}) : Type uEvidence :=
  ∀ kind, profile.Evidence kind

/-- One proof-backed self-revision maps all four protected families. -/
structure FamilyPreservingRevision
    (before after : ProtectedProfile.{uEvidence}) (Proof : Type uProof) where
  proof : Proof
  preserves : ProtectedFamilyMap (Set.univ : Set ObligationKind)
    before.Evidence after.Evidence

namespace FamilyPreservingRevision

variable {before middle after : ProtectedProfile.{uEvidence}}
variable {Proof FirstProof SecondProof : Type uProof}

/-- Transport complete protected certification through the family maps. -/
def transportCertified
    (revision : FamilyPreservingRevision before after Proof)
    (certified : Certified before) : Certified after :=
  fun kind => revision.preserves.map kind (Set.mem_univ kind) (certified kind)

/-- Protected revision maps compose pointwise while retaining both proofs. -/
def comp
    (first : FamilyPreservingRevision before middle FirstProof)
    (second : FamilyPreservingRevision middle after SecondProof) :
    FamilyPreservingRevision before after (FirstProof × SecondProof) where
  proof := (first.proof, second.proof)
  preserves :=
    { map := by
        intro kind _protected evidence
        exact second.preserves.map kind (Set.mem_univ kind)
          (first.preserves.map kind (Set.mem_univ kind) evidence) }

@[simp] theorem comp_transportCertified
    (first : FamilyPreservingRevision before middle FirstProof)
    (second : FamilyPreservingRevision middle after SecondProof)
    (certified : Certified before) :
    (first.comp second).transportCertified certified =
      second.transportCertified (first.transportCertified certified) :=
  rfl

end FamilyPreservingRevision

/-! ## Current lineage-bound admission -/

/-- A protected revision whose proof receipt is current at the exact revision
captured by its parent occurrence.  The receipt's `SourceScoped` instance
retains the independent finite source-occurrence set. -/
structure CurrentProtectedRevision
    {Owner : Type} {State : Type uState}
    (before after : ProtectedProfile.{uEvidence})
    (Proof : Type uProof)
    (discipline : ExecutionDiscipline.{uProof, uSource, 0,
      uAuthority, uEvidence} Proof)
    (parent child : Node Owner discipline.Revision State) where
  modification : FamilyPreservingRevision before after Proof
  lineage : parent.IsParent child
  receipt : IssuedReceipt discipline modification.proof
  current : receipt.CurrentAt parent.id.read.revision

namespace CurrentProtectedRevision

variable {Owner : Type} {State : Type uState}
variable {before middleProfile after : ProtectedProfile.{uEvidence}}
variable {Proof : Type uProof}
variable {discipline : ExecutionDiscipline.{uProof, uSource, 0,
  uAuthority, uEvidence} Proof}
variable {parent middle child : Node Owner discipline.Revision State}

/-- Protected evidence and receipt currentness are returned together without
deriving either from the other. -/
theorem preserves_certification
    (revision : CurrentProtectedRevision before after Proof discipline
      parent child)
    (certified : Nonempty (Certified before)) :
    Nonempty (Certified after) ∧
      revision.receipt.CurrentAt parent.id.read.revision := by
  rcases certified with ⟨evidence⟩
  exact ⟨⟨revision.modification.transportCertified evidence⟩,
    revision.current⟩

/-- Sequential revisions transport the family through both edges and retain
both independently current receipts. -/
theorem sequential_preserves
    (first : CurrentProtectedRevision before middleProfile Proof discipline
      parent middle)
    (second : CurrentProtectedRevision middleProfile after Proof discipline
      middle child)
    (certified : Nonempty (Certified before)) :
    Nonempty (Certified after) ∧
      first.receipt.CurrentAt parent.id.read.revision ∧
      second.receipt.CurrentAt middle.id.read.revision := by
  rcases certified with ⟨evidence⟩
  refine ⟨⟨second.modification.transportCertified
    (first.modification.transportCertified evidence)⟩, first.current,
    second.current⟩

/-- Both branches of a fork must independently transport the protected
family; one branch's certificate does not certify the other. -/
theorem fork_preserves_both
    {fork : Fork parent}
    (leftRevision : CurrentProtectedRevision before after Proof discipline
      parent fork.left)
    (rightRevision : CurrentProtectedRevision before after Proof discipline
      parent fork.right)
    (certified : Nonempty (Certified before)) :
    Nonempty (Certified after) ∧ Nonempty (Certified after) ∧
      leftRevision.receipt.CurrentAt parent.id.read.revision ∧
      rightRevision.receipt.CurrentAt parent.id.read.revision := by
  rcases certified with ⟨evidence⟩
  exact ⟨⟨leftRevision.modification.transportCertified evidence⟩,
    ⟨rightRevision.modification.transportCertified evidence⟩,
    leftRevision.current, rightRevision.current⟩

end CurrentProtectedRevision

/-! ## Positive and negative controls -/

namespace Canary

open RevisionLineage.Canary

/-- Every protected family has one simple witness in the positive profile. -/
def completeProfile : ProtectedProfile where
  Evidence := fun _ => Unit

def completeCertification : Certified completeProfile := fun _ => ()

inductive RevisionProof where
  | leftFork
  | rightFork
  | mergeStep
  deriving DecidableEq

def discipline : ExecutionDiscipline RevisionProof where
  Source := Fin 3
  Revision := Nat
  Authority := Unit
  sourceDecidable := inferInstance
  Authorized := fun _ _ => Unit
  Realizable := fun _ => Unit

def identityModification (proof : RevisionProof) :
    FamilyPreservingRevision completeProfile completeProfile RevisionProof where
  proof := proof
  preserves :=
    { map := by
        intro kind _protected evidence
        exact evidence }

def leftReceipt :
    IssuedReceipt discipline RevisionProof.leftFork where
  authority := ()
  sources := by
    change Finset (Fin 3)
    exact {0}
  issuedAt := parent.id.read.revision
  authorized := ()
  realizable := ()

def rightReceipt :
    IssuedReceipt discipline RevisionProof.rightFork where
  authority := ()
  sources := by
    change Finset (Fin 3)
    exact {1}
  issuedAt := parent.id.read.revision
  authorized := ()
  realizable := ()

def leftRevision : CurrentProtectedRevision completeProfile completeProfile
    RevisionProof discipline parent equalStateFork.left where
  modification := identityModification .leftFork
  lineage := equalStateFork.parent_of_left
  receipt := leftReceipt
  current := by
    simp [IssuedReceipt.CurrentAt, leftReceipt]

def rightRevision : CurrentProtectedRevision completeProfile completeProfile
    RevisionProof discipline parent equalStateFork.right where
  modification := identityModification .rightFork
  lineage := equalStateFork.parent_of_right
  receipt := rightReceipt
  current := by
    simp [IssuedReceipt.CurrentAt, rightReceipt]

/-- Positive fork control: both equal-state children retain independently
source-scoped, current protected-family evidence. -/
theorem fork_preserves_all_obligations :
    Nonempty (Certified completeProfile) ∧
      Nonempty (Certified completeProfile) ∧
      leftReceipt.CurrentAt parent.id.read.revision ∧
      rightReceipt.CurrentAt parent.id.read.revision :=
  CurrentProtectedRevision.fork_preserves_both leftRevision rightRevision
    ⟨completeCertification⟩

def mergeReceipt :
    IssuedReceipt discipline RevisionProof.mergeStep where
  authority := ()
  sources := by
    change Finset (Fin 3)
    exact {0, 1}
  issuedAt := leftCopy.id.read.revision
  authorized := ()
  realizable := ()

def mergeRevision : CurrentProtectedRevision completeProfile completeProfile
    RevisionProof discipline leftCopy mergeCopies.child where
  modification := identityModification .mergeStep
  lineage := mergeCopies.left_parent
  receipt := mergeReceipt
  current := by
    simp [IssuedReceipt.CurrentAt, mergeReceipt]

/-- Sequential transport reaches the merge child while keeping the fork and
merge receipts separately current. -/
theorem sequential_fork_merge_preserves :
    Nonempty (Certified completeProfile) ∧
      leftReceipt.CurrentAt parent.id.read.revision ∧
      mergeReceipt.CurrentAt leftCopy.id.read.revision :=
  CurrentProtectedRevision.sequential_preserves leftRevision mergeRevision
    ⟨completeCertification⟩

/-- A candidate profile with no ethical-evidence fibre. -/
def missingEthicalProfile : ProtectedProfile where
  Evidence
    | .ethical => Empty
    | _ => Unit

/-- Required negative control: there is no total protected-family revision
from a certified profile into one that lacks selected ethical evidence. -/
theorem missing_protected_evidence_blocks_revision (Proof : Type uProof) :
    ¬ Nonempty (FamilyPreservingRevision completeProfile
      missingEthicalProfile Proof) := by
  rintro ⟨revision⟩
  have missing : Empty :=
    revision.preserves.map ObligationKind.ethical
      (Set.mem_univ ObligationKind.ethical) ()
  exact nomatch missing

def staleLeftReceipt :
    IssuedReceipt discipline RevisionProof.leftFork :=
  { leftReceipt with issuedAt := by change Nat; exact 1 }

/-- Receipt source scope and currentness are independent of the family map. -/
theorem stale_receipt_does_not_license_parent_revision :
    ¬ staleLeftReceipt.CurrentAt parent.id.read.revision := by
  change (1 : Nat) ≠ 0
  decide

end Canary

#print axioms FamilyPreservingRevision.comp_transportCertified
#print axioms CurrentProtectedRevision.preserves_certification
#print axioms CurrentProtectedRevision.sequential_preserves
#print axioms CurrentProtectedRevision.fork_preserves_both
#print axioms Canary.fork_preserves_all_obligations
#print axioms Canary.sequential_fork_merge_preserves
#print axioms Canary.missing_protected_evidence_blocks_revision
#print axioms Canary.stale_receipt_does_not_license_parent_revision

end Mettapedia.CognitiveArchitecture.Agent.ProtectedSelfRevision
