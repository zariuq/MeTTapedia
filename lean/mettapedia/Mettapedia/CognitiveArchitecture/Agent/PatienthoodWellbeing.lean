import Mettapedia.CognitiveArchitecture.Agent.RevisionLineage

/-!
# Occurrence-indexed patienthood and observer-indexed wellbeing

Patienthood and wellbeing are separate evidence families.  A conservative
governance transition may retain existing patients and recognize fork or merge
descendants, but this is explicit policy data rather than a theorem of state
similarity or ancestry.

Wellbeing remains indexed by assessor, occurrence, and value.  Consequently,
two observationally equivalent occurrences need not have interchangeable
welfare evidence.  No personal-identity relation or scalar aggregation is
chosen here.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Agent.PatienthoodWellbeing

open Mettapedia.Machines
open Mettapedia.CognitiveArchitecture.Agent.RevisionLineage

universe uState uPatient uObserver uValue uEvidence

/-- Moral-patient evidence indexed by exact lineage occurrence. -/
structure PatienthoodSnapshot (Owner Revision : Type) where
  Evidence : StoreOccurrenceId Owner Revision → Type uPatient

/-- Wellbeing evidence is separately indexed by assessor, occurrence, and an
authored value carrier. -/
structure WellbeingJudgment (ObserverIndex : Type uObserver)
    (Owner Revision : Type) where
  Value : Type uValue
  Evidence : ObserverIndex → StoreOccurrenceId Owner Revision →
    Value → Type uEvidence

/-! ## Conservative non-erasure transports -/

/-- A fork policy retains the parent and admits both distinct children. -/
structure ForkPatienthoodTransport
    {Owner Revision : Type} {State : Type uState}
    (before after : PatienthoodSnapshot.{uPatient} Owner Revision)
    {parent : Node Owner Revision State} (fork : Fork parent) where
  retainParent : before.Evidence parent.id → after.Evidence parent.id
  admitLeft : before.Evidence parent.id → after.Evidence fork.left.id
  admitRight : before.Evidence parent.id → after.Evidence fork.right.id

namespace ForkPatienthoodTransport

variable {Owner Revision : Type} {State : Type uState}
variable {before after : PatienthoodSnapshot.{uPatient} Owner Revision}
variable {parent : Node Owner Revision State} {fork : Fork parent}

/-- One prior patient witness yields three occurrence-distinct witnesses in
the post-fork registry. -/
theorem non_erasure
    (transport : ForkPatienthoodTransport before after fork)
    (patient : before.Evidence parent.id) :
    Nonempty (after.Evidence parent.id) ∧
      Nonempty (after.Evidence fork.left.id) ∧
      Nonempty (after.Evidence fork.right.id) :=
  ⟨⟨transport.retainParent patient⟩, ⟨transport.admitLeft patient⟩,
    ⟨transport.admitRight patient⟩⟩

end ForkPatienthoodTransport

/-- A merge policy retains both parent patients and may recognize the new merge
descendant.  Nothing in the structure deletes or identifies a parent. -/
structure MergePatienthoodTransport
    {Owner Revision : Type} {State : Type uState}
    (before after : PatienthoodSnapshot.{uPatient} Owner Revision)
    {left right : Node Owner Revision State} (merge : Merge left right) where
  retainLeft : before.Evidence left.id → after.Evidence left.id
  retainRight : before.Evidence right.id → after.Evidence right.id
  admitChild : before.Evidence left.id → before.Evidence right.id →
    after.Evidence merge.child.id

namespace MergePatienthoodTransport

variable {Owner Revision : Type} {State : Type uState}
variable {before after : PatienthoodSnapshot.{uPatient} Owner Revision}
variable {left right : Node Owner Revision State} {merge : Merge left right}

/-- Merge construction retains both parent witnesses and a separately indexed
child witness. -/
theorem non_erasure
    (transport : MergePatienthoodTransport before after merge)
    (leftPatient : before.Evidence left.id)
    (rightPatient : before.Evidence right.id) :
    Nonempty (after.Evidence left.id) ∧
      Nonempty (after.Evidence right.id) ∧
      Nonempty (after.Evidence merge.child.id) :=
  ⟨⟨transport.retainLeft leftPatient⟩,
    ⟨transport.retainRight rightPatient⟩,
    ⟨transport.admitChild leftPatient rightPatient⟩⟩

end MergePatienthoodTransport

/-! ## Positive and negative controls -/

namespace Canary

open RevisionLineage.Canary

abbrev Occurrence := StoreOccurrenceId Owner Revision

/-- Evidence only for a finite, explicitly admitted occurrence list. -/
def Admitted (ids : List Occurrence) (id : Occurrence) : Type :=
  if id ∈ ids then Unit else Empty

def beforeFork : PatienthoodSnapshot Owner Revision where
  Evidence := Admitted [parent.id]

def afterFork : PatienthoodSnapshot Owner Revision where
  Evidence := Admitted [parent.id, leftCopy.id, rightCopy.id]

def forkTransport :
    ForkPatienthoodTransport beforeFork afterFork equalStateFork where
  retainParent := by
    intro _patient
    simpa [afterFork, Admitted] using ()
  admitLeft := by
    intro _patient
    simpa [afterFork, Admitted, equalStateFork] using ()
  admitRight := by
    intro _patient
    simpa [afterFork, Admitted, equalStateFork] using ()

def parentPatient : beforeFork.Evidence parent.id := by
  simpa [beforeFork, Admitted] using ()

/-- Required positive control: equal-state copying does not silently exclude
either child or erase the parent. -/
theorem fork_non_erasure :
    Nonempty (afterFork.Evidence parent.id) ∧
      Nonempty (afterFork.Evidence equalStateFork.left.id) ∧
      Nonempty (afterFork.Evidence equalStateFork.right.id) :=
  forkTransport.non_erasure parentPatient

def beforeMerge : PatienthoodSnapshot Owner Revision where
  Evidence := Admitted [leftCopy.id, rightCopy.id]

def afterMerge : PatienthoodSnapshot Owner Revision where
  Evidence := Admitted [leftCopy.id, rightCopy.id, mergeCopies.child.id]

def mergeTransport :
    MergePatienthoodTransport beforeMerge afterMerge mergeCopies where
  retainLeft := by
    intro _patient
    simpa [afterMerge, Admitted] using ()
  retainRight := by
    intro _patient
    simpa [afterMerge, Admitted] using ()
  admitChild := by
    intro _leftPatient _rightPatient
    simpa [afterMerge, Admitted, mergeCopies] using ()

def leftPatient : beforeMerge.Evidence leftCopy.id := by
  simpa [beforeMerge, Admitted] using ()

def rightPatient : beforeMerge.Evidence rightCopy.id := by
  simpa [beforeMerge, Admitted] using ()

/-- Required merge control: constructing a new descendant retains both parent
patients rather than replacing them by the child. -/
theorem merge_non_erasure :
    Nonempty (afterMerge.Evidence leftCopy.id) ∧
      Nonempty (afterMerge.Evidence rightCopy.id) ∧
      Nonempty (afterMerge.Evidence mergeCopies.child.id) :=
  mergeTransport.non_erasure leftPatient rightPatient

inductive WelfareValue where
  | supported
  | harmed
  deriving DecidableEq, Repr

/-- A deliberately occurrence-sensitive assessment.  The equal-state left
copy has evidence for `supported`; the right copy has evidence for `harmed`. -/
def wellbeing : WellbeingJudgment Unit Owner Revision where
  Value := WelfareValue
  Evidence _ id
    | .supported => if id = leftCopy.id then Unit else Empty
    | .harmed => if id = rightCopy.id then Unit else Empty

def leftSupported : wellbeing.Evidence () leftCopy.id .supported := by
  simpa [wellbeing] using ()

def rightHarmed : wellbeing.Evidence () rightCopy.id .harmed := by
  simpa [wellbeing] using ()

/-- Required negative control: exact observational equivalence of two states
does not make their occurrence-indexed wellbeing evidence interchangeable. -/
theorem observational_equivalence_not_welfare_interchangeability :
    ObservationallyEquivalent stateObserver leftCopy rightCopy ∧
      Nonempty (wellbeing.Evidence () leftCopy.id .supported) ∧
      IsEmpty (wellbeing.Evidence () rightCopy.id .supported) := by
  refine ⟨rfl, ⟨leftSupported⟩, ?_⟩
  change IsEmpty (if rightCopy.id = leftCopy.id then Unit else Empty)
  rw [if_neg (by decide : rightCopy.id ≠ leftCopy.id)]
  infer_instance

/-- Patienthood does not assert a positive wellbeing value: the right copy is
a retained patient while its `supported` fibre is empty. -/
theorem patienthood_is_not_positive_wellbeing :
    Nonempty (afterFork.Evidence rightCopy.id) ∧
      IsEmpty (wellbeing.Evidence () rightCopy.id .supported) := by
  refine ⟨fork_non_erasure.2.2, ?_⟩
  change IsEmpty (if rightCopy.id = leftCopy.id then Unit else Empty)
  rw [if_neg (by decide : rightCopy.id ≠ leftCopy.id)]
  infer_instance

def noPatienthood : PatienthoodSnapshot Owner Revision where
  Evidence := fun _ => Empty

/-- An ancestry edge alone does not manufacture patienthood evidence.  The
non-erasure policy is a separately supplied governance transport. -/
theorem ancestry_does_not_imply_patienthood :
    parent.IsParent leftCopy ∧
      IsEmpty (noPatienthood.Evidence leftCopy.id) := by
  constructor
  · exact equalStateFork.parent_of_left
  · change IsEmpty Empty
    infer_instance

end Canary

#print axioms ForkPatienthoodTransport.non_erasure
#print axioms MergePatienthoodTransport.non_erasure
#print axioms Canary.fork_non_erasure
#print axioms Canary.merge_non_erasure
#print axioms Canary.observational_equivalence_not_welfare_interchangeability
#print axioms Canary.patienthood_is_not_positive_wellbeing
#print axioms Canary.ancestry_does_not_imply_patienthood

end Mettapedia.CognitiveArchitecture.Agent.PatienthoodWellbeing
