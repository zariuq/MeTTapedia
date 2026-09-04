import Mettapedia.Machines.RevisionedOccurrenceStore
import Mathlib.Data.Finset.Image

/-!
# Finite dependencies on revision-scoped store occurrences

A derived result may depend on exact logical occurrences from several stores.
The occurrence identity retains store, revision, and logical position; a finite
dependency set records which of those identities must remain current.

Validity is local.  Environments that agree on the stores named by a
dependency set give the same validity judgment.  Updating an unrelated store
therefore preserves validity, while changing the revision of any named store
invalidates every dependency on the old revision.

This is a source-validity contract, not a cache implementation.  Cache
invalidation may use the contract, but deleting or retaining physical entries
is a separate operational decision.
-/

set_option autoImplicit false

namespace Mettapedia.Machines

/-- The current revision selected for every logical store. -/
structure RevisionEnvironment (StoreId Revision : Type) where
  current : StoreId → Revision

namespace RevisionEnvironment

variable {StoreId Revision : Type}

/-- Change the current revision of exactly one store. -/
def update [DecidableEq StoreId]
    (environment : RevisionEnvironment StoreId Revision)
    (store : StoreId) (revision : Revision) :
    RevisionEnvironment StoreId Revision where
  current := Function.update environment.current store revision

/-- Two revision environments agree on a selected finite store support. -/
def AgreesOn [DecidableEq StoreId] (support : Finset StoreId)
    (left right : RevisionEnvironment StoreId Revision) : Prop :=
  ∀ store ∈ support, left.current store = right.current store

theorem agreesOn_refl [DecidableEq StoreId] (support : Finset StoreId)
    (environment : RevisionEnvironment StoreId Revision) :
    AgreesOn support environment environment := by
  intro store _
  rfl

theorem agreesOn_symm [DecidableEq StoreId] {support : Finset StoreId}
    {left right : RevisionEnvironment StoreId Revision}
    (agrees : AgreesOn support left right) :
    AgreesOn support right left := by
  intro store member
  exact (agrees store member).symm

theorem agreesOn_trans [DecidableEq StoreId] {support : Finset StoreId}
    {first second third : RevisionEnvironment StoreId Revision}
    (firstSecond : AgreesOn support first second)
    (secondThird : AgreesOn support second third) :
    AgreesOn support first third := by
  intro store member
  exact (firstSecond store member).trans (secondThird store member)

end RevisionEnvironment

/-- A finite set of exact occurrence identities consulted by a result. -/
abbrev RevisionDependencySet (StoreId Revision : Type) :=
  Finset (StoreOccurrenceId StoreId Revision)

namespace RevisionDependencySet

variable {StoreId Revision : Type}
variable [DecidableEq StoreId] [DecidableEq Revision]

/-- The finite set of stores on which the exact occurrences depend. -/
def storeSupport (dependencies : RevisionDependencySet StoreId Revision) :
    Finset StoreId :=
  dependencies.image fun occurrence => occurrence.read.storeId

/-- Every named occurrence belongs to the revision currently selected for its
store. -/
def ValidAt (environment : RevisionEnvironment StoreId Revision)
    (dependencies : RevisionDependencySet StoreId Revision) : Prop :=
  ∀ occurrence ∈ dependencies,
    environment.current occurrence.read.storeId = occurrence.read.revision

omit [DecidableEq StoreId] [DecidableEq Revision] in
@[simp] theorem validAt_empty
    (environment : RevisionEnvironment StoreId Revision) :
    ValidAt environment ∅ := by
  simp [ValidAt]

omit [DecidableEq StoreId] [DecidableEq Revision] in
@[simp] theorem validAt_singleton_iff
    (environment : RevisionEnvironment StoreId Revision)
    (occurrence : StoreOccurrenceId StoreId Revision) :
    ValidAt environment {occurrence} ↔
      environment.current occurrence.read.storeId =
        occurrence.read.revision := by
  simp [ValidAt]

@[simp] theorem validAt_union_iff
    (environment : RevisionEnvironment StoreId Revision)
    (left right : RevisionDependencySet StoreId Revision) :
    ValidAt environment (left ∪ right) ↔
      ValidAt environment left ∧ ValidAt environment right := by
  constructor
  · intro valid
    constructor
    · intro occurrence member
      exact valid occurrence (Finset.mem_union_left right member)
    · intro occurrence member
      exact valid occurrence (Finset.mem_union_right left member)
  · rintro ⟨leftValid, rightValid⟩ occurrence member
    rcases Finset.mem_union.mp member with leftMember | rightMember
    · exact leftValid occurrence leftMember
    · exact rightValid occurrence rightMember

omit [DecidableEq Revision] in
/-- Revision validity depends only on the current revisions of stores in the
finite support. -/
theorem validAt_iff_of_agreesOn_storeSupport
    {left right : RevisionEnvironment StoreId Revision}
    (dependencies : RevisionDependencySet StoreId Revision)
    (agrees : RevisionEnvironment.AgreesOn
      dependencies.storeSupport left right) :
    ValidAt left dependencies ↔ ValidAt right dependencies := by
  constructor
  · intro valid occurrence member
    have storeMember : occurrence.read.storeId ∈ dependencies.storeSupport :=
      Finset.mem_image.mpr ⟨occurrence, member, rfl⟩
    calc
      right.current occurrence.read.storeId =
          left.current occurrence.read.storeId :=
        (agrees occurrence.read.storeId storeMember).symm
      _ = occurrence.read.revision := valid occurrence member
  · intro valid occurrence member
    have storeMember : occurrence.read.storeId ∈ dependencies.storeSupport :=
      Finset.mem_image.mpr ⟨occurrence, member, rfl⟩
    calc
      left.current occurrence.read.storeId =
          right.current occurrence.read.storeId :=
        agrees occurrence.read.storeId storeMember
      _ = occurrence.read.revision := valid occurrence member

omit [DecidableEq Revision] in
/-- Advancing a store outside the finite support cannot stale the dependency
set. -/
theorem validAt_update_iff_of_not_mem_storeSupport
    (environment : RevisionEnvironment StoreId Revision)
    (dependencies : RevisionDependencySet StoreId Revision)
    (store : StoreId) (revision : Revision)
    (outside : store ∉ dependencies.storeSupport) :
    ValidAt (environment.update store revision) dependencies ↔
      ValidAt environment dependencies := by
  apply validAt_iff_of_agreesOn_storeSupport
  intro observed observedMember
  have different : observed ≠ store := by
    intro equalStore
    subst equalStore
    exact outside observedMember
  simp [RevisionEnvironment.update, different]

omit [DecidableEq Revision] in
/-- Advancing the store of a consulted occurrence to a genuinely different
revision makes the old finite dependency set invalid. -/
theorem not_validAt_update_of_mem
    (environment : RevisionEnvironment StoreId Revision)
    (dependencies : RevisionDependencySet StoreId Revision)
    (occurrence : StoreOccurrenceId StoreId Revision)
    (member : occurrence ∈ dependencies)
    (nextRevision : Revision)
    (changed : nextRevision ≠ occurrence.read.revision) :
    ¬ ValidAt
      (environment.update occurrence.read.storeId nextRevision)
      dependencies := by
  intro valid
  have current := valid occurrence member
  simp [RevisionEnvironment.update] at current
  exact changed current

end RevisionDependencySet

/-! ## Positive and negative controls -/

namespace RevisionDependencySetCanary

inductive Store where
  | evidence
  | model
  | unrelated
deriving DecidableEq

def environment : RevisionEnvironment Store Nat where
  current
    | .evidence => 7
    | .model => 3
    | .unrelated => 99

def evidenceOccurrence : StoreOccurrenceId Store Nat :=
  ⟨⟨.evidence, 7⟩, 0⟩

def modelOccurrence : StoreOccurrenceId Store Nat :=
  ⟨⟨.model, 3⟩, 4⟩

def dependencies : RevisionDependencySet Store Nat :=
  {evidenceOccurrence, modelOccurrence}

example : RevisionDependencySet.ValidAt environment dependencies := by
  simp [RevisionDependencySet.ValidAt, dependencies, evidenceOccurrence,
    modelOccurrence, environment]

/-- An unrelated store revision leaves the dependency set live. -/
example : RevisionDependencySet.ValidAt
    (environment.update .unrelated 100) dependencies := by
  rw [RevisionDependencySet.validAt_update_iff_of_not_mem_storeSupport]
  · simp [RevisionDependencySet.ValidAt, dependencies, evidenceOccurrence,
      modelOccurrence, environment]
  · simp [RevisionDependencySet.storeSupport, dependencies,
      evidenceOccurrence, modelOccurrence]

/-- Advancing a consulted store rejects its old occurrence identity. -/
example : ¬ RevisionDependencySet.ValidAt
    (environment.update .evidence 8) dependencies := by
  apply RevisionDependencySet.not_validAt_update_of_mem
    environment dependencies evidenceOccurrence
  · simp [dependencies]
  · decide

end RevisionDependencySetCanary

#print axioms RevisionDependencySet.validAt_iff_of_agreesOn_storeSupport
#print axioms RevisionDependencySet.validAt_update_iff_of_not_mem_storeSupport
#print axioms RevisionDependencySet.not_validAt_update_of_mem

end Mettapedia.Machines
