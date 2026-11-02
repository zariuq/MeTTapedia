import Mettapedia.Machines.LiveRegionAdmission
import Mettapedia.GSLT.Contracts.RelyGuaranteeClaims

/-!
# Read-certificate stability as a region rely condition

A captured adaptive read certificate is stable under changes that agree on
its observed coordinates. A region may write only its declared write set.
Disjoint cross read/write footprints establish coexistence in the existing
rely–guarantee separation algebra. Relevant writes instead require live
validation or replanning; this model does not ban those writes globally.

Keys must include the relevant owner, definition, profile and scope identities
when those affect execution. Exact value comparison is not a claim that a
hash or an unqualified revision number suffices. Native atomicity is separate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RegionDependencyStability

open Mettapedia.GSLT.Contracts

universe u
variable {Key Value : Type u}

def retains (reads : ReadOnlyQuery.Reads Key Value) (before after : Key → Value) : Prop :=
  ∀ observed ∈ reads, after observed.1 = before observed.1

def writesOnly (writes : Finset Key) (before after : Key → Value) : Prop :=
  ∀ key, key ∉ writes → after key = before key

def claim (reads : ReadOnlyQuery.Reads Key Value) (writes : Finset Key) : RGClaim (Key → Value) where
  assertion := {world | ReadOnlyQuery.Agrees world reads}
  rely := retains reads
  guarantee := writesOnly writes
  stable := by
    intro before after valid untouched observed member
    exact (untouched observed member).trans (valid observed member)

/-- Each side's writes leave the other side's complete captured reads intact. -/
theorem coexist_of_cross_footprints
    (firstReads secondReads : ReadOnlyQuery.Reads Key Value) (firstWrites secondWrites : Finset Key)
    (firstSafe : ∀ observed ∈ secondReads, observed.1 ∉ firstWrites)
    (secondSafe : ∀ observed ∈ firstReads, observed.1 ∉ secondWrites) :
    RGClaim.Coexist (claim firstReads firstWrites) (claim secondReads secondWrites) := by
  constructor
  · intro before after changed observed member
    exact changed observed.1 (firstSafe observed member)
  · intro before after changed observed member
    exact changed observed.1 (secondSafe observed member)

theorem retains_trans (reads : ReadOnlyQuery.Reads Key Value)
    (first second third : Key → Value) (a : retains reads first second) (b : retains reads second third) :
    retains reads first third := fun observed member => (b observed member).trans (a observed member)

theorem retains_refl (reads : ReadOnlyQuery.Reads Key Value) (world : Key → Value) :
    retains reads world world := fun _ _ => rfl

theorem certificate_survives (reads : ReadOnlyQuery.Reads Key Value)
    (before after : Key → Value) (valid : ReadOnlyQuery.Agrees before reads)
    (unchanged : retains reads before after) : ReadOnlyQuery.Agrees after reads := by
  intro observed member
  exact (unchanged observed member).trans (valid observed member)

theorem successful_validation_survives [DecidableEq Value] (reads : ReadOnlyQuery.Reads Key Value)
    (before after : Key → Value) (valid : ReadOnlyQuery.checkReads before reads = true)
    (unchanged : retains reads before after) : ReadOnlyQuery.checkReads after reads = true := by
  exact (ReadOnlyQuery.checkReads_iff after reads).2
    (certificate_survives reads before after ((ReadOnlyQuery.checkReads_iff before reads).1 valid) unchanged)

theorem update_writesOnly [DecidableEq Key] (writes : Finset Key) (world : Key → Value)
    (key : Key) (value : Value) (permitted : key ∈ writes) :
    writesOnly writes world (Function.update world key value) := by
  intro other outside
  have apart : other ≠ key := fun same => outside (same ▸ permitted)
  simp [apart]

theorem update_retains [DecidableEq Key] (reads : ReadOnlyQuery.Reads Key Value)
    (world : Key → Value) (key : Key) (value : Value)
    (unread : ∀ observed ∈ reads, observed.1 ≠ key) :
    retains reads world (Function.update world key value) := by
  intro observed member
  simp [unread observed member]

namespace Controls

def first : RGClaim (Nat → Nat) := claim [(0, 5)] {0}
def second : RGClaim (Nat → Nat) := claim [(1, 8)] {1}

theorem disjoint_regions_coexist : RGClaim.Coexist first second := by
  apply coexist_of_cross_footprints <;> simp

theorem same_read_and_write_do_not_coexist : ¬ RGClaim.Coexist first first := by
  intro coexist
  have permitted : writesOnly ({0} : Finset Nat) (fun _ => 5) (Function.update (fun _ => 5) 0 6) :=
    update_writesOnly _ _ _ _ (by simp)
  have impossible := coexist.1 (fun _ => 5) (Function.update (fun _ => 5) 0 6) permitted (0, 5) (by simp)
  norm_num at impossible

theorem irrelevant_write_keeps_certificate :
    ReadOnlyQuery.checkReads (Function.update (fun _ : Nat => 5) 1 99) [(0, 5)] = true := by decide

theorem relevant_write_invalidates_certificate :
    ReadOnlyQuery.checkReads (Function.update (fun _ : Nat => 5) 0 6) [(0, 5)] = false := by decide

end Controls

end Mettapedia.Machines.RegionDependencyStability
