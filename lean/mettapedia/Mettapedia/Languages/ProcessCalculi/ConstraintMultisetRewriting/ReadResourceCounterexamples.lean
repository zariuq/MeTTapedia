import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PositiveResourceProjection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-!
# Arbitrary resource read footprints do not imply ordinary rule admission

The forward resource projection is sound for an actual qualified selection.
Its resource-instance carrier alone does not check that the instance's read
ports match the source rule. Consequently its unqualified converse is false,
already for one required read over the empty world.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadResourceCounterexamples

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ConstraintMultisetRewriting.Controls (signature A zero)
open PositiveResourceProjection

noncomputable section
local instance : DecidableEq (Term signature) := Classical.decEq _

def requiresOne : RuleInstance (Term signature) := ⟨[], [.const 0], [], [], []⟩
def emptyPorts : Selection Nat := ⟨[], [], []⟩
def constantLabel (_ : Nat) : Term signature := .const 0
def emptyWorld : Configuration (Term signature) Nat := ⟨[], ∅⟩

/-- The arbitrary footprint omits the source rule's required read. The
resource system therefore accepts a firing from the empty bag. -/
theorem arbitrary_footprint_is_enabled :
    (resources A zero constantLabel).Enables 0 (site := ⟨requiresOne⟩) ⟨emptyPorts⟩ := by
  change (0 : Multiset (Term signature)) + 0 ≤ 0
  exact le_rfl

/-- No ordinary selection can implement that source rule over the empty
physical world, regardless of what substitution it proposes. -/
theorem required_read_cannot_fire_in_empty_world (selection : Selection Nat) :
    ¬selection.Valid A constantLabel requiresOne emptyWorld := by
  intro valid
  have positive : 0 < selection.read.length := by
    rw [← valid.read_length]
    exact Nat.zero_lt_succ _
  let occurrence := selection.read.get ⟨0, positive⟩
  have present : occurrence ∈ emptyWorld.present :=
    valid.occurrences.kept_subset (by
      simpa only [Selection.commit, List.mem_toFinset] using
        List.get_mem selection.read ⟨0, positive⟩)
  exact Finset.notMem_empty occurrence present

theorem unqualified_resource_converse_is_false :
    (resources A zero constantLabel).Enables 0 (site := ⟨requiresOne⟩) ⟨emptyPorts⟩ ∧
      ¬∃ selection : Selection Nat, selection.Valid A constantLabel requiresOne emptyWorld :=
  ⟨arbitrary_footprint_is_enabled, fun ⟨selection, valid⟩ =>
    required_read_cannot_fire_in_empty_world selection valid⟩

end
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadResourceCounterexamples
