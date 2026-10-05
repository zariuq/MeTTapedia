import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathConservation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSeparationControls

/-!
# Physical accounting of an authored copying program

The existing compiler-image example copies nonempty code with one purse cell
containing two signing atoms. The unrestricted communicated-purse example
violates the same inventory law. Both paths use the existing funded relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathControls

open ActivationSeparationControls

def compiledDuplication : CostStepPath source target :=
  .fire compiler_funded_source_fires (.done _)

/-- Exact accounting is a consequence of the general path theorem on an
inhabited compiler-image source, including a real duplicating communication. -/
theorem compiled_duplication_accounting :
    source.storedSignatures = target.storedSignatures + compiledDuplication.demands.sum :=
  compiledDuplication.stored_signatures_balance compiler_funded_source_separated

/-- The one cell funds one firing with two signing atoms. No one of these
three quantities is silently substituted for another. -/
theorem compiled_duplication_counts :
    compiledDuplication.length = 1 ∧ source.physicalPurseCells = 1 ∧
      source.storedSignatures.card = 2 ∧ target.storedSignatures = 0 := by
  refine ⟨rfl, compiler_funded_physical_counts.1, ?_, ?_⟩
  all_goals
    simp [source, target, copyBody, sender, ActivationCodeImage.wrappedCopyReceiver,
      ActivationCodeImage.wrappedNonemptyPayload, CostTerm.commSubst,
      CostTerm.substitute, CostTerm.components, CostConfig.storedSignatures,
      CostConfig.physicalPurseMeasure, CostTerm.physicalPurseMeasure,
      CostStack.storedSignatures]

def unrestrictedDuplication : CostStepPath unrestrictedSource unrestrictedTarget :=
  .fire unrestricted_source_fires (.done _)

/-- Sorting/runtime support alone cannot replace resource separation: the
actual unrestricted firing creates signing atoms in newly activated purses. -/
theorem unrestricted_duplication_breaks_accounting :
    unrestrictedSource.storedSignatures ≠
      unrestrictedTarget.storedSignatures + unrestrictedDuplication.demands.sum := by
  decide +kernel

/-- The physical firing bound also fails on this admitted unrestricted path. -/
theorem unrestricted_duplication_breaks_cell_bound :
    ¬ (unrestrictedDuplication.length + unrestrictedTarget.physicalPurseCells ≤
      unrestrictedSource.physicalPurseCells) := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathControls
