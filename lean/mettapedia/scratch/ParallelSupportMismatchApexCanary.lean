import ParallelSupportMismatchStopCanary

/-!
# Parallel support-mismatch apex canary

This file tests the exact parent-cospan endpoint produced by the admitted
parallel stop when the canonicalization key depth and restoration depth are
different.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ParallelSupportMismatchApexCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open ParallelSupportMismatchStopCanary

noncomputable def leftEnvironment :=
  CostStaticAtomEnvironment.ofInventory
    (leftView.node.semanticAtomEnvironment
      (leftView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1

noncomputable def rightEnvironment :=
  CostStaticAtomEnvironment.ofInventory
    (rightView.node.semanticAtomEnvironment
      (rightView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1

noncomputable def cospan := leftEnvironment.semanticKeyCospan rightEnvironment

theorem leftEntries_length :
    leftView.node.finiteBoundaryTable.entries.length = 2 := by
  decide

theorem rightEntries_length :
    rightView.node.finiteBoundaryTable.entries.length = 2 := by
  decide

noncomputable def leftExposedEntry :=
  leftView.node.finiteBoundaryTable.entries[0]'(by
    rw [leftEntries_length]
    decide)

noncomputable def leftSealedEntry :=
  leftView.node.finiteBoundaryTable.entries[1]'(by
    rw [leftEntries_length]
    decide)

noncomputable def rightSealedEntry :=
  rightView.node.finiteBoundaryTable.entries[0]'(by
    rw [rightEntries_length]
    decide)

noncomputable def rightExposedEntry :=
  rightView.node.finiteBoundaryTable.entries[1]'(by
    rw [rightEntries_length]
    decide)

noncomputable def leftExposedName :=
  costRegionBoundaryVariableName leftExposedEntry.boundary

noncomputable def leftSealedName :=
  costRegionBoundaryVariableName leftSealedEntry.boundary

noncomputable def rightSealedName :=
  costRegionBoundaryVariableName rightSealedEntry.boundary

noncomputable def rightExposedName :=
  costRegionBoundaryVariableName rightExposedEntry.boundary

theorem leftAbstract_shape :
    leftView.node.plan.abstractPattern =
      .collection rhoReflectivePresentation.parallelCollection
        [.apply "PDrop" [.fvar leftExposedName],
          .apply "PDrop"
            [.apply "NQuote" [.apply "PDrop" [.fvar leftSealedName]]]]
        none := by
  rfl

theorem rightAbstract_shape :
    rightView.node.plan.abstractPattern =
      .collection rhoReflectivePresentation.parallelCollection
        [.apply "PDrop"
            [.apply "NQuote" [.apply "PDrop" [.fvar rightSealedName]]],
          .apply "PDrop" [.fvar rightExposedName]]
        none := by
  rfl

end ParallelSupportMismatchApexCanary
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
