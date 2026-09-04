import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticPairApex

/-!
# Flattened-leaf traversal semantics

Order, nested flattening, unit dropping at the declaration parameter, and the
non-parallel singleton — the four facts the occurrence-ordered reassembly
depends on, checked on closed instances.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ParallelLeafTraversal

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.RhoCommonRestorationApex

def authored := rhoReflectivePresentation.toReflectivePresentationDecl

/-- Nested bare parallels flatten in occurrence order, dropping the
declaration's own unit. -/
theorem leaves_flatten_ordered :
    parallelLeaves authored
        (.collection .hashBag
          [.fvar "a",
           .collection .hashBag [.fvar "b", .apply "PZero" []] none,
           .apply "PZero" []] none) =
      [.fvar "a", .fvar "b"] := by
  simp [parallelLeaves, parallelLeavesList, authored, rhoReflectivePresentation]

/-- A unit-only parallel has no leaves. -/
theorem leaves_unit_only_nil :
    parallelLeaves authored
        (.collection .hashBag [.apply "PZero" [], .apply "PZero" []] none) =
      [] := by
  simp [parallelLeaves, parallelLeavesList, authored, rhoReflectivePresentation]

/-- A non-parallel payload is its own singleton frontier. -/
theorem leaves_nonparallel_singleton :
    parallelLeaves authored (.apply "NQuote" [.apply "PZero" []]) =
      [.apply "NQuote" [.apply "PZero" []]] := by
  simp [parallelLeaves, authored, rhoReflectivePresentation]

/-- **Declaration sensitivity**: a foreign-tagged unit is NOT dropped by the
authored frontier — leaf lists must be computed at the declaration the
classifier permutation uses. -/
theorem leaves_keep_foreign_unit :
    parallelLeaves authored
        (.collection .hashBag [.apply (costBaseConstructorName "PZero") []]
          none) =
      [.apply (costBaseConstructorName "PZero") []] := by
  simp [parallelLeaves, parallelLeavesList, authored, rhoReflectivePresentation,
    costBaseConstructorName]
  decide

end ParallelLeafTraversal
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
