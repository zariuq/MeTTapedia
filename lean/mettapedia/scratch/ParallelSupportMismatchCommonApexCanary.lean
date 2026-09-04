import ParallelSupportMismatchApexCanary

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ParallelSupportMismatchApexCanary

open Mettapedia.GSLT.LanguageDef
open ParallelSupportMismatchStopCanary

example (availableDepth scopeDepth rootDepth : Nat) :
    RhoReachedPlanPairCommonApex leftView rightView availableDepth scopeDepth
      rootDepth leftView.node.plan.abstractPattern
        rightView.node.plan.abstractPattern := by
  dsimp only [RhoReachedPlanPairCommonApex]
  apply CostStaticAtomKeyCospan.CommonRestorationApex.of_eq
  simp [leftEnvironment, rightEnvironment, cospan,
    ParallelSupportMismatchStopCanary.leftView,
    ParallelSupportMismatchStopCanary.rightView,
    ParallelSupportMismatchStopCanary.leftViewPair,
    ParallelSupportMismatchStopCanary.rightViewPair]

end ParallelSupportMismatchApexCanary
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
