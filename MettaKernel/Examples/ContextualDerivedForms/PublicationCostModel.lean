import Mettapedia.Machines.ImmediateStoreCost
import Mettapedia.Languages.MeTTa.ContextualTransform.HybridImmediateRemoval

/-! Derived consumer of the checked list-work and mixed-publication models. -/

open Mettapedia.Data.List
open Mettapedia.Machines

private def workLine (name : String) (work : PublicationWork.Work) : String :=
  s!"{name}: predicates={work.predicates} comparisons={work.comparisons} cells={work.cells} price={work.price 1 1 1}"

def main : IO Unit := do
  let direct := PublicationWork.immediate (· == 7) [7, 8, 7]
  let staged := PublicationWork.prepared (· == 7) [7, 8, 7]
  IO.println (workLine "fused" direct.work)
  IO.println (workLine "prepared" staged.work)
  IO.println s!"same result={decide (staged.value = some direct.value)}"
  IO.println s!"changed selection refused={(PublicationWork.checked (· == 7) [7] [7, 7]).value.isNone}"
  IO.println s!"pause charge={ImmediateStoreCost.Controls.firstCut.1}; resumed charge={ImmediateStoreCost.Controls.resumed.1}"
  IO.println s!"prepared pause charge={ImmediateStoreCost.Controls.preparedCut.1}; resumed charge={ImmediateStoreCost.Controls.preparedResumed.1}"
  let mixed := HybridStorePublication.Controls.mixed
  let refused := HybridStorePublication.removeAll (· == 7) 0 mixed
  let broken := HybridStorePublication.denseFirst (· == 7) 0 mixed
  let accepted := HybridStorePublication.removeAll (· == 7) 1 mixed
  IO.println s!"mixed refused={refused.1.isNone}; remaining-seven={(HybridShapeStore.denote refused.2).count 7}"
  IO.println s!"dense-first refused={broken.1.isNone}; remaining-seven={(HybridShapeStore.denote broken.2).count 7}"
  IO.println s!"mixed accepted={accepted.1.getD 0}; remaining-eight={(HybridShapeStore.denote accepted.2).count 8}"
