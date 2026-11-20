import Mettapedia.Machines.SymbolHeadMemo
import Mettapedia.Machines.SymbolHeadService
import Mettapedia.Languages.MeTTa.ContextualTransform.TransformHeadRecognition
import Mettapedia.Languages.MeTTa.ContextualTransform.SpecializedPublicationWork

/-! Derived consumer of measured specialization and scoped head recognition. -/

open Mettapedia.Data.List
open Mettapedia.Machines
open Mettapedia.Languages.MeTTa.ContextualTransform

def main : IO Unit := do
  let direct := PublicationSpecializationWork.first (fun n : Nat => n % 2 == 0) [1, 2, 4, 6]
  let prepared := PublicationSpecializationWork.preparedFirst (fun n : Nat => n % 2 == 0) [1, 2, 4, 6]
  IO.println s!"first survivors={reprStr direct.value.1}; predicates={direct.work.predicates}; cells={direct.work.cells}"
  IO.println s!"prepared first same={decide (prepared.value = some direct.value)}; price={prepared.work.price 1 1 1}"
  IO.println s!"append cells={(PublicationSpecializationWork.append [1, 2, 3] [4]).work.cells}; empty-take append cells={(PublicationSpecializationWork.appendAfterEmptyTake [1, 2, 3] [4]).work.cells}"
  let old := SymbolTableHeadCache.Controls.retained
  let fresh := SymbolTableHeadCache.Controls.replaced
  let names := SymbolTableHeadCache.Controls.names
  let permits := SymbolTableHeadCache.Controls.permits
  IO.println s!"stale raw IDs={SymbolTableHeadCache.recognized old permits 1 2}; guarded={(SymbolTableHeadCache.query fresh names permits (some old) 1 2).1}"
  IO.println s!"retired reference refused={(SymbolTableHeadCache.queryReference fresh names permits (some old) ⟨old.owner, 1⟩ 2).1.isNone}"
  let moved := SymbolTableHeadCache.transport SymbolTableHeadCache.Controls.original fresh ⟨old.owner, 1⟩
  IO.println s!"transferred ID={reprStr (moved.map (fun result => result.1.head))}; spelling={reprStr (moved.bind (fun result => SymbolTableHeadCache.decode result.2 result.1.head))}"
  IO.println s!"colliding head={SymbolHeadMemo.lookup SymbolHeadMemo.Controls.compiled SymbolHeadMemo.Controls.permits SymbolHeadMemo.Controls.cached 17 2}"
  let table := TransformHeadRecognition.Controls.table
  let cache := TransformHeadRecognition.Controls.cache
  IO.println s!"transform public={(SymbolTableHeadCache.query table TransformHeadRecognition.names TransformHeadRecognition.permits cache 1 (.publicCall 3)).1}; native-helper={(SymbolTableHeadCache.query table TransformHeadRecognition.names TransformHeadRecognition.permits cache 1 (.nativeCall 3)).1}"
  let life := QueryState.run (SymbolTableHeadCache.cachedStep names permits)
    SymbolTableHeadCache.Controls.lifecycle ⟨SymbolTableHeadCache.Controls.missing, none⟩
  IO.println s!"lifecycle replies correct={decide (life.answer = [.classified false, .classified true, .classified false])}"
  let both := QueryState.run (SymbolHeadService.step names permits)
    SymbolHeadService.Controls.lifecycle (SymbolHeadService.cold SymbolHeadService.Controls.original)
  IO.println s!"combined replies correct={decide (both.answer = [.classified true, .classified true, .classified false, .classified true])}"
  let paused := SymbolHeadService.Controls.cut
  let resumed := SymbolHeadService.Controls.finished
  let sample := SymbolHeadService.checkedStep names permits
  IO.println s!"pause charge={paused.1}; resumed charge={resumed.1}; incarnation={(Cursor.ReadOnlyQuery.Sampled.savedState sample resumed.2).1.val.table.owner.2}"
