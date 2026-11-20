import Mettapedia.Languages.MeTTa.ContextualTransform.RetainedStorePrograms
import Mettapedia.Machines.PreparedReceiptOwnership
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.OrderedStoreStability

/-! Derived consumer of preparation stability, receipt graphs and retained IDs. -/

open Mettapedia.Machines
open Mettapedia.Data.List
open Mettapedia.Languages.MeTTa.ContextualTransform
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

def main : IO Unit := do
  let before := PreparedStoreStability.Controls.original
  let changed := PreparedStoreStability.Controls.changed
  let pending := PreparedStoreStability.Controls.waiting
  IO.println s!"changed rows={before.rows.length}->{changed.rows.length}; preparation valid={decide (PreparedStoreProtocol.Ready PreparedStoreStability.Controls.value changed pending)}"
  let store := OrderedStoreStability.Controls.store
  let altered := fire store OrderedStoreStability.Controls.makesObserved
  IO.println s!"after writer: absence valid={decide (Enabled id altered OrderedStoreStability.Controls.waitingAbsent)}; keep valid={decide (Enabled id altered OrderedStoreStability.Controls.waitingKeep)}"
  IO.println s!"same count={decide ((regionOf id store (· != 0)).card = (regionOf id altered (· != 0)).card)}; captured region valid={decide (Enabled id altered OrderedStoreStability.Controls.capturedRegion)}"
  let receipt := PreparedReceiptOwnership.Controls.receipt
  let heap := PreparedReceiptOwnership.Controls.heap
  let exported := PreparedReceiptOwnership.Controls.exported
  IO.println s!"receipt entries={(PreparedReceiptOwnership.addresses receipt).length}; roots={exported.card}; graph cells={(ResourceOwnership.census heap exported).card}"
  IO.println s!"removed rows={PreparedReceiptOwnership.Controls.publication.2.world.rows.length}; old preparation valid={decide (PreparedStoreProtocol.Ready PreparedReceiptOwnership.Controls.address PreparedReceiptOwnership.Controls.publication.2.world PreparedReceiptOwnership.Controls.plan)}"
  let unowned := ResourceOwnership.cancel
    (PreparedReceiptOwnership.patch PreparedReceiptOwnership.Controls.address
      PreparedReceiptOwnership.Controls.roots PreparedReceiptOwnership.Controls.plan)
    (PreparedReceiptOwnership.deadOwners ({99} : Finset Nat))
  let released := ResourceOwnership.release exported (.external 7)
  IO.println s!"without receipt ownership={(ResourceOwnership.census heap unowned).card}; after final release={(ResourceOwnership.census heap released).card}"
  let single := PreparedReceiptOwnership.patch PreparedReceiptOwnership.Controls.address
    PreparedReceiptOwnership.Controls.roots PreparedReceiptOwnership.Controls.oneTaken
  IO.println s!"one occurrence removed: remaining roots={single.card}; graph cells={(ResourceOwnership.census heap single).card}"
  let held := RetainedStorePrograms.Controls.held
  let program := RetainedStorePrograms.Controls.cycle
  let start := RetainedStorePrograms.Controls.empty
  let retained := QueryState.run (RetainedStorePrograms.backend held) program start
  let free := QueryState.run (RetainedStorePrograms.backend []) program start
  IO.println s!"retained IDs={reprStr (retained.state.val.map (fun row => row.identity))}; released IDs={reprStr (free.state.val.map (fun row => row.identity))}; same answers={decide (retained.answer = free.answer)}"
