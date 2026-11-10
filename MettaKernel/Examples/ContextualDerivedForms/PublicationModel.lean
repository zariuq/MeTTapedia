import Mettapedia.Machines.PreparedStoreProtocolControls

/-! Derived executable consumer of the checked publication model. -/

open Mettapedia.Machines.PreparedStoreProtocol
open Mettapedia.Machines.PreparedStoreProtocol.Controls

private def status : Publication Nat Nat → String
  | .refused fault => s!"refused {reprStr fault}"
  | .noMatch => "no-match"
  | .committed none => "committed unrecorded"
  | .committed (some receipt) => s!"committed records={receipt.length}"

def main : IO Unit := do
  IO.println s!"stale dense flags: initialized={(staleFlagReceipt [] [0, 1]).initialized}"
  IO.println s!"correct dense batch: {status (publish label (some 1) takeTwo).1}"
  let repeated := sequentialPhysicalTakes [0, 1] [0, 0]
  IO.println s!"repeated physical take: success={repeated.1} remaining={reprStr repeated.2}"
  IO.println s!"correct repeated keys: {status (publish label (some 1) takeRepeated).1}"
  IO.println s!"equal stored copies: {status (publish label (some 1) takeCopies).1}"
  IO.println s!"bad reprepare changes slot={decide ((retagThenReject (.erase [20]) pendingAddition).2.slot ≠ pendingAddition.slot)}"
  IO.println s!"correct reprepare preserves slot={decide ((prepare label (.erase [20]) false true pendingAddition).2.slot = pendingAddition.slot)}"
  IO.println s!"kind-and-space accepts wrong receipt={acceptsOnlyKindAndSpace planA receiptB}"
  IO.println s!"correct association: {status (publish label (some receiptB.ticket) takeA).1}"
  IO.println s!"ordinary publication: {status (publish label none pendingAddition).1}; tickets={pendingAddition.nextTicket}"
