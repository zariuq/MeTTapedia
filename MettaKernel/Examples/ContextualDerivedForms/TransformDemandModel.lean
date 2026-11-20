import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaTransformDemand

/-! Derived consumer of authored transform traces and common-cursor demand. -/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines
open Mettapedia.Languages.MeTTa.PeTTa.LibTransform
open Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaTransformDemand
open Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaTransformDemand.Controls

def names (atoms : List Atom) : List String := atoms.map fun atom =>
  match atom with
  | .symbol name => name
  | _ => "expression"

def main : IO Unit := do
  IO.println s!"zero demand unchanged={decide (zero.answers = [] && zero.world == start)}"
  IO.println s!"source first={reprStr (names firstSource.1)}; store={reprStr (names firstSource.2.1)}"
  IO.println s!"cursor first={reprStr (names one.answers)}; store={reprStr (names one.world)}"
  let afterChange := ScopedCommit.resume (ScopedCommitCursor.sourceView one).2.2 [.symbol "outside", .symbol "c"]
  IO.println s!"consumer-change resume={reprStr (names afterChange.1)}; store={reprStr (names afterChange.2)}"
  let restarted := (job [.symbol "a", .symbol "c"]).drain
  let continued := (firstSource.2.2 [.symbol "a", .symbol "c"]).drain
  IO.println s!"restart store={reprStr (names restarted.2)}; residual store={reprStr (names continued.2)}"
  IO.println s!"poll cutoff answers={reprStr (names limited.answers)}; reason={reprStr limited.stop}"
  IO.println s!"resumed answers={reprStr (names resumed.answers)}; reason={reprStr resumed.stop}"
  let claimed := (transform contention result pairs).drain
  IO.println s!"contention order preserved={decide (claimed.1 = [.expression [.symbol "done", .symbol "a", .symbol "alice"], .expression [.symbol "done", .symbol "b", .symbol "bob"]])}; remaining={claimed.2.length}"
  let empty := select 1 (transform source (.expression [.symbol ","])) start
  IO.println s!"empty template: answers={empty.1.length}; remaining={empty.2.1.length}"
