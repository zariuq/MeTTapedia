import Mettapedia.Machines.ImmediateStorePrefixes
import Mettapedia.Languages.MeTTa.ContextualTransform.ImmediateRemoval

/-! Derived executable consumer of immediate/publication correspondence. -/

open Mettapedia.Machines
open ImmediateStorePublication
open ImmediateStorePublication.Controls
open Mettapedia.Languages.MeTTa.ContextualTransform
open Mettapedia.Data.List
open Cursor.ReadOnlyQuery

def main : IO Unit := do
  let direct := QueryState.run (immediate id) appendThenRefuse emptyWorld
  let recorded := QueryState.run (staged id true true) appendThenRefuse (emptyWorld, 0)
  let ordinary := QueryState.run (staged id false true) appendThenRefuse (emptyWorld, 0)
  IO.println s!"replies agree={decide (direct.answer = recorded.answer && direct.answer = ordinary.answer)}"
  IO.println s!"store after later refusal={reprStr direct.state.rows}"
  IO.println s!"recorded tickets={recorded.state.2}; ordinary tickets={ordinary.state.2}"
  IO.println s!"recording refusal={reprStr (staged id true false (emptyWorld, 0) put).1}"
  let rows := ImmediateRemoval.Controls.copies
  let chosen := (CountedErase.scan (fun n => n % 2 == 0) 1 rows.rows).1
  IO.println s!"first-only survivors={reprStr (ImmediateRemoval.publishSelected rows chosen).2.rows}"
  IO.println s!"all-equal survivors={reprStr (immediate (fun n => n % 2) rows ⟨.erase [0], true⟩).2.rows}"
  let finished := ImmediateStorePrefixes.Controls.resumed
  IO.println s!"resumed charge={finished.1}; tickets={(Sampled.savedState (staged id true true) finished.2).1.2}"
