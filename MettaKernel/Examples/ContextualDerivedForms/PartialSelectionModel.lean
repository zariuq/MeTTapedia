import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaSelectionCursor

/-! Derived consumer of partial selection and its source removal adapter. -/

open Mettapedia.Machines
open Mettapedia.Languages.MeTTa.ContextualTransform
open Cursor.ReadOnlyQuery

def main : IO Unit := do
  let test := EffectfulRowSelection.Controls.record
  let cut := EffectfulRowSelection.Controls.paused
  let resumed := EffectfulRowSelection.Controls.finished
  IO.println s!"paused={ (Sampled.completed? test cut.2).isNone }; earlier effects={reprStr (Sampled.savedState test cut.2).1}"
  IO.println s!"resumed result={reprStr ((Sampled.completed? test resumed.2).map (fun value => value.answer))}; effects={reprStr (Sampled.savedState test resumed.2).1}; charges={resumed.1}"
  let restarted := EffectfulRowSelection.reference test 10 [1, 2, 3, 4] (Sampled.savedState test cut.2).1
  IO.println s!"restart repeats effects={reprStr restarted.state}"
  let initial := EffectfulRowSelection.reference EffectfulRowSelection.Controls.changesDecision 0 [7] 0
  let rechecked := EffectfulRowSelection.reference EffectfulRowSelection.Controls.changesDecision 0 [7] initial.state
  IO.println s!"first selection={reprStr initial.answer}; rechecked={reprStr rechecked.answer}; effects={rechecked.state}"
  let pettaTest := PeTTaSelectionCursor.test PeTTaSelectionCursor.Controls.rows PeTTaSelectionCursor.Controls.pattern
  let petta := PeTTaSelectionCursor.Controls.finished
  IO.println s!"scoped selection={reprStr ((Sampled.completed? pettaTest petta.2).map (fun value => value.answer))}; charges={petta.1}"
  let step := Mettapedia.Languages.MeTTa.PeTTa.Unifying.step
    PeTTaSelectionCursor.Controls.registry PeTTaSelectionCursor.Controls.source
  IO.println s!"source survivors and uses={reprStr (step.map (fun result => (result.state.core.length, result.uses)))}"
  IO.println s!"source earlier output retained={reprStr (step.map (fun result => decide (result.output = PeTTaSelectionCursor.Controls.source.output)))}"
