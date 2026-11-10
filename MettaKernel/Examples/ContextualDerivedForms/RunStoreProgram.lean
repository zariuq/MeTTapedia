import Mettapedia.Languages.MeTTa.ContextualTransform.StoreProgramPrefixes

/-! Derived consumer of the checked adaptive store interpretation and cursor. -/

open Mettapedia.Languages.MeTTa.ContextualTransform
open Mettapedia.Machines
open Cursor.ReadOnlyQuery
open ConcreteStorePrograms

private def visible (state : AdaptiveStorePrograms.State Id) : String :=
  let names := (AdaptiveStorePrograms.decode label state).map fun atom =>
    match atom with
    | .symbol name => name
    | other => reprStr other
  "[" ++ String.intercalate ", " names ++ "]"

def main : IO Unit := do
  let cut := StoreProgramPrefixes.Controls.cut
  let finished := StoreProgramPrefixes.Controls.finished
  let backend := StoreProgramPrefixes.Controls.backend
  IO.println s!"prefix charge={cut.1}; completed={(Sampled.completed? backend cut.2).isSome}"
  IO.println s!"prefix store={visible (Sampled.savedState backend cut.2).1}"
  IO.println s!"resumed charge={finished.1}; completed={(Sampled.completed? backend finished.2).isSome}"
  IO.println s!"resumed store={visible (Sampled.savedState backend finished.2).1}"
  IO.println s!"answers correct={decide ((Sampled.completed? backend finished.2).map (fun result => result.answer) = some expected)}"
