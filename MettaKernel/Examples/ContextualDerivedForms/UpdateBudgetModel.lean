import Mettapedia.Languages.MeTTa.Experimental.DerivedTransformForms.BudgetCycle

/-! Executable consumer of the canonical source/transform update-credit laws. -/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.Experimental.DerivedTransformForms.BudgetCycle
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

def spellings (values : List Atom) : List String := values.map Atom.toString

def main : IO Unit := do
  IO.println s!"source replies={reprStr (spellings sourceResult.1)}"
  IO.println s!"source pending={reprStr (spellings sourceResult.2)}"
  IO.println s!"target q={reprStr (spellings (regionPayloads "q" targetRun.last.2))}"
  IO.println s!"target out={reprStr (spellings (regionPayloads "out" targetRun.last.2))}"
  IO.println s!"updates={ConsumableBudget.spendingCount charge targetRun}; primitive events={targetRun.word.length}"
  IO.println s!"initial credits={charge.potential (state [0, 1, 2, 3, 4])}; remaining credits={charge.potential targetRun.last}"
  let resumed := (Mettapedia.Languages.MeTTa.PeTTa.LibTransform.transform sources (reply (.var "j"))
    (sourceResult.2 ++ [credit (.symbol "three")])).drain
  IO.println s!"new credit replies={reprStr (spellings resumed.1)}; pending={reprStr (spellings resumed.2)}"
