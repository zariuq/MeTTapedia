import Mettapedia.Algorithms.Compression.TensorSelection
import Lean.Util.CollectAxioms
import Lean.Data.Json.Printer

namespace Mettapedia.Examples.Compression.TensorSelectionControls

open Mettapedia.Algorithms.Compression.TensorSelection

theorem positive_negative_and_missing :
    selectCells [some true, some false, none, some true]
      [some 7, some 8, some 9, none] [none, some 3, some 4, some 5] =
        some [some 7, some 3, none, (none : Option Nat)] := by decide

theorem not_intersection_of_all_three_supports :
    writeSelected 0 [some true, some false] [some 7, none] [none, some 3] =
      some [(0, 7), (1, 3)] := by decide

theorem absent_condition_is_not_a_false_observation :
    selectCells [none] [some 7] [some 3] ≠ selectCells [some false] [some 7] [some 3] := by decide

theorem no_implicit_scalar_broadcast :
    selectCells [some true, some false] [some 7] [some 8, some 9] = none := by decide

theorem empty_shape_still_checks_other_shapes :
    selectCells [] ([] : List (Option Nat)) [some 7] = none := by decide

theorem count_only_selected_support :
    countSelected [some true, none, some false, some true]
      [some 7, some 1, some 2, none] [none, some 3, some 4, some 9] = some 2 := by decide

theorem ordered_two_pass_output :
    writeSelected 4 [some true, none, some false, some true]
      [some 7, some 1, some 2, none] [none, some 3, some 4, some 9] =
        some [(4, 7), (6, 4)] := by decide

theorem preserves_duplicate_occurrences :
    writeSelected 0 [some true, some true] [some 7, some 7] [none, none] =
      some [(0, 7), (1, 7)] := by decide

def tree : DecisionTree 4 Nat :=
  .branch (fun i => if i.val < 2 then some true else some false)
    (.branch (fun i => if i.val = 0 then some true else none)
      (.leaf (fun _ => some 7)) (.leaf (fun _ => some 3)))
    (.leaf (fun i => some (10 + i.val)))

theorem nested_tree_reconstructs :
    DecisionTree.compile tree = some [some 7, none, some 12, some 13] := by decide

theorem strict_fault_control :
    selectStrict (ε := Nat) (.ok (some true)) (.ok (some 7)) (.error 42) ≠ .ok (some 7) := by decide

end Mettapedia.Examples.Compression.TensorSelectionControls

open Lean Elab Command

run_cmd do
  let modules := #[`Mettapedia.Algorithms.Compression.TensorSelection,
    `Mettapedia.Examples.Compression.TensorSelectionControls]
  let allowed := #[``propext, ``Quot.sound, ``Classical.choice]
  let env ← getEnv
  let mut safe := 0
  let mut theorems := 0
  let mut compilerImplementations := 0
  for moduleName in modules do
    let declarations := if moduleName == env.header.mainModule then env.constants.toList.map Prod.fst else
      match env.header.moduleNames.toList.idxOf? moduleName with
      | some index => env.header.moduleData[index]!.constNames.toList
      | none => []
    for declName in declarations do
      unless moduleName.isPrefixOf declName do continue
      let some info := env.checked.get.find? declName | throwError "missing declaration {declName}"
      if info.isUnsafe || info.isPartial then
        unless declName.toString.endsWith "._unsafe_rec" do throwError "nonlogical declaration {declName}"
        compilerImplementations := compilerImplementations + 1
        continue
      if info matches .axiomInfo _ then throwError "added axiom {declName}"
      let dependencies ← liftCoreM <| collectAxioms declName
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "unpermitted dependency {declName}: {dependency}"
      safe := safe + 1
      if info matches .thmInfo _ then theorems := theorems + 1
  liftIO <| IO.println (Json.mkObj [("safeKernelDeclarations", toJson safe), ("theorems", toJson theorems),
    ("separateCompilerImplementations", toJson compilerImplementations)]).compress
