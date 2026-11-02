import Mettapedia.Languages.Maude.ACUFold
import Mettapedia.Languages.Maude.Examples

/-! Source-level ACU controls over the standard vending-machine theory.
Duplicate coins remain separate resources; unrelated constructor identities
and undeclared empty terms do not disappear during flattening. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude.ACUFoldControls

def operation : ACUOperation Examples.vending [] where
  declaration := ⟨"vending.merge", "__", ["Marking", "Marking"], "Marking",
    {constructor := true, associative := true, commutative := true,
      identity := some (.app "vending.empty" [])}⟩
  declared := by simp [Examples.vending, Examples.markingOperators, Examples.constant]
  arguments := rfl
  associative := rfl
  commutative := rfl
  unit := .app "vending.empty" []
  identity := rfl
  unit_sorted := .app
    (declaration := ⟨"vending.empty", "empty", [], "Marking", {constructor := true}⟩)
    (by simp [Examples.vending, Examples.markingOperators]) .nil

def dollar : Term := .app "vending.$" []
def quarter : Term := .app "vending.q" []
def coffee : Term := .app "vending.c" []

theorem dollar_sorted : HasSort Examples.vending.signature [] dollar "Marking" :=
  .app (declaration := ⟨"vending.$", "$", [], "Marking", {constructor := true}⟩)
    (by simp [Examples.vending, Examples.markingOperators]) .nil
theorem quarter_sorted : HasSort Examples.vending.signature [] quarter "Marking" :=
  .app (declaration := ⟨"vending.q", "q", [], "Marking", {constructor := true}⟩)
    (by simp [Examples.vending, Examples.markingOperators]) .nil
theorem coffee_sorted : HasSort Examples.vending.signature [] coffee "Marking" :=
  .app (declaration := ⟨"vending.c", "c", [], "Marking", {constructor := true}⟩)
    (by simp [Examples.vending, Examples.markingOperators]) .nil

theorem initial_sorted : operation.Sorted [quarter, dollar, quarter] := by
  intro term member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact quarter_sorted
  · exact dollar_sorted
  · exact quarter_sorted

#guard operation.flatten (operation.merge quarter (operation.merge dollar quarter)) = [quarter, dollar, quarter]
#guard operation.flatten (operation.merge operation.unit quarter) = [quarter]
#guard operation.flatten (operation.fold [quarter, quarter]) = [quarter, quarter]
#guard operation.flatten (.app "foreign.merge" [quarter, dollar]) = [.app "foreign.merge" [quarter, dollar]]
#guard operation.flatten (.app "foreign.empty" []) = [.app "foreign.empty" []]
#guard operation.flatten (.app "vending.merge" [quarter]) = [.app "vending.merge" [quarter]]

theorem duplicate_coins_preserved :
    (operation.flatten (operation.fold [quarter, quarter])).length = 2 := by decide_cbv

theorem insufficient_change :
    ¬ (operation.flatten (operation.fold [quarter, quarter, quarter])).Perm
      [quarter, quarter, quarter, quarter] := by decide_cbv

def coffeeRule : Row := ⟨"coffee", [], [], dollar, coffee⟩

theorem coffee_raw : RawStep Examples.vending [] "Marking" dollar coffee := by
  let assignment : Valuation := Term.var
  have typedAssignment : TypedValuation Examples.vending.signature [] coffeeRule.usedContext assignment := by
    intro name sort found
    simp [coffeeRule, Row.usedContext, Term.variables, dollar, coffee] at found
  simpa only [coffeeRule, dollar, coffee, Term.substitute, List.map_nil] using
    RawStep.rule (row := coffeeRule) assignment
    (by simp [Examples.vending, coffeeRule, dollar, coffee, Examples.constant]) (by decide_cbv)
    dollar_sorted coffee_sorted typedAssignment (.nil assignment)

theorem vending_fires_with_duplicates :
    Step Examples.vending [] "Marking" (operation.fold [quarter, dollar, quarter])
      (operation.fold [coffee, quarter, quarter]) := by
  have flatCoffee : operation.flatten coffee = [coffee] := by decide_cbv
  have result : operation.declaration.result = "Marking" := rfl
  simpa only [flatCoffee, List.cons_append, List.nil_append, result] using operation.step_of_subbag (by decide_cbv)
    (operation.fold_sorted _ initial_sorted) [dollar] [quarter, quarter]
    (by decide_cbv) (operation.right_unit dollar_sorted) coffee_raw

#print axioms duplicate_coins_preserved
#print axioms insufficient_change
#print axioms vending_fires_with_duplicates

end Mettapedia.Languages.Maude.ACUFoldControls
