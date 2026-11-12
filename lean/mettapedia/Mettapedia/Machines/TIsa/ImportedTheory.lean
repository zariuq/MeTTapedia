import Mettapedia.Machines.TIsa.JsonImport

/-!
# The actual native 23-rule table

The elaborator imports the native export as literal constructors. The kernel
checks every coordinate compiler certificate. The theorem concerns matching
and conclusion production, with privileged C leaf publishers kept explicit.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.Machines.TIsa.ImportedTheory

open RuleTable TheoryData

def entries : List Entry :=
  tisa_theory% "../../../tcalc/tisa/manifests/lean_tcalc_theory_v1.json"

theorem table_checked : checkedKernelTable? entries = true := by decide

theorem exact_inventory : entries.length = 23 ∧
    (entries.filter fun entry => entry.role == .publisher).length = 12 ∧
    (entries.filter fun entry => entry.role == .premise).length = 11 := by decide

/-- Each actual premise-bearing row implements its own source rule in both directions. -/
theorem all_premise_rows_correspond (entry : Entry) (member : entry ∈ entries) (plan : Plan)
    (role : entry.role = .premise) (selected : entry.plan = some plan)
    (premises : List Tuple) (output : Tuple) :
    plan.run premises = some output ↔ Derives entry.source premises output :=
  entry.premise_correspondence plan role selected
    (checkedKernelTable_member entries table_checked entry member) premises output

/-- Publisher correspondence accounts for supplied words without granting them logical truth. -/
theorem all_publishers_accounted (entry : Entry) (member : entry ∈ entries)
    (arguments : List Word) (output : Tuple) (published : entry.publish arguments = some output) :
    Derives entry.source [] output :=
  entry.publish_reflects_source arguments output
    (checkedKernelTable_member entries table_checked entry member) published

private def removeGuard (entry : Entry) : Entry :=
  if entry.id = 22 then {entry with plan := entry.plan.map fun plan => {plan with guards := plan.guards.drop 1}}
  else entry

private def changeSpace (entry : Entry) : Entry :=
  if entry.id = 14 then {entry with plan := entry.plan.map fun plan => {plan with outputTag := plan.outputTag + 2}}
  else entry

private def removeOutput (entry : Entry) : Entry :=
  if entry.id = 20 then {entry with plan := entry.plan.map fun plan => {plan with outputFields := plan.outputFields.drop 1}}
  else entry

theorem missing_guard_rejected : checkedKernelTable? (entries.map removeGuard) = false := by decide

theorem wrong_space_rejected : checkedKernelTable? (entries.map changeSpace) = false := by decide

theorem wrong_gather_rejected : checkedKernelTable? (entries.map removeOutput) = false := by decide

#print axioms table_checked
#print axioms all_premise_rows_correspond
#print axioms all_publishers_accounted

end Mettapedia.Machines.TIsa.ImportedTheory
