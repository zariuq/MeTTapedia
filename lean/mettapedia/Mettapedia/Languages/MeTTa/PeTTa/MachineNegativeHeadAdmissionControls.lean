import Mettapedia.Languages.MeTTa.PeTTa.MachineNegativeHeadAdmission

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MachineNegativeHeadAdmission.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax SchematicRows ListView
open Unifying (Idempotent idempotent_bindVar bindVar)
open AtomNegativeFreshNamespaces (Frame X)
open AtomNegativeSchematicReads (E closures)
open MachineNegativeHeadExecution (data arguments state)

private def integer (value : Int) : Atom := .grounded (.int value)
private def frame : Frame := ⟨[(.var "v", integer 7)], by
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  change Atom.var "v" ≠ integer 7
  decide +kernel⟩
private def inputs : Subst := [("v", integer 9)]
private theorem valid : Idempotent inputs := by
  change Idempotent (bindVar [] "v" (integer 9))
  apply idempotent_bindVar idempotent_nil rfl
  · intro _ absent; cases absent
  · intro absent; cases absent
private def present : Finset Nat := {0}
private def label (_ : Nat) : Atom := .expression [.symbol "Saved", .var "v"]
private def rows : Finset Nat := {0}
private def source : Atom := MachineHeadSelection.row (.symbol "f") (integer 0)
  (MachineClauseReads.head (.expression [.var "v", .var "v"]))
private def sources (_ : Nat) : Atom := source
private def query (second : Int) : Atom := MachineHeadSelection.row (.symbol "f") (integer 0)
  (MachineClauseReads.head (.expression [integer 8, integer second]))

theorem actual_correlated_query_firing_is_admitted :
    (direct frame inputs present label rows sources 0 2 (query 8)).Admits X := by
  apply (admits_iff_computed frame inputs present label rows sources 0 2 (query 8)
    (by decide +kernel) (by decide +kernel) valid).mpr
  simp only [MachineNegativeHeadExecution.probe, AtomFreshNamespaces.sourceTerms,
    present, Finset.toList_singleton, List.map_singleton]
  decide +kernel

theorem inconsistent_repeated_parameter_refuses_the_actual_firing :
    ¬ (direct frame inputs present label rows sources 0 2 (query 9)).Admits X := by
  rw [admits_iff_computed frame inputs present label rows sources 0 2 (query 9)
    (by decide +kernel) (by decide +kernel) valid]
  simp only [MachineNegativeHeadExecution.probe, AtomFreshNamespaces.sourceTerms,
    present, Finset.toList_singleton, List.map_singleton]
  decide +kernel

theorem a_logical_match_does_not_supply_a_missing_physical_occurrence :
    MachineHeadSelection.accepted (MachineHeadSelectionApart.probe frame inputs source (query 8)) = true ∧
      ¬ (direct frame inputs present label ∅ sources 0 2 (query 8)).Admits X := by
  refine ⟨by decide +kernel, ?_⟩
  intro admitted
  have requirements := HeldReadGenericFirings.direct_admission_data (E := E) X
    (state frame inputs present label) ∅
    (closures (state frame inputs present label) (data sources) (arguments (query 8))) 0 PUnit.unit
    (rowOpening frame inputs present label ∅ sources (query 8) 0)
    (rowOpening frame inputs present label ∅ sources (query 8) 1) 2 admitted
  exact Finset.notMem_empty 0 requirements.2.2.1

theorem a_matching_read_cannot_overwrite_an_existing_output_occurrence :
    ¬ (direct frame inputs present label rows sources 0 0 (query 8)).Admits X := by
  intro admitted
  have requirements := HeldReadGenericFirings.direct_admission_data (E := E) X
    (state frame inputs present label) rows
    (closures (state frame inputs present label) (data sources) (arguments (query 8))) 0 PUnit.unit
    (rowOpening frame inputs present label rows sources (query 8) 0)
    (rowOpening frame inputs present label rows sources (query 8) 1) 0 admitted
  exact requirements.2.2.2.1 (by decide +kernel)

end Mettapedia.Languages.MeTTa.PeTTa.MachineNegativeHeadAdmission.Controls
