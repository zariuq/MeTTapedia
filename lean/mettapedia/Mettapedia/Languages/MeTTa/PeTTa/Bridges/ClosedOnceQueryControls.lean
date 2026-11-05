import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryExtraction

/-! Admission controls distinguish source fuel, probe work, row support and
the declared observer. Different relation names use the same proved family. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryRegion.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.GSLT.Dynamics ObservationQualified
open EagerDFS.Destination
open ClosedOnceQueryExecution

def program : SpaceSemantics.Program := {equations := [], declarations := []}
def late : Input := ⟨Allocator.empty 0 0, ⟨NamedSpaces.Store.new
  [pattern "sat" 1 8, pattern "sat" 1 7] [], [], [.symbol "already-emitted"]⟩, 11⟩
def early : Input := {late with world := {late.world with state := (NamedSpaces.Store.new
  [pattern "sat" 1 7, pattern "sat" 1 8] [])}}
def openRows : Input := {late with world := {late.world with state := (NamedSpaces.Store.new
  [.expression [.symbol "sat", .var "formula", .grounded (.int 7)]] [])}}
def zeroFuel : Input := {late with sourceFuel := 0}

theorem paused_probe_does_not_become_absence : attempt "sat" 1 7 1 late = .declined late := by
  have admitted : 11 ≤ late.sourceFuel ∧
      ClosedQueryAdmission.rowsReady (pattern "sat" 1 7) late.world.state.core = true := by decide +kernel
  have stored : late.world.state.core = [pattern "sat" 1 8, pattern "sat" 1 7] := rfl
  have missed : SpaceSemantics.matchValue [] (pattern "sat" 1 7) (pattern "sat" 1 8) = none := by decide +kernel
  unfold attempt
  rw [if_pos admitted, stored]
  simp [FirstQueryCursor.machine, Machine.run, missed]

theorem early_witness_commits : attempt "sat" 1 7 1 early = .committed (result "sat" 1 7 early true) := by
  have admitted : 11 ≤ early.sourceFuel ∧
      ClosedQueryAdmission.rowsReady (pattern "sat" 1 7) early.world.state.core = true := by decide +kernel
  have stored : early.world.state.core = [pattern "sat" 1 7, pattern "sat" 1 8] := rfl
  have matched : SpaceSemantics.matchValue [] (pattern "sat" 1 7) (pattern "sat" 1 7) = some [] := by decide +kernel
  unfold attempt
  rw [if_pos admitted, stored]
  simp [FirstQueryCursor.machine, Machine.run, matched]

theorem open_candidates_refuse : attempt "sat" 1 7 10 openRows = .declined openRows := by
  have refused : ClosedQueryAdmission.rowsReady (pattern "sat" 1 7) openRows.world.state.core = false := by decide +kernel
  simp [attempt, refused]

theorem zero_source_fuel_refuses : attempt "sat" 1 7 10 zeroFuel = .declined zeroFuel := by rfl

theorem fallback_retains_late_success_and_world :
    (region (0 : Nat) program "sat" 1 7 (by decide) 1).execute late = result "sat" 1 7 late true := by
  rw [fallback_is_the_reference]
  have receipt := source_result program "sat" 1 7 (by decide) late (by decide)
  have present : pattern "sat" 1 7 ∈ late.world.state.core := by decide +kernel
  simpa [present] using receipt

theorem zero_source_fuel_retains_the_entrance :
    (region (0 : Nat) program "sat" 1 7 (by decide) 10).execute zeroFuel =
      ([], .exhausted (root zeroFuel.allocator zeroFuel.world (initialControl "sat" 1 7))) := by
  rw [fallback_is_the_reference]
  rfl

theorem arbitrary_relation_name_extracts :
    (ClosedOnceQueryExtraction.parse (expression "edges" (-2) 42)).map
      ClosedOnceQueryExtraction.Description.source = some (expression "edges" (-2) 42) := by decide +kernel

theorem ordinary_relation_name_extracts :
    (ClosedOnceQueryExtraction.parse (expression "sat" 1 7)).map
      ClosedOnceQueryExtraction.Description.source = some (expression "sat" 1 7) := by decide +kernel

theorem special_cons_view_refuses : ClosedOnceQueryExtraction.parse (expression "cons" 1 7) = none := by rfl

theorem missing_once_does_not_drop_duplicates :
    ClosedOnceQueryExtraction.parse (query "sat" 1 7) = none := rfl

theorem effectful_template_is_not_the_literal_query :
    ClosedOnceQueryExtraction.parse (.expression [.symbol "once", .expression [.symbol "match", .symbol "&self",
      pattern "sat" 1 7, .expression [.symbol "println!", .symbol "effect"]]]) = none := rfl

theorem false_answer_is_not_an_absence_probe :
    ClosedOnceQueryExtraction.parse (.expression [.symbol "once", .expression [.symbol "match", .symbol "&self",
      pattern "sat" 1 7, Effects.boolean false]]) = none := rfl

theorem exact_page_keeps_reference_execution :
    ClosedOnceQueryExtraction.classify (0 : Nat) .exactPage program (expression "sat" 1 7) 10 = none := rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryRegion.Controls
