import Mettapedia.OSLF.Syntax.GSOSNativeOccurrenceComparison
import Mettapedia.OSLF.Syntax.GSOSNativeFiringControls

/-!
# Repeated authored premises and their complete native receipts

Three positive occurrences test two actions of the same child: the first
two test action seven, with different retained origins. Their targets are
forced equal by deterministic validity. Normalizing and expanding cannot
recover those distinct histories, whereas the native occurrence certificate
retains all three positions and the supplied varying target witness.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.NativeOccurrenceControls

open _root_.CategoryTheory Mettapedia.TypeTheory
open Controls EdgeReadout NativeGuard NativeFiring NativeFiringControls
open PresheafEventCertificates DisplayedPresheafTransport DisplayedPresheafComprehension

abbrev inventoryAddress (position : Fin 3) : PositiveAddress bothClause :=
  if position = 2 then eight else seven

theorem inventoryAddress_covered : Function.Surjective inventoryAddress := by
  intro address
  have member := address.val.property
  simp only [bothClause, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with same | same
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact same.symm
  · refine ⟨2, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact same.symm

abbrev bothInventory : PositiveInventory bothClause where
  Position := Fin 3
  finite := inferInstance
  address := inventoryAddress
  covered := inventoryAddress_covered

noncomputable abbrev inventories : ∀ sort operator action (origin : authored.Origin sort operator action),
    PositiveInventory (authored.rule sort operator action origin) :=
  fun _ operator _ origin => match operator with
  | .stopped => origin.elim
  | .prefix label =>
      { Position := Empty
        finite := inferInstance
        address := Empty.elim
        covered := by
          intro address
          have impossible := address.property
          simp [authored, negativeClause] at impossible }
  | .priority => bothInventory

noncomputable def repeated : OccurrenceFiring authored inventories worlds steps (Fin 3)
    spot (sort := ()) .priority 0 where
  origin := ()
  children := bothChildren
  positive position := childEvent position (inventoryAddress position).val.val.2
  positive_source position := by
    have atLeft := positive_position_left (inventoryAddress position)
    simp only [childEvent, bothChildren, atLeft, ↓reduceIte]
    rfl
  positive_action _ := rfl
  negative address := by
    have impossible := address.property
    simp [authored, bothClause] at impossible

/-- The generic realization theorem accepts an actual empty position-to-
identifier map for a negative-only firing, without an inhabitance axiom. -/
theorem negative_only_guard_realizes_with_empty_origins :
    ∃ firing : OccurrenceFiring authored inventories worlds steps Empty
      spot (sort := ()) (.prefix 9) 0, firing.origin = 0 ∧ firing.children = negativeChildren := by
  let firing := realizeGuard authored inventories worlds steps Empty (.prefix 9) 0
    0 spot negativeChildren Empty.elim (negativeFiring 0 0).native_guard
  exact ⟨firing, rfl, rfl⟩

/-- Guard realization preserves the independently supplied position
identifiers even when two positions test the same operational address. -/
theorem realized_repeated_origins :
    ((realizeGuard authored inventories worlds steps (Fin 3) .priority 0 () spot bothChildren
      (fun position => position) repeated.native_guard).positive 0).origin = 0 ∧
    ((realizeGuard authored inventories worlds steps (Fin 3) .priority 0 () spot bothChildren
      (fun position => position) repeated.native_guard).positive 1).origin = 1 := ⟨rfl, rfl⟩

theorem repeated_test_has_two_origins :
    (repeated.positive 0).action = (repeated.positive 1).action ∧
      (repeated.positive 0).source = (repeated.positive 1).source ∧
      (repeated.positive 0).origin ≠ (repeated.positive 1).origin :=
  ⟨rfl, rfl, Fin.zero_ne_one⟩

theorem repeated_targets_forced_equal :
    HEq (repeated.positive 0).target (repeated.positive 1).target :=
  repeated.equal_address_targets 0 1 rfl

theorem three_authored_positions_two_addresses :
    Fintype.card bothInventory.Position = 3 ∧ bothClause.observed.card = 2 := by
  decide

/-- Expansion duplicates the selected normalized edge at repeated
addresses, so the original two distinct origins cannot be recovered. -/
theorem normalization_does_not_recover_history :
    repeated.normalize.expand (inventories := inventories) ≠ repeated := by
  intro recovered
  have first := congrArg (fun firing : OccurrenceFiring authored inventories worlds steps (Fin 3)
    spot (sort := ()) .priority 0 => (firing.positive 0).origin) recovered
  have second := congrArg (fun firing : OccurrenceFiring authored inventories worlds steps (Fin 3)
    spot (sort := ()) .priority 0 => (firing.positive 1).origin) recovered
  have same : ((repeated.normalize.expand (inventories := inventories)).positive 0).origin =
      ((repeated.normalize.expand (inventories := inventories)).positive 1).origin := rfl
  exact Fin.zero_ne_one (first.symm.trans (same.trans second))

theorem every_origin_survives_collision :
    ((repeated.map change).positive 0).origin = 0 ∧
      ((repeated.map change).positive 1).origin = 1 ∧
      ((repeated.map change).positive 2).origin = 2 := ⟨rfl, rfl, rfl⟩

theorem selected_readout_natural :
    repeated.normalize.map change = (repeated.map change).normalize :=
  repeated.normalize_natural change

theorem actual_conclusion_natural :
    mapEvent authored.toLaw worlds steps change (repeated.conclusion consistent) =
      (repeated.map change).conclusion consistent :=
  repeated.conclusion_natural consistent change

theorem repeated_target :
    (repeated.conclusion consistent).target = priority (Controls.pure (X := naturals) 10) (Controls.pure (X := naturals) 10) := by
  have firstValid := (repeated.conclusion consistent).valid
  have secondValid := (bothFiring.conclusion consistent).valid
  have sourceEqual : (repeated.conclusion consistent).source =
      (bothFiring.conclusion consistent).source := rfl
  rw [sourceEqual] at firstValid
  exact (Option.some.inj (firstValid.symm.trans secondValid)).trans both_target

noncomputable def witness : targetFamily.obj ⟨spot, (repeated.conclusion consistent).target⟩ :=
  Fin.last (size (repeated.conclusion consistent).target)

noncomputable def receipt := repeated.certificate consistent targetFamily witness

theorem full_receipt_retains_inventory :
    ((occurrenceSpan authored inventories worlds steps consistent (Fin 3) .priority 0).eventReadout
      targetFamily).app spot ⟨(repeated.conclusion consistent).source, receipt⟩ = repeated :=
  repeated.certificate_firing consistent targetFamily witness

theorem complete_native_result :
    ((occurrenceSpan authored inventories worlds steps consistent (Fin 3) .priority 0).resultReadout
      targetFamily).app spot ⟨(repeated.conclusion consistent).source, receipt⟩ =
        ⟨(repeated.conclusion consistent).target, witness⟩ :=
  repeated.certificate_result consistent targetFamily witness

theorem receipt_distinguishes_premise_origins :
    (repeated.positive 0).origin ≠ (repeated.positive 1).origin := Fin.zero_ne_one

theorem full_receipt_future_inventory :
    ((occurrenceSpan authored inventories worlds steps consistent (Fin 3) .priority 0).eventReadout
      targetFamily).app future
      ((totalSpace ((occurrenceSpan authored inventories worlds steps consistent (Fin 3) .priority 0).certificates
        targetFamily)).map change ⟨(repeated.conclusion consistent).source, receipt⟩) = repeated.map change :=
  repeated.certificate_firing_natural consistent change targetFamily witness

theorem full_receipt_future_result :
    ((occurrenceSpan authored inventories worlds steps consistent (Fin 3) .priority 0).resultReadout
      targetFamily).app future
      ((totalSpace ((occurrenceSpan authored inventories worlds steps consistent (Fin 3) .priority 0).certificates
        targetFamily)).map change ⟨(repeated.conclusion consistent).source, receipt⟩) =
      (totalSpace targetFamily).map change ⟨(repeated.conclusion consistent).target, witness⟩ :=
  repeated.certificate_result_natural consistent change targetFamily witness

end Mettapedia.OSLF.DeterministicGSOS.NativeOccurrenceControls
