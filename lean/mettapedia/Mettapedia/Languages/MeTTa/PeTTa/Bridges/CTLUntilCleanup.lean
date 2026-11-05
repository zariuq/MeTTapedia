import Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryBagErasure
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilPublicationSource

/-!
# Typed current-frontier cleanup

The existing erasure worker captures every current frontier occurrence before
deletion. Repeated rows contribute repeated body results even when an earlier
deletion already removed their payload. The resulting store is the ordered
filter excluding precisely that formula and round; its decoding is derived.

The source theorem here is the batch `Eval.PureReturns` judgment. It does not
identify that judgment with a retained scoped call or a whole recursive driver.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCleanup

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom isGroundAtom)
open FlatQueryRowCodec (Codec)
open CTLUntilMixedStore (Row render decodeRows frontSelect)
open CTLUntilSourceRows (number)
open SpaceSemantics NamedSpaces

structure Names where
  space : String
  formula : String
  round : String
  node : String

def fields (names : Names) : List Atom :=
  [.symbol "fr", .var names.formula, .var names.round, .var names.node]

def pattern (names : Names) : Atom := .expression (fields names)

def source (names : Names) : Atom := QueryBagErasure.source names.space (pattern names) (fields names)

variable {Label : Type} [DecidableEq Label]

def remaining (label : Label) (round : Nat) (rows : List (Row Label)) : List (Row Label) :=
  rows.filter fun row => (frontSelect label round row).isNone

theorem selected_iff (label : Label) (round node : Nat) (row : Row Label) :
    frontSelect label round row = some node ↔ row = .frontier label round node := by
  cases row <;> simp [frontSelect, and_assoc]

theorem raw_match (codec : Codec Label) (label : Label) (round : Nat) (names : Names) (caller : Subst)
    (formulaRead : caller.lookup names.formula = some (codec.encode label))
    (roundRead : caller.lookup names.round = some (number round))
    (nodeFresh : caller.lookup names.node = none) (row : Row Label) (admitted : row.admitted) :
    matchValue caller (pattern names) (render codec row) =
      (frontSelect label round row).map (fun node => (names.node, number node) :: caller) := by
  cases row with
  | frontier other step node =>
      unfold pattern fields render
      rw [matchValue_expression_of_not_cons _ _ _ (by simp)]
      by_cases sameLabel : other = label
      · subst other
        by_cases sameRound : step = round
        · subst step
          simp [matchValue.matchValues, matchValue, matchAtom, formulaRead, roundRead, nodeFresh,
            number, frontSelect]
        · simp [matchValue.matchValues, matchValue, matchAtom, formulaRead, roundRead,
            number, frontSelect, sameRound]
      · simp [matchValue.matchValues, matchValue, matchAtom, formulaRead, codec.injective.eq_iff,
          frontSelect, sameLabel]
  | edge prior next => exact CTLUntilMixedStore.different_head caller "fr" "rt" _ _ (by decide) (by decide)
  | satisfaction other node => exact CTLUntilMixedStore.different_head caller "fr" "sat" _ _ (by decide) (by decide)
  | other head children => exact CTLUntilMixedStore.different_head caller "fr" head _ _ (by decide) (Ne.symm admitted.1)

theorem choices_exact (codec : Codec Label) (label : Label) (round : Nat) (names : Names) (caller : Subst)
    (formulaRead : caller.lookup names.formula = some (codec.encode label))
    (roundRead : caller.lookup names.round = some (number round))
    (nodeFresh : caller.lookup names.node = none) (rows : List (Row Label))
    (admitted : ∀ row ∈ rows, row.admitted) :
    EffectfulQuerySource.choices caller (pattern names) (rows.map (render codec)) =
      (rows.filterMap (frontSelect label round)).map (fun node => (names.node, number node) :: caller) := by
  rw [EffectfulQuerySource.choices, CTLUntilMixedStore.scan_admitted codec (frontSelect label round)
    (fun node => (names.node, number node) :: caller) caller (pattern names)
    (raw_match codec label round names caller formulaRead roundRead nodeFresh) 0 rows admitted]
  simp only [List.map_map, Function.comp_def]
  exact CTLUntilSourceRows.located_map (frontSelect label round) 0 rows (fun node => (names.node, number node) :: caller)

omit [DecidableEq Label] in
theorem captured_payload (codec : Codec Label) (label : Label) (round node : Nat) (names : Names) (caller : Subst)
    (formulaRead : caller.lookup names.formula = some (codec.encode label))
    (roundRead : caller.lookup names.round = some (number round))
    (nodeFresh : caller.lookup names.node = none) :
    applySubst ((names.node, number node) :: caller) (pattern names) = render codec (.frontier label round node) := by
  have formulaApart : names.formula ≠ names.node := by
    intro same
    rw [same, nodeFresh] at formulaRead
    cases formulaRead
  have roundApart : names.round ≠ names.node := by
    intro same
    rw [same, nodeFresh] at roundRead
    cases roundRead
  simp only [Subst.lookup] at formulaRead roundRead
  simp [pattern, fields, render, applySubst, applySubst.applySubstList, Subst.lookup,
    Ne.symm formulaApart, Ne.symm roundApart, formulaRead, roundRead]

theorem payloads_exact (codec : Codec Label) (label : Label) (round : Nat) (names : Names) (caller : Subst)
    (formulaRead : caller.lookup names.formula = some (codec.encode label))
    (roundRead : caller.lookup names.round = some (number round))
    (nodeFresh : caller.lookup names.node = none) (rows : List (Row Label))
    (admitted : ∀ row ∈ rows, row.admitted) :
    (EffectfulQuerySource.choices caller (pattern names) (rows.map (render codec))).map
      (fun bindings => applySubst bindings (pattern names)) =
      (rows.filterMap (frontSelect label round)).map (fun node => render codec (.frontier label round node)) := by
  rw [choices_exact codec label round names caller formulaRead roundRead nodeFresh rows admitted]
  simp only [List.map_map, Function.comp_def, captured_payload codec label round _ names caller formulaRead roundRead nodeFresh]

theorem removal_matches_selected (codec : Codec Label) (label : Label) (round node : Nat) (row : Row Label)
    (admitted : row.admitted) :
    Effects.removalMatches (render codec (.frontier label round node)) (render codec row) =
      decide (frontSelect label round row = some node) := by
  change Effects.removalMatches (.expression [.symbol "fr", codec.encode label, number round, number node])
    (render codec row) = _
  rw [Effects.removalMatches_literal _ (by simp) (CTLUntilPublicationSource.frontier_literal codec label round node)]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, selected_iff]
  constructor
  · intro same
    have decoded := congrArg (CTLUntilMixedStore.decode codec) same
    change CTLUntilMixedStore.decode codec (render codec (.frontier label round node)) =
      CTLUntilMixedStore.decode codec (render codec row) at decoded
    rw [CTLUntilMixedStore.decode_render codec (.frontier label round node) (by trivial),
      CTLUntilMixedStore.decode_render codec row admitted] at decoded
    exact (Option.some.inj decoded).symm
  · rintro rfl
    rfl

theorem retained_exact (codec : Codec Label) (label : Label) (round : Nat) (rows : List (Row Label))
    (admitted : ∀ row ∈ rows, row.admitted) :
    QueryBagErasure.retained
      ((rows.filterMap (frontSelect label round)).map (fun node => render codec (.frontier label round node)))
      (rows.map (render codec)) = (remaining label round rows).map (render codec) := by
  unfold QueryBagErasure.retained remaining
  rw [List.filter_map]
  apply congrArg (List.map (render codec))
  apply List.filter_congr
  intro row member
  simp only [Function.comp_def, List.any_map]
  cases selected : frontSelect label round row with
  | none =>
      have absent : (rows.filterMap (frontSelect label round)).any
          (fun node => Effects.removalMatches (render codec (.frontier label round node)) (render codec row)) = false := by
        apply List.any_eq_false.mpr
        intro node _
        rw [removal_matches_selected codec label round node row (admitted row member), selected]
        simp
      simp [absent]
  | some node =>
      have present : node ∈ rows.filterMap (frontSelect label round) := List.mem_filterMap.mpr ⟨row, member, selected⟩
      have found : (rows.filterMap (frontSelect label round)).any
          (fun value => Effects.removalMatches (render codec (.frontier label round value)) (render codec row)) = true := by
        apply List.any_eq_true.mpr
        exact ⟨node, present, by rw [removal_matches_selected codec label round node row (admitted row member), selected]; simp⟩
      simp [found]

theorem remaining_admitted (label : Label) (round : Nat) (rows : List (Row Label))
    (admitted : ∀ row ∈ rows, row.admitted) : ∀ row ∈ remaining label round rows, row.admitted := by
  intro row member
  exact admitted row (List.mem_filter.mp member).1

theorem remaining_frontier_empty (label : Label) (round : Nat) (rows : List (Row Label)) :
    (remaining label round rows).filterMap (frontSelect label round) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro node member
  obtain ⟨row, kept, selected⟩ := List.mem_filterMap.mp member
  have missing := (List.mem_filter.mp kept).2
  rw [selected] at missing
  cases missing

private theorem remaining_view {Value : Type} (label : Label) (round : Nat)
    (view : Row Label → Option Value)
    (disjoint : ∀ row node, frontSelect label round row = some node → view row = none)
    (rows : List (Row Label)) :
    (remaining label round rows).filterMap view = rows.filterMap view := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    cases selected : frontSelect label round row with
    | none =>
        simp only [remaining] at ih
        simp [remaining, selected, List.filterMap_cons, ih]
    | some node =>
        simpa [remaining, selected, List.filterMap_cons, disjoint row node selected] using ih

/-- Removing frontier rows leaves every graph occurrence in its old order. -/
theorem remaining_graph (label : Label) (round : Nat) (rows : List (Row Label)) :
    CTLUntilMixedStore.graphView (remaining label round rows) = CTLUntilMixedStore.graphView rows := by
  apply remaining_view
  intro row node selected
  rw [(selected_iff label round node row).mp selected]

/-- All satisfaction labels, including the active output label, are retained. -/
theorem remaining_satisfaction (label observed : Label) (round : Nat) (rows : List (Row Label)) :
    CTLUntilMixedStore.satisfactionView observed (remaining label round rows) =
      CTLUntilMixedStore.satisfactionView observed rows := by
  apply remaining_view
  intro row node selected
  rw [(selected_iff label round node row).mp selected]

theorem remaining_other_frontier (label observed : Label) (round otherRound : Nat)
    (apart : observed ≠ label ∨ otherRound ≠ round) (rows : List (Row Label)) :
    (remaining label round rows).filterMap (frontSelect observed otherRound) =
      rows.filterMap (frontSelect observed otherRound) := by
  apply remaining_view
  intro row node selected
  rw [(selected_iff label round node row).mp selected]
  apply if_neg
  intro same
  rcases apart with labelApart | roundApart
  · exact labelApart same.1.symm
  · exact roundApart same.2.symm

theorem remaining_next_frontier (label : Label) (round : Nat) (rows : List (Row Label)) :
    (remaining label round rows).filterMap (frontSelect label (round + 1)) =
      rows.filterMap (frontSelect label (round + 1)) :=
  remaining_other_frontier label label round (round + 1) (Or.inr (by omega)) rows

/-- Uniform completion of the existing checked erasure route. The final
typed read and source result are conclusions of actual execution. -/
theorem completed_cleanup (codec : Codec Label) (label : Label) (round : Nat) (names : Names)
    (program : Program) (target : Handle) (caller : Subst) (before : Effects.State) (atoms : List Atom) (rows : List (Row Label))
    (location : caller.lookup names.space = some (Effects.handleValue target))
    (formulaRead : caller.lookup names.formula = some (codec.encode label))
    (roundRead : caller.lookup names.round = some (number round))
    (nodeFresh : caller.lookup names.node = none)
    (snapshot : before.read target = some atoms) (decoded : decodeRows codec atoms = some rows) :
    ∃ after,
      QueryBagErasure.execute names.space target (pattern names) (fields names) caller before =
        some (after, List.replicate (rows.filterMap (frontSelect label round)).length (Effects.boolean true)) ∧
      Eval.PureReturns program caller before (source names) after (number (rows.filterMap (frontSelect label round)).length) ∧
      after.read target = some ((remaining label round rows).map (render codec)) ∧
      decodeRows codec ((remaining label round rows).map (render codec)) = some (remaining label round rows) ∧
      (∀ other, other ≠ target → after.read other = before.read other) ∧ after.cells = before.cells := by
  obtain ⟨rendered, admitted⟩ := CTLUntilMixedStore.decode_rows_sound codec atoms rows decoded
  let captured := EffectfulQuerySource.choices caller (pattern names) atoms
  let payloads := captured.map (fun bindings => applySubst bindings (pattern names))
  have choices := choices_exact codec label round names caller formulaRead roundRead nodeFresh rows admitted
  have values := payloads_exact codec label round names caller formulaRead roundRead nodeFresh rows admitted
  rw [rendered] at choices values
  have count : captured.length = (rows.filterMap (frontSelect label round)).length := by
    change (EffectfulQuerySource.choices caller (pattern names) atoms).length = _
    rw [choices, List.length_map]
  obtain ⟨after, erased⟩ := QueryBagErasure.eraseRows_exists target payloads before atoms snapshot
  have completed : QueryBagErasure.run target (pattern names) (fields names) caller before =
      some (after, List.replicate (rows.filterMap (frontSelect label round)).length (Effects.boolean true)) := by
    simp only [QueryBagErasure.run, snapshot, QueryBagErasure.traverse_erase_exact]
    change (QueryBagErasure.eraseRows target payloads before).map
      (fun result => (result, [] ++ List.replicate captured.length (Effects.boolean true))) = _
    rw [erased, count]
    rfl
  have capturesReady : ClosedQueryAdmission.capturesReady caller (pattern names) = true := by
    simp [ClosedQueryAdmission.capturesReady, pattern, fields,
      Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars, Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars.atomFreeVarsList,
      formulaRead, roundRead, nodeFresh, number, isGroundAtom, ClosedQueryAdmission.literal_ground (codec.literal label)]
  have rowsReady : ClosedQueryAdmission.rowsReady (pattern names) atoms = true := by
    rw [← rendered]
    exact CTLUntilMixedStore.rows_ready codec "fr" _ (by simp) rows admitted
  have payloadReady : payloads.all QueryBagErasure.factPayload = true := by
    change ((EffectfulQuerySource.choices caller (pattern names) atoms).map _).all _ = true
    rw [values]
    apply List.all_eq_true.mpr
    intro payload member
    obtain ⟨node, _, rfl⟩ := List.mem_map.mp member
    change isGroundAtom (render codec (.frontier label round node)) = true
    exact ClosedQueryAdmission.literal_ground (CTLUntilPublicationSource.frontier_literal codec label round node)
  have targetReady : ClosedQueryAdmission.targetReady before target payloads = true := by
    unfold ClosedQueryAdmission.targetReady
    split
    · rfl
    · rw [snapshot]
      apply List.all_eq_true.mpr
      intro payload member
      change payload ∈ (EffectfulQuerySource.choices caller (pattern names) atoms).map _ at member
      rw [values] at member
      obtain ⟨node, _, rfl⟩ := List.mem_map.mp member
      rw [← rendered]
      exact CTLUntilMixedStore.rows_ready codec "fr" _ (by simp) rows admitted
  have executed : QueryBagErasure.execute names.space target (pattern names) (fields names) caller before =
      some (after, List.replicate (rows.filterMap (frontSelect label round)).length (Effects.boolean true)) := by
    unfold QueryBagErasure.execute
    rw [if_pos ⟨location, by simp [fields]⟩, snapshot]
    dsimp only
    change (if ClosedQueryAdmission.capturesReady caller (pattern names) && ClosedQueryAdmission.rowsReady (pattern names) atoms &&
      payloads.all QueryBagErasure.factPayload && ClosedQueryAdmission.targetReady before target payloads then
      QueryBagErasure.run target (pattern names) (fields names) caller before else none) = _
    rw [if_pos (by simp [capturesReady, rowsReady, payloadReady, targetReady])]
    exact completed
  obtain ⟨reading, others, cells⟩ := QueryBagErasure.eraseRows_receipt target payloads before after atoms snapshot erased
  have remainingRead : after.read target = some ((remaining label round rows).map (render codec)) := by
    rw [reading]
    congr 1
    change QueryBagErasure.retained ((EffectfulQuerySource.choices caller (pattern names) atoms).map _) atoms = _
    rw [values, ← rendered, retained_exact codec label round rows admitted]
  refine ⟨after, executed, ?_, remainingRead,
    CTLUntilMixedStore.decode_rows_complete codec _ (remaining_admitted label round rows admitted), others, cells⟩
  simpa only [source, number, List.length_replicate] using
    QueryBagErasure.execute_source program names.space target (pattern names) (fields names) caller before after _ executed

namespace Controls

def rows : List (Row Nat) := [.frontier 10 0 1, .edge 1 2, .frontier 10 0 1,
  .frontier 10 1 7, .satisfaction 20 1, .frontier 20 0 9, .frontier 10 1 7]

theorem cleanup_preserves_order_and_other_duplicates :
    remaining 10 0 rows = [.edge 1 2, .frontier 10 1 7, .satisfaction 20 1, .frontier 20 0 9, .frontier 10 1 7] := by
  decide +kernel

theorem another_round_is_not_current_cleanup : remaining 10 0 rows ≠ remaining 10 1 rows := by decide +kernel

theorem duplicate_producers_are_not_a_set_count :
    (rows.filterMap (frontSelect 10 0)).length = 2 ∧ (rows.filterMap (frontSelect 10 0)).toFinset.card = 1 := by decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCleanup

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCleanup.completed_cleanup
