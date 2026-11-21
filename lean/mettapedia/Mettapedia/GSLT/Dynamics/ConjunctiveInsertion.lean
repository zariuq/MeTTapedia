import Mettapedia.GSLT.Dynamics.IndexedJoinDelivery

/-!
# Insertion deltas of conjunctive witnesses

For a fixed read position, replace its relation by the inserted
occurrences to compute the delta. Completed derivations are counted
with multiplicity. Changing which assignments are feasible is included:
the proof uses a common carrier of possible assignments, where failed
assignments contribute an empty bag. The indexed realization can retain
the prepared representation of every unchanged read position.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ConjunctiveInsertion

open ConjunctiveRegionProvenance GenericJoinRegions PreparedJoinRegions IndexedJoinDelivery

variable {n : Nat} {Value Id : Type}

abbrev Rows (factor : Factor (Fin n) Value Id) := List (Id × (Fin factor.arity → Value))

def replace (factor : Factor (Fin n) Value Id) (rows : Rows factor) : Factor (Fin n) Value Id :=
  { factor with rows }

def insert (factor : Factor (Fin n) Value Id) (rows : Rows factor) : Factor (Fin n) Value Id :=
  replace factor (factor.rows ++ rows)

section Source

variable [LinearOrder Value]

private theorem carrier_filter (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (order : List (Fin n)) (before : Environment n Value) :
    reference domain factors order before =
      (reference (Id := Id) domain [] order before).filter (fun after => feasible after factors) := by
  induction order generalizing before with
  | nil =>
    have empty : feasible before ([] : List (Factor (Fin n) Value Id)) := by simp [feasible]
    ext after
    by_cases same : after = before
    · subst after
      by_cases ok : feasible before factors <;> simp [reference, empty, ok]
    · by_cases ok : feasible before factors <;> simp [reference, empty, same, ok]
  | cons coordinate rest ih =>
    ext after
    simp only [reference, Finset.mem_biUnion, Finset.mem_filter, ih]
    constructor
    · rintro ⟨value, ready, held, valid⟩
      exact ⟨⟨value, ready, held⟩, valid⟩
    · rintro ⟨⟨value, ready, held⟩, valid⟩
      exact ⟨value, ready, held, valid⟩

private theorem witnesses_satisfy (assignment : Fin n → Value)
    (factors : List (Factor (Fin n) Value Id)) (present : witnesses assignment factors ≠ []) :
    ∀ factor ∈ factors, ∃ row ∈ factor.rows, factor.acceptsRow assignment row = true := by
  induction factors with
  | nil => simp
  | cons factor rest ih =>
    have someAnswer : ∃ answer, answer ∈ witnesses assignment (factor :: rest) :=
      List.exists_mem_of_ne_nil _ present
    obtain ⟨answer, member⟩ := someAnswer
    obtain ⟨occurrence, emitted, tail⟩ := List.mem_flatMap.mp member
    obtain ⟨follow, inRest, _⟩ := List.mem_map.mp tail
    intro sought belongs
    rcases List.mem_cons.mp belongs with rfl | later
    · obtain ⟨row, listed, _, matched⟩ := (Factor.mem_occurrences _ _ _).mp emitted
      exact ⟨row, listed, (Factor.acceptsRow_iff ..).mpr matched⟩
    · exact ih (fun empty => by rw [empty] at inRest; cases inRest) sought later

private theorem infeasible_has_no_witnesses (outside : Value) (environment : Environment n Value)
    (factors : List (Factor (Fin n) Value Id)) (excluded : ¬ feasible environment factors) :
    witnesses (valuation outside environment) factors = [] := by
  classical
  by_contra notEmpty
  apply excluded
  have context : Extends environment (fun name => some (valuation outside environment name)) := by
    intro name value bound
    simp [valuation, bound]
  intro factor used
  obtain ⟨row, listed, accepted⟩ := witnesses_satisfy (valuation outside environment) factors notEmpty factor used
  exact ⟨row, listed, rowMatches_downward context factor row ((full_row_matches_iff _ _ _).mpr accepted)⟩

theorem sourceBag_common_carrier (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value) :
    sourceBag domain factors outside order before =
      (reference (Id := Id) domain [] order before).val.bind fun environment =>
        ((witnesses (valuation outside environment) factors).map (environment, ·) : List _) := by
  unfold sourceBag
  rw [carrier_filter, Finset.filter_val, Multiset.bind_filter]
  apply Multiset.bind_congr
  intro environment _
  by_cases feasibleHere : feasible environment factors
  · simp [feasibleHere]
  · simp [feasibleHere, infeasible_has_no_witnesses outside environment factors feasibleHere]

private theorem occurrences_insert (assignment : Fin n → Value) (factor : Factor (Fin n) Value Id)
    (added : Rows factor) :
    (insert factor added).occurrences assignment =
      factor.occurrences assignment ++ (replace factor added).occurrences assignment := by
  simp only [insert, replace, Factor.occurrences, List.filter_append, List.map_append]
  rfl

theorem witnesses_insert (assignment : Fin n → Value)
    (leading suffix : List (Factor (Fin n) Value Id)) (factor : Factor (Fin n) Value Id)
    (added : Rows factor) :
    (witnesses assignment (leading ++ insert factor added :: suffix) : Multiset (List Id)) =
      (witnesses assignment (leading ++ factor :: suffix) : Multiset (List Id)) +
        (witnesses assignment (leading ++ replace factor added :: suffix) : Multiset (List Id)) := by
  induction leading with
  | nil =>
    simp only [List.nil_append, witnesses, occurrences_insert, List.flatMap_append, Multiset.coe_add]
  | cons node leading ih =>
    simp only [List.cons_append, witnesses, ← Multiset.coe_bind]
    rw [← Multiset.bind_add]
    apply Multiset.bind_congr
    intro occurrence _
    simp only [← Multiset.map_coe, ih, Multiset.map_add]

theorem insertion_exact (domain : Finset Value) (outside : Value) (order : List (Fin n))
    (before : Environment n Value) (leading suffix : List (Factor (Fin n) Value Id))
    (factor : Factor (Fin n) Value Id) (added : Rows factor) :
    sourceBag domain (leading ++ insert factor added :: suffix) outside order before =
      sourceBag domain (leading ++ factor :: suffix) outside order before +
        sourceBag domain (leading ++ replace factor added :: suffix) outside order before := by
  simp only [sourceBag_common_carrier]
  rw [← Multiset.bind_add]
  apply Multiset.bind_congr
  intro environment _
  simp only [← Multiset.map_coe, witnesses_insert, Multiset.map_add]

/-- One entry per authored read occurrence. A shared relation can supply
insertions at more than one position. -/
structure Change (n : Nat) (Value Id : Type) where
  original : Factor (Fin n) Value Id
  added : Rows original

def Change.updated (edit : Change n Value Id) : Factor (Fin n) Value Id := insert edit.original edit.added

/-- A batch is differenced in read order. Each delta sees the new
earlier relations and the old later ones, so cross terms appear once. -/
def deltaQueries : List (Factor (Fin n) Value Id) → List (Change n Value Id) →
    List (List (Factor (Fin n) Value Id))
  | _, [] => []
  | leading, edit :: later =>
    (leading ++ replace edit.original edit.added :: later.map Change.original) ::
      deltaQueries (leading ++ [edit.updated]) later

theorem batch_exact (domain : Finset Value) (outside : Value) (order : List (Fin n))
    (before : Environment n Value) (leading : List (Factor (Fin n) Value Id)) (edits : List (Change n Value Id)) :
    sourceBag domain (leading ++ edits.map Change.updated) outside order before =
      sourceBag domain (leading ++ edits.map Change.original) outside order before +
        ((deltaQueries leading edits).map (fun query => sourceBag domain query outside order before)).sum := by
  induction edits generalizing leading with
  | nil => simp [deltaQueries]
  | cons edit later ih =>
    have step := insertion_exact domain outside order before leading (later.map Change.original)
      edit.original edit.added
    have rest := ih (leading ++ [edit.updated])
    simp only [List.append_assoc, List.singleton_append] at rest
    simp only [List.map_cons, deltaQueries, List.sum_cons]
    rw [rest, Change.updated, step, add_assoc]

end Source

section Indexed

variable [LinearOrder Value]

def deltaFactors (leading suffix : List (StoredFactor n Value Id)) (factor : Factor (Fin n) Value Id)
    (added : Rows factor) : List (StoredFactor n Value Id) :=
  leading ++ prepareFactors [replace factor added] ++ suffix

theorem delta_sources (leading suffix : List (StoredFactor n Value Id)) (factor : Factor (Fin n) Value Id)
    (added : Rows factor) :
    sources (deltaFactors leading suffix factor added) = sources leading ++ replace factor added :: sources suffix := by
  simp only [deltaFactors, sources, List.map_append]
  change sources leading ++ sources (prepareFactors [replace factor added]) ++ sources suffix = _
  rw [sources_prepare]
  simp only [List.append_assoc, List.singleton_append]
  rfl

theorem indexed_insertion_exact {values : Finset Value} (domain : Domain values)
    (outside : Value) (order : List (Fin n)) (before : Environment n Value)
    (leading suffix : List (StoredFactor n Value Id)) (factor : Factor (Fin n) Value Id) (added : Rows factor) :
    sourceBag values (sources leading ++ insert factor added :: sources suffix) outside order before =
      sourceBag values (sources leading ++ factor :: sources suffix) outside order before +
        (deliver domain (deltaFactors leading suffix factor added) outside order before : Multiset _) := by
  rw [delivery_bag_exact, delta_sources]
  exact insertion_exact values outside order before _ _ factor added

/-- The exact sum-min account for the prepared cyclic delta. The output
coefficient counts complete occurrence witnesses. The index construction
for the new relation is a separate operation. -/
theorem indexed_delta_work {values : Finset Value} (domain : Domain values)
    (outside : Value) (order : List (Fin n)) (before : Environment n Value)
    (leading suffix : List (StoredFactor n Value Id)) (factor : Factor (Fin n) Value Id) (added : Rows factor) :
    let stored := deltaFactors leading suffix factor added
    let width := IndexedJoinRegions.maximumArity (sources stored)
    let maximum := IndexedJoinRegions.maximumWidth values (sources stored)
    let stages := CyclicJoinRegions.cyclicStages values (sources stored) (stage domain stored outside) order before
    let base := 4 * width + 2 * width ^ 2 + PreparedJoinLedger.nodeBudget values stored
    let slope := 4 * width + 2 * width ^ 2 +
      2 * width * (3 * width + 4 + Mettapedia.Machines.Cursor.IndexedIntersection.seekBudget maximum) +
      1 + PreparedJoinLedger.nodeBudget values stored
    deliveryAllowance domain stored outside order before ≤
      3 * base + (2 * order.length + 3) +
        Mettapedia.Machines.Cursor.IndexedMultiwayProjection.sumMin stages * (3 * slope + (2 * order.length + 3)) +
        (IndexedJoinMaterialization.outputCoefficient stored.length + 2) *
          (deliver domain stored outside order before).length :=
  delivery_sum_min_bound domain (deltaFactors leading suffix factor added) outside order before

end Indexed

namespace Controls

open GenericJoinRegions.Controls (edge)

private def leading : List (Factor (Fin 3) Nat Nat) :=
  [edge 0 1 [(10, (0, 1)), (11, (0, 1))], edge 1 2 [(20, (1, 2))]]

private def missingEdge : Factor (Fin 3) Nat Nat := edge 2 0 [(9, (2, 1))]

private def delta : Rows missingEdge := (edge 2 0 [(30, (2, 0))]).rows

private def values : Finset Nat := {0, 1, 2}

theorem inserting_the_closing_edge_delivers_both_occurrences :
    let stored := deltaFactors (prepareFactors leading) [] missingEdge delta
    ((deliver (prepareDomain 0 values) stored 0 [0, 1, 2] (fun _ => none)).map Prod.snd :
      Multiset (List Nat)) = ([[10, 20, 30], [11, 20, 30]] : List (List Nat)) := by
  dsimp only
  rw [← Multiset.map_coe, delivery_bag_exact, delta_sources, sources_prepare]
  decide +kernel

theorem a_mismatched_closing_edge_has_no_witness :
    sourceBag values (leading ++ [missingEdge]) 0 [0, 1, 2] (fun _ => none) = 0 := by decide +kernel

private def repeatedRead : Change 1 Nat Nat where
  original := ⟨1, fun _ => .variable 0, [(10, fun _ => 7)]⟩
  added := [(11, fun _ => 7)]

theorem two_inserted_reads_keep_the_cross_term_once :
    let plan := deltaQueries [] [repeatedRead, repeatedRead]
    let delta := (plan.map fun query => sourceBag {7} query 0 [0] (fun _ => none)).sum
    delta.map Prod.snd = ([[11, 10], [10, 11], [11, 11]] : List (List Nat)) := by decide +kernel

end Controls

end Mettapedia.GSLT.Dynamics.ConjunctiveInsertion
