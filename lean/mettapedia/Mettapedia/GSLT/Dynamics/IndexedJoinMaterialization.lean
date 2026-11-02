import Mettapedia.GSLT.Dynamics.PreparedJoinLedger
import Mettapedia.Algorithms.Compression.ParameterRegionCost

/-!
# Occurrence-preserving indexed join materialization

Prepared index leaves supply occurrence lists, not sets. The existing
resumable product frontier materializes their combinations. Per-assignment
results are bag-exact against the authored nested loops; prepared leaf order
is not asserted equal to authored source order.

Existence is checked before mapping occurrence IDs. Rejected assignments do
not traverse large successful leaves just to discover an empty last factor.
The ledger charges two index descents on successful assignments, ID visits,
empty-domain screening, frontier dispatch and copied prefix cells. The first
descent allowance includes all factors even when existence short-circuits.
This is abstract work, not native instructions or allocator bytes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.IndexedJoinMaterialization

open ConjunctiveRegionProvenance GenericJoinRegions PreparedJoinRegions IndexedJoinLeaves
open Mettapedia.Machines.Cursor
open Mettapedia.Algorithms.Compression

variable {n : Nat} {Value Id : Type} [LinearOrder Value]

structure Inputs (Id : Type) where
  domains : List (List Id)
  comparisons : Nat
  occurrenceVisits : Nat

def gather (outside : Value) (environment : Environment n Value) : List (StoredFactor n Value Id) → Inputs Id
  | [] => ⟨[], 0, 0⟩
  | factor :: rest =>
      let found := PrefixRunIndex.query (PreparedFactorIndex.columns factor.source).length factor.leaves.index outside
        (PreparedFactorIndex.targets factor.source (valuation outside environment))
      let later := gather outside environment rest
      ⟨found.1.map Prod.fst :: later.domains, found.2 + later.comparisons, found.1.length + later.occurrenceVisits⟩

theorem gather_domains (outside : Value) (environment : Environment n Value) (stored : List (StoredFactor n Value Id)) :
    (gather outside environment stored).domains = stored.map
      (fun factor => PreparedFactorIndex.occurrences factor.leaves (valuation outside environment) outside) := by
  induction stored with
  | nil => rfl
  | cons factor rest ih => simp only [gather, List.map_cons, PreparedFactorIndex.occurrences, ih]

theorem gather_comparisons (outside : Value) (environment : Environment n Value) (stored : List (StoredFactor n Value Id)) :
    (gather outside environment stored).comparisons = PreparedJoinLedger.leafComparisons stored outside environment := by
  induction stored with
  | nil => rfl
  | cons factor rest ih => simp only [gather, PreparedJoinLedger.leafComparisons, List.map_cons, List.sum_cons] at ih ⊢; rw [ih]

theorem gather_visits (outside : Value) (environment : Environment n Value) (stored : List (StoredFactor n Value Id)) :
    (gather outside environment stored).occurrenceVisits =
      ((gather outside environment stored).domains.map List.length).sum := by
  induction stored with
  | nil => rfl
  | cons factor rest ih => simp only [gather, List.map_cons, List.sum_cons, List.length_map, ih]

theorem gather_length (outside : Value) (environment : Environment n Value) (stored : List (StoredFactor n Value Id)) :
    (gather outside environment stored).domains.length = stored.length := by rw [gather_domains, List.length_map]

theorem gather_nonempty (outside : Value) (environment : Environment n Value) (stored : List (StoredFactor n Value Id)) :
    ParameterRegionCost.NonemptyDomains (gather outside environment stored).domains ↔
      groundCheck stored outside (valuation outside environment) = true := by
  rw [gather_domains]
  simp [ParameterRegionCost.NonemptyDomains, groundCheck, PreparedFactorIndex.occurrences, PreparedFactorIndex.present]

theorem product_bag_exact (outside : Value) (environment : Environment n Value) (stored : List (StoredFactor n Value Id)) :
    (ParameterRegion.product (gather outside environment stored).domains).Perm
      (witnesses (valuation outside environment) (sources stored)) := by
  rw [gather_domains]
  induction stored with
  | nil => exact List.Perm.refl _
  | cons factor rest ih =>
      change ((PreparedFactorIndex.occurrences factor.leaves (valuation outside environment) outside).flatMap _).Perm _
      exact (PreparedFactorIndex.occurrences_exact factor.leaves (valuation outside environment) outside).flatMap
        (fun occurrence _ => ih.map (occurrence :: ·))

theorem count_exact (outside : Value) (environment : Environment n Value) (stored : List (StoredFactor n Value Id)) :
    ParameterRegionCost.count (gather outside environment stored).domains =
      (witnesses (valuation outside environment) (sources stored)).length := by
  rw [← ParameterRegionCost.product_length]
  exact (product_bag_exact outside environment stored).length_eq

structure Entry (Id : Type) where
  frontier : ParameterRegion.Frontier Id
  allowance : Nat

def enter (outside : Value) (environment : Environment n Value) (stored : List (StoredFactor n Value Id)) : Entry Id :=
  let checked := PreparedJoinLedger.leafComparisons stored outside environment + stored.length
  if groundCheck stored outside (valuation outside environment) then
    let input := gather outside environment stored
    ⟨ParameterRegionCost.prepare input.domains,
      checked + input.comparisons + input.occurrenceVisits + (ParameterRegionCost.screen input.domains).2⟩
  else ⟨[], checked⟩

theorem entered_values (outside : Value) (environment : Environment n Value) (stored : List (StoredFactor n Value Id)) :
    ParameterRegion.values (enter outside environment stored).frontier =
      ParameterRegion.product (gather outside environment stored).domains := by
  unfold enter
  split
  · exact ParameterRegionCost.prepare_exact _
  next rejected =>
    have empty := ParameterRegionCost.count_eq_zero_of_empty (gather outside environment stored).domains
      (fun inhabited => rejected ((gather_nonempty outside environment stored).mp inhabited))
    have noAnswers := List.length_eq_zero_iff.mp ((ParameterRegionCost.product_length _).trans empty)
    simpa only [ParameterRegion.values, List.flatMap_nil] using noAnswers.symm

theorem completed_bag_exact (outside : Value) (environment : Environment n Value) (stored : List (StoredFactor n Value Id)) :
    let entry := enter outside environment stored
    ((ParameterRegionCost.metered (ParameterRegion.work entry.frontier) entry.frontier).2.1).Perm
      (witnesses (valuation outside environment) (sources stored)) := by
  dsimp only
  rw [ParameterRegionCost.metered_erases, ParameterRegion.complete_order, entered_values]
  exact product_bag_exact outside environment stored

def outputCoefficient (factors : Nat) : Nat := factors + (3 + factors) * (factors + 1)

/-- Every finite page pays only a prefix of the complete materialization
allowance. Query-size coefficients and repeated index lookups are explicit. -/
theorem page_cost_bound (outside : Value) (environment : Environment n Value)
    (stored : List (StoredFactor n Value Id)) (fuel : Nat) :
    (enter outside environment stored).allowance +
      (ParameterRegionCost.metered fuel (enter outside environment stored).frontier).1 ≤
      2 * (PreparedJoinLedger.leafComparisons stored outside environment + stored.length) +
        outputCoefficient stored.length * (witnesses (valuation outside environment) (sources stored)).length := by
  unfold enter
  split
  next accepted =>
    have inhabited := (gather_nonempty outside environment stored).mpr accepted
    have running := ParameterRegionCost.prepared_prefix_cost (gather outside environment stored).domains fuel
    have copying := ParameterRegionCost.input_visits_bound (gather outside environment stored).domains inhabited
    rw [← gather_visits] at copying
    rw [gather_length, count_exact] at running copying
    dsimp only
    rw [gather_comparisons]
    unfold outputCoefficient
    nlinarith
  next =>
    have zero : (ParameterRegionCost.metered fuel ([] : ParameterRegion.Frontier Id)).1 = 0 := by
      have bound := ParameterRegionCost.metered_prefix_bound fuel ([] : ParameterRegion.Frontier Id)
      simpa [ParameterRegionCost.potential] using Nat.eq_zero_of_le_zero bound
    dsimp only
    rw [zero]
    omega

namespace Controls

open IndexedJoinRegions.Controls

theorem duplicate_path_materializes_two_votes_per_binding :
    let stored := prepareFactors path
    let environment : Environment 3 Nat := fun i => some i.val
    let entry := enter 0 environment stored
    (ParameterRegionCost.metered (ParameterRegion.work entry.frontier) entry.frontier).2.1.length = 2 := by
  calc
    _ = (witnesses (GenericJoinRegions.valuation 0 (fun i : Fin 3 => some i.val)) path).length := by
      simpa only [sources_prepare] using
        (completed_bag_exact 0 (fun i : Fin 3 => some i.val) (prepareFactors path)).length_eq
    _ = 2 := by decide +kernel

theorem impossible_ground_assignment_has_no_frontier :
    (enter 0 (fun (_ : Fin 4) => some 0) (prepareFactors clique)).frontier = [] := by decide +kernel

theorem paused_is_not_an_empty_answer_bag :
    let entry := enter 0 (fun i : Fin 3 => some i.val) (prepareFactors path)
    (ParameterRegionCost.metered 0 entry.frontier).2.1 = [] ∧ entry.frontier ≠ [] := by decide +kernel

end Controls

end Mettapedia.GSLT.Dynamics.IndexedJoinMaterialization
