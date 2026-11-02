import Mettapedia.GSLT.Dynamics.IndexedJoinMaterialization
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.List.Nodup

/-!
# Complete indexed join delivery with occurrence bags

The variable-at-a-time traversal produces each binding key once. Each key
then expands the retained occurrence product. The resulting bag preserves
the authored source witnesses, including repeated uses of the same row.
Only binding keys are unique; occurrence outputs are not deduplicated.

The delivery ledger composes indexed navigation, leaf reads and counted
product traversal. It is an abstract work bound, not a native layout or
wall-clock theorem. Ordered source consumers do not acquire permission to
use this bag route.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.IndexedJoinDelivery

open ConjunctiveRegionProvenance GenericJoinRegions PreparedJoinRegions IndexedJoinLeaves
open IndexedJoinMaterialization
open Mettapedia.Algorithms.Compression

variable {n : Nat} {Value Id : Type} [LinearOrder Value]

theorem leaf_extends {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before after : Environment n Value)
    (member : after ∈ leafStates domain stored outside order before) : Extends before after := by
  induction order generalizing before with
  | nil =>
      have same : after = before := List.mem_singleton.mp member
      subst after
      exact Extends.refl _
  | cons coordinate rest ih =>
      obtain ⟨value, key, later⟩ := List.mem_flatMap.mp member
      have candidate : value ∈ candidates values (sources stored) before coordinate := by
        simpa only [Finset.mem_sort, CyclicJoinRegions.execute_exact, IndexedJoinRegions.Stage.execute_exact] using key
      exact (update_extends values before coordinate value
        (candidate_allowed values (sources stored) before coordinate value candidate)).trans (ih _ later)

theorem leaf_keys_nodup {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value) :
    (leafStates domain stored outside order before).Nodup := by
  induction order generalizing before with
  | nil => exact List.nodup_singleton _
  | cons coordinate rest ih =>
      apply List.nodup_flatMap.mpr
      refine ⟨fun value _ => ih _, ?_⟩
      apply ((CyclicJoinRegions.execute (stage domain stored outside before coordinate)).sort_nodup (· ≤ ·)).imp
      intro left right distinct after leftMember rightMember
      have leftBound := leaf_extends domain stored outside rest
        (Function.update before coordinate (some left)) after leftMember coordinate left (by simp)
      have rightBound := leaf_extends domain stored outside rest
        (Function.update before coordinate (some right)) after rightMember coordinate right (by simp)
      exact distinct (Option.some.inj (leftBound.symm.trans rightBound))

def bindings {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value) : List (Environment n Value) :=
  (leafStates domain stored outside order before).filter (leafCheck stored outside)

theorem bindings_cons {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (coordinate : Fin n) (rest : List (Fin n)) (before : Environment n Value) :
    bindings domain stored outside (coordinate :: rest) before =
      ((CyclicJoinRegions.execute (stage domain stored outside before coordinate)).sort (· ≤ ·)).flatMap
        (fun value => bindings domain stored outside rest (Function.update before coordinate (some value))) := by
  unfold bindings
  rw [leafStates, List.filter_flatMap]

theorem bindings_nodup {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value) :
    (bindings domain stored outside order before).Nodup :=
  (leaf_keys_nodup domain stored outside order before).filter _

theorem mem_bindings {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before after : Environment n Value) :
    after ∈ bindings domain stored outside order before ↔
      after ∈ IndexedJoinLeaves.run domain stored outside order before := by
  induction order generalizing before with
  | nil =>
      by_cases checked : leafCheck stored outside before = true <;>
        simp [bindings, leafStates, IndexedJoinLeaves.run, checked]
  | cons coordinate rest ih =>
      simp only [bindings, leafStates, List.filter_flatMap, List.mem_flatMap,
        Finset.mem_sort, IndexedJoinLeaves.run, Finset.mem_biUnion]
      exact exists_congr fun value => and_congr_right fun _ => ih _

theorem bindings_support {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value) :
    (bindings domain stored outside order before).toFinset =
      IndexedJoinLeaves.run domain stored outside order before := by
  ext after
  exact List.mem_toFinset.trans (mem_bindings domain stored outside order before after)

def complete (outside : Value) (stored : List (StoredFactor n Value Id)) (environment : Environment n Value) :
    List (List Id) :=
  let entry := enter outside environment stored
  (ParameterRegionCost.metered (ParameterRegion.work entry.frontier) entry.frontier).2.1

def deliver {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value) :
    List (Environment n Value × List Id) :=
  (bindings domain stored outside order before).flatMap fun environment =>
    (complete outside stored environment).map (environment, ·)

def sourceBag (values : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value) :
    Multiset (Environment n Value × List Id) :=
  (GenericJoinRegions.reference values factors order before).val.bind fun environment =>
    ((witnesses (valuation outside environment) factors).map (environment, ·) : List _)

theorem delivery_bag_exact {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value) :
    (deliver domain stored outside order before : Multiset _) =
      sourceBag values (sources stored) outside order before := by
  have support := congrArg Finset.val (bindings_support domain stored outside order before)
  rw [IndexedJoinLeaves.run_exact, execute_exact] at support
  have noDuplicates := bindings_nodup domain stored outside order before
  rw [List.toFinset_val, List.dedup_eq_self.mpr noDuplicates] at support
  unfold deliver sourceBag
  rw [← Multiset.coe_bind, ← support]
  apply Multiset.bind_congr
  intro environment _
  exact Quot.sound ((completed_bag_exact outside environment stored).map (environment, ·))

theorem commutative_readout_exact {K : Type*} [AddCommMonoid K]
    {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value)
    (readout : Environment n Value × List Id → K) :
    ((deliver domain stored outside order before).map readout).sum =
      ((sourceBag values (sources stored) outside order before).map readout).sum := by
  simpa only [Multiset.map_coe, Multiset.sum_coe] using
    congrArg (fun bag : Multiset (Environment n Value × List Id) => (bag.map readout).sum)
      (delivery_bag_exact domain stored outside order before)

def outputCount {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value) : Nat :=
  ((bindings domain stored outside order before).map fun environment =>
    (witnesses (valuation outside environment) (sources stored)).length).sum

theorem delivered_count {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value) :
    (deliver domain stored outside order before).length = outputCount domain stored outside order before := by
  simp only [deliver, List.length_flatMap, List.length_map, outputCount]
  apply congrArg List.sum
  apply List.map_congr_left
  intro environment _
  exact (completed_bag_exact outside environment stored).length_eq

theorem output_count_source {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value) :
    outputCount domain stored outside order before =
      ∑ environment ∈ GenericJoinRegions.reference values (sources stored) order before,
        (witnesses (valuation outside environment) (sources stored)).length := by
  rw [← execute_exact domain stored outside, ← IndexedJoinLeaves.run_exact,
    ← bindings_support, List.sum_toFinset _ (bindings_nodup domain stored outside order before)]
  rfl

theorem nodes_positive {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value) :
    1 ≤ PreparedJoinLedger.nodes domain stored outside order before := by
  cases order <;> simp [PreparedJoinLedger.nodes]

theorem leaf_length_le_nodes {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value) :
    (leafStates domain stored outside order before).length ≤
      PreparedJoinLedger.nodes domain stored outside order before := by
  induction order generalizing before with
  | nil => exact Nat.le_refl _
  | cons coordinate rest ih =>
      have children := List.sum_le_sum
        (l := (CyclicJoinRegions.execute (stage domain stored outside before coordinate)).sort (· ≤ ·))
        (fun value _ => ih (Function.update before coordinate (some value)))
      simp only [leafStates, List.length_flatMap, PreparedJoinLedger.nodes]
      exact children.trans (Nat.le_add_left _ _)

/-- List-level bookkeeping: terminal cell, filter inspection and retained
cell, plus internal dispatch, key visits and copied child-list spines.
Cell payload comparison and native allocation are not unit-cost claims. -/
def bindingWork {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) : List (Fin n) → Environment n Value → Nat
  | [], _ => 3
  | coordinate :: rest, before =>
      let keys := (CyclicJoinRegions.execute (stage domain stored outside before coordinate)).sort (· ≤ ·)
      1 + keys.length + (keys.map fun value =>
        bindingWork domain stored outside rest (Function.update before coordinate (some value)) +
          (leafStates domain stored outside rest (Function.update before coordinate (some value))).length).sum

theorem bindingWork_bound {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value) :
    bindingWork domain stored outside order before ≤
      (2 * order.length + 3) * PreparedJoinLedger.nodes domain stored outside order before := by
  induction order generalizing before with
  | nil => exact Nat.le_refl _
  | cons coordinate rest ih =>
      let keys := (CyclicJoinRegions.execute (stage domain stored outside before coordinate)).sort (· ≤ ·)
      have children := List.sum_le_sum (l := keys)
        (fun value _ => ih (Function.update before coordinate (some value)))
      rw [List.sum_map_mul_left] at children
      have leaves := List.sum_le_sum (l := keys) (fun value _ =>
        leaf_length_le_nodes domain stored outside rest (Function.update before coordinate (some value)))
      have keysBound := List.sum_le_sum (l := keys) (fun value _ =>
        nodes_positive domain stored outside rest (Function.update before coordinate (some value)))
      simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one] at keysBound
      simp only [bindingWork, PreparedJoinLedger.nodes, List.length_cons, List.sum_map_add]
      change 1 + keys.length + _ ≤ (2 * (rest.length + 1) + 3) * (1 + _)
      nlinarith

def terminalWork {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value) : Nat :=
  ((bindings domain stored outside order before).map fun environment =>
    PreparedJoinLedger.leafComparisons stored outside environment + stored.length).sum

theorem terminalWork_bound {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value) :
    terminalWork domain stored outside order before ≤
      PreparedJoinLedger.boundaryAllowance domain stored outside order before := by
  induction order generalizing before with
  | nil =>
      by_cases checked : leafCheck stored outside before = true <;>
        simp [terminalWork, bindings, leafStates, checked, PreparedJoinLedger.boundaryAllowance, Nat.add_comm]
  | cons coordinate rest ih =>
      have children := List.sum_le_sum
        (l := (CyclicJoinRegions.execute (stage domain stored outside before coordinate)).sort (· ≤ ·))
        (fun value _ => ih (Function.update before coordinate (some value)))
      change ((bindings domain stored outside (coordinate :: rest) before).map
        (fun environment => PreparedJoinLedger.leafComparisons stored outside environment + stored.length)).sum ≤ _
      rw [bindings_cons]
      simp only [List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def]
      exact children.trans (Nat.le_add_left _ _)

def materializationWork {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value)
    (budgets : Environment n Value → Nat) : Nat :=
  ((bindings domain stored outside order before).map fun environment =>
    (enter outside environment stored).allowance +
      (ParameterRegionCost.metered (budgets environment) (enter outside environment stored).frontier).1).sum

theorem materializationWork_bound {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value)
    (budgets : Environment n Value → Nat) :
    materializationWork domain stored outside order before budgets ≤
      2 * terminalWork domain stored outside order before +
        outputCoefficient stored.length * outputCount domain stored outside order before := by
  have combined := List.sum_le_sum (l := bindings domain stored outside order before)
    (fun environment _ => page_cost_bound outside environment stored (budgets environment))
  simpa only [materializationWork, terminalWork, outputCount, List.sum_map_add,
    List.sum_map_mul_left] using combined

def deliveryAllowance {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value) : Nat :=
  CyclicJoinRegions.navigationWork values (sources stored) (stage domain stored outside) order before +
    PreparedJoinLedger.boundaryAllowance domain stored outside order before +
    bindingWork domain stored outside order before +
    materializationWork domain stored outside order before
      (fun environment => ParameterRegion.work (enter outside environment stored).frontier) +
    2 * outputCount domain stored outside order before

/-- Fixed-query sum-min/logarithmic navigation plus occurrence output work.
The coefficient exposes query size rather than charging a whole tuple as an
unqualified constant. Index construction and native representation costs
remain outside this ledger. -/
theorem delivery_sum_min_bound {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value) :
    let width := IndexedJoinRegions.maximumArity (sources stored)
    let maximum := IndexedJoinRegions.maximumWidth values (sources stored)
    let visited := CyclicJoinRegions.cyclicStages values (sources stored) (stage domain stored outside) order before
    let base := 4 * width + 2 * width ^ 2 + PreparedJoinLedger.nodeBudget values stored
    let slope := 4 * width + 2 * width ^ 2 +
      2 * width * (3 * width + 4 + Mettapedia.Machines.Cursor.IndexedIntersection.seekBudget maximum) +
      1 + PreparedJoinLedger.nodeBudget values stored
    deliveryAllowance domain stored outside order before ≤
      3 * base + (2 * order.length + 3) +
        Mettapedia.Machines.Cursor.IndexedMultiwayProjection.sumMin visited * (3 * slope + (2 * order.length + 3)) +
        (outputCoefficient stored.length + 2) * (deliver domain stored outside order before).length := by
  have navigation := PreparedJoinLedger.combined_sum_min_bound domain stored outside order before
  have terminals := terminalWork_bound domain stored outside order before
  have materialization := materializationWork_bound domain stored outside order before
    (fun environment => ParameterRegion.work (enter outside environment stored).frontier)
  have listWork := bindingWork_bound domain stored outside order before
  rw [PreparedJoinLedger.nodes_eq_delivered_add_one] at listWork
  have delivered := Mettapedia.Machines.Cursor.IndexedMultiwayProjection.delivered_le_sumMin
    (CyclicJoinRegions.cyclicStages values (sources stored) (stage domain stored outside) order before)
  have scaled := Nat.mul_le_mul_left (2 * order.length + 3) (Nat.add_le_add_left delivered 1)
  rw [delivered_count]
  unfold deliveryAllowance
  dsimp only at navigation ⊢
  nlinarith

namespace Portfolio

open ObservationQualified

def boundary (values : Finset Value) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) :
    Boundary (Environment n Value) (Multiset (Environment n Value × List Id))
      (Multiset (Environment n Value × List Id)) where
  source := sourceBag values (sources stored) outside order
  summarize := id
  future := {
    Question := Multiset (Environment n Value × List Id) → Bool
    Answer _ := Bool
    read question bag := question bag }
  sufficient _ _ same question := congrArg question same

def region {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) : CertifiedRegion (boundary values stored outside order) Nat where
  regime := 4
  Artifact := List (Environment n Value × List Id)
  attempt before := .committed (deliver domain stored outside order before)
  decode rows := rows
  restores _ _ impossible := by cases impossible
  exact before _ accepted := by
    cases accepted
    exact delivery_bag_exact domain stored outside order before

end Portfolio

namespace Controls

open IndexedJoinRegions.Controls

theorem path_delivers_four_occurrences :
    (deliver (prepareDomain 0 {0, 1, 2}) (prepareFactors path) 0 (List.finRange 3) (fun _ => none)).length = 4 := by
  rw [delivered_count, output_count_source, sources_prepare]
  decide +kernel

theorem two_keys_are_not_four_answers :
    (IndexedJoinLeaves.run (prepareDomain 0 {0, 1, 2}) (prepareFactors path) 0
      (List.finRange 3) (fun _ => none)).card ≠
      (deliver (prepareDomain 0 {0, 1, 2}) (prepareFactors path) 0 (List.finRange 3) (fun _ => none)).length := by
  rw [path_delivers_four_occurrences, IndexedJoinLeaves.run_exact, execute_exact, sources_prepare]
  decide +kernel

theorem empty_query_delivers_one_empty_witness :
    (deliver (prepareDomain 0 ({0} : Finset Nat)) (prepareFactors ([] : List (Factor (Fin 0) Nat Nat)))
      0 [] (fun _ => none)).length = 1 := by
  rw [delivered_count, output_count_source, sources_prepare]
  decide +kernel

end Controls

end Mettapedia.GSLT.Dynamics.IndexedJoinDelivery
