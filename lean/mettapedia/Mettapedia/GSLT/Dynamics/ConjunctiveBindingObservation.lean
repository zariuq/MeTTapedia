import Mettapedia.GSLT.Dynamics.ConjunctiveBindingEnumeration

/-!
# Occurrence-bag observations across binding schedules

Input-domain and variable-coverage admission preserves the complete bag of
bindings paired with occurrence witnesses, not only its cardinality. Every
commutative readout follows. Ordered consumers require a separate permission:
the variable-at-a-time engine can enumerate the same bag in a different order.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ConjunctiveBindingObservation

open ConjunctiveRegionProvenance GenericJoinRegions ConjunctiveBindingJoin
open ConjunctiveBindingDomain ConjunctiveBindingEnumeration PreparedJoinRegions IndexedJoinLeaves

variable {n : Nat} {Value Id : Type} [LinearOrder Value]

private theorem sum_key_readouts {Item Key K : Type} [DecidableEq Key] [AddCommMonoid K]
    (keys : Finset Key) (items : List Item) (key : Item → Key) (readout : Item → K)
    (covered : ∀ item ∈ items, key item ∈ keys) :
    (∑ target ∈ keys, ((items.filter fun item => decide (key item = target)).map readout).sum) =
      (items.map readout).sum := by
  induction items with
  | nil => simp
  | cons item items ih =>
      have tail := ih (fun next member => covered next (List.mem_cons_of_mem _ member))
      have member := covered item (by simp)
      have perKey (target : Key) :
          (((item :: items).filter fun entry => decide (key entry = target)).map readout).sum =
            (if key item = target then readout item else 0) +
              ((items.filter fun entry => decide (key entry = target)).map readout).sum := by
        by_cases same : key item = target <;> simp [same]
      simp only [perKey, Finset.sum_add_distrib, tail, List.map_cons, List.sum_cons]
      have one : (∑ target ∈ keys, if key item = target then readout item else 0) = readout item := by
        rw [Finset.sum_eq_single (key item)]
        · simp
        · intro target _ different
          simp [Ne.symm different]
        · intro absent
          exact False.elim (absent member)
      rw [one]

theorem reference_slice_values (domain : Finset Value) (before target : Environment n Value)
    (factors : List (Factor (Fin n) Value Id)) (outside : Value)
    (covered : Covered before factors)
    (member : target ∈ GenericJoinRegions.reference domain factors (List.finRange n) before) :
    (ConjunctiveBindingJoin.run before factors).filter (fun answer => decide (answer.1 = target)) =
      (witnesses (valuation outside target) factors).map (target, ·) := by
  have extension := reference_extends domain factors _ before target member
  obtain ⟨assignment, same⟩ := full_schedule_is_total domain factors before target
    (by simpa only [genericJoin_exact] using member)
  have valued : (fun name => some (valuation outside target name)) = target := by
    simp only [same, valuation, Option.getD_some]
  have projected := projected_witnesses_exact before (valuation outside target) factors
  rw [valued, show extendsTo before target = true from (extendsTo_iff _ _).mpr extension,
    if_pos rfl, project_is_key_slice before target factors covered] at projected
  have paired := congrArg (List.map (target, ·)) projected
  rw [List.map_map] at paired
  have unchanged :
      (((ConjunctiveBindingJoin.run before factors).filter fun answer => decide (answer.1 = target)).map
        ((target, ·) ∘ Prod.snd)) =
      ((ConjunctiveBindingJoin.run before factors).filter fun answer => decide (answer.1 = target)) := by
    conv_rhs => rw [← List.map_id (l := (ConjunctiveBindingJoin.run before factors).filter
      (fun answer => decide (answer.1 = target)))]
    apply List.map_congr_left
    intro answer present
    have equal : answer.1 = target := of_decide_eq_true (List.mem_filter.mp present).2
    exact Prod.ext equal.symm rfl
  exact unchanged.symm.trans paired

theorem source_readout_eq_reference {K : Type} [AddCommMonoid K]
    (domain : Finset Value) (before : Environment n Value) (factors : List (Factor (Fin n) Value Id))
    (outside : Value) (initial : InDomain domain before) (rows : RowsInDomain domain factors)
    (covered : Covered before factors) (readout : Environment n Value × List Id → K) :
    ((ConjunctiveBindingJoin.run before factors).map readout).sum =
      ∑ target ∈ GenericJoinRegions.reference domain factors (List.finRange n) before,
        ((witnesses (valuation outside target) factors).map (fun ids => readout (target, ids))).sum := by
  rw [← sum_key_readouts (GenericJoinRegions.reference domain factors (List.finRange n) before)
    (ConjunctiveBindingJoin.run before factors) Prod.fst readout
    (fun answer member => source_binding_is_reference_key domain before factors initial rows covered answer member)]
  apply Finset.sum_congr rfl
  intro target member
  rw [reference_slice_values domain before target factors outside covered member, List.map_map]
  rfl

theorem source_bag_eq_reference (domain : Finset Value) (before : Environment n Value)
    (factors : List (Factor (Fin n) Value Id)) (outside : Value)
    (initial : InDomain domain before) (rows : RowsInDomain domain factors) (covered : Covered before factors) :
    (ConjunctiveBindingJoin.run before factors : Multiset _) =
      IndexedJoinDelivery.sourceBag domain factors outside (List.finRange n) before := by
  have readout := source_readout_eq_reference domain before factors outside initial rows covered
    (fun answer => ({answer} : Multiset (Environment n Value × List Id)))
  have singletonSum (answers : List (Environment n Value × List Id)) :
      (answers.map (fun answer => ({answer} : Multiset (Environment n Value × List Id)))).sum =
        (answers : Multiset (Environment n Value × List Id)) := by
    simpa only [Multiset.map_coe, Multiset.sum_coe] using
      Multiset.sum_map_singleton (answers : Multiset (Environment n Value × List Id))
  rw [singletonSum] at readout
  unfold IndexedJoinDelivery.sourceBag Multiset.bind Multiset.join
  change _ = ∑ target ∈ GenericJoinRegions.reference domain factors (List.finRange n) before,
    (((witnesses (valuation outside target) factors).map (target, ·)) : Multiset (Environment n Value × List Id))
  rw [readout]
  apply Finset.sum_congr rfl
  intro target _
  simpa only [List.map_map, Function.comp_def] using
    singletonSum ((witnesses (valuation outside target) factors).map (target, ·))

theorem indexed_bag_eq_source {values : Finset Value} (domain : Domain values)
    (stored : List (StoredFactor n Value Id)) (outside : Value) (before : Environment n Value)
    (initial : InDomain values before) (rows : RowsInDomain values (sources stored))
    (covered : Covered before (sources stored)) :
    (IndexedJoinDelivery.deliver domain stored outside (List.finRange n) before : Multiset _) =
      (ConjunctiveBindingJoin.run before (sources stored) : Multiset (Environment n Value × List Id)) := by
  rw [IndexedJoinDelivery.delivery_bag_exact]
  exact (source_bag_eq_reference values before (sources stored) outside initial rows covered).symm

theorem indexed_commutative_readout {K : Type} [AddCommMonoid K]
    {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (before : Environment n Value) (initial : InDomain values before)
    (rows : RowsInDomain values (sources stored)) (covered : Covered before (sources stored))
    (readout : Environment n Value × List Id → K) :
    ((IndexedJoinDelivery.deliver domain stored outside (List.finRange n) before).map readout).sum =
      ((ConjunctiveBindingJoin.run before (sources stored)).map readout).sum := by
  simpa only [Multiset.map_coe, Multiset.sum_coe] using
    congrArg (fun bag : Multiset (Environment n Value × List Id) => (bag.map readout).sum)
      (indexed_bag_eq_source domain stored outside before initial rows covered)

namespace Controls

def reverseValues : Factor (Fin 1) Nat Nat :=
  ⟨1, fun _ => .variable 0, [(10, fun _ => 7), (20, fun _ => 2)]⟩

theorem source_keeps_row_order :
    (ConjunctiveBindingJoin.run (fun _ => none) [reverseValues]).map Prod.snd = [[10], [20]] := by decide +kernel

theorem bag_equality_does_not_preserve_first :
    ([[10], [20]] : Multiset (List Nat)) = ([[20], [10]] : Multiset (List Nat)) ∧
    ([[10], [20]] : List (List Nat)).head? ≠ ([[20], [10]] : List (List Nat)).head? := by
  constructor
  · exact Quot.sound (List.Perm.swap _ _ [])
  · decide +kernel

end Controls

end Mettapedia.GSLT.Dynamics.ConjunctiveBindingObservation
