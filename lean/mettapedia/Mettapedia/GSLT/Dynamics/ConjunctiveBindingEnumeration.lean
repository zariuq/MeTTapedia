import Mettapedia.GSLT.Dynamics.ConjunctiveBindingDomain
import Mettapedia.GSLT.Dynamics.IndexedJoinDelivery

/-!
# Source binding enumeration and indexed join counts

An input-domain and variable-coverage proof connects row-wise binding to a
variable-at-a-time join. Binding keys partition the source answers; each key
retains all of its occurrence witnesses. Counting keys alone is not counting
answers. No equality of traversal order is claimed by this commutative route.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ConjunctiveBindingEnumeration

open ConjunctiveRegionProvenance GenericJoinRegions ConjunctiveBindingJoin
open ConjunctiveBindingDomain PreparedJoinRegions IndexedJoinLeaves

variable {n : Nat} {Value Id : Type} [LinearOrder Value]

omit [LinearOrder Value] in
theorem total_extends_iff_equal (before target : Environment n Value)
    (total : ∀ name, ∃ value, before name = some value) :
    Extends before target ↔ before = target := by
  constructor
  · intro extension
    funext name
    obtain ⟨value, found⟩ := total name
    exact found.trans (extension name value found).symm
  · rintro rfl
    exact Extends.refl _

theorem project_is_key_slice (before target : Environment n Value)
    (factors : List (Factor (Fin n) Value Id)) (covered : Covered before factors) :
    project target (ConjunctiveBindingJoin.run before factors) =
      ((ConjunctiveBindingJoin.run before factors).filter fun answer => decide (answer.1 = target)).map Prod.snd := by
  have total := covered_results_total before factors covered
  generalize answers_eq : ConjunctiveBindingJoin.run before factors = answers at *
  clear answers_eq covered
  induction answers with
  | nil => rfl
  | cons answer answers ih =>
      have check : extendsTo answer.1 target = decide (answer.1 = target) := by
        apply Bool.eq_iff_iff.mpr
        simp only [extendsTo_iff, decide_eq_true_eq]
        exact total_extends_iff_equal answer.1 target (total answer (by simp))
      have rest := ih (fun result member => total result (List.mem_cons_of_mem _ member))
      cases same : decide (answer.1 = target) <;>
        simpa [project, check, same] using rest

private theorem sum_key_slices {Item Key : Type} [DecidableEq Key]
    (keys : Finset Key) (items : List Item) (key : Item → Key)
    (covered : ∀ item ∈ items, key item ∈ keys) :
    (∑ target ∈ keys, (items.filter fun item => decide (key item = target)).length) = items.length := by
  induction items with
  | nil => simp
  | cons item items ih =>
      have tail := ih (fun next member => covered next (List.mem_cons_of_mem _ member))
      have member := covered item (by simp)
      have perKey (target : Key) :
          ((item :: items).filter fun entry => decide (key entry = target)).length =
            (if key item = target then 1 else 0) +
              (items.filter fun entry => decide (key entry = target)).length := by
        by_cases same : key item = target <;> simp [same, Nat.add_comm]
      simp only [perKey, Finset.sum_add_distrib, tail, List.length_cons]
      have one : (∑ target ∈ keys, if key item = target then 1 else 0) = (1 : Nat) := by
        rw [Finset.sum_eq_single (key item)]
        · simp
        · intro target _ different
          simp [Ne.symm different]
        · intro absent
          exact False.elim (absent member)
      omega

theorem reference_slice (domain : Finset Value) (before target : Environment n Value)
    (factors : List (Factor (Fin n) Value Id)) (outside : Value)
    (covered : Covered before factors)
    (member : target ∈ GenericJoinRegions.reference domain factors (List.finRange n) before) :
    ((ConjunctiveBindingJoin.run before factors).filter fun answer => decide (answer.1 = target)).length =
      (witnesses (valuation outside target) factors).length := by
  have extension := reference_extends domain factors _ before target member
  obtain ⟨assignment, same⟩ := full_schedule_is_total domain factors before target
    (by simpa only [genericJoin_exact] using member)
  have valued : (fun name => some (valuation outside target name)) = target := by
    simp only [same, valuation, Option.getD_some]
  have projected := projected_witnesses_exact before (valuation outside target) factors
  rw [valued, show extendsTo before target = true from (extendsTo_iff _ _).mpr extension] at projected
  rw [project_is_key_slice before target factors covered] at projected
  simpa only [↓reduceIte, List.length_map] using congrArg List.length projected

theorem source_count_eq_reference (domain : Finset Value) (before : Environment n Value)
    (factors : List (Factor (Fin n) Value Id)) (outside : Value)
    (initial : InDomain domain before) (rows : RowsInDomain domain factors) (covered : Covered before factors) :
    (ConjunctiveBindingJoin.run before factors).length =
      ∑ target ∈ GenericJoinRegions.reference domain factors (List.finRange n) before,
        (witnesses (valuation outside target) factors).length := by
  rw [← sum_key_slices (GenericJoinRegions.reference domain factors (List.finRange n) before)
    (ConjunctiveBindingJoin.run before factors) Prod.fst
    (fun answer member => source_binding_is_reference_key domain before factors initial rows covered answer member)]
  apply Finset.sum_congr rfl
  intro target member
  exact reference_slice domain before target factors outside covered member

theorem indexed_count_eq_source {values : Finset Value} (domain : Domain values)
    (stored : List (StoredFactor n Value Id)) (outside : Value) (before : Environment n Value)
    (initial : InDomain values before) (rows : RowsInDomain values (sources stored))
    (covered : Covered before (sources stored)) :
    IndexedJoinDelivery.outputCount domain stored outside (List.finRange n) before =
      (ConjunctiveBindingJoin.run before (sources stored)).length := by
  rw [IndexedJoinDelivery.output_count_source]
  exact (source_count_eq_reference values before (sources stored) outside initial rows covered).symm

/-- Counting uses the product of per-factor occurrence counts, not a materialized
Cartesian product of complete occurrence witnesses. -/
def weightedCount {values : Finset Value} (domain : Domain values)
    (stored : List (StoredFactor n Value Id)) (outside : Value) (before : Environment n Value) : Nat :=
  ∑ target ∈ IndexedJoinLeaves.run domain stored outside (List.finRange n) before,
    annotation stored (fun _ => (1 : Nat)) outside target

theorem weighted_count_eq_source {values : Finset Value} (domain : Domain values)
    (stored : List (StoredFactor n Value Id)) (outside : Value) (before : Environment n Value)
    (initial : InDomain values before) (rows : RowsInDomain values (sources stored))
    (covered : Covered before (sources stored)) :
    weightedCount domain stored outside before = (ConjunctiveBindingJoin.run before (sources stored)).length := by
  unfold weightedCount
  rw [weighted_source_exact, source_count_eq_reference values before (sources stored) outside initial rows covered]
  apply Finset.sum_congr rfl
  intro target _
  simp [interpretation]

namespace Controls

open ConjunctiveBindingJoin.Controls

theorem duplicate_rows_are_not_just_one_key :
    IndexedJoinDelivery.outputCount (prepareDomain 0 {7}) (prepareFactors [duplicate, duplicate])
      0 (List.finRange 1) (fun _ => none) = 4 := by
  rw [IndexedJoinDelivery.output_count_source, sources_prepare]
  decide +kernel

theorem unused_variable_would_multiply_answers :
    IndexedJoinDelivery.outputCount (prepareDomain 0 {1, 2}) (prepareFactors (Id := Nat) [])
      0 (List.finRange 1) (fun _ => none) = 2 ∧
    (ConjunctiveBindingJoin.run (Id := Nat) (fun (_ : Fin 1) => (none : Option Nat)) []).length = 1 := by
  rw [IndexedJoinDelivery.output_count_source, sources_prepare]
  decide +kernel

end Controls

end Mettapedia.GSLT.Dynamics.ConjunctiveBindingEnumeration
