import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionObservations
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite acceptance support is separate from a query's physical footprint

Support data records an actual finite set and the existing `SupportedBy`
licence. Exact observations have their supplied names; counts and absence
name no occurrence in their acceptance test. Arbitrary region observations
remain admissible without finite support. In particular, an effective
acceptance test need not have a finite nominal support.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.RegionQuerySupport

open PredicateQueryAdmission

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO}

structure AcceptanceSupport (query : RegionQuery T S O) where
  names : Finset O
  supported : query.SupportedBy names

def exact (region : S → T → Bool) (seen : Finset O) : AcceptanceSupport (RegionQuery.exact region seen) :=
  ⟨seen,RegionQuery.exact_supportedBy region seen⟩

def count (region : S → T → Bool) (number : Nat) : AcceptanceSupport (RegionQuery.count region number : RegionQuery T S O) :=
  ⟨∅,RegionQuery.count_supportedBy region number⟩

def predicate (quantifier : Quantifier) (region : S → T → Bool) :
    AcceptanceSupport (RegionQuery.predicate quantifier region : RegionQuery T S O) :=
  ⟨∅,RegionQuery.predicate_supportedBy quantifier region⟩

theorem supportedBy_mono {query : RegionQuery T S O} {smaller larger : Finset O}
    (supported : query.SupportedBy smaller) (included : smaller ⊆ larger) : query.SupportedBy larger := by
  intro permutation fixes candidate found
  exact supported permutation (fun occurrence member => fixes occurrence (included member)) candidate found

theorem rename_refl (query : RegionQuery T S O) : query.rename (Equiv.refl O) = query := by
  rcases query with ⟨region,accepts⟩
  simp [RegionQuery.rename]

theorem rename_trans (first second : O ≃ O) (query : RegionQuery T S O) :
    (query.rename first).rename second = query.rename (first.trans second) := by
  rcases query with ⟨region,accepts⟩
  apply congrArg (RegionQuery.mk region)
  funext candidate found
  apply congrArg (accepts candidate)
  rw [Finset.map_map]
  rfl

theorem rename_fixed {query : RegionQuery T S O} (support : AcceptanceSupport query)
    (permutation : O ≃ O) (fixes : ∀ occurrence ∈ support.names, permutation occurrence = occurrence) :
    query.rename permutation = query := by
  have fixesInverse : ∀ occurrence ∈ support.names, permutation.symm occurrence = occurrence := by
    intro occurrence member
    simpa only [Equiv.symm_apply_apply] using (congrArg permutation.symm (fixes occurrence member)).symm
  rcases query with ⟨region,accepts⟩
  apply congrArg (RegionQuery.mk region)
  funext candidate found
  exact propext (support.supported permutation.symm fixesInverse candidate found)

abbrev Supports (queries : List (RegionQuery T S O)) :=
  (index : Fin queries.length) → AcceptanceSupport queries[index]

def names [DecidableEq O] (queries : List (RegionQuery T S O)) (supports : Supports queries) : Finset O :=
  Finset.univ.biUnion fun index => (supports index).names

theorem mem_names [DecidableEq O] (queries : List (RegionQuery T S O)) (supports : Supports queries) (occurrence : O) :
    occurrence ∈ names queries supports ↔ ∃ index, occurrence ∈ (supports index).names := by
  simp [names]

theorem rename_queries_fixed [DecidableEq O] (queries : List (RegionQuery T S O)) (supports : Supports queries)
    (permutation : O ≃ O) (fixes : ∀ occurrence ∈ names queries supports, permutation occurrence = occurrence) :
    queries.map (RegionQuery.rename permutation) = queries := by
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    simp only [List.getElem_map]
    exact rename_fixed (supports ⟨index,rightBound⟩) permutation
      (fun occurrence member => fixes occurrence ((mem_names queries supports occurrence).mpr ⟨⟨index,rightBound⟩,member⟩))

namespace Controls

/-- This is an effective test of the supplied finite set. -/
def evenSet (found : Finset Nat) : Bool := decide (∀ occurrence ∈ found, occurrence % 2 = 0)

def parityQuery : RegionQuery Unit Unit Nat :=
  ⟨fun _ _ => true,fun _ found => evenSet found = true⟩

theorem parity_singleton_iff (candidate : Unit) (occurrence : Nat) :
    parityQuery.accepts candidate {occurrence} ↔ occurrence % 2 = 0 := by
  simp [parityQuery,evenSet]

/-- Every claimed finite support misses an even/odd transposition that
changes this actual query's acceptance of a singleton. -/
theorem parity_has_no_finite_support (names : Finset Nat) : ¬ parityQuery.SupportedBy names := by
  intro supported
  let bound := names.sup id
  let even := 2 * (bound + 1)
  let odd := even + 1
  have evenGt : bound < even := by dsimp [even]; omega
  have oddGt : bound < odd := by dsimp [odd]; omega
  have evenOutside : even ∉ names := by
    intro member
    have atMost : even ≤ bound := Finset.le_sup (f := id) member
    omega
  have oddOutside : odd ∉ names := by
    intro member
    have atMost : odd ≤ bound := Finset.le_sup (f := id) member
    omega
  let permutation := Equiv.swap even odd
  have fixes : ∀ occurrence ∈ names, permutation occurrence = occurrence := by
    intro occurrence member
    exact Equiv.swap_apply_of_ne_of_ne
      (fun same => evenOutside (same ▸ member)) (fun same => oddOutside (same ▸ member))
  have mapped : ({even} : Finset Nat).map permutation.toEmbedding = {odd} := by
    simp [permutation]
  have transported := supported permutation fixes () {even}
  rw [mapped] at transported
  have evenMod : even % 2 = 0 := by dsimp [even]; omega
  have oddMod : odd % 2 = 1 := by dsimp [odd,even]; omega
  have accepted := transported.mpr ((parity_singleton_iff () even).mpr evenMod)
  have impossible := (parity_singleton_iff () odd).mp accepted
  omega

theorem parity_no_support_data : IsEmpty (AcceptanceSupport parityQuery) :=
  ⟨fun support => parity_has_no_finite_support support.names support.supported⟩

/-- Acceptance support is not the set of physically read identities. -/
theorem count_support_empty_footprint_nonempty :
    (count (O := Nat) (S := Unit) (fun _ (label : Bool) => label) 1).names = ∅ ∧
      (RegionQuery.count (S := Unit) (fun _ (label : Bool) => label) 1).Holds () (fun _ : Nat => true) {7} ∧
      ((RegionQuery.count (S := Unit) (fun _ (label : Bool) => label) 1).footprintAt () (fun _ : Nat => true) {7}).seen = {7} := by
  refine ⟨rfl,?_,?_⟩
  · simp [RegionQuery.count_holds_iff,MeTTaCalculus.OccurrenceCommits.regionOf]
  · simp [RegionQuery.footprintAt,RegionQuery.count,MeTTaCalculus.OccurrenceCommits.regionOf]

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.RegionQuerySupport
