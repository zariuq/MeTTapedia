import Mettapedia.GSLT.Dynamics.ConjunctiveRegionProvenance
import Mettapedia.GSLT.Dynamics.RegionPortfolio
import Mettapedia.Machines.PolyCursor
import Mathlib.Data.Finset.Sort

/-!
# Variable-at-a-time joins with complete occurrence projections

The reference enumerates a finite supplied value domain, respecting captured
bindings, and filters at the end. The worker instead intersects the matching
rows' coordinate projections using the existing leapfrog implementation at
each coordinate. Both return a finite set of binding keys. Occurrence weights
are supplied separately by `ConjunctiveRegionProvenance`; deduplicating binding
keys is not deduplicating source facts or derivations.

Projection is deliberately conservative for order not bound yet. The
final check retains repeated-coordinate correlation and constant constraints.
This module proves exact enumeration. Building projections currently scans
rows in this reference implementation; indexed seek and sum-min work bounds
are additional obligations, not consequences of semantic exactness.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.GenericJoinRegions

open ConjunctiveRegionProvenance

variable {n : Nat} {Value Id : Type}

abbrev Environment (n : Nat) (Value : Type) := Fin n → Option Value

def Extends (before after : Environment n Value) : Prop :=
  ∀ coordinate value, before coordinate = some value → after coordinate = some value

theorem Extends.refl (environment : Environment n Value) : Extends environment environment :=
  fun _ _ same => same

theorem Extends.trans {a b c : Environment n Value} (first : Extends a b) (later : Extends b c) :
    Extends a c := fun coordinate value present => later coordinate value (first coordinate value present)

def compatible (environment : Environment n Value) (cell : Cell (Fin n) Value) (value : Value) : Prop :=
  match cell with
  | .constant literal => value = literal
  | .variable name => match environment name with
    | none => True
    | some bound => value = bound

variable [LinearOrder Value]

instance (environment : Environment n Value) (cell : Cell (Fin n) Value) (value : Value) :
    Decidable (compatible environment cell value) := by
  cases cell with
  | constant literal => exact inferInstanceAs (Decidable (value = literal))
  | «variable» name => cases found : environment name <;> simp only [compatible, found] <;> infer_instance

def rowMatches (environment : Environment n Value) (factor : Factor (Fin n) Value Id)
    (row : Id × (Fin factor.arity → Value)) : Prop :=
  ∀ column, compatible environment (factor.pattern column) (row.2 column)

instance (environment : Environment n Value) (factor : Factor (Fin n) Value Id)
    (row : Id × (Fin factor.arity → Value)) : Decidable (rowMatches environment factor row) :=
  inferInstanceAs (Decidable (∀ column, compatible environment (factor.pattern column) (row.2 column)))

def feasible (environment : Environment n Value) (factors : List (Factor (Fin n) Value Id)) : Prop :=
  ∀ factor ∈ factors, ∃ row ∈ factor.rows, rowMatches environment factor row

instance (environment : Environment n Value) (factors : List (Factor (Fin n) Value Id)) :
    Decidable (feasible environment factors) :=
  inferInstanceAs (Decidable (∀ factor ∈ factors, ∃ row ∈ factor.rows, rowMatches environment factor row))

omit [LinearOrder Value] in
theorem compatible_downward {before after : Environment n Value} (extension : Extends before after)
    (cell : Cell (Fin n) Value) (value : Value) (matched : compatible after cell value) :
    compatible before cell value := by
  cases cell with
  | constant literal => exact matched
  | «variable» name =>
      cases found : before name with
      | none => simp [compatible, found]
      | some bound => simpa [compatible, found, extension name bound found] using matched

omit [LinearOrder Value] in
theorem rowMatches_downward {before after : Environment n Value} (extension : Extends before after)
    (factor : Factor (Fin n) Value Id) (row : Id × (Fin factor.arity → Value))
    (matched : rowMatches after factor row) : rowMatches before factor row :=
  fun column => compatible_downward extension _ _ (matched column)

def allowed (domain : Finset Value) (environment : Environment n Value) (coordinate : Fin n) : Finset Value :=
  domain.filter fun value => environment coordinate = none ∨ environment coordinate = some value

theorem update_extends (domain : Finset Value) (environment : Environment n Value) (coordinate : Fin n)
    (value : Value) (permitted : value ∈ allowed domain environment coordinate) :
    Extends environment (Function.update environment coordinate (some value)) := by
  intro name old found
  by_cases same : name = coordinate
  · subst name
    obtain empty | equal := (Finset.mem_filter.mp permitted).2
    · rw [found] at empty; cases empty
    · have eqValues : old = value := Option.some.inj (found.symm.trans equal)
      simp [eqValues]
  · simp [Function.update_of_ne same, found]

def projection (environment : Environment n Value) (factor : Factor (Fin n) Value Id)
    (column : Fin factor.arity) : Finset Value :=
  ((factor.rows.filter fun row => decide (rowMatches environment factor row)).map
    fun row => row.2 column).toFinset

def domains (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (environment : Environment n Value) (coordinate : Fin n) : List (Finset Value) :=
  allowed domain environment coordinate :: factors.flatMap fun factor =>
    ((List.finRange factor.arity).filter fun column => factor.pattern column = .variable coordinate).map
      (projection environment factor)

def candidates (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (environment : Environment n Value) (coordinate : Fin n) : Finset Value :=
  (Mettapedia.Machines.PolyCursor.leapfrog
    ((domains domain factors environment coordinate).map (fun keys => keys.sort (· ≤ ·)))).toFinset

theorem mem_candidates_iff (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (environment : Environment n Value) (coordinate : Fin n) (value : Value) :
    value ∈ candidates domain factors environment coordinate ↔
      ∀ keys ∈ domains domain factors environment coordinate, value ∈ keys := by
  unfold candidates
  rw [List.mem_toFinset]
  rw [Mettapedia.Machines.PolyCursor.mem_leapfrog
    (Mettapedia.Machines.PolyCursor.total _) _ le_rfl]
  · have nonempty : ((domains domain factors environment coordinate).map
        (fun keys => keys.sort (· ≤ ·))) ≠ [] := by simp [domains]
    simp only [List.forall_mem_map, Finset.mem_sort]
    exact and_iff_right nonempty
  · intro keys member
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp member
    exact source.sortedLT_sort.pairwise

theorem candidate_allowed (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (environment : Environment n Value) (coordinate : Fin n) (value : Value)
    (present : value ∈ candidates domain factors environment coordinate) :
    value ∈ allowed domain environment coordinate :=
  (mem_candidates_iff domain factors environment coordinate value).mp present _ (by simp [domains])

/-- Any satisfying extension supplies a witness in every participating
projection. This is the no-false-negative law used by the whole join. -/
theorem satisfying_extension_is_candidate (domain : Finset Value)
    (factors : List (Factor (Fin n) Value Id)) (before after : Environment n Value)
    (coordinate : Fin n) (value : Value)
    (permitted : value ∈ allowed domain before coordinate) (extension : Extends before after)
    (assigned : after coordinate = some value) (satisfies : feasible after factors) :
    value ∈ candidates domain factors before coordinate := by
  apply (mem_candidates_iff domain factors before coordinate value).mpr
  intro keys member
  simp only [domains, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_finRange, true_and, decide_eq_true_eq] at member
  rcases member with rfl | ⟨factor, present, column, used, rfl⟩
  · exact permitted
  · obtain ⟨row, rowPresent, matched⟩ := satisfies factor present
    have matchBefore := rowMatches_downward extension factor row matched
    have sameValue : row.2 column = value := by
      have atColumn := matched column
      simpa [compatible, used, assigned] using atColumn
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨row, List.mem_filter.mpr ⟨rowPresent, by simpa using matchBefore⟩, sameValue⟩

def reference (domain : Finset Value) (factors : List (Factor (Fin n) Value Id)) :
    List (Fin n) → Environment n Value → Finset (Environment n Value)
  | [], environment => if feasible environment factors then {environment} else ∅
  | coordinate :: rest, environment =>
      (allowed domain environment coordinate).biUnion fun value =>
        reference domain factors rest (Function.update environment coordinate (some value))

def genericJoin (domain : Finset Value) (factors : List (Factor (Fin n) Value Id)) :
    List (Fin n) → Environment n Value → Finset (Environment n Value)
  | [], environment => if feasible environment factors then {environment} else ∅
  | coordinate :: rest, environment =>
      (candidates domain factors environment coordinate).biUnion fun value =>
        genericJoin domain factors rest (Function.update environment coordinate (some value))

theorem reference_extends (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (order : List (Fin n)) (before after : Environment n Value)
    (produced : after ∈ reference domain factors order before) : Extends before after := by
  induction order generalizing before with
  | nil =>
      by_cases satisfied : feasible before factors
      · have same : after = before := by simpa [reference, satisfied] using produced
        subst after
        exact Extends.refl _
      · simp [reference, satisfied] at produced
  | cons coordinate rest ih =>
      obtain ⟨value, permitted, remaining⟩ := Finset.mem_biUnion.mp produced
      exact (update_extends domain before coordinate value permitted).trans (ih _ remaining)

theorem reference_feasible (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (order : List (Fin n)) (before after : Environment n Value)
    (produced : after ∈ reference domain factors order before) : feasible after factors := by
  induction order generalizing before with
  | nil =>
      by_cases satisfied : feasible before factors
      · have same : after = before := by simpa [reference, satisfied] using produced
        simpa [same] using satisfied
      · simp [reference, satisfied] at produced
  | cons coordinate rest ih =>
      obtain ⟨value, _, remaining⟩ := Finset.mem_biUnion.mp produced
      exact ih _ remaining

/-- Exact output bindings for every finite coordinate schedule and captured
environment. Unused or repeated order are allowed: neither overwrites a
previously captured value. The final full-coordinate call binds all coordinates. -/
theorem genericJoin_exact (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (order : List (Fin n)) (environment : Environment n Value) :
    genericJoin domain factors order environment = reference domain factors order environment := by
  induction order generalizing environment with
  | nil => rfl
  | cons coordinate rest ih =>
      simp only [genericJoin, reference, ih]
      ext final
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨value, candidate, remaining⟩
        exact ⟨value, candidate_allowed domain factors environment coordinate value candidate, remaining⟩
      · rintro ⟨value, permitted, remaining⟩
        have extension := reference_extends domain factors rest _ final remaining
        refine ⟨value, ?_, remaining⟩
        apply satisfying_extension_is_candidate domain factors environment final coordinate value permitted
        · exact (update_extends domain environment coordinate value permitted).trans extension
        · exact extension coordinate value (Function.update_self ..)
        · exact reference_feasible domain factors rest _ final remaining

theorem reference_binds_scheduled (domain : Finset Value)
    (factors : List (Factor (Fin n) Value Id)) (order : List (Fin n))
    (before after : Environment n Value) (produced : after ∈ reference domain factors order before)
    (name : Fin n) (scheduled : name ∈ order) : ∃ value, after name = some value := by
  induction order generalizing before with
  | nil => cases scheduled
  | cons coordinate rest ih =>
      obtain ⟨value, _, remaining⟩ := Finset.mem_biUnion.mp produced
      rcases List.mem_cons.mp scheduled with same | later
      · subst name
        exact ⟨value, reference_extends domain factors rest _ after remaining coordinate value
          (Function.update_self ..)⟩
      · exact ih _ remaining later

/-- Full scheduling leaves no wildcard. The resulting environment therefore
has a total valuation, rather than a collection of unrelated local witnesses. -/
theorem full_schedule_is_total (domain : Finset Value)
    (factors : List (Factor (Fin n) Value Id)) (before after : Environment n Value)
    (produced : after ∈ genericJoin domain factors (List.finRange n) before) :
    ∃ assignment : Fin n → Value, after = fun name => some (assignment name) := by
  classical
  rw [genericJoin_exact] at produced
  have bound : ∀ name, ∃ value, after name = some value := fun name =>
    reference_binds_scheduled domain factors _ before after produced name (by simp)
  exact ⟨fun name => Classical.choose (bound name),
    funext fun name => Classical.choose_spec (bound name)⟩

theorem full_row_matches_iff (assignment : Fin n → Value) (factor : Factor (Fin n) Value Id)
    (row : Id × (Fin factor.arity → Value)) :
    rowMatches (fun name => some (assignment name)) factor row ↔
      factor.acceptsRow assignment row = true := by
  rw [Factor.acceptsRow_iff]
  unfold rowMatches
  apply forall_congr'
  intro column
  cases factor.pattern column <;> rfl

/-- The full worker's output satisfies the independently defined ground
pattern semantics, with every variable correlation shared across factors. -/
theorem full_schedule_source_sound (domain : Finset Value)
    (factors : List (Factor (Fin n) Value Id)) (before after : Environment n Value)
    (produced : after ∈ genericJoin domain factors (List.finRange n) before) :
    ∃ assignment : Fin n → Value,
      after = (fun name => some (assignment name)) ∧
      ∀ factor ∈ factors, ∃ row ∈ factor.rows, factor.acceptsRow assignment row = true := by
  obtain ⟨assignment, same⟩ := full_schedule_is_total domain factors before after produced
  have satisfies := reference_feasible domain factors (List.finRange n) before after
    (by simpa [genericJoin_exact] using produced)
  refine ⟨assignment, same, fun factor present => ?_⟩
  obtain ⟨row, stored, matched⟩ := satisfies factor present
  rw [same] at matched
  exact ⟨row, stored, (full_row_matches_iff assignment factor row).mp matched⟩

theorem reference_complete (domain : Finset Value)
    (factors : List (Factor (Fin n) Value Id)) (order : List (Fin n))
    (before after : Environment n Value) (extension : Extends before after)
    (satisfied : feasible after factors)
    (assigned : ∀ name ∈ order, ∃ value ∈ domain, after name = some value)
    (unchanged : ∀ name, name ∉ order → after name = before name) :
    after ∈ reference domain factors order before := by
  induction order generalizing before with
  | nil =>
      have same : after = before := funext fun name => unchanged name (by simp)
      subst after
      simp [reference, satisfied]
  | cons coordinate rest ih =>
      obtain ⟨value, inDomain, atCoordinate⟩ := assigned coordinate (by simp)
      have permitted : value ∈ allowed domain before coordinate := by
        apply Finset.mem_filter.mpr
        refine ⟨inDomain, ?_⟩
        cases found : before coordinate with
        | none => exact Or.inl rfl
        | some old =>
            have equal : old = value := Option.some.inj ((extension coordinate old found).symm.trans atCoordinate)
            exact Or.inr (congrArg some equal)
      apply Finset.mem_biUnion.mpr
      refine ⟨value, permitted, ih (Function.update before coordinate (some value)) ?_
        (fun name present => assigned name (List.mem_cons_of_mem _ present)) ?_⟩
      · intro name held present
        by_cases same : name = coordinate
        · subst name
          simp only [Function.update_self, Option.some.injEq] at present
          simpa [← present] using atCoordinate
        · apply extension name held
          simpa [Function.update_of_ne same] using present
      · intro name outside
        by_cases same : name = coordinate
        · subst name
          simpa using atCoordinate
        · rw [Function.update_of_ne same]
          exact unchanged name (by simp [same, outside])

/-- Every full valuation satisfying the original ground patterns is reached,
provided its values are in the supplied finite domain and it respects captures.
Together with source soundness this prevents invented or missing answers. -/
theorem full_schedule_source_complete (domain : Finset Value)
    (factors : List (Factor (Fin n) Value Id)) (before : Environment n Value)
    (assignment : Fin n → Value) (bounded : ∀ name, assignment name ∈ domain)
    (captured : Extends before (fun name => some (assignment name)))
    (satisfied : ∀ factor ∈ factors, ∃ row ∈ factor.rows,
      factor.acceptsRow assignment row = true) :
    (fun name => some (assignment name)) ∈ genericJoin domain factors (List.finRange n) before := by
  rw [genericJoin_exact]
  apply reference_complete domain factors _ before _ captured
  · intro factor present
    obtain ⟨row, stored, matched⟩ := satisfied factor present
    exact ⟨row, stored, (full_row_matches_iff assignment factor row).mpr matched⟩
  · intro name _
    exact ⟨assignment name, bounded name, rfl⟩
  · intro name outside
    simp at outside

/-- On a full result the default is never read. It only makes the annotation
function total on environments which are not outputs of the full schedule. -/
def valuation (fallback : Value) (environment : Environment n Value) : Fin n → Value :=
  fun name => (environment name).getD fallback

theorem default_irrelevant_on_full_output (domain : Finset Value)
    (factors : List (Factor (Fin n) Value Id)) (before after : Environment n Value)
    (produced : after ∈ genericJoin domain factors (List.finRange n) before)
    (first second : Value) : valuation first after = valuation second after := by
  obtain ⟨assignment, rfl⟩ := full_schedule_is_total domain factors before after produced
  rfl

/-- The worker visits each binding key once and evaluates its occurrence
weight without enumerating its derivation Cartesian product. The reference
enumerates both value assignments and the physical row witnesses. -/
theorem weighted_genericJoin_exact {K : Type} [CommSemiring K]
    (tag : Id → K) (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (before : Environment n Value) (fallback : Value) :
    (∑ environment ∈ genericJoin domain factors (List.finRange n) before,
      factorized tag (valuation fallback environment) factors) =
    ∑ environment ∈ reference domain factors (List.finRange n) before,
      interpretation tag (witnesses (valuation fallback environment) factors) := by
  rw [genericJoin_exact]
  exact Finset.sum_congr rfl (fun _ _ => factorized_exact _ _ _)

namespace Portfolio

open ObservationQualified

def questions (n : Nat) (Value : Type) : RegionObservations.Family (Finset (Environment n Value)) where
  Question := Finset (Environment n Value) → Bool
  Answer _ := Bool
  read question result := question result

def boundary (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (order : List (Fin n)) :
    Boundary (Environment n Value) (Finset (Environment n Value)) (Finset (Environment n Value)) where
  source := reference domain factors order
  summarize := id
  future := questions n Value
  sufficient _ _ same _ := congrArg _ same

/-- A successful empty join is a committed empty result. It is not confused
with the generic portfolio's separate specialization-decline constructor. -/
def region (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (order : List (Fin n)) : CertifiedRegion (boundary domain factors order) Nat where
  regime := 0
  Artifact := Finset (Environment n Value)
  attempt environment := .committed (genericJoin domain factors order environment)
  decode := id
  restores _ _ impossible := by cases impossible
  exact environment _ committed := by
    cases committed
    exact genericJoin_exact domain factors order environment

end Portfolio

namespace Controls

def edge (a b : Fin 3) (rows : List (Nat × (Nat × Nat))) : Factor (Fin 3) Nat Nat :=
  ⟨2, (fun column => .variable (if column = 0 then a else b)),
    rows.map fun row => (row.1, fun column => if column = 0 then row.2.1 else row.2.2)⟩

def triangle : List (Factor (Fin 3) Nat Nat) :=
  [edge 0 1 [(10, (0, 1)), (11, (0, 1))], edge 1 2 [(20, (1, 2))], edge 2 0 [(30, (2, 0))]]

theorem cyclic_triangle_enumeration :
    genericJoin {0, 1, 2} triangle [0, 1, 2] (fun _ => none) =
      {fun coordinate => some coordinate.val} := by
  rw [genericJoin_exact]
  decide

theorem duplicate_edge_weight_not_lost :
    factorized (fun _ => (1 : Nat)) (fun coordinate : Fin 3 => coordinate.val) triangle = 2 := by decide

theorem captured_conflict_has_no_result :
    genericJoin {0, 1, 2} triangle [0, 1, 2] (fun _ => some 2) = ∅ := by
  rw [genericJoin_exact]
  decide

def repeatedCoordinate : Factor (Fin 1) Nat Nat :=
  ⟨2, fun _ => .variable 0, [(40, fun column => if column = 0 then 1 else 2)]⟩

theorem repeated_coordinate_is_not_two_wildcards :
    genericJoin {1, 2} [repeatedCoordinate] [0] (fun _ => none) = ∅ := by
  rw [genericJoin_exact]
  decide

theorem committed_empty_is_not_decline :
    (Portfolio.region {1, 2} [repeatedCoordinate] [0]).attempt (fun _ => none) =
      .committed (∅ : Finset (Environment 1 Nat)) := by
  change PartialRegionPlan.Attempt.committed (genericJoin {1, 2} [repeatedCoordinate] [0] (fun _ => none)) = _
  rw [repeated_coordinate_is_not_two_wildcards]
  rfl

end Controls

#print axioms mem_candidates_iff
#print axioms satisfying_extension_is_candidate
#print axioms genericJoin_exact
#print axioms full_schedule_source_sound
#print axioms full_schedule_source_complete
#print axioms weighted_genericJoin_exact
#print axioms Portfolio.region
#print axioms Controls.cyclic_triangle_enumeration

end Mettapedia.GSLT.Dynamics.GenericJoinRegions
