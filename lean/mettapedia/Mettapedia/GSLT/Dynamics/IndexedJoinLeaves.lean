import Mettapedia.GSLT.Dynamics.PreparedJoinRegions

/-!
# Indexed feasibility and occurrence annotations at join leaves

Full assignments check factor existence through the retained occurrence
indexes. The general entry preserves the source fallback for partial
assignments. A schedule invariant proves that the complete-variable join
never takes that partial-assignment fallback at a leaf. Weighted answers
use the same retained occurrence leaves and preserve the independently
defined authored witness interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.IndexedJoinLeaves

open ConjunctiveRegionProvenance GenericJoinRegions PreparedJoinRegions

variable {n : Nat} {Value Id : Type} [LinearOrder Value]

def groundCheck (stored : List (StoredFactor n Value Id)) (outside : Value) (assignment : Fin n → Value) : Bool :=
  stored.all (fun factor => PreparedFactorIndex.present factor.leaves assignment outside)

theorem groundCheck_exact (stored : List (StoredFactor n Value Id)) (outside : Value)
    (assignment : Fin n → Value) : groundCheck stored outside assignment = true ↔
      feasible (fun name => some (assignment name)) (sources stored) := by
  simp only [groundCheck, List.all_eq_true, PreparedFactorIndex.present_exact,
    feasible, sources, List.forall_mem_map]
  constructor
  · intro all factor member
    obtain ⟨row, rowMember, matched⟩ := all factor member
    exact ⟨row, rowMember, (full_row_matches_iff assignment factor.source row).mpr matched⟩
  · intro all factor member
    obtain ⟨row, rowMember, matched⟩ := all factor member
    exact ⟨row, rowMember, (full_row_matches_iff assignment factor.source row).mp matched⟩

def Total (environment : Environment n Value) : Prop := ∀ name, (environment name).isSome

instance (environment : Environment n Value) : Decidable (Total environment) :=
  inferInstanceAs (Decidable (∀ name, (environment name).isSome))

omit [LinearOrder Value] in
theorem total_as_assignment (environment : Environment n Value) (outside : Value) (total : Total environment) :
    environment = fun name => some (valuation outside environment name) := by
  funext name
  have present := total name
  cases found : environment name with
  | none => simp [found] at present
  | some value => simp [valuation, found]

def leafCheck (stored : List (StoredFactor n Value Id)) (outside : Value)
    (environment : Environment n Value) : Bool :=
  if Total environment then groundCheck stored outside (valuation outside environment)
  else decide (feasible environment (sources stored))

theorem leafCheck_exact (stored : List (StoredFactor n Value Id)) (outside : Value)
    (environment : Environment n Value) : leafCheck stored outside environment = true ↔
      feasible environment (sources stored) := by
  unfold leafCheck
  split
  next total =>
    rw [groundCheck_exact]
    rw [← total_as_assignment environment outside total]
  · simp

def run {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) : List (Fin n) → Environment n Value → Finset (Environment n Value)
  | [], environment => if leafCheck stored outside environment then {environment} else ∅
  | coordinate :: rest, environment =>
      (CyclicJoinRegions.execute (stage domain stored outside environment coordinate)).biUnion (fun value =>
        run domain stored outside rest (Function.update environment coordinate (some value)))

theorem run_exact {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (environment : Environment n Value) :
    run domain stored outside order environment = execute domain stored outside order environment := by
  induction order generalizing environment with
  | nil =>
      change (if leafCheck stored outside environment = true then _ else _) =
        (if feasible environment (sources stored) then _ else _)
      simp only [leafCheck_exact]
  | cons coordinate rest ih =>
      simpa only [run, execute, CyclicJoinRegions.cyclicJoin] using
        congrArg (fun child => (CyclicJoinRegions.execute (stage domain stored outside environment coordinate)).biUnion child)
          (funext (fun value => ih (Function.update environment coordinate (some value))))

def leafStates {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) : List (Fin n) → Environment n Value → List (Environment n Value)
  | [], environment => [environment]
  | coordinate :: rest, environment =>
      ((CyclicJoinRegions.execute (stage domain stored outside environment coordinate)).sort (· ≤ ·)).flatMap
        (fun value => leafStates domain stored outside rest (Function.update environment coordinate (some value)))

def Covers (order : List (Fin n)) (environment : Environment n Value) : Prop :=
  ∀ name, name ∈ order ∨ (environment name).isSome

omit [LinearOrder Value] in
theorem covers_update (coordinate : Fin n) (rest : List (Fin n)) (environment : Environment n Value)
    (value : Value) (covers : Covers (coordinate :: rest) environment) :
    Covers rest (Function.update environment coordinate (some value)) := by
  intro name
  by_cases same : name = coordinate
  · subst name
    exact Or.inr (by simp)
  · rcases covers name with member | present
    · exact Or.inl (by simpa [same] using member)
    · exact Or.inr (by simpa [Function.update_of_ne same] using present)

theorem leaves_total {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (before : Environment n Value) (covers : Covers order before) :
    ∀ after ∈ leafStates domain stored outside order before, Total after := by
  induction order generalizing before with
  | nil =>
      intro after member
      have same : after = before := List.mem_singleton.mp member
      subst after
      intro name
      exact (covers name).resolve_left (by simp)
  | cons coordinate rest ih =>
      intro after member
      obtain ⟨value, _, later⟩ := List.mem_flatMap.mp member
      exact ih _ (covers_update coordinate rest before value covers) after later

/-- This covers attempted leaves too, not only successful output bindings. -/
theorem full_schedule_never_scans_source_at_leaf {values : Finset Value} (domain : Domain values)
    (stored : List (StoredFactor n Value Id)) (outside : Value) (before : Environment n Value) :
    ∀ after ∈ leafStates domain stored outside (List.finRange n) before,
      leafCheck stored outside after = groundCheck stored outside (valuation outside after) := by
  intro after member
  have total := leaves_total domain stored outside (List.finRange n) before
    (fun name => Or.inl (List.mem_finRange name)) after member
  exact if_pos total

def annotation {K : Type} [CommSemiring K] (stored : List (StoredFactor n Value Id))
    (tag : Id → K) (outside : Value) (environment : Environment n Value) : K :=
  (stored.map (fun factor => PreparedFactorIndex.weight factor.leaves tag (valuation outside environment) outside)).prod

theorem annotation_exact {K : Type} [CommSemiring K] (stored : List (StoredFactor n Value Id))
    (tag : Id → K) (outside : Value) (environment : Environment n Value) :
    annotation stored tag outside environment = factorized tag (valuation outside environment) (sources stored) := by
  simp only [annotation, factorized, sources, List.map_map, Function.comp_def, PreparedFactorIndex.weight_exact]

theorem weighted_source_exact {K : Type} [CommSemiring K] {values : Finset Value}
    (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (tag : Id → K) (outside : Value) (before : Environment n Value) :
    (∑ environment ∈ run domain stored outside (List.finRange n) before, annotation stored tag outside environment) =
      ∑ environment ∈ GenericJoinRegions.reference values (sources stored) (List.finRange n) before,
        interpretation tag (witnesses (valuation outside environment) (sources stored)) := by
  simp only [run_exact, annotation_exact]
  exact weighted_execute_exact domain stored outside tag before

namespace Portfolio

open ObservationQualified

def region {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) :
    CertifiedRegion (GenericJoinRegions.Portfolio.boundary values (sources stored) order) Nat where
  regime := 3
  Artifact := Finset (Environment n Value)
  attempt environment := .committed (run domain stored outside order environment)
  decode := id
  restores _ _ impossible := by cases impossible
  exact environment _ committed := by
    cases committed
    rw [run_exact, execute_exact]
    rfl

end Portfolio

namespace Controls

open IndexedJoinRegions.Controls

theorem duplicate_path_votes :
    (∑ environment ∈ run (prepareDomain 0 {0, 1, 2}) (prepareFactors path) 0 (List.finRange 3) (fun _ => none),
      annotation (prepareFactors path) (fun _ => (1 : Nat)) 0 environment) = 4 := by
  rw [weighted_source_exact, sources_prepare]
  decide +kernel

theorem partial_assignment_keeps_source_fallback :
    leafCheck (prepareFactors path) 0 (fun _ => none) = decide (feasible (fun _ => none) path) := by
  simp only [leafCheck, Total, Option.isSome_none, Bool.false_eq_true, forall_const, ↓reduceIte, sources_prepare]

theorem ground_conflict_not_an_answer :
    groundCheck (prepareFactors clique) 0 (fun _ => 0) = false := by
  apply Bool.eq_false_iff.mpr
  simp only [ne_eq, groundCheck_exact, sources_prepare]
  decide +kernel

end Controls

end Mettapedia.GSLT.Dynamics.IndexedJoinLeaves
