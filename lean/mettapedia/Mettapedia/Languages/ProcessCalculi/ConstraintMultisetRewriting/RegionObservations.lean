import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PredicateQueryAdmission

/-!
# Region queries: a region over each solution, and what is observed of its occurrences

A predicate query of the occurrence-commit layer observes a region of labels. Its admission form
(`PredicateQueryAdmission.Query`) lets the region depend on the solution of the firing's constraints
and fixes the occurrences seen there. Two things fall outside that form.

* Some regions are not one pattern up to an equivalence. A schematic row matches several patterns at
  one solution while a row with shared unknowns matches only one, so their regions overlap without
  being equal; regions given by an equivalence are equal or disjoint.
* Some observations are not a fixed set of occurrences. A count holds of different occurrences at
  different solutions.

A **region query** therefore has two parts:

* `region`: at each solution, a predicate on labels, the query's fiber over that solution;
* `accepts`: at each solution, a predicate on the occurrences of that fiber, what is observed of them.

The observation sees only its fiber: every statement about a query goes through `regionOf`. So one
law carries every observation across a commit that writes nothing in its region
(`holds_fire_of_no_write`, `ask_fire_iff`), and the writes a query ignores (`IgnoresWrites`) do not
depend on what it observes.

Observations defined here: `exact seen` (the fiber holds exactly the occurrences `seen`), `count n`
(the fiber holds `n` occurrences) and `predicate q` (the quantifier `q` holds of the fiber's
occurrences: `any` asks for one, `none` for none). The admission form's query is the exact
observation of its region (`Query.toRegion`), with its ask and its ignored writes unchanged. No
observation is a default.

At one solution and one world a query has a footprint in the occurrence layer: the occurrences its
fiber holds there (`footprintAt`). A count fixes no set of occurrences in general, only this one, at
that model and world.

For a firing with region queries: its footprint at one solution and world (`regionCommit`) and its
admission (`RegionValid`). The admission form's are the exact case: `regionCommit_toRegion` where the
exact queries hold, and `valid_iff_regionValid`.

Not here: the round and the steps that carry region queries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PredicateQueryAdmission

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uT uS uO uO'

/-- **A region query**: at each solution, a region of labels (the query's fiber over that solution)
and what is observed of the occurrences in it. -/
structure RegionQuery (T : Type uT) (S : Type uS) (O : Type uO) where
  region : S → T → Bool
  accepts : S → Finset O → Prop

namespace RegionQuery

variable {T : Type uT} {S : Type uS} {O : Type uO}

/-- The query holds at a solution when what it observes of the occurrences of its fiber there is
accepted. It reads the world only through `regionOf`. -/
def Holds (q : RegionQuery T S O) (σ : S) (label : O → T) (world : Finset O) : Prop :=
  q.accepts σ (regionOf label world (q.region σ))

/-- Asked at a constraint problem: the query holds at every solution of the problem. -/
def Ask (A : SubstitutionAction T S) (problem : EquationStore T) (label : O → T)
    (world : Finset O) (q : RegionQuery T S O) : Prop :=
  A.Entails problem fun σ => q.Holds σ label world

/-- A writer is invisible to the query at a problem when, at every solution, nothing it takes or
makes lies in the query's fiber. It does not depend on what the query observes. -/
def IgnoresWrites (A : SubstitutionAction T S) (problem : EquationStore T) (label : O → T)
    (writer : Selection O) (q : RegionQuery T S O) : Prop :=
  A.Entails problem fun σ => ∀ o ∈ writer.taken ++ writer.made, q.region σ (label o) = false

/-! ## Observations -/

/-- **Exact**: the fiber holds exactly the occurrences `seen`. -/
def exact (region : S → T → Bool) (seen : Finset O) : RegionQuery T S O :=
  ⟨region, fun _ found => found = seen⟩

/-- **Count**: the fiber holds `number` occurrences. -/
def count (region : S → T → Bool) (number : Nat) : RegionQuery T S O :=
  ⟨region, fun _ found => found.card = number⟩

/-- **Predicate**: the quantifier holds of the fiber's occurrences. -/
def predicate (quantifier : Quantifier) (region : S → T → Bool) : RegionQuery T S O :=
  ⟨region, fun _ found => quantifier.Accepts found⟩

theorem exact_holds_iff {region : S → T → Bool} {seen : Finset O} {σ : S} {label : O → T}
    {world : Finset O} :
    (exact region seen).Holds σ label world ↔ regionOf label world (region σ) = seen :=
  Iff.rfl

theorem count_holds_iff {region : S → T → Bool} {number : Nat} {σ : S} {label : O → T}
    {world : Finset O} :
    (count region number).Holds σ label world ↔ (regionOf label world (region σ)).card = number :=
  Iff.rfl

theorem predicate_holds_iff {quantifier : Quantifier} {region : S → T → Bool} {σ : S}
    {label : O → T} {world : Finset O} :
    (predicate quantifier region).Holds σ label world ↔
      quantifier.Holds world fun o => region σ (label o) = true := by
  cases quantifier with
  | any =>
      show (regionOf label world (region σ)).Nonempty ↔ _
      constructor
      · rintro ⟨o, inside⟩
        exact ⟨o, (Finset.mem_filter.mp inside).1, (Finset.mem_filter.mp inside).2⟩
      · rintro ⟨o, present, inside⟩
        exact ⟨o, Finset.mem_filter.mpr ⟨present, inside⟩⟩
  | none =>
      show regionOf label world (region σ) = ∅ ↔ _
      rw [regionOf, Finset.filter_eq_empty_iff]
      rfl

theorem none_holds_iff {region : S → T → Bool} {σ : S} {label : O → T} {world : Finset O} :
    (predicate .none region).Holds σ label world ↔ ∀ o ∈ world, region σ (label o) = false := by
  rw [predicate_holds_iff]
  simp

/-! ## One transport law for every observation -/

section Transport

variable [DecidableEq O]

/-- **A commit that writes nothing in the fiber leaves what is observed of it as it was**, whatever
the observation. -/
theorem holds_fire_of_no_write {q : RegionQuery T S O} {σ : S} {label : O → T} {world : Finset O}
    {writer : Selection O}
    (outside : ∀ o ∈ writer.taken ++ writer.made, q.region σ (label o) = false) :
    q.Holds σ label (fire world (writer.commit (T := T))) ↔ q.Holds σ label world := by
  have noWrite : ∀ o ∈ (writer.commit (T := T)).taken ∪ (writer.commit (T := T)).made,
      q.region σ (label o) = false := by
    intro o member
    apply outside
    simp only [Selection.commit, Finset.mem_union, List.mem_toFinset] at member
    exact List.mem_append.mpr member
  unfold Holds
  rw [regionOf_fire_of_no_write noWrite]

/-- **At a problem**: a writer the query ignores leaves its ask as it was. -/
theorem ask_fire_iff {A : SubstitutionAction T S} {problem : EquationStore T} {label : O → T}
    {world : Finset O} {writer : Selection O} {q : RegionQuery T S O}
    (ignores : q.IgnoresWrites A problem label writer) :
    q.Ask A problem label (fire world (writer.commit (T := T))) ↔ q.Ask A problem label world := by
  constructor
  · intro asked σ model
    exact (holds_fire_of_no_write (ignores σ model)).mp (asked σ model)
  · intro asked σ model
    exact (holds_fire_of_no_write (ignores σ model)).mpr (asked σ model)

end Transport

/-! ## The footprint at one model -/

/-- **The footprint of a query at one solution and world**: the predicate query of the occurrence
layer that sees exactly what the fiber holds there. -/
def footprintAt (q : RegionQuery T S O) (σ : S) (label : O → T) (world : Finset O) :
    PredicateQuery O T :=
  ⟨q.region σ, regionOf label world (q.region σ)⟩

theorem footprintAt_holds (q : RegionQuery T S O) (σ : S) (label : O → T) (world : Finset O) :
    (q.footprintAt σ label world).Holds label world :=
  rfl

/-- The number of occurrences the fiber holds at one solution and world. -/
def cardAt (q : RegionQuery T S O) (σ : S) (label : O → T) (world : Finset O) : Nat :=
  (regionOf label world (q.region σ)).card

theorem count_holds_iff_cardAt {region : S → T → Bool} {number : Nat} {σ : S} {label : O → T}
    {world : Finset O} :
    (count region number).Holds σ label world ↔ (count region number).cardAt σ label world = number :=
  Iff.rfl

/-- Where an exact query holds, its footprint is the occurrences it names. -/
theorem exact_footprintAt {region : S → T → Bool} {seen : Finset O} {σ : S} {label : O → T}
    {world : Finset O} (holds : (exact region seen).Holds σ label world) :
    (exact region seen).footprintAt σ label world = ⟨region σ, seen⟩ := by
  have same : regionOf label world (region σ) = seen := holds
  show (⟨region σ, regionOf label world (region σ)⟩ : PredicateQuery O T) = ⟨region σ, seen⟩
  rw [same]

/-! ## Renaming identities, the identities an observation depends on, and uniformity -/

section Renaming

variable {O' : Type uO'}

/-- **Renaming occurrence identities** along a bijection: the region is unchanged, and the
observation reads the occurrences it is given back along the bijection. -/
def rename (π : O ≃ O') (q : RegionQuery T S O) : RegionQuery T S O' :=
  ⟨q.region, fun σ found => q.accepts σ (found.map π.symm.toEmbedding)⟩

/-- The fiber of a renamed world, read back along the bijection, is the fiber of the world. -/
theorem regionOf_rename (π : O ≃ O') (label : O → T) (world : Finset O) (region : T → Bool) :
    (regionOf (label ∘ π.symm) (world.map π.toEmbedding) region).map π.symm.toEmbedding =
      regionOf label world region := by
  unfold regionOf
  ext o
  constructor
  · intro member
    obtain ⟨o', inFilter, rfl⟩ := Finset.mem_map.mp member
    obtain ⟨inMap, inside⟩ := Finset.mem_filter.mp inFilter
    obtain ⟨a, inWorld, rfl⟩ := Finset.mem_map.mp inMap
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simpa using inWorld
    · simpa using inside
  · intro member
    obtain ⟨inWorld, inside⟩ := Finset.mem_filter.mp member
    refine Finset.mem_map.mpr ⟨π o, Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨o, inWorld, rfl⟩, ?_⟩, ?_⟩
    · simpa using inside
    · simp

/-- **Renaming is equivariant**: the renamed query holds of the renamed world, under the renamed
labels, exactly when the query holds of the world. -/
theorem rename_holds_iff (π : O ≃ O') (q : RegionQuery T S O) (σ : S) (label : O → T)
    (world : Finset O) :
    (q.rename π).Holds σ (label ∘ π.symm) (world.map π.toEmbedding) ↔ q.Holds σ label world := by
  show q.accepts σ ((regionOf (label ∘ π.symm) (world.map π.toEmbedding) (q.region σ)).map
      π.symm.toEmbedding) ↔ q.accepts σ (regionOf label world (q.region σ))
  rw [regionOf_rename]

end Renaming

/-- **An observation depends only on the identities in `N`**: a bijection that fixes `N` pointwise
leaves what it accepts unchanged. This is about the observation's own data, not about what it
reads: a count depends on no identity and still reads the rows of its fiber. -/
def SupportedBy (q : RegionQuery T S O) (N : Finset O) : Prop :=
  ∀ π : Equiv.Perm O, (∀ o ∈ N, π o = o) →
    ∀ σ found, q.accepts σ (found.map π.toEmbedding) ↔ q.accepts σ found

/-- A bijection that fixes a set pointwise maps it onto itself. -/
theorem map_eq_self_of_fixes (π : Equiv.Perm O) {N : Finset O} (fixes : ∀ o ∈ N, π o = o) :
    N.map π.toEmbedding = N := by
  ext o
  constructor
  · intro member
    obtain ⟨a, inN, rfl⟩ := Finset.mem_map.mp member
    simpa [fixes a inN] using inN
  · intro inN
    exact Finset.mem_map.mpr ⟨o, inN, by simp [fixes o inN]⟩

/-- **An exact observation depends on exactly the identities it names.** -/
theorem exact_supportedBy (region : S → T → Bool) (seen : Finset O) :
    (exact region seen).SupportedBy seen := by
  intro π fixes σ found
  show found.map π.toEmbedding = seen ↔ found = seen
  have same := map_eq_self_of_fixes π fixes
  constructor
  · intro mapped
    exact Finset.map_injective π.toEmbedding (mapped.trans same.symm)
  · rintro rfl
    exact same

/-- **A count depends on no identity.** -/
theorem count_supportedBy (region : S → T → Bool) (number : Nat) :
    (count region number : RegionQuery T S O).SupportedBy ∅ := by
  intro π _ σ found
  show (found.map π.toEmbedding).card = number ↔ found.card = number
  rw [Finset.card_map]

/-- **A predicate query depends on no identity.** -/
theorem predicate_supportedBy (quantifier : Quantifier) (region : S → T → Bool) :
    (predicate quantifier region : RegionQuery T S O).SupportedBy ∅ := by
  intro π _ σ found
  show quantifier.Accepts (found.map π.toEmbedding) ↔ quantifier.Accepts found
  cases quantifier <;> simp [Quantifier.Accepts]

/-- **The query reads every solution alike**: neither its region nor its observation depends on
the solution. -/
def Uniform (q : RegionQuery T S O) : Prop :=
  (∀ σ σ', q.region σ = q.region σ') ∧ ∀ σ σ', q.accepts σ = q.accepts σ'

/-- With a uniform query, holding at one solution is holding at every solution. -/
theorem Uniform.holds_iff {q : RegionQuery T S O} (uniform : q.Uniform) (σ σ' : S)
    (label : O → T) (world : Finset O) : q.Holds σ label world ↔ q.Holds σ' label world := by
  unfold Holds
  rw [uniform.1 σ σ', uniform.2 σ σ']

theorem exact_uniform (region : T → Bool) (seen : Finset O) :
    (exact (fun _ : S => region) seen).Uniform :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem count_uniform (region : T → Bool) (number : Nat) :
    (count (fun _ : S => region) number : RegionQuery T S O).Uniform :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem predicate_uniform (quantifier : Quantifier) (region : T → Bool) :
    (predicate quantifier (fun _ : S => region) : RegionQuery T S O).Uniform :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- **An exact observation sees every write into its fiber**: if a commit makes an occurrence of the
fiber that was not present, the exact observation cannot hold both before and after. A count can (see
`RegionObservationControls.count_keeps_a_swap_inside_its_region`). -/
theorem exact_not_both_of_make [DecidableEq O] {region : S → T → Bool} {seen : Finset O} {σ : S}
    {label : O → T} {world : Finset O} {writer : Selection O} {o : O} (made : o ∈ writer.made)
    (absentBefore : o ∉ world) (inside : region σ (label o) = true) :
    ¬ ((exact region seen).Holds σ label world ∧
        (exact region seen).Holds σ label (fire world (writer.commit (T := T)))) := by
  rintro ⟨before, after⟩
  have before' : regionOf label world (region σ) = seen := before
  have after' : regionOf label (fire world (writer.commit (T := T))) (region σ) = seen := after
  have inAfter : o ∈ regionOf label (fire world (writer.commit (T := T))) (region σ) := by
    refine Finset.mem_filter.mpr ⟨mem_fire.mpr (Or.inr ?_), inside⟩
    simp [Selection.commit, made]
  have notBefore : o ∉ regionOf label world (region σ) :=
    fun member => absentBefore (Finset.mem_filter.mp member).1
  rw [after', ← before'] at inAfter
  exact notBefore inAfter

end RegionQuery

/-! ## The admission form's query is the exact observation -/

namespace Query

variable {T : Type uT} {S : Type uS} {O : Type uO}

/-- **The admission form's query as a region query**: the exact observation of its region. -/
def toRegion (q : Query T S O) : RegionQuery T S O :=
  RegionQuery.exact q.region q.seen

theorem toRegion_holds_iff (q : Query T S O) {σ : S} {label : O → T} {world : Finset O} :
    q.toRegion.Holds σ label world ↔ (q.atSolution σ).Holds label world :=
  Iff.rfl

theorem toRegion_ask_iff (q : Query T S O) {A : SubstitutionAction T S}
    {problem : EquationStore T} {label : O → T} {world : Finset O} :
    q.toRegion.Ask A problem label world ↔ q.Ask A problem label world :=
  Iff.rfl

theorem toRegion_ignoresWrites_iff (q : Query T S O) {A : SubstitutionAction T S}
    {problem : EquationStore T} {label : O → T} {writer : Selection O} :
    q.toRegion.IgnoresWrites A problem label writer ↔ q.IgnoresWrites A problem label writer :=
  Iff.rfl

end Query

/-! ## A firing's footprint and admission with region queries -/

section Firings

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-- **The footprint of a selection with region queries, at one solution and one world**: the
selection's commit with each query's footprint there. Unlike `commit` it takes the world: a count
fixes no set of occurrences, only the one its fiber holds at that solution and world. -/
def regionCommit (selection : Selection O) (queries : List (RegionQuery T S O)) (σ : S)
    (label : O → T) (world : Finset O) : Commit O T :=
  { (selection.commit (T := T)) with queries := queries.map fun q => q.footprintAt σ label world }

/-- **Exact queries keep their footprint**: where each holds at the solution and world, the region
footprint of the admission form's queries is their `commit`. -/
theorem regionCommit_toRegion {selection : Selection O} {queries : List (Query T S O)} {σ : S}
    {label : O → T} {world : Finset O}
    (holds : ∀ q ∈ queries, (q.atSolution σ).Holds label world) :
    regionCommit selection (queries.map Query.toRegion) σ label world =
      commit selection queries σ := by
  have footprints : (queries.map Query.toRegion).map (fun q => q.footprintAt σ label world) =
      queries.map fun query => query.atSolution σ := by
    rw [List.map_map]
    refine List.map_congr_left fun q member => ?_
    exact RegionQuery.exact_footprintAt (region := q.region) (seen := q.seen) (holds q member)
  unfold regionCommit commit
  rw [footprints]

/-- **Admission with region queries**: the firing is valid, and every query is asked at the firing's
problem against the occurrences present before it. -/
structure RegionValid (A : SubstitutionAction T S) (label : O → T) (rule : RuleInstance T)
    (queries : List (RegionQuery T S O)) (before : Configuration T O) (selection : Selection O) :
    Prop where
  firing : selection.Valid A label rule before
  observations : ∀ q ∈ queries, q.Ask A (selection.problem label rule before) label before.present

/-- **The admission form is the exact case**: admission with queries is admission with their exact
region queries. -/
theorem valid_iff_regionValid {A : SubstitutionAction T S} {label : O → T} {rule : RuleInstance T}
    {queries : List (Query T S O)} {before : Configuration T O} {selection : Selection O} :
    Valid A label rule queries before selection ↔
      RegionValid A label rule (queries.map Query.toRegion) before selection := by
  constructor
  · rintro ⟨firing, observations⟩
    refine ⟨firing, fun r member => ?_⟩
    obtain ⟨q, qmember, rfl⟩ := List.mem_map.mp member
    exact observations q qmember
  · rintro ⟨firing, observations⟩
    exact ⟨firing, fun q member => observations q.toRegion (List.mem_map.mpr ⟨q, member, rfl⟩)⟩

/-- **Without queries, admission is the firing's own admission.** -/
theorem regionValid_nil_iff {A : SubstitutionAction T S} {label : O → T} {rule : RuleInstance T}
    {before : Configuration T O} {selection : Selection O} :
    RegionValid A label rule [] before selection ↔ selection.Valid A label rule before :=
  ⟨fun valid => valid.firing, fun firing => ⟨firing, fun _ member => by cases member⟩⟩

/-- Without queries, the footprint is the selection's commit. -/
theorem regionCommit_nil {selection : Selection O} {σ : S} {label : O → T} {world : Finset O} :
    regionCommit selection ([] : List (RegionQuery T S O)) σ label world = selection.commit (T := T) :=
  rfl

end Firings

/-! ## Controls -/

namespace RegionObservationControls

/-- **The transport law needs its hypothesis.** A commit that makes an occurrence inside the fiber
changes a count: no occurrence before, one after. -/
theorem count_changes_under_a_write_into_its_region :
    (RegionQuery.count (S := Unit) (fun _ (t : Bool) => t) 0).Holds () (fun _ : ℕ => true) ∅ ∧
      ¬ (RegionQuery.count (S := Unit) (fun _ (t : Bool) => t) 0).Holds () (fun _ : ℕ => true)
          (fire ∅ ((⟨[], [], [0]⟩ : Selection ℕ).commit (T := Bool))) := by
  refine ⟨?_, ?_⟩
  · simp [RegionQuery.count_holds_iff, regionOf]
  · simp [RegionQuery.count_holds_iff, regionOf, fire, Selection.commit]

/-- **Exact and count observe one region differently.** At a world whose fiber holds the occurrences
`{0, 1}`, the count of two holds while the exact observation of `{0}` fails: the count fixes no set. -/
theorem count_is_not_one_exact_set :
    (RegionQuery.count (S := Unit) (fun _ (t : Bool) => t) 2).Holds () (fun _ : ℕ => true) {0, 1} ∧
      ¬ (RegionQuery.exact (S := Unit) (fun _ (t : Bool) => t) ({0} : Finset ℕ)).Holds ()
          (fun _ : ℕ => true) {0, 1} := by
  refine ⟨?_, ?_⟩
  · simp [RegionQuery.count_holds_iff, regionOf]
  · simp only [RegionQuery.exact_holds_iff, regionOf]
    decide

/-- **A count does not see a write that keeps its number.** Taking the occurrence `0` of the fiber and
making `1` keeps a count of one, while the exact observation of `{0}` holds before and fails after. So
both orders of such a writer and a counting reader can run although the writer writes into the
reader's fiber: running in both orders implies no write into the region only for exact observations. -/
theorem count_keeps_a_swap_inside_its_region :
    (RegionQuery.count (S := Unit) (fun _ (t : Bool) => t) 1).Holds () (fun _ : ℕ => true) {0} ∧
      (RegionQuery.count (S := Unit) (fun _ (t : Bool) => t) 1).Holds () (fun _ : ℕ => true)
        (fire {0} ((⟨[0], [], [1]⟩ : Selection ℕ).commit (T := Bool))) ∧
      (RegionQuery.exact (S := Unit) (fun _ (t : Bool) => t) ({0} : Finset ℕ)).Holds ()
        (fun _ : ℕ => true) {0} ∧
      ¬ (RegionQuery.exact (S := Unit) (fun _ (t : Bool) => t) ({0} : Finset ℕ)).Holds ()
        (fun _ : ℕ => true) (fire {0} ((⟨[0], [], [1]⟩ : Selection ℕ).commit (T := Bool))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [RegionQuery.count_holds_iff, regionOf]
  · simp [RegionQuery.count_holds_iff, regionOf, fire, Selection.commit]
  · simp [RegionQuery.exact_holds_iff, regionOf]
  · simp only [RegionQuery.exact_holds_iff, regionOf, fire, Selection.commit]
    decide

/-- **An observation that reads the solution is not uniform.** -/
theorem solution_reading_not_uniform :
    ¬ (⟨fun _ _ => true, fun σ _ => σ = true⟩ : RegionQuery Bool Bool ℕ).Uniform := by
  rintro ⟨-, same⟩
  have reading := congrFun (same true false) ∅
  simp at reading

end RegionObservationControls

#print axioms RegionQuery.predicate_holds_iff
#print axioms RegionQuery.holds_fire_of_no_write
#print axioms RegionQuery.ask_fire_iff
#print axioms RegionQuery.footprintAt_holds
#print axioms RegionQuery.exact_footprintAt
#print axioms Query.toRegion_ask_iff
#print axioms Query.toRegion_ignoresWrites_iff
#print axioms regionCommit_toRegion
#print axioms valid_iff_regionValid
#print axioms regionValid_nil_iff
#print axioms regionCommit_nil
#print axioms RegionQuery.rename_holds_iff
#print axioms RegionQuery.exact_supportedBy
#print axioms RegionQuery.count_supportedBy
#print axioms RegionQuery.Uniform.holds_iff
#print axioms RegionQuery.exact_not_both_of_make
#print axioms RegionObservationControls.count_keeps_a_swap_inside_its_region
#print axioms RegionObservationControls.solution_reading_not_uniform
#print axioms RegionObservationControls.count_changes_under_a_write_into_its_region
#print axioms RegionObservationControls.count_is_not_one_exact_set

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PredicateQueryAdmission
