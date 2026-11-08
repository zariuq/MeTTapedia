import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsAnnotations
import Mettapedia.GSLT.Core.GradedSelectionIrreducibility
import Mettapedia.GSLT.Logic.GradedSupport

/-!
# Grades, provenance and metering of the candidate step

## Per-match grades

A graded where-clause in Meredith's design is evaluated once per candidate match and valued in
a commutative semiring. Here a candidate is a firing, and its grade is any function of the
firing, so it may read what the firing matched.

* **A local discipline needs no predicate query.** A discipline that keeps a candidate by a
  test of its own grade (support: a nonzero grade; a fixed threshold) acts on every bag of
  candidates by filtering. Its verdict on a candidate does not change when other candidates
  arrive (`local_stable`), so it needs no complete observation.
* **A comparing discipline needs one.** Maximum selection is not a filter
  (`GradedSelectionIrreducibility.not_pointwiseSelection_of_isMaxSelection`), so an arrival can
  change its verdict on a candidate (`argmax_changed_by_arrival`). With a predicate query of
  the candidate region, the census is the complete bag, and the verdict becomes a test of the
  firing's own data (`argmax_iff_census`). A normalized discipline needs the race total
  likewise (`GradedSelectionIrreducibility.normalizedShare_not_candidatewise`).
* **A charge on the size of a firing's own census is a site charge** (`census_region_card`):
  at an admitted firing the query region has the census's size at every solution of its cut.

## Provenance

The grade of a run is the product of its firings' grades, a site annotation into the
multiplicative monoid of the semiring: in a commutative semiring it respects the interchange
squares (`AnnotatedRuns.siteAccount_factors_static`). The graded denotation of
`GradedSupport` sums over interleavings: on one commuting square of two independent firings
it counts both orders (`Controls.denote_counts_interleavings`), while the square is one causal
history. The two sums agree when the semiring's addition is idempotent
(`Controls.orBool_square`). Meredith's design asks for the sum over causal histories.

## Metering

A metered step pays the price of its firing from a purse and is refused when the purse is
short (`MeteredRun`). Metered runs never fire unfunded (`MeteredRun.funded`), they are exactly
the runs whose total price fits the purse (`meteredRun_iff`), so metering only removes runs,
and funding is a property of the trace (`funded_of_traceEquiv`).

Metering can also be paid in tokens: a metered firing also takes fuel occurrences
(`Firing.metered`). It never fires unfunded (`metered_funded`); it is an admitted plain firing
whose update is the plain update without the fuel (`metered_erases`); and for guard-free
firings without predicate queries a metered run erases to a run of the plain firings
(`metered_run_erases`), so metering only removes runs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open MeTTaCalculus.OccurrenceCommits (regionOf mem_regionOf fire)
open Mettapedia.GSLT.Core (PointwiseSelection IsMaxSelection maxSelector)
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-! ## Local and comparing disciplines -/

section Disciplines

variable {Candidate : Type*}

/-- **A local discipline does not change its verdict when other candidates arrive.** -/
theorem local_stable {select : Multiset Candidate → Multiset Candidate}
    (pointwise : PointwiseSelection select) {candidate : Candidate}
    {bag larger : Multiset Candidate} (member : candidate ∈ bag) (inLarger : candidate ∈ larger) :
    candidate ∈ select bag ↔ candidate ∈ select larger := by
  obtain ⟨keep, filters⟩ := pointwise
  rw [filters, filters, Multiset.mem_filter, Multiset.mem_filter]
  exact ⟨fun kept => ⟨inLarger, kept.2⟩, fun kept => ⟨member, kept.2⟩⟩

/-- **An arrival changes the verdict of maximum selection.** A low candidate alone is
selected, and it is refused once a higher candidate arrives. -/
theorem argmax_changed_by_arrival (weight : Candidate → ℕ) {low high : Candidate}
    (outweighed : weight low < weight high) :
    low ∈ maxSelector weight {low} ∧ low ∉ maxSelector weight {low, high} := by
  classical
  refine ⟨?_, ?_⟩
  · rw [Mettapedia.GSLT.Core.maxSelector_isMaxSelection weight]
    simp
  · rw [Mettapedia.GSLT.Core.maxSelector_isMaxSelection weight]
    rintro ⟨-, maximal⟩
    exact absurd (maximal high (by simp)) (not_le.mpr outweighed)

/-- **Maximum selection is not a local discipline**: it needs every candidate. -/
theorem argmax_not_local (weight : Candidate → ℕ) {low high : Candidate}
    (outweighed : weight low < weight high) : ¬ PointwiseSelection (maxSelector weight) :=
  Mettapedia.GSLT.Core.not_pointwiseSelection_of_isMaxSelection weight outweighed
    (Mettapedia.GSLT.Core.maxSelector_isMaxSelection weight)

end Disciplines

section Census

variable (A : SubstitutionAction T S) (label : O → T)

/-- **With a predicate query of the candidate region, maximum selection is a test of the
firing's own census.** At an admitted firing the census is the region's complete answer, so
an occurrence of the region is maximal there exactly when it is maximal in the census. -/
theorem argmax_iff_census {f : Firing T S O} {C : Configuration T O}
    (valid : f.Valid A label C)
    {query : MeTTaCalculus.OccurrenceCommits.PredicateQuery O T}
    (member : PredicateQueryAdmission.Query.fixed query ∈ f.queries) (weight : T → ℕ) (o : O) :
    (o ∈ regionOf label C.present query.region ∧
        ∀ other ∈ regionOf label C.present query.region, weight (label other) ≤ weight (label o)) ↔
      (o ∈ query.seen ∧ ∀ other ∈ query.seen, weight (label other) ≤ weight (label o)) := by
  obtain ⟨σ, solved⟩ := valid.firing.consistent
  have census : regionOf label C.present query.region = query.seen :=
    valid.observations _ member σ solved
  rw [census]

/-- **A charge on the size of a firing's own census is a site charge.** At an admitted
firing, the region of a predicate query has exactly the census's size at every solution of the
firing's cut, so the charge is a function of the firing. -/
theorem census_region_card {f : Firing T S O} {C : Configuration T O}
    (valid : f.Valid A label C) {query : PredicateQueryAdmission.Query T S O} (member : query ∈ f.queries)
    {σ : S} (solved : A.Models σ (f.selection.problem label f.rule C)) :
    (regionOf label C.present (query.region σ)).card = query.seen.card :=
  (valid.observations query member).card solved

end Census

/-! ## Metering -/

section Metering

variable (A : SubstitutionAction T S) (label : O → T) (price : Firing T S O → ℕ)

/-- **A metered run**: each firing pays its price from the purse, and a firing whose price
exceeds the purse is refused. -/
def MeteredRun : Configuration T O → ℕ → List (Firing T S O) → Prop
  | C, _, [] => A.Consistent C.equations
  | C, purse, f :: rest =>
      f.Valid A label C ∧ price f ≤ purse ∧ MeteredRun (f.result label C) (purse - price f) rest

/-- **Metered runs never fire unfunded**, and they are runs. -/
theorem MeteredRun.funded : ∀ {C : Configuration T O} {purse : ℕ} {w : List (Firing T S O)},
    MeteredRun A label price C purse w →
      Executable A label C w ∧ (w.map price).sum ≤ purse
  | _, _, [], metered => ⟨metered, Nat.zero_le _⟩
  | _, purse, f :: _, ⟨valid, fits, later⟩ => by
      obtain ⟨executable, bounded⟩ := MeteredRun.funded later
      refine ⟨⟨valid, executable⟩, ?_⟩
      simp only [List.map_cons, List.sum_cons]
      omega

/-- **Metering only removes runs**: the metered runs are exactly the runs whose total price
fits the purse. -/
theorem meteredRun_iff : ∀ (C : Configuration T O) (purse : ℕ) (w : List (Firing T S O)),
    MeteredRun A label price C purse w ↔ Executable A label C w ∧ (w.map price).sum ≤ purse
  | C, purse, [] => ⟨fun metered => ⟨metered, Nat.zero_le _⟩, fun both => both.1⟩
  | C, purse, f :: rest => by
      constructor
      · exact MeteredRun.funded A label price
      · rintro ⟨⟨valid, executable⟩, bounded⟩
        simp only [List.map_cons, List.sum_cons] at bounded
        exact ⟨valid, by omega, (meteredRun_iff (f.result label C) (purse - price f) rest).mpr
          ⟨executable, by omega⟩⟩

/-- **Funding is a property of the trace**: trace-equivalent runs have the same total price. -/
theorem funded_of_traceEquiv {w w' : List (Firing T S O)}
    (equivalent : Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv (StaticIndependent label) w w') :
    (w.map price).sum = (w'.map price).sum :=
  ((Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv.perm equivalent).map price).sum_eq

end Metering

/-! ## Metering as tokens -/

section Tokens

variable (A : SubstitutionAction T S) (label : O → T) (fuelAtom : T)

/-- **A metered firing**: it also takes the listed fuel occurrences, with the fuel atom as their
pattern. Its price is the number of fuel occurrences. -/
def Firing.metered (fuel : List O) (f : Firing T S O) : Firing T S O :=
  ⟨{ f.rule with take := f.rule.take ++ fuel.map fun _ => fuelAtom }, f.queries,
    { f.selection with taken := f.selection.taken ++ fuel }⟩

/-- **A metered firing never fires unfunded**: its fuel is present, and distinct. -/
theorem metered_funded {fuel : List O} {f : Firing T S O} {C : Configuration T O}
    (valid : (f.metered fuelAtom fuel).Valid A label C) :
    fuel.Nodup ∧ ∀ o ∈ fuel, o ∈ C.present := by
  have distinct := valid.firing.take_distinct
  refine ⟨(List.nodup_append.mp distinct).2.1, fun o member => ?_⟩
  apply valid.firing.occurrences.taken_subset
  simp [Firing.metered, Selection.commit, member]

omit [DecidableEq O] in
/-- With fuel labelled by the fuel atom, the fuel equations hold in every solution. -/
theorem metered_problem_models {fuel : List O} {f : Firing T S O} {C : Configuration T O}
    (labelled : ∀ o ∈ fuel, label o = fuelAtom)
    (lengths : f.rule.take.length = f.selection.taken.length) (σ : S) :
    A.Models σ ((f.metered fuelAtom fuel).selection.problem label (f.metered fuelAtom fuel).rule C) ↔
      A.Models σ (f.selection.problem label f.rule C) := by
  have fuelSolved : ∀ rest : List O, (∀ o ∈ rest, label o = fuelAtom) →
      A.Models σ (Selection.equations label (rest.map fun _ => fuelAtom) rest) := by
    intro rest
    induction rest with
    | nil => intro _; simp [Selection.equations]
    | cons o rest ih =>
        intro labelledRest
        simp only [Selection.equations, List.map_cons, List.zipWith_cons_cons,
          SubstitutionAction.models_cons] at ih ⊢
        refine ⟨?_, ih (fun other member => labelledRest other (List.mem_cons_of_mem _ member))⟩
        change A.E (A.apply σ fuelAtom) (A.apply σ (label o))
        rw [labelledRest o List.mem_cons_self]
        exact A.equivalence.refl _
  have split : (f.metered fuelAtom fuel).selection.problem label (f.metered fuelAtom fuel).rule C =
      C.equations ++ (Selection.equations label f.rule.take f.selection.taken ++
        Selection.equations label (fuel.map fun _ => fuelAtom) fuel) ++
          Selection.equations label f.rule.read f.selection.read ++ f.rule.tell := by
    simp only [Firing.metered, Selection.problem, Selection.equations]
    rw [List.zipWith_append lengths]
  rw [split]
  simp only [Selection.problem, SubstitutionAction.models_append]
  exact ⟨fun h => ⟨⟨h.1.1.1, h.1.1.2.1⟩, h.1.2⟩ |> fun g => ⟨g, h.2⟩,
    fun h => ⟨⟨⟨h.1.1.1, h.1.1.2, fuelSolved fuel labelled⟩, h.1.2⟩, h.2⟩⟩

/-- **Metering only removes steps**: a metered firing is an admitted plain firing, and its
update is the plain update without the fuel. -/
theorem metered_erases {fuel : List O} {f : Firing T S O} {C : Configuration T O}
    (labelled : ∀ o ∈ fuel, label o = fuelAtom)
    (valid : (f.metered fuelAtom fuel).Valid A label C) :
    f.Valid A label C ∧
      SameUpTo A (f.metered fuelAtom fuel |>.result label C)
        ⟨(f.result label C).equations, (f.result label C).present \ fuel.toFinset⟩ := by
  have distinct := List.nodup_append.mp valid.firing.take_distinct
  have lengths : f.rule.take.length = f.selection.taken.length := by
    have total := valid.firing.take_length
    simp only [Firing.metered, List.length_append, List.length_map] at total
    omega
  have models := metered_problem_models A label fuelAtom (C := C) labelled lengths
  have enabled := valid.firing.occurrences
  refine ⟨⟨⟨distinct.1, valid.firing.output_distinct, lengths, valid.firing.read_length,
    valid.firing.outputs, ⟨?_, enabled.kept_subset, ?_, enabled.fresh, by simp [Selection.commit]⟩,
    ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro o taken
    apply enabled.taken_subset
    simp only [Selection.commit, List.mem_toFinset] at taken
    simp [Firing.metered, Selection.commit, taken]
  · refine Finset.disjoint_of_subset_left ?_ enabled.apart
    intro o taken
    simp only [Selection.commit, List.mem_toFinset] at taken
    simp [Firing.metered, Selection.commit, taken]
  · obtain ⟨σ, solved⟩ := valid.firing.consistent
    exact ⟨σ, (models σ).mp solved⟩
  · intro check member σ solved
    exact valid.firing.checks check member σ ((models σ).mpr solved)
  · intro query member σ solved
    exact valid.observations query member σ ((models σ).mpr solved)
  · intro σ
    exact models σ
  · change fire C.present ((f.metered fuelAtom fuel).selection.commit (T := T)) =
      fire C.present (f.selection.commit (T := T)) \ fuel.toFinset
    ext o
    have freshFuel : o ∈ fuel → o ∉ f.selection.made := fun inFuel inMade =>
      Finset.disjoint_left.mp enabled.fresh (by simpa [Firing.metered, Selection.commit] using inMade)
        (enabled.taken_subset (by simp [Firing.metered, Selection.commit, inFuel]))
    simp only [MeTTaCalculus.OccurrenceCommits.mem_fire, Firing.metered, Selection.commit,
      List.mem_toFinset, List.mem_append, Finset.mem_sdiff]
    constructor
    · rintro (⟨present, notTaken⟩ | made)
      · exact ⟨Or.inl ⟨present, fun taken => notTaken (Or.inl taken)⟩, fun inFuel => notTaken (Or.inr inFuel)⟩
      · exact ⟨Or.inr made, fun inFuel => freshFuel inFuel made⟩
    · rintro ⟨(⟨present, notTaken⟩ | made), notFuel⟩
      · exact Or.inl ⟨present, fun taken => taken.elim notTaken notFuel⟩
      · exact Or.inr made


omit [DecidableEq O] in
theorem ofPlain_plain_of_queries_nil {f : Firing T S O} (empty : f.queries = []) :
    (Firing.ofPlain f.plain : Firing T S O) = f := by
  cases f
  simp_all [Firing.ofPlain, Firing.plain]

/-- **Metered runs erase to runs.** For guard-free firings without predicate queries, with fuel
labelled by the fuel atom and made by no firing, a run of metered firings erases to a run of the
plain firings: the fuel left in the space is invisible to them. Metering only removes runs. -/
theorem metered_run_erases : ∀ (C : Configuration T O) (w : List (Firing T S O × List O)),
    (∀ x ∈ w, x.1.rule.checks = [] ∧ x.1.queries = []) →
    (∀ x ∈ w, ∀ o ∈ x.2, label o = fuelAtom) →
    (∀ x ∈ w, ∀ y ∈ w, ∀ o ∈ y.2, o ∉ x.1.selection.made) →
    Executable A label C (w.map fun x => x.1.metered fuelAtom x.2) →
      Executable A label C (w.map Prod.fst)
  | C, [], _, _, _, executable => executable
  | C, x :: rest, plain, labelled, unmade, executable => by
      obtain ⟨meteredValid, later⟩ := executable
      obtain ⟨plainValid, same⟩ := metered_erases A label fuelAtom
        (labelled x List.mem_cons_self) meteredValid
      have restPlain : ∀ y ∈ rest, y.1.rule.checks = [] ∧ y.1.queries = [] :=
        fun y member => plain y (List.mem_cons_of_mem _ member)
      have restRun := metered_run_erases _ rest restPlain
        (fun y member => labelled y (List.mem_cons_of_mem _ member))
        (fun y inY z inZ => unmade y (List.mem_cons_of_mem _ inY) z (List.mem_cons_of_mem _ inZ))
        later
      refine ⟨plainValid, ?_⟩
      have funded := metered_funded A label fuelAtom meteredValid
      have distinct := List.nodup_append.mp meteredValid.firing.take_distinct
      have fuelPresent : x.2.toFinset ⊆ (x.1.result label C).present := by
        intro o member
        have inFuel : o ∈ x.2 := List.mem_toFinset.mp member
        refine MeTTaCalculus.OccurrenceCommits.mem_fire.mpr (Or.inl ⟨funded.2 o inFuel, ?_⟩)
        intro taken
        exact distinct.2.2 o (by simpa [Selection.commit] using taken) o inFuel rfl
      let reduced : Configuration T O :=
        ⟨(x.1.result label C).equations, (x.1.result label C).present \ x.2.toFinset⟩
      have atReduced : Executable A label reduced (rest.map Prod.fst) :=
        (executable_congr A label _ same).mp restRun
      have asPlain : rest.map Prod.fst = (rest.map fun y => y.1.plain).map (Firing.ofPlain (S := S)) := by
        rw [List.map_map]
        refine List.map_congr_left fun y member => ?_
        exact (ofPlain_plain_of_queries_nil (plain y (List.mem_cons_of_mem _ member)).2).symm
      rw [asPlain] at atReduced ⊢
      rw [executable_ofPlain_iff] at atReduced ⊢
      have framed := (GuardFreeProcessOrders.executable_frame A label (rest.map fun y => y.1.plain)
        reduced x.2.toFinset
        (fun y member => by
          obtain ⟨z, inRest, rfl⟩ := List.mem_map.mp member
          exact (plain z (List.mem_cons_of_mem _ inRest)).1)
        Finset.sdiff_disjoint
        (fun y member => by
          obtain ⟨z, inRest, rfl⟩ := List.mem_map.mp member
          exact Finset.disjoint_left.mpr fun o made inFuel =>
            unmade z (List.mem_cons_of_mem _ inRest) x List.mem_cons_self o
              (List.mem_toFinset.mp inFuel) (List.mem_toFinset.mp made))
        atReduced).1
      have restored : (⟨reduced.equations, reduced.present ∪ x.2.toFinset⟩ : Configuration T O) =
          x.1.result label C := by
        change Configuration.mk (x.1.result label C).equations
          (((x.1.result label C).present \ x.2.toFinset) ∪ x.2.toFinset) = x.1.result label C
        rw [Finset.sdiff_union_of_subset fuelPresent]
      rw [restored] at framed
      exact framed

end Tokens

/-! ## Controls -/

namespace GradeControls

open Mettapedia.GSLT.GradedSupport
open Mettapedia.GSLT.GradedSupport.Control

/-- One commuting square of two independent firings with grades `a` and `b`: either may go
first, and the other follows. -/
def square {V : Type*} [Zero V] (a b : V) : Node → List (Node × V)
  | .source => [(.left, a), (.right, b)]
  | .left => [(.sink, b)]
  | .right => [(.sink, a)]
  | _ => []

/-- **The interleaving sum counts both orders of one causal history.** Over the natural
numbers, with unit grades, the denotation of the sink is `2`. -/
theorem denote_counts_interleavings : denote (square (1 : ℕ) 1) 2 .source .sink = 2 := by
  decide

/-- Over the disjunctive Booleans the two orders coincide: addition is idempotent. -/
theorem orBool_square : denote (square (1 : OrBool) 1) 2 .source .sink = 1 := by
  decide

open AnnotatedRuns.Controls (label Run taker reader start taker_valid)
open ConstraintMultisetRewriting.Controls (signature A)

/-- **Positive control: a local discipline.** Keeping candidates of nonzero grade is a filter. -/
theorem support_is_local (grade : Run → ℕ) :
    PointwiseSelection (fun bag : Multiset Run => bag.filter fun f => grade f ≠ 0) :=
  ⟨fun f => decide (grade f ≠ 0), fun bag => by simp⟩

/-- **Negative control: maximum selection between the taker and the reader.** Graded by how many
occurrences they read, the taker alone is maximal, and the reader's arrival refuses it. -/
theorem argmax_needs_both :
    taker ∈ maxSelector (fun f : Run => f.selection.read.length) {taker} ∧
      taker ∉ maxSelector (fun f : Run => f.selection.read.length) {taker, reader} :=
  argmax_changed_by_arrival _ (by simp [taker, reader])

/-- **Positive control: a metered run.** With a purse of two and unit prices, the taker and
the reader both fire; with a purse of one the pair is refused. -/
theorem metered_pair :
    MeteredRun A label (fun _ => 1) start 2 [taker, reader] ∧
      ¬ MeteredRun A label (fun _ => 1) start 1 [taker, reader] := by
  refine ⟨(meteredRun_iff A label _ start 2 _).mpr
      ⟨AnnotatedRuns.Controls.taker_then_reader, by decide⟩,
    fun metered => ?_⟩
  have bounded := (MeteredRun.funded A label _ metered).2
  simp at bounded

/-- A space with one fuel occurrence, `9`, labelled by the fuel atom `9`. -/
def fueled : Configuration (Mettapedia.Logic.LP.Term signature) Nat := ⟨[], {0, 1, 9}⟩

/-- **Positive control: metering as tokens.** The taker metered by the fuel occurrence `9` fires
in the fueled space and erases to the plain taker. -/
theorem metered_taker_fires :
    (taker.metered (.const 9) [9]).Valid A label fueled ∧ taker.Valid A label fueled := by
  have valid : (taker.metered (.const 9) [9]).Valid A label fueled := by
    refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨AnnotatedRuns.Controls.zeros, ?_⟩,
      by simp [Firing.metered, taker]⟩, by simp [Firing.metered, taker]⟩
    intro equation member
    have cases : equation = (ConstraintMultisetRewriting.Controls.f (.const 0), label 0) ∨
        equation = (.const 9, label 9) := by
      simpa [Selection.problem, Selection.equations, Firing.metered, fueled, taker] using member
    rcases cases with rfl | rfl <;> rfl
  exact ⟨valid, (metered_erases A label (.const 9) (fun o member => by
    obtain rfl := List.mem_singleton.mp member; rfl) valid).1⟩

/-- **Negative control: never unfunded.** Without the fuel occurrence the metered taker is
refused, though the plain taker fires. -/
theorem metered_taker_unfunded :
    ¬ (taker.metered (.const 9) [9]).Valid A label start ∧ taker.Valid A label start := by
  refine ⟨fun valid => ?_, taker_valid⟩
  have present := (metered_funded A label (.const 9) valid).2 9 (by simp)
  revert present
  decide

end GradeControls


#print axioms local_stable
#print axioms argmax_changed_by_arrival
#print axioms argmax_not_local
#print axioms argmax_iff_census
#print axioms census_region_card
#print axioms MeteredRun.funded
#print axioms meteredRun_iff
#print axioms funded_of_traceEquiv
#print axioms metered_funded
#print axioms metered_problem_models
#print axioms metered_erases
#print axioms metered_run_erases
#print axioms GradeControls.denote_counts_interleavings
#print axioms GradeControls.orBool_square
#print axioms GradeControls.support_is_local
#print axioms GradeControls.argmax_needs_both
#print axioms GradeControls.metered_pair
#print axioms GradeControls.metered_taker_fires
#print axioms GradeControls.metered_taker_unfunded

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
