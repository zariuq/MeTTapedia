import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.HEFootprints
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.PeTTaFootprints
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Exactness

/-!
# The race between an add and a complete query

Zar (11/12): "if you have an add as well as a read of 1000 `(double $x)`s, you would have weird race
conditions in theory." With honest footprints the race is a theorem of the step.

A **complete query** (`queryCommit`) reads the occurrences of its region and observes that the
region holds exactly them. An **add** (`Commit.makeOne`) makes one occurrence.

* `add_into_region_race`: an add into the region **conflicts** with the query: the add spoils the
  query's observation (their footprints overlap), the query does not spoil the add, and they do not
  clash. So the step orders them. Query first, the add still runs; add first, the query as it was
  is disabled, and the query asked again reads one occurrence more. Both serializations reach the
  same store, but the query observes two different region contents: two distinct outcomes.
* `write_outside_commutes`, `add_outside_region_commutes`: a write that takes and makes nothing in
  the region is independent of the query: both orders run, reach one store, and the query observes
  the same rows.
* `readRequest_commit`: the complete read request of the ordered store
  (`StoreOperations.readRequest`, PeTTa's `readWithQuery`) is exactly such a complete query.
* `rowStep_spoiled_by_make_inside`, `rowStep_not_spoiled_outside`: a firing of a row-world machine
  (HE's machine included) carries its complete observation; a commit making a row of its region
  spoils it, one making only rows outside does not write into it.

## Instances

* `PeTTaRace`: three rows `(double 1)`, `(double 2)`, `(double 3)` and the query
  `(match &self (double $x) $x)`, at small size. On PeTTa's streaming machine the query reads the
  three rows and answers `1, 2, 3`; after `(add-atom &self (double 4))` it answers `1, 2, 3, 4`.
  The add's request makes a row inside the query's region (`add_double_conflicts`); the request of
  `(add-atom &self (p a))` makes a row outside it (`add_pa_commutes`).
* `HERace`: on the frontier fixture, a new copy of `(= a result)` lies inside the region of HE's
  equation query `a`, while `(= b missed)` and `(p a)` lie outside.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

open MeTTaCalculus.OccurrenceCommits
open HEOnTheStep (Cell)

/-! ## Complete queries and adds -/

section Race

variable {O R : Type} [DecidableEq O]

/-- **A complete query**: it reads the occurrences `seen` and observes that its region holds exactly
them. It takes and makes nothing. -/
def queryCommit (region : R → Bool) (seen : Finset O) : Commit O R :=
  ⟨∅, seen, ∅, [⟨region, seen⟩]⟩

omit [DecidableEq O] in
/-- A complete query of a region is enabled at every store, seeing the region's occurrences. -/
theorem query_enabled (label : O → R) (store : Finset O) (region : R → Bool) :
    Enabled label store (queryCommit region (regionOf label store region)) where
  taken_subset := by simp [queryCommit]
  kept_subset := fun _ member => (mem_regionOf.mp member).1
  apart := by simp [queryCommit]
  fresh := by simp [queryCommit]
  queries_hold := by
    intro read member
    simp only [queryCommit, List.mem_singleton] at member
    subst member
    rfl

omit [DecidableEq O] in
/-- An add of a fresh occurrence is enabled. -/
theorem add_enabled (label : O → R) {store : Finset O} {o : O} (fresh : o ∉ store) :
    Enabled label store (Commit.makeOne o : Commit O R) where
  taken_subset := by simp
  kept_subset := by simp
  apart := by simp
  fresh := Finset.disjoint_singleton_left.mpr fresh
  queries_hold := by simp

theorem fire_query (store : Finset O) (region : R → Bool) (seen : Finset O) :
    fire store (queryCommit region seen) = store := by
  ext o
  simp [mem_fire, queryCommit]

theorem query_not_spoils (label : O → R) (region : R → Bool) (seen : Finset O) (d : Commit O R) :
    ¬ Spoils label (queryCommit region seen) d := by
  rintro (taken | ⟨read, _, x, written, _⟩)
  · exact taken (by simp [queryCommit])
  · simp [queryCommit] at written

omit [DecidableEq O] in
theorem query_no_clash (region : R → Bool) (seen : Finset O) (d : Commit O R) :
    ¬ Clash (queryCommit region seen) d := by
  rintro (taken | made)
  · exact taken (by simp [queryCommit])
  · exact made (by simp [queryCommit])

/-- **Zar's race: an add into the region of a complete query conflicts with it.** The add spoils
the query and not conversely, and they do not clash, so the step orders them. With the query first
the add still runs; with the add first the query as it was cannot run, and asked again it reads the
added occurrence too. Both orders reach the same store, and the query observes two different
contents of its region. -/
theorem add_into_region_race (label : O → R) {store : Finset O} {region : R → Bool} {o : O}
    (fresh : o ∉ store) (inside : region (label o) = true) :
    Spoils label (Commit.makeOne o) (queryCommit region (regionOf label store region)) ∧
      ¬ Spoils label (queryCommit region (regionOf label store region)) (Commit.makeOne o) ∧
      ¬ Clash (queryCommit region (regionOf label store region)) (Commit.makeOne o : Commit O R) ∧
      Enabled label (fire store (queryCommit region (regionOf label store region)))
        (Commit.makeOne o : Commit O R) ∧
      ¬ Enabled label (fire store (Commit.makeOne o : Commit O R))
        (queryCommit region (regionOf label store region)) ∧
      Enabled label (fire store (Commit.makeOne o : Commit O R))
        (queryCommit region (regionOf label (fire store (Commit.makeOne o : Commit O R)) region)) ∧
      regionOf label (fire store (Commit.makeOne o : Commit O R)) region =
        insert o (regionOf label store region) ∧
      o ∉ regionOf label store region ∧
      fire (fire store (queryCommit region (regionOf label store region)))
          (Commit.makeOne o : Commit O R) =
        fire (fire store (Commit.makeOne o : Commit O R))
          (queryCommit region
            (regionOf label (fire store (Commit.makeOne o : Commit O R)) region)) := by
  have spoils : Spoils label (Commit.makeOne o) (queryCommit region (regionOf label store region)) :=
    Or.inr ⟨⟨region, regionOf label store region⟩, by simp [queryCommit], o, by simp, inside⟩
  have orders := spoils_blocks_one_order (query_enabled label store region) (add_enabled label fresh)
    (query_no_clash region _ _) spoils (query_not_spoils label region _ _)
  have grown : regionOf label (fire store (Commit.makeOne o : Commit O R)) region =
      insert o (regionOf label store region) := by
    ext x
    simp only [mem_regionOf, mem_fire, Finset.mem_insert, Commit.makeOne_taken,
      Commit.makeOne_made, Finset.notMem_empty, not_false_eq_true, and_true,
      Finset.mem_singleton]
    constructor
    · rintro ⟨inStore | rfl, inRegion⟩
      · exact Or.inr ⟨inStore, inRegion⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨inStore, inRegion⟩)
      · exact ⟨Or.inr rfl, inside⟩
      · exact ⟨Or.inl inStore, inRegion⟩
  refine ⟨spoils, query_not_spoils label region _ _, query_no_clash region _ _, orders.1, orders.2,
    query_enabled label _ region, grown, fun member => fresh (mem_regionOf.mp member).1, ?_⟩
  rw [fire_query, fire_query]

/-- **A write outside the region commutes with the complete query**: a commit that takes and makes
nothing in the region is independent of the query. -/
theorem write_outside_commutes (label : O → R) {store : Finset O} {region : R → Bool}
    {d : Commit O R} (outside : ∀ x ∈ d.taken ∪ d.made, region (label x) = false) :
    Independent label (queryCommit region (regionOf label store region)) d := by
  refine ⟨query_no_clash region _ d, query_not_spoils label region _ d, ?_⟩
  rintro (taken | ⟨read, member, x, written, inRegion⟩)
  · obtain ⟨x, inTaken, inKept⟩ := Finset.not_disjoint_iff.mp taken
    have := outside x (Finset.mem_union_left _ inTaken)
    rw [(mem_regionOf.mp inKept).2] at this
    cases this
  · simp only [queryCommit, List.mem_singleton] at member
    subst member
    exact Bool.false_ne_true ((outside x written).symm.trans inRegion)

/-- **An add outside the region commutes with the complete query**: both orders run, they reach
one store, and the query observes the same rows in both. -/
theorem add_outside_region_commutes (label : O → R) {store : Finset O} {region : R → Bool} {o : O}
    (fresh : o ∉ store) (outside : region (label o) = false) :
    Independent label (queryCommit region (regionOf label store region))
        (Commit.makeOne o : Commit O R) ∧
      Enabled label (fire store (queryCommit region (regionOf label store region)))
        (Commit.makeOne o : Commit O R) ∧
      Enabled label (fire store (Commit.makeOne o : Commit O R))
        (queryCommit region (regionOf label store region)) ∧
      fire (fire store (queryCommit region (regionOf label store region)))
          (Commit.makeOne o : Commit O R) =
        fire (fire store (Commit.makeOne o : Commit O R))
          (queryCommit region (regionOf label store region)) ∧
      regionOf label (fire store (Commit.makeOne o : Commit O R)) region =
        regionOf label store region := by
  have independent : Independent label (queryCommit region (regionOf label store region))
      (Commit.makeOne o : Commit O R) :=
    write_outside_commutes label fun x written => by
      simp only [Commit.makeOne_taken, Commit.makeOne_made, Finset.empty_union,
        Finset.mem_singleton] at written
      rw [written]
      exact outside
  have both := (independent_iff_both_orders (query_enabled label store region)
    (add_enabled label fresh)).mp independent
  refine ⟨independent, both.1, both.2,
    fire_comm (query_enabled label store region) (add_enabled label fresh), ?_⟩
  apply regionOf_fire_of_no_write
  intro x written
  simp only [Commit.makeOne_taken, Commit.makeOne_made, Finset.empty_union,
    Finset.mem_singleton] at written
  rw [written]
  exact outside

end Race

/-! ## The complete read request is a complete query -/

section Requests

open Mettapedia.Languages.MeTTa.ContextualTransform
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

variable {Obj : Type} {Tm : Obj → Type} {a : Obj} {O : Type} [DecidableEq O]

/-- **The complete read request of the ordered store is a complete query** of its region, at the
rows it was asked over. -/
theorem readRequest_commit (label : O → Tm a) (select : Tm a → Bool) (rows : List O) :
    (StoreOperations.readRequest (a := a) label select rows).commit =
      queryCommit select (regionOf label rows.toFinset select) := by
  have census := StoreOperations.census_holds (a := a) label select rows
  change regionOf label rows.toFinset select =
    (rows.filter fun occurrence => select (label occurrence)).toFinset at census
  rw [census]
  rfl

end Requests

/-! ## Firings of a row-world machine -/

section Firings

variable {X C F A : Type}

/-- **A commit making a row of a firing's region spoils the firing's observation.** -/
theorem rowStep_spoiled_by_make_inside {ρ : X → Bool} {sel : Selection (RowCell X C F A × ℕ)}
    {d : Commit (RowCell X C F A × ℕ) (RowCell X C F A)} {o : RowCell X C F A × ℕ}
    {row : X × ℕ} (made : o ∈ d.made) (labelled : o.1 = Cell.world row) (inside : ρ row.1 = true) :
    Spoils Prod.fst d (PredicateQueryAdmission.commit sel [observation ρ sel] ()) := by
  refine Or.inr ⟨⟨cellRegion ρ, sel.read.toFinset⟩, ?_, o, Finset.mem_union_right _ made, ?_⟩
  · simp [PredicateQueryAdmission.commit, observation, PredicateQueryAdmission.Query.fixed,
      PredicateQueryAdmission.Query.atSolution]
  · rw [labelled]
    exact inside

/-- **A commit writing only rows outside a firing's region, and nothing else of the region, does
not write into its observation.** -/
theorem rowStep_not_spoiled_outside {ρ : X → Bool} {sel : Selection (RowCell X C F A × ℕ)}
    {d : Commit (RowCell X C F A × ℕ) (RowCell X C F A)}
    (outside : ∀ o ∈ d.taken ∪ d.made, cellRegion ρ o.1 = false) :
    ¬ WritesInto Prod.fst d (PredicateQueryAdmission.commit sel [observation ρ sel] ()) := by
  rintro ⟨read, member, o, written, inRegion⟩
  simp only [PredicateQueryAdmission.commit, observation, PredicateQueryAdmission.Query.fixed,
    PredicateQueryAdmission.Query.atSolution, List.map_cons, List.map_nil,
    List.mem_singleton] at member
  subst member
  exact Bool.false_ne_true ((outside o written).symm.trans inRegion)

end Firings

/-! ## Instances -/

namespace PeTTaRace

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings
open Mettapedia.Languages.ProcessCalculi.MORK (matchAtom)
open RunsAsFirings.Controls (p a registry shape)

/-- `(double n)`. -/
def double (n : Int) : Atom := .expression [.symbol "double", .grounded (.int n)]

/-- Three rows of the `(double $x)` shape. -/
def doubles : List Atom := [double 1, double 2, double 3]
def doublesStore : Effects.State := NamedSpaces.Store.new doubles []
def doublesIds : List Row := Row.load 0 doubles

/-- The same store after the add. -/
def doublesAdded : Effects.State := NamedSpaces.Store.new (doubles ++ [double 4]) []

/-- `(match &self (double $x) $x)`. -/
def matchDouble : Atom :=
  .expression [.symbol "match", .symbol "&self", .expression [.symbol "double", .var "x"], .var "x"]

/-- `(add-atom &self (double 4))`. -/
def addDouble : Atom := .expression [.symbol "add-atom", .symbol "&self", double 4]

/-- `(add-atom &self (p a))`. -/
def addPa : Atom := .expression [.symbol "add-atom", .symbol "&self", p a]

/-- The region of the query: rows of the own space that `(double $x)` matches. -/
def doubleRegion : Atom → Bool :=
  selectAt .self fun atom => (matchAtom [] (.expression [.symbol "double", .var "x"]) atom).isSome

/-- The row the add of `(double 4)` makes, and the row the add of `(p a)` makes. -/
def doubleRow : Row := ⟨3, .self, double 4⟩
def paRow : Row := ⟨3, .self, p a⟩

/-- **On PeTTa's machine**: the query reads the three rows and answers `1, 2, 3`; after the add of
`(double 4)` it answers `1, 2, 3, 4`; the two adds each make one row. -/
theorem machine_runs :
    (requests rowSupply registry 30 (Streaming.enter { state := doublesStore } matchDouble)
        doublesIds).map shape =
      [([], [⟨0, .self, double 1⟩, ⟨1, .self, double 2⟩, ⟨2, .self, double 3⟩], [])] ∧
      Streaming.values (Streaming.advance registry 30
        (Streaming.enter { state := doublesStore } matchDouble)) =
          [.grounded (.int 1), .grounded (.int 2), .grounded (.int 3)] ∧
      Streaming.values (Streaming.advance registry 30
        (Streaming.enter { state := doublesAdded } matchDouble)) =
          [.grounded (.int 1), .grounded (.int 2), .grounded (.int 3), .grounded (.int 4)] ∧
      (requests rowSupply registry 30 (Streaming.enter { state := doublesStore } addDouble)
        doublesIds).map shape = [([], [], [doubleRow])] ∧
      (requests rowSupply registry 30 (Streaming.enter { state := doublesStore } addPa)
        doublesIds).map shape = [([], [], [paRow])] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The complete request of the query reads the same three rows as the machine. -/
theorem complete_query_reads :
    (readWithQuery rowSupply doubleRegion doublesIds).selection.read =
      [⟨0, .self, double 1⟩, ⟨1, .self, double 2⟩, ⟨2, .self, double 3⟩] := by
  decide +kernel

theorem doubleRow_fresh : doubleRow ∉ doublesIds.toFinset := by decide
theorem paRow_fresh : paRow ∉ doublesIds.toFinset := by decide
theorem doubleRow_inside : doubleRegion (rowSupply.located doubleRow) = true := by decide +kernel
theorem paRow_outside : doubleRegion (rowSupply.located paRow) = false := by decide +kernel

/-- **Positive control: the add of `(double 4)` conflicts with the query.** Its request's commit
spoils the commit of the query's complete request; with the add first the query as it was is
disabled, and asked again it reads the added row. -/
theorem add_double_conflicts :
    Spoils rowSupply.located (Commit.makeOne doubleRow)
        (readWithQuery rowSupply doubleRegion doublesIds).commit ∧
      ¬ Enabled rowSupply.located
        (fire doublesIds.toFinset (Commit.makeOne doubleRow : Commit Row Atom))
        (readWithQuery rowSupply doubleRegion doublesIds).commit ∧
      Enabled rowSupply.located
        (fire doublesIds.toFinset (readWithQuery rowSupply doubleRegion doublesIds).commit)
        (Commit.makeOne doubleRow : Commit Row Atom) ∧
      doubleRow ∈ regionOf rowSupply.located
        (fire doublesIds.toFinset (Commit.makeOne doubleRow : Commit Row Atom)) doubleRegion ∧
      doubleRow ∉ regionOf rowSupply.located doublesIds.toFinset doubleRegion := by
  have race := add_into_region_race rowSupply.located (region := doubleRegion) doubleRow_fresh
    doubleRow_inside
  rw [readRequest_commit]
  refine ⟨race.1, race.2.2.2.2.1, race.2.2.2.1, ?_, race.2.2.2.2.2.2.2.1⟩
  rw [race.2.2.2.2.2.2.1]
  exact Finset.mem_insert_self _ _

/-- **Negative control: the add of `(p a)` commutes with the query.** Its request's commit is
independent of the query's: both orders run, reach one store, and the query reads the same rows. -/
theorem add_pa_commutes :
    Independent rowSupply.located (readWithQuery rowSupply doubleRegion doublesIds).commit
        (Commit.makeOne paRow : Commit Row Atom) ∧
      fire (fire doublesIds.toFinset (readWithQuery rowSupply doubleRegion doublesIds).commit)
          (Commit.makeOne paRow : Commit Row Atom) =
        fire (fire doublesIds.toFinset (Commit.makeOne paRow : Commit Row Atom))
          (readWithQuery rowSupply doubleRegion doublesIds).commit ∧
      regionOf rowSupply.located (fire doublesIds.toFinset (Commit.makeOne paRow : Commit Row Atom))
          doubleRegion =
        regionOf rowSupply.located doublesIds.toFinset doubleRegion := by
  have commutes := add_outside_region_commutes rowSupply.located (region := doubleRegion)
    paRow_fresh paRow_outside
  rw [readRequest_commit]
  exact ⟨commutes.1, commutes.2.2.2.1, commutes.2.2.2.2⟩

end PeTTaRace

namespace HERace

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Result)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.FrontierControls (rule missedRule)

/-- **HE's equation query on the fixture**: a commit that makes a new copy of `(= a result)`, at
position `4`, spoils every firing whose region is the region of the query `a`; one that makes
`(= b missed)` or `(p a)` there does not write into it. -/
theorem fixture_race (live : List Atom)
    {sel : Selection (RowCell Atom Control Continuation Result × ℕ)}
    {copy : Commit (RowCell Atom Control Continuation Result × ℕ)
      (RowCell Atom Control Continuation Result)}
    {o : RowCell Atom Control Continuation Result × ℕ} (made : o ∈ copy.made)
    (labelled : o.1 = Cell.world (rule, 4))
    (others : Commit (RowCell Atom Control Continuation Result × ℕ)
      (RowCell Atom Control Continuation Result))
    (outside : ∀ x ∈ others.taken ∪ others.made,
      x.1 = Cell.world (missedRule, 4) ∨ x.1 = Cell.world (Controls.pa, 4)) :
    Spoils Prod.fst copy (PredicateQueryAdmission.commit sel
      [observation (eqRegion live (.symbol "a") Mettapedia.Languages.MeTTa.HE.Bindings.empty) sel] ()) ∧
      ¬ WritesInto Prod.fst others (PredicateQueryAdmission.commit sel
        [observation (eqRegion live (.symbol "a") Mettapedia.Languages.MeTTa.HE.Bindings.empty) sel]
          ()) := by
  refine ⟨rowStep_spoiled_by_make_inside made labelled (Controls.rule_inside live), ?_⟩
  apply rowStep_not_spoiled_outside
  intro x written
  rcases outside x written with same | same
  · rw [same]
    exact Controls.missed_outside live
  · rw [same]
    exact Controls.pa_outside live _ _

end HERace

#print axioms query_enabled
#print axioms add_into_region_race
#print axioms write_outside_commutes
#print axioms add_outside_region_commutes
#print axioms readRequest_commit
#print axioms rowStep_spoiled_by_make_inside
#print axioms rowStep_not_spoiled_outside
#print axioms PeTTaRace.machine_runs
#print axioms PeTTaRace.complete_query_reads
#print axioms PeTTaRace.add_double_conflicts
#print axioms PeTTaRace.add_pa_commutes
#print axioms HERace.fixture_race

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
