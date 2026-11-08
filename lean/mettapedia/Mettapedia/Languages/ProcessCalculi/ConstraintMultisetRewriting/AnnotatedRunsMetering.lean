import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsGrades

/-!
# Token metering for guarded firings and firings with predicate queries

`AnnotatedRunsGrades` meters a firing in tokens: the metered firing also takes fuel
occurrences (`Firing.metered`). There, a metered run erases to a run of the plain firings
(`metered_run_erases`) for guard-free firings without predicate queries. Here the same holds for
firings with guards and predicate queries, provided the fuel lies outside what they observe.

## Firings blind to the fuel

A firing is **blind to the fuel atom** (`FuelBlind`) when no pattern scanned by an absence or
count guard matches the fuel atom, and no space observed by its predicate queries contains it, at any
solution. An equation guard scans no occurrence. A guard-free firing without predicate queries
is blind (`fuelBlind_of_plain`).

* **The frame law** (`Firing.valid_frame_blind`, `executable_frame_blind`): adding fuel
  occurrences that no firing makes keeps an admitted blind firing admitted, and adds the fuel to
  its result.
* **Metering only removes runs** (`metered_run_erases_blind`): with fuel labelled by the fuel
  atom and made by no firing, a run of metered blind firings erases to a run of the plain
  firings. `metered_run_erases` is the guard-free case (`metered_run_erases_of_plain`).

## Where blindness fails

A guard or a predicate query that sees the fuel can be enabled by metering: the metered firing
before it consumes the fuel the observation forbids.

* `MeteringControls.guard_sees_fuel`: after a metered worker, a guard "no fuel present" is
  admitted; after the plain worker it is refused.
* `MeteringControls.query_sees_fuel`: the same with a predicate query of the fuel's space.

So without blindness a metered run need not erase to a run: metering can add runs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open MeTTaCalculus.OccurrenceCommits (regionOf mem_regionOf fire mem_fire fire_union_frame)
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-! ## Firings blind to the fuel -/

/-- The pattern whose matches a guard excludes or counts; an equation guard scans no
occurrence. -/
def checkScanned : Check T → Option T
  | .equal _ _ => none
  | .absent pattern => some pattern
  | .count pattern _ => some pattern

/-- **A firing blind to the fuel atom**: no pattern scanned by its guards matches the fuel atom,
and no space observed by its predicate queries contains it, at any solution. -/
structure FuelBlind (A : SubstitutionAction T S) (fuelAtom : T) (f : Firing T S O) : Prop where
  checks : ∀ check ∈ f.rule.checks, ∀ pattern, checkScanned check = some pattern →
    ∀ σ : S, ¬ A.E (A.apply σ pattern) (A.apply σ fuelAtom)
  queries : ∀ query ∈ f.queries, ∀ σ : S, query.region σ fuelAtom = false

omit [DecidableEq O] in
/-- A guard-free firing without predicate queries is blind to every fuel atom. -/
theorem fuelBlind_of_plain (A : SubstitutionAction T S) (fuelAtom : T) {f : Firing T S O}
    (checks : f.rule.checks = []) (queries : f.queries = []) : FuelBlind A fuelAtom f :=
  ⟨fun check member => (by rw [checks] at member; cases member),
    fun query member => (by rw [queries] at member; cases member)⟩

/-! ## The frame law -/

section Frame

variable (A : SubstitutionAction T S) (label : O → T) (fuelAtom : T)

/-- A guard blind to the fuel keeps its verdict when fuel is added to the store. -/
theorem check_holds_frame {σ : S} {store frame : Finset O} {check : Check T}
    (labelled : ∀ o ∈ frame, label o = fuelAtom)
    (blind : ∀ pattern, checkScanned check = some pattern →
      ¬ A.E (A.apply σ pattern) (A.apply σ fuelAtom))
    (holds : check.Holds A σ label store) : check.Holds A σ label (store ∪ frame) := by
  cases check with
  | equal left right => exact holds
  | absent pattern =>
      intro o member
      rcases Finset.mem_union.mp member with inStore | inFrame
      · exact holds o inStore
      · rw [labelled o inFrame]
        exact blind pattern rfl
  | count pattern number =>
      have same : Check.matches A σ label (store ∪ frame) pattern =
          Check.matches A σ label store pattern := by
        ext o
        simp only [Check.matches, Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨inStore | inFrame, matched⟩
          · exact ⟨inStore, matched⟩
          · rw [labelled o inFrame] at matched
            exact absurd matched (blind pattern rfl)
        · rintro ⟨inStore, matched⟩
          exact ⟨Or.inl inStore, matched⟩
      change (Check.matches A σ label (store ∪ frame) pattern).card = number
      rw [same]
      exact holds

/-- A predicate query whose space excludes the fuel keeps its answer when fuel is added. -/
theorem query_holds_frame {σ : S} {store frame : Finset O} {query : PredicateQueryAdmission.Query T S O}
    (labelled : ∀ o ∈ frame, label o = fuelAtom) (blind : query.region σ fuelAtom = false)
    (holds : regionOf label store (query.region σ) = query.seen) :
    regionOf label (store ∪ frame) (query.region σ) = query.seen := by
  rw [← holds]
  ext o
  simp only [mem_regionOf, Finset.mem_union]
  constructor
  · rintro ⟨inStore | inFrame, inRegion⟩
    · exact ⟨inStore, inRegion⟩
    · rw [labelled o inFrame, blind] at inRegion
      cases inRegion
  · rintro ⟨inStore, inRegion⟩
    exact ⟨Or.inl inStore, inRegion⟩

/-- **The frame law for one blind firing.** -/
theorem Firing.valid_frame_blind {f : Firing T S O} {C : Configuration T O} {frame : Finset O}
    (labelled : ∀ o ∈ frame, label o = fuelAtom) (blind : FuelBlind A fuelAtom f)
    (apartMade : Disjoint f.selection.made.toFinset frame) (valid : f.Valid A label C) :
    f.Valid A label ⟨C.equations, C.present ∪ frame⟩ := by
  refine ⟨⟨valid.firing.take_distinct, valid.firing.output_distinct, valid.firing.take_length,
    valid.firing.read_length, valid.firing.outputs,
    valid.firing.occurrences.frame_of_positive rfl apartMade, valid.firing.consistent, ?_⟩, ?_⟩
  · intro check member σ solved
    exact check_holds_frame A label fuelAtom labelled
      (fun pattern scanned => blind.checks check member pattern scanned σ)
      (valid.firing.checks check member σ solved)
  · intro query member σ solved
    exact query_holds_frame label fuelAtom labelled (blind.queries query member σ)
      (valid.observations query member σ solved)

/-- A firing in a larger store adds the frame to its result, when it takes nothing of it. -/
theorem Firing.result_frame (f : Firing T S O) (C : Configuration T O) {frame : Finset O}
    (apartTaken : Disjoint f.selection.taken.toFinset frame) :
    f.result label ⟨C.equations, C.present ∪ frame⟩ =
      ⟨(f.result label C).equations, (f.result label C).present ∪ frame⟩ := by
  change Configuration.mk (f.selection.problem label f.rule ⟨C.equations, C.present ∪ frame⟩)
      (fire (C.present ∪ frame) (f.selection.commit (T := T))) =
    Configuration.mk (f.selection.problem label f.rule C)
      (fire C.present (f.selection.commit (T := T)) ∪ frame)
  rw [fire_union_frame apartTaken]
  rfl

/-- **The frame law for runs of blind firings.** -/
theorem executable_frame_blind : ∀ (w : List (Firing T S O)) (C : Configuration T O)
    (frame : Finset O), (∀ o ∈ frame, label o = fuelAtom) → (∀ f ∈ w, FuelBlind A fuelAtom f) →
    Disjoint C.present frame → (∀ f ∈ w, Disjoint f.selection.made.toFinset frame) →
    Executable A label C w →
      Executable A label ⟨C.equations, C.present ∪ frame⟩ w ∧
        follow label ⟨C.equations, C.present ∪ frame⟩ w =
          ⟨(follow label C w).equations, (follow label C w).present ∪ frame⟩
  | [], _, _, _, _, _, _, executable => ⟨executable, rfl⟩
  | f :: rest, C, frame, labelled, blind, apart, madeApart, ⟨valid, later⟩ => by
      have framed := Firing.valid_frame_blind A label fuelAtom labelled
        (blind f List.mem_cons_self) (madeApart f List.mem_cons_self) valid
      have takenApart : Disjoint f.selection.taken.toFinset frame :=
        Finset.disjoint_of_subset_left valid.firing.occurrences.taken_subset apart
      have resultSame := Firing.result_frame label f C takenApart
      have apartAfter : Disjoint (f.result label C).present frame := by
        change Disjoint (fire C.present (f.selection.commit (T := T))) frame
        refine Finset.disjoint_left.mpr fun o inFire inFrame => ?_
        rcases mem_fire.mp inFire with ⟨present, _⟩ | made
        · exact Finset.disjoint_left.mp apart present inFrame
        · exact Finset.disjoint_left.mp (madeApart f List.mem_cons_self) made inFrame
      obtain ⟨restExecutable, restFollow⟩ := executable_frame_blind rest (f.result label C) frame
        labelled (fun g member => blind g (List.mem_cons_of_mem _ member)) apartAfter
        (fun g member => madeApart g (List.mem_cons_of_mem _ member)) later
      refine ⟨⟨framed, ?_⟩, ?_⟩
      · rw [resultSame]
        exact restExecutable
      · change follow label (f.result label ⟨C.equations, C.present ∪ frame⟩) rest = _
        rw [resultSame]
        exact restFollow

end Frame

/-! ## Metering only removes runs -/

section Metering

variable (A : SubstitutionAction T S) (label : O → T) (fuelAtom : T)

/-- **Metered runs erase to runs, for guarded firings and firings with predicate queries.** With
fuel labelled by the fuel atom, made by no firing of the run, and outside every pattern scanned by
a guard and every space observed by a predicate query of the run's firings, a run of metered firings
erases to a run of the plain firings: the fuel left in the space is invisible to them. -/
theorem metered_run_erases_blind : ∀ (C : Configuration T O) (w : List (Firing T S O × List O)),
    (∀ x ∈ w, FuelBlind A fuelAtom x.1) →
    (∀ x ∈ w, ∀ o ∈ x.2, label o = fuelAtom) →
    (∀ x ∈ w, ∀ y ∈ w, ∀ o ∈ y.2, o ∉ x.1.selection.made) →
    Executable A label C (w.map fun x => x.1.metered fuelAtom x.2) →
      Executable A label C (w.map Prod.fst)
  | C, [], _, _, _, executable => executable
  | C, x :: rest, blind, labelled, unmade, executable => by
      obtain ⟨meteredValid, later⟩ := executable
      obtain ⟨plainValid, same⟩ := metered_erases A label fuelAtom
        (labelled x List.mem_cons_self) meteredValid
      have restRun := metered_run_erases_blind _ rest
        (fun y member => blind y (List.mem_cons_of_mem _ member))
        (fun y member => labelled y (List.mem_cons_of_mem _ member))
        (fun y inY z inZ => unmade y (List.mem_cons_of_mem _ inY) z (List.mem_cons_of_mem _ inZ))
        later
      refine ⟨plainValid, ?_⟩
      have funded := metered_funded A label fuelAtom meteredValid
      have distinct := List.nodup_append.mp meteredValid.firing.take_distinct
      have fuelPresent : x.2.toFinset ⊆ (x.1.result label C).present := by
        intro o member
        have inFuel : o ∈ x.2 := List.mem_toFinset.mp member
        refine mem_fire.mpr (Or.inl ⟨funded.2 o inFuel, ?_⟩)
        intro taken
        exact distinct.2.2 o (by simpa [Selection.commit] using taken) o inFuel rfl
      let reduced : Configuration T O :=
        ⟨(x.1.result label C).equations, (x.1.result label C).present \ x.2.toFinset⟩
      have atReduced : Executable A label reduced (rest.map Prod.fst) :=
        (executable_congr A label _ same).mp restRun
      have framed := (executable_frame_blind A label fuelAtom (rest.map Prod.fst) reduced
        x.2.toFinset
        (fun o member => labelled x List.mem_cons_self o (List.mem_toFinset.mp member))
        (fun g member => by
          obtain ⟨y, inRest, rfl⟩ := List.mem_map.mp member
          exact blind y (List.mem_cons_of_mem _ inRest))
        Finset.sdiff_disjoint
        (fun g member => by
          obtain ⟨y, inRest, rfl⟩ := List.mem_map.mp member
          exact Finset.disjoint_left.mpr fun o made inFuel =>
            unmade y (List.mem_cons_of_mem _ inRest) x List.mem_cons_self o
              (List.mem_toFinset.mp inFuel) (List.mem_toFinset.mp made))
        atReduced).1
      have restored : (⟨reduced.equations, reduced.present ∪ x.2.toFinset⟩ : Configuration T O) =
          x.1.result label C := by
        change Configuration.mk (x.1.result label C).equations
          (((x.1.result label C).present \ x.2.toFinset) ∪ x.2.toFinset) = x.1.result label C
        rw [Finset.sdiff_union_of_subset fuelPresent]
      rw [restored] at framed
      exact framed

/-- **The guard-free case is the existing erasure.** -/
theorem metered_run_erases_of_plain (C : Configuration T O) (w : List (Firing T S O × List O))
    (plain : ∀ x ∈ w, x.1.rule.checks = [] ∧ x.1.queries = [])
    (labelled : ∀ x ∈ w, ∀ o ∈ x.2, label o = fuelAtom)
    (unmade : ∀ x ∈ w, ∀ y ∈ w, ∀ o ∈ y.2, o ∉ x.1.selection.made)
    (executable : Executable A label C (w.map fun x => x.1.metered fuelAtom x.2)) :
    Executable A label C (w.map Prod.fst) :=
  metered_run_erases_blind A label fuelAtom C w
    (fun x member => fuelBlind_of_plain A fuelAtom (plain x member).1 (plain x member).2)
    labelled unmade executable

end Metering

/-! ## Controls -/

namespace MeteringControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (Run observer persistent)

/-- Labels: the token `5`, the output `6`, the fuel `9`; every other occurrence is `2`. -/
def label : Nat → Term signature
  | 5 => .const 5
  | 6 => .const 6
  | 9 => .const 9
  | _ => .const 2

/-- The fuel atom. -/
def fuel : Term signature := .const 9

/-- Takes the token `5` and makes the output `6`. -/
def worker : Run := ⟨⟨[.const 5], [], [], [], [.const 6]⟩, [], ⟨[5], [], [6]⟩⟩

/-- Guards that no fuel is present. -/
def noFuelGuard : Run := ⟨⟨[], [], [], [.absent fuel], []⟩, [], ⟨[], [], []⟩⟩

/-- Guards that no `7` is present: blind to the fuel. -/
def blindGuard : Run := ⟨⟨[], [], [], [.absent (.const 7)], []⟩, [], ⟨[], [], []⟩⟩

/-- The token and one fuel occurrence. -/
def start : Configuration (Term signature) Nat := ⟨[], {5, 9}⟩

theorem worker_problem (σ : Subst signature) :
    A.Models σ (worker.selection.problem label worker.rule start) := by
  intro equation member
  simp only [Selection.problem, Selection.equations, worker, start, List.zipWith_cons_cons,
    List.zipWith_nil_left, List.append_nil, List.nil_append, List.mem_singleton] at member
  subst member
  rfl

theorem metered_worker_problem (σ : Subst signature) :
    A.Models σ ((worker.metered fuel [9]).selection.problem label (worker.metered fuel [9]).rule
      start) := by
  intro equation member
  simp only [Selection.problem, Selection.equations, Firing.metered, worker, start, fuel,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.zipWith_cons_cons,
    List.zipWith_nil_left, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem metered_worker_valid : (worker.metered fuel [9]).Valid A label start :=
  ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨Subst.id signature, metered_worker_problem _⟩,
    by simp [Firing.metered, worker]⟩, by simp [Firing.metered, worker]⟩

theorem worker_valid : worker.Valid A label start :=
  ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨Subst.id signature, worker_problem _⟩,
    by simp [worker]⟩, by simp [worker]⟩

/-- After the metered worker, only its output is left. -/
theorem metered_present : ((worker.metered fuel [9]).result label start).present = {6} := by
  decide

/-- After the plain worker, the fuel is left beside its output. -/
theorem plain_present : (worker.result label start).present = {9, 6} := by
  decide

/-- An absence guard whose pattern is ground holds at a store none of whose labels is it. -/
theorem absent_holds {pattern : Term signature} {store : Finset Nat} (σ : Subst signature)
    (ground : ∀ τ : Subst signature, τ.applyTerm pattern = pattern)
    (apart : ∀ o ∈ store, label o ≠ pattern) :
    (Check.absent pattern).Holds A σ label store := by
  intro o member same
  have labelGround : ∀ n, (σ.applyTerm (label n)) = label n := by
    intro n
    unfold label
    split <;> rfl
  change σ.applyTerm pattern = σ.applyTerm (label o) at same
  rw [ground σ, labelGround] at same
  exact apart o member same.symm

theorem metered_then_guard_runs : Executable A label start [worker.metered fuel [9], noFuelGuard] := by
  refine ⟨metered_worker_valid, ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    ⟨Subst.id signature, ?_⟩, ?_⟩, by simp [noFuelGuard]⟩, ?_⟩
  · intro equation member
    simp only [Selection.problem, Selection.equations, noFuelGuard, List.zipWith_nil_left,
      List.append_nil] at member
    exact metered_worker_problem _ equation member
  · intro check member σ _
    obtain rfl := List.mem_singleton.mp member
    refine absent_holds σ (fun _ => rfl) ?_
    rw [metered_present]
    intro o inStore
    obtain rfl := Finset.mem_singleton.mp inStore
    intro same
    injection same with same
    exact absurd same (by decide)
  · refine ⟨Subst.id signature, ?_⟩
    intro equation member
    simp only [Selection.problem, Selection.equations, noFuelGuard, Firing.result,
      Selection.result, List.zipWith_nil_left, List.append_nil] at member
    exact metered_worker_problem _ equation member

theorem plain_then_guard_refused : ¬ Executable A label start [worker, noFuelGuard] := by
  rintro ⟨-, guardValid, -⟩
  have holds := guardValid.firing.checks _ List.mem_cons_self (Subst.id signature) (by
    intro equation member
    simp only [Selection.problem, Selection.equations, noFuelGuard, Firing.result,
      Selection.result, List.zipWith_nil_left, List.append_nil] at member
    exact worker_problem _ equation member)
  have fuelLeft : 9 ∈ (worker.result label start).present := by
    rw [plain_present]
    decide
  exact holds 9 fuelLeft rfl

/-- **Negative control: a guard that sees the fuel.** After the metered worker the guard "no fuel
present" is admitted; after the plain worker it is refused. The metered run does not erase to a
run: metering added a run. -/
theorem guard_sees_fuel :
    Executable A label start [worker.metered fuel [9], noFuelGuard] ∧
      ¬ Executable A label start [worker, noFuelGuard] ∧
      ¬ FuelBlind A fuel noFuelGuard :=
  ⟨metered_then_guard_runs, plain_then_guard_refused,
    fun blind => blind.checks _ List.mem_cons_self fuel rfl (Subst.id signature) rfl⟩

theorem metered_then_query_runs : Executable A label start [worker.metered fuel [9], observer] := by
  refine ⟨metered_worker_valid, ?_, ?_⟩
  · refine (PredicateQueryAdmission.valid_fixed_iff A label observer.rule [⟨persistent, ∅⟩] _
      observer.selection).mpr ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
        ⟨Subst.id signature, ?_⟩, by simp [observer]⟩, ?_⟩
    · intro equation member
      simp only [Selection.problem, Selection.equations, observer, List.zipWith_nil_left,
        List.append_nil] at member
      exact metered_worker_problem _ equation member
    · intro query member
      obtain rfl := List.mem_singleton.mp member
      decide
  · refine ⟨Subst.id signature, ?_⟩
    intro equation member
    simp only [Selection.problem, Selection.equations, observer, Firing.result,
      Selection.result, List.zipWith_nil_left, List.append_nil] at member
    exact metered_worker_problem _ equation member

theorem plain_then_query_refused : ¬ Executable A label start [worker, observer] := by
  rintro ⟨-, queryValid, -⟩
  have holds := queryValid.observations _ List.mem_cons_self (Subst.id signature) (by
    intro equation member
    simp only [Selection.problem, Selection.equations, observer, Firing.result,
      Selection.result, List.zipWith_nil_left, List.append_nil] at member
    exact worker_problem _ equation member)
  revert holds
  decide

/-- **Negative control: a predicate query that sees the fuel.** After the metered worker the
query "no fuel present" is admitted; after the plain worker it is refused. -/
theorem query_sees_fuel :
    Executable A label start [worker.metered fuel [9], observer] ∧
      ¬ Executable A label start [worker, observer] ∧ ¬ FuelBlind A fuel observer :=
  ⟨metered_then_query_runs, plain_then_query_refused,
    fun blind => absurd (blind.queries _ List.mem_cons_self (Subst.id signature)) (by decide)⟩

theorem blindGuard_blind : FuelBlind A fuel blindGuard := by
  refine ⟨fun check member pattern scanned σ same => ?_, fun query member => by cases member⟩
  obtain rfl := List.mem_singleton.mp member
  obtain rfl := Option.some.inj scanned.symm
  change σ.applyTerm (.const 7) = σ.applyTerm (.const 9) at same
  cases same

theorem metered_then_blind_runs :
    Executable A label start ([(worker, [9]), (blindGuard, [])].map fun x => x.1.metered fuel x.2) := by
  refine ⟨metered_worker_valid, ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    ⟨Subst.id signature, ?_⟩, ?_⟩, by simp [Firing.metered, blindGuard]⟩, ?_⟩
  · intro equation member
    simp only [Selection.problem, Selection.equations, Firing.metered, blindGuard,
      List.map_nil, List.append_nil, List.zipWith_nil_left] at member
    exact metered_worker_problem _ equation member
  · intro check member σ _
    simp only [Firing.metered, blindGuard, List.mem_singleton] at member
    subst member
    refine absent_holds σ (fun _ => rfl) ?_
    rw [metered_present]
    intro o inStore
    obtain rfl := Finset.mem_singleton.mp inStore
    intro same
    injection same with same
    exact absurd same (by decide)
  · refine ⟨Subst.id signature, ?_⟩
    intro equation member
    simp only [Selection.problem, Selection.equations, Firing.metered, blindGuard, Firing.result,
      Selection.result, List.map_nil, List.append_nil, List.zipWith_nil_left] at member
    exact metered_worker_problem _ equation member

/-- **Positive control: a guard blind to the fuel.** The metered run of the worker and a guard on
another atom erases to the run of the plain firings, by the frame law. -/
theorem blind_guard_erases : Executable A label start [worker, blindGuard] :=
  metered_run_erases_blind A label fuel start [(worker, [9]), (blindGuard, [])]
    (fun x member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact fuelBlind_of_plain A fuel rfl rfl
      · exact blindGuard_blind)
    (fun x member o inFuel => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · obtain rfl := List.mem_singleton.mp inFuel
        rfl
      · cases inFuel)
    (fun x inX y inY o inFuel made => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inX inY
      rcases inY with rfl | rfl
      · obtain rfl := List.mem_singleton.mp inFuel
        rcases inX with rfl | rfl <;> simp [worker, blindGuard] at made
      · cases inFuel)
    metered_then_blind_runs

end MeteringControls

#print axioms fuelBlind_of_plain
#print axioms check_holds_frame
#print axioms query_holds_frame
#print axioms Firing.valid_frame_blind
#print axioms Firing.result_frame
#print axioms executable_frame_blind
#print axioms metered_run_erases_blind
#print axioms metered_run_erases_of_plain
#print axioms MeteringControls.guard_sees_fuel
#print axioms MeteringControls.query_sees_fuel
#print axioms MeteringControls.blind_guard_erases

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
