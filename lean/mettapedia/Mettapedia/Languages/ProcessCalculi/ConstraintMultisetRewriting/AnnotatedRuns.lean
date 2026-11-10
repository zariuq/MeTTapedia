import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PredicateQueryAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardFreeProcessOrders
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Traces
import Mettapedia.GSLT.Distinction.CausalGluing
import Mettapedia.GSLT.Causality.HistoryMonad
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface

/-!
# Runs of the candidate step: the base of every annotation

A firing of the candidate step is a rule instance, its predicate queries and its
selected occurrences. Its admission is `PredicateQueryAdmission.Valid`: the queries'
census, the complete answer table, must hold at the firing's cut. Its update is
the existing `Selection.result`. A run is a word of firings, each admitted where
its predecessors left the configuration.

## The first-order step is the one-frame instance of the interface

The candidate step is stated once in `Interface.Step`, over a category of frames whose canonical
instance is the contextual one. This file is its **one-frame case** (`firstOrder`): the frame is
the one object of `Interface.Frames.ofSubstitution A`, a firing moves along the identity, its
information is `Selection.problem`, and its admission is `Firing.Valid`, which is the interface's
characterization (`firstOrder_admits_iff`). The executable words are the runs of that instance
(`executable_iff_run`, `follow_eq_last`), so every theorem here is a theorem about the one-frame
case of the interface. The static independence below is a property of a fixed alphabet of
firings and belongs to this one-frame case.

## Renaming occurrence identities

A bijection of occurrence identities that keeps their labels renames firings and configurations.
Admission, the update and runs are equivariant (`Firing.valid_rename`, `Firing.result_rename`,
`executable_rename`, `follow_rename`): fresh identities are interchangeable.

## The base category

Admission depends on a configuration only through the solutions of its
equations and its present occurrences (`GuardFreeProcessOrders.valid_congr`;
`Firing.valid_congr` adds the predicate queries). Configurations are therefore
read up to `SameUpTo`. On these classes the candidate step is a GSLT whose events
are the firings (`theory`, `presentation`). Its runs are the arrows of the free
category `OccurrenceHistory.OccurrenceCat` on that presentation, and they are
histories of the writer theory of `HistoryMonad` (`eventLabels`,
`run_is_history`). Annotations of runs are functors out of this category; see
`AnnotatedRunsAnnotations`.

## Two independences, not one

* **Static.** For firings without checks whose query regions do not depend on
  the solution, the relation `StaticIndependent` is decided by the firings
  alone: at every solution, their footprints, queries included, are trace
  independent in the ground layer (`OccurrenceCommits.TraceIndependent`).
  Equations are unrestricted and may share variables. A firing is independent
  of itself exactly when it writes nothing (`independent_self_iff`); removing
  these pairs makes the relation irreflexive and generates the same equivalence
  (`traceEquiv_irreflexive_iff`). An executed independent pair runs in the other
  order to the same class (`swap_valid`), so **trace-equivalent runs reach the
  same configuration** (`traceEquiv_executable`). Each such swap is a generated
  2-cell of the existing Mazurkiewicz equivalence (`tile`, `swap_is_diamond`).
* **The finest tracing.** Without guards and predicate queries, runs of the same firings with
  fresh, distinct footprints are trace equivalent (`same_firings_traceEquiv`): the trace of such
  a run is its set of firings with their occurrence identities, ordered by what they make and
  use. With `CausalGluing.TraceEquiv.perm` this identifies its traces with its processes.
* **Contextual.** Two firings admitted at one configuration need their joint
  equations to be consistent before both can fire; that is a property of the
  configuration, never of the firings (`AnnotatedRunsRounds`).

## Where the static relation stops

* A guard can read what another firing tells. Footprints can be trace
  independent while one order runs and the other is refused
  (`Controls.told_check_one_order`).
* A predicate query has a predicate-read dependency on its region: it conflicts
  with every writer into that region (`Controls.census_writer_one_order`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open MeTTaCalculus.OccurrenceCommits (Commit TraceIndependent regionOf regionOf_fire_of_no_write fire)
open GuardFreeProcessOrders (SameUpTo NoCause NoAsym NoReuse problem_eq equivalent_append)
open Mettapedia.GSLT.Distinction.CausalGluing (TraceEquiv Swap)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

omit [DecidableEq O] in
theorem sameUpTo_symm (A : SubstitutionAction T S) {C D : Configuration T O}
    (same : SameUpTo A C D) : SameUpTo A D C :=
  ⟨fun σ => (same.1 σ).symm, same.2.symm⟩

/-- One firing of the candidate step: a rule instance, its predicate queries and the selected
occurrences. -/
structure Firing (T : Type uT) (S : Type uS) (O : Type uO) where
  rule : RuleInstance T
  queries : List (PredicateQueryAdmission.Query T S O)
  selection : Selection O

namespace Firing

/-- The firing without its predicate queries, as the existing schedules write it. -/
def plain (f : Firing T S O) : ConditionalSchedule.Firing T O := (f.rule, f.selection)

/-- A firing without predicate queries. -/
def ofPlain (x : ConditionalSchedule.Firing T O) : Firing T S O := ⟨x.1, [], x.2⟩

variable (A : SubstitutionAction T S) (label : O → T)

/-- Admission is the existing census admission: the queries must hold at the firing's cut. -/
def Valid (f : Firing T S O) (C : Configuration T O) : Prop :=
  PredicateQueryAdmission.Valid A label f.rule f.queries C f.selection

/-- The update is the existing occurrence operation; the queries add none. -/
def result (f : Firing T S O) (C : Configuration T O) : Configuration T O :=
  f.selection.result label f.rule C

/-- The ground footprint of a firing at one solution, its queries included. -/
def footprintAt (f : Firing T S O) (σ : S) : Commit O T :=
  PredicateQueryAdmission.commit f.selection f.queries σ

/-- Without queries, admission is the plain admission (`PredicateQueryAdmission.valid_empty_iff`). -/
theorem valid_ofPlain_iff (x : ConditionalSchedule.Firing T O) (C : Configuration T O) :
    (ofPlain x : Firing T S O).Valid A label C ↔ x.2.Valid A label x.1 C :=
  PredicateQueryAdmission.valid_empty_iff A label x.1 C x.2

/-- Admission with queries depends only on the solutions and the present occurrences. -/
theorem valid_congr {f : Firing T S O} {C D : Configuration T O} (same : SameUpTo A C D) :
    f.Valid A label C ↔ f.Valid A label D := by
  have problems : A.Equivalent (f.selection.problem label f.rule C)
      (f.selection.problem label f.rule D) := by
    rw [problem_eq, problem_eq]
    exact equivalent_append A same.1 _
  constructor
  · rintro ⟨firing, observations⟩
    refine ⟨(GuardFreeProcessOrders.valid_congr A label same).mp firing, ?_⟩
    intro query member σ solved
    change regionOf label D.present (query.region σ) = query.seen
    rw [← same.2]
    exact observations query member σ ((problems σ).mpr solved)
  · rintro ⟨firing, observations⟩
    refine ⟨(GuardFreeProcessOrders.valid_congr A label same).mpr firing, ?_⟩
    intro query member σ solved
    change regionOf label C.present (query.region σ) = query.seen
    rw [same.2]
    exact observations query member σ ((problems σ).mp solved)

theorem result_congr (f : Firing T S O) {C D : Configuration T O} (same : SameUpTo A C D) :
    SameUpTo A (f.result label C) (f.result label D) :=
  GuardFreeProcessOrders.result_congr A label f.rule f.selection same

end Firing

section Runs

variable (A : SubstitutionAction T S) (label : O → T)

/-- A run: each firing admitted at the configuration its predecessors left. As for
`ConditionalSchedule.Executable`, the empty run asks for a consistent store. -/
def Executable : Configuration T O → List (Firing T S O) → Prop
  | C, [] => A.Consistent C.equations
  | C, f :: rest => f.Valid A label C ∧ Executable (f.result label C) rest

/-- The configuration a run leaves. -/
def follow : Configuration T O → List (Firing T S O) → Configuration T O
  | C, [] => C
  | C, f :: rest => follow (f.result label C) rest

theorem follow_eq_plain : ∀ (C : Configuration T O) (w : List (Firing T S O)),
    follow label C w = ConditionalSchedule.follow label C (w.map Firing.plain)
  | _, [] => rfl
  | C, f :: rest => follow_eq_plain (f.result label C) rest

/-- A run with predicate queries is a run of the existing schedules. -/
theorem Executable.plain : ∀ {C : Configuration T O} {w : List (Firing T S O)},
    Executable A label C w → ConditionalSchedule.Executable A label C (w.map Firing.plain)
  | _, [], executable => executable
  | _, _ :: _, executable => ⟨executable.1.firing, Executable.plain executable.2⟩

/-- **Runs without predicate queries are exactly the existing schedules.** -/
theorem executable_ofPlain_iff : ∀ (C : Configuration T O) (w : List (ConditionalSchedule.Firing T O)),
    Executable A label C (w.map (Firing.ofPlain (S := S))) ↔ ConditionalSchedule.Executable A label C w
  | _, [] => Iff.rfl
  | C, x :: rest => by
      change (_ ∧ _) ↔ (_ ∧ _)
      rw [Firing.valid_ofPlain_iff, executable_ofPlain_iff]
      rfl

theorem executable_congr : ∀ (w : List (Firing T S O)) {C D : Configuration T O},
    SameUpTo A C D → (Executable A label C w ↔ Executable A label D w)
  | [], _, _, same => SubstitutionAction.equivalent_consistent A same.1
  | f :: rest, _, _, same => by
      change (_ ∧ _) ↔ (_ ∧ _)
      rw [Firing.valid_congr A label same, executable_congr rest (f.result_congr A label same)]

theorem follow_congr (w : List (Firing T S O)) {C D : Configuration T O} (same : SameUpTo A C D) :
    SameUpTo A (follow label C w) (follow label D w) := by
  rw [follow_eq_plain, follow_eq_plain]
  exact GuardFreeProcessOrders.follow_congr A label _ same

end Runs

/-! ## The one-frame instance of the interface -/

section OneFrame

variable (A : SubstitutionAction T S) (label : O → T)

open Interface (Frames)

/-- **The first-order step as the one-frame instance of the candidate step's interface.** Its
frame is the one object of `Frames.ofSubstitution A`, its firings move along the identity, and its
information is `Selection.problem`. -/
def firstOrder :
    Interface.Step.Standard (Frames.ofSubstitution A) O (Configuration T O) (fun _ => Firing T S O) where
  frame _ := PUnit.unit
  knowledge C := C.equations
  present C := C.present
  selection f := f.selection
  target _ := PUnit.unit
  extension _ := A.identity
  information {C} f := f.selection.problem label f.rule C
  transported := by
    intro C f e member
    show (A.apply A.identity e.1, A.apply A.identity e.2) ∈ f.selection.problem label f.rule C
    rw [A.apply_identity, A.apply_identity]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member))
  Shapes f := f.selection.taken.Nodup ∧ f.selection.made.Nodup ∧
    f.rule.take.length = f.selection.taken.length ∧ f.rule.read.length = f.selection.read.length ∧
    f.selection.made.map label = f.rule.produce
  Holds {C} f _ σ := (∀ check ∈ f.rule.checks, check.Holds A σ label C.present) ∧
    ∀ query ∈ f.queries, (query.atSolution σ).Holds label C.present
  Admits {C} f := f.Valid A label C
  admits_iff := by
    intro C f
    constructor
    · rintro ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs, occurrences,
        consistent, checks⟩, observations⟩
      refine ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs⟩,
        ⟨occurrences.taken_subset, occurrences.kept_subset, occurrences.apart, occurrences.fresh, ?_⟩,
        (Frames.ofSubstitution_solvable_iff A _).mpr consistent, ?_⟩
      · intro query member
        simp [Selection.commit] at member
      · intro _ σ solved
        exact ⟨fun check present => checks check present σ solved,
          fun query present => observations query present σ solved⟩
    · rintro ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs⟩, occurrences,
        solvable, asks⟩
      refine ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs,
        ⟨occurrences.taken_subset, occurrences.kept_subset, occurrences.apart, occurrences.fresh, ?_⟩,
        (Frames.ofSubstitution_solvable_iff A _).mp solvable, ?_⟩, ?_⟩
      · intro query member
        simp [Selection.commit] at member
      · intro check present σ solved
        exact (asks PUnit.unit σ solved).1 check present
      · intro query present σ solved
        exact (asks PUnit.unit σ solved).2 query present
  preparedResult {C} f _ := f.result label C
  present_preparedResult _ _ := rfl
  preparedSettle _ _ := A.identity
  knowledge_preparedResult {C} f _ := (Frames.applyStore_id (X := Frames.ofSubstitution A)
    (f.selection.problem label f.rule C)).symm

/-- Admission of the one-frame instance is `Firing.Valid`: the interface's characterization. -/
theorem firstOrder_admits_iff (C : Configuration T O) (f : Firing T S O) :
    f.Valid A label C ↔ (firstOrder A label).Shapes (s := C) f ∧
      MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : O => ()) C.present (f.selection.commit (T := Unit)) ∧
      (Frames.ofSubstitution A).Solvable (a := PUnit.unit) (f.selection.problem label f.rule C) ∧
      (Frames.ofSubstitution A).Entails (a := PUnit.unit) (f.selection.problem label f.rule C)
        ((firstOrder A label).Holds (s := C) f) :=
  (firstOrder A label).admits_iff (s := C) f

/-- **The executable words are the runs of the one-frame instance** that end in consistent
knowledge. -/
theorem executable_iff_run : ∀ (C : Configuration T O) (w : List (Firing T S O)),
    Executable A label C w ↔ ∃ r : (firstOrder A label).Run C,
      r.word.map Sigma.snd = w ∧ A.Consistent r.last.equations
  | C, [] => by
      constructor
      · intro consistent
        exact ⟨.nil C, rfl, consistent⟩
      · rintro ⟨r, word, consistent⟩
        cases r with
        | nil => exact consistent
        | cons f admitted rest => simp [Interface.Step.Run.word] at word
  | C, f :: rest => by
      constructor
      · rintro ⟨valid, later⟩
        obtain ⟨r, word, consistent⟩ := (executable_iff_run (f.result label C) rest).mp later
        refine ⟨.cons f valid r, ?_, consistent⟩
        show List.map Sigma.snd (⟨C, f⟩ :: r.word) = f :: rest
        rw [List.map_cons, word]
      · rintro ⟨r, word, consistent⟩
        cases r with
        | nil => simp [Interface.Step.Run.word] at word
        | cons g admitted r =>
            simp only [Interface.Step.Run.word, List.map_cons, List.cons.injEq] at word
            obtain ⟨rfl, word⟩ := word
            exact ⟨admitted, (executable_iff_run (g.result label C) rest).mpr ⟨r, word, consistent⟩⟩

/-- A run of the one-frame instance ends where its word leaves the configuration. -/
theorem follow_eq_last : ∀ {C : Configuration T O} (r : (firstOrder A label).Run C),
    follow label C (r.word.map Sigma.snd) = r.last
  | _, .nil _ => rfl
  | _, .cons _ _ r => follow_eq_last r

end OneFrame

/-! ## Renaming occurrence identities

A bijection of occurrence identities that keeps their labels renames a selection, the identities
the predicate queries of a firing saw, and the present occurrences of a configuration; knowledge
never mentions identities. Admission and the update are equivariant (`Firing.valid_rename`,
`Firing.result_rename`), and so are runs (`executable_rename`, `follow_rename`). -/

section Renaming

variable (π : O ≃ O)

/-- Rename the occurrences a selection takes, reads and makes. -/
def renameSelection (selection : Selection O) : Selection O :=
  ⟨selection.taken.map π, selection.read.map π, selection.made.map π⟩

/-- Rename the identities a predicate query saw. -/
def renameQuery (query : PredicateQueryAdmission.Query T S O) : PredicateQueryAdmission.Query T S O :=
  ⟨query.region, query.seen.map π.toEmbedding⟩

/-- Rename a firing: its selection and its queries' sightings. -/
def Firing.rename (f : Firing T S O) : Firing T S O :=
  ⟨f.rule, f.queries.map (renameQuery π), renameSelection π f.selection⟩

/-- Rename the present occurrences of a configuration. -/
def renameConfiguration (C : Configuration T O) : Configuration T O :=
  ⟨C.equations, C.present.map π.toEmbedding⟩

variable {label : O → T} {π}

omit [DecidableEq O] in
theorem equations_rename (keeps : ∀ o, label (π o) = label o) (patterns : List T)
    (selected : List O) :
    Selection.equations label patterns (selected.map π) = Selection.equations label patterns selected := by
  simp only [Selection.equations, List.zipWith_map_right, keeps]

omit [DecidableEq O] in
theorem problem_rename (keeps : ∀ o, label (π o) = label o) (selection : Selection O)
    (rule : RuleInstance T) (C : Configuration T O) :
    (renameSelection π selection).problem label rule (renameConfiguration π C) =
      selection.problem label rule C := by
  simp only [Selection.problem, renameSelection, renameConfiguration, equations_rename keeps]

theorem toFinset_rename (l : List O) : (l.map π).toFinset = l.toFinset.map π.toEmbedding := by
  ext o
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_map, Equiv.coe_toEmbedding]

theorem fire_rename (present : Finset O) (selection : Selection O) :
    fire (present.map π.toEmbedding) ((renameSelection π selection).commit (T := T)) =
      (fire present (selection.commit (T := T))).map π.toEmbedding := by
  simp only [fire, Selection.commit, renameSelection, toFinset_rename, Finset.map_sdiff,
    Finset.map_union]

theorem enabled_rename (present : Finset O) (selection : Selection O) :
    MeTTaCalculus.OccurrenceCommits.Enabled label (present.map π.toEmbedding)
        ((renameSelection π selection).commit (T := T)) ↔
      MeTTaCalculus.OccurrenceCommits.Enabled label present (selection.commit (T := T)) := by
  constructor
  · rintro ⟨taken, kept, apart, fresh, -⟩
    simp only [Selection.commit, renameSelection, toFinset_rename, Finset.map_subset_map,
      Finset.disjoint_map] at taken kept apart fresh
    exact ⟨taken, kept, apart, fresh, by simp [Selection.commit]⟩
  · rintro ⟨taken, kept, apart, fresh, -⟩
    refine ⟨?_, ?_, ?_, ?_, by simp [Selection.commit]⟩ <;>
      simp only [Selection.commit, renameSelection, toFinset_rename, Finset.map_subset_map,
        Finset.disjoint_map] <;> assumption

omit [DecidableEq O] in
theorem region_rename (A : SubstitutionAction T S) (keeps : ∀ o, label (π o) = label o) (σ : S)
    (present : Finset O) (pattern : T) :
    Check.matches A σ label (present.map π.toEmbedding) pattern =
      (Check.matches A σ label present pattern).map π.toEmbedding := by
  classical
  ext o
  simp only [Check.matches, Finset.mem_filter, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨⟨a, member, rfl⟩, matched⟩
    exact ⟨a, ⟨member, by rwa [keeps] at matched⟩, rfl⟩
  · rintro ⟨a, ⟨member, matched⟩, rfl⟩
    exact ⟨⟨a, member, rfl⟩, by rwa [keeps]⟩

omit [DecidableEq O] in
theorem holds_rename (A : SubstitutionAction T S) (keeps : ∀ o, label (π o) = label o) (σ : S)
    (present : Finset O) (check : Check T) :
    check.Holds A σ label (present.map π.toEmbedding) ↔ check.Holds A σ label present := by
  cases check with
  | equal left right => exact Iff.rfl
  | absent pattern =>
      constructor
      · intro absent o member matched
        apply absent _ (Finset.mem_map_of_mem π.toEmbedding member)
        show A.E (A.apply σ pattern) (A.apply σ (label (π o)))
        rw [keeps]
        exact matched
      · intro absent o member matched
        obtain ⟨a, inside, rfl⟩ := Finset.mem_map.mp member
        change A.E (A.apply σ pattern) (A.apply σ (label (π a))) at matched
        rw [keeps] at matched
        exact absent a inside matched
  | count pattern number =>
      show (Check.matches A σ label (present.map π.toEmbedding) pattern).card = number ↔
        (Check.matches A σ label present pattern).card = number
      rw [region_rename A keeps, Finset.card_map]

omit [DecidableEq O] in
theorem regionOf_rename (keeps : ∀ o, label (π o) = label o) (present : Finset O)
    (region : T → Bool) :
    regionOf label (present.map π.toEmbedding) region =
      (regionOf label present region).map π.toEmbedding := by
  ext o
  simp only [regionOf, Finset.mem_filter, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨⟨a, member, rfl⟩, inside⟩
    exact ⟨a, ⟨member, by rwa [keeps] at inside⟩, rfl⟩
  · rintro ⟨a, ⟨member, inside⟩, rfl⟩
    exact ⟨⟨a, member, rfl⟩, by rwa [keeps]⟩

omit [DecidableEq O] in
theorem queryHolds_rename (keeps : ∀ o, label (π o) = label o) (σ : S) (present : Finset O)
    (query : PredicateQueryAdmission.Query T S O) :
    ((renameQuery π query).atSolution σ).Holds label (present.map π.toEmbedding) ↔
      (query.atSolution σ).Holds label present := by
  show regionOf label (present.map π.toEmbedding) (query.region σ) = query.seen.map π.toEmbedding ↔
    regionOf label present (query.region σ) = query.seen
  rw [regionOf_rename keeps]
  exact Finset.map_inj

/-- **Admission is equivariant** under label-preserving renamings of occurrence identities. -/
theorem Firing.valid_rename (A : SubstitutionAction T S) (keeps : ∀ o, label (π o) = label o)
    (f : Firing T S O) (C : Configuration T O) :
    (f.rename π).Valid A label (renameConfiguration π C) ↔ f.Valid A label C := by
  have problem := problem_rename keeps f.selection f.rule C
  have outputs : (f.selection.made.map π).map label = f.selection.made.map label := by
    rw [List.map_map]
    exact congrArg (fun g => f.selection.made.map g) (funext keeps)
  constructor
  · rintro ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputsEq, occurrences,
      consistent, checks⟩, observations⟩
    refine ⟨⟨List.Nodup.of_map π takeDistinct, List.Nodup.of_map π outputDistinct, ?_, ?_, ?_,
      (enabled_rename C.present f.selection).mp occurrences, ?_, ?_⟩, ?_⟩
    · simpa [Firing.rename, renameSelection] using takeLength
    · simpa [Firing.rename, renameSelection] using readLength
    · exact outputs.symm.trans outputsEq
    · simpa only [Firing.rename, problem] using consistent
    · intro check member σ solved
      have asked := checks check member σ (by simpa only [Firing.rename, problem] using solved)
      exact (holds_rename A keeps σ C.present check).mp asked
    · intro query member σ solved
      have asked := observations (renameQuery π query) (List.mem_map_of_mem member) σ
        (by simpa only [Firing.rename, problem] using solved)
      exact (queryHolds_rename keeps σ C.present query).mp asked
  · rintro ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputsEq, occurrences,
      consistent, checks⟩, observations⟩
    refine ⟨⟨takeDistinct.map π.injective, outputDistinct.map π.injective, ?_, ?_, ?_,
      (enabled_rename C.present f.selection).mpr occurrences, ?_, ?_⟩, ?_⟩
    · simpa [Firing.rename, renameSelection] using takeLength
    · simpa [Firing.rename, renameSelection] using readLength
    · exact outputs.trans outputsEq
    · simpa only [Firing.rename, problem] using consistent
    · intro check member σ solved
      have asked := checks check member σ (by simpa only [Firing.rename, problem] using solved)
      exact (holds_rename A keeps σ C.present check).mpr asked
    · intro query member σ solved
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      have asked := observations original present σ (by simpa only [Firing.rename, problem] using solved)
      exact (queryHolds_rename keeps σ C.present original).mpr asked

/-- **The update is equivariant.** -/
theorem Firing.result_rename (keeps : ∀ o, label (π o) = label o) (f : Firing T S O)
    (C : Configuration T O) :
    (f.rename π).result label (renameConfiguration π C) = renameConfiguration π (f.result label C) := by
  show Configuration.mk ((renameSelection π f.selection).problem label f.rule (renameConfiguration π C))
      (fire (C.present.map π.toEmbedding) ((renameSelection π f.selection).commit (T := T))) =
    Configuration.mk (f.selection.problem label f.rule C)
      ((fire C.present (f.selection.commit (T := T))).map π.toEmbedding)
  rw [problem_rename keeps, fire_rename]

/-- **Runs are equivariant.** -/
theorem executable_rename (A : SubstitutionAction T S) (keeps : ∀ o, label (π o) = label o) :
    ∀ (C : Configuration T O) (w : List (Firing T S O)),
      Executable A label (renameConfiguration π C) (w.map (Firing.rename π)) ↔ Executable A label C w
  | _, [] => Iff.rfl
  | C, f :: rest => by
      change ((f.rename π).Valid A label (renameConfiguration π C) ∧
          Executable A label ((f.rename π).result label (renameConfiguration π C))
            (rest.map (Firing.rename π))) ↔ (f.Valid A label C ∧ Executable A label (f.result label C) rest)
      rw [Firing.valid_rename A keeps, Firing.result_rename keeps,
        executable_rename A keeps (f.result label C) rest]

theorem follow_rename (keeps : ∀ o, label (π o) = label o) :
    ∀ (C : Configuration T O) (w : List (Firing T S O)),
      follow label (renameConfiguration π C) (w.map (Firing.rename π)) =
        renameConfiguration π (follow label C w)
  | _, [] => rfl
  | C, f :: rest => by
      change follow label ((f.rename π).result label (renameConfiguration π C))
        (rest.map (Firing.rename π)) = _
      rw [Firing.result_rename keeps]
      exact follow_rename keeps (f.result label C) rest

end Renaming

/-! ## The static independence -/

namespace Firing

/-- Query regions that do not depend on the solution. -/
def StaticQueries (f : Firing T S O) : Prop :=
  ∀ query ∈ f.queries, ∀ σ τ : S, query.region σ = query.region τ

/-- The fragment with a static independence: no checks, and query regions that do not
depend on the solution. Equations, including shared variables, are not restricted. -/
structure Static (f : Firing T S O) : Prop where
  checks : f.rule.checks = []
  queries : f.StaticQueries

@[simp] theorem footprintAt_taken (f : Firing T S O) (σ : S) :
    (f.footprintAt σ).taken = f.selection.taken.toFinset := rfl

@[simp] theorem footprintAt_kept (f : Firing T S O) (σ : S) :
    (f.footprintAt σ).kept = f.selection.read.toFinset := rfl

@[simp] theorem footprintAt_made (f : Firing T S O) (σ : S) :
    (f.footprintAt σ).made = f.selection.made.toFinset := rfl

@[simp] theorem footprintAt_queries (f : Firing T S O) (σ : S) :
    (f.footprintAt σ).queries = f.queries.map fun query => query.atSolution σ := rfl

omit [DecidableEq O] in
@[simp] theorem plain_fst (f : Firing T S O) : f.plain.1 = f.rule := rfl

omit [DecidableEq O] in
@[simp] theorem plain_snd (f : Firing T S O) : f.plain.2 = f.selection := rfl

end Firing

/-- **Static independence of firings**: at every solution, the two footprints, queries
included, are trace independent in the ground layer. -/
def Independent (label : O → T) (f g : Firing T S O) : Prop :=
  ∀ σ : S, TraceIndependent label (f.footprintAt σ) (g.footprintAt σ)

namespace Independent

variable {label : O → T} {f g : Firing T S O}

theorem symm (independent : Independent label f g) : Independent label g f :=
  fun σ => (independent σ).symm

/-- Neither makes what the other takes or reads (`GuardFreeProcessOrders.NoCause`). -/
theorem noCause (independent : Independent label f g) (σ : S) : NoCause f.plain g.plain := by
  intro o made
  have apart := (independent σ).2.1
  have inMade : o ∈ (f.footprintAt σ).made := by simpa using made
  refine ⟨fun taken => Finset.disjoint_left.mp apart inMade ?_,
    fun read => Finset.disjoint_left.mp apart inMade ?_⟩
  · exact MeTTaCalculus.OccurrenceCommits.Commit.mem_uses.mpr (Or.inl (by simpa using taken))
  · exact MeTTaCalculus.OccurrenceCommits.Commit.mem_uses.mpr (Or.inr (by simpa using read))

/-- The second takes nothing the first reads (`GuardFreeProcessOrders.NoAsym`). -/
theorem noAsym (independent : Independent label f g) (σ : S) : NoAsym f.plain g.plain := by
  intro o read taken
  apply (independent σ).1.2.2
  left
  rw [Finset.not_disjoint_iff]
  exact ⟨o, by simpa using taken, by simpa using read⟩

/-- The second makes no identity the first took (`GuardFreeProcessOrders.NoReuse`). -/
theorem noReuse (independent : Independent label f g) (σ : S) : NoReuse f.plain g.plain := by
  intro o made taken
  exact Finset.disjoint_left.mp (independent σ).2.2 (by simpa using made)
    (MeTTaCalculus.OccurrenceCommits.Commit.mem_uses.mpr (Or.inl (by simpa using taken)))

/-- **No predicate-read dependency**: the first writes nothing into a query region of the
second. -/
theorem writesOutside (independent : Independent label f g) (σ : S) :
    ∀ query ∈ g.queries,
      ∀ o ∈ (f.selection.commit (T := T)).taken ∪ (f.selection.commit (T := T)).made,
        query.region σ (label o) = false := by
  intro query member o written
  by_contra inRegion
  apply (independent σ).1.2.1
  right
  exact ⟨query.atSolution σ, List.mem_map.mpr ⟨query, member, rfl⟩, o, written,
    by simpa [PredicateQueryAdmission.Query.atSolution] using inRegion⟩

end Independent

/-- A commit is trace independent of itself exactly when it writes nothing. -/
theorem traceIndependent_self_iff (label : O → T) (c : Commit O T) :
    TraceIndependent label c c ↔ c.taken = ∅ ∧ c.made = ∅ := by
  constructor
  · rintro ⟨⟨noClash, -, -⟩, -, -⟩
    simp only [MeTTaCalculus.OccurrenceCommits.Clash, not_or, not_not] at noClash
    exact ⟨(Finset.disjoint_self_iff_empty _).mp noClash.1,
      (Finset.disjoint_self_iff_empty _).mp noClash.2⟩
  · rintro ⟨taken, made⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · simp [MeTTaCalculus.OccurrenceCommits.Clash, taken, made]
    · simp [MeTTaCalculus.OccurrenceCommits.Spoils, MeTTaCalculus.OccurrenceCommits.WritesInto,
        taken, made]
    · simp [MeTTaCalculus.OccurrenceCommits.Spoils, MeTTaCalculus.OccurrenceCommits.WritesInto,
        taken, made]
    · simp [made]
    · simp [made]

/-- **The reflexive part.** A firing is independent of itself exactly when it takes and makes
nothing. Removing these pairs leaves an irreflexive relation (`MazurkiewiczIndependent`). -/
theorem independent_self_iff (label : O → T) (σ : S) (f : Firing T S O) :
    Independent label f f ↔ f.selection.taken = [] ∧ f.selection.made = [] := by
  constructor
  · intro independent
    obtain ⟨taken, made⟩ := (traceIndependent_self_iff label _).mp (independent σ)
    exact ⟨(List.toFinset_eq_empty_iff _).mp (by simpa using taken),
      (List.toFinset_eq_empty_iff _).mp (by simpa using made)⟩
  · rintro ⟨taken, made⟩ τ
    exact (traceIndependent_self_iff label _).mpr ⟨by simp [taken], by simp [made]⟩

/-- The static independence: both firings in the static fragment, and independent. -/
def StaticIndependent (label : O → T) (f g : Firing T S O) : Prop :=
  f.Static ∧ g.Static ∧ Independent label f g

theorem StaticIndependent.symm {label : O → T} {f g : Firing T S O}
    (independent : StaticIndependent label f g) : StaticIndependent label g f :=
  ⟨independent.2.1, independent.1, independent.2.2.symm⟩

/-- **The Mazurkiewicz independence of the candidate step**: distinct, statically independent
firings. It is symmetric and irreflexive. -/
def MazurkiewiczIndependent (label : O → T) (f g : Firing T S O) : Prop :=
  f ≠ g ∧ StaticIndependent label f g

theorem MazurkiewiczIndependent.symm {label : O → T} {f g : Firing T S O}
    (independent : MazurkiewiczIndependent label f g) : MazurkiewiczIndependent label g f :=
  ⟨Ne.symm independent.1, independent.2.symm⟩

theorem MazurkiewiczIndependent.irrefl (label : O → T) (f : Firing T S O) :
    ¬ MazurkiewiczIndependent label f f :=
  fun independent => independent.1 rfl

/-- Removing the reflexive pairs does not change the generated equivalence: swapping a firing
with itself rewrites nothing. -/
theorem traceEquiv_irreflexive_iff (label : O → T) {w w' : List (Firing T S O)} :
    TraceEquiv (MazurkiewiczIndependent label) w w' ↔ TraceEquiv (StaticIndependent label) w w' := by
  constructor
  · exact Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv.mono fun _ _ related => related.2
  · intro equivalent
    induction equivalent with
    | rel _ _ swapped =>
        cases swapped with
        | @swap u v f g related =>
            by_cases same : f = g
            · subst same
              exact .refl _
            · exact .rel _ _ (.swap u v ⟨same, related⟩)
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

/-! ## Swaps and trace equivalence of runs -/

section Swaps

variable (A : SubstitutionAction T S) (label : O → T)

/-- **The swap of the candidate step with predicate queries.** An executed pair of statically
independent firings runs in the other order and reaches the same class. -/
theorem swap_valid {f g : Firing T S O} {C : Configuration T O}
    (independent : StaticIndependent label f g)
    (fValid : f.Valid A label C) (gValid : g.Valid A label (f.result label C)) :
    g.Valid A label C ∧ f.Valid A label (g.result label C) ∧
      SameUpTo A (g.result label (f.result label C)) (f.result label (g.result label C)) := by
  obtain ⟨fStatic, gStatic, apart⟩ := independent
  obtain ⟨gPlain, fPlain, same⟩ := GuardFreeProcessOrders.swap_valid A label
    (f := f.plain) (g := g.plain) fStatic.checks gStatic.checks
    (apart.noCause A.identity) (apart.noAsym A.identity) (apart.noReuse A.identity)
    fValid.firing gValid.firing
  refine ⟨⟨gPlain, ?_⟩, ⟨fPlain, ?_⟩, same⟩
  · intro query member σ _
    obtain ⟨τ, solvedAfter⟩ := gValid.firing.consistent
    have holds := gValid.observations query member τ solvedAfter
    change regionOf label (fire C.present (f.selection.commit (T := T))) (query.region τ) =
      query.seen at holds
    change regionOf label C.present (query.region σ) = query.seen
    rw [gStatic.queries query member σ τ,
      ← regionOf_fire_of_no_write (apart.writesOutside τ query member)]
    exact holds
  · intro query member σ _
    obtain ⟨τ, solvedBefore⟩ := fValid.firing.consistent
    have holds := fValid.observations query member τ solvedBefore
    change regionOf label C.present (query.region τ) = query.seen at holds
    change regionOf label (fire C.present (g.selection.commit (T := T))) (query.region σ) =
      query.seen
    rw [fStatic.queries query member σ τ,
      regionOf_fire_of_no_write (apart.symm.writesOutside τ query member)]
    exact holds

theorem executable_swap {f g : Firing T S O} {rest : List (Firing T S O)} {C : Configuration T O}
    (independent : StaticIndependent label f g)
    (executable : Executable A label C (f :: g :: rest)) :
    Executable A label C (g :: f :: rest) ∧
      SameUpTo A (follow label C (f :: g :: rest)) (follow label C (g :: f :: rest)) := by
  obtain ⟨fValid, gValid, later⟩ := executable
  obtain ⟨gFirst, fSecond, same⟩ := swap_valid A label independent fValid gValid
  exact ⟨⟨gFirst, fSecond, (executable_congr A label rest same).mp later⟩,
    follow_congr A label rest same⟩

theorem swap_append_executable {f g : Firing T S O} (independent : StaticIndependent label f g) :
    ∀ (u v : List (Firing T S O)) (C : Configuration T O),
      Executable A label C (u ++ f :: g :: v) →
        Executable A label C (u ++ g :: f :: v) ∧
          SameUpTo A (follow label C (u ++ f :: g :: v)) (follow label C (u ++ g :: f :: v))
  | [], _, _, executable => executable_swap A label independent executable
  | x :: u, v, C, executable => by
      obtain ⟨valid, later⟩ := executable
      obtain ⟨moved, same⟩ := swap_append_executable independent u v (x.result label C) later
      exact ⟨⟨valid, moved⟩, same⟩

/-- **Trace-equivalent runs reach the same configuration.** For the static independence,
words related by swaps of adjacent independent firings are executable together and end in
configurations with the same solutions and the same occurrences. -/
theorem traceEquiv_executable {w w' : List (Firing T S O)}
    (equivalent : TraceEquiv (StaticIndependent label) w w') :
    ∀ C : Configuration T O,
      (Executable A label C w ↔ Executable A label C w') ∧
        (Executable A label C w → SameUpTo A (follow label C w) (follow label C w')) := by
  induction equivalent with
  | rel _ _ swapped =>
      cases swapped with
      | swap u v related =>
          intro C
          exact ⟨⟨fun executable => (swap_append_executable A label related u v C executable).1,
            fun executable => (swap_append_executable A label related.symm u v C executable).1⟩,
            fun executable => (swap_append_executable A label related u v C executable).2⟩
  | refl => exact fun C => ⟨Iff.rfl, fun _ => SameUpTo.refl A _⟩
  | symm _ _ _ ih =>
      intro C
      obtain ⟨equal, same⟩ := ih C
      exact ⟨equal.symm, fun executable => sameUpTo_symm A (same (equal.mpr executable))⟩
  | trans _ _ _ _ _ first second =>
      intro C
      obtain ⟨equal₁, same₁⟩ := first C
      obtain ⟨equal₂, same₂⟩ := second C
      exact ⟨equal₁.trans equal₂,
        fun executable => (same₁ executable).trans A (same₂ (equal₁.mp executable))⟩

/-- The irreflexive form gives the same theorem. -/
theorem mazurkiewicz_executable {w w' : List (Firing T S O)}
    (equivalent : TraceEquiv (MazurkiewiczIndependent label) w w') (C : Configuration T O) :
    (Executable A label C w ↔ Executable A label C w') ∧
      (Executable A label C w → SameUpTo A (follow label C w) (follow label C w')) :=
  traceEquiv_executable A label ((traceEquiv_irreflexive_iff label).mp equivalent) C

end Swaps


/-! ## Runs with the same firings are one trace -/

section Processes

variable (A : SubstitutionAction T S) (label : O → T)

/-- The ground footprints of a run, in order. -/
def footprints (w : List (Firing T S O)) : List (Commit O T) :=
  w.map fun f => f.selection.commit (T := T)

theorem follow_present : ∀ (C : Configuration T O) (w : List (Firing T S O)),
    (follow label C w).present =
      MeTTaCalculus.OccurrenceCommits.fireList C.present (footprints w)
  | _, [] => rfl
  | C, f :: rest => follow_present (f.result label C) rest

/-- **A run fires its footprints in the ground layer.** -/
theorem Executable.ground : ∀ {C : Configuration T O} {w : List (Firing T S O)},
    Executable A label C w →
      MeTTaCalculus.OccurrenceCommits.Executable label C.present (footprints w)
  | _, [], _ => .nil _
  | _, _ :: _, executable =>
      .cons executable.1.firing.occurrences (Executable.ground executable.2)

/-- A firing without predicate queries has its selection's commit as its footprint. -/
theorem Firing.footprintAt_of_queries_nil {f : Firing T S O} (empty : f.queries = []) (σ : S) :
    f.footprintAt σ = f.selection.commit (T := T) := by
  simp [Firing.footprintAt, PredicateQueryAdmission.commit, Selection.commit, empty]

/-- A ground swap of the footprints of a run without guards and predicate queries lifts to a
swap of its firings. -/
theorem lift_swapStep {w : List (Firing T S O)} {l : List (Commit O T)}
    (plain : ∀ f ∈ w, f.rule.checks = [] ∧ f.queries = [])
    (step : MeTTaCalculus.OccurrenceCommits.SwapStep label (footprints w) l) :
    ∃ w', footprints w' = l ∧ Swap (StaticIndependent label) w w' := by
  generalize same : footprints w = m at step
  cases step with
  | swap pre post c d independent =>
      obtain ⟨u, rest, rfl, before, after⟩ := List.map_eq_append_iff.mp same
      obtain ⟨f, rest', rfl, first, after'⟩ := List.map_eq_cons_iff.mp after
      obtain ⟨g, v, rfl, second, final⟩ := List.map_eq_cons_iff.mp after'
      have fPlain := plain f (by simp)
      have gPlain := plain g (by simp)
      refine ⟨u ++ g :: f :: v, ?_, Swap.swap u v ⟨⟨fPlain.1, ?_⟩, ⟨gPlain.1, ?_⟩, fun σ => ?_⟩⟩
      · simp only [footprints, List.map_append, List.map_cons] at before final ⊢
        rw [before, first, second, final]
      · intro query member
        rw [fPlain.2] at member
        cases member
      · intro query member
        rw [gPlain.2] at member
        cases member
      · rw [Firing.footprintAt_of_queries_nil fPlain.2, Firing.footprintAt_of_queries_nil gPlain.2,
          first, second]
        exact independent

/-- **Runs with the same firings are one trace.** Without guards and predicate queries, two
runs of the same firings, with fresh and pairwise distinct footprints, are trace equivalent:
the trace of such a run is its set of firings, ordered by what they make and use. This carries
`OccurrenceCommits.positive_runs_traceEq` from footprints to firings. With predicate queries it
fails: an absence can be falsified and restored (`OccurrenceCommits.Controls.restored_absence_two_traces`). -/
theorem same_firings_traceEquiv {C : Configuration T O} {w₁ w₂ : List (Firing T S O)}
    (plain : ∀ f ∈ w₁, f.rule.checks = [] ∧ f.queries = [])
    (fresh : MeTTaCalculus.OccurrenceCommits.GloballyFresh C.present (footprints w₁))
    (distinct : (footprints w₁).Nodup) (perm : w₁.Perm w₂)
    (executable₁ : Executable A label C w₁) (executable₂ : Executable A label C w₂) :
    TraceEquiv (StaticIndependent label) w₁ w₂ := by
  have positive : ∀ c ∈ footprints w₁, c.Positive := by
    intro c member
    obtain ⟨f, -, rfl⟩ := List.mem_map.mp member
    rfl
  have ground := MeTTaCalculus.OccurrenceCommits.positive_runs_traceEq positive fresh distinct
    (perm.map _) (executable₁.ground A label) (executable₂.ground A label)
  have lifted : ∀ l, Relation.ReflTransGen (MeTTaCalculus.OccurrenceCommits.SwapStep label)
      (footprints w₁) l → ∃ w', footprints w' = l ∧ w'.Perm w₁ ∧
        TraceEquiv (StaticIndependent label) w₁ w' := by
    intro l related
    induction related with
    | refl => exact ⟨w₁, rfl, List.Perm.refl _, .refl _⟩
    | tail _ step ih =>
        obtain ⟨w', footprinted, permuted, equivalent⟩ := ih
        obtain ⟨w'', footprinted', swapped⟩ :=
          lift_swapStep label (fun f member => plain f (permuted.subset member))
            (footprinted ▸ step)
        refine ⟨w'', footprinted', ?_, .trans _ _ _ equivalent (.rel _ _ swapped)⟩
        cases swapped with
        | swap u v _ => exact (List.Perm.append_left u (List.Perm.swap _ _ v)).symm.trans permuted
  obtain ⟨w', footprinted, permuted, equivalent⟩ := lifted _ ground
  have injective := List.inj_on_of_nodup_map distinct
  have equal : ∀ (a b : List (Firing T S O)), (∀ f ∈ a, f ∈ w₁) → (∀ f ∈ b, f ∈ w₁) →
      footprints a = footprints b → a = b := by
    intro a
    induction a with
    | nil => intro b _ _ same; exact (List.map_eq_nil_iff.mp same.symm).symm
    | cons x a ih =>
        intro b inA inB same
        obtain ⟨y, b', rfl, head, tail⟩ := List.map_eq_cons_iff.mp same.symm
        have xy : x = y := injective (inA x (by simp)) (inB y (by simp)) head.symm
        rw [xy, ih b' (fun f member => inA f (by simp [member]))
          (fun f member => inB f (by simp [member])) tail.symm]
  rw [← equal w' w₂ (fun f member => permuted.subset member)
    (fun f member => perm.symm.subset member) footprinted]
  exact equivalent

end Processes

/-! ## The candidate step on configuration classes -/

section Classes

omit [DecidableEq O] in
/-- Configurations with the same solutions and the same present occurrences. -/
def sameSetoid (A : SubstitutionAction T S) : Setoid (Configuration T O) where
  r := SameUpTo A
  iseqv := ⟨SameUpTo.refl A, sameUpTo_symm A, fun first second => SameUpTo.trans A first second⟩

/-- A configuration up to its solutions and its present occurrences. -/
def ConfigurationClass (A : SubstitutionAction T S) (Occurrence : Type uO) : Type (max uT uO) :=
  Quotient (sameSetoid (O := Occurrence) A)

omit [DecidableEq O] in
/-- The class of a configuration. -/
def ConfigurationClass.mk (A : SubstitutionAction T S) (C : Configuration T O) :
    ConfigurationClass A O :=
  Quotient.mk (sameSetoid A) C
end Classes

namespace Firing

variable (A : SubstitutionAction T S) (label : O → T)

/-- Admission on classes. -/
def ValidAt (f : Firing T S O) : ConfigurationClass A O → Prop :=
  Quotient.lift (f.Valid A label) fun _ _ same => propext (Firing.valid_congr A label same)

/-- The update on classes. -/
def resultClass (f : Firing T S O) : ConfigurationClass A O → ConfigurationClass A O :=
  Quotient.lift (fun C => ConfigurationClass.mk A (f.result label C))
    fun _ _ same => Quotient.sound (f.result_congr A label same)

theorem validAt_mk (f : Firing T S O) (C : Configuration T O) :
    f.ValidAt A label (ConfigurationClass.mk A C) ↔ f.Valid A label C := Iff.rfl

theorem resultClass_mk (f : Firing T S O) (C : Configuration T O) :
    f.resultClass A label (ConfigurationClass.mk A C) =
      ConfigurationClass.mk A (f.result label C) := rfl

end Firing

section Presentation

open Mettapedia.GSLT (GSLT)
open Mettapedia.GSLT.Core.InteractionEvent (InteractionPresentation)
open Mettapedia.GSLT.Causality.OccurrenceHistory (SiteIndependence IndependenceTile OccurrencePath)


variable (A : SubstitutionAction T S) (label : O → T)

/-- **The candidate step with predicate queries as a GSLT** on configuration classes. -/
def theory : GSLT where
  Term := ConfigurationClass A O
  equations := ⟨Eq, eq_equivalence⟩
  rewrites x y := ∃ f : Firing T S O, f.ValidAt A label x ∧ y = f.resultClass A label x
  rewrites_resp_left := by
    intro x x' y same step
    exact ⟨y, (same : x = x') ▸ step, rfl⟩
  rewrites_resp_right := by
    intro x y y' step same
    exact (same : y = y') ▸ step

/-- Its events are the firings; the evidence of an event is its admission and its update. -/
def presentation : InteractionPresentation (theory A label) where
  Site := Firing T S O
  Event f x y := PLift (f.ValidAt A label x ∧ y = f.resultClass A label x)
  sound := fun {f} {_} {_} event => ⟨f, event.down⟩

/-- The Mazurkiewicz independence as an independence of sites. -/
def siteIndependence : SiteIndependence (presentation A label) where
  indep f g := MazurkiewiczIndependent label f g
  symm := fun _ _ independent => independent.symm
  irrefl := fun f => MazurkiewiczIndependent.irrefl label f

/-- **An executed independent pair is a tile**: its two routes are the two orders. -/
def tile {C : Configuration T O} {f g : Firing T S O}
    (independent : MazurkiewiczIndependent label f g)
    (fValid : f.Valid A label C) (gValid : g.Valid A label (f.result label C)) :
    IndependenceTile (presentation A label) (siteIndependence A label)
      (ConfigurationClass.mk A C) where
  first := ⟨f, ConfigurationClass.mk A (f.result label C), ⟨⟨fValid, rfl⟩⟩⟩
  altFirst := ⟨g, ConfigurationClass.mk A (g.result label C),
    ⟨⟨(swap_valid A label independent.2 fValid gValid).1, rfl⟩⟩⟩
  second := ⟨g, ConfigurationClass.mk A (g.result label (f.result label C)), ⟨⟨gValid, rfl⟩⟩⟩
  altSecond := ⟨f, ConfigurationClass.mk A (f.result label (g.result label C)),
    ⟨⟨(swap_valid A label independent.2 fValid gValid).2.1, rfl⟩⟩⟩
  independent := independent
  close := Quotient.sound (swap_valid A label independent.2 fValid gValid).2.2
  sameFirst := rfl
  sameSecond := rfl

/-- **Each swap is a generated 2-cell of the existing Mazurkiewicz equivalence.** -/
theorem swap_is_diamond {C : Configuration T O} {f g : Firing T S O}
    (independent : MazurkiewiczIndependent label f g)
    (fValid : f.Valid A label C) (gValid : g.Valid A label (f.result label C)) :
    Mettapedia.GSLT.Causality.Mazurkiewicz.DiamondEq (siteIndependence A label)
      (tile A label independent fValid gValid).path
      (tile A label independent fValid gValid).pathSwap' :=
  .swap _

/-- The two routes of the tile fire the two orders of the pair. -/
theorem tile_sites {C : Configuration T O} {f g : Firing T S O}
    (independent : MazurkiewiczIndependent label f g)
    (fValid : f.Valid A label C) (gValid : g.Valid A label (f.result label C)) :
    OccurrencePath.sites (tile A label independent fValid gValid).path = [f, g] ∧
      OccurrencePath.sites (tile A label independent fValid gValid).pathSwap' = [g, f] := by
  refine ⟨rfl, ?_⟩
  exact (IndependenceTile.sites_pathSwap' (tile A label independent fValid gValid)).trans rfl

/-- **Firings label the steps of the class theory**, which has discrete equations. -/
def eventLabels : Mettapedia.GSLT.Causality.HistoryMonad.EventLabels (theory A label) (Firing T S O) where
  labelled x y f := f.ValidAt A label x ∧ y = f.resultClass A label x
  sound := fun labelled => ⟨_, labelled⟩
  resp_left := by
    intro x x' y f same labelled
    exact ⟨y, (same : x = x') ▸ labelled, rfl⟩
  resp_right := by
    intro x y y' f labelled same
    exact (same : y = y') ▸ labelled

theorem eventLabels_total : (eventLabels A label).Total := fun step => step

/-- **Runs are histories.** A run from `C` is a path of the history theory of
`HistoryMonad`: the class moves as the run does, and the word of the writer records the
firings in order. -/
theorem run_is_history : ∀ (C : Configuration T O) (w : List (Firing T S O))
    (word : FreeMonoid (Firing T S O)), Executable A label C w →
      (Mettapedia.GSLT.Causality.HistoryMonad.history (eventLabels A label)).MultiStep
        (ConfigurationClass.mk A C, word)
        (ConfigurationClass.mk A (follow label C w), word * FreeMonoid.ofList w)
  | C, [], word, _ => by
      simpa [follow] using GSLT.MultiStep.refl
        (S := Mettapedia.GSLT.Causality.HistoryMonad.history (eventLabels A label))
        (ConfigurationClass.mk A C, word)
  | C, f :: rest, word, executable => by
      have step : (Mettapedia.GSLT.Causality.HistoryMonad.history (eventLabels A label)).Step
          (ConfigurationClass.mk A C, word)
          (ConfigurationClass.mk A (f.result label C), word * FreeMonoid.of f) :=
        (Mettapedia.GSLT.Causality.HistoryMonad.history_step_iff (eventLabels A label)).mpr
          ⟨f, ⟨executable.1, rfl⟩, rfl⟩
      have later := run_is_history (f.result label C) rest (word * FreeMonoid.of f) executable.2
      rw [mul_assoc, ← FreeMonoid.ofList_cons] at later
      exact GSLT.MultiStep.step step later

end Presentation

/-! ## Controls -/

namespace Controls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)

/-- Occurrence labels: `0 : f(X)`, `1 : X`, `2 : 1`, `3 : 0`, `9 : 9`, otherwise `2`. -/
def label : Nat → Term signature
  | 0 => ConstraintMultisetRewriting.Controls.f (.var 0)
  | 1 => .var 0
  | 2 => .const 1
  | 3 => .const 0
  | 9 => .const 9
  | _ => .const 2

abbrev Run := Firing (Term signature) (Subst signature) Nat

/-- Every variable to `0`. -/
def zeros : Subst signature := fun _ => .const 0

/-- Takes `0 : f(X)` with the pattern `f(0)`, so the shared `X` becomes `0`, and makes `2`. -/
def taker : Run :=
  ⟨⟨[ConstraintMultisetRewriting.Controls.f (.const 0)], [], [], [], [.const 1]⟩, [],
    ⟨[0], [], [2]⟩⟩

/-- Reads `1 : X` with the pattern `Y`, so `Y` joins the shared `X`, and makes `3`. -/
def reader : Run := ⟨⟨[], [.var 1], [], [], [.const 0]⟩, [], ⟨[], [1], [3]⟩⟩

def start : Configuration (Term signature) Nat := ⟨[], {0, 1}⟩

theorem taker_valid : taker.Valid A label start := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [taker]⟩,
    by simp [taker]⟩
  intro equation member
  have same : equation = (ConstraintMultisetRewriting.Controls.f (.const 0), label 0) := by
    simpa [Selection.problem, Selection.equations, start, taker] using member
  subst same
  rfl

theorem reader_valid : reader.Valid A label (taker.result label start) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [reader]⟩,
    by simp [reader]⟩
  intro equation member
  have cases : equation = (ConstraintMultisetRewriting.Controls.f (.const 0), label 0) ∨
      equation = (.var 1, label 1) := by
    simpa [Selection.problem, Selection.equations, Selection.result, Firing.result, start, taker,
      reader]
      using member
  rcases cases with rfl | rfl <;> rfl

theorem taker_reader_independent : StaticIndependent label taker reader := by
  refine ⟨⟨rfl, by simp [Firing.StaticQueries, taker]⟩,
    ⟨rfl, by simp [Firing.StaticQueries, reader]⟩,
    fun _ => ?_⟩
  unfold TraceIndependent MeTTaCalculus.OccurrenceCommits.Independent
    MeTTaCalculus.OccurrenceCommits.Clash MeTTaCalculus.OccurrenceCommits.Spoils
    MeTTaCalculus.OccurrenceCommits.WritesInto MeTTaCalculus.OccurrenceCommits.Commit.uses
  simp only [Firing.footprintAt_taken, Firing.footprintAt_kept, Firing.footprintAt_made,
    Firing.footprintAt_queries, taker, reader, List.map_nil]
  decide

theorem taker_then_reader : Executable A label start [taker, reader] :=
  ⟨taker_valid, reader_valid, reader_valid.firing.consistent⟩

/-- **Positive control, shared variables.** The two firings constrain the shared `X` from two
sides; the run swaps, and both orders reach the same class. -/
theorem shared_variables_swap :
    Executable A label start [reader, taker] ∧
      SameUpTo A (follow label start [taker, reader]) (follow label start [reader, taker]) :=
  executable_swap A label taker_reader_independent taker_then_reader

/-- In every solution of the final store, the reader's `Y` is `0`: the equations are genuine. -/
theorem reader_variable_bound (σ : Subst signature)
    (solved : A.Models σ (follow label start [taker, reader]).equations) :
    σ.applyTerm (.var 1) = .const 0 := by
  have first := solved (ConstraintMultisetRewriting.Controls.f (.const 0), label 0) (by
    simp [follow, Firing.result, Selection.result, Selection.problem, Selection.equations,
      start, taker, reader])
  have second := solved (.var 1, label 1) (by
    simp [follow, Firing.result, Selection.result, Selection.problem, Selection.equations,
      start, taker, reader])
  change ConstraintMultisetRewriting.Controls.f (.const 0) =
    ConstraintMultisetRewriting.Controls.f (σ 0) at first
  change σ 1 = σ 0 at second
  have children : (fun _ : Fin 1 => Term.const (σ := signature) 0) = (fun _ => σ 0) :=
    eq_of_heq (Term.app.inj first).2
  change σ 1 = .const 0
  rw [second]
  exact (congr_fun children 0).symm

/-- The word swap is a generated equivalence, so the theorem applies to it. -/
theorem swapped_words :
    TraceEquiv (StaticIndependent label) [taker, reader] [reader, taker] :=
  .rel _ _ (by simpa using Swap.swap [] [] taker_reader_independent)

/-- **Positive control: the same firings, one trace**, derived from footprints alone. -/
theorem same_firings_one_trace :
    TraceEquiv (StaticIndependent label) [taker, reader] [reader, taker] := by
  refine same_firings_traceEquiv A label ?_ ?_ ?_ (List.Perm.swap reader taker [])
    taker_then_reader shared_variables_swap.1
  · intro f member
    rcases List.mem_pair.mp member with rfl | rfl <;> exact ⟨rfl, rfl⟩
  · refine ⟨fun c member => ?_, List.pairwise_pair.mpr (by decide)⟩
    simp only [footprints, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl <;> decide
  · simp only [footprints, List.map_cons, List.map_nil, List.nodup_cons, List.mem_singleton,
      List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true]
    intro same
    have taken := congrArg Commit.taken same
    simp [Selection.commit, taker, reader] at taken

/-! ### The reflexive part -/

/-- Reads `1` and nothing else. -/
def onlyReads : Run := ⟨⟨[], [.var 1], [], [], []⟩, [], ⟨[], [1], []⟩⟩

/-- A reader is independent of itself; the taker is not. -/
theorem reflexive_part :
    Independent label onlyReads onlyReads ∧ ¬ Independent label taker taker :=
  ⟨(independent_self_iff label zeros onlyReads).mpr ⟨rfl, rfl⟩,
    fun self => by
      have := ((independent_self_iff label zeros taker).mp self).1
      simp [taker] at this⟩

/-! ### A guard reads what another firing tells -/

/-- Tells `X = 1`. -/
def teller : Run := ⟨⟨[], [], [(.var 0, .const 1)], [], []⟩, [], ⟨[], [], []⟩⟩

/-- Asks `X = 1`. -/
def asker : Run := ⟨⟨[], [], [], [.equal (.var 0) (.const 1)], []⟩, [], ⟨[], [], []⟩⟩

def empty : Configuration (Term signature) Nat := ⟨[], ∅⟩

/-- Every variable to `1`. -/
def ones : Subst signature := fun _ => .const 1

theorem teller_valid : teller.Valid A label empty := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨ones, ?_⟩, by simp [teller]⟩,
    by simp [teller]⟩
  intro equation member
  have same : equation = (.var 0, .const 1) := by
    simpa [Selection.problem, Selection.equations, empty, teller] using member
  subst same
  rfl

theorem asker_valid_after : asker.Valid A label (teller.result label empty) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨ones, ?_⟩, ?_⟩, by simp [asker]⟩
  · intro equation member
    have same : equation = (.var 0, .const 1) := by
      simpa [Selection.problem, Selection.equations, Selection.result, Firing.result, empty,
        teller, asker] using member
    subst same
    rfl
  · intro check member σ solved
    have only : check = .equal (.var 0) (.const 1) := by simpa [asker] using member
    subst only
    exact solved (.var 0, .const 1) (by
      simp [Selection.problem, Selection.equations, Selection.result, Firing.result, empty,
        teller, asker])

theorem asker_refused_first : ¬ asker.Valid A label empty := by
  intro valid
  have holds := valid.firing.checks _ (List.mem_singleton_self _) (Subst.id signature) (by
    simp [Selection.problem, Selection.equations, empty, asker])
  change (Term.var (σ := signature) 0) = .const 1 at holds
  cases holds

/-- **Negative control.** The commits are trace independent, yet only one order runs: the
guard reads the other firing's tell. Static independence requires the guard-free fragment. -/
theorem told_check_one_order :
    Independent label teller asker ∧ Executable A label empty [teller, asker] ∧
      ¬ Executable A label empty [asker, teller] ∧ ¬ asker.Static := by
  refine ⟨fun _ => ?_, ⟨teller_valid, asker_valid_after, asker_valid_after.firing.consistent⟩,
    fun executable => asker_refused_first executable.1, fun static => by
      have := static.checks
      simp [asker] at this⟩
  unfold TraceIndependent MeTTaCalculus.OccurrenceCommits.Independent
    MeTTaCalculus.OccurrenceCommits.Clash MeTTaCalculus.OccurrenceCommits.Spoils
    MeTTaCalculus.OccurrenceCommits.WritesInto MeTTaCalculus.OccurrenceCommits.Commit.uses
  simp only [Firing.footprintAt_taken, Firing.footprintAt_kept, Firing.footprintAt_made,
    Firing.footprintAt_queries, teller, asker, List.map_nil]
  decide

/-! ### A predicate query and a writer into its region -/

/-- The region of persistent atoms. -/
def persistent : Term signature → Bool
  | .const name => name == 9
  | _ => false

/-- A predicate query of the persistent region whose census is empty. -/
def noPersistent : MeTTaCalculus.OccurrenceCommits.PredicateQuery Nat (Term signature) :=
  ⟨persistent, ∅⟩

/-- Observes that no persistent atom is present. -/
def observer : Run :=
  ⟨⟨[], [], [], [], []⟩, [PredicateQueryAdmission.Query.fixed noPersistent], ⟨[], [], []⟩⟩

/-- Makes the persistent atom `9`. -/
def maker : Run := ⟨⟨[], [], [], [], [.const 9]⟩, [], ⟨[], [], [9]⟩⟩

theorem observer_valid : observer.Valid A label empty := by
  refine (PredicateQueryAdmission.valid_fixed_iff A label observer.rule [noPersistent] empty
    observer.selection).mpr ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
      ⟨Subst.id signature, by simp [Selection.problem, Selection.equations, empty, observer]⟩,
      by simp [observer]⟩, ?_⟩
  intro query member
  obtain rfl := List.mem_singleton.mp member
  decide

theorem maker_valid_after : maker.Valid A label (observer.result label empty) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    ⟨Subst.id signature, by
      simp [Selection.problem, Selection.equations, Selection.result, Firing.result, empty,
        observer, maker]⟩, by simp [maker]⟩, by simp [maker]⟩

theorem observer_refused_after_maker : ¬ observer.Valid A label (maker.result label empty) := by
  intro valid
  have holds := valid.observations _ (List.mem_singleton_self _) (Subst.id signature) (by
    simp [Selection.problem, Selection.equations, Selection.result, Firing.result, empty,
      observer, maker])
  revert holds
  decide

/-- **Negative control, the predicate-read dependency.** Both firings are in the static
fragment; a writer into the query region is not independent of the query, and only the
order with the query first runs. -/
theorem census_writer_one_order :
    observer.Static ∧ maker.Static ∧ ¬ Independent label observer maker ∧
      Executable A label empty [observer, maker] ∧ ¬ Executable A label empty [maker, observer] := by
  refine ⟨⟨rfl, ?_⟩, ⟨rfl, by simp [Firing.StaticQueries, maker]⟩, fun independent => ?_,
    ⟨observer_valid, maker_valid_after, maker_valid_after.firing.consistent⟩,
    fun executable => observer_refused_after_maker executable.2.1⟩
  · intro query member σ τ
    obtain rfl := List.mem_singleton.mp member
    rfl
  · have spoiled := independent (Subst.id signature)
    revert spoiled
    unfold TraceIndependent MeTTaCalculus.OccurrenceCommits.Independent
      MeTTaCalculus.OccurrenceCommits.Clash MeTTaCalculus.OccurrenceCommits.Spoils
      MeTTaCalculus.OccurrenceCommits.WritesInto MeTTaCalculus.OccurrenceCommits.Commit.uses
    simp only [Firing.footprintAt_taken, Firing.footprintAt_kept, Firing.footprintAt_made,
      Firing.footprintAt_queries, observer, maker, List.map_cons, List.map_nil]
    decide

end Controls


#print axioms Firing.valid_congr
#print axioms executable_ofPlain_iff
#print axioms executable_congr
#print axioms follow_congr
#print axioms firstOrder_admits_iff
#print axioms executable_iff_run
#print axioms follow_eq_last
#print axioms Firing.valid_rename
#print axioms Firing.result_rename
#print axioms executable_rename
#print axioms follow_rename
#print axioms Independent.writesOutside
#print axioms independent_self_iff
#print axioms traceEquiv_irreflexive_iff
#print axioms swap_valid
#print axioms executable_swap
#print axioms traceEquiv_executable
#print axioms mazurkiewicz_executable
#print axioms siteIndependence
#print axioms tile
#print axioms swap_is_diamond
#print axioms tile_sites
#print axioms eventLabels_total
#print axioms run_is_history
#print axioms Executable.ground
#print axioms lift_swapStep
#print axioms same_firings_traceEquiv
#print axioms Controls.same_firings_one_trace
#print axioms Controls.shared_variables_swap
#print axioms Controls.reader_variable_bound
#print axioms Controls.swapped_words
#print axioms Controls.reflexive_part
#print axioms Controls.told_check_one_order
#print axioms Controls.census_writer_one_order

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
