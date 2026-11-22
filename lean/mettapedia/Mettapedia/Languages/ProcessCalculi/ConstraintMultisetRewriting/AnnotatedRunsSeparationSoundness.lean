import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsSeparationFrame
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsPeak

/-!
# Soundness and completeness of the candidate step against its separation-logic reading

The precedent is the linear-logic semantics of Constraint Handling Rules (Betz and Frühwirth):
a rule is read as a linear implication applied inside a context, and computations correspond to
derivations. Here a firing is read as a **small axiom** at its footprint, applied beside a frame by
the frame rule, and runs of a program correspond to **derivations**: sequences of framed small
steps (`FramedStep`, `Derives`).

## The footprint of a firing

`footprintSet f queries`: what the firing takes, what it reads, and what its exact queries saw.
Sightings are seen sets, so the footprint is stated for a firing whose queries are exact
(`f.queries = queries.map Query.toRegion`). At a configuration `C` where it is admitted, `C` is the
tensor of the footprint configuration `smallOf f queries C` and the rest `restOf f queries C`, both
carrying the knowledge of `C`, which is duplicable
(`small_rest_sameUpTo`, `small_rest_separable`). The firing is admitted at its footprint
(`small_valid`), the rest lies outside every query region at the cut (`rest_blind_at_cut`), and the
configuration the firing leaves is the tensor of what it leaves at its footprint and the rest
(`result_small_rest_sameUpTo`). A predicate query owns the occurrences it saw; a count guard records
nothing of what it counted and an `any` query nothing of the row it found, so the footprint keeps
neither and both are excluded: every guard must survive removing rows (`AntitoneGuards`).

## Soundness and completeness

* **Soundness** (`framedStep_of_valid`, `programReaches_derives`): every run of a program whose
  firings have guards that survive removing rows and exact queries is a derivation from small axioms
  and the frame rule, exact queries and `none` queries included.
* **Completeness for the query-free fragment** (`step_of_framedStep`, `derives_reaches`): every
  derivation of a program of query-free firings is a run of the program, exactly, up to classes.
  So `derives_iff_reaches`.
* Completeness fails with an absence query, and soundness fails with a count guard
  (`SeparationControls.completeness_fails_with_absence`,
  `SeparationControls.soundness_fails_with_count_guard`). Framing whole derivations instead of single
  steps is unsound even without queries, because made identities are fixed names
  (`SeparationControls.multi_step_frame_unsound`).

## Program logic

Exact assertions (`exactly`), sequencing (`triple_append`) and consequence (`triple_mono`). With
the frame rule they verify programs from local specifications
(`SeparationControls.round_verified_by_frames`).

## Authority over regions

An owned configuration (`Owned`) carries the regions whose complete contents it owns. Two owned
configurations are separable (`OwnedSeparable`) when their configurations are, and neither has an
occurrence in a region the other owns. This is again a separation algebra up to classes
(`ownedSeparable_comm`, `ownedSeparable_assoc`). A firing whose queries observe owned regions
(`ObservesUnder`) is local against every separable owned frame (`owned_valid_frame`), whatever its
queries observe: the query's side condition becomes part of separability.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open MeTTaCalculus.OccurrenceCommits (PredicateQuery regionOf mem_regionOf fire mem_fire)
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO

namespace SeparationRuns

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-! ## The footprint of a firing -/

section Footprint

variable (A : SubstitutionAction T S) (label : O → T)

/-- What a list of predicate queries saw. -/
def seenSet : List (PredicateQueryAdmission.Query T S O) → Finset O
  | [] => ∅
  | q :: rest => q.seen ∪ seenSet rest

theorem mem_seenSet {qs : List (PredicateQueryAdmission.Query T S O)} {o : O} :
    o ∈ seenSet qs ↔ ∃ q ∈ qs, o ∈ q.seen := by
  induction qs with
  | nil => simp [seenSet]
  | cons q rest ih => simp [seenSet, ih]

/-- **The footprint of a firing with exact queries**: what it takes, what it reads, and what its
exact queries `queries` saw. Sightings are seen sets, so the footprint is stated for the exact
queries the firing carries (`f.queries = queries.map Query.toRegion` wherever it is used). -/
def footprintSet (f : Firing T S O) (queries : List (PredicateQueryAdmission.Query T S O)) :
    Finset O :=
  f.selection.taken.toFinset ∪ f.selection.read.toFinset ∪ seenSet queries

/-- The footprint configuration: the knowledge where the firing fires, on its footprint. -/
def smallOf (f : Firing T S O) (queries : List (PredicateQueryAdmission.Query T S O))
    (C : Configuration T O) : Configuration T O :=
  ⟨C.equations, footprintSet f queries⟩

/-- The rest: the same knowledge, on everything else. -/
def restOf (f : Firing T S O) (queries : List (PredicateQueryAdmission.Query T S O))
    (C : Configuration T O) : Configuration T O :=
  ⟨C.equations, C.present \ footprintSet f queries⟩

omit [DecidableEq O] in
/-- The guards of a query-free firing are equations, which survive removing rows. -/
theorem QueryFree.antitoneGuards {f : Firing T S O} (free : QueryFree f) : AntitoneGuards f := by
  intro check member
  obtain ⟨left, right, rfl⟩ := free.guards check member
  exact ⟨fun _ _ same => (by cases same), fun _ same => (by cases same)⟩

theorem mem_footprintSet_of_taken {f : Firing T S O}
    {queries : List (PredicateQueryAdmission.Query T S O)} {o : O} (taken : o ∈ f.selection.taken) :
    o ∈ footprintSet f queries := by
  simp only [footprintSet, Finset.mem_union, List.mem_toFinset]
  exact Or.inl (Or.inl taken)

theorem mem_footprintSet_of_read {f : Firing T S O}
    {queries : List (PredicateQueryAdmission.Query T S O)} {o : O} (read : o ∈ f.selection.read) :
    o ∈ footprintSet f queries := by
  simp only [footprintSet, Finset.mem_union, List.mem_toFinset]
  exact Or.inl (Or.inr read)

theorem mem_footprintSet_of_seen {f : Firing T S O}
    {queries : List (PredicateQueryAdmission.Query T S O)} {o : O}
    {q : PredicateQueryAdmission.Query T S O} (member : q ∈ queries) (seen : o ∈ q.seen) :
    o ∈ footprintSet f queries := by
  simp only [footprintSet, Finset.mem_union]
  exact Or.inr (mem_seenSet.mpr ⟨q, member, seen⟩)

/-- The footprint of an admitted firing with exact queries lies where it fires. -/
theorem footprintSet_subset {f : Firing T S O} {C : Configuration T O}
    {queries : List (PredicateQueryAdmission.Query T S O)}
    (exact : f.queries = queries.map PredicateQueryAdmission.Query.toRegion)
    (valid : f.Valid A label C) : footprintSet f queries ⊆ C.present := by
  intro o member
  simp only [footprintSet, Finset.mem_union, List.mem_toFinset] at member
  rcases member with (taken | read) | seen
  · exact used_present A label valid (Or.inl taken)
  · exact used_present A label valid (Or.inr read)
  · obtain ⟨q, inQ, inSeen⟩ := mem_seenSet.mp seen
    obtain ⟨σ, solved⟩ := valid.firing.consistent
    have asked : q.toRegion ∈ f.queries := by
      rw [exact]
      exact List.mem_map_of_mem inQ
    have saw : regionOf label C.present (q.region σ) = q.seen :=
      valid.observations q.toRegion asked σ solved
    rw [← saw] at inSeen
    exact (mem_regionOf.mp inSeen).1

/-- **The footprint and the rest make up the configuration.** -/
theorem small_rest_sameUpTo {f : Firing T S O} {C : Configuration T O}
    {queries : List (PredicateQueryAdmission.Query T S O)}
    (exact : f.queries = queries.map PredicateQueryAdmission.Query.toRegion)
    (valid : f.Valid A label C) :
    SameUpTo A (tensor (smallOf f queries C) (restOf f queries C)) C := by
  refine ⟨fun σ => ?_, ?_⟩
  · change A.Models σ (C.equations ++ C.equations) ↔ A.Models σ C.equations
    rw [A.models_append, and_self]
  · change footprintSet f queries ∪ (C.present \ footprintSet f queries) = C.present
    exact Finset.union_sdiff_of_subset (footprintSet_subset A label exact valid)

theorem small_rest_separable {f : Firing T S O} {C : Configuration T O}
    {queries : List (PredicateQueryAdmission.Query T S O)} (valid : f.Valid A label C) :
    Separable A (smallOf f queries C) (restOf f queries C) := by
  refine ⟨Finset.disjoint_sdiff, ?_⟩
  obtain ⟨σ, solved⟩ := valid.firing.consistent
  rw [Firing.problem_eq', A.models_append] at solved
  exact ⟨σ, (A.models_append σ _ _).mpr ⟨solved.1, solved.1⟩⟩

/-- **A firing with exact queries is admitted at its footprint.** -/
theorem small_valid {f : Firing T S O} {C : Configuration T O}
    {queries : List (PredicateQueryAdmission.Query T S O)}
    (exact : f.queries = queries.map PredicateQueryAdmission.Query.toRegion)
    (valid : f.Valid A label C) (antitone : AntitoneGuards f) :
    f.Valid A label (smallOf f queries C) := by
  have firing := valid.firing
  have sub := footprintSet_subset A label exact valid
  refine ⟨⟨firing.take_distinct, firing.output_distinct, firing.take_length, firing.read_length,
    firing.outputs, ⟨fun o member => ?_, fun o member => ?_, firing.occurrences.apart,
      Finset.disjoint_of_subset_right sub firing.occurrences.fresh,
      fun query member => by simp [Selection.commit] at member⟩, firing.consistent, ?_⟩, ?_⟩
  · exact mem_footprintSet_of_taken (by simpa [Selection.commit] using member)
  · exact mem_footprintSet_of_read (by simpa [Selection.commit] using member)
  · intro check member σ solved
    have holds := firing.checks check member σ solved
    cases check with
    | equal left right => exact holds
    | predicate quantifier pattern =>
        cases quantifier with
        | any => exact absurd rfl ((antitone _ member).2 pattern)
        | none =>
            intro o present
            exact holds o (sub present)
    | count pattern number => exact absurd rfl ((antitone _ member).1 pattern number)
  · intro query member σ solved
    have listed := member
    rw [exact] at listed
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp listed
    have saw : regionOf label C.present (original.region σ) = original.seen :=
      valid.observations _ member σ solved
    change regionOf label (footprintSet f queries) (original.region σ) = original.seen
    ext o
    constructor
    · intro inRegion
      rw [← saw]
      exact mem_regionOf.mpr ⟨sub (mem_regionOf.mp inRegion).1, (mem_regionOf.mp inRegion).2⟩
    · intro inSeen
      have inC : o ∈ regionOf label C.present (original.region σ) := by
        rw [saw]
        exact inSeen
      exact mem_regionOf.mpr ⟨mem_footprintSet_of_seen inOriginal inSeen, (mem_regionOf.mp inC).2⟩

/-- **The rest lies outside every query region at the cut**, for a firing with exact queries. -/
theorem rest_blind_at_cut {f : Firing T S O} {C : Configuration T O}
    {queries : List (PredicateQueryAdmission.Query T S O)}
    (exact : f.queries = queries.map PredicateQueryAdmission.Query.toRegion)
    (valid : f.Valid A label C) :
    ∀ query ∈ f.queries, ∀ σ, A.Models σ (f.selection.problem label f.rule C) →
      ∀ o ∈ (restOf f queries C).present, query.region σ (label o) = false := by
  intro query member σ solved o inRest
  have listed := member
  rw [exact] at listed
  obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp listed
  have saw : regionOf label C.present (original.region σ) = original.seen :=
    valid.observations _ member σ solved
  obtain ⟨inC, notFoot⟩ := Finset.mem_sdiff.mp inRest
  show original.region σ (label o) = false
  cases inside : original.region σ (label o) with
  | false => rfl
  | true =>
      have seen : o ∈ original.seen := by
        rw [← saw]
        exact mem_regionOf.mpr ⟨inC, inside⟩
      exact absurd (mem_footprintSet_of_seen inOriginal seen) notFoot

theorem result_small_rest_separable {f : Firing T S O} {C : Configuration T O}
    {queries : List (PredicateQueryAdmission.Query T S O)} (valid : f.Valid A label C) :
    Separable A (f.result label (smallOf f queries C)) (restOf f queries C) := by
  refine ⟨?_, ?_⟩
  · change Disjoint (fire (footprintSet f queries) (f.selection.commit (T := T)))
      (C.present \ footprintSet f queries)
    refine Finset.disjoint_left.mpr fun o inFire inRest => ?_
    obtain ⟨inC, notFoot⟩ := Finset.mem_sdiff.mp inRest
    rcases mem_fire.mp inFire with ⟨inFoot, -⟩ | made
    · exact notFoot inFoot
    · exact Finset.disjoint_left.mp valid.firing.occurrences.fresh made inC
  · obtain ⟨σ, solved⟩ := valid.firing.consistent
    refine ⟨σ, ?_⟩
    rw [A.models_append, Firing.result_equations']
    rw [Firing.problem_eq'] at solved
    exact ⟨solved, ((A.models_append σ _ _).mp solved).1⟩

/-- **The configuration a firing with exact queries leaves is what it leaves at its footprint,
beside the rest.** -/
theorem result_small_rest_sameUpTo {f : Firing T S O} {C : Configuration T O}
    {queries : List (PredicateQueryAdmission.Query T S O)}
    (exact : f.queries = queries.map PredicateQueryAdmission.Query.toRegion)
    (valid : f.Valid A label C) :
    SameUpTo A (tensor (f.result label (smallOf f queries C)) (restOf f queries C))
      (f.result label C) := by
  have sub := footprintSet_subset A label exact valid
  refine ⟨fun σ => ?_, ?_⟩
  · change A.Models σ ((f.result label (smallOf f queries C)).equations ++ C.equations) ↔
      A.Models σ (f.result label C).equations
    rw [A.models_append, Firing.result_equations', Firing.result_equations', A.models_append,
      A.models_append]
    exact ⟨fun ⟨⟨c, a⟩, _⟩ => ⟨c, a⟩, fun ⟨c, a⟩ => ⟨⟨c, a⟩, c⟩⟩
  · change fire (footprintSet f queries) (f.selection.commit (T := T)) ∪
        (C.present \ footprintSet f queries) = fire C.present (f.selection.commit (T := T))
    ext o
    simp only [Finset.mem_union, mem_fire, Finset.mem_sdiff]
    constructor
    · rintro ((⟨inFoot, notTaken⟩ | made) | ⟨inC, notFoot⟩)
      · exact Or.inl ⟨sub inFoot, notTaken⟩
      · exact Or.inr made
      · refine Or.inl ⟨inC, fun taken => notFoot (mem_footprintSet_of_taken ?_)⟩
        simpa [Selection.commit] using taken
    · rintro (⟨inC, notTaken⟩ | made)
      · by_cases inFoot : o ∈ footprintSet f queries
        · exact Or.inl (Or.inl ⟨inFoot, notTaken⟩)
        · exact Or.inr ⟨inC, inFoot⟩
      · exact Or.inl (Or.inr made)

end Footprint

/-! ## Soundness and completeness -/

section Logic

variable (A : SubstitutionAction T S) (label : O → T)

/-- **A framed small step of a program**: a firing of the program with exact queries, admitted at
its footprint configuration, beside a frame separable from that configuration before and after. -/
def FramedStep (F : Set (Firing T S O)) (C D : Configuration T O) : Prop :=
  ∃ f ∈ F, ∃ queries : List (PredicateQueryAdmission.Query T S O),
    f.queries = queries.map PredicateQueryAdmission.Query.toRegion ∧
    ∃ M E : Configuration T O, M.present = footprintSet f queries ∧ f.Valid A label M ∧
      Separable A M E ∧ Separable A (f.result label M) E ∧
      SameUpTo A (tensor M E) C ∧ SameUpTo A (tensor (f.result label M) E) D

/-- **Derivations**: framed small steps in sequence, up to classes. -/
inductive Derives (F : Set (Firing T S O)) : Configuration T O → Configuration T O → Prop
  | refl {C D : Configuration T O} : A.Consistent C.equations → SameUpTo A C D → Derives F C D
  | step {C D E : Configuration T O} : FramedStep A label F C D → Derives F D E → Derives F C E

/-- **Runs of a program** reaching a class. -/
def ProgramReaches (F : Set (Firing T S O)) (C D : Configuration T O) : Prop :=
  ∃ w : List (Firing T S O), (∀ f ∈ w, f ∈ F) ∧ Executable A label C w ∧
    SameUpTo A (follow label C w) D

/-- **Every step of a firing with exact queries is a framed small step.** -/
theorem framedStep_of_valid {F : Set (Firing T S O)} {f : Firing T S O} {C : Configuration T O}
    {queries : List (PredicateQueryAdmission.Query T S O)} (member : f ∈ F)
    (exact : f.queries = queries.map PredicateQueryAdmission.Query.toRegion)
    (valid : f.Valid A label C) (antitone : AntitoneGuards f) :
    FramedStep A label F C (f.result label C) :=
  ⟨f, member, queries, exact, smallOf f queries C, restOf f queries C, rfl,
    small_valid A label exact valid antitone, small_rest_separable A label valid,
    result_small_rest_separable A label valid, small_rest_sameUpTo A label exact valid,
    result_small_rest_sameUpTo A label exact valid⟩

/-- Runs of firings with exact queries are derivations. -/
theorem reaches_derives {F : Set (Firing T S O)} (antitone : ∀ f ∈ F, AntitoneGuards f)
    (exactAll : ∀ f ∈ F, ∃ queries : List (PredicateQueryAdmission.Query T S O),
      f.queries = queries.map PredicateQueryAdmission.Query.toRegion) :
    ∀ (w : List (Firing T S O)) {C D : Configuration T O}, (∀ f ∈ w, f ∈ F) →
      Executable A label C w → SameUpTo A (follow label C w) D → Derives A label F C D
  | [], _, _, _, runs, same => .refl runs same
  | f :: w, _, _, inF, runs, same => by
      obtain ⟨queries, isExact⟩ := exactAll f (inF f List.mem_cons_self)
      exact .step (framedStep_of_valid A label (inF f List.mem_cons_self) isExact runs.1
          (antitone f (inF f List.mem_cons_self)))
        (reaches_derives antitone exactAll w (fun g member => inF g (List.mem_cons_of_mem f member))
          runs.2 same)

/-- **Soundness**: every run of a program whose guards survive removing rows, and whose queries are
exact, is a derivation. -/
theorem programReaches_derives {F : Set (Firing T S O)} (antitone : ∀ f ∈ F, AntitoneGuards f)
    (exactAll : ∀ f ∈ F, ∃ queries : List (PredicateQueryAdmission.Query T S O),
      f.queries = queries.map PredicateQueryAdmission.Query.toRegion)
    {C D : Configuration T O} (reaches : ProgramReaches A label F C D) : Derives A label F C D := by
  obtain ⟨w, inF, runs, same⟩ := reaches
  exact reaches_derives A label antitone exactAll w inF runs same

/-- **A framed small step of a query-free firing is a step.** -/
theorem step_of_framedStep {F : Set (Firing T S O)} (free : ∀ f ∈ F, QueryFree f)
    {C D : Configuration T O} (framed : FramedStep A label F C D) :
    ∃ f ∈ F, f.Valid A label C ∧ SameUpTo A (f.result label C) D := by
  obtain ⟨f, member, -, -, M, E, -, valid, sep, after, start, finish⟩ := framed
  have framedValid := (free f member).valid_frame A label valid after
  refine ⟨f, member, (Firing.valid_congr A label start).mp framedValid, ?_⟩
  exact (f.result_congr A label (sameUpTo_symm A start)).trans A
    ((result_frame A label valid sep.1).trans A finish)

/-- **Completeness for the query-free fragment**: every derivation is a run of the program. -/
theorem derives_reaches {F : Set (Firing T S O)} (free : ∀ f ∈ F, QueryFree f)
    {C D : Configuration T O} (derives : Derives A label F C D) : ProgramReaches A label F C D := by
  induction derives with
  | refl consistent same => exact ⟨[], fun _ member => (by cases member), consistent, same⟩
  | step framed _ ih =>
      obtain ⟨f, member, valid, same⟩ := step_of_framedStep A label free framed
      obtain ⟨w, inF, runs, ends⟩ := ih
      refine ⟨f :: w, ?_, ⟨valid, (executable_congr A label w same).mpr runs⟩,
        (follow_congr A label w same).trans A ends⟩
      intro g inG
      rcases List.mem_cons.mp inG with rfl | later
      · exact member
      · exact inF g later

/-- **Soundness and completeness for the query-free fragment.** -/
theorem derives_iff_reaches {F : Set (Firing T S O)} (free : ∀ f ∈ F, QueryFree f)
    {C D : Configuration T O} : Derives A label F C D ↔ ProgramReaches A label F C D :=
  ⟨derives_reaches A label free,
    programReaches_derives A label (fun f member => (free f member).antitoneGuards)
      (fun f member => ⟨[], (free f member).queries⟩)⟩

end Logic

/-! ## Program logic: exact assertions, sequencing, consequence -/

section Program

variable (A : SubstitutionAction T S) (label : O → T)

omit [DecidableEq O] in
/-- **The exact assertion** of a class. -/
def exactly (C₀ : Configuration T O) : Assertion T O := fun C => SameUpTo A C₀ C

/-- A run from a configuration is a triple of exact assertions. -/
theorem triple_exactly {C₀ : Configuration T O} {w : List (Firing T S O)}
    (runs : Executable A label C₀ w) :
    Triple A label (exactly A C₀) w (exactly A (follow label C₀ w)) :=
  fun _ same => ⟨(executable_congr A label w same).mp runs, follow_congr A label w same⟩

/-- **Sequencing.** -/
theorem triple_append {P Q R : Assertion T O} {u v : List (Firing T S O)}
    (first : Triple A label P u Q) (second : Triple A label Q v R) :
    Triple A label P (u ++ v) R := by
  intro C hP
  obtain ⟨runsU, hQ⟩ := first C hP
  obtain ⟨runsV, hR⟩ := second _ hQ
  refine ⟨executable_append' A label C u v runsU runsV, ?_⟩
  rw [follow_append']
  exact hR

/-- **Consequence.** -/
theorem triple_mono {P P' Q Q' : Assertion T O} {w : List (Firing T S O)}
    (triple : Triple A label P w Q) (pre : ∀ C, P' C → P C) (post : ∀ C, Q C → Q' C) :
    Triple A label P' w Q' :=
  fun C hP => ⟨(triple C (pre C hP)).1, post _ (triple C (pre C hP)).2⟩

/-- The tensor of separable representatives satisfies the separating conjunction of their exact
assertions. -/
theorem star_exactly {C D : Configuration T O} (sep : Separable A C D) :
    star A (exactly A C) (exactly A D) (tensor C D) :=
  ⟨C, D, sep, SameUpTo.refl A _, SameUpTo.refl A C, SameUpTo.refl A D⟩

end Program

/-! ## Authority over regions -/

section Authority

variable (A : SubstitutionAction T S) (label : O → T)

omit [DecidableEq O] in
/-- **A configuration with authority over regions**: the regions whose complete contents it
owns. -/
structure Owned (T : Type uT) (O : Type uO) where
  configuration : Configuration T O
  authority : List (T → Bool)

/-- The composite of owned configurations. -/
def Owned.tensor (x y : Owned T O) : Owned T O :=
  ⟨AnnotatedRuns.tensor x.configuration y.configuration, x.authority ++ y.authority⟩

omit [DecidableEq O] in
/-- No occurrence of `C` lies in a region of the list. -/
def Outside (regions : List (T → Bool)) (C : Configuration T O) : Prop :=
  ∀ region ∈ regions, ∀ o ∈ C.present, region (label o) = false

omit [DecidableEq O] in
/-- **Separability with authority**: separable configurations, and neither has an occurrence in a
region the other owns. -/
def OwnedSeparable (x y : Owned T O) : Prop :=
  Separable A x.configuration y.configuration ∧ Outside label x.authority y.configuration ∧
    Outside label y.authority x.configuration

omit [DecidableEq O] in
theorem ownedSeparable_comm {x y : Owned T O} :
    OwnedSeparable A label x y ↔ OwnedSeparable A label y x :=
  ⟨fun sep => ⟨(separable_comm A).mp sep.1, sep.2.2, sep.2.1⟩,
    fun sep => ⟨(separable_comm A).mp sep.1, sep.2.2, sep.2.1⟩⟩

theorem outside_tensor_iff {regions : List (T → Bool)} {C D : Configuration T O} :
    Outside label regions (AnnotatedRuns.tensor C D) ↔
      Outside label regions C ∧ Outside label regions D := by
  constructor
  · intro outside
    exact ⟨fun region member o present => outside region member o (Finset.mem_union_left _ present),
      fun region member o present => outside region member o (Finset.mem_union_right _ present)⟩
  · rintro ⟨outC, outD⟩ region member o present
    rcases Finset.mem_union.mp present with inC | inD
    · exact outC region member o inC
    · exact outD region member o inD

omit [DecidableEq O] in
theorem outside_append_iff {regions regions' : List (T → Bool)} {C : Configuration T O} :
    Outside label (regions ++ regions') C ↔ Outside label regions C ∧ Outside label regions' C := by
  constructor
  · intro outside
    exact ⟨fun region member => outside region (List.mem_append_left _ member),
      fun region member => outside region (List.mem_append_right _ member)⟩
  · rintro ⟨out, out'⟩ region member
    rcases List.mem_append.mp member with inFirst | inSecond
    · exact out region inFirst
    · exact out' region inSecond

/-- **Associativity of separability with authority.** -/
theorem ownedSeparable_assoc {x y z : Owned T O} :
    (OwnedSeparable A label x y ∧ OwnedSeparable A label (x.tensor y) z) ↔
      (OwnedSeparable A label y z ∧ OwnedSeparable A label x (y.tensor z)) := by
  unfold OwnedSeparable Owned.tensor
  simp only [outside_tensor_iff, outside_append_iff]
  constructor
  · rintro ⟨⟨sepXY, xOutY, yOutX⟩, sepXYZ, ⟨xOutZ, yOutZ⟩, zOutX, zOutY⟩
    obtain ⟨sepYZ, sepXYZ'⟩ := (separable_assoc A).mp ⟨sepXY, sepXYZ⟩
    exact ⟨⟨sepYZ, yOutZ, zOutY⟩, sepXYZ', ⟨xOutY, xOutZ⟩, yOutX, zOutX⟩
  · rintro ⟨⟨sepYZ, yOutZ, zOutY⟩, sepXYZ', ⟨xOutY, xOutZ⟩, yOutX, zOutX⟩
    obtain ⟨sepXY, sepXYZ⟩ := (separable_assoc A).mpr ⟨sepYZ, sepXYZ'⟩
    exact ⟨⟨sepXY, xOutY, yOutX⟩, sepXYZ, ⟨xOutZ, yOutZ⟩, zOutX, zOutY⟩

omit [DecidableEq O] in
/-- A firing observes under the authority of an owned configuration when each of its predicate
queries is a fixed query of an owned region. -/
def ObservesUnder (x : Owned T O) (f : Firing T S O) : Prop :=
  ∀ query ∈ f.queries, ∃ region ∈ x.authority, ∀ σ : S, query.region σ = region

/-- **With authority, query firings are local**: a firing admitted at an owned configuration whose
regions it observes is admitted beside every separable owned frame compatible with what it
leaves, whatever its queries observe. -/
theorem owned_valid_frame {f : Firing T S O} {x y : Owned T O}
    (guards : ∀ check ∈ f.rule.checks, ∃ left right, check = .equal left right)
    (observes : ObservesUnder x f) (valid : f.Valid A label x.configuration)
    (sep : OwnedSeparable A label x y)
    (after : Separable A (f.result label x.configuration) y.configuration) :
    f.Valid A label (AnnotatedRuns.tensor x.configuration y.configuration) := by
  refine valid_tensor_of_outside A label guards valid after ?_
  intro query member σ _ o inY
  obtain ⟨region, owned, fixed⟩ := observes query member
  rw [fixed σ]
  exact sep.2.1 region owned o inY

end Authority

end SeparationRuns

open SeparationRuns

#print axioms mem_seenSet
#print axioms QueryFree.antitoneGuards
#print axioms footprintSet_subset
#print axioms small_rest_sameUpTo
#print axioms small_rest_separable
#print axioms small_valid
#print axioms rest_blind_at_cut
#print axioms result_small_rest_separable
#print axioms result_small_rest_sameUpTo
#print axioms framedStep_of_valid
#print axioms reaches_derives
#print axioms programReaches_derives
#print axioms step_of_framedStep
#print axioms derives_reaches
#print axioms derives_iff_reaches
#print axioms triple_exactly
#print axioms triple_append
#print axioms triple_mono
#print axioms star_exactly
#print axioms ownedSeparable_comm
#print axioms outside_tensor_iff
#print axioms outside_append_iff
#print axioms ownedSeparable_assoc
#print axioms owned_valid_frame

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
