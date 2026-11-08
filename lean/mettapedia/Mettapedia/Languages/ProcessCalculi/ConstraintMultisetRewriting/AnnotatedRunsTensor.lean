import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsPaths
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsMetering

/-!
# The partial tensor of runs with local configurations

A round (`AnnotatedRunsRounds.Round`) is the tensor of single firings at one configuration. Here
the tensor is taken of **whole runs**, each from its own local configuration.

## Local configurations

The tensor of two configurations has both stores of equations and both spaces of occurrences
(`tensor`). It is associative and unital on the nose (`tensor_assoc`, `tensor_unit_left`,
`tensor_unit_right`) and symmetric up to the solutions of its store (`tensor_comm`).

## Separated runs

Two runs `r₁` from `C₁` and `r₂` from `C₂` are **separated** (`Separated`) when

* their spaces, the present occurrences and everything the run makes, are disjoint;
* each run is blind to the other's space: no pattern scanned by its guards and no space observed by
  its predicate queries contains the label of an occurrence there, at any solution;
* their **joint store**, both configurations' equations and every firing's equations, is
  consistent.

Equations may share variables across the two runs; only joint consistency is asked.

## The partial tensor

* **Tensor of whole runs** (`tensor_executable`): separated runs run one after the other from the
  tensor of their configurations, and reach the tensor of their ends.
* **Definedness is joint consistency** (`tensor_defined_iff`): for runs with disjoint spaces that are
  blind to each other, the tensor run exists exactly when the joint store is consistent. It is a
  property of the two runs together, never of each alone
  (`TensorControls.tensor_undefined_by_equations`).
* **Symmetry beyond single swaps** (`tensor_interchange`): `r₁ ++ r₂` and `r₂ ++ r₁` are one
  contextual trace. Every firing of `r₂` moves past every firing of `r₁`, each swap a round where it
  stands (`bubble_right`).
* **The interchange law** (`interchange_law`): `(r₁ ⊗ r₂) ; (s₁ ⊗ s₂)` and
  `(r₁ ; s₁) ⊗ (r₂ ; s₂)` are one contextual trace.
* **Blindness is needed** (`TensorControls.blindness_needed`): a maker and a predicate query of the
  maker's space have disjoint spaces and a consistent joint store, and only one order runs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open MeTTaCalculus.OccurrenceCommits (regionOf mem_regionOf fire mem_fire fire_union_frame)
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-! ## Local configurations and their tensor -/

section Configurations

/-- **The tensor of two local configurations**: both stores of equations, both spaces. -/
def tensor (C D : Configuration T O) : Configuration T O :=
  ⟨C.equations ++ D.equations, C.present ∪ D.present⟩

/-- The empty local configuration. -/
def unitConfiguration : Configuration T O := ⟨[], ∅⟩

theorem tensor_assoc (C D E : Configuration T O) :
    tensor (tensor C D) E = tensor C (tensor D E) := by
  simp [tensor, List.append_assoc, Finset.union_assoc]

theorem tensor_unit_left (C : Configuration T O) : tensor unitConfiguration C = C := by
  cases C
  simp [tensor, unitConfiguration]

theorem tensor_unit_right (C : Configuration T O) : tensor C unitConfiguration = C := by
  cases C
  simp [tensor, unitConfiguration]

theorem tensor_comm (A : SubstitutionAction T S) (C D : Configuration T O) :
    SameUpTo A (tensor C D) (tensor D C) :=
  ⟨fun σ => by simp only [tensor, A.models_append]; exact and_comm, Finset.union_comm _ _⟩

/-- The occurrences a run makes. -/
def madeBy (w : List (Firing T S O)) : Finset O := (w.flatMap fun f => f.selection.made).toFinset

/-- **The space of a run** from a configuration: its present occurrences and everything it makes. -/
def space (C : Configuration T O) (w : List (Firing T S O)) : Finset O := C.present ∪ madeBy w

theorem madeBy_cons (f : Firing T S O) (w : List (Firing T S O)) :
    madeBy (f :: w) = f.selection.made.toFinset ∪ madeBy w := by
  simp [madeBy, List.toFinset_append]

theorem madeBy_append (u v : List (Firing T S O)) : madeBy (u ++ v) = madeBy u ∪ madeBy v := by
  simp [madeBy, List.toFinset_append]

end Configurations

/-! ## Blindness and the frame law with more equations -/

section Frame

variable (A : SubstitutionAction T S) (label : O → T)

/-- **A firing blind to a set of occurrences**: no pattern scanned by its guards and no space observed by its
predicate queries contains the label of one of them, at any solution. -/
structure BlindTo (frame : Finset O) (f : Firing T S O) : Prop where
  checks : ∀ check ∈ f.rule.checks, ∀ pattern, checkScanned check = some pattern →
    ∀ σ : S, ∀ o ∈ frame, ¬ A.E (A.apply σ pattern) (A.apply σ (label o))
  queries : ∀ query ∈ f.queries, ∀ σ : S, ∀ o ∈ frame, query.region σ (label o) = false

variable {A label} in
omit [DecidableEq O] in
theorem BlindTo.mono {frame frame' : Finset O} {f : Firing T S O}
    (blind : BlindTo A label frame f) (sub : frame' ⊆ frame) : BlindTo A label frame' f :=
  ⟨fun check member pattern scanned σ o inFrame =>
      blind.checks check member pattern scanned σ o (sub inFrame),
    fun query member σ o inFrame => blind.queries query member σ o (sub inFrame)⟩

omit [DecidableEq O] in
/-- A guard-free firing without predicate queries is blind to everything. -/
theorem blindTo_of_plain {frame : Finset O} {f : Firing T S O} (checks : f.rule.checks = [])
    (queries : f.queries = []) : BlindTo A label frame f :=
  ⟨fun check member => (by rw [checks] at member; cases member),
    fun query member => (by rw [queries] at member; cases member)⟩

theorem check_holds_union {σ : S} {store frame : Finset O} {check : Check T}
    (blind : ∀ pattern, checkScanned check = some pattern →
      ∀ o ∈ frame, ¬ A.E (A.apply σ pattern) (A.apply σ (label o)))
    (holds : check.Holds A σ label store) : check.Holds A σ label (store ∪ frame) := by
  cases check with
  | equal left right => exact holds
  | absent pattern =>
      intro o member
      rcases Finset.mem_union.mp member with inStore | inFrame
      · exact holds o inStore
      · exact blind pattern rfl o inFrame
  | count pattern number =>
      have same : Check.matches A σ label (store ∪ frame) pattern =
          Check.matches A σ label store pattern := by
        ext o
        simp only [Check.matches, Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨inStore | inFrame, matched⟩
          · exact ⟨inStore, matched⟩
          · exact absurd matched (blind pattern rfl o inFrame)
        · rintro ⟨inStore, matched⟩
          exact ⟨Or.inl inStore, matched⟩
      change (Check.matches A σ label (store ∪ frame) pattern).card = number
      rw [same]
      exact holds

theorem query_holds_union {σ : S} {store frame : Finset O} {query : PredicateQueryAdmission.Query T S O}
    (blind : ∀ o ∈ frame, query.region σ (label o) = false)
    (holds : regionOf label store (query.region σ) = query.seen) :
    regionOf label (store ∪ frame) (query.region σ) = query.seen := by
  rw [← holds]
  ext o
  simp only [mem_regionOf, Finset.mem_union]
  constructor
  · rintro ⟨inStore | inFrame, inRegion⟩
    · exact ⟨inStore, inRegion⟩
    · rw [blind o inFrame] at inRegion
      cases inRegion
  · rintro ⟨inStore, inRegion⟩
    exact ⟨Or.inl inStore, inRegion⟩

/-- **The frame law with more equations.** A firing admitted at `C` and blind to `frame` is admitted
at a configuration that adds `frame` to the space of `C` and refines its store, when its problem
there is consistent. -/
theorem Firing.valid_of_frame {f : Firing T S O} {C D : Configuration T O} {frame : Finset O}
    (present : D.present = C.present ∪ frame) (refines : A.Refines D.equations C.equations)
    (blind : BlindTo A label frame f) (apartMade : Disjoint f.selection.made.toFinset frame)
    (consistent : A.Consistent (f.selection.problem label f.rule D)) (valid : f.Valid A label C) :
    f.Valid A label D := by
  have older : ∀ σ, A.Models σ (f.selection.problem label f.rule D) →
      A.Models σ (f.selection.problem label f.rule C) := by
    intro σ solved
    rw [Firing.problem_eq' label f D, A.models_append] at solved
    rw [Firing.problem_eq' label f C, A.models_append]
    exact ⟨refines σ solved.1, solved.2⟩
  refine ⟨⟨valid.firing.take_distinct, valid.firing.output_distinct, valid.firing.take_length,
    valid.firing.read_length, valid.firing.outputs, ?_, consistent, ?_⟩, ?_⟩
  · rw [present]
    exact valid.firing.occurrences.frame_of_positive rfl apartMade
  · intro check member σ solved
    rw [present]
    exact check_holds_union A label (fun pattern scanned => blind.checks check member pattern scanned σ)
      (valid.firing.checks check member σ (older σ solved))
  · intro query member σ solved
    change regionOf label D.present (query.region σ) = query.seen
    rw [present]
    exact query_holds_union label (blind.queries query member σ)
      (valid.observations query member σ (older σ solved))

end Frame

/-! ## Separated runs -/

section Separated

variable (A : SubstitutionAction T S) (label : O → T)

/-- The joint store of two runs: both configurations' equations and every firing's. -/
def jointStore (C₁ : Configuration T O) (r₁ : List (Firing T S O)) (C₂ : Configuration T O)
    (r₂ : List (Firing T S O)) : EquationStore T :=
  C₁.equations ++ C₂.equations ++ (r₁.flatMap (Firing.added label) ++ r₂.flatMap (Firing.added label))

omit [DecidableEq O] in
theorem models_jointStore (σ : S) (C₁ : Configuration T O) (r₁ : List (Firing T S O))
    (C₂ : Configuration T O) (r₂ : List (Firing T S O)) :
    A.Models σ (jointStore label C₁ r₁ C₂ r₂) ↔
      A.Models σ C₁.equations ∧ A.Models σ C₂.equations ∧
        A.Models σ (r₁.flatMap (Firing.added label)) ∧ A.Models σ (r₂.flatMap (Firing.added label)) := by
  simp only [jointStore, A.models_append, and_assoc]

omit [DecidableEq O] in
theorem models_flatMap_cons (σ : S) (f : Firing T S O) (w : List (Firing T S O)) :
    A.Models σ ((f :: w).flatMap (Firing.added label)) ↔
      A.Models σ (f.added label) ∧ A.Models σ (w.flatMap (Firing.added label)) := by
  rw [List.flatMap_cons, A.models_append]

omit [DecidableEq O] in
theorem models_flatMap_append (σ : S) (u v : List (Firing T S O)) :
    A.Models σ ((u ++ v).flatMap (Firing.added label)) ↔
      A.Models σ (u.flatMap (Firing.added label)) ∧ A.Models σ (v.flatMap (Firing.added label)) := by
  rw [List.flatMap_append, A.models_append]

/-- **Separated runs**: disjoint spaces, each blind to the other's space, and a consistent joint
store. -/
structure Separated (C₁ : Configuration T O) (r₁ : List (Firing T S O)) (C₂ : Configuration T O)
    (r₂ : List (Firing T S O)) : Prop where
  left : Executable A label C₁ r₁
  right : Executable A label C₂ r₂
  apart : Disjoint (space C₁ r₁) (space C₂ r₂)
  leftBlind : ∀ f ∈ r₁, BlindTo A label (space C₂ r₂) f
  rightBlind : ∀ g ∈ r₂, BlindTo A label (space C₁ r₁) g
  joint : A.Consistent (jointStore label C₁ r₁ C₂ r₂)

/-- What a firing leaves stays in the space of the run it begins. -/
theorem space_result_subset (f : Firing T S O) (C : Configuration T O) (w : List (Firing T S O)) :
    space (f.result label C) w ⊆ space C (f :: w) := by
  intro o member
  rcases Finset.mem_union.mp member with present | made
  · change o ∈ fire C.present (f.selection.commit (T := T)) at present
    rcases mem_fire.mp present with ⟨inC, _⟩ | inMade
    · exact Finset.mem_union_left _ inC
    · refine Finset.mem_union_right _ ?_
      rw [madeBy_cons]
      exact Finset.mem_union_left _ (by simpa [Selection.commit] using inMade)
  · refine Finset.mem_union_right _ ?_
    rw [madeBy_cons]
    exact Finset.mem_union_right _ made

/-- A firing admitted at `C` takes, reads and makes only inside the space of the run it begins. -/
theorem footprint_subset {f : Firing T S O} {C : Configuration T O} (w : List (Firing T S O))
    (valid : f.Valid A label C) :
    f.selection.taken.toFinset ⊆ space C (f :: w) ∧ f.selection.read.toFinset ⊆ space C (f :: w) ∧
      f.selection.made.toFinset ⊆ space C (f :: w) := by
  refine ⟨fun o member => Finset.mem_union_left _ (valid.firing.occurrences.taken_subset member),
    fun o member => Finset.mem_union_left _ (valid.firing.occurrences.kept_subset member),
    fun o member => Finset.mem_union_right _ ?_⟩
  rw [madeBy_cons]
  exact Finset.mem_union_left _ member

variable {A label}

theorem Separated.symm {C₁ C₂ : Configuration T O} {r₁ r₂ : List (Firing T S O)}
    (separated : Separated A label C₁ r₁ C₂ r₂) : Separated A label C₂ r₂ C₁ r₁ := by
  refine ⟨separated.right, separated.left, separated.apart.symm, separated.rightBlind,
    separated.leftBlind, ?_⟩
  obtain ⟨σ, solved⟩ := separated.joint
  refine ⟨σ, (models_jointStore A label σ _ _ _ _).mpr ?_⟩
  obtain ⟨one, two, three, four⟩ := (models_jointStore A label σ _ _ _ _).mp solved
  exact ⟨two, one, four, three⟩

/-- Firing the first firing of the left run keeps the runs separated. -/
theorem Separated.tail_left {C₁ C₂ : Configuration T O} {f : Firing T S O}
    {r₁ r₂ : List (Firing T S O)} (separated : Separated A label C₁ (f :: r₁) C₂ r₂) :
    Separated A label (f.result label C₁) r₁ C₂ r₂ := by
  have shrink := space_result_subset label f C₁ r₁
  refine ⟨separated.left.2, separated.right, Finset.disjoint_of_subset_left shrink separated.apart,
    fun f' member => separated.leftBlind f' (List.mem_cons_of_mem _ member),
    fun g member => (separated.rightBlind g member).mono shrink, ?_⟩
  obtain ⟨σ, solved⟩ := separated.joint
  refine ⟨σ, (models_jointStore A label σ _ _ _ _).mpr ?_⟩
  obtain ⟨one, two, three, four⟩ := (models_jointStore A label σ _ _ _ _).mp solved
  obtain ⟨head, tail⟩ := (models_flatMap_cons A label σ f r₁).mp three
  refine ⟨?_, two, tail, four⟩
  rw [Firing.result_equations', A.models_append]
  exact ⟨one, head⟩

/-- Firing the first firing of the right run keeps the runs separated. -/
theorem Separated.tail_right {C₁ C₂ : Configuration T O} {g : Firing T S O}
    {r₁ r₂ : List (Firing T S O)} (separated : Separated A label C₁ r₁ C₂ (g :: r₂)) :
    Separated A label C₁ r₁ (g.result label C₂) r₂ :=
  separated.symm.tail_left.symm

/-- The first firing of the left run is admitted at the tensor. -/
theorem Separated.head_left_valid {C₁ C₂ : Configuration T O} {f : Firing T S O}
    {r₁ r₂ : List (Firing T S O)} (separated : Separated A label C₁ (f :: r₁) C₂ r₂) :
    f.Valid A label (tensor C₁ C₂) := by
  have valid := separated.left.1
  have madeIn := (footprint_subset A label r₁ valid).2.2
  refine Firing.valid_of_frame A label (C := C₁) rfl
    (fun σ solved => ((A.models_append σ _ _).mp solved).1)
    ((separated.leftBlind f List.mem_cons_self).mono Finset.subset_union_left)
    (Finset.disjoint_of_subset_left madeIn
      (Finset.disjoint_of_subset_right Finset.subset_union_left separated.apart)) ?_ valid
  obtain ⟨σ, solved⟩ := separated.joint
  obtain ⟨one, two, three, _⟩ := (models_jointStore A label σ _ _ _ _).mp solved
  refine ⟨σ, ?_⟩
  rw [Firing.problem_eq', A.models_append]
  exact ⟨(A.models_append σ _ _).mpr ⟨one, two⟩, ((models_flatMap_cons A label σ f r₁).mp three).1⟩

/-- The first firing of the right run is admitted at the tensor. -/
theorem Separated.head_right_valid {C₁ C₂ : Configuration T O} {g : Firing T S O}
    {r₁ r₂ : List (Firing T S O)} (separated : Separated A label C₁ r₁ C₂ (g :: r₂)) :
    g.Valid A label (tensor C₁ C₂) := by
  have valid := separated.right.1
  have madeIn := (footprint_subset A label r₂ valid).2.2
  refine Firing.valid_of_frame A label (C := C₂) (Finset.union_comm _ _)
    (fun σ solved => ((A.models_append σ _ _).mp solved).2)
    ((separated.rightBlind g List.mem_cons_self).mono Finset.subset_union_left)
    (Finset.disjoint_of_subset_left madeIn
      (Finset.disjoint_of_subset_right Finset.subset_union_left separated.apart.symm)) ?_ valid
  obtain ⟨σ, solved⟩ := separated.joint
  obtain ⟨one, two, _, four⟩ := (models_jointStore A label σ _ _ _ _).mp solved
  refine ⟨σ, ?_⟩
  rw [Firing.problem_eq', A.models_append]
  exact ⟨(A.models_append σ _ _).mpr ⟨one, two⟩, ((models_flatMap_cons A label σ g r₂).mp four).1⟩

variable (A label)

/-- A left firing at the tensor leaves the tensor of its result and the right configuration. -/
theorem tensor_result_left {f : Firing T S O} {C₁ C₂ : Configuration T O}
    (takenApart : Disjoint f.selection.taken.toFinset C₂.present) :
    SameUpTo A (f.result label (tensor C₁ C₂)) (tensor (f.result label C₁) C₂) := by
  refine ⟨fun σ => ?_, ?_⟩
  · show A.Models σ (f.result label (tensor C₁ C₂)).equations ↔
      A.Models σ ((f.result label C₁).equations ++ C₂.equations)
    rw [Firing.result_equations', Firing.result_equations']
    simp only [tensor, A.models_append]
    exact ⟨fun ⟨⟨one, two⟩, three⟩ => ⟨⟨one, three⟩, two⟩,
      fun ⟨⟨one, three⟩, two⟩ => ⟨⟨one, two⟩, three⟩⟩
  · change fire (C₁.present ∪ C₂.present) (f.selection.commit (T := T)) =
      fire C₁.present (f.selection.commit (T := T)) ∪ C₂.present
    exact fire_union_frame takenApart

/-- A right firing at the tensor leaves the tensor of the left configuration and its result. -/
theorem tensor_result_right {g : Firing T S O} {C₁ C₂ : Configuration T O}
    (takenApart : Disjoint g.selection.taken.toFinset C₁.present) :
    SameUpTo A (g.result label (tensor C₁ C₂)) (tensor C₁ (g.result label C₂)) := by
  refine ⟨fun σ => ?_, ?_⟩
  · show A.Models σ (g.result label (tensor C₁ C₂)).equations ↔
      A.Models σ (C₁.equations ++ (g.result label C₂).equations)
    rw [Firing.result_equations', Firing.result_equations']
    simp only [tensor, List.append_assoc]
  · change fire (C₁.present ∪ C₂.present) (g.selection.commit (T := T)) =
      C₁.present ∪ fire C₂.present (g.selection.commit (T := T))
    rw [Finset.union_comm C₁.present, fire_union_frame takenApart, Finset.union_comm]

theorem Separated.head_left_apart {C₁ C₂ : Configuration T O} {f : Firing T S O}
    {r₁ r₂ : List (Firing T S O)} (separated : Separated A label C₁ (f :: r₁) C₂ r₂) :
    Disjoint f.selection.taken.toFinset C₂.present :=
  Finset.disjoint_of_subset_left (footprint_subset A label r₁ separated.left.1).1
    (Finset.disjoint_of_subset_right Finset.subset_union_left separated.apart)

theorem Separated.head_right_apart {C₁ C₂ : Configuration T O} {g : Firing T S O}
    {r₁ r₂ : List (Firing T S O)} (separated : Separated A label C₁ r₁ C₂ (g :: r₂)) :
    Disjoint g.selection.taken.toFinset C₁.present :=
  Finset.disjoint_of_subset_left (footprint_subset A label r₂ separated.right.1).1
    (Finset.disjoint_of_subset_right Finset.subset_union_left separated.apart.symm)

end Separated

/-! ## The tensor of whole runs -/

section Tensor

variable (A : SubstitutionAction T S) (label : O → T)

theorem tensor_executable_right : ∀ (C₁ C₂ : Configuration T O) (r₂ : List (Firing T S O)),
    Separated A label C₁ [] C₂ r₂ →
      Executable A label (tensor C₁ C₂) r₂ ∧
        SameUpTo A (follow label (tensor C₁ C₂) r₂) (tensor C₁ (follow label C₂ r₂))
  | C₁, C₂, [], separated => by
      refine ⟨?_, SameUpTo.refl A _⟩
      obtain ⟨σ, solved⟩ := separated.joint
      obtain ⟨one, two, _, _⟩ := (models_jointStore A label σ _ _ _ _).mp solved
      exact ⟨σ, (A.models_append σ _ _).mpr ⟨one, two⟩⟩
  | C₁, C₂, g :: r₂, separated => by
      have same := tensor_result_right A label (C₁ := C₁) (C₂ := C₂)
        (separated.head_right_apart A label)
      obtain ⟨later, ends⟩ := tensor_executable_right C₁ (g.result label C₂) r₂ separated.tail_right
      exact ⟨⟨separated.head_right_valid, (executable_congr A label r₂ same).mpr later⟩,
        (follow_congr A label r₂ same).trans A ends⟩

/-- **The tensor of whole runs.** Separated runs run one after the other from the tensor of their
configurations, and reach the tensor of their ends. -/
theorem tensor_executable : ∀ (C₁ : Configuration T O) (r₁ : List (Firing T S O))
    (C₂ : Configuration T O) (r₂ : List (Firing T S O)), Separated A label C₁ r₁ C₂ r₂ →
      Executable A label (tensor C₁ C₂) (r₁ ++ r₂) ∧
        SameUpTo A (follow label (tensor C₁ C₂) (r₁ ++ r₂))
          (tensor (follow label C₁ r₁) (follow label C₂ r₂))
  | C₁, [], C₂, r₂, separated => tensor_executable_right A label C₁ C₂ r₂ separated
  | C₁, f :: r₁, C₂, r₂, separated => by
      have same := tensor_result_left A label (C₁ := C₁) (C₂ := C₂)
        (separated.head_left_apart A label)
      obtain ⟨later, ends⟩ := tensor_executable (f.result label C₁) r₁ C₂ r₂ separated.tail_left
      exact ⟨⟨separated.head_left_valid, (executable_congr A label _ same).mpr later⟩,
        (follow_congr A label _ same).trans A ends⟩

/-- **Definedness is joint consistency.** For runs with disjoint spaces that are blind to each
other, the tensor run exists exactly when their joint store is consistent. -/
theorem tensor_defined_iff {C₁ C₂ : Configuration T O} {r₁ r₂ : List (Firing T S O)}
    (left : Executable A label C₁ r₁) (right : Executable A label C₂ r₂)
    (apart : Disjoint (space C₁ r₁) (space C₂ r₂))
    (leftBlind : ∀ f ∈ r₁, BlindTo A label (space C₂ r₂) f)
    (rightBlind : ∀ g ∈ r₂, BlindTo A label (space C₁ r₁) g) :
    Executable A label (tensor C₁ C₂) (r₁ ++ r₂) ↔ A.Consistent (jointStore label C₁ r₁ C₂ r₂) := by
  constructor
  · intro executable
    obtain ⟨σ, solved⟩ := Executable.joint A label executable
    refine ⟨σ, (models_jointStore A label σ _ _ _ _).mpr ?_⟩
    simp only [jointProblem, tensor, A.models_append] at solved
    obtain ⟨⟨one, two⟩, rest⟩ := solved
    exact ⟨one, two, ((models_flatMap_append A label σ r₁ r₂).mp rest).1,
      ((models_flatMap_append A label σ r₁ r₂).mp rest).2⟩
  · intro joint
    exact (tensor_executable A label C₁ r₁ C₂ r₂ ⟨left, right, apart, leftBlind, rightBlind, joint⟩).1

end Tensor

/-! ## Interchange beyond single swaps -/

section Interchange

variable (A : SubstitutionAction T S) (label : O → T)

/-- **Round equivalence depends only on the class of the configuration.** -/
theorem RoundEquiv.congr {C D : Configuration T O} (same : SameUpTo A C D)
    {w w' : List (Firing T S O)} (equivalent : RoundEquiv A label C w w') :
    RoundEquiv A label D w w' := by
  induction equivalent with
  | rel _ _ swapped =>
      cases swapped with
      | swap u v f g isRound =>
          exact .rel _ _ (RoundSwap.swap u v f g
            ((Round.congr A label (follow_congr A label u same)).mp isRound))
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

/-- **The first firings of two separated runs form a round at the tensor.** -/
theorem Separated.head_round {C₁ C₂ : Configuration T O} {f g : Firing T S O}
    {r₁ r₂ : List (Firing T S O)} (separated : Separated A label C₁ (f :: r₁) C₂ (g :: r₂)) :
    Round A label (tensor C₁ C₂) [f, g] := by
  have fValid := separated.head_left_valid
  have gValid := separated.head_right_valid
  obtain ⟨fTaken, fRead, fMade⟩ := footprint_subset A label r₁ separated.left.1
  obtain ⟨gTaken, gRead, gMade⟩ := footprint_subset A label r₂ separated.right.1
  have apart := separated.apart
  have fBlind := separated.leftBlind f List.mem_cons_self
  have gBlind := separated.rightBlind g List.mem_cons_self
  have gWrites : ∀ o ∈ g.selection.taken ++ g.selection.made, o ∈ space C₂ (g :: r₂) := by
    intro o member
    rcases List.mem_append.mp member with taken | made
    · exact gTaken (List.mem_toFinset.mpr taken)
    · exact gMade (List.mem_toFinset.mpr made)
  have fWrites : ∀ o ∈ f.selection.taken ++ f.selection.made, o ∈ space C₁ (f :: r₁) := by
    intro o member
    rcases List.mem_append.mp member with taken | made
    · exact fTaken (List.mem_toFinset.mpr taken)
    · exact fMade (List.mem_toFinset.mpr made)
  refine ⟨?_, ?_, List.pairwise_pair.mpr ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x member
    rcases List.mem_pair.mp member with rfl | rfl
    · exact fValid
    · exact gValid
  · obtain ⟨σ, solved⟩ := separated.joint
    obtain ⟨one, two, three, four⟩ := (models_jointStore A label σ _ _ _ _).mp solved
    refine ⟨σ, ?_⟩
    simp only [jointProblem, tensor, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      A.models_append]
    exact ⟨⟨one, two⟩, ((models_flatMap_cons A label σ f r₁).mp three).1,
      ((models_flatMap_cons A label σ g r₂).mp four).1⟩
  · refine ⟨?_, ?_, ?_⟩
    · rintro (taken | made)
      · exact taken (Finset.disjoint_of_subset_left fTaken
          (Finset.disjoint_of_subset_right gTaken apart))
      · exact made (Finset.disjoint_of_subset_left fMade
          (Finset.disjoint_of_subset_right gMade apart))
    · rintro (kept | ⟨read, member, _⟩)
      · exact kept (Finset.disjoint_of_subset_left fTaken
          (Finset.disjoint_of_subset_right gRead apart))
      · simp [Selection.commit] at member
    · rintro (kept | ⟨read, member, _⟩)
      · exact kept (Finset.disjoint_of_subset_left gTaken
          (Finset.disjoint_of_subset_right fRead apart.symm))
      · simp [Selection.commit] at member
  · intro check member
    cases check with
    | equal left right => trivial
    | absent pattern =>
        intro o written ⟨σ, solved⟩
        exact fBlind.checks _ member pattern rfl σ o (gWrites o written)
          (solved _ (List.mem_append_right _ (List.mem_singleton_self _)))
    | count pattern number =>
        intro o written ⟨σ, solved⟩
        exact fBlind.checks _ member pattern rfl σ o (gWrites o written)
          (solved _ (List.mem_append_right _ (List.mem_singleton_self _)))
  · intro check member
    cases check with
    | equal left right => trivial
    | absent pattern =>
        intro o written ⟨σ, solved⟩
        exact gBlind.checks _ member pattern rfl σ o (fWrites o written)
          (solved _ (List.mem_append_right _ (List.mem_singleton_self _)))
    | count pattern number =>
        intro o written ⟨σ, solved⟩
        exact gBlind.checks _ member pattern rfl σ o (fWrites o written)
          (solved _ (List.mem_append_right _ (List.mem_singleton_self _)))
  · intro query member σ _ o written
    exact fBlind.queries query member σ o (gWrites o written)
  · intro query member σ _ o written
    exact gBlind.queries query member σ o (fWrites o written)

/-- **A firing of the right run moves past the whole left run**, one round at a time. -/
theorem bubble_right : ∀ (C₁ : Configuration T O) (r₁ : List (Firing T S O))
    (C₂ : Configuration T O) (g : Firing T S O) (r₂ : List (Firing T S O)),
    Separated A label C₁ r₁ C₂ (g :: r₂) →
      RoundEquiv A label (tensor C₁ C₂) (r₁ ++ g :: r₂) (g :: (r₁ ++ r₂))
  | _, [], _, _, _, _ => .refl _
  | C₁, f :: r₁, C₂, g, r₂, separated => by
      have later := bubble_right (f.result label C₁) r₁ C₂ g r₂ separated.tail_left
      have same := tensor_result_left A label (C₁ := C₁) (C₂ := C₂)
        (separated.head_left_apart A label)
      have moved : RoundEquiv A label (tensor C₁ C₂) (f :: (r₁ ++ g :: r₂)) (f :: g :: (r₁ ++ r₂)) :=
        RoundEquiv.cons A label (RoundEquiv.congr A label (sameUpTo_symm A same) later)
      exact .trans _ _ _ moved
        (.rel _ _ (RoundSwap.swap [] (r₁ ++ r₂) f g (Separated.head_round A label separated)))

/-- **Symmetry of the tensor beyond single swaps.** The tensor run of two separated runs and the
tensor run in the other order are one contextual trace. -/
theorem tensor_interchange : ∀ (C₁ : Configuration T O) (r₁ : List (Firing T S O))
    (C₂ : Configuration T O) (r₂ : List (Firing T S O)), Separated A label C₁ r₁ C₂ r₂ →
      RoundEquiv A label (tensor C₁ C₂) (r₁ ++ r₂) (r₂ ++ r₁)
  | C₁, r₁, C₂, [], _ => by
      rw [List.append_nil]
      exact .refl _
  | C₁, r₁, C₂, g :: r₂, separated => by
      have bubbled := bubble_right A label C₁ r₁ C₂ g r₂ separated
      have rest := tensor_interchange C₁ r₁ (g.result label C₂) r₂ separated.tail_right
      have same := tensor_result_right A label (C₁ := C₁) (C₂ := C₂)
        (separated.head_right_apart A label)
      exact .trans _ _ _ bubbled
        (RoundEquiv.cons A label (RoundEquiv.congr A label (sameUpTo_symm A same) rest))

/-! ### Prefixes of separated runs -/

theorem executable_append_left : ∀ (C : Configuration T O) (u v : List (Firing T S O)),
    Executable A label C (u ++ v) → Executable A label C u
  | _, [], v, executable => by
      cases v with
      | nil => exact executable
      | cons _ _ =>
          obtain ⟨σ, solved⟩ := executable.1.firing.consistent
          exact ⟨σ, (A.models_append σ _ _).mp (by
            rw [← Firing.problem_eq']
            exact solved) |>.1⟩
  | _, _ :: u, v, executable => ⟨executable.1, executable_append_left _ u v executable.2⟩

theorem executable_append_right : ∀ (C : Configuration T O) (u v : List (Firing T S O)),
    Executable A label C (u ++ v) → Executable A label (follow label C u) v
  | _, [], _, executable => executable
  | _, _ :: u, v, executable => executable_append_right _ u v executable.2

variable {A label}

/-- Dropping a prefix of the left run keeps the runs separated, from where the prefix leaves. -/
theorem Separated.drop_left : ∀ {C₁ : Configuration T O} (u : List (Firing T S O))
    {r₁ : List (Firing T S O)} {C₂ : Configuration T O} {r₂ : List (Firing T S O)},
    Separated A label C₁ (u ++ r₁) C₂ r₂ → Separated A label (follow label C₁ u) r₁ C₂ r₂
  | _, [], _, _, _, separated => separated
  | _, _ :: u, _, _, _, separated => Separated.drop_left u separated.tail_left

/-- Keeping a prefix of the left run keeps the runs separated. -/
theorem Separated.take_left {C₁ C₂ : Configuration T O} {r₁ s₁ r₂ : List (Firing T S O)}
    (separated : Separated A label C₁ (r₁ ++ s₁) C₂ r₂) : Separated A label C₁ r₁ C₂ r₂ := by
  have shrink : space C₁ r₁ ⊆ space C₁ (r₁ ++ s₁) := by
    intro o member
    rcases Finset.mem_union.mp member with present | made
    · exact Finset.mem_union_left _ present
    · exact Finset.mem_union_right _ (by rw [madeBy_append]; exact Finset.mem_union_left _ made)
  refine ⟨executable_append_left A label C₁ r₁ s₁ separated.left, separated.right,
    Finset.disjoint_of_subset_left shrink separated.apart,
    fun f member => separated.leftBlind f (List.mem_append_left _ member),
    fun g member => (separated.rightBlind g member).mono shrink, ?_⟩
  obtain ⟨σ, solved⟩ := separated.joint
  obtain ⟨one, two, three, four⟩ := (models_jointStore A label σ _ _ _ _).mp solved
  exact ⟨σ, (models_jointStore A label σ _ _ _ _).mpr
    ⟨one, two, ((models_flatMap_append A label σ r₁ s₁).mp three).1, four⟩⟩

/-- Keeping a prefix of the right run keeps the runs separated. -/
theorem Separated.take_right {C₁ C₂ : Configuration T O} {r₁ r₂ s₂ : List (Firing T S O)}
    (separated : Separated A label C₁ r₁ C₂ (r₂ ++ s₂)) : Separated A label C₁ r₁ C₂ r₂ :=
  separated.symm.take_left.symm

variable (A label)

/-- **The interchange law of the tensor.** For separated runs `r₁ ++ s₁` and `r₂ ++ s₂`, the
sequential composite of the tensors, `r₁ r₂ s₁ s₂`, and the tensor of the sequential composites,
`r₁ s₁ r₂ s₂`, are one contextual trace from the tensor of the configurations. -/
theorem interchange_law (C₁ C₂ : Configuration T O) (r₁ s₁ r₂ s₂ : List (Firing T S O))
    (separated : Separated A label C₁ (r₁ ++ s₁) C₂ (r₂ ++ s₂)) :
    RoundEquiv A label (tensor C₁ C₂) ((r₁ ++ r₂) ++ (s₁ ++ s₂)) ((r₁ ++ s₁) ++ (r₂ ++ s₂)) := by
  have middleSeparated : Separated A label (follow label C₁ r₁) s₁ C₂ r₂ :=
    (Separated.drop_left r₁ separated).take_right
  have prefixSeparated : Separated A label C₁ r₁ C₂ [] :=
    (separated.take_left (s₁ := s₁)).take_right (r₂ := []) (s₂ := r₂ ++ s₂)
  have prefixEnd := (tensor_executable A label C₁ r₁ C₂ [] prefixSeparated).2
  rw [List.append_nil] at prefixEnd
  have middle : RoundEquiv A label (follow label (tensor C₁ C₂) r₁) (r₂ ++ s₁) (s₁ ++ r₂) :=
    RoundEquiv.congr A label (sameUpTo_symm A prefixEnd)
      (.symm _ _ (tensor_interchange A label _ s₁ C₂ r₂ middleSeparated))
  have moved := RoundEquiv.append_right A label
    (RoundEquiv.append_left A label (tensor C₁ C₂) r₁ middle) s₂
  simpa [List.append_assoc] using moved

end Interchange

/-! ## The tensor is a partial operation on contextual traces -/

section Bifunctor

variable (A : SubstitutionAction T S) (label : O → T)

/-- **A round at a configuration stays a round beside a blind frame**, when the joint problem is
consistent. -/
theorem Round.tensor_frame {D E : Configuration T O} {round : List (Firing T S O)}
    (isRound : Round A label D round)
    (blind : ∀ f ∈ round, BlindTo A label E.present f)
    (apartMade : ∀ f ∈ round, Disjoint f.selection.made.toFinset E.present)
    (joint : A.Consistent (jointProblem label (tensor D E) round)) :
    Round A label (tensor D E) round := by
  have refines : A.Refines (tensor D E).equations D.equations :=
    fun σ solved => ((A.models_append σ _ _).mp solved).1
  refine ⟨fun f member => ?_, joint,
    isRound.compatible.imp fun pair => pair.of_refines A label refines⟩
  refine Firing.valid_of_frame A label (C := D) rfl refines (blind f member) (apartMade f member) ?_
    (isRound.valid f member)
  obtain ⟨σ, solved⟩ := joint
  refine ⟨σ, ?_⟩
  rw [Firing.problem_eq', A.models_append]
  rw [jointProblem, A.models_append] at solved
  exact ⟨solved.1, fun e inAdded => solved.2 e (List.mem_flatMap.mpr ⟨f, member, inAdded⟩)⟩

theorem made_subset_madeBy {f : Firing T S O} {w : List (Firing T S O)} (member : f ∈ w) :
    f.selection.made.toFinset ⊆ madeBy w := by
  intro o made
  exact List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨f, member, List.mem_toFinset.mp made⟩)

theorem madeBy_perm {u v : List (Firing T S O)} (perm : u.Perm v) : madeBy u = madeBy v := by
  unfold madeBy
  exact List.toFinset_eq_of_perm _ _ (perm.flatMap_right _)

variable {A label} in
/-- Separation depends on the left run only through its firings, once it runs. -/
theorem Separated.perm_left {C₁ C₂ : Configuration T O} {r₁ r₁' r₂ : List (Firing T S O)}
    (separated : Separated A label C₁ r₁ C₂ r₂) (runs : Executable A label C₁ r₁')
    (perm : r₁.Perm r₁') : Separated A label C₁ r₁' C₂ r₂ := by
  have sameSpace : space C₁ r₁' = space C₁ r₁ := by
    unfold space
    rw [madeBy_perm perm.symm]
  refine ⟨runs, separated.right, by rw [sameSpace]; exact separated.apart,
    fun f member => separated.leftBlind f (perm.symm.subset member),
    fun g member => by rw [sameSpace]; exact separated.rightBlind g member, ?_⟩
  obtain ⟨σ, solved⟩ := separated.joint
  obtain ⟨one, two, three, four⟩ := (models_jointStore A label σ _ _ _ _).mp solved
  exact ⟨σ, (models_jointStore A label σ _ _ _ _).mpr ⟨one, two,
    fun e member => three e ((perm.flatMap_right _).mem_iff.mpr member), four⟩⟩

variable {A label} in
theorem Separated.perm_right {C₁ C₂ : Configuration T O} {r₁ r₂ r₂' : List (Firing T S O)}
    (separated : Separated A label C₁ r₁ C₂ r₂) (runs : Executable A label C₂ r₂')
    (perm : r₂.Perm r₂') : Separated A label C₁ r₁ C₂ r₂' :=
  (separated.symm.perm_left runs perm).symm

/-- **One swap of the left run is a swap of the tensor run.** -/
theorem roundSwap_tensor_left {C₁ C₂ : Configuration T O} {w w' r₂ : List (Firing T S O)}
    (swapped : RoundSwap A label C₁ w w') (separated : Separated A label C₁ w C₂ r₂) :
    RoundSwap A label (tensor C₁ C₂) (w ++ r₂) (w' ++ r₂) := by
  cases swapped with
  | swap u v f g isRound =>
      have prefixSeparated : Separated A label C₁ u C₂ [] :=
        (separated.take_left (s₁ := f :: g :: v)).take_right (r₂ := []) (s₂ := r₂)
      have prefixEnd := (tensor_executable A label C₁ u C₂ [] prefixSeparated).2
      rw [List.append_nil] at prefixEnd
      have rest : Separated A label (follow label C₁ u) (f :: g :: v) C₂ r₂ :=
        Separated.drop_left u separated
      have inRest : ∀ x ∈ [f, g], x ∈ f :: g :: v := by
        intro x member
        rcases List.mem_pair.mp member with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
      have lifted : Round A label (tensor (follow label C₁ u) C₂) [f, g] := by
        refine Round.tensor_frame A label isRound
          (fun x member => (rest.leftBlind x (inRest x member)).mono Finset.subset_union_left)
          (fun x member => Finset.disjoint_of_subset_left
            ((made_subset_madeBy (inRest x member)).trans Finset.subset_union_right)
            (Finset.disjoint_of_subset_right Finset.subset_union_left rest.apart)) ?_
        obtain ⟨σ, solved⟩ := rest.joint
        obtain ⟨one, two, three, _⟩ := (models_jointStore A label σ _ _ _ _).mp solved
        obtain ⟨fAdded, more⟩ := (models_flatMap_cons A label σ f (g :: v)).mp three
        obtain ⟨gAdded, _⟩ := (models_flatMap_cons A label σ g v).mp more
        refine ⟨σ, ?_⟩
        simp only [jointProblem, tensor, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          A.models_append]
        exact ⟨⟨one, two⟩, fAdded, gAdded⟩
      have swappedTensor := RoundSwap.swap u (v ++ r₂) f g ((Round.congr A label prefixEnd).mpr lifted)
      simpa [List.append_assoc] using swappedTensor

/-- **The tensor respects contextual traces on the left.** -/
theorem tensor_respects_left {C₁ C₂ : Configuration T O} {r₁ r₁' r₂ : List (Firing T S O)}
    (equivalent : RoundEquiv A label C₁ r₁ r₁') :
    Separated A label C₁ r₁ C₂ r₂ → RoundEquiv A label (tensor C₁ C₂) (r₁ ++ r₂) (r₁' ++ r₂) := by
  induction equivalent with
  | rel _ _ swapped => exact fun separated => .rel _ _ (roundSwap_tensor_left A label swapped separated)
  | refl => exact fun _ => .refl _
  | symm _ _ first ih =>
      intro separated
      have runs := (RoundEquiv.executable A label first).1.mpr separated.left
      exact .symm _ _ (ih (separated.perm_left runs (RoundEquiv.perm A label first).symm))
  | trans _ _ _ first _ ih₁ ih₂ =>
      intro separated
      have runs := (RoundEquiv.executable A label first).1.mp separated.left
      exact .trans _ _ _ (ih₁ separated)
        (ih₂ (separated.perm_left runs (RoundEquiv.perm A label first)))

/-- **The tensor respects contextual traces on the right.** -/
theorem tensor_respects_right {C₁ C₂ : Configuration T O} {r₁ r₂ r₂' : List (Firing T S O)}
    (equivalent : RoundEquiv A label C₂ r₂ r₂') (separated : Separated A label C₁ r₁ C₂ r₂) :
    RoundEquiv A label (tensor C₁ C₂) (r₁ ++ r₂) (r₁ ++ r₂') := by
  have runs := (RoundEquiv.executable A label equivalent).1.mp separated.right
  have separated' := separated.perm_right runs (RoundEquiv.perm A label equivalent)
  have swapped := tensor_interchange A label C₁ r₁ C₂ r₂ separated
  have moved : RoundEquiv A label (tensor C₁ C₂) (r₂ ++ r₁) (r₂' ++ r₁) :=
    RoundEquiv.congr A label (tensor_comm A C₂ C₁)
      (tensor_respects_left A label equivalent separated.symm)
  have back := tensor_interchange A label C₁ r₁ C₂ r₂' separated'
  exact .trans _ _ _ swapped (.trans _ _ _ moved (.symm _ _ back))

/-- **The tensor is a partial operation on contextual traces.** Round-equivalent left runs and
round-equivalent right runs give round-equivalent tensor runs. -/
theorem tensor_respects {C₁ C₂ : Configuration T O} {r₁ r₁' r₂ r₂' : List (Firing T S O)}
    (left : RoundEquiv A label C₁ r₁ r₁') (right : RoundEquiv A label C₂ r₂ r₂')
    (separated : Separated A label C₁ r₁ C₂ r₂) :
    RoundEquiv A label (tensor C₁ C₂) (r₁ ++ r₂) (r₁' ++ r₂') := by
  have runs := (RoundEquiv.executable A label left).1.mp separated.left
  have separated' := separated.perm_left runs (RoundEquiv.perm A label left)
  exact .trans _ _ _ (tensor_respects_left A label left separated)
    (tensor_respects_right A label right separated')

end Bifunctor

/-! ## Controls -/

namespace TensorControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label Run taker reader zeros observer maker)

/-- Tells `X = 1`. -/
def tellOne : Run := ⟨⟨[], [], [(.var 0, .const 1)], [], []⟩, [], ⟨[], [], []⟩⟩

/-- Tells `X = 2`. -/
def tellTwo : Run := ⟨⟨[], [], [(.var 0, .const 2)], [], []⟩, [], ⟨[], [], []⟩⟩

def empty : Configuration (Term signature) Nat := ⟨[], ∅⟩

theorem tellOne_runs : Executable A label empty [tellOne] := by
  refine ⟨⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨fun _ => .const 1, ?_⟩, by simp [tellOne]⟩,
    by simp [tellOne]⟩, ⟨fun _ => .const 1, ?_⟩⟩
  · intro equation member
    have same : equation = (.var 0, .const 1) := by
      simpa [Selection.problem, Selection.equations, empty, tellOne] using member
    subst same
    rfl
  · intro equation member
    have same : equation = (.var 0, .const 1) := by
      simpa [Selection.problem, Selection.equations, Selection.result, Firing.result, empty,
        tellOne] using member
    subst same
    rfl

theorem tellTwo_runs : Executable A label empty [tellTwo] := by
  refine ⟨⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨fun _ => .const 2, ?_⟩, by simp [tellTwo]⟩,
    by simp [tellTwo]⟩, ⟨fun _ => .const 2, ?_⟩⟩
  · intro equation member
    have same : equation = (.var 0, .const 2) := by
      simpa [Selection.problem, Selection.equations, empty, tellTwo] using member
    subst same
    rfl
  · intro equation member
    have same : equation = (.var 0, .const 2) := by
      simpa [Selection.problem, Selection.equations, Selection.result, Firing.result, empty,
        tellTwo] using member
    subst same
    rfl

/-- **Negative control: definedness is a property of the two runs together.** The run telling
`X = 1` and the run telling `X = 2` each run, have empty spaces and no guards, and their tensor is
undefined: the joint store has no solution. -/
theorem tensor_undefined_by_equations :
    Executable A label empty [tellOne] ∧ Executable A label empty [tellTwo] ∧
      ¬ Executable A label (tensor empty empty) ([tellOne] ++ [tellTwo]) := by
  refine ⟨tellOne_runs, tellTwo_runs, ?_⟩
  intro executable
  obtain ⟨σ, solved⟩ := Executable.joint A label executable
  have one := solved (.var 0, .const 1) (by
    simp [jointProblem, Firing.added, GuardFreeProcessOrders.added, Selection.equations, tensor,
      empty, tellOne, tellTwo])
  have two := solved (.var 0, .const 2) (by
    simp [jointProblem, Firing.added, GuardFreeProcessOrders.added, Selection.equations, tensor,
      empty, tellOne, tellTwo])
  change σ 0 = .const 1 at one
  change σ 0 = .const 2 at two
  rw [one] at two
  injection two with two
  exact absurd two (by decide)

/-- **Negative control: blindness is needed.** The maker of a persistent atom and a predicate query
that no persistent atom is present have disjoint spaces and a consistent joint store, and only
the order with the query first runs: the query is not blind to the maker's space. -/
theorem blindness_needed :
    Disjoint (space AnnotatedRuns.Controls.empty [maker]) (space AnnotatedRuns.Controls.empty [observer]) ∧
      A.Consistent (jointStore label AnnotatedRuns.Controls.empty [maker]
        AnnotatedRuns.Controls.empty [observer]) ∧
      ¬ BlindTo A label (space AnnotatedRuns.Controls.empty [maker]) observer ∧
      ¬ Executable A label AnnotatedRuns.Controls.empty [maker, observer] ∧
      Executable A label AnnotatedRuns.Controls.empty [observer, maker] := by
  refine ⟨by decide, ⟨Subst.id signature, ?_⟩, fun blind => ?_,
    AnnotatedRuns.Controls.census_writer_one_order.2.2.2.2,
    AnnotatedRuns.Controls.census_writer_one_order.2.2.2.1⟩
  · intro equation member
    simp [jointStore, Firing.added, GuardFreeProcessOrders.added, Selection.equations,
      AnnotatedRuns.Controls.empty, maker, observer] at member
  · have := blind.queries _ List.mem_cons_self (Subst.id signature) 9 (by decide)
    revert this
    decide

/-- The taker's local configuration. -/
def takerSide : Configuration (Term signature) Nat := ⟨[], {0}⟩

/-- The reader's local configuration. -/
def readerSide : Configuration (Term signature) Nat := ⟨[], {1}⟩

theorem taker_runs : Executable A label takerSide [taker] := by
  refine ⟨⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [taker]⟩,
    by simp [taker]⟩, ⟨zeros, ?_⟩⟩
  · intro equation member
    have same : equation = (ConstraintMultisetRewriting.Controls.f (.const 0), label 0) := by
      simpa [Selection.problem, Selection.equations, takerSide, taker] using member
    subst same
    rfl
  · intro equation member
    have same : equation = (ConstraintMultisetRewriting.Controls.f (.const 0), label 0) := by
      simpa [Selection.problem, Selection.equations, Selection.result, Firing.result, takerSide,
        taker] using member
    subst same
    rfl

theorem reader_runs : Executable A label readerSide [reader] := by
  refine ⟨⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [reader]⟩,
    by simp [reader]⟩, ⟨zeros, ?_⟩⟩
  · intro equation member
    have same : equation = (.var 1, label 1) := by
      simpa [Selection.problem, Selection.equations, readerSide, reader] using member
    subst same
    rfl
  · intro equation member
    have same : equation = (.var 1, label 1) := by
      simpa [Selection.problem, Selection.equations, Selection.result, Firing.result, readerSide,
        reader] using member
    subst same
    rfl

/-- The taker and the reader, each from its own local configuration, are separated: their
equations share the variable `X`, and their joint store is consistent. -/
theorem taker_reader_separated : Separated A label takerSide [taker] readerSide [reader] := by
  refine ⟨taker_runs, reader_runs, by decide,
    fun f member => blindTo_of_plain A label (by simp at member; subst member; rfl)
      (by simp at member; subst member; rfl),
    fun g member => blindTo_of_plain A label (by simp at member; subst member; rfl)
      (by simp at member; subst member; rfl), ⟨zeros, ?_⟩⟩
  intro equation member
  have cases : equation = (ConstraintMultisetRewriting.Controls.f (.const 0), label 0) ∨
      equation = (.var 1, label 1) := by
    simpa [jointStore, Firing.added, GuardFreeProcessOrders.added, Selection.equations, takerSide,
      readerSide, taker, reader] using member
  rcases cases with rfl | rfl <;> rfl

/-- **Positive control: the tensor of two separated runs with a shared variable.** It runs, and its
two orders are one contextual trace. -/
theorem taker_reader_tensor :
    Executable A label (tensor takerSide readerSide) [taker, reader] ∧
      RoundEquiv A label (tensor takerSide readerSide) [taker, reader] [reader, taker] :=
  ⟨(tensor_executable A label _ [taker] _ [reader] taker_reader_separated).1,
    tensor_interchange A label _ [taker] _ [reader] taker_reader_separated⟩

end TensorControls

#print axioms tensor_assoc
#print axioms tensor_unit_left
#print axioms tensor_unit_right
#print axioms tensor_comm
#print axioms Firing.valid_of_frame
#print axioms Separated.symm
#print axioms Separated.tail_left
#print axioms Separated.head_left_valid
#print axioms Separated.head_right_valid
#print axioms tensor_result_left
#print axioms tensor_result_right
#print axioms tensor_executable
#print axioms tensor_defined_iff
#print axioms RoundEquiv.congr
#print axioms Separated.head_round
#print axioms bubble_right
#print axioms tensor_interchange
#print axioms interchange_law
#print axioms Round.tensor_frame
#print axioms Separated.perm_left
#print axioms roundSwap_tensor_left
#print axioms tensor_respects_left
#print axioms tensor_respects_right
#print axioms tensor_respects
#print axioms TensorControls.tensor_undefined_by_equations
#print axioms TensorControls.blindness_needed
#print axioms TensorControls.taker_reader_tensor

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
