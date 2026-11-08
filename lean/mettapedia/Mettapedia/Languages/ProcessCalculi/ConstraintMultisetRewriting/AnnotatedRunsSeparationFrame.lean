import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsSeparationAssertions

/-!
# Firings as local actions, and the frame rule for runs

## Local actions

A firing is a local action of the separation algebra in the sense of Calcagno, O'Hearn and Yang,
once its frame is compatible with it:

* **Safety monotonicity** (`valid_frame`): a firing admitted at `C` is admitted at `C ⊗ E` when it
  is blind to `E` and `E` is separable from the configuration it leaves. Query-free firings
  (`QueryFree`: no predicate query, equation guards only) are blind to everything
  (`QueryFree.blindTo`, `QueryFree.valid_frame`).
* **The frame property** (`result_frame`): the framed firing leaves the tensor of what it leaves and
  the frame.

The frame must be separable from the configuration the firing *leaves*, not only from the one it
starts from. Firings add knowledge, and a tell is not a frame-preserving update: `X = 1` and a
frame knowing `X = 2` are each fine and cannot meet (`SeparationControls.knowledge_frame_refused`).

## The frame rule for runs

`Triple P w Q`: from every configuration in `P` the run `w` executes and ends in `Q`.

* `FrameAlong C w E`: `E` is disjoint from the space of the run and its knowledge is compatible with
  the knowledge the run ends with; with an executable run, exactly `E` separable from every stage
  (`frameAlong_iff_stages`). Together with blindness it is R26's `Separated C w E []`
  (`separated_nil_iff`), so the framed run is R26's tensor (`executable_frame`).
* **The frame rule** (`frame_rule`): `{P} w {Q}` gives `{P ∗ R} w {Q ∗ R}` when every frame in `R`
  beside a configuration in `P` is blind to the run and a frame along it.
* For query-free runs blindness is automatic (`frame_rule_queryFree`), and frames without knowledge
  that avoid the identities the run makes are frames along every run (`frame_rule_spatial`): the
  classical frame rule. Frames whose knowledge the precondition already entails are frames along
  every query-free run that avoids their identities (`frame_rule_known`).
* **Up to renaming** (`frame_rule_renamed`): a spatial frame that collides with the identities a
  query-free run makes is kept once those identities are renamed apart, by a label-preserving
  bijection that fixes the start. The renamed run is the run up to the names it makes
  (`executable_rename`).

## Predicate queries break locality, exactly where the frame enters their region

* **Exactness** (`census_frame_iff`): a firing with equation guards admitted at `C` is admitted at
  `C ⊗ E` exactly when no query region contains an occurrence of `E` at a solution of the framed
  cut. It is the frame analogue of `census_after_iff`. For fixed queries: exactly when the frame
  changes no query region (`fixed_frame_iff`).
* **Regions are a homomorphism of the separation algebra** (`regionOf_tensor`): absence is
  multiplicative (`absent_tensor_iff`) and counts are additive (`count_tensor`).
* **The anti-frame** (`valid_restrict`): removing occurrences outside a firing's takes, reads and
  sightings never refuses it, when the removed part tells nothing and the firing has no count
  guard. Absence and queries are stable under restriction where positive reads are stable under
  extension.
* **Verdicts on a region** (`regionValues`, `frame_admitted_iff_values`): a firing whose one predicate
  query is a fixed query of a region is admitted beside a frame exactly when no verdict on the
  values the region carries changes. `AnnotatedRunsSeparationVerdicts` instantiates it at R33's
  paths, where `verdict_iff_query` says each such verdict is the verdict on what the query saw.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open MeTTaCalculus.OccurrenceCommits (PredicateQuery regionOf mem_regionOf fire mem_fire
  fire_union_frame made_subset_fire)
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO

namespace SeparationRuns

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-! ## Local actions -/

section Local

variable (A : SubstitutionAction T S) (label : O → T)

omit [DecidableEq O] in
/-- **The query-free fragment**: no predicate query, and every guard an equation. -/
structure QueryFree (f : Firing T S O) : Prop where
  queries : f.queries = []
  guards : ∀ check ∈ f.rule.checks, ∃ left right, check = .equal left right

omit [DecidableEq O] in
/-- A query-free firing is blind to every frame. -/
theorem QueryFree.blindTo {f : Firing T S O} (free : QueryFree f) (frame : Finset O) :
    BlindTo A label frame f :=
  ⟨fun check member pattern scanned => (by
      obtain ⟨left, right, rfl⟩ := free.guards check member
      cases scanned),
    fun query member => (by
      rw [free.queries] at member
      cases member)⟩

/-- The problem at a tensor has a solution when the configuration a firing leaves is compatible
with the frame. -/
theorem consistent_problem_tensor {f : Firing T S O} {C E : Configuration T O}
    (after : A.Consistent ((f.result label C).equations ++ E.equations)) :
    A.Consistent (f.selection.problem label f.rule (tensor C E)) := by
  obtain ⟨σ, solved⟩ := after
  refine ⟨σ, ?_⟩
  rw [Firing.problem_eq', A.models_append]
  rw [A.models_append, Firing.result_equations', A.models_append] at solved
  exact ⟨(A.models_append σ _ _).mpr ⟨solved.1.1, solved.2⟩, solved.1.2⟩

/-- What a firing makes is present where it leaves. -/
theorem made_disjoint_frame {f : Firing T S O} {C E : Configuration T O}
    (after : Disjoint (f.result label C).present E.present) :
    Disjoint (f.selection.commit (T := T)).made E.present :=
  Finset.disjoint_of_subset_left (made_subset_fire (store := C.present)
    (c := f.selection.commit (T := T))) after

/-- **Safety monotonicity.** A firing admitted at `C`, blind to `E`, is admitted at `C ⊗ E` when
`E` is separable from the configuration it leaves. -/
theorem valid_frame {f : Firing T S O} {C E : Configuration T O} (valid : f.Valid A label C)
    (blind : BlindTo A label E.present f) (after : Separable A (f.result label C) E) :
    f.Valid A label (tensor C E) :=
  Firing.valid_of_frame A label (C := C) rfl
    (fun σ solved => ((A.models_append σ _ _).mp solved).1) blind
    (made_disjoint_frame label after.1) (consistent_problem_tensor A label after.2) valid

/-- **The frame property.** The framed firing leaves the tensor of what it leaves and the frame. -/
theorem result_frame {f : Firing T S O} {C E : Configuration T O} (valid : f.Valid A label C)
    (apart : Disjoint C.present E.present) :
    SameUpTo A (f.result label (tensor C E)) (tensor (f.result label C) E) :=
  tensor_result_left A label
    (Finset.disjoint_of_subset_left valid.firing.occurrences.taken_subset apart)

/-- **Query-free firings are local actions.** -/
theorem QueryFree.valid_frame {f : Firing T S O} (free : QueryFree f) {C E : Configuration T O}
    (valid : f.Valid A label C) (after : Separable A (f.result label C) E) :
    f.Valid A label (tensor C E) :=
  SeparationRuns.valid_frame A label valid (free.blindTo A label E.present) after

end Local

/-! ## The frame rule for runs -/

section Runs

variable (A : SubstitutionAction T S) (label : O → T)

/-- **A frame along a run**: disjoint from the run's space, with knowledge compatible with the
knowledge the run ends with. -/
def FrameAlong (C : Configuration T O) (w : List (Firing T S O)) (E : Configuration T O) : Prop :=
  Disjoint (space C w) E.present ∧ A.Consistent ((follow label C w).equations ++ E.equations)

/-- **A frame along a run is a configuration separable from every stage of it.** -/
theorem frameAlong_iff_stages {C E : Configuration T O} {w : List (Firing T S O)} :
    FrameAlong A label C w E ↔ ∀ u, u <+: w → Separable A (follow label C u) E := by
  constructor
  · rintro ⟨apart, consistent⟩ u pu
    refine ⟨Finset.disjoint_of_subset_left
      ((follow_present_subset_space label C u).trans (space_mono_prefix pu)) apart, ?_⟩
    obtain ⟨σ, solved⟩ := consistent
    refine ⟨σ, ?_⟩
    rw [A.models_append, follow_equations, A.models_append] at solved ⊢
    exact ⟨⟨solved.1.1, models_prefix_added A label pu solved.1.2⟩, solved.2⟩
  · intro stages
    refine ⟨Finset.disjoint_left.mpr fun o inSpace inE => ?_, (stages w (List.prefix_refl _)).2⟩
    obtain ⟨u, pu, inU⟩ := (mem_space_iff_stage label C w o).mp inSpace
    exact Finset.disjoint_left.mp (stages u pu).1 inU inE

/-- **A frame along a run, with blindness, is R26's separation from the empty run.** -/
theorem separated_nil_iff {C E : Configuration T O} {w : List (Firing T S O)} :
    Separated A label C w E [] ↔
      Executable A label C w ∧ (∀ f ∈ w, BlindTo A label E.present f) ∧
        FrameAlong A label C w E := by
  have spaceE : space E ([] : List (Firing T S O)) = E.present := by simp [space, madeBy]
  have joint := SubstitutionAction.equivalent_consistent A (jointStore_equivalent A label C w E [])
  constructor
  · intro separated
    refine ⟨separated.left, fun f member => ?_, ?_, joint.mp separated.joint⟩
    · rw [← spaceE]
      exact separated.leftBlind f member
    · rw [← spaceE]
      exact separated.apart
  · rintro ⟨runs, blind, apart, consistent⟩
    refine ⟨runs, consistent_append_right A consistent, ?_, fun f member => ?_,
      fun g member => (by cases member), joint.mpr consistent⟩
    · rw [spaceE]
      exact apart
    · rw [spaceE]
      exact blind f member

/-- **The frame law for runs** is R26's tensor with the empty run. -/
theorem executable_frame {C E : Configuration T O} {w : List (Firing T S O)}
    (runs : Executable A label C w) (blind : ∀ f ∈ w, BlindTo A label E.present f)
    (along : FrameAlong A label C w E) :
    Executable A label (tensor C E) w ∧
      SameUpTo A (follow label (tensor C E) w) (tensor (follow label C w) E) := by
  have framed := tensor_executable A label C w E []
    ((separated_nil_iff A label).mpr ⟨runs, blind, along⟩)
  rw [List.append_nil] at framed
  exact framed

/-- **A Hoare triple for one run**: from every configuration in `P` the run executes and ends in
`Q`. -/
def Triple (P : Assertion T O) (w : List (Firing T S O)) (Q : Assertion T O) : Prop :=
  ∀ C, P C → Executable A label C w ∧ Q (follow label C w)

/-- **The frame rule for runs.** -/
theorem frame_rule {P Q R : Assertion T O} {w : List (Firing T S O)}
    (triple : Triple A label P w Q)
    (blind : ∀ C E, P C → R E → Separable A C E → ∀ f ∈ w, BlindTo A label E.present f)
    (along : ∀ C E, P C → R E → Separable A C E → FrameAlong A label C w E) :
    Triple A label (star A P R) w (star A Q R) := by
  rintro C' ⟨C, E, sep, same, hP, hR⟩
  obtain ⟨runs, hQ⟩ := triple C hP
  have alongCE := along C E hP hR sep
  obtain ⟨framed, ends⟩ := executable_frame A label runs (blind C E hP hR sep) alongCE
  exact ⟨(executable_congr A label w same).mp framed, follow label C w, E,
    ⟨Finset.disjoint_of_subset_left (follow_present_subset_space label C w) alongCE.1, alongCE.2⟩,
    (sameUpTo_symm A ends).trans A (follow_congr A label w same), hQ, hR⟩

/-- **The frame rule for query-free runs.** -/
theorem frame_rule_queryFree {P Q R : Assertion T O} {w : List (Firing T S O)}
    (triple : Triple A label P w Q) (free : ∀ f ∈ w, QueryFree f)
    (along : ∀ C E, P C → R E → Separable A C E → FrameAlong A label C w E) :
    Triple A label (star A P R) w (star A Q R) :=
  frame_rule A label triple (fun _ E _ _ _ f member => (free f member).blindTo A label E.present)
    along

/-- **The classical frame rule**: a query-free run keeps every frame without knowledge that avoids
the identities it makes. -/
theorem frame_rule_spatial {P Q R : Assertion T O} {w : List (Firing T S O)}
    (triple : Triple A label P w Q) (free : ∀ f ∈ w, QueryFree f)
    (spatialFrame : ∀ E, R E → A.Equivalent E.equations [] ∧ Disjoint (madeBy w) E.present) :
    Triple A label (star A P R) w (star A Q R) := by
  refine frame_rule_queryFree A label triple free fun C E hP hR sep => ⟨?_, ?_⟩
  · exact Finset.disjoint_union_left.mpr ⟨sep.1, (spatialFrame E hR).2⟩
  · obtain ⟨σ, solved⟩ := Executable.joint A label (triple C hP).1
    refine ⟨σ, (A.models_append σ _ _).mpr ⟨?_, ((spatialFrame E hR).1 σ).mpr (A.models_nil σ)⟩⟩
    rw [follow_equations]
    exact solved

/-- **Framing knowledge the precondition already has**: a query-free run keeps every frame that
avoids the identities it makes and whose knowledge every precondition beside it entails. Knowledge
that is merely compatible is not enough (`SeparationControls.knowledge_frame_refused`). -/
theorem frame_rule_known {P Q R : Assertion T O} {w : List (Firing T S O)}
    (triple : Triple A label P w Q) (free : ∀ f ∈ w, QueryFree f)
    (names : ∀ E, R E → Disjoint (madeBy w) E.present)
    (known : ∀ C E, P C → R E → A.Refines C.equations E.equations) :
    Triple A label (star A P R) w (star A Q R) := by
  refine frame_rule_queryFree A label triple free fun C E hP hR sep => ⟨?_, ?_⟩
  · exact Finset.disjoint_union_left.mpr ⟨sep.1, names E hR⟩
  · obtain ⟨σ, solved⟩ := Executable.joint A label (triple C hP).1
    refine ⟨σ, (A.models_append σ _ _).mpr ⟨?_, known C E hP hR σ ?_⟩⟩
    · rw [follow_equations]
      exact solved
    · exact ((A.models_append σ _ _).mp solved).1

/-- **The frame rule up to renaming.** A query-free run whose made identities may collide with a
spatial frame keeps the frame once those identities are renamed apart, by a label-preserving
bijection that fixes the start's occurrences and moves what the run makes off the frame. The
renamed run is the run up to the names it makes (`executable_rename`), and it ends in the renamed
end beside the frame. -/
theorem frame_rule_renamed {P Q R : Assertion T O} {w : List (Firing T S O)}
    (triple : Triple A label P w Q) (free : ∀ f ∈ w, QueryFree f)
    (empty : ∀ E, R E → A.Equivalent E.equations [])
    {C E : Configuration T O} (hP : P C) (hR : R E) (sep : Separable A C E)
    (π : O ≃ O) (keeps : ∀ o, label (π o) = label o) (fixes : C.present.map π.toEmbedding = C.present)
    (apart : Disjoint (madeBy (w.map (Firing.rename π))) E.present) :
    Executable A label (tensor C E) (w.map (Firing.rename π)) ∧
      SameUpTo A (follow label (tensor C E) (w.map (Firing.rename π)))
        (tensor (renameConfiguration π (follow label C w)) E) ∧ Q (follow label C w) := by
  have start : renameConfiguration π C = C := by
    show Configuration.mk C.equations (C.present.map π.toEmbedding) = C
    rw [fixes]
  obtain ⟨runs, hQ⟩ := triple C hP
  have renamedRuns : Executable A label C (w.map (Firing.rename π)) := by
    have renamed := (executable_rename A keeps C w).mpr runs
    rwa [start] at renamed
  have ends : follow label C (w.map (Firing.rename π)) = renameConfiguration π (follow label C w) := by
    have renamed := follow_rename keeps C w
    rwa [start] at renamed
  have renamedFree : ∀ f ∈ w.map (Firing.rename π), QueryFree f := by
    intro f member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact ⟨by simp [Firing.rename, (free original present).queries], (free original present).guards⟩
  have along : FrameAlong A label C (w.map (Firing.rename π)) E := by
    refine ⟨Finset.disjoint_union_left.mpr ⟨sep.1, apart⟩, ?_⟩
    obtain ⟨σ, solved⟩ := Executable.joint A label runs
    refine ⟨σ, (A.models_append σ _ _).mpr ⟨?_, ((empty E hR) σ).mpr (A.models_nil σ)⟩⟩
    rw [ends]
    show A.Models σ (follow label C w).equations
    rw [follow_equations]
    exact solved
  obtain ⟨framed, endsFramed⟩ := executable_frame A label renamedRuns
    (fun f member => (renamedFree f member).blindTo A label E.present) along
  refine ⟨framed, ?_, hQ⟩
  rw [← ends]
  exact endsFramed

end Runs

/-! ## Predicate queries: exactness, regions, the anti-frame -/

section Queries

variable (A : SubstitutionAction T S) (label : O → T)

/-- **A query is local exactly where the frame avoids its region**, at the framed cut. -/
theorem census_frame_iff {f : Firing T S O} {C E : Configuration T O}
    (guards : ∀ check ∈ f.rule.checks, ∃ left right, check = .equal left right)
    (valid : f.Valid A label C) (apart : Disjoint C.present E.present)
    (after : Separable A (f.result label C) E) :
    f.Valid A label (tensor C E) ↔
      ∀ query ∈ f.queries, ∀ σ, A.Models σ (f.selection.problem label f.rule (tensor C E)) →
        ∀ o ∈ E.present, query.region σ (label o) = false := by
  have older : ∀ σ, A.Models σ (f.selection.problem label f.rule (tensor C E)) →
      A.Models σ (f.selection.problem label f.rule C) := by
    intro σ solved
    rw [Firing.problem_eq', A.models_append] at solved ⊢
    exact ⟨((A.models_append σ _ _).mp solved.1).1, solved.2⟩
  constructor
  · intro framed query member σ solved o inE
    cases inside : query.region σ (label o) with
    | false => rfl
    | true =>
        exfalso
        have framedSaw : regionOf label (C.present ∪ E.present) (query.region σ) = query.seen :=
          framed.observations query member σ solved
        have saw : regionOf label C.present (query.region σ) = query.seen :=
          valid.observations query member σ (older σ solved)
        have seen : o ∈ query.seen := by
          rw [← framedSaw]
          exact mem_regionOf.mpr ⟨Finset.mem_union_right _ inE, inside⟩
        rw [← saw] at seen
        exact Finset.disjoint_left.mp apart (mem_regionOf.mp seen).1 inE
  · intro outside
    have firing := valid.firing
    have positive : f.selection.Valid A label f.rule (tensor C E) := by
      refine ⟨firing.take_distinct, firing.output_distinct, firing.take_length, firing.read_length,
        firing.outputs, firing.occurrences.frame_of_positive rfl (made_disjoint_frame label after.1),
        consistent_problem_tensor A label after.2, ?_⟩
      intro check member σ solved
      obtain ⟨left, right, rfl⟩ := guards check member
      exact firing.checks _ member σ (older σ solved)
    refine ⟨positive, fun query member σ solved => ?_⟩
    change regionOf label (C.present ∪ E.present) (query.region σ) = query.seen
    exact query_holds_union label (outside query member σ solved)
      (valid.observations query member σ (older σ solved))

/-- **Regions are a homomorphism of the separation algebra.** -/
theorem regionOf_tensor (region : T → Bool) (C E : Configuration T O) :
    regionOf label (tensor C E).present region =
      regionOf label C.present region ∪ regionOf label E.present region := by
  ext o
  simp only [mem_regionOf, tensor, Finset.mem_union, or_and_right]

/-- **Absence is multiplicative.** -/
theorem absent_tensor_iff (region : T → Bool) (C E : Configuration T O) :
    regionOf label (tensor C E).present region = ∅ ↔
      regionOf label C.present region = ∅ ∧ regionOf label E.present region = ∅ := by
  rw [regionOf_tensor, Finset.union_eq_empty]

/-- **Counts are additive.** -/
theorem count_tensor (region : T → Bool) {C E : Configuration T O}
    (apart : Disjoint C.present E.present) :
    (regionOf label (tensor C E).present region).card =
      (regionOf label C.present region).card + (regionOf label E.present region).card := by
  rw [regionOf_tensor]
  exact Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
    (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) apart))

/-- **For fixed queries: a firing is admitted beside a frame exactly when the frame changes no query
region.** -/
theorem fixed_frame_iff {f : Firing T S O} {C E : Configuration T O}
    {queries : List (PredicateQuery O T)}
    (fixed : f.queries = queries.map PredicateQueryAdmission.Query.fixed)
    (guards : ∀ check ∈ f.rule.checks, ∃ left right, check = .equal left right)
    (valid : f.Valid A label C) (apart : Disjoint C.present E.present)
    (after : Separable A (f.result label C) E) :
    f.Valid A label (tensor C E) ↔
      ∀ query ∈ queries,
        regionOf label (tensor C E).present query.region = regionOf label C.present query.region := by
  rw [census_frame_iff A label guards valid apart after]
  obtain ⟨σ₀, solved₀⟩ := consistent_problem_tensor A label after.2
  constructor
  · intro outside query member
    have inF : PredicateQueryAdmission.Query.fixed query ∈ f.queries := by
      rw [fixed]
      exact List.mem_map_of_mem member
    rw [regionOf_tensor]
    refine Finset.union_eq_left.mpr fun o inRegion => ?_
    have none := outside _ inF σ₀ solved₀ o (mem_regionOf.mp inRegion).1
    change query.region (label o) = false at none
    rw [(mem_regionOf.mp inRegion).2] at none
    cases none
  · intro unchanged query member σ _ o inE
    rw [fixed] at member
    obtain ⟨q, inQ, rfl⟩ := List.mem_map.mp member
    change q.region (label o) = false
    cases inside : q.region (label o) with
    | false => rfl
    | true =>
        exfalso
        have inTensor : o ∈ regionOf label (tensor C E).present q.region :=
          mem_regionOf.mpr ⟨Finset.mem_union_right _ inE, inside⟩
        rw [unchanged q inQ] at inTensor
        exact Finset.disjoint_left.mp apart (mem_regionOf.mp inTensor).1 inE

/-- **The anti-frame.** A firing admitted beside a frame that tells nothing, whose takes, reads and
query sightings lie on one side, is admitted on that side. Absence, and every predicate query
whose sightings stay, survive the removal of occurrences. -/
theorem valid_restrict {f : Firing T S O} {C E : Configuration T O}
    (framed : f.Valid A label (tensor C E)) (noKnowledge : A.Equivalent E.equations [])
    (taken : ∀ o ∈ f.selection.taken, o ∈ C.present) (read : ∀ o ∈ f.selection.read, o ∈ C.present)
    (seen : ∀ query ∈ f.queries, query.seen ⊆ C.present)
    (noCount : ∀ check ∈ f.rule.checks, ∀ pattern number, check ≠ .count pattern number) :
    f.Valid A label C := by
  have newer : ∀ σ, A.Models σ (f.selection.problem label f.rule C) →
      A.Models σ (f.selection.problem label f.rule (tensor C E)) := by
    intro σ solved
    rw [Firing.problem_eq', A.models_append] at solved ⊢
    exact ⟨(A.models_append σ _ _).mpr ⟨solved.1, (noKnowledge σ).mpr (A.models_nil σ)⟩, solved.2⟩
  have older : ∀ σ, A.Models σ (f.selection.problem label f.rule (tensor C E)) →
      A.Models σ (f.selection.problem label f.rule C) := by
    intro σ solved
    rw [Firing.problem_eq', A.models_append] at solved ⊢
    exact ⟨((A.models_append σ _ _).mp solved.1).1, solved.2⟩
  have firing := framed.firing
  refine ⟨⟨firing.take_distinct, firing.output_distinct, firing.take_length, firing.read_length,
    firing.outputs, ⟨fun o member => taken o (by simpa [Selection.commit] using member),
      fun o member => read o (by simpa [Selection.commit] using member), firing.occurrences.apart,
      Finset.disjoint_of_subset_right Finset.subset_union_left firing.occurrences.fresh,
      fun query member => by simp [Selection.commit] at member⟩, ?_, ?_⟩, ?_⟩
  · obtain ⟨σ, solved⟩ := firing.consistent
    exact ⟨σ, older σ solved⟩
  · intro check member σ solved
    have holds := firing.checks check member σ (newer σ solved)
    cases check with
    | equal left right => exact holds
    | absent pattern =>
        intro o present
        exact holds o (Finset.mem_union_left _ present)
    | count pattern number => exact absurd rfl (noCount _ member pattern number)
  · intro query member σ solved
    have framedSaw : regionOf label (C.present ∪ E.present) (query.region σ) = query.seen :=
      framed.observations query member σ (newer σ solved)
    change regionOf label C.present (query.region σ) = query.seen
    ext o
    constructor
    · intro inRegion
      rw [← framedSaw]
      exact mem_regionOf.mpr ⟨Finset.mem_union_left _ (mem_regionOf.mp inRegion).1,
        (mem_regionOf.mp inRegion).2⟩
    · intro inSeen
      have inFramed : o ∈ regionOf label (C.present ∪ E.present) (query.region σ) := by
        rw [framedSaw]
        exact inSeen
      exact mem_regionOf.mpr ⟨seen query member inSeen, (mem_regionOf.mp inFramed).2⟩

end Queries

/-! ## Verdicts on a region -/

section Verdicts

variable (A : SubstitutionAction T S) (label : O → T) {V : Type*} (wave : T → V)

omit [DecidableEq O] in
/-- **The values a region carries**: one per present occurrence of the region, read from its
label. R33's paths of a region are the instance at amplitudes. -/
def regionValues (region : T → Bool) (C : Configuration T O) : Multiset V :=
  (regionOf label C.present region).val.map fun o => wave (label o)

omit [DecidableEq O] in
theorem card_regionValues (region : T → Bool) (C : Configuration T O) :
    Multiset.card (regionValues label wave region C) = (regionOf label C.present region).card := by
  unfold regionValues
  rw [Multiset.card_map]
  rfl

/-- **A query admits exactly the frames that change no verdict on its region.** For a firing whose
one predicate query is a fixed query of a region, the framed firing is admitted exactly when every
verdict on the values the region carries is the same beside the frame as without it. -/
theorem frame_admitted_iff_values {f : Firing T S O} {C E : Configuration T O}
    {query : PredicateQuery O T} (only : f.queries = [PredicateQueryAdmission.Query.fixed query])
    (guards : ∀ check ∈ f.rule.checks, ∃ left right, check = .equal left right)
    (valid : f.Valid A label C) (apart : Disjoint C.present E.present)
    (after : Separable A (f.result label C) E) :
    f.Valid A label (tensor C E) ↔
      ∀ verdict : Multiset V → Prop,
        verdict (regionValues label wave query.region (tensor C E)) ↔
          verdict (regionValues label wave query.region C) := by
  rw [fixed_frame_iff A label (queries := [query]) only guards valid apart after]
  constructor
  · intro unchanged verdict
    unfold regionValues
    rw [unchanged query (List.mem_singleton_self _)]
  · intro same q inQ
    rw [List.mem_singleton.mp inQ]
    have values : regionValues label wave query.region (tensor C E) =
        regionValues label wave query.region C :=
      (same (fun values => values = regionValues label wave query.region C)).mpr rfl
    have cards := congrArg Multiset.card values
    rw [card_regionValues, card_regionValues] at cards
    have sub : regionOf label C.present query.region ⊆
        regionOf label (tensor C E).present query.region := by
      rw [regionOf_tensor]
      exact Finset.subset_union_left
    exact (Finset.eq_of_subset_of_card_le sub cards.le).symm

end Verdicts

end SeparationRuns

open SeparationRuns

#print axioms QueryFree.blindTo
#print axioms consistent_problem_tensor
#print axioms made_disjoint_frame
#print axioms valid_frame
#print axioms result_frame
#print axioms QueryFree.valid_frame
#print axioms frameAlong_iff_stages
#print axioms separated_nil_iff
#print axioms executable_frame
#print axioms frame_rule
#print axioms frame_rule_queryFree
#print axioms frame_rule_spatial
#print axioms frame_rule_known
#print axioms frame_rule_renamed
#print axioms census_frame_iff
#print axioms regionOf_tensor
#print axioms absent_tensor_iff
#print axioms count_tensor
#print axioms fixed_frame_iff
#print axioms valid_restrict
#print axioms card_regionValues
#print axioms frame_admitted_iff_values

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
