import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObservationModuloControls

/-!
# Rows modulo the knowledge: congruence for firings

Equivalence modulo the knowledge relates states by a renaming that keeps labels only up to what the
knowledge entails. A firing renamed along it therefore meets labels that differ syntactically from
its own. The congruence factors in two steps:

* **Renaming transports labels** (`Firing.valid_rename_comp`, `Firing.result_rename_comp`): a firing
  renamed along any bijection is admitted at the renamed state under the labels exactly when the
  original is admitted under the labels read through the bijection. `Firing.valid_rename` and
  `Firing.result_rename` are the case where the bijection keeps labels.
* **Relabelling within the knowledge** (`Firing.valid_relabel`, `Firing.result_relabel`): two label
  maps that the knowledge entails equal on every identity, and that agree syntactically on the
  firing's made identities, admit the same firings with results of the same solutions and
  occurrences, provided the firing's query regions read labels through solutions
  (`QueriesReadThroughSolutions`).

## Congruence

* **Equivariance** (`ModuloEquivalent.firing`): at equivalent states, along a renaming supported on
  the present occurrences, a firing and its renaming are admitted together and their results are
  equivalent again, when the firing's made identities are absent from both states and its query
  regions read labels through solutions.
* **Firings and runs that name only escaped identities keep the equivalence**
  (`ModuloEquivalent.named_firing`, `ModuloEquivalent.named_run`), when their query regions read
  labels through solutions.
* **A bisimulation** (`ModuloEquivalent.bisimulation`): when the labels of a firing's made identities
  have fresh identities outside every finite set, the made identities that collide with the other
  state are first renamed to fresh ones of the same label (`exists_fresh_relabelling`), and every
  admitted firing whose query regions read labels through solutions has a counterpart of the same
  rule at the other state, with equivalent results.

## Both side conditions are needed (`ModuloFiringControls`)

* **A made identity present at the other state** (`made_collision`): under the knowledge `X = Z`
  the row `20 : X` is equivalent to the row `24 : Z`, nothing escaped. A firing that makes `24 : Z`
  is admitted at the first state, and no firing of its rule is admitted at the second: the only
  identity labelled `Z` is present there. Labels of fresh identities are fixed in advance, so a
  counterpart needs a fresh identity of the same syntactic label.
  With the label `Z` plentiful, the same firing has a counterpart (`made_plenty`).
* **A query region that reads labels syntactically** (`syntactic_query_collision`): at C2, a firing
  whose query asks for no row labelled `Y` itself is admitted at the first state, and none of its
  renamings is admitted at the second.
* **Positive** (`c2_take_congruent`): at C2 the firing that takes the row `20` with the pattern `X`
  has a counterpart at the second state, and the results are equivalent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

open AnnotatedRuns
open GuardFreeProcessOrders (SameUpTo)
open MeTTaCalculus.OccurrenceCommits (regionOf Enabled)

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-! ## Renaming transports labels -/

section Transport

variable {label : O → T} (π : O ≃ O)

omit [DecidableEq O] in
theorem equations_rename_comp (patterns : List T) (selected : List O) :
    Selection.equations label patterns (selected.map π) =
      Selection.equations (fun o => label (π o)) patterns selected := by
  simp only [Selection.equations, List.zipWith_map_right]

omit [DecidableEq O] in
theorem problem_rename_comp (selection : Selection O) (rule : RuleInstance T) (C : Configuration T O) :
    (renameSelection π selection).problem label rule (renameConfiguration π C) =
      selection.problem (fun o => label (π o)) rule C := by
  simp only [Selection.problem, renameSelection, renameConfiguration, equations_rename_comp]

omit [DecidableEq O] in
theorem regionOf_rename_comp (present : Finset O) (region : T → Bool) :
    regionOf label (present.map π.toEmbedding) region =
      (regionOf (fun o => label (π o)) present region).map π.toEmbedding := by
  ext o
  simp only [regionOf, Finset.mem_filter, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨⟨a, member, rfl⟩, inside⟩
    exact ⟨a, ⟨member, inside⟩, rfl⟩
  · rintro ⟨a, ⟨member, inside⟩, rfl⟩
    exact ⟨⟨a, member, rfl⟩, inside⟩

omit [DecidableEq O] in
theorem matches_rename_comp (A : SubstitutionAction T S) (σ : S) (present : Finset O) (pattern : T) :
    Check.matches A σ label (present.map π.toEmbedding) pattern =
      (Check.matches A σ (fun o => label (π o)) present pattern).map π.toEmbedding := by
  classical
  ext o
  simp only [Check.matches, Finset.mem_filter, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨⟨a, member, rfl⟩, matched⟩
    exact ⟨a, ⟨member, matched⟩, rfl⟩
  · rintro ⟨a, ⟨member, matched⟩, rfl⟩
    exact ⟨⟨a, member, rfl⟩, matched⟩

omit [DecidableEq O] in
theorem holds_rename_comp (A : SubstitutionAction T S) (σ : S) (present : Finset O) (check : Check T) :
    check.Holds A σ label (present.map π.toEmbedding) ↔
      check.Holds A σ (fun o => label (π o)) present := by
  cases check with
  | equal left right => exact Iff.rfl
  | absent pattern =>
      constructor
      · intro absent o member matched
        exact absent _ (Finset.mem_map_of_mem π.toEmbedding member) matched
      · intro absent o member matched
        obtain ⟨a, inside, rfl⟩ := Finset.mem_map.mp member
        exact absent a inside matched
  | count pattern number =>
      show (Check.matches A σ label (present.map π.toEmbedding) pattern).card = number ↔
        (Check.matches A σ (fun o => label (π o)) present pattern).card = number
      rw [matches_rename_comp, Finset.card_map]

omit [DecidableEq O] in
theorem queryHolds_rename_comp (σ : S) (present : Finset O)
    (query : PredicateQueryAdmission.Query T S O) :
    ((renameQuery π query).atSolution σ).Holds label (present.map π.toEmbedding) ↔
      (query.atSolution σ).Holds (fun o => label (π o)) present := by
  show regionOf label (present.map π.toEmbedding) (query.region σ) = query.seen.map π.toEmbedding ↔
    regionOf (fun o => label (π o)) present (query.region σ) = query.seen
  rw [regionOf_rename_comp]
  exact Finset.map_inj

/-- The occurrence conditions of a selection do not read labels. -/
theorem enabled_relabel (label' : O → T) (present : Finset O) (selection : Selection O) :
    Enabled label present (selection.commit (T := T)) ↔
      Enabled label' present (selection.commit (T := T)) :=
  ⟨fun ⟨taken, kept, apart, fresh, _⟩ => ⟨taken, kept, apart, fresh, by simp [Selection.commit]⟩,
    fun ⟨taken, kept, apart, fresh, _⟩ => ⟨taken, kept, apart, fresh, by simp [Selection.commit]⟩⟩

/-- **Renaming transports labels**: a renamed firing is admitted at the renamed state exactly when
the firing is admitted under the labels read through the renaming. -/
theorem Firing.valid_rename_comp (A : SubstitutionAction T S) (f : Firing T S O) (C : Configuration T O) :
    (f.rename π).Valid A label (renameConfiguration π C) ↔ f.Valid A (fun o => label (π o)) C := by
  have problem := problem_rename_comp (label := label) π f.selection f.rule C
  have outputs : (f.selection.made.map π).map label = f.selection.made.map fun o => label (π o) := by
    rw [List.map_map]
    rfl
  constructor
  · rintro ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputsEq, occurrences,
      consistent, checks⟩, observations⟩
    refine ⟨⟨List.Nodup.of_map π takeDistinct, List.Nodup.of_map π outputDistinct, ?_, ?_, ?_,
      (enabled_relabel (fun o => label (π o)) _ _).mp ((enabled_rename C.present f.selection).mp occurrences), ?_, ?_⟩, ?_⟩
    · simpa [Firing.rename, renameSelection] using takeLength
    · simpa [Firing.rename, renameSelection] using readLength
    · exact outputs.symm.trans outputsEq
    · simpa only [Firing.rename, problem] using consistent
    · intro check member σ solved
      have asked := checks check member σ (by simpa only [Firing.rename, problem] using solved)
      exact (holds_rename_comp π A σ C.present check).mp asked
    · intro query member σ solved
      have asked := observations (renameQuery π query) (List.mem_map_of_mem member) σ
        (by simpa only [Firing.rename, problem] using solved)
      exact (queryHolds_rename_comp π σ C.present query).mp asked
  · rintro ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputsEq, occurrences,
      consistent, checks⟩, observations⟩
    refine ⟨⟨takeDistinct.map π.injective, outputDistinct.map π.injective, ?_, ?_, ?_,
      (enabled_rename C.present f.selection).mpr ((enabled_relabel (fun o => label (π o)) _ _).mpr occurrences),
      ?_, ?_⟩, ?_⟩
    · simpa [Firing.rename, renameSelection] using takeLength
    · simpa [Firing.rename, renameSelection] using readLength
    · exact outputs.trans outputsEq
    · simpa only [Firing.rename, problem] using consistent
    · intro check member σ solved
      have asked := checks check member σ (by simpa only [Firing.rename, problem] using solved)
      exact (holds_rename_comp π A σ C.present check).mpr asked
    · intro query member σ solved
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      have asked := observations original present σ (by simpa only [Firing.rename, problem] using solved)
      exact (queryHolds_rename_comp π σ C.present original).mpr asked

/-- **The update transports labels.** -/
theorem Firing.result_rename_comp (f : Firing T S O) (C : Configuration T O) :
    (f.rename π).result label (renameConfiguration π C) =
      renameConfiguration π (f.result (fun o => label (π o)) C) := by
  show Configuration.mk ((renameSelection π f.selection).problem label f.rule (renameConfiguration π C))
      (MeTTaCalculus.OccurrenceCommits.fire (C.present.map π.toEmbedding)
        ((renameSelection π f.selection).commit (T := T))) =
    Configuration.mk (f.selection.problem (fun o => label (π o)) f.rule C)
      ((MeTTaCalculus.OccurrenceCommits.fire C.present (f.selection.commit (T := T))).map π.toEmbedding)
  rw [problem_rename_comp, fire_rename]

end Transport

/-! ## Relabelling within the knowledge -/

section Relabel

variable {A : SubstitutionAction T S}

/-- **The query regions of a firing read labels through solutions.** -/
def QueriesReadThroughSolutions (A : SubstitutionAction T S) (f : Firing T S O) : Prop :=
  ∀ query ∈ f.queries, ∀ σ {s t : T}, A.Solves σ (s, t) → query.region σ s = query.region σ t

variable {label label' : O → T} {σ : S}

omit [DecidableEq O] in
theorem models_equations_relabel (agree : ∀ o, A.Solves σ (label o, label' o)) :
    ∀ (patterns : List T) (selected : List O),
      A.Models σ (Selection.equations label patterns selected) ↔
        A.Models σ (Selection.equations label' patterns selected)
  | [], _ => by simp [Selection.equations]
  | _ :: _, [] => by simp [Selection.equations]
  | pattern :: patterns, o :: selected => by
      simp only [Selection.equations, List.zipWith_cons_cons, SubstitutionAction.models_cons]
      refine and_congr ⟨fun matched => A.equivalence.trans matched (agree o),
        fun matched => A.equivalence.trans matched (A.equivalence.symm (agree o))⟩ ?_
      exact models_equations_relabel agree patterns selected

omit [DecidableEq O] in
theorem matches_relabel (agree : ∀ o, A.Solves σ (label o, label' o)) (present : Finset O)
    (pattern : T) : Check.matches A σ label present pattern = Check.matches A σ label' present pattern := by
  classical
  ext o
  simp only [Check.matches, Finset.mem_filter]
  exact and_congr_right fun _ => ⟨fun matched => A.equivalence.trans matched (agree o),
    fun matched => A.equivalence.trans matched (A.equivalence.symm (agree o))⟩

omit [DecidableEq O] in
theorem holds_relabel (agree : ∀ o, A.Solves σ (label o, label' o)) (present : Finset O)
    (check : Check T) : check.Holds A σ label present ↔ check.Holds A σ label' present := by
  cases check with
  | equal left right => exact Iff.rfl
  | absent pattern =>
      exact forall₂_congr fun o _ => not_congr ⟨fun matched => A.equivalence.trans matched (agree o),
        fun matched => A.equivalence.trans matched (A.equivalence.symm (agree o))⟩
  | count pattern number =>
      show (Check.matches A σ label present pattern).card = number ↔
        (Check.matches A σ label' present pattern).card = number
      rw [matches_relabel agree]

variable {C : Configuration T O} {f : Firing T S O}

omit [DecidableEq O] in
/-- **Relabelling within the knowledge keeps the solutions of a firing's problem.** -/
theorem problem_relabel (within : ∀ o, Entailed A C.equations (label o) (label' o))
    (selection : Selection O) (rule : RuleInstance T) :
    A.Equivalent (selection.problem label rule C) (selection.problem label' rule C) := by
  intro σ
  simp only [Selection.problem, SubstitutionAction.models_append]
  constructor
  · rintro ⟨⟨⟨known, takes⟩, reads⟩, tells⟩
    have agree : ∀ o, A.Solves σ (label o, label' o) := fun o => within o σ known
    exact ⟨⟨⟨known, (models_equations_relabel agree _ _).mp takes⟩,
      (models_equations_relabel agree _ _).mp reads⟩, tells⟩
  · rintro ⟨⟨⟨known, takes⟩, reads⟩, tells⟩
    have agree : ∀ o, A.Solves σ (label o, label' o) := fun o => within o σ known
    exact ⟨⟨⟨known, (models_equations_relabel agree _ _).mpr takes⟩,
      (models_equations_relabel agree _ _).mpr reads⟩, tells⟩

omit [DecidableEq O] in
theorem problem_refines (label : O → T) (selection : Selection O) (rule : RuleInstance T) :
    A.Refines (selection.problem label rule C) C.equations := by
  intro σ solved
  simp only [Selection.problem, SubstitutionAction.models_append] at solved
  exact solved.1.1.1

/-- **Relabelling within the knowledge keeps admission**, when the made identities keep their labels
and the query regions read labels through solutions. -/
theorem Firing.valid_relabel (within : ∀ o, Entailed A C.equations (label o) (label' o))
    (made : ∀ o ∈ f.selection.made, label o = label' o) (reads : QueriesReadThroughSolutions A f) :
    f.Valid A label C ↔ f.Valid A label' C := by
  have problems := problem_relabel within f.selection f.rule (C := C)
  have outputs : f.selection.made.map label = f.selection.made.map label' := List.map_congr_left made
  have agreeAt : ∀ σ, A.Models σ (f.selection.problem label f.rule C) →
      ∀ o, A.Solves σ (label o, label' o) := fun σ solved o =>
    within o σ (problem_refines label f.selection f.rule σ solved)
  have regions : ∀ σ, A.Models σ (f.selection.problem label f.rule C) →
      ∀ query ∈ f.queries, regionOf label C.present (query.region σ) =
        regionOf label' C.present (query.region σ) := by
    intro σ solved query member
    exact Finset.filter_congr fun o _ => by rw [reads query member σ (agreeAt σ solved o)]
  constructor
  · rintro ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputsEq, occurrences,
      consistent, checks⟩, observations⟩
    refine ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs.symm.trans outputsEq,
      (enabled_relabel label' _ _).mp occurrences,
      (SubstitutionAction.equivalent_consistent A problems).mp consistent, ?_⟩, ?_⟩
    · intro check member σ solved
      have solved' := (problems σ).mpr solved
      exact (holds_relabel (agreeAt σ solved') C.present check).mp (checks check member σ solved')
    · intro query member σ solved
      have solved' := (problems σ).mpr solved
      show regionOf label' C.present (query.region σ) = query.seen
      rw [← regions σ solved' query member]
      exact observations query member σ solved'
  · rintro ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputsEq, occurrences,
      consistent, checks⟩, observations⟩
    refine ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs.trans outputsEq,
      (enabled_relabel label' _ _).mpr occurrences,
      (SubstitutionAction.equivalent_consistent A problems).mpr consistent, ?_⟩, ?_⟩
    · intro check member σ solved
      exact (holds_relabel (agreeAt σ solved) C.present check).mpr
        (checks check member σ ((problems σ).mp solved))
    · intro query member σ solved
      show regionOf label C.present (query.region σ) = query.seen
      rw [regions σ solved query member]
      exact observations query member σ ((problems σ).mp solved)

/-- **Relabelling within the knowledge keeps the result** up to the solutions of its knowledge. -/
theorem Firing.result_relabel (within : ∀ o, Entailed A C.equations (label o) (label' o)) :
    SameUpTo A (f.result label C) (f.result label' C) :=
  ⟨problem_relabel within f.selection f.rule, rfl⟩

end Relabel

/-! ## Congruence -/

section Congruence

variable {A : SubstitutionAction T S} {label : O → T} {E : Finset O}

/-- The knowledge of a result refines the knowledge before. -/
theorem result_refines (f : Firing T S O) (C : Configuration T O) :
    A.Refines (f.result label C).equations C.equations :=
  problem_refines label f.selection f.rule

/-- The step shared by both congruences: a renaming up to the knowledge that fixes the made
identities carries admission and results. -/
theorem modulo_step {C D : Configuration T O} {π : O ≃ O}
    (k : RenamingUpTo (entailedSetoid A C.equations) label E π)
    (same : SameUpTo A (renameConfiguration π C) D) {f : Firing T S O}
    (fixesMade : ∀ r ∈ f.selection.made, π r = r) (reads : QueriesReadThroughSolutions A f) :
    ((f.rename π).Valid A label D ↔ f.Valid A label C) ∧
      ModuloEquivalent A label E (f.result label C) ((f.rename π).result label D) := by
  have within : ∀ o, Entailed A C.equations (label (π o)) (label o) := k.keeps
  have madeKept : ∀ r ∈ f.selection.made, label (π r) = label r := fun r member => by
    rw [fixesMade r member]
  refine ⟨?_, π, k.weaken (entailedSetoid_mono (result_refines f C)), ?_⟩
  · calc (f.rename π).Valid A label D
        ↔ (f.rename π).Valid A label (renameConfiguration π C) := (Firing.valid_congr A label same).symm
      _ ↔ f.Valid A (fun o => label (π o)) C := Firing.valid_rename_comp π A f C
      _ ↔ f.Valid A label C := Firing.valid_relabel within madeKept reads
  · have relabelled : SameUpTo A (f.result label C) (f.result (fun o => label (π o)) C) :=
      Firing.result_relabel fun o σ solved => A.equivalence.symm (within o σ solved)
    have moved := sameUpTo_rename A π relabelled
    rw [← Firing.result_rename_comp] at moved
    exact GuardFreeProcessOrders.SameUpTo.trans A moved ((f.rename π).result_congr A label same)

/-- **Equivariance modulo the knowledge**: at equivalent states, along a renaming supported on the
present occurrences, a firing and its renaming are admitted together and their results are
equivalent, when the firing's made identities are absent from both states and its query regions
read labels through solutions. -/
theorem ModuloEquivalent.firing {C D : Configuration T O} (h : ModuloEquivalent A label E C D)
    {f : Firing T S O} (avoids : ∀ r ∈ f.selection.made, r ∉ C.present ∧ r ∉ D.present)
    (reads : QueriesReadThroughSolutions A f) :
    ∃ π : O ≃ O, RenamingUpTo (entailedSetoid A C.equations) label E π ∧
      (∀ r ∈ f.selection.made, π r = r) ∧ ((f.rename π).Valid A label D ↔ f.Valid A label C) ∧
      ModuloEquivalent A label E (f.result label C) ((f.rename π).result label D) := by
  obtain ⟨π, k, same, support⟩ := h.supported
  have fixesMade : ∀ r ∈ f.selection.made, π r = r := fun r member =>
    support r (avoids r member).1 (avoids r member).2
  exact ⟨π, k, fixesMade, modulo_step k same fixesMade reads⟩

/-- **Admitted firings whose made identities avoid the other state keep the equivalence.** -/
theorem ModuloEquivalent.admitted {C D : Configuration T O} (h : ModuloEquivalent A label E C D)
    {f : Firing T S O} (valid : f.Valid A label C) (avoids : ∀ r ∈ f.selection.made, r ∉ D.present)
    (reads : QueriesReadThroughSolutions A f) :
    ∃ π : O ≃ O, (f.rename π).Valid A label D ∧
      ModuloEquivalent A label E (f.result label C) ((f.rename π).result label D) := by
  obtain ⟨π, -, -, admits, results⟩ := h.firing (f := f)
    (fun r member => ⟨made_fresh valid member, avoids r member⟩) reads
  exact ⟨π, admits.mpr valid, results⟩

/-- **Firings that name only escaped identities keep the equivalence.** -/
theorem ModuloEquivalent.named_firing {C D : Configuration T O} (h : ModuloEquivalent A label E C D)
    {f : Firing T S O} (named : f.names ⊆ E) (reads : QueriesReadThroughSolutions A f) :
    (f.Valid A label C ↔ f.Valid A label D) ∧
      ModuloEquivalent A label E (f.result label C) (f.result label D) := by
  obtain ⟨π, k, same⟩ := h
  have fixed : f.rename π = f := f.rename_eq_self fun o member => k.fixes o (named member)
  have fixesMade : ∀ r ∈ f.selection.made, π r = r := fun r member =>
    k.fixes r (named (by simp [Firing.names, member]))
  obtain ⟨admits, results⟩ := modulo_step k same fixesMade reads
  rw [fixed] at admits results
  exact ⟨admits.symm, results⟩

/-- **Runs that name only escaped identities keep the equivalence.** -/
theorem ModuloEquivalent.named_run :
    ∀ {C D : Configuration T O}, ModuloEquivalent A label E C D →
      ∀ {w : List (Firing T S O)}, (∀ f ∈ w, f.names ⊆ E) → (∀ f ∈ w, QueriesReadThroughSolutions A f) →
        (Executable A label C w ↔ Executable A label D w) ∧
          ModuloEquivalent A label E (follow label C w) (follow label D w)
  | _, _, h, [], _, _ => ⟨SubstitutionAction.equivalent_consistent A h.solutions, h⟩
  | _, _, h, f :: rest, named, reads => by
      obtain ⟨admits, results⟩ := h.named_firing (named f List.mem_cons_self)
        (reads f List.mem_cons_self)
      obtain ⟨later, ends⟩ := ModuloEquivalent.named_run results
        (fun g member => named g (List.mem_cons_of_mem f member))
        (fun g member => reads g (List.mem_cons_of_mem f member))
      exact ⟨and_congr admits later, ends⟩

end Congruence

/-! ## A bisimulation, given fresh identities of the made labels -/

section Bisimulation

variable {A : SubstitutionAction T S} {label : O → T} {E : Finset O}

/-- **Fresh relabelling**: when every label of `M` has fresh identities outside every finite set, a
label-keeping bijection moves every identity of `M` out of `F ⊇ M` and fixes the rest of `F`. -/
theorem exists_fresh_relabelling :
    ∀ (M F : Finset O), M ⊆ F → (∀ m ∈ M, ∀ G : Finset O, ∃ o, o ∉ G ∧ label o = label m) →
      ∃ ρ : O ≃ O, (∀ o, label (ρ o) = label o) ∧ (∀ m ∈ M, ρ m ∉ F) ∧
        ∀ o ∈ F, o ∉ M → ρ o = o := by
  intro M
  induction M using Finset.induction_on with
  | empty =>
      intro F _ _
      exact ⟨Equiv.refl O, fun _ => rfl, fun m member => absurd member (Finset.notMem_empty m),
        fun _ _ _ => rfl⟩
  | insert m M' notIn ih =>
      intro F sub supply
      obtain ⟨ρ', keeps', moved', fixed'⟩ := ih F (fun o member => sub (Finset.mem_insert_of_mem member))
        (fun o member => supply o (Finset.mem_insert_of_mem member))
      obtain ⟨n, fresh, labelled⟩ := supply m (Finset.mem_insert_self m M') (F ∪ M'.image ρ')
      have mInF : m ∈ F := sub (Finset.mem_insert_self m M')
      have nNotF : n ∉ F := fun inF => fresh (Finset.mem_union_left _ inF)
      have nNotImage : n ∉ M'.image ρ' := fun inImage => fresh (Finset.mem_union_right _ inImage)
      have ρ'm : ρ' m = m := fixed' m mInF notIn
      refine ⟨ρ'.trans (Equiv.swap m n), fun o => ?_, fun x member => ?_, fun o inF notInM => ?_⟩
      · rw [Equiv.trans_apply, swap_keeps labelled (ρ' o), keeps']
      · rcases Finset.mem_insert.mp member with rfl | inM'
        · rw [Equiv.trans_apply, ρ'm, Equiv.swap_apply_left]
          exact nNotF
        · have out := moved' x inM'
          have neM : ρ' x ≠ m := fun same => out (by rw [same]; exact mInF)
          have neN : ρ' x ≠ n := fun same => nNotImage (by rw [← same]; exact Finset.mem_image_of_mem ρ' inM')
          rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne neM neN]
          exact out
      · have notM' : o ∉ M' := fun inM' => notInM (Finset.mem_insert_of_mem inM')
        have neM : o ≠ m := fun same => notInM (by rw [same]; exact Finset.mem_insert_self m M')
        have neN : o ≠ n := fun same => nNotF (by rw [← same]; exact inF)
        rw [Equiv.trans_apply, fixed' o inF notM', Equiv.swap_apply_of_ne_of_ne neM neN]

/-- **Equivalence modulo the knowledge is a bisimulation** for admitted firings whose query regions
read labels through solutions, when the labels of their made identities have fresh identities
outside every finite set: every admitted firing at one state has a counterpart of the same rule at
the other, and the results are equivalent again. The made identities that collide with the other
state are first renamed to fresh identities of the same label. -/
theorem ModuloEquivalent.bisimulation {C D : Configuration T O} (h : ModuloEquivalent A label E C D)
    {f : Firing T S O} (valid : f.Valid A label C) (reads : QueriesReadThroughSolutions A f)
    (supply : ∀ r ∈ f.selection.made, ∀ G : Finset O, ∃ o, o ∉ G ∧ label o = label r) :
    ∃ g : Firing T S O, g.rule = f.rule ∧ g.Valid A label D ∧
      ModuloEquivalent A label E (f.result label C) (g.result label D) := by
  classical
  let M := f.selection.made.toFinset.filter (· ∈ D.present)
  let F := C.present ∪ D.present ∪ E ∪ f.names
  have inF_C : ∀ {o}, o ∈ C.present → o ∈ F := fun inC =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ inC))
  have inF_D : ∀ {o}, o ∈ D.present → o ∈ F := fun inD =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ inD))
  have inF_E : ∀ {o}, o ∈ E → o ∈ F := fun inE =>
    Finset.mem_union_left _ (Finset.mem_union_right _ inE)
  have madeNamed : ∀ {o}, o ∈ f.selection.made → o ∈ f.names := fun made => by
    simp [Firing.names, made]
  have madeOfM : ∀ {o}, o ∈ M → o ∈ f.selection.made := fun inM =>
    List.mem_toFinset.mp (Finset.mem_filter.mp inM).1
  have sub : M ⊆ F := fun o inM => inF_D (Finset.mem_filter.mp inM).2
  obtain ⟨ρ, keeps, moved, fixed⟩ := exists_fresh_relabelling M F sub
    fun m inM => supply m (madeOfM inM)
  have freshC : ∀ {r}, r ∈ f.selection.made → r ∉ C.present := fun made => made_fresh valid made
  have fixC : ∀ o ∈ C.present, ρ o = o := fun o inC =>
    fixed o (inF_C inC) fun inM => freshC (madeOfM inM) inC
  have fixE : ∀ o ∈ E, ρ o = o := fun o inE =>
    fixed o (inF_E inE) fun inM =>
      freshC (madeOfM inM) ((h.escaped_iff inE).mpr (Finset.mem_filter.mp inM).2)
  have stays : renameConfiguration ρ C = C := by
    show (⟨C.equations, C.present.map ρ.toEmbedding⟩ : Configuration T O) = C
    rw [finset_map_eq_self ρ fixC]
  have gValid : (f.rename ρ).Valid A label C := by
    have moved := (Firing.valid_rename A keeps f C).mpr valid
    rwa [stays] at moved
  have gResult : (f.rename ρ).result label C = renameConfiguration ρ (f.result label C) := by
    have moved := Firing.result_rename keeps f C
    rwa [stays] at moved
  have privateStep : PrivatelyEquivalent A label E (f.result label C) ((f.rename ρ).result label C) :=
    ⟨ρ, ⟨keeps, fixE⟩, by rw [gResult]; exact SameUpTo.refl A _⟩
  have gAvoids : ∀ r ∈ (f.rename ρ).selection.made, r ∉ C.present ∧ r ∉ D.present := by
    intro r member
    change r ∈ f.selection.made.map ρ at member
    obtain ⟨r₀, made₀, rfl⟩ := List.mem_map.mp member
    by_cases inD : r₀ ∈ D.present
    · have out := moved r₀ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr made₀, inD⟩)
      exact ⟨fun inC => out (inF_C inC), fun inD' => out (inF_D inD')⟩
    · have same : ρ r₀ = r₀ := fixed r₀
        (Finset.mem_union_right _ (madeNamed made₀)) fun inM => inD (Finset.mem_filter.mp inM).2
      rw [same]
      exact ⟨freshC made₀, inD⟩
  have gReads : QueriesReadThroughSolutions A (f.rename ρ) := by
    intro query member σ s t solved
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact reads original present σ solved
  obtain ⟨π, -, -, admits, results⟩ := h.firing gAvoids gReads
  exact ⟨(f.rename ρ).rename π, rfl, admits.mpr gValid, (PrivatelyEquivalent.modulo privateStep).trans results⟩

end Bisimulation

/-! ## Controls -/

namespace ModuloFiringControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (zeros)
open ModuloControls (Tm X Y Z X_ne_Y c2 knowsXY zeros_solves c2_equivalent syntacticY)

/-! ### A made identity present at the other state -/

/-- Labels where `24` is the only identity labelled `Z`; every other identity is labelled `X`. -/
def soleLabel (o : ℕ) : Tm := if o = 24 then Z else X

theorem X_ne_Z : X ≠ Z := fun same => absurd (Term.var.inj same) (by decide)

theorem soleLabel_eq_Z {o : ℕ} (labelled : soleLabel o = Z) : o = 24 := by
  by_contra other
  rw [soleLabel, if_neg other] at labelled
  exact X_ne_Z labelled

/-- The knowledge `X = Z`. -/
def knowsXZ : EquationStore Tm := [(X, Z)]

def rowX : Configuration Tm ℕ := ⟨knowsXZ, {20}⟩
def rowZ : Configuration Tm ℕ := ⟨knowsXZ, {24}⟩

theorem zeros_solves_XZ : A.Models zeros knowsXZ := by
  intro e member
  rw [show e = (X, Z) from List.mem_singleton.mp member]
  rfl

/-- **The rows `20 : X` and `24 : Z` are equivalent under `X = Z`.** -/
theorem rows_equivalent : ModuloEquivalent A soleLabel ∅ rowX rowZ := by
  refine (moduloEquivalent_iff A soleLabel ∅ rowX rowZ).mpr
    ⟨fun _ => Iff.rfl, fun o member => absurd member (Finset.notMem_empty o), ?_⟩
  show ({20} : Finset ℕ).val.map (fun o => Quotient.mk (entailedSetoid A knowsXZ) (soleLabel o)) =
    ({24} : Finset ℕ).val.map (fun o => Quotient.mk (entailedSetoid A knowsXZ) (soleLabel o))
  rw [Finset.singleton_val, Finset.singleton_val, Multiset.map_singleton, Multiset.map_singleton]
  exact congrArg (fun c => ({c} : Multiset _)) (Quotient.sound
    (fun _ solved => solved (X, Z) (List.mem_singleton_self _)))

/-- The rule that makes one row labelled `Z`. -/
def makeZRule : RuleInstance Tm := ⟨[], [], [], [], [Z]⟩

/-- The firing that makes the row `24 : Z`. -/
def makeZ : Firing Tm (Subst signature) ℕ := ⟨makeZRule, [], ⟨[], [], [24]⟩⟩

theorem makeZ_valid : makeZ.Valid A soleLabel rowX := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [makeZ, makeZRule]⟩,
    by simp [makeZ]⟩
  intro e member
  have known : e ∈ knowsXZ := by
    simpa [Selection.problem, Selection.equations, makeZ, makeZRule, rowX] using member
  exact zeros_solves_XZ e known

/-- **A made identity present at the other state**: `makeZ` is admitted at the first state, and no
firing of its rule is admitted at the second, where the only identity labelled `Z` is present. -/
theorem made_collision :
    ModuloEquivalent A soleLabel ∅ rowX rowZ ∧ makeZ.Valid A soleLabel rowX ∧
      ∀ g : Firing Tm (Subst signature) ℕ, g.rule = makeZRule → ¬ g.Valid A soleLabel rowZ := by
  refine ⟨rows_equivalent, makeZ_valid, fun g rule valid => ?_⟩
  have outputs := valid.firing.outputs
  rw [rule] at outputs
  obtain ⟨r, single⟩ : ∃ r, g.selection.made = [r] := by
    rcases madeEq : g.selection.made with _ | ⟨r, _ | ⟨r', rest⟩⟩
    · rw [madeEq] at outputs
      exact absurd outputs (by simp [makeZRule])
    · exact ⟨r, rfl⟩
    · rw [madeEq] at outputs
      exact absurd outputs (by simp [makeZRule])
  rw [single] at outputs
  have is24 : r = 24 := soleLabel_eq_Z (List.singleton_inj.mp outputs)
  have fresh := valid.firing.occurrences.fresh
  simp only [Selection.commit, single, is24] at fresh
  exact Finset.disjoint_left.mp fresh (by simp) (show 24 ∈ ({24} : Finset ℕ) by simp)

/-- Labels where every identity but `20` is labelled `Z`: fresh identities of the label `Z` never run
out. -/
def plentyLabel (o : ℕ) : Tm := if o = 20 then X else Z

theorem rows_equivalent_plenty : ModuloEquivalent A plentyLabel ∅ rowX rowZ := by
  refine (moduloEquivalent_iff A plentyLabel ∅ rowX rowZ).mpr
    ⟨fun _ => Iff.rfl, fun o member => absurd member (Finset.notMem_empty o), ?_⟩
  show ({20} : Finset ℕ).val.map (fun o => Quotient.mk (entailedSetoid A knowsXZ) (plentyLabel o)) =
    ({24} : Finset ℕ).val.map (fun o => Quotient.mk (entailedSetoid A knowsXZ) (plentyLabel o))
  rw [Finset.singleton_val, Finset.singleton_val, Multiset.map_singleton, Multiset.map_singleton]
  exact congrArg (fun c => ({c} : Multiset _)) (Quotient.sound
    (fun _ solved => solved (X, Z) (List.mem_singleton_self _)))

theorem makeZ_valid_plenty : makeZ.Valid A plentyLabel rowX := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [makeZ, makeZRule]⟩,
    by simp [makeZ]⟩
  intro e member
  have known : e ∈ knowsXZ := by
    simpa [Selection.problem, Selection.equations, makeZ, makeZRule, rowX] using member
  exact zeros_solves_XZ e known

theorem plenty_supply (G : Finset ℕ) : ∃ o, o ∉ G ∧ plentyLabel o = Z := by
  obtain ⟨o, out⟩ := Infinite.exists_notMem_finset (insert 20 G)
  refine ⟨o, fun inG => out (Finset.mem_insert_of_mem inG), ?_⟩
  have other : o ≠ 20 := fun same => out (by rw [same]; exact Finset.mem_insert_self 20 G)
  simp [plentyLabel, other]

/-- **With fresh identities of the made label the collision disappears**: the same states and the
same firing, with the label `Z` plentiful, have a counterpart of `makeZ` at the second state, and
the results are equivalent. -/
theorem made_plenty :
    ∃ g : Firing Tm (Subst signature) ℕ, g.rule = makeZRule ∧ g.Valid A plentyLabel rowZ ∧
      ModuloEquivalent A plentyLabel ∅ (makeZ.result plentyLabel rowX) (g.result plentyLabel rowZ) :=
  rows_equivalent_plenty.bisimulation makeZ_valid_plenty (fun _ member => by simp [makeZ] at member)
    fun r member G => by
      have is24 : r = 24 := by simpa [makeZ] using member
      subst is24
      exact plenty_supply G

/-! ### A query region that reads labels syntactically -/

/-- The firing whose query asks for no row labelled `Y` itself. -/
noncomputable def noY : Firing Tm (Subst signature) ℕ := ⟨⟨[], [], [], [], []⟩, [syntacticY], ⟨[], [], []⟩⟩

/-- **A query region that reads labels syntactically breaks congruence**: `noY` is admitted at the
first C2 state, and none of its renamings is admitted at the second. -/
theorem syntactic_query_collision :
    noY.Valid A ModuloControls.label (c2 20) ∧
      ∀ ρ : ℕ ≃ ℕ, ¬ (noY.rename ρ).Valid A ModuloControls.label (c2 21) := by
  have separated := ModuloControls.syntactic_region_separates
  refine ⟨⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [noY]⟩, ?_⟩,
    fun ρ valid => ?_⟩
  · intro e member
    have known : e ∈ knowsXY := by
      simpa [Selection.problem, Selection.equations, noY, c2] using member
    exact zeros_solves e known
  · intro query member σ solved
    rw [show query = syntacticY by simpa [noY] using member]
    exact separated.2.1 σ (by simpa [Selection.problem, Selection.equations, noY, c2] using solved)
  · apply separated.2.2
    intro σ solved
    have asked := valid.observations (renameQuery ρ syntacticY) (by simp [Firing.rename, noY]) σ
      (by simpa [Selection.problem, Selection.equations, Firing.rename, noY, renameSelection, c2]
        using solved)
    simpa [renameQuery, syntacticY, PredicateQueryAdmission.Query.atSolution,
      MeTTaCalculus.OccurrenceCommits.PredicateQuery.Holds] using asked

/-! ### Positive -/

/-- The firing that takes the row `20` with the pattern `X`. -/
def takeX : Firing Tm (Subst signature) ℕ := ⟨⟨[X], [], [], [], []⟩, [], ⟨[20], [], []⟩⟩

theorem takeX_valid : takeX.Valid A ModuloControls.label (c2 20) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [takeX]⟩,
    by simp [takeX]⟩
  intro e member
  simp only [Selection.problem, Selection.equations, takeX, c2, knowsXY, List.zipWith_cons_cons,
    List.zipWith_nil_left, List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

/-- **At C2 the firing that takes the row `20` has an equivalent counterpart.** -/
theorem c2_take_congruent :
    ∃ π : ℕ ≃ ℕ, (takeX.rename π).Valid A ModuloControls.label (c2 21) ∧
      ModuloEquivalent A ModuloControls.label ∅ (takeX.result ModuloControls.label (c2 20))
        ((takeX.rename π).result ModuloControls.label (c2 21)) :=
  c2_equivalent.admitted takeX_valid (fun _ member => by simp [takeX] at member)
    (fun _ member => by simp [takeX] at member)

end ModuloFiringControls

#print axioms equations_rename_comp
#print axioms problem_rename_comp
#print axioms regionOf_rename_comp
#print axioms holds_rename_comp
#print axioms queryHolds_rename_comp
#print axioms enabled_relabel
#print axioms Firing.valid_rename_comp
#print axioms Firing.result_rename_comp
#print axioms models_equations_relabel
#print axioms holds_relabel
#print axioms problem_relabel
#print axioms Firing.valid_relabel
#print axioms Firing.result_relabel
#print axioms modulo_step
#print axioms ModuloEquivalent.firing
#print axioms ModuloEquivalent.admitted
#print axioms ModuloEquivalent.named_firing
#print axioms ModuloEquivalent.named_run
#print axioms exists_fresh_relabelling
#print axioms ModuloEquivalent.bisimulation
#print axioms ModuloFiringControls.rows_equivalent
#print axioms ModuloFiringControls.makeZ_valid
#print axioms ModuloFiringControls.made_collision
#print axioms ModuloFiringControls.made_plenty
#print axioms ModuloFiringControls.syntactic_query_collision
#print axioms ModuloFiringControls.takeX_valid
#print axioms ModuloFiringControls.c2_take_congruent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation
