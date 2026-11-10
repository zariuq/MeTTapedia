import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DisequalityControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedSubstitution
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Waves

/-!
# Several spaces on the step: occurrences carry space handles

## Restrictions of the step (`restrict`)

A predicate on firings restricts any instance of `Interface.Step` to the firings it allows; the
result is again an instance, with the same knowledge, solutions and results (`restrict`,
`restrict_admits_iff`), and its runs are runs of the original (`toRun`, `toRun_last`, `toRun_word`,
`run_allowed`). Permissions and the birth of spaces are such restrictions.

## Spaces as handles on occurrences (any instance)

Every occurrence identity carries a space handle, `space : O → H`. The **space** `h` of a store is
its occurrences with handle `h` (`fiber`), and a commit restricted to `h` is `commitAt`.

* **Runs are executable commit words** (`run_executable`): the firings of every run of every instance
  of the interface, read as commits of `MeTTaCalculus.OccurrenceCommits`, are an executable word
  from its first present occurrences, and firing them gives its last. The occurrence-commit layer
  on which the space and permission modules of the MeTTa calculus are stated is the physical
  projection of the step.
* **One store with handles is a family of spaces** (`spaces_injective`, `enabled_iff_spaces`,
  `spaces_fire`, `present_result_spaces`). The adequacy criterion: a store is determined by its
  spaces; a commit without predicate queries is enabled exactly when its restriction to each space
  is enabled at that space; and firing acts space by space. So the step over one store whose
  occurrences carry handles is the step over the family of its spaces.
* **Frame law** (`fiber_unchanged`): a firing that takes and makes nothing at `h` leaves the space
  `h` as it was.

## The first-order step with located occurrences (`located`)

Labels are pairs of a handle and a payload under `LocatedSubstitution.action`, which keeps handles
rigid. A firing is **at `h`** (`At`) when its take, read and produce patterns, its absence and count
guards and its predicate queries all name `h`.

* **A query over one space is not affected by other spaces** (`checkAt_holds_iff`,
  `regionOf_fiber`): a guard or predicate query at `h` holds exactly as it holds on the space `h`.
* **Admission at one space depends only on that space and the knowledge** (`admits_of_fiber`,
  `admits_iff_of_fiber`): for a firing at `h`, two configurations with equivalent knowledge and the
  same space `h` admit it together (its made identities fresh in both).
* **Independence** (`independent`): a firing at `a` that adds no information does not change
  admission of any firing at a different space `b`.
* **Spaces separate resources and observations, not information**
  (`Controls.shared_variable_crosses_spaces`): a read at space `1` that binds a shared variable
  refuses a read at space `2` through the same variable, while a read with a fresh variable is
  still admitted, and a read at `1` that adds no information leaves the read at `2` admitted
  (`Controls.quiet_read_independent`). The hypothesis of `independent` is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Spaces

open Interface (Frames)
open AnnotatedRuns (firstOrder)
open MeTTaCalculus.OccurrenceCommits (Commit Enabled fire mem_fire Executable fireList regionOf)

/-! ## Restrictions of the step -/

section Restriction

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}

/-- **The restriction of a step to the firings a predicate allows.** -/
def restrict (P : Interface.Step X O State Firing) (allowed : ∀ {s : State}, Firing s → Prop) :
    Interface.Step X O State Firing where
  toEffectCore := P.effectCore
  Admits f := P.Admits f ∧ allowed f
  admitted_prepares _ admitted := P.prepares admitted.1

variable (P : Interface.Step X O State Firing) (allowed : ∀ {s : State}, Firing s → Prop)

/-- Restricting permission preserves the prepared effect and its domain. -/
theorem restrict_prepares_iff {s : State} (f : Firing s) :
    (restrict P allowed).Prepares f ↔ P.Prepares f := Iff.rfl

instance restrict_guarded [P.Guarded] : (restrict P allowed).Guarded where
  holds f b σ := P.Holds f b σ ∧ allowed f
  admission f := by
    constructor
    · rintro ⟨admitted, permitted⟩
      refine ⟨P.prepares admitted, fun b σ solved => ?_⟩
      exact ⟨((P.admits_iff_prepares f).mp admitted).2 b σ solved, permitted⟩
    · rintro ⟨prepared, asks⟩
      refine ⟨(P.admits_iff_prepares f).mpr ⟨prepared, fun b σ solved => (asks b σ solved).1⟩, ?_⟩
      obtain ⟨b, σ, solved⟩ := prepared.2.2
      exact (asks b σ solved).2

instance restrict_literalInformation [P.LiteralInformation] : (restrict P allowed).LiteralInformation :=
  ⟨P.transported⟩

instance restrict_literalKnowledge [P.LiteralKnowledge] : (restrict P allowed).LiteralKnowledge :=
  ⟨P.knowledge_preparedResult⟩

instance restrict_exact [P.Exact] : (restrict P allowed).Exact :=
  ⟨Interface.Step.Exact.exactness (P := P)⟩

theorem restrict_admits_iff {s : State} (f : Firing s) :
    (restrict P allowed).Admits f ↔ P.Admits f ∧ allowed f :=
  Iff.rfl

/-- A run of the restriction as a run of the step. -/
def toRun : {s : State} → (restrict P allowed).Run s → P.Run s
  | _, .nil s => .nil s
  | _, .cons f admitted rest => .cons f admitted.1 (toRun rest)

theorem toRun_last : ∀ {s : State} (r : (restrict P allowed).Run s), (toRun P allowed r).last = r.last
  | _, .nil _ => rfl
  | _, .cons _ _ rest => toRun_last rest

theorem toRun_word : ∀ {s : State} (r : (restrict P allowed).Run s),
    (toRun P allowed r).word = r.word
  | _, .nil _ => rfl
  | _, .cons f _ rest => by
      show ⟨_, f⟩ :: (toRun P allowed rest).word = ⟨_, f⟩ :: rest.word
      rw [toRun_word rest]

/-- Every firing of a run of the restriction is allowed. -/
theorem run_allowed : ∀ {s : State} (r : (restrict P allowed).Run s), ∀ x ∈ r.word, allowed x.2
  | _, .nil _, x, member => by simp [Interface.Step.Run.word] at member
  | _, .cons f admitted rest, x, member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact admitted.2
      · exact run_allowed rest x member

end Restriction

/-! ## Spaces as handles on occurrences -/

section Handles

universe uO uT uH uOcc uS uF uN uR

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Interface.Step X O State Firing) {H : Type uN} (space : O → H)

/-- The commits of a run, its occurrences located by their handles. -/
def commits : {s : State} → P.Run s → List (Commit O H)
  | _, .nil _ => []
  | _, .cons f _ rest => (P.selection f).commit (T := H) :: commits rest

/-- The physical enabling of the interface, with occurrences located by handles. -/
theorem enabled_located {store : Finset O} (selection : Selection O)
    (enabled : Enabled (fun _ : O => ()) store (selection.commit (T := Unit))) :
    Enabled space store (selection.commit (T := H)) :=
  ⟨enabled.taken_subset, enabled.kept_subset, enabled.apart, enabled.fresh, by
    intro query member
    simp [Selection.commit] at member⟩

/-- **The runs of every instance are executable commit words** of the occurrence-commit layer,
from the first present occurrences to the last. -/
theorem run_executable : ∀ {s : State} (r : P.Run s),
    Executable space (P.present s) (commits (H := H) P r) ∧
      fireList (P.present s) (commits (H := H) P r) = P.present r.last
  | _, .nil _ => ⟨.nil _, rfl⟩
  | _, .cons f admitted rest => by
      obtain ⟨executable, last⟩ := run_executable rest
      have enabled := (P.prepares admitted).2.1
      have fired : P.present (P.result f admitted) =
          fire (P.present _) ((P.selection f).commit (T := H)) :=
        P.present_result f admitted
      refine ⟨.cons (enabled_located space _ enabled) (fired ▸ executable), ?_⟩
      show fireList (fire (P.present _) ((P.selection f).commit (T := H))) (commits P rest) = _
      rw [← fired]
      exact last

variable [DecidableEq H]

/-- **The space `h` of a store**: its occurrences with handle `h`. -/
def fiber (h : H) (store : Finset O) : Finset O := store.filter fun o => space o = h

omit [DecidableEq O] in
theorem mem_fiber {h : H} {store : Finset O} {o : O} : o ∈ fiber space h store ↔ o ∈ store ∧ space o = h :=
  Finset.mem_filter

/-- A commit restricted to the space `h`; predicate queries are dropped. -/
def commitAt {R : Type uR} (h : H) (c : Commit O R) : Commit O R :=
  ⟨fiber space h c.taken, fiber space h c.kept, fiber space h c.made, []⟩

/-- The family of spaces of a store. -/
def spaces (store : Finset O) : H → Finset O := fun h => fiber space h store

omit [DecidableEq O] in
/-- **A store is determined by its spaces.** -/
theorem spaces_injective : Function.Injective (spaces (O := O) space) := by
  intro first second same
  ext o
  have atSpace := congrFun same (space o)
  constructor
  · intro member
    have inFiber : o ∈ fiber space (space o) first := (mem_fiber space).mpr ⟨member, rfl⟩
    rw [show fiber space (space o) first = spaces space first (space o) from rfl, atSpace] at inFiber
    exact ((mem_fiber space).mp inFiber).1
  · intro member
    have inFiber : o ∈ fiber space (space o) second := (mem_fiber space).mpr ⟨member, rfl⟩
    rw [show fiber space (space o) second = spaces space second (space o) from rfl, ← atSpace] at inFiber
    exact ((mem_fiber space).mp inFiber).1

/-- **Firing acts space by space.** -/
theorem spaces_fire {R : Type uR} (store : Finset O) (c : Commit O R) (h : H) :
    spaces space (fire store c) h = fire (spaces space store h) (commitAt space h c) := by
  ext o
  simp only [spaces, fiber, commitAt, fire, Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
  tauto

omit [DecidableEq O] in
/-- **A commit without predicate queries is enabled exactly when it is enabled space by space.** -/
theorem enabled_iff_spaces {R : Type uR} {label : O → R} {store : Finset O} {c : Commit O R}
    (positive : c.queries = []) :
    Enabled label store c ↔ ∀ h, Enabled label (spaces space store h) (commitAt space h c) := by
  constructor
  · intro enabled h
    refine ⟨fun o member => ?_, fun o member => ?_, ?_, ?_, by simp [commitAt]⟩
    · obtain ⟨taken, atH⟩ := (mem_fiber space).mp member
      exact (mem_fiber space).mpr ⟨enabled.taken_subset taken, atH⟩
    · obtain ⟨kept, atH⟩ := (mem_fiber space).mp member
      exact (mem_fiber space).mpr ⟨enabled.kept_subset kept, atH⟩
    · exact Finset.disjoint_filter_filter enabled.apart
    · exact Finset.disjoint_filter_filter enabled.fresh
  · intro enabled
    refine ⟨fun o taken => ?_, fun o kept => ?_, ?_, ?_, by simp [positive]⟩
    · exact ((mem_fiber space).mp
        ((enabled (space o)).taken_subset ((mem_fiber space).mpr ⟨taken, rfl⟩))).1
    · exact ((mem_fiber space).mp
        ((enabled (space o)).kept_subset ((mem_fiber space).mpr ⟨kept, rfl⟩))).1
    · rw [Finset.disjoint_left]
      intro o taken kept
      exact Finset.disjoint_left.mp (enabled (space o)).apart ((mem_fiber space).mpr ⟨taken, rfl⟩)
        ((mem_fiber space).mpr ⟨kept, rfl⟩)
    · rw [Finset.disjoint_left]
      intro o made present
      exact Finset.disjoint_left.mp (enabled (space o)).fresh ((mem_fiber space).mpr ⟨made, rfl⟩)
        ((mem_fiber space).mpr ⟨present, rfl⟩)

/-- **Each space of the result is its space fired by the firing's part there**, in every instance. -/
theorem present_result_spaces {s : State} (f : Firing s) (admitted : P.Admits f) (h : H) :
    spaces space (P.present (P.result f admitted)) h =
      fire (spaces space (P.present s) h) (commitAt space h ((P.selection f).commit (T := H))) := by
  have fired : P.present (P.result f admitted) = fire (P.present s) ((P.selection f).commit (T := H)) :=
    P.present_result f admitted
  rw [fired, spaces_fire]

/-- **Frame law**: a commit that takes and makes nothing at `h` leaves the space `h` as it was. -/
theorem fiber_unchanged {R : Type uR} {h : H} (store : Finset O) (c : Commit O R)
    (taken : ∀ o ∈ c.taken, space o ≠ h) (made : ∀ o ∈ c.made, space o ≠ h) :
    fiber space h (fire store c) = fiber space h store := by
  ext o
  simp only [fiber, fire, Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro ⟨inStore | inMade, atH⟩
    · exact ⟨inStore.1, atH⟩
    · exact absurd atH (made o inMade)
  · rintro ⟨inStore, atH⟩
    exact ⟨Or.inl ⟨inStore, fun inTaken => taken o inTaken atH⟩, atH⟩

end Handles

/-! ## The first-order step with located occurrences -/

section Located

universe uT uS uH uO

variable {T : Type uT} {S : Type uS} {H : Type uH} {O : Type uO} [DecidableEq O] [DecidableEq H]
  (A : SubstitutionAction T S) (space : O → H) (payload : O → T)

/-- Labels are a handle and a payload. -/
def label : O → H × T := fun o => (space o, payload o)

/-- **The first-order step over located occurrences**: handles are rigid under substitution. -/
abbrev located :=
  firstOrder (S := S) (LocatedSubstitution.action (N := H) A) (label space payload)

omit [DecidableEq O] [DecidableEq H] in
@[simp] theorem located_apply (σ : S) (x : H × T) :
    (LocatedSubstitution.action (N := H) A).apply σ x = (x.1, A.apply σ x.2) := rfl

omit [DecidableEq O] [DecidableEq H] in
@[simp] theorem located_E (x y : H × T) :
    (LocatedSubstitution.action (N := H) A).E x y ↔ x.1 = y.1 ∧ A.E x.2 y.2 := Iff.rfl

/-- A guard looks only at the space `h`. -/
def CheckAt (h : H) : Check (H × T) → Prop
  | .equal _ _ => True
  | .absent p => p.1 = h
  | .count p _ => p.1 = h

/-- A predicate query looks only at the space `h`. -/
def QueryAt (h : H) (query : PredicateQueryAdmission.Query (H × T) S O) : Prop :=
  ∀ σ x, query.region σ x = true → x.1 = h

/-- **A firing at the space `h`**: its patterns, guards and predicate queries name only `h`. -/
structure At (h : H) (f : AnnotatedRuns.Firing (H × T) S O) : Prop where
  take : ∀ p ∈ f.rule.take, p.1 = h
  read : ∀ p ∈ f.rule.read, p.1 = h
  produce : ∀ p ∈ f.rule.produce, p.1 = h
  checks : ∀ c ∈ f.rule.checks, CheckAt h c
  queries : ∀ q ∈ f.queries, QueryAt h q

variable {space}

omit [DecidableEq O] [DecidableEq H] in
theorem forall₂_space {h : H} : ∀ {patterns : List (H × T)} {selected : List O},
    List.Forall₂ (fun expected o => expected.1 = space o) patterns selected →
      (∀ p ∈ patterns, p.1 = h) → ∀ o ∈ selected, space o = h := by
  intro patterns selected matched
  induction matched with
  | nil => intro _ o member; cases member
  | @cons p o ps os same rest ih =>
      intro atH o' member
      rcases List.mem_cons.mp member with rfl | member
      · exact same.symm.trans (atH p List.mem_cons_self)
      · exact ih (fun q member => atH q (List.mem_cons_of_mem _ member)) o' member

variable (space)

omit [DecidableEq O] in
/-- **A guard at `h` holds exactly as it holds on the space `h`.** -/
theorem checkAt_holds_iff (σ : S) (store : Finset O) {h : H} (c : Check (H × T))
    (atH : CheckAt h c) :
    c.Holds (LocatedSubstitution.action (N := H) A) σ (label space payload) store ↔
      c.Holds (LocatedSubstitution.action (N := H) A) σ (label space payload) (fiber space h store) := by
  cases c with
  | equal left right => exact Iff.rfl
  | absent p =>
      change p.1 = h at atH
      constructor
      · intro holds o member
        exact holds o ((mem_fiber space).mp member).1
      · intro holds o member same
        exact holds o ((mem_fiber space).mpr ⟨member, same.1.symm.trans atH⟩) same
  | count p number =>
      change p.1 = h at atH
      have same : Check.matches (LocatedSubstitution.action (N := H) A) σ (label space payload) store p =
          Check.matches (LocatedSubstitution.action (N := H) A) σ (label space payload)
            (fiber space h store) p := by
        ext o
        simp only [Check.matches, Finset.mem_filter, mem_fiber]
        constructor
        · rintro ⟨member, matched⟩
          exact ⟨⟨member, matched.1.symm.trans atH⟩, matched⟩
        · rintro ⟨⟨member, _⟩, matched⟩
          exact ⟨member, matched⟩
      simp only [Check.Holds, same]

omit [DecidableEq O] in
/-- **A predicate query at `h` sees only the space `h`.** -/
theorem regionOf_fiber (store : Finset O) {h : H} {region : H × T → Bool}
    (atH : ∀ x, region x = true → x.1 = h) :
    regionOf (label space payload) store region = regionOf (label space payload) (fiber space h store) region := by
  ext o
  simp only [regionOf, Finset.mem_filter, mem_fiber]
  constructor
  · rintro ⟨member, inRegion⟩
    exact ⟨⟨member, atH _ inRegion⟩, inRegion⟩
  · rintro ⟨⟨member, _⟩, inRegion⟩
    exact ⟨member, inRegion⟩

omit [DecidableEq O] [DecidableEq H] in
theorem models_problem_iff {C D : Configuration (H × T) O} (f : AnnotatedRuns.Firing (H × T) S O)
    (knowledge : (LocatedSubstitution.action (N := H) A).Equivalent C.equations D.equations) (σ : S) :
    (LocatedSubstitution.action (N := H) A).Models σ (f.selection.problem (label space payload) f.rule C) ↔
      (LocatedSubstitution.action (N := H) A).Models σ (f.selection.problem (label space payload) f.rule D) := by
  simp only [Selection.problem, SubstitutionAction.models_append]
  rw [knowledge σ]

/-- **Admission of a firing at `h` depends only on the space `h` and the knowledge.** -/
theorem admits_of_fiber {C D : Configuration (H × T) O} {h : H} {f : AnnotatedRuns.Firing (H × T) S O}
    (atH : At h f) (knowledge : (LocatedSubstitution.action (N := H) A).Equivalent C.equations D.equations)
    (same : fiber space h C.present = fiber space h D.present)
    (fresh : ∀ o ∈ f.selection.made, o ∉ D.present)
    (admitted : (located A space payload).Admits (s := C) f) :
    (located A space payload).Admits (s := D) f := by
  obtain ⟨firing, observations⟩ := admitted
  have takenAt := forall₂_space (LocatedSubstitution.take_locations A space payload firing) atH.take
  have readAt := forall₂_space (LocatedSubstitution.read_locations A space payload firing) atH.read
  refine ⟨⟨firing.take_distinct, firing.output_distinct, firing.take_length, firing.read_length,
    firing.outputs, ?_, ?_, ?_⟩, ?_⟩
  · refine ⟨fun o member => ?_, fun o member => ?_, firing.occurrences.apart, ?_, ?_⟩
    · have taken : o ∈ f.selection.taken := by simpa [Selection.commit] using member
      have inFiber : o ∈ fiber space h C.present :=
        (mem_fiber space).mpr ⟨firing.occurrences.taken_subset member, takenAt o taken⟩
      rw [same] at inFiber
      exact ((mem_fiber space).mp inFiber).1
    · have kept : o ∈ f.selection.read := by simpa [Selection.commit] using member
      have inFiber : o ∈ fiber space h C.present :=
        (mem_fiber space).mpr ⟨firing.occurrences.kept_subset member, readAt o kept⟩
      rw [same] at inFiber
      exact ((mem_fiber space).mp inFiber).1
    · rw [Finset.disjoint_left]
      intro o made present
      exact fresh o (by simpa [Selection.commit] using made) present
    · intro query member
      simp [Selection.commit] at member
  · obtain ⟨σ, model⟩ := firing.consistent
    exact ⟨σ, (models_problem_iff A space payload f knowledge σ).mp model⟩
  · intro check member σ model
    have holds : check.Holds (LocatedSubstitution.action (N := H) A) σ (label space payload) C.present :=
      firing.checks check member σ ((models_problem_iff A space payload f knowledge σ).mpr model)
    rw [checkAt_holds_iff A space payload σ _ check (atH.checks check member)] at holds ⊢
    rw [← same]
    exact holds
  · intro query member σ model
    have holds := observations query member σ ((models_problem_iff A space payload f knowledge σ).mpr model)
    change regionOf (label space payload) C.present (query.region σ) = query.seen at holds
    change regionOf (label space payload) D.present (query.region σ) = query.seen
    rw [regionOf_fiber space payload _ (atH.queries query member σ)] at holds ⊢
    rw [← same]
    exact holds

/-- **Two configurations with equivalent knowledge and the same space `h` admit a firing at `h`
together.** -/
theorem admits_iff_of_fiber {C D : Configuration (H × T) O} {h : H}
    {f : AnnotatedRuns.Firing (H × T) S O} (atH : At h f)
    (knowledge : (LocatedSubstitution.action (N := H) A).Equivalent C.equations D.equations)
    (same : fiber space h C.present = fiber space h D.present)
    (freshC : ∀ o ∈ f.selection.made, o ∉ C.present) (freshD : ∀ o ∈ f.selection.made, o ∉ D.present) :
    (located A space payload).Admits (s := C) f ↔ (located A space payload).Admits (s := D) f :=
  ⟨admits_of_fiber A space payload atH knowledge same freshD,
    admits_of_fiber A space payload atH (fun σ => (knowledge σ).symm) same.symm freshC⟩

omit [DecidableEq H] in
/-- The made occurrences of an admitted firing at `h` lie at `h`. -/
theorem made_at {C : Configuration (H × T) O} {h : H} {f : AnnotatedRuns.Firing (H × T) S O}
    (atH : At h f) (admitted : (located A space payload).Admits (s := C) f) :
    ∀ o ∈ f.selection.made, space o = h := by
  intro o made
  have produced : label space payload o ∈ f.rule.produce := by
    rw [← admitted.firing.outputs]
    exact List.mem_map_of_mem made
  exact atH.produce _ produced

omit [DecidableEq H] in
/-- The taken occurrences of an admitted firing at `h` lie at `h`. -/
theorem taken_at {C : Configuration (H × T) O} {h : H} {f : AnnotatedRuns.Firing (H × T) S O}
    (atH : At h f) (admitted : (located A space payload).Admits (s := C) f) :
    ∀ o ∈ f.selection.taken, space o = h :=
  forall₂_space (LocatedSubstitution.take_locations A space payload admitted.firing) atH.take

/-- **Independence of spaces**: a firing at `a` that adds no information does not change the
admission of a firing at another space `b`. -/
theorem independent {C : Configuration (H × T) O} {f g : AnnotatedRuns.Firing (H × T) S O} {a b : H}
    (different : a ≠ b) (atF : At a f) (atG : At b g)
    (admittedF : (located A space payload).Admits (s := C) f)
    (quiet : (LocatedSubstitution.action (N := H) A).Equivalent
      (f.selection.problem (label space payload) f.rule C) C.equations)
    (distinct : ∀ o ∈ g.selection.made, o ∉ f.selection.made) :
    (located A space payload).Admits (s := C) g ↔
      (located A space payload).Admits (s := (located A space payload).result f admittedF) g := by
  have unchanged : fiber space b ((located A space payload).result f admittedF).present =
      fiber space b C.present :=
    fiber_unchanged space C.present (f.selection.commit (T := H × T))
      (fun o taken => by
        rw [taken_at A space payload atF admittedF o (by simpa [Selection.commit] using taken)]
        exact different)
      (fun o made => by
        rw [made_at A space payload atF admittedF o (by simpa [Selection.commit] using made)]
        exact different)
  constructor
  · intro admittedG
    refine admits_of_fiber A space payload atG (fun σ => (quiet σ).symm) unchanged.symm ?_ admittedG
    intro o made present
    rcases (mem_fire.mp present) with ⟨old, _⟩ | newly
    · exact Finset.disjoint_left.mp admittedG.firing.occurrences.fresh
        (by simpa [Selection.commit] using made) old
    · exact distinct o made (by simpa [Selection.commit] using newly)
  · intro admittedG
    refine admits_of_fiber A space payload atG quiet unchanged ?_ admittedG
    intro o made present
    have atB := made_at A space payload atG admittedG o made
    have gone : o ∉ ((located A space payload).result f admittedF).present :=
      Finset.disjoint_left.mp admittedG.firing.occurrences.fresh (by simpa [Selection.commit] using made)
    have taken : o ∈ f.selection.taken := by
      by_contra notTaken
      exact gone (mem_fire.mpr (Or.inl ⟨present, by simpa [Selection.commit] using notTaken⟩))
    exact different ((taken_at A space payload atF admittedF o taken).symm.trans atB)

end Located

/-! ## Controls: spaces separate resources and observations, not information -/

namespace Controls

open Mettapedia.Logic.LP
open Disequality.Controls (signature app X E_iff apply_X apply_const apply_app app_eq_app
  const_eq_const bind bind_zero)

abbrev B := FirstOrder.action signature

/-- Row `0` is `p(1)` at space `1`, row `1` is `p(2)` at space `2`. -/
def space : Nat → Nat
  | 0 => 1
  | 1 => 2
  | _ => 0

def payload : Nat → Term signature
  | 0 => app 0 (.const 1)
  | 1 => app 0 (.const 2)
  | _ => .const 0

abbrev P := located B space payload
abbrev Fir := AnnotatedRuns.Firing (Nat × Term signature) (Subst signature) Nat

def start : Configuration (Nat × Term signature) Nat := ⟨[], {0, 1}⟩

/-- Read row `0` at space `1` through `p(X)`: it binds `X = 1`. -/
def readOne : Fir := ⟨⟨[], [(1, app 0 X)], [], [], []⟩, [], ⟨[], [0], []⟩⟩
/-- Read row `0` at space `1` through `p(1)`: it adds no information. -/
def readOneQuiet : Fir := ⟨⟨[], [(1, app 0 (.const 1))], [], [], []⟩, [], ⟨[], [0], []⟩⟩
/-- Read row `1` at space `2` through `p(X)`, with the same `X`. -/
def readTwo : Fir := ⟨⟨[], [(2, app 0 X)], [], [], []⟩, [], ⟨[], [1], []⟩⟩
/-- Read row `1` at space `2` through `p(Y)`, with a fresh `Y`. -/
def readTwoFresh : Fir := ⟨⟨[], [(2, app 0 (.var 1))], [], [], []⟩, [], ⟨[], [1], []⟩⟩

theorem readOne_admitted : P.Admits (s := start) readOne :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨bind (.const 1), by
      intro e member
      simp [readOne, Selection.problem, Selection.equations, start, label] at member
      subst member
      simp [SubstitutionAction.Solves, payload, space]⟩, by simp [readOne]⟩

theorem readOneQuiet_admitted : P.Admits (s := start) readOneQuiet :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨bind (.const 1), by
      intro e member
      simp [readOneQuiet, Selection.problem, Selection.equations, start, label] at member
      subst member
      simp [SubstitutionAction.Solves, payload, space]⟩, by simp [readOneQuiet]⟩

theorem readTwo_admitted : P.Admits (s := start) readTwo :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨bind (.const 2), by
      intro e member
      simp [readTwo, Selection.problem, Selection.equations, start, label] at member
      subst member
      simp [SubstitutionAction.Solves, payload, space]⟩, by simp [readTwo]⟩

/-- `X := 1`, every other variable to `2`. -/
def split : Subst signature := fun v => if v = 0 then .const 1 else .const 2

@[simp] theorem split_zero : split 0 = .const 1 := rfl
@[simp] theorem split_one : split 1 = .const 2 := rfl
@[simp] theorem apply_var (σ : Subst signature) (v : Nat) : B.apply σ (.var v) = σ v := rfl

/-- The configuration after the binding read at space `1`. -/
def afterOne : Configuration (Nat × Term signature) Nat := readOne.result (label space payload) start

theorem readTwo_refused_after_one : ¬ P.Admits (s := afterOne) readTwo := by
  intro admitted
  obtain ⟨σ, model⟩ := admitted.firing.consistent
  have first := model ((1, app 0 X), label space payload 0) (by
    simp [readOne, readTwo, afterOne, AnnotatedRuns.Firing.result, Selection.result, Selection.problem,
      Selection.equations, start])
  have second := model ((2, app 0 X), label space payload 1) (by
    simp [readOne, readTwo, afterOne, AnnotatedRuns.Firing.result, Selection.result, Selection.problem,
      Selection.equations, start])
  simp [SubstitutionAction.Solves, label, payload, space] at first second
  exact absurd (first.symm.trans second) (by simp)

theorem readTwoFresh_admitted_after_one : P.Admits (s := afterOne) readTwoFresh :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨by decide, by decide, rfl, rfl, rfl, by decide,
      ⟨split, by
        intro e member
        simp [readOne, readTwoFresh, afterOne, AnnotatedRuns.Firing.result, Selection.result,
          Selection.problem, Selection.equations, start, label] at member
        rcases member with rfl | rfl <;> simp [SubstitutionAction.Solves, payload, space]⟩,
      by simp [readTwoFresh]⟩

/-- **A shared variable crosses spaces**: the read at space `2` through `X` is admitted at the
start and refused after the read at space `1` binds `X`; through a fresh variable it is still
admitted. The two reads are at different spaces. -/
theorem shared_variable_crosses_spaces :
    At 1 readOne ∧ At 2 readTwo ∧ P.Admits (s := start) readTwo ∧
      ¬ P.Admits (s := P.result readOne readOne_admitted) readTwo ∧
      P.Admits (s := P.result readOne readOne_admitted) readTwoFresh :=
  ⟨⟨by simp [readOne], by simp [readOne], by simp [readOne], by simp [readOne], by simp [readOne]⟩,
    ⟨by simp [readTwo], by simp [readTwo], by simp [readTwo], by simp [readTwo], by simp [readTwo]⟩,
    readTwo_admitted, readTwo_refused_after_one, readTwoFresh_admitted_after_one⟩

/-- **A read that adds no information is independent of the other space.** -/
theorem quiet_read_independent :
    P.Admits (s := start) readTwo ∧ P.Admits (s := P.result readOneQuiet readOneQuiet_admitted) readTwo :=
  ⟨readTwo_admitted, (independent B space payload (a := 1) (b := 2) (by decide)
    ⟨by simp [readOneQuiet], by simp [readOneQuiet], by simp [readOneQuiet], by simp [readOneQuiet],
      by simp [readOneQuiet]⟩
    ⟨by simp [readTwo], by simp [readTwo], by simp [readTwo], by simp [readTwo], by simp [readTwo]⟩
    readOneQuiet_admitted (by
      intro σ
      simp [readOneQuiet, Selection.problem, Selection.equations, start, label, payload, space,
        SubstitutionAction.Solves]) (by simp [readTwo])).mp readTwo_admitted⟩

end Controls

#print axioms restrict_admits_iff
#print axioms toRun_last
#print axioms toRun_word
#print axioms run_allowed
#print axioms run_executable
#print axioms spaces_injective
#print axioms spaces_fire
#print axioms enabled_iff_spaces
#print axioms present_result_spaces
#print axioms fiber_unchanged
#print axioms checkAt_holds_iff
#print axioms regionOf_fiber
#print axioms admits_of_fiber
#print axioms admits_iff_of_fiber
#print axioms independent
#print axioms Controls.shared_variable_crosses_spaces
#print axioms Controls.quiet_read_independent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Spaces
