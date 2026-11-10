import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

/-!
# Disequality tells: knowledge with equations and disequations, as frames of the step

The step's knowledge is an equation store, so a disequality cannot be told. This module extends it
without editing the step: a disequation becomes part of the **frame** a firing lives at.

## Disequation frames (`Frame`, `Hom`, `frames`)

Over any substitution action, a disequation store is *separated* by a substitution that identifies
the two sides of none of its disequations (`Separates`). A **disequation frame** is a store that
the identity separates; equivalently, one with a separating substitution
(`separates_identity_iff`). A morphism of frames is a substitution that carries every separating
substitution of the later frame back to one of the earlier frame. These form a category of frames
in the sense of `Interface.Frames` (`frames`), so the interface's solvability, asks and principal
answers apply unchanged:

* **Solvability is solvability with separation** (`solvable_iff`): an equation store at a frame is
  solvable exactly when one substitution solves its equations and separates the frame's
  disequations. A solution into a later frame is a substitution together with the disequations
  still to be kept.
* **An ask is asked at every separating solution** (`entails_iff`).
* **Principal answers survive as answers into a frame** (`principal`, `solvable_iff_separates`): a
  principal answer of the equations that separates the disequations is principal at the frame, with
  the residual disequations as its target frame; if it does not separate them, the store is not
  solvable there. This is the solved form of equations and disequations: a substitution with
  residual disequations.
* **No single substitution presents them** (`presents_iff`): the separating substitutions of a
  disequation store are exactly those factoring through one substitution if and only if every
  substitution separates the store. A satisfiable disequation that some substitution violates, such
  as `X ≠ a`, has no presenting answer; disunification has no principal answer in general.

## The step with disequations (`step`)

A state carries a configuration and a disequation frame; a firing is a firing of the first-order
step together with the disequations it tells, which must form a frame with the state's. Its target
frame is the state's disequations and its tells, reached along the identity. Its information is the
first-order information. Admission is `Valid`: the first-order shapes and occurrences, a solution of
the information that separates every disequation, and the guards and predicate queries at every such
solution. **The step's single admission theorem holds for it** (`step`, `admits_iff_frames`): it is
an instance of `Interface.Step` over `frames`.

* **Conservative over equation-only stores** (`conservative`, `lift`, `lift_last`, `lift_word`): at a
  state without disequations, a firing that tells none is admitted exactly when its first-order firing
  is, with the same result; every run of the first-order step is a run of this step with the same
  firings and last configuration.
* A disequation is checked: telling an equation that identifies a told disequation is refused, and a
  disequation can make an absence guard hold that equations alone leave open
  (`DisequalityControls`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Disequality

open Interface (Frames)
open AnnotatedRuns (firstOrder)

universe uT uS uO

variable {T : Type uT} {S : Type uS}

/-- A disequation: two terms that must stay apart. -/
abbrev Disequation (T : Type uT) := T × T

/-- A list of disequations. -/
abbrev DisequationStore (T : Type uT) := List (Disequation T)

/-! ## Separation -/

section Separation

variable (A : SubstitutionAction T S)

/-- A substitution **separates** a disequation store when it identifies the two sides of none of
its disequations. -/
def Separates (σ : S) (store : DisequationStore T) : Prop :=
  ∀ d ∈ store, ¬ A.E (A.apply σ d.1) (A.apply σ d.2)

variable {A}

@[simp] theorem separates_nil (σ : S) : Separates A σ [] := by
  simp [Separates]

theorem separates_append {σ : S} {one two : DisequationStore T} :
    Separates A σ (one ++ two) ↔ Separates A σ one ∧ Separates A σ two := by
  constructor
  · intro separated
    exact ⟨fun d member => separated d (List.mem_append_left _ member),
      fun d member => separated d (List.mem_append_right _ member)⟩
  · rintro ⟨first, second⟩ d member
    rcases List.mem_append.mp member with member | member
    · exact first d member
    · exact second d member

/-- Separation depends on a substitution only through its action. -/
theorem separates_congr {σ τ : S} (same : ∀ t, A.apply σ t = A.apply τ t)
    (store : DisequationStore T) : Separates A σ store ↔ Separates A τ store := by
  simp only [Separates, same]

/-- **Separation is reflected along instantiation**: what a later instantiation separates, the
earlier substitution separated. -/
theorem separates_of_compose {σ τ : S} {store : DisequationStore T}
    (later : Separates A (A.compose τ σ) store) : Separates A σ store := by
  intro d member same
  apply later d member
  rw [A.apply_compose, A.apply_compose]
  exact A.preserves τ same

/-- A disequation store has a separating substitution exactly when the identity separates it. -/
theorem separates_identity_iff (store : DisequationStore T) :
    Separates A A.identity store ↔ ∃ σ, Separates A σ store := by
  constructor
  · intro separated
    exact ⟨_, separated⟩
  · rintro ⟨σ, separated⟩
    apply separates_of_compose (τ := σ)
    exact (separates_congr (fun t => by rw [A.apply_compose, A.apply_identity]) store).mpr separated

end Separation

/-! ## Disequation frames -/

section Frames

variable (A : SubstitutionAction T S)

/-- A **disequation frame**: a disequation store that has a separating substitution, witnessed by
the identity. -/
def Frame : Type uT := {store : DisequationStore T // Separates A A.identity store}

/-- A morphism of disequation frames: a substitution that carries every separating substitution of
the later frame back to a separating substitution of the earlier one. -/
def Hom (D D' : Frame A) : Type uS :=
  {σ : S // ∀ τ : S, Separates A τ D'.1 → Separates A (A.compose τ σ) D.1}

/-- **The category of disequation frames**, acting on terms by substitution. -/
def frames : Frames (fun _ : Frame A => T) (Hom A) where
  E := A.E
  equivalence _ := A.equivalence
  act f t := A.apply f.1 t
  id D := ⟨A.identity, fun τ separated =>
    (separates_congr (fun t => by rw [A.apply_compose, A.apply_identity]) D.1).mpr separated⟩
  comp g f := ⟨A.compose g.1 f.1, fun τ separated =>
    (separates_congr (fun t => by simp only [A.apply_compose]) _).mpr (f.2 _ (g.2 τ separated))⟩
  act_id t := A.apply_identity t
  act_comp g f t := A.apply_compose g.1 f.1 t
  preserves := fun {_ _} f {_ _} same => A.preserves f.1 same

variable {A}

theorem models_iff {D D' : Frame A} (f : Hom A D D') (store : EquationStore T) :
    (frames A).Models f store ↔ A.Models f.1 store :=
  Iff.rfl

/-- **A morphism separates its source frame.** -/
theorem separates_hom {D D' : Frame A} (f : Hom A D D') : Separates A f.1 D.1 :=
  separates_of_compose (τ := A.identity) (f.2 A.identity D'.2)

/-- The frame of the disequations a separating substitution leaves. -/
def image (σ : S) (store : DisequationStore T) (separated : Separates A σ store) : Frame A :=
  ⟨store.map fun d => (A.apply σ d.1, A.apply σ d.2), by
    intro d member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    simpa only [A.apply_identity] using separated original present⟩

/-- A separating substitution as a morphism into the frame it leaves. -/
def toImage (D : Frame A) (σ : S) (separated : Separates A σ D.1) :
    Hom A D (image σ D.1 separated) :=
  ⟨σ, fun τ later d member => by
    have kept := later _ (List.mem_map.mpr ⟨d, member, rfl⟩)
    simpa only [A.apply_compose] using kept⟩

/-- **Solvability at a frame is solvability with separation.** -/
theorem solvable_iff {D : Frame A} (store : EquationStore T) :
    (frames A).Solvable (a := D) store ↔ ∃ σ, A.Models σ store ∧ Separates A σ D.1 := by
  constructor
  · rintro ⟨D', f, solved⟩
    exact ⟨f.1, solved, separates_hom f⟩
  · rintro ⟨σ, solved, separated⟩
    exact ⟨_, toImage D σ separated, solved⟩

/-- **An ask at a frame is asked at every separating solution.** -/
theorem entails_iff {D : Frame A} (store : EquationStore T) (observation : S → Prop) :
    (frames A).Entails (a := D) store (fun _ f => observation f.1) ↔
      ∀ σ, A.Models σ store → Separates A σ D.1 → observation σ := by
  constructor
  · intro asked σ solved separated
    exact asked _ (toImage D σ separated) solved
  · intro asked D' f solved
    exact asked f.1 solved (separates_hom f)

/-- **Principal answers survive, as answers into a frame**: a principal answer of the equations
that separates the disequations is principal at the frame, its target frame being the residual
disequations. -/
theorem principal {D : Frame A} {store : EquationStore T} {answer : S}
    (principalAnswer : A.Principal store answer) (separated : Separates A answer D.1) :
    (frames A).Principal (a := D) store (toImage D answer separated) where
  sound := principalAnswer.sound
  factors := by
    intro D' f solved
    obtain ⟨residual, through⟩ := principalAnswer.factors f.1 solved
    refine ⟨⟨residual, fun τ later d member => ?_⟩, fun t => through t⟩
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    intro same
    apply f.2 τ later original present
    have first : A.E (A.apply (A.compose τ f.1) original.1)
        (A.apply (A.compose τ residual) (A.apply answer original.1)) := by
      have moved := A.preserves τ (through original.1)
      simpa only [A.apply_compose] using moved
    have second : A.E (A.apply (A.compose τ f.1) original.2)
        (A.apply (A.compose τ residual) (A.apply answer original.2)) := by
      have moved := A.preserves τ (through original.2)
      simpa only [A.apply_compose] using moved
    exact A.equivalence.trans first (A.equivalence.trans same (A.equivalence.symm second))

/-- **Solvability of equations and disequations is decided by a principal answer of the
equations**: the store is solvable at the frame exactly when that answer separates the frame. -/
theorem solvable_iff_separates {D : Frame A} {store : EquationStore T} {answer : S}
    (principalAnswer : A.Principal store answer) :
    (frames A).Solvable (a := D) store ↔ Separates A answer D.1 := by
  constructor
  · intro solvable d member same
    obtain ⟨σ, solved, separated⟩ := (solvable_iff store).mp solvable
    obtain ⟨residual, through⟩ := principalAnswer.factors σ solved
    apply separated d member
    have moved : A.E (A.apply (A.compose residual answer) d.1)
        (A.apply (A.compose residual answer) d.2) := by
      simp only [A.apply_compose]
      exact A.preserves residual same
    exact A.equivalence.trans (through d.1) (A.equivalence.trans moved (A.equivalence.symm (through d.2)))
  · intro separated
    exact (solvable_iff store).mpr ⟨answer, principalAnswer.sound, separated⟩

variable (A) in
/-- A substitution **presents** a disequation store when the store's separating substitutions are
exactly the substitutions that factor through it. -/
def Presents (store : DisequationStore T) (answer : S) : Prop :=
  ∀ σ, Separates A σ store ↔
    ∃ residual, ∀ t, A.E (A.apply σ t) (A.apply (A.compose residual answer) t)

variable (A) in
/-- **Disunification has no single principal answer in general**: a disequation store is presented
by one substitution exactly when every substitution separates it. A store that some substitution
separates and another violates has no presenting answer. -/
theorem presents_iff (store : DisequationStore T) :
    (∃ answer, Presents A store answer) ↔ ∀ σ, Separates A σ store := by
  constructor
  · rintro ⟨answer, presents⟩ σ
    have answerSeparates : Separates A answer store :=
      (presents answer).mpr ⟨A.identity, fun t => by
        simp only [A.apply_compose, A.apply_identity]
        exact A.equivalence.refl _⟩
    have identitySeparates : Separates A A.identity store :=
      (separates_identity_iff store).mpr ⟨answer, answerSeparates⟩
    obtain ⟨back, through⟩ := (presents A.identity).mp identitySeparates
    apply (presents σ).mpr
    refine ⟨A.compose σ back, fun t => ?_⟩
    have moved := A.preserves σ (through t)
    simp only [A.apply_compose, A.apply_identity] at moved ⊢
    exact moved
  · intro every
    refine ⟨A.identity, fun σ => ⟨fun _ => ⟨σ, fun t => ?_⟩, fun _ => every σ⟩⟩
    simp only [A.apply_compose, A.apply_identity]
    exact A.equivalence.refl _

end Frames

/-! ## The step with disequations -/

section Step

variable (A : SubstitutionAction T S) (O : Type uO) [DecidableEq O]

/-- A state of the step with disequations: a configuration and a disequation frame. -/
structure State where
  configuration : Configuration T O
  disequations : Frame A

/-- A firing of the step with disequations: a first-order firing and the disequations it tells,
which together with the state's form a disequation frame. -/
structure Firing (s : State A O) where
  base : AnnotatedRuns.Firing T S O
  tells : DisequationStore T
  formed : Separates A A.identity (s.disequations.1 ++ tells)

variable {A O}

/-- The frame a firing's information lives at: the state's disequations and the firing's. -/
def Firing.target {s : State A O} (f : Firing A O s) : Frame A :=
  ⟨s.disequations.1 ++ f.tells, f.formed⟩

/-- A firing moves along the identity substitution into its target frame. -/
def Firing.extension {s : State A O} (f : Firing A O s) : Hom A s.disequations f.target :=
  ⟨A.identity, fun τ separated =>
    (separates_congr (fun t => by rw [A.apply_compose, A.apply_identity]) _).mpr
      (separates_append.mp separated).1⟩

/-- A firing that tells no disequation. -/
def Firing.ofBase (s : State A O) (f : AnnotatedRuns.Firing T S O) : Firing A O s :=
  ⟨f, [], by simpa only [List.append_nil] using s.disequations.2⟩

/-- The equation-only state of a configuration. -/
def plain (C : Configuration T O) : State A O := ⟨C, ⟨[], separates_nil _⟩⟩

variable (A)
variable (label : O → T)

/-- The guards and predicate queries of a firing at one substitution. -/
def holdsAt {s : State A O} (f : Firing A O s) (σ : S) : Prop :=
  (∀ check ∈ f.base.rule.checks, check.Holds A σ label s.configuration.present) ∧
    ∀ query ∈ f.base.queries, (query.atSolution σ).Holds label s.configuration.present

/-- **Admission with disequations**: the first-order shapes and occurrences, a solution of the
information that separates every disequation, and the guards and predicate queries at every such
solution. -/
structure Valid {s : State A O} (f : Firing A O s) : Prop where
  take_distinct : f.base.selection.taken.Nodup
  output_distinct : f.base.selection.made.Nodup
  take_length : f.base.rule.take.length = f.base.selection.taken.length
  read_length : f.base.rule.read.length = f.base.selection.read.length
  outputs : f.base.selection.made.map label = f.base.rule.produce
  occurrences : MeTTaCalculus.OccurrenceCommits.Enabled label s.configuration.present
    (f.base.selection.commit (T := T))
  consistent : ∃ σ, A.Models σ (f.base.selection.problem label f.base.rule s.configuration) ∧
    Separates A σ f.target.1
  asks : ∀ σ, A.Models σ (f.base.selection.problem label f.base.rule s.configuration) →
    Separates A σ f.target.1 → holdsAt A label f σ

/-- **The step with disequations, an instance of the interface over disequation frames.** -/
def step : Interface.Step.Standard (frames A) O (State A O) (Firing A O) where
  frame s := s.disequations
  knowledge s := s.configuration.equations
  present s := s.configuration.present
  selection f := f.base.selection
  target f := f.target
  extension f := f.extension
  information {s} f := f.base.selection.problem label f.base.rule s.configuration
  transported := by
    intro s f e member
    show (A.apply A.identity e.1, A.apply A.identity e.2) ∈
      f.base.selection.problem label f.base.rule s.configuration
    rw [A.apply_identity, A.apply_identity]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member))
  Shapes f := f.base.selection.taken.Nodup ∧ f.base.selection.made.Nodup ∧
    f.base.rule.take.length = f.base.selection.taken.length ∧
    f.base.rule.read.length = f.base.selection.read.length ∧
    f.base.selection.made.map label = f.base.rule.produce
  Holds f _ σ := holdsAt A label f σ.1
  Admits f := Valid A label f
  admits_iff := by
    intro s f
    constructor
    · rintro ⟨takeDistinct, outputDistinct, takeLength, readLength, outputs, occurrences,
        consistent, asks⟩
      refine ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs⟩,
        ⟨occurrences.taken_subset, occurrences.kept_subset, occurrences.apart, occurrences.fresh, ?_⟩,
        (solvable_iff _).mpr consistent, (entails_iff (D := f.target) _ (holdsAt A label f)).mpr asks⟩
      intro query member
      simp [Selection.commit] at member
    · rintro ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs⟩, occurrences,
        solvable, asks⟩
      refine ⟨takeDistinct, outputDistinct, takeLength, readLength, outputs,
        ⟨occurrences.taken_subset, occurrences.kept_subset, occurrences.apart, occurrences.fresh, ?_⟩,
        (solvable_iff _).mp solvable, (entails_iff (D := f.target) _ (holdsAt A label f)).mp asks⟩
      intro query member
      simp [Selection.commit] at member
  preparedResult {s} f _ := ⟨f.base.result label s.configuration, f.target⟩
  present_preparedResult _ _ := rfl
  preparedSettle f _ := (frames A).id f.target
  knowledge_preparedResult {s} f _ := (Frames.applyStore_id (X := frames A)
    (f.base.selection.problem label f.base.rule s.configuration)).symm

/-- **The admission theorem for knowledge with disequations**: the interface's characterization,
over disequation frames. -/
theorem admits_iff_frames {s : State A O} (f : Firing A O s) :
    Valid A label f ↔ (step A label).Shapes f ∧
      MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : O => ()) s.configuration.present
        (f.base.selection.commit (T := Unit)) ∧
      (frames A).Solvable (a := f.target) (f.base.selection.problem label f.base.rule s.configuration) ∧
      (frames A).Entails (a := f.target) (f.base.selection.problem label f.base.rule s.configuration)
        ((step A label).Holds f) :=
  (step A label).admits_iff f

/-! ## Conservativity over equation-only stores -/

/-- **Conservative over equation-only stores**: at a state without disequations, a firing that tells
none is admitted exactly when its first-order firing is. -/
theorem conservative {s : State A O} (f : Firing A O s) (empty : s.disequations.1 = [])
    (silent : f.tells = []) :
    (step A label).Admits f ↔ (firstOrder A label).Admits (s := s.configuration) f.base := by
  have separated : ∀ σ, Separates A σ f.target.1 := by
    intro σ
    show Separates A σ (s.disequations.1 ++ f.tells)
    rw [empty, silent]
    exact separates_nil σ
  constructor
  · rintro ⟨takeDistinct, outputDistinct, takeLength, readLength, outputs, occurrences,
      ⟨σ, solved, -⟩, asks⟩
    exact ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs, occurrences, ⟨σ, solved⟩,
        fun check member τ model => (asks τ model (separated τ)).1 check member⟩,
      fun query member τ model => (asks τ model (separated τ)).2 query member⟩
  · rintro ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs, occurrences, ⟨σ, solved⟩,
      checks⟩, observations⟩
    exact ⟨takeDistinct, outputDistinct, takeLength, readLength, outputs, occurrences,
      ⟨σ, solved, separated σ⟩, fun τ model _ =>
        ⟨fun check member => checks check member τ model,
          fun query member => observations query member τ model⟩⟩

/-- The result of an equation-only firing at an equation-only state is the equation-only state of
the first-order result. -/
theorem result_plain {C : Configuration T O} (f : AnnotatedRuns.Firing T S O)
    (admitted : (step A label).Admits (Firing.ofBase (plain C) f)) :
    (step A label).result (Firing.ofBase (plain C) f) admitted = plain (f.result label C) :=
  rfl

/-- **Every run of the first-order step is a run of the step with disequations**, from the
equation-only state, firing by firing. -/
def lift : {C : Configuration T O} → (firstOrder A label).Run C → (step A label).Run (plain C)
  | _, .nil C => .nil (plain C)
  | C, .cons f admitted rest =>
      .cons (Firing.ofBase (plain C) f)
        ((conservative A label (Firing.ofBase (plain C) f) rfl rfl).mpr admitted) (lift rest)

theorem lift_last : ∀ {C : Configuration T O} (r : (firstOrder A label).Run C),
    (lift A label r).last = plain r.last
  | _, .nil _ => rfl
  | _, .cons _ _ rest => lift_last rest

theorem lift_word : ∀ {C : Configuration T O} (r : (firstOrder A label).Run C),
    (lift A label r).word.map (fun x => x.2.base) = r.word.map Sigma.snd ∧
      ∀ x ∈ (lift A label r).word, x.2.tells = []
  | _, .nil _ => ⟨rfl, by simp [Interface.Step.Run.word, lift]⟩
  | C, .cons f admitted rest => by
      obtain ⟨same, silent⟩ := lift_word rest
      have word : (lift A label (.cons f admitted rest)).word =
          ⟨plain C, Firing.ofBase (plain C) f⟩ :: (lift A label rest).word := rfl
      rw [word]
      refine ⟨?_, ?_⟩
      · rw [List.map_cons, same]
        rfl
      · intro x member
        rcases List.mem_cons.mp member with rfl | member
        · rfl
        · exact silent x member

end Step

#print axioms separates_identity_iff
#print axioms separates_hom
#print axioms solvable_iff
#print axioms entails_iff
#print axioms principal
#print axioms solvable_iff_separates
#print axioms presents_iff
#print axioms admits_iff_frames
#print axioms conservative
#print axioms result_plain
#print axioms lift_last
#print axioms lift_word

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Disequality
