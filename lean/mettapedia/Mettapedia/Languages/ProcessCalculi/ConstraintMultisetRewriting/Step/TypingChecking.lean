import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentHelpers
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CheckingAlgorithm

/-!
# Bidirectional checking as firings

Checking goals are occurrences. A firing takes one goal, makes its premise goals, and tells its side
conditions (reductions to weak-head forms, the subtype test) as residual obligations into the
knowledge. The kernel's bidirectional relation `CheckingAlgorithm` supplies the rules.

## Obligations as a constraint domain (`obligations`)

Terms are propositions, equivalent when logically equivalent; an obligation `p` is told as the
equation `p ≐ True` (`tell`). A store is solvable exactly when every obligation holds
(`solvable_iff`). There are no metavariables here, so obligations are discharged when told; with
metavariables they would wait, as residual equations do in the step.

## Goal firings (`goalStep`)

A goal firing carries a local soundness certificate: if its premise goals are derivable and its
residual obligations hold, its goal is derivable. A state *reaches* the root when derivability of
its present goals and truth of its knowledge give the root (`Reaches`).

* `reaches_step`, `reaches_run`: every admitted goal firing, hence every run, keeps reaching.
* **`completed_run_derives`**: a run from the root goal that ends with no goal present, and whose
  residual obligations hold, derives the root.

## The kernel's rules (`Kernel`)

Variable synthesis, application, abstraction checking and the switch from checking to synthesis,
each as a goal firing with its side conditions told. **`checking_run_sound`**: a completed checking
run from a goal `Γ ⊢ t ⇐ T` in a formed context, at a formed type, gives a typing derivation, by the
existing soundness of the kernel's algorithm (`CheckingAlgorithm.sound`).

Controls (`TypingCheckingControls`): `λx.x ⇐ g → g` in the two-head package is checked by a
completed run of three firings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingChecking

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

/-! ## Obligations -/

/-- **Obligations as a constraint domain**: propositions up to logical equivalence. -/
def obligations : SubstitutionAction Prop Unit where
  E := Iff
  equivalence := ⟨Iff.refl, Iff.symm, Iff.trans⟩
  apply _ p := p
  identity := ()
  compose _ _ := ()
  apply_identity _ := rfl
  apply_compose _ _ _ := rfl
  preserves _ _ _ same := same

/-- Tell an obligation. -/
def tell (p : Prop) : Equation Prop := (p, True)

theorem solvable_iff (store : EquationStore Prop) :
    (Frames.ofSubstitution obligations).Solvable (a := PUnit.unit) store ↔ ∀ e ∈ store, (e.1 ↔ e.2) :=
  ⟨fun ⟨_, _, solved⟩ => solved, fun holds => ⟨PUnit.unit, (), holds⟩⟩

/-! ## Goal firings -/

variable {G O : Type} [DecidableEq O]

variable (G O) in
/-- A state of goal-directed search: goal labels, present goals, and told obligations. -/
structure GoalState where
  goal : O → G
  present : Finset O
  knowledge : EquationStore Prop

/-- **A goal firing**: it takes one goal, makes premise goals, asks guards and tells residual
obligations, with a local soundness certificate. -/
structure GoalFiring (Derives : G → Prop) (s : GoalState G O) where
  taken : O
  made : List O
  premise : O → G
  guards : List Prop
  residuals : List Prop
  sound : (∀ o ∈ made, Derives (premise o)) → (∀ p ∈ residuals, p) → Derives (s.goal taken)

namespace GoalFiring

variable {Derives : G → Prop} {s : GoalState G O} (f : GoalFiring Derives s)

def selection : Selection O := ⟨[f.taken], [], f.made⟩

/-- The state after a goal firing. -/
def after : GoalState G O :=
  ⟨fun o => if o ∈ f.made then f.premise o else s.goal o,
    fire s.present (f.selection.commit (T := Unit)), s.knowledge ++ f.residuals.map tell⟩

end GoalFiring

variable (Derives : G → Prop)

/-- **The goal step**, over the one-frame category of obligations. -/
def goalStep :
    Interface.Step.Standard (Frames.ofSubstitution obligations) O (GoalState G O) (GoalFiring Derives) where
  frame _ := PUnit.unit
  knowledge s := s.knowledge
  present s := s.present
  selection f := f.selection
  target _ := PUnit.unit
  extension _ := ()
  information {s} f := s.knowledge ++ f.residuals.map tell
  transported := by
    intro s _ e member
    exact List.mem_append_left _ member
  Shapes f := f.made.Nodup
  Holds f _ _ := ∀ p ∈ f.guards, p
  Admits {s} f := f.made.Nodup ∧ Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    (Frames.ofSubstitution obligations).Solvable (a := PUnit.unit) (s.knowledge ++ f.residuals.map tell) ∧
    (Frames.ofSubstitution obligations).Entails (a := PUnit.unit) (s.knowledge ++ f.residuals.map tell)
      (fun _ _ => ∀ p ∈ f.guards, p)
  admits_iff _ := Iff.rfl
  preparedResult f _ := f.after
  present_preparedResult _ _ := rfl
  preparedSettle _ _ := ()
  knowledge_preparedResult {s} f _ :=
    (Frames.applyStore_id (X := Frames.ofSubstitution obligations) (s.knowledge ++ f.residuals.map tell)).symm

/-- A state **reaches** the root when its present goals and its knowledge give the root. -/
def Reaches (root : G) (s : GoalState G O) : Prop :=
  (∀ o ∈ s.present, Derives (s.goal o)) → (∀ e ∈ s.knowledge, (e.1 ↔ e.2)) → Derives root

variable {Derives}

/-- **Admitted goal firings keep reaching the root.** -/
theorem reaches_step {root : G} {s : GoalState G O} (f : GoalFiring Derives s)
    (admitted : (goalStep Derives).Admits f) (reach : Reaches Derives root s) :
    Reaches Derives root f.after := by
  intro derived holds
  have old : ∀ e ∈ s.knowledge, (e.1 ↔ e.2) := fun e member => holds e (List.mem_append_left _ member)
  have residual : ∀ p ∈ f.residuals, p := fun p member =>
    (holds (tell p) (List.mem_append_right _ (List.mem_map_of_mem member))).mpr trivial
  have premises : ∀ o ∈ f.made, Derives (f.premise o) := by
    intro o made
    have present : o ∈ f.after.present :=
      mem_fire.mpr (.inr (by simpa [GoalFiring.selection, Selection.commit] using made))
    have := derived o present
    simpa [GoalFiring.after, made] using this
  have takenDerives := f.sound premises residual
  apply reach _ old
  intro o present
  by_cases taken : o = f.taken
  · rw [taken]
    exact takenDerives
  · have stays : o ∈ f.after.present :=
      mem_fire.mpr (.inl ⟨present, by simpa [GoalFiring.selection, Selection.commit] using taken⟩)
    have notMade : o ∉ f.made := by
      have outside := Finset.disjoint_right.mp admitted.2.1.fresh present
      simpa [GoalFiring.selection, Selection.commit] using outside
    have := derived o stays
    simpa [GoalFiring.after, notMade] using this

/-- **Every run keeps reaching the root.** -/
theorem reaches_run {root : G} : ∀ {s : GoalState G O} (r : (goalStep Derives).Run s),
    Reaches Derives root s → Reaches Derives root r.last
  | _, .nil _, reach => reach
  | _, .cons f admitted rest, reach => reaches_run rest (reaches_step f admitted reach)

/-- **A completed run derives its root**: it starts from the root goal alone, ends with no goal
present, and its residual obligations hold. -/
theorem completed_run_derives {root : G} {s₀ : GoalState G O} {o₀ : O} (start : s₀.present = {o₀})
    (rootGoal : s₀.goal o₀ = root) (r : (goalStep Derives).Run s₀) (done : r.last.present = ∅)
    (discharged : (Frames.ofSubstitution obligations).Solvable (a := PUnit.unit) r.last.knowledge) :
    Derives root := by
  have initial : Reaches Derives root s₀ := fun derived _ => by
    rw [← rootGoal]
    exact derived o₀ (by rw [start]; exact Finset.mem_singleton_self o₀)
  exact reaches_run r initial (fun o present => by rw [done] at present; cases present)
    ((solvable_iff _).mp discharged)

/-! ## The kernel's rules as goal firings -/

namespace Kernel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Normalization

variable {Head : Type}

variable (Head) in
/-- A checking goal: a mode, a context, a term and a type. -/
abbrev Goal := Σ n : Nat, Mode × Ctx Head n × Tm Head n × Tm Head n

/-- A goal holds when the kernel's algorithm derives it. -/
def Checks (R : Rules Head) (g : Goal Head) : Prop :=
  CheckingAlgorithm R g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2

variable (R : Rules Head)

/-- Synthesize a variable's type from the context. -/
def varFiring (s : GoalState (Goal Head) O) (taken : O) {n : Nat} (Γ : Ctx Head n) (i : Fin n)
    (labelled : s.goal taken = ⟨n, .synth, Γ, .var i, Ctx.lookup Γ i⟩) : GoalFiring (Checks R) s where
  taken := taken
  made := []
  premise _ := ⟨n, .synth, Γ, .var i, Ctx.lookup Γ i⟩
  guards := []
  residuals := []
  sound _ _ := by
    rw [Checks, labelled]
    exact .var i

/-- Synthesize an application: synthesize the function, check the argument, and tell that the
function's type reduces to a dependent function type. -/
def appFiring (s : GoalState (Goal Head) O) (taken first second : O) (distinct : first ≠ second)
    {n : Nat} (Γ : Ctx Head n) (f a F A : Tm Head n) (B : Tm Head (n + 1))
    (labelled : s.goal taken = ⟨n, .synth, Γ, .app f a, inst0 a B⟩) : GoalFiring (Checks R) s where
  taken := taken
  made := [first, second]
  premise o := if o = first then ⟨n, .synth, Γ, f, F⟩ else ⟨n, .check, Γ, a, A⟩
  guards := []
  residuals := [Reduces R F (.pi A B)]
  sound premises residual := by
    rw [Checks, labelled]
    have function : Checks R ⟨n, .synth, Γ, f, F⟩ := by
      have premise := premises first (by simp)
      rwa [if_pos rfl] at premise
    have argument : Checks R ⟨n, .check, Γ, a, A⟩ := by
      have premise := premises second (by simp)
      rwa [if_neg (Ne.symm distinct)] at premise
    exact .app function (residual _ (by simp)) argument

/-- Check an abstraction: tell that the expected type reduces to a dependent function type, and
check the body under its domain. -/
def lamFiring (s : GoalState (Goal Head) O) (taken made : O) {n : Nat} (Γ : Ctx Head n)
    (body : Tm Head (n + 1)) (E A : Tm Head n) (B : Tm Head (n + 1))
    (labelled : s.goal taken = ⟨n, .check, Γ, .lam body, E⟩) : GoalFiring (Checks R) s where
  taken := taken
  made := [made]
  premise _ := ⟨n + 1, .check, .snoc Γ A, body, B⟩
  guards := []
  residuals := [Reduces R E (.pi A B)]
  sound premises residual := by
    rw [Checks, labelled]
    exact .lamCheck (residual _ (by simp)) (premises made (by simp))

/-- Check by synthesis: synthesize a type, and tell the subtype test against the expected type. -/
def switchFiring (s : GoalState (Goal Head) O) (taken made : O) {n : Nat} (Γ : Ctx Head n)
    (t T E : Tm Head n) (labelled : s.goal taken = ⟨n, .check, Γ, t, E⟩) :
    GoalFiring (Checks R) s where
  taken := taken
  made := [made]
  premise _ := ⟨n, .synth, Γ, t, T⟩
  guards := []
  residuals := [BelowAlgorithm R Γ T E]
  sound premises residual := by
    rw [Checks, labelled]
    exact .switch (premises made (by simp)) (residual _ (by simp))

/-- **A completed checking run is a typing derivation**: from the goal `Γ ⊢ t ⇐ T` alone, in a
formed context and at a formed type, a completed run whose obligations hold gives `Γ ⊢ t : T`. -/
theorem checking_run_sound {L : Type} [Mettapedia.TypeTheory.UniverseLevel.LevelOrder L] {S : Setting Head L}
    (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
    (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
    {s₀ : GoalState (Goal Head) O} {o₀ : O} {n : Nat} {Γ : Ctx Head n} {t T : Tm Head n}
    (start : s₀.present = {o₀}) (rootGoal : s₀.goal o₀ = ⟨n, .check, Γ, t, T⟩)
    (r : (goalStep (Checks S.R)).Run s₀) (done : r.last.present = ∅)
    (discharged : (Frames.ofSubstitution obligations).Solvable (a := PUnit.unit) r.last.knowledge)
    (formed : CtxFormed S.R Γ) (type : IsType S.R Γ T) : Typed S.R Γ t T :=
  CheckingAlgorithm.sound facts roots heads algebra declared
    (completed_run_derives start rootGoal r done discharged : Checks S.R ⟨n, .check, Γ, t, T⟩) formed type

#print axioms checking_run_sound

end Kernel

#print axioms solvable_iff
#print axioms reaches_step
#print axioms reaches_run
#print axioms completed_run_derives

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingChecking
