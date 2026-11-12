import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Frames

/-!
# Exact transitions of equation stores over frames

A unification problem is a store of equations at a frame. A solver changes the store by
transitions. A transition moves along a morphism `σ : a ⟶ m`, which records what it has committed
(for example an unknown it has instantiated), to a new store at `m`. It is **exact** when the
solutions of the old store are exactly the composites through `σ` of the solutions of the new one:
no solution is lost and none is added (`Exact`). Exactness composes, so every run of exact
transitions is exact (`Solver.Reaches.exact`).

A run ends in one of three ways, and each has its own true statement:

* **solved**: the residual store is empty. The composite morphism is then a principal answer by
  construction (`solved_principal`); conversely a principal answer is exactly an exact transition
  to the empty store (`exact_nil_iff_principal`). When the answer is an epimorphism on terms it is
  the initial solution: every solution factors through it, uniquely up to the frame's equality
  (`solved_initial`).
* **refuted**: a refutation with its reason as data; the store has no solution (`refuted_none`).
* **postponed**: equations remain. They are the knowledge after the run and the solution set is
  unchanged (`postponed_exact`): the store is solvable exactly when the residual is
  (`Exact.solvable_iff`), and an ask over the store is an ask over the residual along the answer
  (`Exact.entails_iff`).

Nothing here says that a run ends solved or refuted. Where a store has no principal answer, no run
reaches the empty store (`not_solved_of_no_principal`); where it is solvable, no run refutes it
(`not_refuted_of_solvable`). On such a store every run that stops, stops postponed.

The frames are the step's own (`Interface.Frames`): any category of frames acting on terms. The
concrete term models are separate modules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Interface

universe uO uT uH

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

section Definitions

variable (X : Frames Tm Hom)

/-- Two morphisms that act alike on every term, up to the frame's equality. -/
def Agree {a b : Obj} (f g : Hom a b) : Prop :=
  ∀ t : Tm a, X.E (X.act f t) (X.act g t)

/-- **An exact transition** from the store `S` at `a` to the store `S'` at `m`, along `σ`: the
solutions of `S` are exactly the composites `g ∘ σ` with `g` a solution of `S'`. -/
def Exact {a m : Obj} (S : EquationStore (Tm a)) (σ : Hom a m) (S' : EquationStore (Tm m)) :
    Prop :=
  ∀ (b : Obj) (f : Hom a b), X.Models f S ↔ ∃ g : Hom m b, Agree X f (X.comp g σ) ∧ X.Models g S'

/-- `σ` is an epimorphism on terms: two morphisms that agree on its image agree on every term. -/
def EpiOnTerms {a m : Obj} (σ : Hom a m) : Prop :=
  ∀ {b : Obj} (g h : Hom m b),
    (∀ t : Tm a, X.E (X.act g (X.act σ t)) (X.act h (X.act σ t))) → Agree X g h

/-- **The initial solution** of a store: a solution through which every solution factors, and
the factor is unique up to the frame's equality. This is the initial object of the category of
solutions of `S` (objects: solutions; morphisms: factorizations, compared by their action). In
the category of contexts, whose arrows run the other way, it is the terminal one. -/
structure InitialSolution {a m : Obj} (S : EquationStore (Tm a)) (σ : Hom a m) : Prop where
  solves : X.Models σ S
  factor : ∀ (b : Obj) (f : Hom a b), X.Models f S → ∃ g : Hom m b, Agree X f (X.comp g σ)
  unique : ∀ (b : Obj) (f : Hom a b) (g h : Hom m b),
    Agree X f (X.comp g σ) → Agree X f (X.comp h σ) → Agree X g h

end Definitions

/-- Why a refuted store has no solution, as data. Each term model proves what its reason means
there. -/
inductive Reason
  /-- Two different rigid heads: no solution in any model of the heads. -/
  | clash
  /-- An unknown equated with a term that properly contains it: **no well-founded solution**. A
  model of rational trees may still solve the same store. -/
  | noWellFoundedSolution
  /-- The level constraints have no solution over the natural numbers. -/
  | levels
  deriving DecidableEq, Repr

section Laws

variable {X : Frames Tm Hom}

theorem Agree.refl {a b : Obj} (f : Hom a b) : Agree X f f :=
  fun _ => (X.equivalence b).refl _

theorem Agree.symm {a b : Obj} {f g : Hom a b} (same : Agree X f g) : Agree X g f :=
  fun t => (X.equivalence b).symm (same t)

theorem Agree.trans {a b : Obj} {f g h : Hom a b} (one : Agree X f g) (two : Agree X g h) :
    Agree X f h :=
  fun t => (X.equivalence b).trans (one t) (two t)

/-- Composing with the identity does not change the action. -/
theorem agree_comp_id {a b : Obj} (f : Hom a b) : Agree X f (X.comp f (X.id a)) := by
  intro t
  rw [X.act_comp, X.act_id]
  exact (X.equivalence b).refl _

theorem agree_id_comp {a b : Obj} (f : Hom a b) : Agree X f (X.comp (X.id b) f) := by
  intro t
  rw [X.act_comp, X.act_id]
  exact (X.equivalence b).refl _

/-- A morphism that agrees with a solution is a solution. -/
theorem models_of_agree {a b : Obj} {f g : Hom a b} (same : Agree X f g)
    (S : EquationStore (Tm a)) : X.Models f S ↔ X.Models g S := by
  constructor
  · intro solved e member
    exact (X.equivalence b).trans ((X.equivalence b).symm (same e.1))
      ((X.equivalence b).trans (solved e member) (same e.2))
  · intro solved e member
    exact (X.equivalence b).trans (same e.1)
      ((X.equivalence b).trans (solved e member) ((X.equivalence b).symm (same e.2)))

/-- Agreement is kept by composing on the left. -/
theorem Agree.comp_left {a b c : Obj} {f g : Hom a b} (same : Agree X f g) (h : Hom b c) :
    Agree X (X.comp h f) (X.comp h g) := by
  intro t
  rw [X.act_comp, X.act_comp]
  exact X.preserves h (same t)

/-- **Equivalent stores at one frame are an exact transition along the identity.** This is how a
store is rewritten in place: deleting a trivial equation, decomposing, reordering. -/
theorem exact_id_of_equivalent {a : Obj} {S S' : EquationStore (Tm a)}
    (same : X.Equivalent S S') : Exact X S (X.id a) S' := by
  intro b f
  constructor
  · intro solved
    exact ⟨f, agree_comp_id f, (same b f).mp solved⟩
  · rintro ⟨g, fg, solvedG⟩
    have agree : Agree X f g := fg.trans (agree_comp_id g).symm
    exact (models_of_agree agree S).mpr ((same b g).mpr solvedG)

/-- An exact transition along the identity relates equivalent stores. -/
theorem equivalent_of_exact_id {a : Obj} {S S' : EquationStore (Tm a)}
    (exact : Exact X S (X.id a) S') : X.Equivalent S S' := by
  intro b f
  constructor
  · intro solved
    obtain ⟨g, fg, solvedG⟩ := (exact b f).mp solved
    exact (models_of_agree (fg.trans (agree_comp_id g).symm) S').mpr solvedG
  · intro solved
    exact (exact b f).mpr ⟨f, agree_comp_id f, solved⟩

/-- **Exact transitions compose.** -/
theorem Exact.trans {a m n : Obj} {S : EquationStore (Tm a)} {σ : Hom a m}
    {S' : EquationStore (Tm m)} {τ : Hom m n} {S'' : EquationStore (Tm n)}
    (first : Exact X S σ S') (second : Exact X S' τ S'') : Exact X S (X.comp τ σ) S'' := by
  intro b f
  constructor
  · intro solved
    obtain ⟨g, fg, solvedG⟩ := (first b f).mp solved
    obtain ⟨h, gh, solvedH⟩ := (second b g).mp solvedG
    refine ⟨h, fun t => ?_, solvedH⟩
    have one := fg t
    have two := gh (X.act σ t)
    simp only [X.act_comp] at one two ⊢
    exact (X.equivalence b).trans one two
  · rintro ⟨h, fh, solvedH⟩
    have solvedG : X.Models (X.comp h τ) S' := (second b _).mpr ⟨h, Agree.refl _, solvedH⟩
    apply (first b f).mpr
    refine ⟨X.comp h τ, fun t => ?_, solvedG⟩
    have one := fh t
    simp only [X.act_comp] at one ⊢
    exact one

/-- **Solved is principal, and principal is solved.** An exact transition to the empty store is a
principal answer of `Frames.Principal`, and every principal answer is one. -/
theorem exact_nil_iff_principal {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m} :
    Exact X S σ [] ↔ X.Principal S σ := by
  constructor
  · intro exact
    refine ⟨?_, ?_⟩
    · exact (exact m σ).mpr ⟨X.id m, agree_id_comp σ, Frames.models_nil _⟩
    · intro b f solved
      obtain ⟨g, fg, _⟩ := (exact b f).mp solved
      exact ⟨g, fg⟩
  · intro principal b f
    constructor
    · intro solved
      obtain ⟨g, fg⟩ := principal.factors b f solved
      exact ⟨g, fg, Frames.models_nil _⟩
    · rintro ⟨g, fg, _⟩
      exact (models_of_agree fg S).mpr (Frames.models_comp principal.sound g)

/-- **Principal by construction, initial when epi.** A principal answer that is an epimorphism on
terms is the initial solution. -/
theorem Principal.initial {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m}
    (principal : X.Principal S σ) (epi : EpiOnTerms X σ) : InitialSolution X S σ where
  solves := principal.sound
  factor := principal.factors
  unique := by
    intro b f g h fg fh
    apply epi g h
    intro t
    have one := fg t
    have two := fh t
    rw [X.act_comp] at one two
    exact (X.equivalence b).trans ((X.equivalence b).symm one) two

/-- **A postponed run keeps the solution set**: the store is solvable exactly when the residual
is. -/
theorem Exact.solvable_iff {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m}
    {R : EquationStore (Tm m)} (exact : Exact X S σ R) : X.Solvable S ↔ X.Solvable R := by
  constructor
  · rintro ⟨b, f, solved⟩
    obtain ⟨g, _, solvedG⟩ := (exact b f).mp solved
    exact ⟨b, g, solvedG⟩
  · rintro ⟨b, g, solvedG⟩
    exact ⟨b, X.comp g σ, (exact b _).mpr ⟨g, Agree.refl _, solvedG⟩⟩

/-- **An ask over the store is an ask over the residual along the answer**, for observations that
depend on a solution only through its action. -/
theorem Exact.entails_iff {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m}
    {R : EquationStore (Tm m)} (exact : Exact X S σ R) (observation : (b : Obj) → Hom a b → Prop)
    (respects : ∀ (b : Obj) (f g : Hom a b), Agree X f g → observation b g → observation b f) :
    X.Entails S observation ↔ X.Entails R (fun b g => observation b (X.comp g σ)) := by
  constructor
  · intro asked b g solvedG
    exact asked b _ ((exact b _).mpr ⟨g, Agree.refl _, solvedG⟩)
  · intro asked b f solved
    obtain ⟨g, fg, solvedG⟩ := (exact b f).mp solved
    exact respects b f _ fg (asked b g solvedG)

end Laws

/-! ## Solvers and their runs -/

section Solvers

variable (X : Frames Tm Hom)

/-- A solver: transitions, each exact, and refutations, each sound. -/
structure Solver where
  /-- A transition from `S` at `a` to `S'` at `m` along `σ`. -/
  Step : {a : Obj} → EquationStore (Tm a) → (m : Obj) → Hom a m → EquationStore (Tm m) → Prop
  step_exact : ∀ {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m}
    {S' : EquationStore (Tm m)}, Step S m σ S' → Exact X S σ S'
  /-- A refutation of a store, with its reason. -/
  Refutes : {a : Obj} → EquationStore (Tm a) → Reason → Prop
  refutes_sound : ∀ {a : Obj} {S : EquationStore (Tm a)} {r : Reason}, Refutes S r →
    ¬ X.Solvable S

variable {X}

/-- The runs of a solver: finitely many transitions, with the composite morphism. -/
inductive Solver.Reaches (P : Solver X) :
    {a : Obj} → EquationStore (Tm a) → (m : Obj) → Hom a m → EquationStore (Tm m) → Prop
  | refl {a : Obj} (S : EquationStore (Tm a)) : P.Reaches S a (X.id a) S
  | step {a m n : Obj} {S : EquationStore (Tm a)} {σ : Hom a m} {S' : EquationStore (Tm m)}
      {τ : Hom m n} {S'' : EquationStore (Tm n)} :
      P.Step S m σ S' → P.Reaches S' n τ S'' → P.Reaches S n (X.comp τ σ) S''

/-- A store at which a solver has nothing more to do: no transition and no refutation applies. -/
def Solver.Stopped (P : Solver X) {m : Obj} (R : EquationStore (Tm m)) : Prop :=
  (∀ (n : Obj) (τ : Hom m n) (R' : EquationStore (Tm n)), ¬ P.Step R n τ R') ∧
    ∀ r : Reason, ¬ P.Refutes R r

variable {P : Solver X}

/-- **Every run is exact.** -/
theorem Solver.Reaches.exact {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m}
    {R : EquationStore (Tm m)} (run : P.Reaches S m σ R) : Exact X S σ R := by
  induction run with
  | refl S => exact exact_id_of_equivalent (fun _ _ => Iff.rfl)
  | step first _ rest => exact (P.step_exact first).trans rest

/-- **Solved**: a run to the empty store ends with a principal answer. -/
theorem solved_principal {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m}
    (run : P.Reaches S m σ []) : X.Principal S σ :=
  exact_nil_iff_principal.mp run.exact

/-- **Solved, as a universal property**: with an epimorphic answer, the initial solution. -/
theorem solved_initial {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m}
    (run : P.Reaches S m σ []) (epi : EpiOnTerms X σ) : InitialSolution X S σ :=
  Principal.initial (solved_principal run) epi

/-- **Refuted**: a refuted run leaves no solution of the store it started from. -/
theorem refuted_none {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m}
    {R : EquationStore (Tm m)} {r : Reason} (run : P.Reaches S m σ R) (refuted : P.Refutes R r) :
    ¬ X.Solvable S :=
  fun solvable => P.refutes_sound refuted (run.exact.solvable_iff.mp solvable)

/-- **Postponed**: the residual is exact for the store it started from. -/
theorem postponed_exact {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m}
    {R : EquationStore (Tm m)} (run : P.Reaches S m σ R) : Exact X S σ R :=
  run.exact

/-- A store without principal answer is never solved. -/
theorem not_solved_of_no_principal {a : Obj} {S : EquationStore (Tm a)}
    (none : ∀ (m : Obj) (σ : Hom a m), ¬ X.Principal S σ) {m : Obj} {σ : Hom a m}
    (run : P.Reaches S m σ []) : False :=
  none m σ (solved_principal run)

/-- A solvable store is never refuted. -/
theorem not_refuted_of_solvable {a : Obj} {S : EquationStore (Tm a)} (solvable : X.Solvable S)
    {m : Obj} {σ : Hom a m} {R : EquationStore (Tm m)} {r : Reason} (run : P.Reaches S m σ R) :
    ¬ P.Refutes R r :=
  fun refuted => refuted_none run refuted solvable

/-- **The forced third outcome**: on a solvable store without principal answer, every run stops,
if it stops, with a nonempty residual that no refutation applies to, and the residual is exact. -/
theorem postponed_of_solvable_no_principal {a : Obj} {S : EquationStore (Tm a)}
    (solvable : X.Solvable S) (none : ∀ (m : Obj) (σ : Hom a m), ¬ X.Principal S σ)
    {m : Obj} {σ : Hom a m} {R : EquationStore (Tm m)} (run : P.Reaches S m σ R) :
    R ≠ [] ∧ (∀ r : Reason, ¬ P.Refutes R r) ∧ Exact X S σ R := by
  refine ⟨?_, fun r => not_refuted_of_solvable solvable run, run.exact⟩
  rintro rfl
  exact not_solved_of_no_principal none run

end Solvers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
