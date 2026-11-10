import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderIndependence

/-!
# Guards of the one-frame step as predicates of a solution

The first-order run layer (`AnnotatedRuns.firstOrder`) writes a firing's guards as checks:
equations, absence and counts. Proof calculi need guards outside that syntax, such as the
ordering side conditions of superposition. This module adds them, keeping the interface's
semantics: a **guarded firing** (`GuardedFiring`) is a first-order firing with a list of guards,
each a predicate of a solution, asked at every solution of the firing's information.

## The guarded step

* `guarded A label` is an instance of the candidate step's interface (`Interface.Step`) over the one
  frame of `A`, with the first-order step's states, selections, information and results.
  **Admission** is first-order admission together with the ask of the guards (`guarded_admits_iff`).
* **The first-order step embeds** (`lift`, `admits_lift_iff`, `result_lift`, `liftRun`, `liftRun_last`): a firing
  with no guards is admitted exactly when it is admitted in `firstOrder`, with the same result, so
  resolution firings and guarded firings share one store and interleave in one run. Sharing the step
  proves no completeness of a mixed calculus: each calculus keeps its own inferences, redundancy
  criterion, coverage and fairness, and those are proved per calculus.
* **Transport and independence** (`guardedTransport`, `guarded_closes`,
  `guarded_independent_iff`): isomorphic states are configurations with the same solutions and
  occurrences, firings move and have residuals as themselves, diamonds close, and independence is
  the four admissions.

## Three readings of a side condition

A guard is **stable** when it survives instantiation, and **co-stable** when it survives
generalization. Equations are stable. The negation of a stable relation, such as `¬ (r ⪰ l)` for a
stable term ordering, is co-stable; the ordering side conditions of superposition are of this kind.

With a principal answer `μ` of the information:

* a stable guard asked at every solution is the guard at `μ` (`entails_iff_of_stable`);
* a co-stable guard holds at some solution exactly when it holds at `μ` (`exists_iff_of_coStable`);
* asked at every solution, a co-stable guard is in general **stronger** than the guard at `μ`
  (`at_principal_of_entails`; the converse fails, see the controls);
* the **closure** of a guard (`Closure`: some solution more general than this one satisfies it) is
  stable (`Closure.stable`), and its ask at every solution is the guard at `μ`
  (`entails_closure_iff`). This is how a side condition stated at the most general unifier becomes a
  guard of the step.

Without a principal answer, over a minimal complete set of solutions `U` (`MinimalComplete`), the
closure's ask at every solution holds exactly when the guard holds at **every** member of `U`
(`entails_closure_iff_complete`), while the guard holds at some solution exactly when it holds at
**some** member (`exists_iff_complete`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition

open Interface (Frames Transport)
open AnnotatedRuns (Firing firstOrder sameUpTo_symm)
open GuardFreeProcessOrders (SameUpTo problem_eq equivalent_append)

universe uT uS uO

/-! ## Readings of a guard over a substitution action -/

section Readings

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S)

/-- `σ` factors through `τ` on every term: `σ` is an instance of `τ`. -/
def Factors (σ τ : S) : Prop := ∃ ν : S, ∀ t : T, A.E (A.apply σ t) (A.apply (A.compose ν τ) t)

/-- A guard depends on a solution only through its action on terms. -/
def Respects (G : S → Prop) : Prop :=
  ∀ σ τ : S, (∀ t : T, A.E (A.apply σ t) (A.apply τ t)) → (G σ ↔ G τ)

/-- **A stable guard** survives instantiation. -/
def Stable (G : S → Prop) : Prop := ∀ ν σ : S, G σ → G (A.compose ν σ)

/-- **A co-stable guard** survives generalization. -/
def CoStable (G : S → Prop) : Prop := ∀ ν σ : S, G (A.compose ν σ) → G σ

/-- **The closure of a guard**: some solution of the store more general than this one satisfies it. -/
def Closure (store : EquationStore T) (G : S → Prop) (σ : S) : Prop :=
  ∃ τ : S, A.Models τ store ∧ Factors A σ τ ∧ G τ

variable {A}

theorem Factors.refl_compose (ν τ : S) : Factors A (A.compose ν τ) τ :=
  ⟨ν, fun _ => A.equivalence.refl _⟩

/-- Instances of instances are instances. -/
theorem Factors.compose {σ τ : S} (factors : Factors A σ τ) (ν : S) : Factors A (A.compose ν σ) τ := by
  obtain ⟨ρ, through⟩ := factors
  refine ⟨A.compose ν ρ, fun t => ?_⟩
  rw [A.apply_compose, A.apply_compose, A.apply_compose]
  have step := A.preserves ν (through t)
  rwa [A.apply_compose] at step

/-- **The closure is stable.** -/
theorem Closure.stable {store : EquationStore T} {G : S → Prop} : Stable A (Closure A store G) := by
  rintro ν σ ⟨τ, solved, factors, holds⟩
  exact ⟨τ, solved, factors.compose ν, holds⟩

/-- An instance of a principal answer through which the guard is respected. -/
theorem respects_factor {G : S → Prop} (respects : Respects A G) {σ τ : S} {ν : S}
    (through : ∀ t : T, A.E (A.apply σ t) (A.apply (A.compose ν τ) t)) :
    G σ ↔ G (A.compose ν τ) :=
  respects σ (A.compose ν τ) through

variable {store : EquationStore T} {μ : S} {G : S → Prop}

/-- **A stable guard asked at every solution is the guard at a principal answer.** -/
theorem entails_iff_of_stable (principal : A.Principal store μ) (respects : Respects A G)
    (stable : Stable A G) : A.Entails store G ↔ G μ := by
  constructor
  · exact fun asked => asked μ principal.sound
  · intro holds σ solved
    obtain ⟨ν, through⟩ := principal.factors σ solved
    exact (respects_factor respects through).mpr (stable ν μ holds)

/-- **A co-stable guard holds at some solution exactly when it holds at a principal answer.** -/
theorem exists_iff_of_coStable (principal : A.Principal store μ) (respects : Respects A G)
    (coStable : CoStable A G) : (∃ σ, A.Models σ store ∧ G σ) ↔ G μ := by
  constructor
  · rintro ⟨σ, solved, holds⟩
    obtain ⟨ν, through⟩ := principal.factors σ solved
    exact coStable ν μ ((respects_factor respects through).mp holds)
  · exact fun holds => ⟨μ, principal.sound, holds⟩

/-- **Asked at every solution, a guard holds at a principal answer**; for a co-stable guard the
converse fails in general. -/
theorem at_principal_of_entails (principal : A.Principal store μ) (asked : A.Entails store G) : G μ :=
  asked μ principal.sound

/-- **The closure asked at every solution is the guard at a principal answer.** -/
theorem entails_closure_iff (principal : A.Principal store μ) (respects : Respects A G)
    (coStable : CoStable A G) : A.Entails store (Closure A store G) ↔ G μ := by
  constructor
  · intro asked
    obtain ⟨τ, solved, -, holds⟩ := asked μ principal.sound
    obtain ⟨ν, through⟩ := principal.factors τ solved
    exact coStable ν μ ((respects_factor respects through).mp holds)
  · intro holds σ solved
    obtain ⟨ν, through⟩ := principal.factors σ solved
    exact ⟨μ, principal.sound, ⟨ν, through⟩, holds⟩

/-- **A minimal complete set of solutions**: every member solves, every solution is an instance of a
member, and a solution of which a member is an instance is an instance of that member. -/
structure MinimalComplete (A : SubstitutionAction T S) (store : EquationStore T) (U : Set S) : Prop where
  sound : ∀ u ∈ U, A.Models u store
  complete : ∀ σ, A.Models σ store → ∃ u ∈ U, Factors A σ u
  minimal : ∀ u ∈ U, ∀ τ, A.Models τ store → Factors A u τ → Factors A τ u

variable {U : Set S}

/-- **Without a principal answer, the closure asked at every solution is the guard at every member of
a minimal complete set.** -/
theorem entails_closure_iff_complete (complete : MinimalComplete A store U) (respects : Respects A G)
    (coStable : CoStable A G) : A.Entails store (Closure A store G) ↔ ∀ u ∈ U, G u := by
  constructor
  · intro asked u member
    obtain ⟨τ, solved, factors, holds⟩ := asked u (complete.sound u member)
    obtain ⟨ν, through⟩ := complete.minimal u member τ solved factors
    exact coStable ν u ((respects_factor respects through).mp holds)
  · intro holds σ solved
    obtain ⟨u, member, factors⟩ := complete.complete σ solved
    exact ⟨u, complete.sound u member, factors, holds u member⟩

/-- **A co-stable guard holds at some solution exactly when it holds at some member** of a complete
set. -/
theorem exists_iff_complete (complete : MinimalComplete A store U) (respects : Respects A G)
    (coStable : CoStable A G) : (∃ σ, A.Models σ store ∧ G σ) ↔ ∃ u ∈ U, G u := by
  constructor
  · rintro ⟨σ, solved, holds⟩
    obtain ⟨u, member, ν, through⟩ := complete.complete σ solved
    exact ⟨u, member, coStable ν u ((respects_factor respects through).mp holds)⟩
  · rintro ⟨u, member, holds⟩
    exact ⟨u, complete.sound u member, holds⟩

/-- A principal answer is a minimal complete set of one. -/
theorem MinimalComplete.singleton (principal : A.Principal store μ) : MinimalComplete A store {μ} where
  sound u member := by
    rw [Set.mem_singleton_iff.mp member]
    exact principal.sound
  complete σ solved := ⟨μ, Set.mem_singleton μ, principal.factors σ solved⟩
  minimal u member τ solved _ := by
    rw [Set.mem_singleton_iff.mp member]
    exact principal.factors τ solved

end Readings

/-! ## The guarded step -/

section Guarded

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-- **A guarded firing**: a first-order firing and its guards, each a predicate of a solution. -/
structure GuardedFiring (T : Type uT) (S : Type uS) (O : Type uO) where
  firing : Firing T S O
  guards : List (S → Prop)

variable (A : SubstitutionAction T S) (label : O → T)

/-- The guards of a firing hold at a solution. -/
def GuardedFiring.Holds (f : GuardedFiring T S O) (σ : S) : Prop := ∀ g ∈ f.guards, g σ

/-- **The guarded one-frame step**: the first-order step whose firings also carry guards. -/
def guarded :
    Interface.Step.Standard (Frames.ofSubstitution A) O (Configuration T O) (fun _ => GuardedFiring T S O) where
  frame _ := PUnit.unit
  knowledge C := C.equations
  present C := C.present
  selection f := f.firing.selection
  target _ := PUnit.unit
  extension _ := A.identity
  information {C} f := f.firing.selection.problem label f.firing.rule C
  transported {C} f e member := (firstOrder A label).transported (s := C) f.firing e member
  Shapes {C} f := (firstOrder A label).Shapes (s := C) f.firing
  Holds {C} f b σ := (firstOrder A label).Holds (s := C) f.firing b σ ∧ f.Holds σ
  Admits {C} f := f.firing.Valid A label C ∧
    A.Entails (f.firing.selection.problem label f.firing.rule C) f.Holds
  admits_iff := by
    intro C f
    constructor
    · rintro ⟨valid, asked⟩
      obtain ⟨shapes, enabled, solvable, entails⟩ := (AnnotatedRuns.firstOrder_admits_iff A label C f.firing).mp valid
      exact ⟨shapes, enabled, solvable, fun b σ solved => ⟨entails b σ solved, asked σ solved⟩⟩
    · rintro ⟨shapes, enabled, solvable, entails⟩
      exact ⟨(AnnotatedRuns.firstOrder_admits_iff A label C f.firing).mpr
          ⟨shapes, enabled, solvable, fun b σ solved => (entails b σ solved).1⟩,
        fun σ solved => (entails PUnit.unit σ solved).2⟩
  preparedResult {C} f _ := f.firing.result label C
  present_preparedResult _ _ := rfl
  preparedSettle _ _ := A.identity
  knowledge_preparedResult {C} f p := (firstOrder A label).knowledge_preparedResult (s := C) f.firing p

/-- **Guarded admission**: first-order admission and the ask of the guards. -/
theorem guarded_admits_iff (C : Configuration T O) (f : GuardedFiring T S O) :
    (guarded A label).Admits (s := C) f ↔ f.firing.Valid A label C ∧
      A.Entails (f.firing.selection.problem label f.firing.rule C) f.Holds :=
  Iff.rfl

theorem guarded_result (C : Configuration T O) (f : GuardedFiring T S O)
    (admitted : (guarded A label).Admits (s := C) f) :
    (guarded A label).result f admitted = f.firing.result label C :=
  rfl

/-- A first-order firing with no guards. -/
def lift (f : Firing T S O) : GuardedFiring T S O := ⟨f, []⟩

/-- **The first-order step embeds**: a firing without guards is admitted exactly when it is
admitted in `firstOrder`. -/
theorem admits_lift_iff (C : Configuration T O) (f : Firing T S O) :
    (guarded A label).Admits (s := C) (lift f) ↔ (firstOrder A label).Admits (s := C) f := by
  constructor
  · exact fun admitted => admitted.1
  · intro valid
    exact ⟨valid, fun _ _ g member => by cases member⟩

theorem result_lift (C : Configuration T O) (f : Firing T S O)
    (admitted : (guarded A label).Admits (s := C) (lift f)) :
    (guarded A label).result (lift f) admitted =
      (firstOrder A label).result f ((admits_lift_iff A label C f).mp admitted) :=
  rfl

variable {A label} in
/-- **Runs of the first-order step are runs of the guarded step**, with the same last state. -/
def liftRun : {C : Configuration T O} → (firstOrder A label).Run C → (guarded A label).Run C
  | _, .nil C => .nil C
  | _, .cons f admitted rest => .cons (lift f) ((admits_lift_iff A label _ f).mpr admitted) (liftRun rest)

theorem liftRun_last : ∀ {C : Configuration T O} (r : (firstOrder A label).Run C),
    (liftRun r).last = r.last
  | _, .nil _ => rfl
  | _, .cons _ _ rest => liftRun_last rest

/-- Guarded admission depends only on the solutions and the present occurrences. -/
theorem guarded_admits_congr {C D : Configuration T O} (same : SameUpTo A C D) (f : GuardedFiring T S O) :
    (guarded A label).Admits (s := C) f ↔ (guarded A label).Admits (s := D) f := by
  have problems : A.Equivalent (f.firing.selection.problem label f.firing.rule C)
      (f.firing.selection.problem label f.firing.rule D) := by
    rw [problem_eq, problem_eq]
    exact equivalent_append A same.1 _
  constructor
  · rintro ⟨valid, asked⟩
    exact ⟨(Firing.valid_congr A label same).mp valid, fun σ solved => asked σ ((problems σ).mpr solved)⟩
  · rintro ⟨valid, asked⟩
    exact ⟨(Firing.valid_congr A label same).mpr valid, fun σ solved => asked σ ((problems σ).mp solved)⟩

/-- **Transport in the guarded step**: configurations with the same solutions and occurrences,
firings moving and having residuals as themselves. -/
def guardedTransport : Transport (guarded A label).toStep where
  Iso C D := PLift (SameUpTo A C D)
  toStateIso {C D} i :=
    { frame := Frames.Iso.refl PUnit.unit
      knowledge := Frames.Equivalent.trans (Frames.Iso.equivalent_refl _) (fun _ σ => i.down.1 σ)
      rename := Equiv.refl O
      present := by
        simp only [Equiv.refl_toEmbedding, Finset.map_refl]
        exact i.down.2 }
  refl C := ⟨GuardFreeProcessOrders.SameUpTo.refl A C⟩
  symm i := ⟨sameUpTo_symm A i.down⟩
  trans i j := ⟨GuardFreeProcessOrders.SameUpTo.trans A i.down j.down⟩
  Alike f f' := f = f'
  alike_equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  selection_alike same := congrArg _ same
  admits_alike same := same ▸ Iff.rfl
  result_alike {C} {f} _ same _ _ := by
    subst same
    exact ⟨GuardFreeProcessOrders.SameUpTo.refl A _⟩
  move _ f := f
  move_alike _ _ _ same := same
  move_refl _ := rfl
  move_trans _ _ _ := rfl
  move_symm _ _ := rfl
  selection_move _ f := (Interface.renameSelection_refl f.firing.selection).symm
  admits_move i f := (guarded_admits_congr A label i.down f).symm
  result_move i f _ := ⟨f.firing.result_congr A label i.down⟩
  residual _ _ f := f
  selection_residual _ _ _ := rfl
  move_residual _ _ _ _ := rfl

/-- **Diamonds close in the guarded step** whenever both orders are admitted. -/
theorem guarded_closes : (guardedTransport A label).Closes := by
  intro C f g first second afterFirst afterSecond
  obtain ⟨⟨same⟩⟩ := AnnotatedRuns.firstOrder_closes A label
    first.1 second.1 afterFirst.1 afterSecond.1
  exact ⟨⟨same⟩⟩

/-- **Independence in the guarded step is the four admissions.** -/
theorem guarded_independent_iff {C : Configuration T O} {f g : GuardedFiring T S O} :
    (guardedTransport A label).Independent C f g ↔
      (guarded A label).Admits (s := C) f ∧ (guarded A label).Admits (s := C) g ∧
        (guarded A label).Admits (s := f.firing.result label C) g ∧
        (guarded A label).Admits (s := g.firing.result label C) f := by
  rw [Transport.independent_iff_admits (guarded_closes A label)]
  constructor
  · rintro ⟨first, second, afterFirst, afterSecond⟩
    exact ⟨first, second, afterFirst, afterSecond⟩
  · rintro ⟨first, second, afterFirst, afterSecond⟩
    exact ⟨first, second, afterFirst, afterSecond⟩

end Guarded

#print axioms Factors.compose
#print axioms Closure.stable
#print axioms entails_iff_of_stable
#print axioms exists_iff_of_coStable
#print axioms at_principal_of_entails
#print axioms entails_closure_iff
#print axioms entails_closure_iff_complete
#print axioms exists_iff_complete
#print axioms MinimalComplete.singleton
#print axioms guarded_admits_iff
#print axioms admits_lift_iff
#print axioms result_lift
#print axioms liftRun_last
#print axioms guarded_admits_congr
#print axioms guarded_closes
#print axioms guarded_independent_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition
