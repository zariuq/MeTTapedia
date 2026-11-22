import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.DependentFibre

/-!
# Postponing fragments of the tree's driver: decided, or stuck only where no principal answer exists

The tree's worklist driver decides the stores of a `ContextualDependentWorklist.Fragment`: a class of stores kept by
the solver's updates on which it is **never stuck** (`Fragment.decided`). Every conditional decision of the earlier
line asks for such a class containing the dynamic pattern fragment, and at the tower none exists: the fragment holds
`crossStore`, solvable and without principal answer, on which every exact run stops postponed.

The true replacement asks less. **A postponing fragment** (`PostponingFragment`) is a class kept by the solver's
updates on which the solver is stuck **only at stores without a principal answer**. On it every run ends, at some
budget and at every larger one, in one of three ways (`PostponingFragment.outcome`):

* solved, with a principal answer of the original store;
* refuted, with a certificate;
* stuck at a residual store that is exact for the original store and has no principal answer, so that no exact run
  from it can end solved (`ExactTransitions.not_solved_of_no_principal`): the postponement is forced.

* Every fragment of the driver is a postponing fragment (`Fragment.postponing`).
* **The stores without a principal answer form a postponing fragment of every solver** (`noPrincipal`): a principal
  answer of a residual store would give one of the store, along the exact update (`Exact.principal_of_residual`).
* Postponing fragments are closed under union (`PostponingFragment.union`): a fragment on which a solver is
  decisive, joined with the stores without a principal answer, is the shape of the class that a progress lemma by
  shape has to produce for the tree's families.
* At the tower, every run of every solver on `crossStore` ends stuck, at an exact residual without a principal answer
  (`cross_run_postponed`).

What this module does not do is the progress lemma by shape itself: that the rounds of the tree's families, on a
class kept by their rules, are stuck only where no principal answer exists. That lemma replaces the hypotheses
`uncovered` and `firing` of the conditional decisions, which ask for no stuck store at all.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Interface

universe uO uT uH

section General

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {X : Frames Tm Hom}

/-- **Principal answers are reflected along exact transitions**: a principal answer of the residual, after the
transition, is a principal answer of the store. -/
theorem Exact.principal_of_residual {a m n : Obj} {S : EquationStore (Tm a)} {σ : Hom a m}
    {R : EquationStore (Tm m)} (exact : Exact X S σ R) {τ : Hom m n} (principal : X.Principal R τ) :
    X.Principal S (X.comp τ σ) :=
  exact_nil_iff_principal.mp (exact.trans (exact_nil_iff_principal.mpr principal))

end General

namespace DependentFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}

/-- A store has no principal answer. -/
def NoPrincipal (levels : LevelModel rules L) {Γ : Context rules} (problem : EquationStore (TotalTerm Γ)) : Prop :=
  ∀ {Δ : Context rules} (answer : Δ ⟶ Γ), ¬ (frames levels).Principal problem answer

/-- **A postponing fragment for a solver**: a class of stores kept by its updates, on which it is stuck only at
stores without a principal answer. -/
structure PostponingFragment (solver : ContextualDependentWorklist.Solver levels) where
  holds : {Γ : Context rules} → EquationStore (TotalTerm Γ) → Prop
  stable : ∀ {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)} {update : Update levels problem}
    {smaller : Below (solver.rank update.remaining) (solver.rank problem)},
    holds problem → solver.round problem = .progress update smaller → holds update.remaining
  forced : ∀ {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)},
    holds problem → problem ≠ [] → solver.round problem = .stuck → NoPrincipal levels problem

variable {solver : ContextualDependentWorklist.Solver levels}

/-- **Every fragment of the driver is a postponing fragment**: it is never stuck. -/
def Fragment.postponing (fragment : ContextualDependentWorklist.Fragment solver) : PostponingFragment solver where
  holds := fragment.holds
  stable := fragment.stable
  forced := fun inside nonempty stuck => absurd stuck (fragment.decisive inside nonempty)

/-- **The stores without a principal answer form a postponing fragment of every solver.** -/
def noPrincipal (solver : ContextualDependentWorklist.Solver levels) : PostponingFragment solver where
  holds := NoPrincipal levels
  stable := by
    intro Γ problem update smaller none _ Δ τ principal
    exact none _ ((update_exact update).principal_of_residual principal)
  forced := fun none _ _ => none

/-- **Postponing fragments are closed under union.** -/
def PostponingFragment.union (one two : PostponingFragment solver) : PostponingFragment solver where
  holds problem := one.holds problem ∨ two.holds problem
  stable := by
    rintro Γ problem update smaller (inside | inside) progressed
    · exact Or.inl (one.stable inside progressed)
    · exact Or.inr (two.stable inside progressed)
  forced := by
    rintro Γ problem (inside | inside) nonempty stuck
    · exact one.forced inside nonempty stuck
    · exact two.forced inside nonempty stuck

/-- A round that ends the run stuck reports the state it started from. -/
theorem advance_done_stuck_state {Γ : Context rules} {original : EquationStore (TotalTerm Γ)}
    {state s : Update levels original} (ended : advance solver state = .done (.stuck s)) : s = state := by
  unfold advance at ended
  split at ended
  · cases ended
  · split at ended
    · cases ended
    · cases ended
    · cases ended
      rfl

namespace PostponingFragment

variable (fragment : PostponingFragment solver)

/-- From every state in the fragment, the driver ends at some budget, and a stuck end is at a nonempty residual
without a principal answer. -/
theorem ends {Γ : Context rules} {original : EquationStore (TotalTerm Γ)} (state : Update levels original)
    (inside : fragment.holds state.remaining) :
    ∃ fuel, (drive solver fuel state).Finished ∧ ∀ s, drive solver fuel state = .stuck s →
      s.remaining ≠ [] ∧ NoPrincipal levels s.remaining := by
  suffices key : ∀ rank (state : Update levels original), solver.rank state.remaining = rank →
      fragment.holds state.remaining → ∃ fuel, (drive solver fuel state).Finished ∧
        ∀ s, drive solver fuel state = .stuck s → s.remaining ≠ [] ∧ NoPrincipal levels s.remaining from
    key _ state rfl inside
  intro rank
  refine below_wf.induction (C := fun rank => ∀ state : Update levels original,
    solver.rank state.remaining = rank → fragment.holds state.remaining → ∃ fuel,
      (drive solver fuel state).Finished ∧
        ∀ s, drive solver fuel state = .stuck s → s.remaining ≠ [] ∧ NoPrincipal levels s.remaining) rank ?_
  intro rank ih state ranked inside
  cases decided : advance solver state with
  | done outcome =>
      refine ⟨1, ?_, fun s stuck => ?_⟩
      · rw [drive_succ, decided]
        exact advance_done_finished solver decided
      · rw [drive_succ, decided] at stuck
        subst stuck
        have same := advance_done_stuck_state decided
        subst same
        obtain ⟨nonempty, isStuck⟩ := advance_done_stuck solver decided (fun h => h)
        exact ⟨nonempty, fragment.forced inside nonempty isStuck⟩
  | next next =>
      have smaller := advance_next solver decided
      rw [ranked] at smaller
      obtain ⟨update, _, isProgress, rfl⟩ := advance_next_progress solver decided
      obtain ⟨fuel, finished, stuck⟩ := ih _ smaller (state.then update) rfl
        (fragment.stable (update := update) inside isProgress)
      refine ⟨fuel + 1, ?_, fun s hs => ?_⟩
      · rw [drive_succ, decided]
        exact finished
      · rw [drive_succ, decided] at hs
        exact stuck s hs

/-- **Decided, or postponed where postponement is forced**: on a postponing fragment, the run from the original
store ends at some budget, with the same outcome at every larger budget, solved with a principal answer, refuted, or
stuck at a nonempty residual that is exact for the original store and has no principal answer. -/
theorem outcome {Γ : Context rules} {original : EquationStore (TotalTerm Γ)} (inside : fragment.holds original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run solver original larger = run solver original fuel ∧
      ((∃ state finished, run solver original larger = .solved state finished ∧
          (frames levels).Principal original state.answer) ∨
        (∃ absent, run solver original larger = .refuted absent) ∨
        (∃ state, run solver original larger = .stuck state ∧ state.remaining ≠ [] ∧
          Exact (frames levels) original state.answer state.remaining ∧ NoPrincipal levels state.remaining)) := by
  obtain ⟨fuel, finished, stuck⟩ := fragment.ends (Update.pending levels original) inside
  refine ⟨fuel, fun larger enough => ?_⟩
  have same := drive_mono solver fuel _ finished larger enough
  refine ⟨same, ?_⟩
  unfold run
  rw [same]
  cases result : drive solver fuel (Update.pending levels original) with
  | solved state finished => exact .inl ⟨state, finished, rfl, state.completed finished⟩
  | refuted absent => exact .inr (.inl ⟨absent, rfl⟩)
  | stuck state =>
      obtain ⟨nonempty, none⟩ := stuck state result
      exact .inr (.inr ⟨state, rfl, nonempty, update_exact state, none⟩)
  | cutoff _ =>
      rw [result] at finished
      exact False.elim finished

end PostponingFragment

open ContextualDependentSweep.Witnesses in
/-- **At the tower, every run of every solver on `crossStore` ends postponed**: at some budget, and at every larger
one, it is stuck at a nonempty residual that is exact for `crossStore` and has no principal answer. -/
theorem cross_run_postponed
    (solver : ContextualDependentWorklist.Solver ContextualDependentPatternFiring.Controls.setting.levels) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run solver crossStore larger = run solver crossStore fuel ∧
      ∃ state, run solver crossStore larger = .stuck state ∧ state.remaining ≠ [] ∧
        Exact (frames ContextualDependentPatternFiring.Controls.setting.levels) crossStore state.answer
          state.remaining ∧
        NoPrincipal ContextualDependentPatternFiring.Controls.setting.levels state.remaining := by
  have none : NoPrincipal ContextualDependentPatternFiring.Controls.setting.levels crossStore :=
    fun answer => fragment_without_principal_answer.2.2 answer
  obtain ⟨fuel, ends⟩ := (noPrincipal solver).outcome none
  refine ⟨fuel, fun larger enough => ⟨(ends larger enough).1, ?_⟩⟩
  rcases (ends larger enough).2 with ⟨state, _, _, principal⟩ | ⟨absent, _⟩ | stuck
  · exact absurd principal (none state.answer)
  · exact absurd fragment_without_principal_answer.2.1 absent
  · exact stuck

end DependentFibre

#print axioms Exact.principal_of_residual
#print axioms DependentFibre.noPrincipal
#print axioms DependentFibre.PostponingFragment.ends
#print axioms DependentFibre.PostponingFragment.outcome
#print axioms DependentFibre.cross_run_postponed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
