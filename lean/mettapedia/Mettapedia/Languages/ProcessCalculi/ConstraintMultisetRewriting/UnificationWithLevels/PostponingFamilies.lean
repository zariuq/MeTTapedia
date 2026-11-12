import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.PostponingFragments

/-!
# Postponing classes of the tree's families, at one joint budget

Every conditional decision of the earlier line goes through `ContextualDependentDecisiveDriver.Settled`: a class on
which a fuel-indexed family's round is eventually constant, **not stuck**, and kept. Its hypotheses `firing` and
`uncovered` are the "not stuck" part, and at the tower they fail on `crossStore`.

**A postponing class** (`PostponingSettled`) keeps eventual constancy and closure and replaces "not stuck" by
"stuck only at a store without a principal answer". On it the run from the original store, at one joint budget for
the executables and the rounds, and with the same outcome at every larger joint budget, is solved with a principal
answer, refuted, or stuck at a nonempty residual that is exact for the original store and has no principal answer
(`PostponingSettled.outcome`).

* Every settled class is a postponing class (`Settled.postponing`).
* For a family whose round is eventually constant on every store, the stores without a principal answer form a
  postponing class (`noPrincipalSettled`). Postponing classes are closed under union (`PostponingSettled.union`).
* **At the tower** (`tower_sort_const`, `cross_sortTower_postponed`): the round of the tower's family `sortTower`
  is eventually constant on every store, so on `crossStore`, at one joint budget and at every larger one, its run is
  stuck at an exact residual without a principal answer. This is the joint-budget form of
  `UnificationWithLevels.DependentFibre.cross_postponed`.

**What a progress lemma by shape must now give** for a tower family: a postponing class containing the stores to be
decided. Its proof is a classification of the census heads (`ContextualDependentHeadView.classify`) in which every row
is read by some rule of the family, or holds only at stores without a principal answer. That lemma is not proved
here; the rows of the pattern rules (`patternLeft`, `patternRight`, `sameUnknown`, `twoUnknowns`) need the inversion,
pruning, intersection and narrowing of `MillerSolver` and `CodomainNarrowing` as rules of the family.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace DependentFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentDecisiveDriver
open ContextualDependentDecisiveFragment

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}

/-- **A postponing class for a family**: at each nonempty store of it the round is eventually the same at every
larger budget; that round, when it progresses, stays in the class; and when it is stuck, the store has no principal
answer. -/
structure PostponingSettled (family : Family levels) where
  holds : {Γ : Context rules} → EquationStore (TotalTerm Γ) → Prop
  settles : ∀ {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
    ∃ threshold, (∀ fuel, threshold ≤ fuel → family.round fuel problem = family.round threshold problem) ∧
      (family.round threshold problem = .stuck → NoPrincipal levels problem) ∧
      ∀ {update : Update levels problem} {smaller : Below (family.rank update.remaining) (family.rank problem)},
        family.round threshold problem = .progress update smaller → holds update.remaining

variable {family : Family levels}

/-- **Every settled class is a postponing class**: its round is never stuck. -/
def Settled.postponing (settled : Settled family) : PostponingSettled family where
  holds := settled.holds
  settles := by
    intro Γ problem inside nonempty
    obtain ⟨threshold, notStuck, same, stable⟩ := settled.settles inside nonempty
    exact ⟨threshold, same, fun stuck => absurd stuck notStuck, stable⟩

/-- **For a family whose round is eventually constant on every store, the stores without a principal answer form a
postponing class.** -/
def noPrincipalSettled (family : Family levels)
    (const : ∀ {Γ : Context rules} (problem : EquationStore (TotalTerm Γ)),
      EventuallyConst fun fuel => family.round fuel problem) : PostponingSettled family where
  holds := NoPrincipal levels
  settles := by
    intro Γ problem none _
    obtain ⟨threshold, same⟩ := const problem
    refine ⟨threshold, same, fun _ => none, fun {update} _ _ => ?_⟩
    intro Δ τ principal
    exact none _ ((update_exact update).principal_of_residual principal)

/-- **Postponing classes are closed under union.** -/
def PostponingSettled.union (one two : PostponingSettled family) : PostponingSettled family where
  holds problem := one.holds problem ∨ two.holds problem
  settles := by
    rintro Γ problem (inside | inside) nonempty
    · obtain ⟨threshold, same, forced, stable⟩ := one.settles inside nonempty
      exact ⟨threshold, same, forced, fun progressed => Or.inl (stable progressed)⟩
    · obtain ⟨threshold, same, forced, stable⟩ := two.settles inside nonempty
      exact ⟨threshold, same, forced, fun progressed => Or.inr (stable progressed)⟩

theorem advance_stuck (fuel : Nat) {Γ : Context rules} {original : EquationStore (TotalTerm Γ)}
    {state : Update levels original} (nonempty : state.remaining ≠ [])
    (computed : family.round fuel state.remaining = .stuck) :
    advance (family.solver fuel) state = .done (.stuck state) := by
  unfold advance
  split
  · rename_i empty
    exact absurd empty nonempty
  · simp only [Family.solver]
    rw [computed]

/-- How a run ends on a postponing class: decided, or stuck at a nonempty residual without a principal answer. -/
def Ends {Γ : Context rules} {original : EquationStore (TotalTerm Γ)} (outcome : Outcome levels original) : Prop :=
  outcome.Decided ∨ ∃ s, outcome = .stuck s ∧ s.remaining ≠ [] ∧ NoPrincipal levels s.remaining

namespace PostponingSettled

variable (settled : PostponingSettled family)

/-- From every state in the class, one joint threshold of budget and rounds ends the run, decided or postponed
where postponement is forced, with the same outcome at every larger budget and every larger number of rounds. -/
theorem eventually {Γ : Context rules} {original : EquationStore (TotalTerm Γ)} (state : Update levels original)
    (inside : settled.holds state.remaining) :
    ∃ fuel₀ rounds₀, ∀ fuel, fuel₀ ≤ fuel → ∀ rounds, rounds₀ ≤ rounds →
      drive (family.solver fuel) rounds state = drive (family.solver fuel₀) rounds₀ state ∧
      Ends (drive (family.solver fuel₀) rounds₀ state) := by
  suffices key : ∀ rank (state : Update levels original), family.rank state.remaining = rank →
      settled.holds state.remaining →
      ∃ fuel₀ rounds₀, ∀ fuel, fuel₀ ≤ fuel → ∀ rounds, rounds₀ ≤ rounds →
        drive (family.solver fuel) rounds state = drive (family.solver fuel₀) rounds₀ state ∧
        Ends (drive (family.solver fuel₀) rounds₀ state) from key _ state rfl inside
  intro rank
  refine below_wf.induction (C := fun rank => ∀ state : Update levels original,
    family.rank state.remaining = rank → settled.holds state.remaining →
    ∃ fuel₀ rounds₀, ∀ fuel, fuel₀ ≤ fuel → ∀ rounds, rounds₀ ≤ rounds →
      drive (family.solver fuel) rounds state = drive (family.solver fuel₀) rounds₀ state ∧
      Ends (drive (family.solver fuel₀) rounds₀ state)) rank ?_
  intro rank ih state ranked inside
  by_cases empty : state.remaining = []
  · have finished : ∀ fuel rounds, drive (family.solver fuel) (rounds + 1) state = .solved state empty := by
      intro fuel rounds
      rw [drive_succ, Settled.advance_empty fuel empty]
    refine ⟨0, 1, fun fuel _ rounds enough => ?_⟩
    obtain ⟨rounds, rfl⟩ : ∃ k, rounds = k + 1 := ⟨rounds - 1, by omega⟩
    rw [finished, finished]
    exact ⟨rfl, Or.inl trivial⟩
  · obtain ⟨threshold, same, forced, stable⟩ := settled.settles inside empty
    cases computed : family.round threshold state.remaining with
    | stuck =>
        have step : ∀ fuel', threshold ≤ fuel' → ∀ rounds',
            drive (family.solver fuel') (rounds' + 1) state = .stuck state := by
          intro fuel' enough' rounds'
          rw [drive_succ, advance_stuck fuel' empty ((same fuel' enough').trans computed)]
        refine ⟨threshold, 1, fun fuel enough rounds more => ?_⟩
        obtain ⟨rounds, rfl⟩ : ∃ k, rounds = k + 1 := ⟨rounds - 1, by omega⟩
        rw [step fuel enough rounds, step threshold le_rfl 0]
        exact ⟨rfl, Or.inr ⟨state, rfl, empty, forced computed⟩⟩
    | refuted absent =>
        have step : ∀ fuel', threshold ≤ fuel' → ∀ rounds',
            drive (family.solver fuel') (rounds' + 1) state =
              .refuted fun solvable => absent (state.solvable_iff.mp solvable) := by
          intro fuel' enough' rounds'
          rw [drive_succ, Settled.advance_refuted fuel' empty ((same fuel' enough').trans computed)]
        refine ⟨threshold, 1, fun fuel enough rounds more => ?_⟩
        obtain ⟨rounds, rfl⟩ : ∃ k, rounds = k + 1 := ⟨rounds - 1, by omega⟩
        rw [step fuel enough rounds, step threshold le_rfl 0]
        exact ⟨rfl, Or.inl trivial⟩
    | progress update smaller =>
        have nextInside := stable computed
        have smaller' := smaller
        rw [ranked] at smaller'
        obtain ⟨fuel₁, rounds₁, later⟩ := ih _ smaller' (state.then update) rfl nextInside
        have step : ∀ fuel', threshold ≤ fuel' → ∀ rounds',
            drive (family.solver fuel') (rounds' + 1) state =
              drive (family.solver fuel') rounds' (state.then update) := by
          intro fuel' enough' rounds'
          rw [drive_succ, Settled.advance_progress fuel' empty ((same fuel' enough').trans computed)]
        refine ⟨max threshold fuel₁, rounds₁ + 1, fun fuel enough rounds more => ?_⟩
        obtain ⟨rounds, rfl⟩ : ∃ k, rounds = k + 1 := ⟨rounds - 1, by omega⟩
        rw [step fuel (le_of_max_le_left enough), step (max threshold fuel₁) (le_max_left _ _)]
        obtain ⟨first, ends⟩ := later fuel (le_of_max_le_right enough) rounds (by omega)
        obtain ⟨second, _⟩ := later (max threshold fuel₁) (le_max_right _ _) rounds₁ le_rfl
        exact ⟨first.trans second.symm, second ▸ ends⟩

/-- **Decided, or postponed where postponement is forced, at one joint budget**: on a postponing class, the run
from the original store reaches a principal answer, a certified refutation, or a stuck state whose nonempty residual
is exact for the original store and has no principal answer, and the same outcome at every larger joint budget. -/
theorem outcome {Γ : Context rules} {original : EquationStore (TotalTerm Γ)} (inside : settled.holds original) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (family.solver larger) original larger = run (family.solver budget) original budget ∧
      ((∃ state finished, run (family.solver larger) original larger = .solved state finished ∧
          (frames levels).Principal original state.answer) ∨
        (∃ absent, run (family.solver larger) original larger = .refuted absent) ∨
        (∃ state, run (family.solver larger) original larger = .stuck state ∧ state.remaining ≠ [] ∧
          Exact (frames levels) original state.answer state.remaining ∧ NoPrincipal levels state.remaining)) := by
  obtain ⟨fuel₀, rounds₀, eventual⟩ := settled.eventually (Update.pending levels original) inside
  refine ⟨max fuel₀ rounds₀, fun larger enough => ?_⟩
  obtain ⟨atLarger, ends⟩ := eventual larger (le_of_max_le_left enough) larger (le_of_max_le_right enough)
  obtain ⟨atBudget, _⟩ := eventual (max fuel₀ rounds₀) (le_max_left _ _) (max fuel₀ rounds₀) (le_max_right _ _)
  unfold run
  refine ⟨atLarger.trans atBudget.symm, ?_⟩
  rw [atLarger]
  rcases ends with decided | ⟨s, isStuck, nonempty, none⟩
  · cases result : drive (family.solver fuel₀) rounds₀ (Update.pending levels original) with
    | solved state finished => exact .inl ⟨state, finished, rfl, state.completed finished⟩
    | refuted absent => exact .inr (.inl ⟨absent, rfl⟩)
    | stuck _ =>
        rw [result] at decided
        exact False.elim decided
    | cutoff _ =>
        rw [result] at decided
        exact False.elim decided
  · rw [isStuck]
    exact .inr (.inr ⟨s, rfl, nonempty, update_exact s, none⟩)

end PostponingSettled

/-! ## At the tower -/

open ContextualDependentEtaDepth ContextualDependentPatternFiring.Controls

/-- **The round of the tower's family `sortTower` is eventually constant on every store.** -/
theorem tower_sort_const {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => sortTower.round fuel problem :=
  sortRound_const (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))
    ContextualDependentIntersectionGeneral.DeadControls.tower_strengthening towerSorts
    ContextualDependentDecisiveFragment.Controls.stable problem

open ContextualDependentSweep.Witnesses in
/-- **At the tower, `sortTower` postpones `crossStore` at one joint budget**: from some budget on, the run is stuck,
the same at every larger budget, at a nonempty residual that is exact for `crossStore` and has no principal answer. -/
theorem cross_sortTower_postponed :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (sortTower.solver larger) crossStore larger = run (sortTower.solver budget) crossStore budget ∧
      ∃ state, run (sortTower.solver larger) crossStore larger = .stuck state ∧ state.remaining ≠ [] ∧
        Exact (frames setting.levels) crossStore state.answer state.remaining ∧
        NoPrincipal setting.levels state.remaining := by
  have none : NoPrincipal setting.levels crossStore := fun answer => fragment_without_principal_answer.2.2 answer
  obtain ⟨budget, ends⟩ := (noPrincipalSettled sortTower tower_sort_const).outcome none
  refine ⟨budget, fun larger enough => ⟨(ends larger enough).1, ?_⟩⟩
  rcases (ends larger enough).2 with ⟨state, _, _, principal⟩ | ⟨absent, _⟩ | stuck
  · exact absurd principal (none state.answer)
  · exact absurd fragment_without_principal_answer.2.1 absent
  · exact stuck

end DependentFibre

#print axioms DependentFibre.noPrincipalSettled
#print axioms DependentFibre.PostponingSettled.eventually
#print axioms DependentFibre.PostponingSettled.outcome
#print axioms DependentFibre.tower_sort_const
#print axioms DependentFibre.cross_sortTower_postponed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
