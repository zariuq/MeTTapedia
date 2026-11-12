import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.OneSolver

/-!
# Runs driven by the rank, with no budget of rounds

Every round of a solver of the tree's driver that progresses carries the decrease of the solver's own rank
(`ContextualDependentWorklist.Round.progress`), and the order of ranks is well founded (`below_wf`). So a run needs no
budget of rounds.

* **The run by well-founded recursion on the rank** (`driveWF`, `runWF`). It is never cut off (`driveWF_finished`). It
  is the run of every budget at which that run finishes (`drive_eq_driveWF`), hence of every large enough budget
  (`driveWF_eventually`), in particular of every budget at least its own number of rounds (`roundsWF`,
  `drive_eq_driveWF_of_rounds`). It decides exactly the stores that some budget decides (`driveWF_decided_iff`).
* **The same run, computed by structural recursion with its budgets read off the rank** (`driveRank`, `runRank`): the
  first component of the rank bounds the rounds that lower it (`outerRun`); at each such round, the second component
  of the new rank bounds the rounds that keep the first one (`innerRun`). It is the run by well-founded recursion
  (`driveRank_eq_driveWF`), and the kernel evaluates it.
* **On a fragment** the run reaches a principal answer or a certified refutation (`fragment_decidedWF`). The one
  solver's fragment is decided so, with no budget of rounds (`one_decidedWF`, `one_decidedWF_iff`).

The bound of the inner loop is not fixed in advance: a round that lowers the first component may raise the second one
arbitrarily, and the new bound is read from the new rank. A single budget read from the original rank does not exist
for a lexicographic rank in general; the nested loop is what the order of ranks allows.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

/-- The lexicographic order of ranks, read componentwise. -/
theorem below_iff {p q : Nat × Nat} :
    ContextualDependentWorklist.Below p q ↔ p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2) := by
  unfold ContextualDependentWorklist.Below
  exact Prod.lex_def

section Runs

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}
variable (solver : ContextualDependentWorklist.Solver levels) {Γ : Context rules}
  {original : EquationStore (TotalTerm Γ)}

/-! ## The run by well-founded recursion -/

/-- One round of the run, given the run at every state of smaller rank. -/
def stepWF (state : Update levels original)
    (recurse : (next : Update levels original) →
      ContextualDependentWorklist.Below (solver.rank next.remaining) (solver.rank state.remaining) →
        ContextualDependentWorklist.Outcome levels original) :
    ContextualDependentWorklist.Outcome levels original :=
  match h : advance solver state with
  | .done outcome => outcome
  | .next next => recurse next (advance_next solver h)

/-- **The run by well-founded recursion on the rank**: no budget of rounds. -/
noncomputable def driveWF : Update levels original → ContextualDependentWorklist.Outcome levels original :=
  (InvImage.wf (fun state : Update levels original => solver.rank state.remaining) below_wf).fix
    (fun state recurse => stepWF solver state recurse)

/-- **The run from the original store**, by well-founded recursion on the rank. -/
noncomputable def runWF (original : EquationStore (TotalTerm Γ)) : ContextualDependentWorklist.Outcome levels original :=
  driveWF solver (Update.pending levels original)

theorem driveWF_eq (state : Update levels original) :
    driveWF solver state = stepWF solver state (fun next _ => driveWF solver next) :=
  WellFounded.fix_eq _ _ _

/-- A round that ends the run ends the run by well-founded recursion. -/
theorem driveWF_done {state : Update levels original} {outcome : ContextualDependentWorklist.Outcome levels original}
    (ended : advance solver state = .done outcome) : driveWF solver state = outcome := by
  rw [driveWF_eq]
  unfold stepWF
  split
  · rename_i outcome' h
    rw [ended] at h
    cases h
    rfl
  · rename_i next h
    rw [ended] at h
    cases h

/-- A round that continues continues the run by well-founded recursion. -/
theorem driveWF_next {state next : Update levels original}
    (continued : advance solver state = .next next) : driveWF solver state = driveWF solver next := by
  rw [driveWF_eq]
  unfold stepWF
  split
  · rename_i outcome h
    rw [continued] at h
    cases h
  · rename_i next' h
    rw [continued] at h
    cases h
    rfl

/-- **Agreement with a budget**: wherever a run with a budget finishes, it is the run by well-founded recursion. -/
theorem drive_eq_driveWF : ∀ (fuel : Nat) (state : Update levels original),
    (drive solver fuel state).Finished → drive solver fuel state = driveWF solver state
  | 0, _, finished => False.elim finished
  | fuel + 1, state, finished => by
      rw [drive_succ] at finished ⊢
      cases decided : advance solver state with
      | done outcome =>
          rw [driveWF_done solver decided]
      | next next =>
          rw [decided] at finished
          rw [driveWF_next solver decided]
          exact drive_eq_driveWF fuel next finished

/-- **The run by well-founded recursion terminates**: it is never cut off. -/
theorem driveWF_finished (state : Update levels original) : (driveWF solver state).Finished := by
  obtain ⟨fuel, finished⟩ := drive_finishes solver state
  rw [← drive_eq_driveWF solver fuel state finished]
  exact finished

/-- **It is the run of every large enough budget.** -/
theorem driveWF_eventually (state : Update levels original) :
    ∃ bound, ∀ fuel, bound ≤ fuel → drive solver fuel state = driveWF solver state := by
  obtain ⟨bound, finished⟩ := drive_finishes solver state
  refine ⟨bound, fun fuel enough => ?_⟩
  rw [drive_mono solver bound state finished fuel enough]
  exact drive_eq_driveWF solver bound state finished

/-- **It decides exactly the stores that some budget decides.** -/
theorem driveWF_decided_iff (state : Update levels original) :
    (driveWF solver state).Decided ↔ ∃ fuel, (drive solver fuel state).Decided := by
  constructor
  · intro decided
    obtain ⟨bound, same⟩ := driveWF_eventually solver state
    refine ⟨bound, ?_⟩
    rw [same bound le_rfl]
    exact decided
  · rintro ⟨fuel, decided⟩
    rw [← drive_eq_driveWF solver fuel state decided.finished]
    exact decided

/-! ## The number of rounds -/

/-- One round counted, given the count at every state of smaller rank. -/
def roundsStep (state : Update levels original)
    (recurse : (next : Update levels original) →
      ContextualDependentWorklist.Below (solver.rank next.remaining) (solver.rank state.remaining) → Nat) : Nat :=
  match h : advance solver state with
  | .done _ => 1
  | .next next => recurse next (advance_next solver h) + 1

/-- **The number of rounds of the run**, by well-founded recursion on the rank. -/
noncomputable def roundsWF : Update levels original → Nat :=
  (InvImage.wf (fun state : Update levels original => solver.rank state.remaining) below_wf).fix
    (fun state recurse => roundsStep solver state recurse)

theorem roundsWF_done {state : Update levels original} {outcome : ContextualDependentWorklist.Outcome levels original}
    (ended : advance solver state = .done outcome) : roundsWF solver state = 1 := by
  unfold roundsWF
  rw [WellFounded.fix_eq]
  unfold roundsStep
  split
  · rfl
  · rename_i next h
    rw [ended] at h
    cases h

theorem roundsWF_next {state next : Update levels original}
    (continued : advance solver state = .next next) : roundsWF solver state = roundsWF solver next + 1 := by
  unfold roundsWF
  rw [WellFounded.fix_eq]
  unfold roundsStep
  split
  · rename_i outcome h
    rw [continued] at h
    cases h
  · rename_i next' h
    rw [continued] at h
    cases h
    rfl

/-- **The sufficient budget is the run's own number of rounds**: every budget at least that is the run by well-founded
recursion. -/
theorem drive_eq_driveWF_of_rounds (state : Update levels original) :
    ∀ fuel, roundsWF solver state ≤ fuel → drive solver fuel state = driveWF solver state := by
  refine (InvImage.wf (fun state : Update levels original => solver.rank state.remaining) below_wf).induction
    (C := fun state => ∀ fuel, roundsWF solver state ≤ fuel → drive solver fuel state = driveWF solver state)
    state ?_
  intro state ih fuel enough
  cases decided : advance solver state with
  | done outcome =>
      rw [roundsWF_done solver decided] at enough
      obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [drive_succ, decided, driveWF_done solver decided]
  | next next =>
      rw [roundsWF_next solver decided] at enough
      obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [drive_succ, decided, driveWF_next solver decided]
      exact ih next (advance_next solver decided) fuel (by omega)

/-! ## The same run by structural recursion, its budgets read off the rank -/

/-- **The rounds that keep the first component of the rank** at most `bound`, with the rounds that lower it below
`bound` handed to `lower`. The budget is the second component of the rank. -/
def innerRun (bound : Nat)
    (lower : (state : Update levels original) → (solver.rank state.remaining).1 < bound → ContextualDependentWorklist.Outcome levels original) :
    (budget : Nat) → (state : Update levels original) → (solver.rank state.remaining).1 ≤ bound →
      (solver.rank state.remaining).2 ≤ budget → ContextualDependentWorklist.Outcome levels original
  | 0, state, first, second =>
      match h : advance solver state with
      | .done outcome => outcome
      | .next next =>
          if lowered : (solver.rank next.remaining).1 < bound then lower next lowered
          else absurd (advance_next solver h) (by
            intro below
            rcases below_iff.mp below with lt | ⟨_, lt⟩ <;> omega)
  | budget + 1, state, first, second =>
      match h : advance solver state with
      | .done outcome => outcome
      | .next next =>
          if lowered : (solver.rank next.remaining).1 < bound then lower next lowered
          else innerRun bound lower budget next
            (by rcases below_iff.mp (advance_next solver h) with lt | ⟨eq, _⟩ <;> omega)
            (by rcases below_iff.mp (advance_next solver h) with lt | ⟨_, lt⟩ <;> omega)

/-- **The rounds that lower the first component of the rank**, by structural recursion on its bound; each such round
starts the inner loop again with the second component of the new rank as its budget. -/
def outerRun : (bound : Nat) → (state : Update levels original) → (solver.rank state.remaining).1 ≤ bound →
    ContextualDependentWorklist.Outcome levels original
  | 0, state, first =>
      innerRun solver 0 (fun _ lowered => absurd lowered (Nat.not_lt_zero _)) (solver.rank state.remaining).2 state
        first le_rfl
  | bound + 1, state, first =>
      innerRun solver (bound + 1) (fun next lowered => outerRun bound next (Nat.lt_succ_iff.mp lowered))
        (solver.rank state.remaining).2 state first le_rfl

/-- **The run driven by the rank**, by structural recursion: its budgets are read off the rank. -/
def driveRank (state : Update levels original) : ContextualDependentWorklist.Outcome levels original :=
  outerRun solver (solver.rank state.remaining).1 state le_rfl

/-- **The run driven by the rank from the original store.** -/
def runRank (original : EquationStore (TotalTerm Γ)) : ContextualDependentWorklist.Outcome levels original :=
  driveRank solver (Update.pending levels original)

theorem innerRun_eq (bound : Nat)
    (lower : (state : Update levels original) → (solver.rank state.remaining).1 < bound → ContextualDependentWorklist.Outcome levels original)
    (lowerWF : ∀ next lowered, lower next lowered = driveWF solver next) :
    ∀ (budget : Nat) (state : Update levels original) (first : (solver.rank state.remaining).1 ≤ bound)
      (second : (solver.rank state.remaining).2 ≤ budget),
      innerRun solver bound lower budget state first second = driveWF solver state := by
  intro budget
  induction budget with
  | zero =>
      intro state first second
      unfold innerRun
      split
      · rename_i outcome h
        exact (driveWF_done solver h).symm
      · rename_i next h
        split
        · rename_i lowered
          rw [lowerWF, driveWF_next solver h]
        · rename_i lowered
          exfalso
          rcases below_iff.mp (advance_next solver h) with lt | ⟨_, lt⟩ <;> omega
  | succ budget ih =>
      intro state first second
      unfold innerRun
      split
      · rename_i outcome h
        exact (driveWF_done solver h).symm
      · rename_i next h
        split
        · rename_i lowered
          rw [lowerWF, driveWF_next solver h]
        · rename_i lowered
          rw [ih, driveWF_next solver h]

theorem outerRun_eq : ∀ (bound : Nat) (state : Update levels original)
    (first : (solver.rank state.remaining).1 ≤ bound), outerRun solver bound state first = driveWF solver state
  | 0, state, first => by
      unfold outerRun
      exact innerRun_eq solver 0 _ (fun _ lowered => absurd lowered (Nat.not_lt_zero _)) _ state first le_rfl
  | bound + 1, state, first => by
      unfold outerRun
      exact innerRun_eq solver (bound + 1) _ (fun next _ => outerRun_eq bound next _) _ state first le_rfl

/-- **The run driven by the rank is the run by well-founded recursion.** -/
theorem driveRank_eq_driveWF (state : Update levels original) : driveRank solver state = driveWF solver state :=
  outerRun_eq solver _ state le_rfl

theorem runRank_eq_runWF (original : EquationStore (TotalTerm Γ)) : runRank solver original = runWF solver original :=
  driveRank_eq_driveWF solver _

/-- **The run driven by the rank is never cut off.** -/
theorem runRank_finished (original : EquationStore (TotalTerm Γ)) : (runRank solver original).Finished := by
  rw [runRank_eq_runWF]
  exact driveWF_finished solver _

/-- **Wherever a run with a budget finishes, it is the run driven by the rank.** -/
theorem run_eq_runRank {original : EquationStore (TotalTerm Γ)} {fuel : Nat}
    (finished : (run solver original fuel).Finished) : run solver original fuel = runRank solver original := by
  rw [runRank_eq_runWF]
  exact drive_eq_driveWF solver fuel _ finished

/-- **The run driven by the rank is the run of every large enough budget.** -/
theorem runRank_eventually (original : EquationStore (TotalTerm Γ)) :
    ∃ bound, ∀ fuel, bound ≤ fuel → run solver original fuel = runRank solver original := by
  rw [runRank_eq_runWF]
  exact driveWF_eventually solver _

/-- **The run driven by the rank decides exactly the stores that some budget decides.** -/
theorem runRank_decided_iff (original : EquationStore (TotalTerm Γ)) :
    (runRank solver original).Decided ↔ ∃ fuel, (run solver original fuel).Decided := by
  rw [runRank_eq_runWF]
  exact driveWF_decided_iff solver _

/-- **A refutation of the run driven by the rank is certified.** -/
theorem runRank_refuted {original : EquationStore (TotalTerm Γ)}
    (refuted : (runRank solver original).readout = .refuted) : ¬ (frames levels).Solvable original :=
  Outcome.readout_eq_refuted refuted

/-- **A solved run driven by the rank carries a principal answer.** -/
theorem runRank_solved_principal {original : EquationStore (TotalTerm Γ)} {state : Update levels original}
    {finished : state.remaining = []} (_ : runRank solver original = .solved state finished) :
    (frames levels).Principal original state.answer :=
  state.completed finished

/-! ## Fragments are decided with no budget -/

/-- **On a fragment the run by well-founded recursion reaches a principal answer or a certified refutation.** -/
theorem fragment_decidedWF (fragment : ContextualDependentWorklist.Fragment solver) (inside : fragment.holds original) :
    (∃ state finished, runWF solver original = .solved state finished ∧
        (frames levels).Principal original state.answer) ∨
      ∃ absent, runWF solver original = .refuted absent := by
  obtain ⟨fuel, decided⟩ := fragment.decided inside
  have same : run solver original fuel = runWF solver original := by
    apply drive_eq_driveWF
    rcases (decided fuel le_rfl).2 with ⟨state, finished, ran, _⟩ | ⟨absent, ran⟩
    · unfold run at ran
      rw [ran]
      trivial
    · unfold run at ran
      rw [ran]
      trivial
  rw [← same]
  exact (decided fuel le_rfl).2

/-- **On a fragment the run driven by the rank reaches a principal answer or a certified refutation.** -/
theorem fragment_decidedRank (fragment : ContextualDependentWorklist.Fragment solver) (inside : fragment.holds original) :
    (∃ state finished, runRank solver original = .solved state finished ∧
        (frames levels).Principal original state.answer) ∨
      ∃ absent, runRank solver original = .refuted absent := by
  rw [runRank_eq_runWF]
  exact fragment_decidedWF solver fragment inside

end Runs

/-! ## The one solver, with no budget of rounds -/

section One

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq]
variable (choices : ExecutableChecking.HeadChoices S.R)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (inh : Miller.Inhabitants S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)
  (strengthening : ContextualDependentIntersectionGeneral.EqualStrengthening S.R)
  (join : Head → Head → Option Head)
  (joinSound : ∀ {u v w : Head}, join u v = some w → S.R.isUniverse w ∧ IsLub S.R w u v)
  (glb : Head → Head → Option Head) (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)
  (glbTotal : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g)
  (joinTotal : ∀ {u v : Head}, S.R.isUniverse u → S.R.isUniverse v → ∃ w, join u v = some w)

include glbTotal joinTotal in
/-- **The one solver decides its fragment with no budget of rounds**: run by well-founded recursion on the common
rank, every store of its fragment reaches a principal answer or a certified refutation. -/
theorem one_decidedWF {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)} (inside : InOne choices original) :
    (∃ state finished,
        runWF (oneSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
          strengthening join joinSound glb spec) original = .solved state finished ∧
        (frames S.levels).Principal original state.answer) ∨
      ∃ absent, runWF (oneSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
        strengthening join joinSound glb spec) original = .refuted absent :=
  fragment_decidedWF _ (oneFragment choices facts roots heads algebra rigid complete normalizes inh headTypingUnique
    declared strengthening join joinSound glb spec glbTotal joinTotal) inside

/-- **The one solver with no budget decides exactly what it decides at some budget**, on every store. -/
theorem one_decidedWF_iff {Θ : Context S.R} (original : EquationStore (TotalTerm Θ)) :
    (runWF (oneSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
        strengthening join joinSound glb spec) original).Decided ↔
      ∃ fuel, (run (oneSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
        strengthening join joinSound glb spec) original fuel).Decided :=
  driveWF_decided_iff _ _

/-- **The one solver with no budget agrees with every budget at which it finishes.** -/
theorem one_run_eq_runWF {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)} {fuel : Nat}
    (finished : (run (oneSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
      strengthening join joinSound glb spec) original fuel).Finished) :
    run (oneSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
        strengthening join joinSound glb spec) original fuel =
      runWF (oneSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
        strengthening join joinSound glb spec) original :=
  drive_eq_driveWF _ fuel _ finished

end One

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre in
#print axioms driveWF_finished
