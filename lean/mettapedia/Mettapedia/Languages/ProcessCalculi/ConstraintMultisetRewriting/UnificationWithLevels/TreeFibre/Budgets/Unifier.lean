import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Budgets.Laws
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.InPlaceAudit
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveDriver

/-!
# The unifier's three remaining budgets, as outcomes

Rounds are driven by the solver's rank everywhere (`runRank`, `Decided.ofRank`). Three budgets remain, and each is
made a budgeted decision procedure here, with three outcomes and the laws of `Budgets.Laws`:

* **The budget inside one round** (`rounds`). A fuel-indexed solver family passes its budget to the executable type
  checker (the depth of `synth`, `check` and `below`) and to the reducer (the length of each normalization), at
  every call inside a round; a call that runs out returns nothing, its rule declines or takes another branch, and the
  round never says that it ran out. At
  budget `k`, the procedure takes the first decision among the runs of the family's solver at the budgets `0 … k`,
  each driven by the rank, so with no budget of rounds. Every run with a budget of rounds that decides is the run
  the procedure reads (`rounds_attempt_eq`). **Law 4 holds on every class where the family settles**
  (`rounds_answered`): this restates `ContextualDependentDecisiveDriver.Settled.decided`, whose conclusion reads
  "at some joint budget, and at every larger one", as an answer of the procedure at some budget.
* **The depth of phases** (`phasesDepth`). Over the empty telescope there is nothing to phase or exchange, and every
  depth decides what the base decides (`phases_empty`); a phase that decides nothing at a depth leaves its base
  undecided (`base_none_of_phases`).
* **The reader's depth** (`readerDepth`). The reader returns derivations only: it answers yes or nothing, never no
  (`reader_never_no`). Over the empty telescope every depth reads what the fragment's reader reads (`read_empty`).
  A store that does not settle is never read, at any depth (`reader_undecided_of_not_settles`).

**Decisions as answers** (`ofDecided`): the answers of the first two are the decisions themselves, a finished update
or a refutation; a yes carries a principal answer (`principal_of_equal`), a no the lack of solutions. **A solvable
store without a principal answer is exhausted at every budget, by every decision of stores**
(`undecided_of_no_principal`): no budget can answer it, so for it exhaustion is the only honest outcome.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre.Budgets

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open NativeTypesOnTheStep.Computing

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Decisions of stores as answers -/

section Stores

variable {S : Setting Head L}

/-- A store, with its telescope. -/
abbrev Stored (S : Setting Head L) : Type := Σ Θ : Context S.R, EquationStore (TotalTerm Θ)

/-- **The unifier's question**: the store has a solution. -/
def HasSolution (q : Stored S) : Prop := (frames S.levels).Solvable q.2

/-- A finished update says yes, a refutation says no. -/
def decidedSign {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} : Decided problem → Bool
  | .solved _ _ => true
  | .refuted _ => false

/-- **A budget-indexed decision of stores is a decider of solvability**; its answers are the decisions themselves. -/
def ofDecided (attempt : Nat → ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)), Option (Decided problem)) :
    Decider (HasSolution (S := S)) where
  Answer q := Decided q.2
  attempt k q := attempt k q.2
  sign a := decidedSign a
  yes a h := by
    cases a with
    | solved update finished => exact (update.completed finished).solvable
    | refuted missing => simp [decidedSign] at h
  no a h := by
    cases a with
    | solved update finished => simp [decidedSign] at h
    | refuted missing => exact missing

variable (attempt : Nat → ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)), Option (Decided problem))

/-- **A yes carries a principal answer.** -/
theorem principal_of_equal {k : Nat} {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (yes : (ofDecided attempt).procedure.verdict k ⟨Θ, problem⟩ = .equal) :
    ∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), (frames S.levels).Principal problem answer := by
  change (ofDecided attempt).verdictOf (firstUpTo (ofDecided attempt).attempt ⟨Θ, problem⟩ k) = .equal at yes
  cases found : firstUpTo (ofDecided attempt).attempt ⟨Θ, problem⟩ k with
  | none =>
      rw [found] at yes
      simp [Decider.verdictOf] at yes
  | some a =>
      rw [found] at yes
      cases a with
      | solved update finished => exact ⟨update.target, update.answer, update.completed finished⟩
      | refuted missing => simp [Decider.verdictOf, ofDecided, decidedSign] at yes

/-- **A solvable store without a principal answer is exhausted at every budget**, by every decision of stores. -/
theorem undecided_of_no_principal {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (solvable : (frames S.levels).Solvable problem)
    (noPrincipal : ∀ {Δ : Context S.R} (answer : Δ ⟶ Θ), ¬ (frames S.levels).Principal problem answer) (k : Nat) :
    (ofDecided attempt).procedure.verdict k ⟨Θ, problem⟩ = .undecided :=
  (ofDecided attempt).undecided_of_empty (fun d => by
    cases d with
    | solved update finished => exact noPrincipal update.answer (update.completed finished)
    | refuted missing => exact missing solvable) k

end Stores

/-! ## The budget inside one round -/

section Rounds

variable {S : Setting Head L} (family : ContextualDependentDecisiveDriver.Family S.levels)

/-- **The budget inside one round, as an outcome**: at budget `k`, the first decision among the runs of the family's
solver at the budgets `0 … k`, each driven by its rank, with no budget of rounds. -/
def rounds : Decider (HasSolution (S := S)) :=
  ofDecided fun k _ problem => Decided.ofRank (family.solver k) problem

/-- **No budget of rounds hides in it**: wherever a run with a budget of rounds decides, the attempt at that budget
inside a round decides the same. -/
theorem rounds_attempt_eq {k fuel : Nat} {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (found : (Decided.ofRun (family.solver k) fuel problem).isSome = true) :
    (rounds family).attempt k ⟨Θ, problem⟩ = Decided.ofRun (family.solver k) fuel problem :=
  Decided.ofRank_eq_ofRun found

/-- **Law 4 on every class where the family settles**: `Settled.decided` ("at some joint budget, and every larger"),
restated as an answer of the procedure at some budget. -/
theorem rounds_answered (settled : ContextualDependentDecisiveDriver.Settled family) :
    (rounds family).procedure.AnsweredOn fun q => settled.holds q.2 := by
  rintro ⟨Θ, problem⟩ inside
  obtain ⟨budget, eventual⟩ := settled.decided inside
  have found : (Decided.ofRun (family.solver budget) budget problem).isSome = true := by
    rcases (eventual budget le_rfl).2 with ⟨state, finished, ran, _⟩ | ⟨missing, ran⟩ <;>
      simp [Decided.ofRun, ran]
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp found
  exact (rounds family).answered_iff.mpr ⟨budget, d, (rounds_attempt_eq family found).trans hd⟩

end Rounds

/-! ## The depth of phases and the reader's depth -/

section Depths

variable {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

section Phases

variable (base : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)), Option (Decided problem))

/-- **The depth of phases, as an outcome**: at budget `k`, the first decision in phases at a depth up to `k`. -/
def phasesDepth (fuel : Nat) : Decider (HasSolution (S := S)) :=
  ofDecided fun depth _ problem => phases facts roots heads algebra declared choices reducer base fuel depth problem

/-- **Over the empty telescope every depth decides what the base decides**: there is no declaration to phase at
or to exchange. -/
theorem phases_empty (fuel depth : Nat) (problem : EquationStore (TotalTerm (empty S.R))) :
    phases facts roots heads algebra declared choices reducer base fuel depth problem = base problem := by
  cases depth with
  | zero => rfl
  | succ depth =>
      have noNewest : newestOf facts roots heads algebra declared choices reducer fuel (empty S.R) = none := rfl
      cases found : base problem with
      | some d => simp only [phases, found]
      | none => simp only [phases, found, noNewest]

/-- So a store over the empty telescope that the base leaves undecided is exhausted at every depth. -/
theorem phases_empty_undecided (fuel : Nat) {problem : EquationStore (TotalTerm (empty S.R))}
    (undecided : base problem = none) (k : Nat) :
    (phasesDepth facts roots heads algebra declared choices reducer base fuel).procedure.verdict k
      ⟨empty S.R, problem⟩ = .undecided :=
  (phasesDepth facts roots heads algebra declared choices reducer base fuel).verdict_undecided_iff.mpr
    fun j _ => (phases_empty facts roots heads algebra declared choices reducer base fuel j problem).trans undecided

/-- A store undecided in phases at a positive depth is undecided by the base. -/
theorem base_none_of_phases {fuel depth : Nat} {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (missing : phases facts roots heads algebra declared choices reducer base fuel (depth + 1) problem = none) :
    base problem = none := by
  cases found : base problem with
  | none => rfl
  | some d => simp [phases, found] at missing

end Phases

section Reader

variable (fragment : ∀ {Γ : Context S.R}, EquationStore (TotalTerm Γ) → Prop)
  (qW : ∀ {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)), Option (PLift (fragment problem)))

/-- **The reader's depth, as an outcome**: at budget `k`, a derivation found at a depth up to `k`. Its answers are
derivations; it never answers no. -/
def readerDepth (fuel : Nat) : Decider (fun q : Stored S => Through fragment q.2) where
  Answer q := PLift (Through fragment q.2)
  attempt depth q := throughRead fragment facts roots heads algebra declared choices reducer qW fuel depth q.2
  sign _ := true
  yes a _ := a.down
  no _ h := by cases h

/-- **The reader never answers no.** -/
theorem reader_never_no (fuel k : Nat) (q : Stored S) :
    (readerDepth facts roots heads algebra declared choices reducer fragment qW fuel).procedure.verdict k q ≠
      .different :=
  (readerDepth facts roots heads algebra declared choices reducer fragment qW fuel).verdict_ne_different
    (fun _ => rfl) k

/-- **Over the empty telescope every depth reads what the fragment's reader reads.** -/
theorem read_empty (fuel depth : Nat) (problem : EquationStore (TotalTerm (empty S.R))) :
    throughRead fragment facts roots heads algebra declared choices reducer qW fuel depth problem =
      (qW problem).map fun inside => ⟨.base inside.down⟩ := by
  cases depth with
  | zero => rfl
  | succ depth =>
      have noNewest : newestOf facts roots heads algebra declared choices reducer fuel (empty S.R) = none := rfl
      cases found : qW problem with
      | some inside => simp only [throughRead, found, Option.map_some]
      | none => simp only [throughRead, found, noNewest, Option.map_none]

/-- So a store over the empty telescope outside the fragment's reader is exhausted at every depth. -/
theorem read_empty_undecided (fuel : Nat) {problem : EquationStore (TotalTerm (empty S.R))}
    (unread : qW problem = none) (k : Nat) :
    (readerDepth facts roots heads algebra declared choices reducer fragment qW fuel).procedure.verdict k
      ⟨empty S.R, problem⟩ = .undecided :=
  (readerDepth facts roots heads algebra declared choices reducer fragment qW fuel).verdict_undecided_iff.mpr
    fun j _ => by
      show throughRead fragment facts roots heads algebra declared choices reducer qW fuel j problem = none
      rw [read_empty facts roots heads algebra declared choices reducer fragment qW fuel j problem, unread]
      rfl

/-- **A store that does not settle is never read**, when every store of the fragment settles. -/
theorem reader_undecided_of_not_settles (fuel : Nat)
    (settle : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, fragment problem → Settles problem)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (unsettled : ¬ Settles problem) (k : Nat) :
    (readerDepth facts roots heads algebra declared choices reducer fragment qW fuel).procedure.verdict k
      ⟨Θ, problem⟩ = .undecided :=
  (readerDepth facts roots heads algebra declared choices reducer fragment qW fuel).undecided_of_empty
    (fun a => unsettled (through_settles settle a.down)) k

end Reader

end Depths

end TreeFibre.Budgets

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

section Audit
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Budgets
#print axioms ofDecided
#print axioms principal_of_equal
#print axioms undecided_of_no_principal
#print axioms rounds
#print axioms rounds_attempt_eq
#print axioms rounds_answered
#print axioms phasesDepth
#print axioms phases_empty
#print axioms phases_empty_undecided
#print axioms base_none_of_phases
#print axioms readerDepth
#print axioms reader_never_no
#print axioms read_empty
#print axioms read_empty_undecided
#print axioms reader_undecided_of_not_settles
end Audit
