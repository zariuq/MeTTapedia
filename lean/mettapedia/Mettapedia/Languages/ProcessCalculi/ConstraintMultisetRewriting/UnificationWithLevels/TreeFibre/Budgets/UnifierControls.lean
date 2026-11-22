import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Budgets.Unifier
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.InPlaceAuditControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ThroughPhasesControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesCumulativePrincipal

/-!
# Controls: the unifier's three budgets as outcomes, in the tree's tower

For each budget, three controls: a store exhausted at `k` and solved at `k + 1`; a solvable store exhausted at every
budget; an unsolvable store exhausted at every budget, where one is proved.

**Inside one round** (the in-place solver of the tower as a fuel-indexed family, `inPlaceRounds`):
* `U_{max a 0} ≐ U_a` is exhausted at the budgets `0` and `1` and solved at `2` (`max_exhausted_then_solved`);
* `U0 : U1 ≐ U0 : U2` is answered no at budget `0` (`het_rounds_no`);
* the tree's in-place solver is the attempt at budget 16 (`inPlace_is_attempt16`), and what it decides the procedure
  decides by budget 16, the same way (`inPlace_decided_by16`); law 4 holds on the settled class of the
  solving-in-place witness (`blocked_answered`, restating `blocked_decided`);
* the cross store, solvable without a principal answer, is exhausted at every budget (`cross_rounds_exhausted`);
* the fixed store `λ x. F x ≐ λ x. x` over `F : U1 → U0`, unsolvable, is exhausted at the budgets `0 … 3`
  (`fixed_rounds_exhausted`); at every budget is not proved.

**The depth of phases** (`towerPhasesDepth`: the mixed solver as the base, at the checker's budget 6):
* `F ≐ λ x. x` over `F : U0 → U0` is exhausted at depth `0` and solved at depth `1` (`id_exhausted_then_solved`);
* the clash store `U_a ≐ U0` is answered no at depth `0` (`clash_phases_no`);
* the cross store is exhausted at every depth (`cross_phases_exhausted`);
* `U0 : U1 ≐ U0 : U2` over the empty telescope, unsolvable, is exhausted at every depth (`het_phases_exhausted`).

**Where a canonical order of declarations does not remove the depth.** The depth bounds the exchange of the two
newest declarations, which comes back after two exchanges (`exchange_twice_remaining`), and also the phase at the
newest declaration. A store over one declaration has a single order of declarations and no exchange, and its depth
still matters:
* `F ≐ λ x. x` is not decided by the base (`id_base`), is decided at depth `1` and not at depth `0` (`id_phases`), and
  its first phase at `F` is empty (`id_first_phase_empty`); the base decides its η-long form (`id_base`). By the
  definition of `phases`, the decision at depth `1` comes from the phase at `F`, whose empty first phase is followed
  by the store lifted along the empty decision and put in η-long form. A run whose rank falls only under exchanges
  toward an order, and under phases with a nonempty first phase, never takes that phase, so it leaves the store to the
  base and disagrees with the run at depth `1`;
* the fixed store, whose first phase at `F` is empty too (`fixed_first_phase_empty`), is exhausted at the depths
  `0 … 3` (`fixed_phases_exhausted`).

**The reader's depth** (`towerReaderDepth`, over the one solver's fragment):
* the dd store is exhausted at depth `0` and read at depth `1` (`dd_exhausted_then_read`);
* the cross store does not settle (`cross_not_settles`), so it is never read (`cross_reader_exhausted`);
* `U0 : U1 ≐ U0 : U2`, unsolvable, is never read (`het_reader_exhausted`), **although it lies in the class the reader
  reads** (`het_through`: it is equivalent to the clash store, which the fragment's reader reads). So law 4 for the
  reader needs its hypothesis: the reader answers exactly the stores it reads at some depth.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre.Budgets.TowerControls

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternFiring.Controls ContextualDependentSweep.Witnesses
open NativeTypesOnTheStep.Computing
open TreeFibre.Controls (U0 U1 U2 decidedKind towerMixedSolver towerPhases towerRead towerOneWitness)

/-! ## Reading kernel facts -/

theorem eq_none_of_isSome_false {α : Type} {o : Option α} (h : o.isSome = false) : o = none := by
  cases o with
  | none => rfl
  | some a => cases h

theorem none_of_kind {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {found : Option (Decided problem)} (undecided : decidedKind found = 0) : found = none := by
  rcases found with _ | ⟨update, finished⟩ | absent
  · rfl
  · simp [decidedKind] at undecided
  · simp [decidedKind] at undecided

theorem solvable_of_kind {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {found : Option (Decided problem)} (solved : decidedKind found = 1) : (frames setting.levels).Solvable problem := by
  obtain ⟨Δ, answer, principal⟩ := TreeFibre.Controls.principal_of_decided solved
  exact principal.solvable

theorem unsolvable_of_kind {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {found : Option (Decided problem)} (refuted : decidedKind found = 2) :
    ¬ (frames setting.levels).Solvable problem := by
  rcases found with _ | ⟨update, finished⟩ | absent
  · simp [decidedKind] at refuted
  · simp [decidedKind] at refuted
  · exact absent

/-- A refutation at budget `0` is a no at budget `0`. -/
theorem different_at_zero
    {attempt : Nat → ∀ {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)), Option (Decided problem)}
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (refuted : decidedKind ((ofDecided attempt).attempt 0 ⟨Θ, problem⟩) = 2) :
    (ofDecided attempt).procedure.verdict 0 ⟨Θ, problem⟩ = .different := by
  show (ofDecided attempt).verdictOf ((ofDecided attempt).attempt 0 ⟨Θ, problem⟩) = .different
  generalize (ofDecided attempt).attempt 0 ⟨Θ, problem⟩ = found at refuted ⊢
  rcases found with _ | ⟨update, finished⟩ | absent
  · simp [decidedKind] at refuted
  · simp [decidedKind] at refuted
  · simp [Decider.verdictOf, ofDecided, decidedSign]

/-- **The cross store does not settle**: it is solvable and has no principal answer. -/
theorem cross_not_settles : ¬ Settles crossStore := by
  rintro (⟨update, finished⟩ | absent)
  · exact cross_no_principal update.answer (update.completed finished)
  · exact absent cross_identity

/-! ## Inside one round -/

/-- The in-place solver of the tower, its budget inside a round as an outcome. -/
abbrev inPlaceRounds : Decider (HasSolution (S := setting)) :=
  rounds ContextualDependentInPlace.Controls.inPlaceTower

theorem max_attempts :
    (inPlaceRounds.attempt 0 ⟨_, AuditControls.maxStore⟩).isSome = false ∧
      (inPlaceRounds.attempt 1 ⟨_, AuditControls.maxStore⟩).isSome = false ∧
      decidedKind (inPlaceRounds.attempt 2 ⟨_, AuditControls.maxStore⟩) = 1 := by
  decide +kernel

/-- **Exhausted at budget `1`, solved at budget `2`.** -/
theorem max_exhausted_then_solved :
    inPlaceRounds.procedure.verdict 1 ⟨_, AuditControls.maxStore⟩ = .undecided ∧
      inPlaceRounds.procedure.verdict 2 ⟨_, AuditControls.maxStore⟩ = .equal := by
  obtain ⟨zero, one, two⟩ := max_attempts
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (AuditControls.isSome_of_kind two)
  have before : ∀ j, j ≤ 1 → inPlaceRounds.attempt j ⟨_, AuditControls.maxStore⟩ = none := by
    intro j le
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact eq_none_of_isSome_false zero
    · exact eq_none_of_isSome_false one
  obtain ⟨exhausted, next⟩ := inPlaceRounds.verdict_first before hd
  refine ⟨exhausted, ?_⟩
  have decided : inPlaceRounds.procedure.verdict 2 ⟨_, AuditControls.maxStore⟩ ≠ .undecided := by
    rw [next]
    exact inPlaceRounds.verdictOf_some_ne d
  exact (inPlaceRounds.procedure.exact_of_decided decided).mpr (solvable_of_kind two)

/-- **Where the 16 enters**: the tree's in-place solver is the family's solver at budget 16 inside a round, so its
decision, driven by the rank, is the procedure's attempt at budget 16. -/
theorem inPlace_is_attempt16 {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    Decided.ofRank AuditControls.inPlace problem = inPlaceRounds.attempt 16 ⟨Θ, problem⟩ :=
  rfl

/-- **What the tree decides with 16, the procedure decides by budget 16, the same way**: a yes is a yes, a no a no. -/
theorem inPlace_decided_by16 {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (found : (Decided.ofRank AuditControls.inPlace problem).isSome = true) :
    inPlaceRounds.procedure.verdict 16 ⟨Θ, problem⟩ ≠ .undecided ∧
      (inPlaceRounds.procedure.verdict 16 ⟨Θ, problem⟩ = .equal ↔ (frames setting.levels).Solvable problem) := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp found
  have decided : inPlaceRounds.procedure.verdict 16 ⟨Θ, problem⟩ ≠ .undecided := fun undecided => by
    have absent := (inPlaceRounds.verdict_undecided_iff.mp undecided) 16 le_rfl
    rw [← inPlace_is_attempt16, hd] at absent
    cases absent
  exact ⟨decided, inPlaceRounds.procedure.exact_of_decided decided⟩

/-- **Law 4 on a settled class, not vacuous**: the in-place family settles on the solving-in-place witness, so the
procedure answers it at some budget. This restates `blocked_decided`, which reads "from one joint budget on". -/
theorem blocked_answered :
    ∃ k, inPlaceRounds.procedure.verdict k ⟨_, ContextualDependentFragment.Controls.blockedStore⟩ ≠ .undecided :=
  rounds_answered _ ContextualDependentInPlace.Controls.blockedSettled _ (Or.inr rfl)

/-- **The cross store is exhausted at every budget inside a round.** -/
theorem cross_rounds_exhausted (k : Nat) : inPlaceRounds.procedure.verdict k ⟨ctxCross, crossStore⟩ = .undecided :=
  undecided_of_no_principal _ cross_identity (fun answer => cross_no_principal answer) k

/-- **The fixed store, unsolvable, is exhausted at the budgets `0 … 3` inside a round.** -/
theorem fixed_rounds_exhausted :
    inPlaceRounds.procedure.verdict 3 ⟨ctxMixed, fixedStore⟩ = .undecided ∧
      ¬ (frames setting.levels).Solvable fixedStore := by
  refine ⟨inPlaceRounds.undecided_of_none fun j le => ?_, fixed_unsolvable⟩
  have attempts :
      decidedKind (inPlaceRounds.attempt 0 ⟨ctxMixed, fixedStore⟩) = 0 ∧
        decidedKind (inPlaceRounds.attempt 1 ⟨ctxMixed, fixedStore⟩) = 0 ∧
        decidedKind (inPlaceRounds.attempt 2 ⟨ctxMixed, fixedStore⟩) = 0 ∧
        decidedKind (inPlaceRounds.attempt 3 ⟨ctxMixed, fixedStore⟩) = 0 := by
    decide +kernel
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
  · exact none_of_kind attempts.1
  · exact none_of_kind attempts.2.1
  · exact none_of_kind attempts.2.2.1
  · exact none_of_kind attempts.2.2.2

/-! ## The depth of phases -/

/-- Deciding in phases in the tower from the mixed solver, its depth as an outcome. -/
abbrev towerPhasesDepth : Decider (HasSolution (S := setting)) :=
  phasesDepth TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun problem => Decided.ofRun towerMixedSolver 8 problem) 6

/-- `F : U0 → U0`. -/
def famF : TypeOver (empty setting.R) := formIn (empty setting.R) (.pi (.head U0) (.head U0)) (by decide +kernel)
abbrev ctxF := extend (empty setting.R) famF
def arrowF : TypeOver ctxF := formIn ctxF (.pi (.head U0) (.head U0)) (by decide +kernel)

/-- `F ≐ λ x. x` at `U0 → U0`: not η-long on the left. -/
def idStore : EquationStore (TotalTerm ctxF) :=
  [(termIn ctxF arrowF (.var 0) (by decide +kernel), termIn ctxF arrowF (.lam (.var 0)) (by decide +kernel))]

/-- `λ x. F x ≐ λ x. x`: its η-long form. -/
def idLong : EquationStore (TotalTerm ctxF) :=
  [(termIn ctxF arrowF (.lam (.app (.var 1) (.var 0))) (by decide +kernel),
    termIn ctxF arrowF (.lam (.var 0)) (by decide +kernel))]

/-- **The base alone does not decide `F ≐ λ x. x`, and decides its η-long form.** -/
theorem id_base : decidedKind (Decided.ofRun towerMixedSolver 8 idStore) = 0 ∧
    decidedKind (Decided.ofRun towerMixedSolver 8 idLong) = 1 := by
  decide +kernel

/-- **Its first phase at `F` is empty**: its equation mentions `F`. -/
theorem id_first_phase_empty :
    (ContextualDependentInPlace.separation (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 6 famF idStore).val.1.isEmpty = true := by
  decide +kernel

theorem id_phases : (towerPhasesDepth.attempt 0 ⟨ctxF, idStore⟩).isSome = false ∧
    decidedKind (towerPhasesDepth.attempt 1 ⟨ctxF, idStore⟩) = 1 := by
  decide +kernel

/-- **Exhausted at depth `0`, solved at depth `1`**, through the empty first phase. -/
theorem id_exhausted_then_solved :
    towerPhasesDepth.procedure.verdict 0 ⟨ctxF, idStore⟩ = .undecided ∧
      towerPhasesDepth.procedure.verdict 1 ⟨ctxF, idStore⟩ = .equal := by
  obtain ⟨zero, one⟩ := id_phases
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (AuditControls.isSome_of_kind one)
  have before : ∀ j, j ≤ 0 → towerPhasesDepth.attempt j ⟨ctxF, idStore⟩ = none := by
    intro j le
    rw [Nat.le_zero.mp le]
    exact eq_none_of_isSome_false zero
  obtain ⟨exhausted, next⟩ := towerPhasesDepth.verdict_first before hd
  refine ⟨exhausted, ?_⟩
  have decided : towerPhasesDepth.procedure.verdict 1 ⟨ctxF, idStore⟩ ≠ .undecided := by
    rw [next]
    exact towerPhasesDepth.verdictOf_some_ne d
  exact (towerPhasesDepth.procedure.exact_of_decided decided).mpr (solvable_of_kind one)

/-- **The cross store is exhausted at every depth.** -/
theorem cross_phases_exhausted (k : Nat) : towerPhasesDepth.procedure.verdict k ⟨ctxCross, crossStore⟩ = .undecided :=
  undecided_of_no_principal _ cross_identity (fun answer => cross_no_principal answer) k

def tU1 : TypeOver (empty setting.R) := formIn (empty setting.R) (.head U1) (by decide +kernel)
def tU2 : TypeOver (empty setting.R) := formIn (empty setting.R) (.head U2) (by decide +kernel)

/-- `U0 : U1 ≐ U0 : U2`: the two sides at different universes, over the empty telescope. -/
def hetStore : EquationStore (TotalTerm (empty setting.R)) :=
  [(termIn (empty setting.R) tU1 (.head U0) (by decide +kernel),
    termIn (empty setting.R) tU2 (.head U0) (by decide +kernel))]

theorem het_kernel : decidedKind (Decided.ofRun towerMixedSolver 8 hetStore) = 0 ∧
    decidedKind (Decided.ofRank (ContextualDependentInPlace.Controls.inPlaceTower.solver 0) hetStore) = 2 ∧
    (towerOneWitness hetStore).isSome = false := by
  decide +kernel

/-- **It has no solution**: the in-place solver refutes it, with a certificate. -/
theorem het_unsolvable : ¬ (frames setting.levels).Solvable hetStore := unsolvable_of_kind het_kernel.2.1

/-- **Exhausted at every depth**: over the empty telescope every depth is the base, which leaves it undecided. -/
theorem het_phases_exhausted (k : Nat) : towerPhasesDepth.procedure.verdict k ⟨empty setting.R, hetStore⟩ = .undecided :=
  phases_empty_undecided TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun problem => Decided.ofRun towerMixedSolver 8 problem) 6
    (none_of_kind het_kernel.1) k

/-! ### Law 1 answers no, with a certificate -/

/-- **Inside one round, `U0 : U1 ≐ U0 : U2` is answered no at budget `0`.** -/
theorem het_rounds_no : inPlaceRounds.procedure.verdict 0 ⟨empty setting.R, hetStore⟩ = .different :=
  different_at_zero (by decide +kernel)

/-- **In phases, the clash store `U_a ≐ U0` is answered no at depth `0`.** -/
theorem clash_phases_no : towerPhasesDepth.procedure.verdict 0 ⟨empty setting.R, AuditControls.clashStore⟩ = .different :=
  different_at_zero (by decide +kernel)

/-! ### Where a canonical order does not remove the depth -/

/-- **The fixed store's first phase at `F` is empty.** -/
theorem fixed_first_phase_empty :
    (ContextualDependentInPlace.separation (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 6 mixedFamily fixedStore).val.1.isEmpty = true := by
  decide +kernel

/-- **The fixed store is exhausted at the depths `0 … 3`.** -/
theorem fixed_phases_exhausted :
    towerPhasesDepth.procedure.verdict 3 ⟨ctxMixed, fixedStore⟩ = .undecided := by
  refine towerPhasesDepth.undecided_of_none fun j le => ?_
  have depths : decidedKind (towerPhasesDepth.attempt 0 ⟨ctxMixed, fixedStore⟩) = 0 ∧
      decidedKind (towerPhasesDepth.attempt 1 ⟨ctxMixed, fixedStore⟩) = 0 ∧
      decidedKind (towerPhasesDepth.attempt 2 ⟨ctxMixed, fixedStore⟩) = 0 ∧
      decidedKind (towerPhasesDepth.attempt 3 ⟨ctxMixed, fixedStore⟩) = 0 := by
    decide +kernel
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
  · exact none_of_kind depths.1
  · exact none_of_kind depths.2.1
  · exact none_of_kind depths.2.2.1
  · exact none_of_kind depths.2.2.2

/-! ## The reader's depth -/

/-- The reader of the tower over the one solver's fragment, its depth as an outcome. -/
abbrev towerReaderDepth : Decider (fun q : Stored setting => Through (InOne ExecutableTowerChoices.choices) q.2) :=
  readerDepth TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (InOne ExecutableTowerChoices.choices) towerOneWitness 6

/-- **Exhausted at depth `0`, read at depth `1`.** -/
theorem dd_exhausted_then_read :
    towerReaderDepth.procedure.verdict 0 ⟨_, TreeFibre.Controls.ddStore⟩ = .undecided ∧
      towerReaderDepth.procedure.verdict 1 ⟨_, TreeFibre.Controls.ddStore⟩ = .equal := by
  have reads : (towerReaderDepth.attempt 0 ⟨_, TreeFibre.Controls.ddStore⟩).isSome = false ∧
      (towerReaderDepth.attempt 1 ⟨_, TreeFibre.Controls.ddStore⟩).isSome = true := by
    decide +kernel
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp reads.2
  have before : ∀ j, j ≤ 0 → towerReaderDepth.attempt j ⟨_, TreeFibre.Controls.ddStore⟩ = none := by
    intro j le
    rw [Nat.le_zero.mp le]
    exact eq_none_of_isSome_false reads.1
  obtain ⟨exhausted, next⟩ := towerReaderDepth.verdict_first before hd
  exact ⟨exhausted, next⟩

/-- **The cross store is never read.** -/
theorem cross_reader_exhausted (k : Nat) :
    towerReaderDepth.procedure.verdict k ⟨ctxCross, crossStore⟩ = .undecided :=
  reader_undecided_of_not_settles TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (InOne ExecutableTowerChoices.choices) towerOneWitness 6
    (fun inside => TreeFibre.Controls.towerOne_settles inside) cross_not_settles k

/-- **`U0 : U1 ≐ U0 : U2` is never read.** -/
theorem het_reader_exhausted (k : Nat) :
    towerReaderDepth.procedure.verdict k ⟨empty setting.R, hetStore⟩ = .undecided :=
  read_empty_undecided TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (InOne ExecutableTowerChoices.choices) towerOneWitness 6
    (eq_none_of_isSome_false het_kernel.2.2) k

/-- **Yet it lies in the class the reader reads**: it is equivalent to the clash store, which the fragment's reader
reads, both having no solution. -/
theorem het_through : Through (InOne ExecutableTowerChoices.choices) hetStore := by
  have clashRead : (towerOneWitness AuditControls.clashStore).isSome = true := by decide +kernel
  refine .equivalent (other := AuditControls.clashStore) (fun Δ σ => ?_) (.base ((towerOneWitness _).get clashRead).down)
  constructor
  · intro models
    exact absurd ⟨Δ, σ, models⟩ het_unsolvable
  · intro models
    exact absurd ⟨Δ, σ, models⟩ AuditControls.clash_unsolvable

/-- **Law 4 for the reader needs its hypothesis**: a store of the class it reads, never answered. -/
theorem reader_not_answered_on_its_class :
    ¬ towerReaderDepth.procedure.AnsweredOn fun q => Through (InOne ExecutableTowerChoices.choices) q.2 := by
  intro answered
  obtain ⟨k, decided⟩ := answered ⟨empty setting.R, hetStore⟩ het_through
  exact decided (het_reader_exhausted k)

end TreeFibre.Budgets.TowerControls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

section Audit
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Budgets.TowerControls
#print axioms cross_not_settles
#print axioms inPlace_is_attempt16
#print axioms inPlace_decided_by16
#print axioms blocked_answered
#print axioms max_exhausted_then_solved
#print axioms cross_rounds_exhausted
#print axioms fixed_rounds_exhausted
#print axioms id_base
#print axioms id_first_phase_empty
#print axioms id_exhausted_then_solved
#print axioms cross_phases_exhausted
#print axioms het_unsolvable
#print axioms het_phases_exhausted
#print axioms different_at_zero
#print axioms het_rounds_no
#print axioms clash_phases_no
#print axioms fixed_first_phase_empty
#print axioms fixed_phases_exhausted
#print axioms dd_exhausted_then_read
#print axioms cross_reader_exhausted
#print axioms het_reader_exhausted
#print axioms het_through
#print axioms reader_not_answered_on_its_class
end Audit
