import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentOpenedNormal
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralDeadBinderControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Elaboration

/-!
# A conditional decision for the dead-binder family without the normal-reduct hypothesis

On a strongly normalizing package without root computation every store has normal reducts of its opened sides
(`ContextualDependentOpenedNormal.openedNormal_of_sn`), so R119's reduction `dead_decided_of_cumulative` loses its
hypothesis `OpenedNormal` on the store, and its two hypotheses are read on the permuted Miller class alone
(`dead_decided_of_sn`):

* **(firing)** on every nonempty `PermutedMiller` store the dead-binder round is eventually not stuck;
* **(closure)** at every budget the cumulative round keeps `PermutedMiller`.

The tower is strongly normalizing (`tower_stronglyNormalizing`, from `TowerInterpretation.tower_sn`), so for the
tower's dead-binder family the reduction asks nothing of the store beyond the dynamic pattern fragment
(`tower_dead_decided`); it still asks firing and closure. At the tower firing and closure do not both hold: the
conclusion would decide `crossStore`, in the fragment, solvable and without principal answer
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). Closure is proved
(`cumulativeRound_closure`), so firing fails. For every store, runs are exact; on `crossStore` they stop postponed
(`UnificationWithLevels.DependentFibre.cross_postponed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentAcceptance4

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentIntersection ContextualDependentIntersectionGeneral
open ContextualDependentDynamicFragment ContextualDependentShortClosure ContextualDependentHereditary
open ContextualDependentMillerClosure ContextualDependentCumulative ExecutableReduction ContextualDependentExecutableJoin
open ContextualDependentConversionBudget ContextualDependentAcceptance3 ContextualDependentOpenedNormal

section General

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)
  (strengthening : EqualStrengthening S.R)
  (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n), Keeps (reducer fuel term) (reducer (fuel + 1) term))
  (sn : StronglyNormalizing S.R)

include stable sn in
/-- **Conditional decision for the dead-binder family on a strongly normalizing package, from firing and closure on
the permuted Miller class.** No hypothesis on the store beyond the dynamic pattern fragment. At the tower's setting
the conclusion fails on `crossStore` (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`), so
there firing and closure do not both hold. For every store, runs are exact; on `crossStore` they stop postponed
(`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem dead_decided_of_sn
    (firing : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck)
    (closure : ∀ fuel, RoundKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((deadFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
        run ((deadFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver budget) problem budget ∧
      ((∃ state finished, run ((deadFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent, run ((deadFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .refuted absent)) :=
  dead_decided_of_cumulative facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening stable
    (fun held nonempty => firing held.1 nonempty)
    (fun fuel => (keepsPermutedNormal_iff facts roots heads algebra rigid complete sn _).mpr (closure fuel))
    inside (openedNormal_of_sn (computation_empty rigid) sn problem)

end General

/-! ## The tower -/

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls

/-- **The tower is strongly normalizing**: every typed term of a formed context. -/
theorem tower_stronglyNormalizing : StronglyNormalizing setting.R :=
  fun formed typed => TowerInterpretation.tower_sn formed typed

/-- **Every tower store has normal reducts of its opened sides.** -/
theorem tower_openedNormal {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : OpenedNormal problem :=
  openedNormal_of_sn (S := setting) (computation_empty ContextualDependentPiSpine.Controls.rigid)
    tower_stronglyNormalizing problem

/-- The cumulative round of the tower controls, as a fuel-indexed family. -/
noncomputable def cumulativeTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  cumulativeFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- **Conditional decision for the tower's dead-binder family, from firing and closure on the permuted Miller
class**, on every store of the dynamic pattern fragment. At the tower the hypotheses do not both hold: the conclusion
would decide `crossStore`, solvable and without principal answer
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`,
`ContextualDependentSweep.Witnesses.acceptance_conclusion_false`). For every store, runs are exact; on `crossStore`
they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_dead_decided
    (firing : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → deadTower.round larger problem ≠ .stuck)
    (closure : ∀ fuel, RoundKeeps (fun problem => PermutedMiller setting.levels problem) fun problem =>
      cumulativeTower.round fuel problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (deadTower.solver larger) problem larger = run (deadTower.solver budget) problem budget ∧
      ((∃ state finished, run (deadTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (deadTower.solver larger) problem larger = .refuted absent)) :=
  dead_decided_of_sn (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening
    ContextualDependentDecisiveFragment.Controls.stable tower_stronglyNormalizing firing closure inside

end ContextualDependentAcceptance4
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
