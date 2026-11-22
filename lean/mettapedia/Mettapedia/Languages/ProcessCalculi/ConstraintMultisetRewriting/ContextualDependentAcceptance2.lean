import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSpineEtaRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentInPlaceClosure

/-!
# The last family: what it keeps, and a conditional decision

The chain of rounds is R99's arguments round, R107's firing, placed and eliminations rounds, then the reorder round,
the intersection round, the prune-and-solve round and the flexible-base round. Each new round acts only where the round
below it is stuck, so **every store that an earlier family decides at a joint budget, the last family decides at that
budget with the same outcome** (`pruneSolve_decided_of_elims`, `last_decided_of_elims`,
`last_decided_of_arguments`).

**A conditional decision.** `Settled.decided` (R86) on every store of `InFragmentStore` follows, through the last
family's settling criterion, from one hypothesis on the corrected class `StratifiedShort` (`decided_of_settling_short`):
at each nonempty store of the class, from some budget on, the round is not stuck and every progress stays in the class.
That hypothesis is firing and closure. At the tower it fails: the fragment holds `crossStore`, solvable and without
principal answer (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). For every store, runs are
exact; on `crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). The class is
`StratifiedShort` and not `Stratified`, because an in-place answer leaves `Stratified`
(`ContextualDependentInPlaceClosure.witness_first_round`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentAcceptance2

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentDynamicFragment
open ContextualDependentEliminations ContextualDependentFlexReorder ContextualDependentIntersection
open ContextualDependentPruneSolve ContextualDependentInPlaceClosure ContextualDependentSpineEta

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

/-! ## Conservativity of the last family -/

/-- **Every store that R107's eliminations family decides at a joint budget, the last family decides at that budget**,
with the same outcome at every larger joint budget. -/
theorem pruneSolve_decided_of_elims {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {budget : Nat}
    (decided : ∀ larger, budget ≤ larger →
      (run ((elimsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver larger) problem larger).Decided) :
    ∀ larger, budget ≤ larger →
      run ((pruneSolveFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((elimsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger := by
  have reorderSame := reorder_decided_of_elims facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete decided
  have reorderDecided : ∀ larger, budget ≤ larger →
      (run ((reorderFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver larger) problem larger).Decided := fun larger enough => by
    rw [reorderSame larger enough]
    exact decided larger enough
  have intersectSame := intersect_decided_of_reorder facts roots heads algebra rigid complete declared choices reducer
    root normalizes certifyNormal headTypingUnique rootComplete reorderDecided
  have intersectDecided : ∀ larger, budget ≤ larger →
      (run ((intersectFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver larger) problem larger).Decided := fun larger enough => by
    rw [intersectSame larger enough]
    exact reorderDecided larger enough
  have pruneSame := pruneSolve_decided_of_intersect facts roots heads algebra rigid complete declared choices reducer
    root normalizes certifyNormal headTypingUnique rootComplete intersectDecided
  intro larger enough
  rw [pruneSame larger enough, intersectSame larger enough, reorderSame larger enough]

/-- **Every store that R107's eliminations family decides at a joint budget, the flexible-base family decides at that
budget**, with the same outcome at every larger joint budget. -/
theorem last_decided_of_elims {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {budget : Nat}
    (decided : ∀ larger, budget ≤ larger →
      (run ((elimsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver larger) problem larger).Decided) :
    ∀ larger, budget ≤ larger →
      run ((flexFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((elimsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger := by
  have pruneSame := pruneSolve_decided_of_elims facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete decided
  have pruneDecided : ∀ larger, budget ≤ larger →
      (run ((pruneSolveFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver larger) problem larger).Decided := fun larger enough => by
    rw [pruneSame larger enough]
    exact decided larger enough
  intro larger enough
  rw [flex_decided_of_pruneSolve facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete pruneDecided larger enough, pruneSame larger enough]

/-- **Every store that R99's arguments family decides at a joint budget, the last family decides at that budget**,
with the same outcome at every larger joint budget. -/
theorem last_decided_of_arguments {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {budget : Nat}
    (decided : ∀ larger, budget ≤ larger →
      (run ((ContextualDependentIdEndpointsArguments.argumentsFamily facts roots heads algebra rigid complete declared
        choices reducer root normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem
          larger).Decided) :
    ∀ larger, budget ≤ larger →
      run ((flexFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((ContextualDependentIdEndpointsArguments.argumentsFamily facts roots heads algebra rigid complete declared
          choices reducer root normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger := by
  have placedSame := ContextualDependentPatternFiring.placed_decided_of_arguments facts roots heads algebra rigid
    complete declared choices reducer root normalizes certifyNormal headTypingUnique rootComplete decided
  have placedDecided : ∀ larger, budget ≤ larger →
      (run ((ContextualDependentPatternFiring.placedFamily facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger).Decided :=
    fun larger enough => by
      rw [placedSame larger enough]
      exact decided larger enough
  have elimsSame := elims_decided_of_placed facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete placedDecided
  have elimsDecided : ∀ larger, budget ≤ larger →
      (run ((elimsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver larger) problem larger).Decided := fun larger enough => by
    rw [elimsSame larger enough]
    exact placedDecided larger enough
  intro larger enough
  rw [last_decided_of_elims facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete elimsDecided larger enough, elimsSame larger enough,
    placedSame larger enough]

/-! ## A conditional decision from settling on the corrected class -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- **Conditional decision from settling on the corrected class.** If, at each nonempty store of `StratifiedShort` and
from some budget on, the last family's round is not stuck and keeps every residual store in `StratifiedShort`, then
the last family decides every store of the dynamic pattern fragment at one joint budget, with a principal answer or a
certified refutation, and the same outcome at every larger joint budget (R86's `Settled.decided`). At the tower's
setting the conclusion fails on `crossStore` (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`),
so there the hypothesis fails. For every store, runs are exact; on `crossStore` they stop postponed
(`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem decided_of_settling_short
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, StratifiedShort S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            StratifiedShort S.levels update.remaining)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((flexFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((flexFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver budget) problem budget ∧
      ((∃ state finished, run ((flexFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
              .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent, run ((flexFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger = .refuted absent)) :=
  (flexSettledOfConst facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete stable (fun problem => StratifiedShort S.levels problem)
    eventual).decided (stratifiedShort_of_fragment inside)

end ContextualDependentAcceptance2
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
