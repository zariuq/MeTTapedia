import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance2
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusReadings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance

/-!
# The rows that the last family reads

Each round of the chain acts only where the round below it is stuck, so **a round that moves keeps moving in every later
round** (`flexRound_not_stuck_of_elims`, `flexRound_not_stuck_of_arguments`, `flexRound_not_stuck_of_endpoints`). Every
row reading proved for a lower round is therefore a reading of the last round, with the same hypothesis:

| Row | Reader | Theorem |
|---|---|---|
| rigid clash under abstractions (R99) | head clash search | `last_reads_clash` |
| occurrence along formers and endpoints (R99) | occurs check | `last_reads_inside` |
| decomposition (R99) | `decomposeAny` | `last_reads_decomposed` |
| projection spines (R99) | `decomposeProjections` | `last_reads_projections` |
| spine arguments (R99) | `argumentsRefuted` | `last_reads_arguments` |
| rigid local outside the pattern (R107) | `rigidRule` | `last_reads_rigid` |
| inversion, newest (R107) | `patternRuleConv` | `last_reads_pattern` |
| inversion in place (R107) | `placedRule` | `last_reads_placed` |
| flex–flex across a declaration | `reorderRule` | `last_reads_reorder` |
| intersection | `intersectRule` | `last_reads_intersection` |
| pruning under binders | `pruneSolveRule` | `last_reads_pruning` |
| spine at a flexible base | `flexRest` | `flexRound_not_stuck_of_rest` |

This is the reading half of a coverage theorem. The other half, that every equation of a census row satisfies the
hypothesis of its reader on the prepared store, is not proved here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentAcceptance2

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRigidFormers ContextualDependentRank ContextualDependentSpinesMany
open ContextualDependentTwinsUnder ContextualDependentConstantHeads ContextualDependentCensusPairEta
open ContextualDependentIdEndpoints ContextualDependentFragmentDecisive ContextualDependentEtaExpansion
open ContextualDependentIdEndpointsArguments ContextualDependentCensusReadings ContextualDependentAcceptance
open ContextualDependentPatternFiring ContextualDependentEliminations ContextualDependentFlexReorder
open ContextualDependentIntersection ContextualDependentPruneSolve ContextualDependentSpineEta
open ContextualDependentConstantHeadsProjections

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

/-! ## Moving rounds keep moving -/

/-- **The last round moves wherever the reorder round moves.** -/
theorem flexRound_not_stuck_of_reorder (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : reorderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  have intersect := ne_of_eq_of_ne (intersectRound_eq_of_reorder facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel moving) moving
  have prune := ne_of_eq_of_ne (pruneSolveRound_eq_of_intersect facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel intersect) intersect
  exact ne_of_eq_of_ne (flexRound_eq_of_pruneSolve facts roots heads algebra rigid complete declared choices reducer
    root normalizes certifyNormal headTypingUnique rootComplete fuel prune) prune

/-- **The last round moves wherever the intersection round moves.** -/
theorem flexRound_not_stuck_of_intersect (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : intersectRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  have prune := ne_of_eq_of_ne (pruneSolveRound_eq_of_intersect facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel moving) moving
  exact ne_of_eq_of_ne (flexRound_eq_of_pruneSolve facts roots heads algebra rigid complete declared choices reducer
    root normalizes certifyNormal headTypingUnique rootComplete fuel prune) prune

/-- **The last round moves wherever R107's eliminations round moves.** -/
theorem flexRound_not_stuck_of_elims (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : elimsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck :=
  flexRound_not_stuck_of_reorder facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel
    (ne_of_eq_of_ne (reorderRound_eq_of_elims facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel moving) moving)

/-- **The last round moves wherever R107's placed round moves.** -/
theorem flexRound_not_stuck_of_placed (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : placedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck :=
  flexRound_not_stuck_of_elims facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel
    (elimsRound_not_stuck_of_placed facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel moving)

/-- **The last round moves wherever R107's firing round moves.** -/
theorem flexRound_not_stuck_of_firing (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : firingRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck :=
  flexRound_not_stuck_of_placed facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel
    (placedRound_not_stuck_of_firing facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel moving)

/-- **The last round moves wherever R99's arguments round moves.** -/
theorem flexRound_not_stuck_of_arguments (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : argumentsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck :=
  flexRound_not_stuck_of_firing facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel
    (firingRound_not_stuck_of_arguments facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel moving)

/-- **The last round moves wherever R99's endpoints round moves.** -/
theorem flexRound_not_stuck_of_endpoints (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : endpointsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck :=
  flexRound_not_stuck_of_arguments facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel
    (argumentsRound_not_stuck_of_endpoints facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel moving)

/-! ## The rows read by the last round -/

/-- **Rigid clashes** (R99) are read by the last round. -/
theorem last_reads_clash (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (clash : ∃ equation ∈ (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining,
      equation.2.1.code = equation.1.1.code ∧
        HeadClash S.R 0 equation.1.1.code equation.1.2.code equation.2.2.code) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck :=
  flexRound_not_stuck_of_endpoints facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel
    (endpointsRound_not_stuck_of_clash facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel clash)

/-- **Occurrences along formers and identity endpoints** (R99) are read by the last round. -/
theorem last_reads_inside (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (occurrence : ∃ equation ∈ (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining,
      equation.2.1.code = equation.1.1.code ∧
        UnderInside S.R equation.1.1.code equation.1.2.code equation.2.2.code) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck :=
  flexRound_not_stuck_of_endpoints facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel
    (endpointsRound_not_stuck_of_inside facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel occurrence)

/-- **Decompositions** (R99) are read by the last round. -/
theorem last_reads_decomposed (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (found : (decomposeAny facts roots heads algebra rigid complete declared choices reducer fuel
      (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining).isSome) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck :=
  flexRound_not_stuck_of_endpoints facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel
    (endpointsRound_not_stuck_of_decomposed facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel found)

/-- **Projection spines** (R99) are read by the last round. -/
theorem last_reads_projections (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (found : (decomposeProjections facts roots heads algebra rigid complete declared choices reducer fuel
      (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining).isSome) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck :=
  flexRound_not_stuck_of_arguments facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel
    (argumentsRound_not_stuck_of_projections facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel found)

/-- **Spine arguments** (R99) are read by the last round. -/
theorem last_reads_arguments (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (argumentsRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem).isSome) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck :=
  flexRound_not_stuck_of_arguments facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel
    (argumentsRound_not_stuck_of_arguments facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel read)

/-- **A rigid local outside the pattern** (R107) is read by the last round. -/
theorem last_reads_rigid (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (rigidRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      fuel problem).isSome) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck :=
  flexRound_not_stuck_of_firing facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel
    (firingRound_not_stuck_of_rigid facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel read)

/-- **Inversion at the newest declaration** (R107) is read by the last round. -/
theorem last_reads_pattern (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (ContextualDependentRecognitionConversion.patternRuleConv facts roots heads algebra declared choices reducer
      rigid complete root normalizes certifyNormal fuel problem).isSome) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck :=
  flexRound_not_stuck_of_firing facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel
    (firingRound_not_stuck_of_pattern facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel read)

/-- **Inversion in place** (R107) is read by the last round. -/
theorem last_reads_placed (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (placedRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      fuel problem).isSome) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck :=
  flexRound_not_stuck_of_placed facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel
    (placedRound_not_stuck_of_placed facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel read)

/-- **Flex–flex across a declaration** is read by the last round. -/
theorem last_reads_reorder (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (reorderRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique fuel problem).isSome) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck :=
  flexRound_not_stuck_of_reorder facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel
    (reorderRound_not_stuck_of_reorder facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel read)

/-- **Intersection** is read by the last round. -/
theorem last_reads_intersection (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (intersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem).isSome) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck :=
  flexRound_not_stuck_of_intersect facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel
    (intersectRound_not_stuck_of_rule facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel read)

/-- **Pruning under binders** is read by the last round. -/
theorem last_reads_pruning (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (pruneSolveRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel problem).isSome) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  have prune := pruneSolveRound_not_stuck_of_rule facts roots heads algebra rigid complete declared choices reducer
    root normalizes certifyNormal headTypingUnique rootComplete fuel read
  exact ne_of_eq_of_ne (flexRound_eq_of_pruneSolve facts roots heads algebra rigid complete declared choices reducer
    root normalizes certifyNormal headTypingUnique rootComplete fuel prune) prune

end ContextualDependentAcceptance2
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
