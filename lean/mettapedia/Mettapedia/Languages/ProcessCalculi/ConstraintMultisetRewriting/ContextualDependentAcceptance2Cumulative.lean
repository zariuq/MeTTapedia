import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance2Readings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeRound

/-!
# The last family with the cumulative round

The cumulative family extends the flexible-base family by the cumulative round, so it is now the last family:

* every store that R99's arguments family decides at a joint budget, it decides at that budget with the same outcome
  (`cumulative_decided_of_arguments`);
* every row that a lower round reads, its round reads (`cumulativeRound_not_stuck_of_flex`, with
  `flexRound_not_stuck_of_endpoints` and the readings of `ContextualDependentAcceptance2Readings`), and the cumulative
  rule reads the cumulative argument (`cumulativeRound_not_stuck_of_rule`);
* acceptance on `InFragmentStore` reduces to settling on the corrected class `StratifiedShort`
  (`decided_of_settling_short_cumulative`). The hypothesis is firing and closure; it is not proved here.
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
open ContextualDependentInPlaceClosure ContextualDependentSpineEta ContextualDependentCumulative

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

/-- **Every store that R99's arguments family decides at a joint budget, the cumulative family decides at that
budget**, with the same outcome at every larger joint budget. -/
theorem cumulative_decided_of_arguments {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {budget : Nat}
    (decided : ∀ larger, budget ≤ larger →
      (run ((ContextualDependentIdEndpointsArguments.argumentsFamily facts roots heads algebra rigid complete declared
        choices reducer root normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem
          larger).Decided) :
    ∀ larger, budget ≤ larger →
      run ((cumulativeFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((ContextualDependentIdEndpointsArguments.argumentsFamily facts roots heads algebra rigid complete declared
          choices reducer root normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger := by
  have flexSame := last_decided_of_arguments facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete decided
  have flexDecided : ∀ larger, budget ≤ larger →
      (run ((flexFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver larger) problem larger).Decided := fun larger enough => by
    rw [flexSame larger enough]
    exact decided larger enough
  intro larger enough
  rw [cumulative_decided_of_flex facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete flexDecided larger enough, flexSame larger enough]

/-- **The cumulative round moves wherever the flexible-base round moves.** -/
theorem cumulativeRound_not_stuck_of_flex (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck :=
  ne_of_eq_of_ne (cumulativeRound_eq_of_flex facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete fuel moving) moving

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- **Acceptance reduced to settling on the corrected class, for the cumulative family.** If, at each nonempty store
of `StratifiedShort` and from some budget on, the cumulative round is not stuck and keeps every residual store in
`StratifiedShort`, then the cumulative family decides every store of the dynamic pattern fragment at one joint budget,
with a principal answer or a certified refutation, and the same outcome at every larger joint budget. -/
theorem decided_of_settling_short_cumulative
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, StratifiedShort S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            StratifiedShort S.levels update.remaining)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((cumulativeFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((cumulativeFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver budget) problem budget ∧
      ((∃ state finished, run ((cumulativeFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
              .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent, run ((cumulativeFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger = .refuted absent)) :=
  (cumulativeSettledOfConst facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete stable (fun problem => StratifiedShort S.levels problem)
    eventual).decided (stratifiedShort_of_fragment inside)

end ContextualDependentAcceptance2
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
