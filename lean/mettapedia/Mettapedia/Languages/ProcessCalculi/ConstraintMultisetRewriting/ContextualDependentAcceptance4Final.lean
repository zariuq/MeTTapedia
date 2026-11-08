import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureCumulative
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureCarryPlaced

/-!
# Closure of the cumulative round, and acceptance for the dead-binder family from firing

All twenty-five rule obligations of the cumulative round (`ContextualDependentCumulativeClosure.Obligations`) are
discharged on the permuted Miller class of a strongly normalizing package without root computation whose reducer
returns reducts:

| Obligation | Theorem |
|---|---|
| preparation | `prepare_keeps` |
| the occurs checks | `occursSearch_keeps`, `occursFullSearch_keeps` (they only refute) |
| twin collapse | `collapse_keeps` |
| the conversion scan | `conversion_keeps` |
| R110's intersection | `intersect_keeps` |
| R107's conversion pattern rule | `patternRuleConv_keeps` |
| R99's rotation | `rotateRule_keeps` (through R75's pattern rule, `patternRule_keeps`) |
| R110's prune-and-solve | `pruneSolveRule_keeps` |
| R110's cumulative rule | `cumulativeRule_keeps` |
| R98's identity decomposition | `idDecomposeSearch_keeps` |
| R98's binder decomposition | `piDecomposeSearch_keeps` |
| R112's η for Σ | `expanded_keeps` |
| R99's committed decomposition | `decomposeAny_keeps_permuted` (at a universe, under abstractions, between spines) |
| R99's projection spines | `decomposeProjections_keeps` |
| R99's elimination spines, at a rigid base and at a base shape | `decomposeElims_keeps`, `decomposeFlex_keeps` |
| R99's decomposition round | `decomposeRound_keeps`, through R99's local decomposition (`decomposeSearch_keeps`), R76's first rule (`firstRule_stable`) and R75's dispatcher (`dispatch_keeps`) |
| R86's in-place rule | `inPlace_stable` (shaped updates survive lifting past later declarations) |
| R94's rigid formers, η-expansion, the spine rule, deep decomposition | `formerSearch_keeps_of_inPlace`, `etaSearch_keeps_of_inPlace`, `twoSearch_keeps_of_inPlace`, `deepSearch_keeps_of_inPlace` |
| R107's inversion in place | `placedRule_keeps` |
| flex–flex across a declaration | `reorderRule_keeps` |

So the cumulative round keeps the permuted class and `PermutedNormal` at every budget (`cumulativeRound_closure`,
`cumulativeRound_keepsPermutedNormal`). **Acceptance from firing** (`tower_dead_decided_of_firing`): if the tower's
dead-binder round is eventually not stuck on nonempty `PermutedMiller` stores, the dead-binder family decides every
store of the dynamic pattern fragment, with a principal answer or a certified refutation, constant at every larger
budget.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentAcceptance4

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentRank
open ContextualDependentMillerClosure ContextualDependentCumulativeClosure ContextualDependentOpenedNormal
open ContextualDependentConversionBudget ContextualDependentDynamicFragment ContextualDependentAcceptance3
open ContextualDependentIntersectionGeneral

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

/-- **Every open rule obligation holds** on a strongly normalizing package whose reducer returns reducts. -/
theorem open_obligations (sn : StronglyNormalizing S.R)
    (directed : ∀ (fuel : Nat) {n : Nat} (term : Tm Head n) (result : ExecutableReduction.Result S.R term),
      reducer fuel term = some result → ContextualDependentExecutableJoin.Star (R := S.R) term result.val)
    (fuel : Nat) :
    OpenObligations facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel where
  decompose := decomposeRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique sn fuel
    (decomposeSearch_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal sn fuel)
    (worklistRound_keeps facts roots heads algebra rigid complete declared choices reducer fuel
      (dispatch_keeps facts roots heads algebra declared choices reducer directed rigid sn fuel))
  rotate := rotateRule_keeps facts roots heads algebra declared choices reducer rigid complete root normalizes
    certifyNormal sn fuel
  identity := idDecomposeSearch_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal sn fuel
  pi := piDecomposeSearch_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal sn fuel
  inPlace := inPlace_keeps_of_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique fuel
    (inPlace_stable facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique sn fuel)
  formers := formerSearch_keeps_of_inPlace facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique sn fuel
    (inPlace_stable facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique sn fuel)
  eta := etaSearch_keeps_of_inPlace facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique sn fuel
    (inPlace_stable facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique sn fuel)
  two := twoSearch_keeps_of_inPlace facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique sn fuel
    (inPlace_stable facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique sn fuel)
  deep := deepSearch_keeps_of_inPlace facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique sn fuel
    (inPlace_stable facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique sn fuel)
  pattern := patternRuleConv_keeps facts roots heads algebra declared choices reducer rigid complete root normalizes
    certifyNormal sn fuel
  expanded := expanded_keeps facts roots heads algebra rigid declared choices reducer root rootComplete sn fuel
  any := fun _ problem permuted => decomposeAny_keeps_permuted facts roots heads algebra rigid complete declared
    choices reducer sn fuel problem permuted
  projections := fun _ problem permuted => decomposeProjections_keeps facts roots heads algebra rigid complete declared
    choices reducer sn fuel problem permuted
  elims := fun _ problem permuted => decomposeElims_keeps facts roots heads algebra rigid complete declared choices
    reducer sn fuel problem permuted
  flex := fun _ problem permuted => decomposeFlex_keeps facts roots heads algebra rigid complete declared choices
    reducer sn fuel problem permuted
  placed := placedRule_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal sn fuel
  reorder := reorderRule_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique sn fuel
  pruneSolve := pruneSolveRule_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique sn fuel
  cumulative := cumulativeRule_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal sn fuel

/-- **Closure of the cumulative round**: on a strongly normalizing package whose reducer returns reducts, the
cumulative round keeps the permuted Miller class at every budget. -/
theorem cumulativeRound_closure (sn : StronglyNormalizing S.R)
    (directed : ∀ (fuel : Nat) {n : Nat} (term : Tm Head n) (result : ExecutableReduction.Result S.R term),
      reducer fuel term = some result → ContextualDependentExecutableJoin.Star (R := S.R) term result.val)
    (fuel : Nat) :
    RoundKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      ContextualDependentCumulative.cumulativeRound facts roots heads algebra rigid complete declared choices reducer
        root normalizes certifyNormal headTypingUnique rootComplete fuel problem :=
  cumulativeRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
    headTypingUnique rootComplete fuel
    (obligations_of_open facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete sn fuel
      (open_obligations facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete sn directed fuel))

/-- **The cumulative round keeps `PermutedNormal`** at every budget, on the same packages. -/
theorem cumulativeRound_keepsPermutedNormal (sn : StronglyNormalizing S.R)
    (directed : ∀ (fuel : Nat) {n : Nat} (term : Tm Head n) (result : ExecutableReduction.Result S.R term),
      reducer fuel term = some result → ContextualDependentExecutableJoin.Star (R := S.R) term result.val)
    (fuel : Nat) :
    KeepsPermutedNormal facts roots heads algebra rigid complete fun problem =>
      ContextualDependentCumulative.cumulativeRound facts roots heads algebra rigid complete declared choices reducer
        root normalizes certifyNormal headTypingUnique rootComplete fuel problem :=
  (keepsPermutedNormal_iff facts roots heads algebra rigid complete sn _).mpr
    (cumulativeRound_closure facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete sn directed fuel)

/-- **Acceptance for the dead-binder family from firing**, on a strongly normalizing package whose reducer returns
reducts, is monotone in its budget and strengthens typed equality: the family decides every store of the dynamic
pattern fragment as soon as its round is eventually not stuck on nonempty stores of the permuted class. -/
theorem dead_decided_of_firing (strengthening : EqualStrengthening S.R)
    (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n), Keeps (reducer fuel term) (reducer (fuel + 1) term))
    (sn : StronglyNormalizing S.R)
    (directed : ∀ (fuel : Nat) {n : Nat} (term : Tm Head n) (result : ExecutableReduction.Result S.R term),
      reducer fuel term = some result → ContextualDependentExecutableJoin.Star (R := S.R) term result.val)
    (firing : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck)
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
  dead_decided_of_sn facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
    headTypingUnique rootComplete strengthening stable sn firing
    (cumulativeRound_closure facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete sn directed)
    inside

end General

/-! ## The tower -/

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls

/-- **The tower's reducer returns reducts**: it is the executable normalizer. -/
theorem tower_reducer_directed (fuel : Nat) {n : Nat} (term : Tm _ n)
    (result : ExecutableReduction.Result setting.R term)
    (computed : ContextualDependentInversion.Controls.reducer fuel term = some result) :
    ContextualDependentExecutableJoin.Star (R := setting.R) term result.val :=
  normalize_star setting.R (fun _ => none) fuel computed

/-- **Acceptance for the tower's dead-binder family from firing**, on every store of the dynamic pattern fragment: no
rule obligation remains. -/
theorem tower_dead_decided_of_firing
    (firing : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → deadTower.round larger problem ≠ .stuck)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (deadTower.solver larger) problem larger = run (deadTower.solver budget) problem budget ∧
      ((∃ state finished, run (deadTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (deadTower.solver larger) problem larger = .refuted absent)) :=
  tower_dead_decided_of_rules firing
    (fun fuel => open_obligations (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none)
      ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
      ContextualDependentGeneralPattern.DispatchControls.certifyNormal
      ContextualDependentNormalCheckingTower.head_typing_unique
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_stronglyNormalizing
      tower_reducer_directed fuel)
    inside

end ContextualDependentAcceptance4
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
