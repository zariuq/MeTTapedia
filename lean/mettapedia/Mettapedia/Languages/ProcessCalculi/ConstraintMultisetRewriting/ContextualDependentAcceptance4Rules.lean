import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureIntersect

/-!
# Acceptance for the dead-binder family, reduced to firing and the open rule obligations

`ContextualDependentCumulativeClosure.Obligations` lists one closure obligation per rule of the cumulative round. On
the permuted Miller class of a strongly normalizing package without root computation, six are discharged:
preparation (`prepare_keeps`), the two occurs checks (they only refute), twin collapse, the conversion scan, and R110's
intersection (`intersect_keeps`). The rest are `OpenObligations`, one statement per rule; `obligations_of_open`
assembles the full list.

**The reduction** (`dead_decided_of_rules`, and `tower_dead_decided_of_rules` for the tower): if the dead-binder round
is eventually not stuck on nonempty `PermutedMiller` stores (firing) and the open rule obligations hold at every
budget, the dead-binder family decides every store of the dynamic pattern fragment, with a principal answer or a
certified refutation, constant at every larger budget.
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

/-- **The open rule obligations** of the cumulative round on the permuted Miller class, at one budget: R99's
decomposition round and the rotation, the identity and Π decompositions, R86's in-place rule, the rigid formers,
η-expansion, the spine and deep decompositions, R107's conversion pattern rule, η-for-Σ expansion, the decompositions
under abstractions, of projections, of eliminations and at a flexible base, R107's inversion in place, flex–flex across
a declaration, prune-and-solve, and R110's cumulative rule. -/
structure OpenObligations (fuel : Nat) : Prop where
  decompose : LayerKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
    ContextualDependentRigidDecomposition.decomposeRound rigid facts complete roots heads algebra declared choices
      reducer root normalizes certifyNormal headTypingUnique fuel problem
  rotate : RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
    ContextualDependentPermutation.rotateRule rigid complete facts roots heads algebra declared choices reducer root
      normalizes certifyNormal fuel problem
  identity : RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
    idDecomposeSearch facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
      fuel problem
  pi : RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
    piDecomposeSearch facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
      fuel problem
  inPlace : RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
    ContextualDependentInPlace.inPlaceRule facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique fuel problem
  formers : RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
    ContextualDependentRigidFormers.formerSearch facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique fuel problem
  eta : RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
    ContextualDependentEtaExpansion.etaSearch facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique fuel problem
  two : RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
    ContextualDependentRigidFormers.twoSearch facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique fuel problem
  deep : RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
    ContextualDependentRigidFormers.deepSearch facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique fuel problem
  pattern : RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
    ContextualDependentRecognitionConversion.patternRuleConv facts roots heads algebra declared choices reducer rigid
      complete root normalizes certifyNormal fuel problem
  expanded : UpdateKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
    ContextualDependentCensusPairEta.preparedExpanded facts roots heads algebra declared choices reducer root
      rootComplete fuel problem
  any : ∀ ⦃Θ : Context S.R⦄ (problem : EquationStore (TotalTerm Θ)), PermutedMiller S.levels problem →
    DecomposedKeeps (fun problem => PermutedMiller S.levels problem) facts roots heads algebra rigid complete
      (ContextualDependentSpinesMany.decomposeAny facts roots heads algebra rigid complete declared choices reducer
        fuel problem)
  projections : ∀ ⦃Θ : Context S.R⦄ (problem : EquationStore (TotalTerm Θ)), PermutedMiller S.levels problem →
    DecomposedKeeps (fun problem => PermutedMiller S.levels problem) facts roots heads algebra rigid complete
      (ContextualDependentConstantHeadsProjections.decomposeProjections facts roots heads algebra rigid complete
        declared choices reducer fuel problem)
  elims : ∀ ⦃Θ : Context S.R⦄ (problem : EquationStore (TotalTerm Θ)), PermutedMiller S.levels problem →
    DecomposedKeeps (fun problem => PermutedMiller S.levels problem) facts roots heads algebra rigid complete
      (ContextualDependentEliminations.decomposeElims facts roots heads algebra rigid complete declared choices reducer
        fuel problem)
  flex : ∀ ⦃Θ : Context S.R⦄ (problem : EquationStore (TotalTerm Θ)), PermutedMiller S.levels problem →
    DecomposedKeeps (fun problem => PermutedMiller S.levels problem) facts roots heads algebra rigid complete
      (ContextualDependentSpineEta.decomposeFlex facts roots heads algebra rigid complete declared choices reducer
        fuel problem)
  placed : RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
    ContextualDependentPatternFiring.placedRule facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal fuel problem
  reorder : RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
    ContextualDependentFlexReorder.reorderRule facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique fuel problem
  pruneSolve : RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
    ContextualDependentPruneSolve.pruneSolveRule facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique fuel problem
  cumulative : RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
    ContextualDependentCumulative.cumulativeRule facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal fuel problem

/-- **The full list of rule obligations from the open ones**, on a strongly normalizing package. -/
theorem obligations_of_open (sn : StronglyNormalizing S.R) (fuel : Nat)
    (remaining : OpenObligations facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel) :
    Obligations (fun problem => PermutedMiller S.levels problem) facts roots heads algebra rigid complete declared
      choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel where
  lower :=
    { prepare := prepare_keeps root rootComplete facts roots heads rigid sn fuel
      decompose := remaining.decompose
      rotate := remaining.rotate
      identity := remaining.identity
      pi := remaining.pi
      inPlace := remaining.inPlace
      formers := remaining.formers
      eta := remaining.eta
      occurs := occursSearch_keeps facts roots heads algebra rigid complete _
      two := remaining.two
      deep := remaining.deep
      pattern := remaining.pattern
      occursFull := occursFullSearch_keeps facts roots heads algebra rigid complete _ }
  conversion := conversion_keeps facts roots heads algebra reducer fuel
  collapse := collapse_keeps facts roots heads algebra reducer fuel
  expanded := remaining.expanded
  any := remaining.any
  projections := remaining.projections
  elims := remaining.elims
  flex := remaining.flex
  placed := remaining.placed
  reorder := remaining.reorder
  intersect := fun _ problem permuted moved fired =>
    intersect_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes headTypingUnique
      sn fuel problem permuted moved fired
  pruneSolve := remaining.pruneSolve
  cumulative := remaining.cumulative

variable (strengthening : EqualStrengthening S.R)
  (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n), Keeps (reducer fuel term) (reducer (fuel + 1) term))
  (sn : StronglyNormalizing S.R)

include stable sn in
/-- **Acceptance for the dead-binder family, reduced to firing and the open rule obligations**, on a strongly
normalizing package. -/
theorem dead_decided_of_rules
    (firing : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck)
    (remaining : ∀ fuel, OpenObligations facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel)
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
    (fun fuel => cumulativeRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel
      (obligations_of_open facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete sn fuel (remaining fuel)))
    inside

end General

/-! ## The tower -/

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls

/-- The open rule obligations of the tower controls at one budget. -/
abbrev TowerOpen (fuel : Nat) : Prop :=
  OpenObligations (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) fuel

/-- **Acceptance for the tower's dead-binder family, reduced to firing and the open rule obligations**, on every store
of the dynamic pattern fragment. -/
theorem tower_dead_decided_of_rules
    (firing : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → deadTower.round larger problem ≠ .stuck)
    (remaining : ∀ fuel, TowerOpen fuel)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (deadTower.solver larger) problem larger = run (deadTower.solver budget) problem budget ∧
      ((∃ state finished, run (deadTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (deadTower.solver larger) problem larger = .refuted absent)) :=
  dead_decided_of_rules (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening
    ContextualDependentDecisiveFragment.Controls.stable tower_stronglyNormalizing firing remaining inside

end ContextualDependentAcceptance4
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
