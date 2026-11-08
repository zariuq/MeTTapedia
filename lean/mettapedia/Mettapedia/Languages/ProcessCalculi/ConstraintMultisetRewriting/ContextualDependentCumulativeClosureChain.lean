import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosure

/-!
# Closure of the cumulative round, layer by layer: the upper layers

The upper layers rank by weight. Each is read through its view, as the lower ones
(`ContextualDependentCumulativeClosure`): R99's ranked abstraction round (the conversion scan, then one decomposition of
the prepared store), the twin round (the same round on the store with homogeneous twins), the head clashes, η-for-Σ
(the heads round on the prepared store with expanded pairs), the identity endpoints, the projection spines, the spine
arguments, R107's firing, inversion in place and eliminations, flex–flex across a declaration, intersection,
prune-and-solve, the spine at a flexible base, and R110's cumulative rule.

**The reduction** (`cumulativeRound_keeps`): for any class of stores, the cumulative round keeps the class at a budget
as soon as every rule below does (`Obligations`). Refutations need nothing. So closure of the cumulative round on
`PermutedMiller` is exactly the list of rule obligations in `Obligations`, each a statement about one rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCumulativeClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentRank

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable {holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop}

/-! ## Views of the upper layers -/

section Views

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

variable (holds) in
/-- **A decomposition keeps the class**: the decomposed store, when there is one, lies in it. -/
def DecomposedKeeps {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (found : Option (Decomposed facts roots heads algebra rigid complete problem)) : Prop :=
  ∀ decomposed, found = some decomposed → holds decomposed.val

theorem ViewKeeps.decomposed {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {prepared : Update S.levels problem} {found : Option (Decomposed facts roots heads algebra rigid complete
      prepared.remaining)} (keeps : DecomposedKeeps holds facts roots heads algebra rigid complete found) :
    ViewKeeps holds (ContextualDependentConstantHeadsProjections.projectionsViewOf facts roots heads algebra rigid
      complete prepared found) := by
  intro update offered
  cases found with
  | none => cases offered
  | some decomposed =>
      cases offered
      exact keeps decomposed rfl

theorem ViewKeeps.preparedView {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {prepared : Update S.levels problem} {scanned : EquationStore (TotalTerm Θ)} {converted : Update S.levels problem}
    {found : Option (Decomposed facts roots heads algebra rigid complete prepared.remaining)}
    (keepsConverted : holds converted.remaining)
    (keepsFound : DecomposedKeeps holds facts roots heads algebra rigid complete found) :
    ViewKeeps holds (ContextualDependentSpinesMany.preparedView facts roots heads algebra rigid complete problem prepared
      scanned converted found) := by
  intro update offered
  unfold ContextualDependentSpinesMany.preparedView at offered
  split at offered
  · cases offered
    exact keepsConverted
  · cases found with
    | none => cases offered
    | some decomposed =>
        cases offered
        exact keepsFound decomposed rfl

end Views

theorem ViewKeeps.ranked {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {base rest : Option (Option (Update S.levels problem))} (keepsBase : ViewKeeps holds base)
    (keepsRest : ViewKeeps holds rest) : ViewKeeps holds (ContextualDependentRank.rankedView base rest) := by
  intro update offered
  unfold ContextualDependentRank.rankedView at offered
  cases base with
  | none => exact keepsRest update offered
  | some inner =>
      cases inner with
      | none => cases offered
      | some moved =>
          dsimp only at offered
          split at offered
          · have same : moved = update := Option.some.inj (Option.some.inj offered)
            subst same
            exact keepsBase moved rfl
          · exact keepsRest update offered

theorem ViewKeeps.lifted {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {collapsed : Update S.levels problem}
    {view : Option (Option (Update S.levels collapsed.remaining))} (keeps : ViewKeeps holds view) :
    ViewKeeps holds (ContextualDependentTwinsUnder.liftView collapsed view) := by
  intro update offered
  cases view with
  | none => cases offered
  | some inner =>
      cases inner with
      | none => cases offered
      | some moved =>
          cases offered
          exact keeps moved rfl

theorem ViewKeeps.progress {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
    (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
    (complete : AlgorithmicComplete S.R S.roles)
    {found : Option (ContextualDependentIntersection.Progress facts roots heads algebra rigid complete problem)}
    (keeps : ∀ moved, found = some moved → holds moved.val.remaining) :
    ViewKeeps holds (ContextualDependentIntersection.progressView facts roots heads algebra rigid complete found) := by
  intro update offered
  cases found with
  | none => cases offered
  | some moved =>
      cases offered
      exact keeps moved rfl

/-! ## The upper layers -/

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

variable (holds) in
/-- **The obligations of the cumulative round**, rule by rule, at one budget: the lower layers' obligations, then the
conversion scan, twin collapse, η-for-Σ expansion of the prepared store, R99's decompositions under abstractions, the
projection, elimination and flexible-base decompositions of the prepared store with homogeneous twins, R107's
inversion in place, flex–flex across a declaration, intersection, prune-and-solve, and R110's cumulative rule. -/
structure Obligations (fuel : Nat) : Prop where
  lower : LowerObligations (holds := holds) facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete fuel
  conversion : UpdateKeeps holds fun problem => ContextualDependentUpdate.conversion facts roots heads algebra reducer
    fuel problem
  collapse : UpdateKeeps holds fun problem => ContextualDependentTwinsUnder.collapse facts roots heads algebra reducer
    fuel problem
  expanded : UpdateKeeps holds fun problem => ContextualDependentCensusPairEta.preparedExpanded facts roots heads
    algebra declared choices reducer root rootComplete fuel problem
  any : ∀ ⦃Θ : Context S.R⦄ (problem : EquationStore (TotalTerm Θ)), holds problem →
    DecomposedKeeps holds facts roots heads algebra rigid complete
      (ContextualDependentSpinesMany.decomposeAny facts roots heads algebra rigid complete declared choices reducer
        fuel problem)
  projections : ∀ ⦃Θ : Context S.R⦄ (problem : EquationStore (TotalTerm Θ)), holds problem →
    DecomposedKeeps holds facts roots heads algebra rigid complete
      (ContextualDependentConstantHeadsProjections.decomposeProjections facts roots heads algebra rigid complete
        declared choices reducer fuel problem)
  elims : ∀ ⦃Θ : Context S.R⦄ (problem : EquationStore (TotalTerm Θ)), holds problem →
    DecomposedKeeps holds facts roots heads algebra rigid complete
      (ContextualDependentEliminations.decomposeElims facts roots heads algebra rigid complete declared choices reducer
        fuel problem)
  flex : ∀ ⦃Θ : Context S.R⦄ (problem : EquationStore (TotalTerm Θ)), holds problem →
    DecomposedKeeps holds facts roots heads algebra rigid complete
      (ContextualDependentSpineEta.decomposeFlex facts roots heads algebra rigid complete declared choices reducer
        fuel problem)
  placed : RuleKeeps holds fun problem =>
    ContextualDependentPatternFiring.placedRule facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal fuel problem
  reorder : RuleKeeps holds fun problem =>
    ContextualDependentFlexReorder.reorderRule facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique fuel problem
  intersect : ∀ ⦃Θ : Context S.R⦄ (problem : EquationStore (TotalTerm Θ)), holds problem →
    ∀ moved, ContextualDependentIntersection.intersectRule facts roots heads algebra rigid complete declared choices
      reducer root normalizes headTypingUnique fuel problem = some moved → holds moved.val.remaining
  pruneSolve : RuleKeeps holds fun problem =>
    ContextualDependentPruneSolve.pruneSolveRule facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique fuel problem
  cumulative : RuleKeeps holds fun problem =>
    ContextualDependentCumulative.cumulativeRule facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal fuel problem

/-- **R99's ranked abstraction round keeps the class.** -/
theorem anyRound_keeps (fuel : Nat)
    (obligations : Obligations holds facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel) :
    LayerKeeps holds fun problem =>
      ContextualDependentSpinesMany.anyRound facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  intro Θ problem held
  rw [ContextualDependentSpinesMany.anyRound_view]
  dsimp only
  split
  · exact ViewKeeps.refuted true
  · refine ViewKeeps.ranked (occursFullRound_keeps facts roots heads algebra rigid complete declared choices reducer
      root normalizes certifyNormal headTypingUnique rootComplete fuel obligations.lower problem held) ?_
    rw [ContextualDependentSpinesMany.anyRest_view]
    exact ViewKeeps.preparedView facts roots heads algebra rigid complete (obligations.conversion problem held)
      (obligations.any _ (obligations.lower.prepare problem held))

/-- **The twin round keeps the class.** -/
theorem twinRound_keeps (fuel : Nat)
    (obligations : Obligations holds facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel) :
    LayerKeeps holds fun problem =>
      ContextualDependentTwinsUnder.twinRound facts roots heads algebra rigid complete reducer declared choices root
        normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  intro Θ problem held
  have any := anyRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel obligations
  rw [ContextualDependentTwinsUnder.twinRound_view]
  refine (any problem held).or ?_
  unfold ContextualDependentTwinsUnder.twinRest
  rw [ContextualDependentTwinsUnder.liftCollapsed_view]
  exact ViewKeeps.lifted (any _ (obligations.collapse problem held))

/-- **The heads round keeps the class.** -/
theorem headsRound_keeps (fuel : Nat)
    (obligations : Obligations holds facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel) :
    LayerKeeps holds fun problem =>
      ContextualDependentConstantHeads.headsRound facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  intro Θ problem held
  rw [ContextualDependentConstantHeads.headsRound_view]
  exact (twinRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel obligations problem held).or (ViewKeeps.refuted _)

/-- **The pairs round keeps the class.** -/
theorem pairsRound_keeps (fuel : Nat)
    (obligations : Obligations holds facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel) :
    LayerKeeps holds fun problem =>
      ContextualDependentCensusPairEta.pairsRound facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  intro Θ problem held
  have headsKeep := headsRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel obligations
  rw [ContextualDependentCensusPairEta.pairsRound_view]
  refine (headsKeep problem held).or ?_
  unfold ContextualDependentCensusPairEta.pairsRest
  rw [ContextualDependentTwinsUnder.liftCollapsed_view]
  exact ViewKeeps.lifted (headsKeep _ (obligations.expanded problem held))

/-- **The endpoints round keeps the class.** -/
theorem endpointsRound_keeps (fuel : Nat)
    (obligations : Obligations holds facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel) :
    LayerKeeps holds fun problem =>
      ContextualDependentIdEndpoints.endpointsRound facts roots heads algebra rigid complete declared choices reducer
        root normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  intro Θ problem held
  rw [ContextualDependentIdEndpoints.endpointsRound_view]
  exact (pairsRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel obligations problem held).or (ViewKeeps.refuted _)

/-- The prepared store with homogeneous twins keeps the class. -/
theorem preparedTwins_keeps (fuel : Nat)
    (obligations : Obligations holds facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel) :
    UpdateKeeps holds fun problem =>
      ContextualDependentConstantHeads.preparedTwins facts roots heads algebra reducer root rootComplete fuel problem :=
  fun _ problem held => obligations.collapse _ (obligations.lower.prepare problem held)

/-- **The projections round keeps the class.** -/
theorem projectionsRound_keeps (fuel : Nat)
    (obligations : Obligations holds facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel) :
    LayerKeeps holds fun problem =>
      ContextualDependentConstantHeadsProjections.projectionsRound facts roots heads algebra rigid complete declared
        choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  intro Θ problem held
  rw [ContextualDependentConstantHeadsProjections.projectionsRound_view]
  refine (endpointsRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel obligations problem held).or ?_
  rw [ContextualDependentConstantHeadsProjections.projectionsRest_view]
  exact ViewKeeps.decomposed facts roots heads algebra rigid complete (obligations.projections _
    (preparedTwins_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel obligations problem held))

/-- **The arguments round keeps the class.** -/
theorem argumentsRound_keeps (fuel : Nat)
    (obligations : Obligations holds facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel) :
    LayerKeeps holds fun problem =>
      ContextualDependentIdEndpointsArguments.argumentsRound facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  intro Θ problem held
  rw [ContextualDependentIdEndpointsArguments.argumentsRound_view]
  exact (projectionsRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel obligations problem held).or (ViewKeeps.refuted _)

/-- **R107's firing round keeps the class.** -/
theorem firingRound_keeps (fuel : Nat)
    (obligations : Obligations holds facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel) :
    LayerKeeps holds fun problem =>
      ContextualDependentPatternFiring.firingRound facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  intro Θ problem held
  rw [ContextualDependentPatternFiring.firingRound_view]
  exact (argumentsRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel obligations problem held).or
    ((ViewKeeps.foundFiring (obligations.lower.pattern problem held)).or (ViewKeeps.refuted _))

/-- **R107's placed round keeps the class.** -/
theorem placedRound_keeps (fuel : Nat)
    (obligations : Obligations holds facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel) :
    LayerKeeps holds fun problem =>
      ContextualDependentPatternFiring.placedRound facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  intro Θ problem held
  rw [ContextualDependentPatternFiring.placedRound_view]
  exact (firingRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel obligations problem held).or
    (ViewKeeps.foundFiring (obligations.placed problem held))

/-- **R107's eliminations round keeps the class.** -/
theorem elimsRound_keeps (fuel : Nat)
    (obligations : Obligations holds facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel) :
    LayerKeeps holds fun problem =>
      ContextualDependentEliminations.elimsRound facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  intro Θ problem held
  rw [ContextualDependentEliminations.elimsRound_view]
  refine (placedRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel obligations problem held).or ?_
  rw [ContextualDependentEliminations.elimsRest_view]
  exact ViewKeeps.decomposed facts roots heads algebra rigid complete (obligations.elims _
    (preparedTwins_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel obligations problem held))

/-- **The reorder round keeps the class.** -/
theorem reorderRound_keeps (fuel : Nat)
    (obligations : Obligations holds facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel) :
    LayerKeeps holds fun problem =>
      ContextualDependentFlexReorder.reorderRound facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  intro Θ problem held
  rw [ContextualDependentFlexReorder.reorderRound_view]
  exact (elimsRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel obligations problem held).or
    (ViewKeeps.foundFiring (obligations.reorder problem held))

/-- **The intersection round keeps the class.** -/
theorem intersectRound_keeps (fuel : Nat)
    (obligations : Obligations holds facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel) :
    LayerKeeps holds fun problem =>
      ContextualDependentIntersection.intersectRound facts roots heads algebra rigid complete declared choices reducer
        root normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  intro Θ problem held
  rw [ContextualDependentIntersection.intersectRound_view]
  exact (reorderRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel obligations problem held).or
    (ViewKeeps.progress facts roots heads algebra rigid complete (obligations.intersect problem held))

/-- **The prune-and-solve round keeps the class.** -/
theorem pruneSolveRound_keeps (fuel : Nat)
    (obligations : Obligations holds facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel) :
    LayerKeeps holds fun problem =>
      ContextualDependentPruneSolve.pruneSolveRound facts roots heads algebra rigid complete declared choices reducer
        root normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  intro Θ problem held
  rw [ContextualDependentPruneSolve.pruneSolveRound_view]
  exact (intersectRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel obligations problem held).or
    (ViewKeeps.foundFiring (obligations.pruneSolve problem held))

/-- **The flexible-base round keeps the class.** -/
theorem flexRound_keeps (fuel : Nat)
    (obligations : Obligations holds facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel) :
    LayerKeeps holds fun problem =>
      ContextualDependentSpineEta.flexRound facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  intro Θ problem held
  rw [ContextualDependentSpineEta.flexRound_view]
  refine (pruneSolveRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel obligations problem held).or ?_
  rw [ContextualDependentSpineEta.flexRest_view]
  exact ViewKeeps.decomposed facts roots heads algebra rigid complete (obligations.flex _
    (preparedTwins_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel obligations problem held))

/-- **The cumulative round keeps the class** at a budget wherever every rule below it does. -/
theorem cumulativeRound_layerKeeps (fuel : Nat)
    (obligations : Obligations holds facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel) :
    LayerKeeps holds fun problem =>
      ContextualDependentCumulative.cumulativeRound facts roots heads algebra rigid complete declared choices reducer
        root normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  intro Θ problem held
  rw [ContextualDependentCumulative.cumulativeRound_view]
  exact (flexRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel obligations problem held).or
    (ViewKeeps.foundFiring (obligations.cumulative problem held))

/-- **Closure of the cumulative round, reduced to its rules**: wherever every rule obligation holds at a budget, every
move of the cumulative round at that budget keeps the class. -/
theorem cumulativeRound_keeps (fuel : Nat)
    (obligations : Obligations holds facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel) :
    ContextualDependentOpenedNormal.RoundKeeps holds fun problem =>
      ContextualDependentCumulative.cumulativeRound facts roots heads algebra rigid complete declared choices reducer
        root normalizes certifyNormal headTypingUnique rootComplete fuel problem :=
  roundKeeps_of_layer (cumulativeRound_layerKeeps facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete fuel obligations)

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
