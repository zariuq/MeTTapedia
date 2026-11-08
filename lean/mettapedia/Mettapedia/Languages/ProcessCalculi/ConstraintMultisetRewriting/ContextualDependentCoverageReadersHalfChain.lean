import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCoverageReadersHalfCensus

/-!
# The readers' half of coverage: the rows of the upper chain

R110's twelve rows (`Reads`) read the flexible round. The rounds between the committed decomposition and the endpoint
round read more: the conversion scan of the committed decomposition round (`anyRest`), the lower chain itself where
its progress lowers the arity or refutes (`anyRound`), twin retyping (`twinRest`), η for Σ (`pairsRest`), and the
head and endpoint clash refutations (`headsRefuted`, `endpointsRefuted`). Each moves the endpoint round, hence the
flexible round and the dead-binder round (`deadRound_not_stuck_of_chainReads`).

`FullReads` is `AllReads` or one of these rows, and **firing follows from eventual full reading**
(`firing_of_fullReads`, `tower_dead_decided_of_fullReads`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCoverageReadersHalf

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRigidFormers ContextualDependentRank ContextualDependentSpinesMany
open ContextualDependentTwinsUnder ContextualDependentConstantHeads ContextualDependentCensusPairEta
open ContextualDependentIdEndpoints ContextualDependentCensusReadings ContextualDependentAcceptance2
open ContextualDependentIntersectionGeneral ContextualDependentMillerClosure ContextualDependentConversionBudget

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

/-- **The committed decomposition round moves where the conversion scan drops an equation.** -/
theorem anyRound_not_stuck_of_scan (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (shorter : (Conversion.scan facts roots heads algebra reducer fuel problem).length < problem.length) :
    anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  have rest : anyRest facts roots heads algebra rigid complete declared choices reducer root rootComplete fuel problem ≠
      .stuck := by
    unfold anyRest
    rw [dif_pos shorter]
    exact fun impossible => by cases impossible
  unfold anyRound
  split
  · exact fun impossible => by cases impossible
  · split
    · exact fun impossible => by cases impossible
    · split
      · exact fun impossible => by cases impossible
      · exact rest
    · exact rest

/-- **The twin round moves where twin retyping does.** -/
theorem twinRound_not_stuck_of_rest (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : twinRest facts roots heads algebra rigid complete reducer declared choices root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck) :
    twinRound facts roots heads algebra rigid complete reducer declared choices root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold twinRound
  cases anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | stuck => exact moving
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-- **The pairs round moves where η for Σ does.** -/
theorem pairsRound_not_stuck_of_rest (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : pairsRest facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck) :
    pairsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold pairsRound
  cases headsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | stuck => exact moving
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-- **The rows of the upper chain, at one budget.** -/
def ChainReads (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  (Conversion.scan facts roots heads algebra reducer fuel problem).length < problem.length ∨
  anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck ∨
  twinRest facts roots heads algebra rigid complete reducer declared choices root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck ∨
  pairsRest facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck ∨
  (headsRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem).isSome ∨
  (endpointsRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem).isSome

/-- **The endpoint round moves wherever a row of the upper chain reads.** -/
theorem endpointsRound_not_stuck_of_chainReads (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (reads : ChainReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem) :
    endpointsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  have ofPairs := endpointsRound_not_stuck_of_pairs facts roots heads algebra rigid complete declared choices reducer
    root normalizes certifyNormal headTypingUnique rootComplete fuel (problem := problem)
  have ofHeads := pairsRound_not_stuck_of_heads facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete fuel (problem := problem)
  have ofTwin := headsRound_not_stuck_of_twin facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete fuel (problem := problem)
  have ofAny := twinRound_not_stuck_of_any facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete fuel (problem := problem)
  rcases reads with read | read | read | read | read | read
  · exact ofPairs (ofHeads (ofTwin (ofAny (anyRound_not_stuck_of_scan facts roots heads algebra rigid complete
      declared choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel read))))
  · exact ofPairs (ofHeads (ofTwin (ofAny read)))
  · exact ofPairs (ofHeads (ofTwin (twinRound_not_stuck_of_rest facts roots heads algebra rigid complete declared
      choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel read)))
  · exact ofPairs (pairsRound_not_stuck_of_rest facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel read)
  · exact ofPairs (ofHeads (headsRound_not_stuck_of_clash facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete fuel read))
  · exact endpointsRound_not_stuck_of_endpoints facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel read

/-- **The dead-binder round moves wherever a row of the upper chain reads.** -/
theorem deadRound_not_stuck_of_chainReads (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (reads : ChainReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem) :
    deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck :=
  deadRound_not_stuck_of_flex facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening fuel
    (flexRound_not_stuck_of_endpoints facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel
      (endpointsRound_not_stuck_of_chainReads facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete fuel reads))

/-- **Every reader named so far**: the flexible round's rows, the outer rounds' rules, or the upper chain's rows. -/
def FullReads (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  AllReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ∨
    ChainReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem

/-- **Firing from eventual full reading.** -/
theorem firing_of_fullReads
    (reads : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        FullReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
          headTypingUnique rootComplete strengthening larger problem)
    {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} (permuted : PermutedMiller S.levels problem)
    (nonempty : problem ≠ []) :
    ∃ bound, ∀ larger, bound ≤ larger →
      deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening larger problem ≠ .stuck := by
  obtain ⟨bound, eventually⟩ := reads permuted nonempty
  refine ⟨bound, fun larger enough => ?_⟩
  rcases eventually larger enough with all | chain
  · rcases all with flexible | outer
    · exact deadRound_not_stuck_of_reads facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete strengthening larger flexible
    · exact deadRound_not_stuck_of_outerReads facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete strengthening larger outer
  · exact deadRound_not_stuck_of_chainReads facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening larger chain

end General

/-! ## The tower -/

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls
open ContextualDependentAcceptance4 ContextualDependentDynamicFragment ContextualDependentAcceptance3

/-- Every named reader of the tower's dead-binder family at one budget. -/
abbrev TowerFullReads (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  FullReads (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening fuel problem

/-- **Acceptance for the tower's dead-binder family, reduced to eventual reading by a named reader**, on every store
of the dynamic pattern fragment. -/
theorem tower_dead_decided_of_fullReads
    (reads : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → TowerFullReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (deadTower.solver larger) problem larger = run (deadTower.solver budget) problem budget ∧
      ((∃ state finished, run (deadTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (deadTower.solver larger) problem larger = .refuted absent)) :=
  tower_dead_decided_of_firing
    (fun permuted nonempty => firing_of_fullReads (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none)
      ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
      ContextualDependentGeneralPattern.DispatchControls.certifyNormal
      ContextualDependentNormalCheckingTower.head_typing_unique
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening reads permuted
      nonempty)
    inside

end ContextualDependentCoverageReadersHalf
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
