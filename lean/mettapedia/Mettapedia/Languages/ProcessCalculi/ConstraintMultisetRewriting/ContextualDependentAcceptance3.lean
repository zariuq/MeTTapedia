import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentMillerClosureRotation

/-!
# Acceptance for the last family, reduced to the cumulative round

The last family is the in-place family: the cumulative round, then general intersection at the newest metavariable,
after rotation, and in place (`ContextualDependentIntersectionGeneral.inPlaceRound`). Its three new rules drop the first
equation under a pattern answer (`HeadDrop`), so they keep the class

  `MillerNormal` = `StratifiedMiller` and every opened side has a β-normal reduct (`OpenedNormal`):

the stratified Miller class by R116's answer-then-drop closure, the normal reducts by R116's hereditary substitution
(`openedNormal_applyStore`). So the whole last round keeps the class wherever the cumulative round does
(`inPlaceRound_keeps`).

**The reduction** (`inPlace_decided_of_cumulative`): if, on `MillerNormal` stores, the last round is eventually not
stuck (firing) and the cumulative round keeps the class (closure of the R86–R110 rules), then the last family decides
every store of the dynamic pattern fragment whose opened sides have β-normal reducts, with a principal answer or a
certified refutation, at every large joint budget.

The normal reducts are a property of the rule package: they exist for every typed term of a strongly normalizing
package, such as the predicative tower (`tower_sn`), and the closure lemmas need them; the dynamic pattern fragment does
not state them.

The closure hypothesis fails in the tower: R86's in-place step reorders a `MillerNormal` store out of the class
(`ContextualDependentMillerClosure.ReorderControls.cumulativeRound_not_keeps`). The corrected reduction, on the permuted
class and for the anywhere family, is `anywhere_decided_of_cumulative` (`…Acceptance3Anywhere`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentAcceptance3

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentIntersection ContextualDependentIntersectionGeneral
open ContextualDependentDynamicFragment ContextualDependentShortClosure ContextualDependentHereditary
open ContextualDependentMillerClosure ContextualDependentCumulative ExecutableReduction ContextualDependentExecutableJoin
open ContextualDependentConversionBudget

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **The class of the reduction**: the stratified Miller class, with β-normal reducts of every opened side. -/
def MillerNormal {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  StratifiedMiller S.levels problem ∧ OpenedNormal problem

/-- **Normal reducts survive a pattern answer**, for equations with Miller sides. -/
theorem openedNormal_applyStore (rigid : ∀ name, S.roles name = .rigid) {Θ Δ : Context S.R} (σ : Δ ⟶ Θ)
    (answer : PatternAnswer S.R (bodyFlexible (o := Θ.arity) 0) (bodyFlexible (o := Δ.arity) 0) σ.substitution)
    {problem : EquationStore (TotalTerm Θ)} (millerSides : ∀ equation ∈ problem, FragmentSidesMiller equation)
    (opened : OpenedNormal problem) : OpenedNormal ((frames S.levels).applyStore σ problem) := by
  intro later member
  obtain ⟨equation, inside, rfl⟩ := List.mem_map.mp member
  have sides := millerSides equation inside
  obtain ⟨k, deeper⟩ := Nat.exists_eq_add_of_le (lamDepth_le_subst σ.substitution equation.1.2.code)
  change (∃ opened, Star (R := S.R) (openCode (lamDepth (subst σ.substitution equation.1.2.code))
        (subst σ.substitution equation.1.2.code)) opened ∧ Normal S.R opened) ∧
      (∃ opened, Star (R := S.R) (openCode (lamDepth (subst σ.substitution equation.1.2.code))
        (subst σ.substitution equation.2.2.code)) opened ∧ Normal S.R opened)
  rw [deeper]
  obtain ⟨left, toLeft, normalLeft, _⟩ := miller_deeper (computation_empty rigid) k
    (answered_side_miller (computation_empty rigid) answer _ sides.1 (opened equation inside).1)
  obtain ⟨right, toRight, normalRight, _⟩ := miller_deeper (computation_empty rigid) k
    (answered_side_miller (computation_empty rigid) answer _ sides.2 (opened equation inside).2)
  exact ⟨⟨left, toLeft, normalLeft⟩, ⟨right, toRight, normalRight⟩⟩

/-- **A drop under a pattern answer keeps the class.** -/
theorem millerNormal_of_headDrop (rigid : ∀ name, S.roles name = .rigid) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} {update : Update S.levels problem} (held : MillerNormal problem)
    (drops : HeadDrop problem update) : MillerNormal update.remaining := by
  refine ⟨stratifiedMiller_of_headDrop rigid held.1 held.2 drops, ?_⟩
  obtain ⟨first, rest, σ, rfl, _, remaining, _, ⟨answer⟩⟩ := drops
  rw [remaining]
  exact openedNormal_applyStore rigid σ answer
    (fun equation member => StratifiedMiller.sides_of_mem held.1 (List.mem_cons_of_mem _ member))
    fun equation member => held.2 equation (List.mem_cons_of_mem _ member)

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

include rigid in
theorem inPlaceIntersectSearch_headDrop (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    ∀ (depths : List Nat) {found : SitedProgress facts roots heads algebra rigid complete problem},
      inPlaceIntersectSearch facts roots heads algebra rigid complete declared choices reducer root normalizes
        headTypingUnique fuel problem depths = some found → HeadDrop problem found.val
  | [], _, fired => by cases fired
  | depth :: rest, found, fired => by
      simp only [inPlaceIntersectSearch] at fired
      split at fired
      · rename_i progress computed
        cases fired
        exact inPlaceIntersectAt_headDrop facts roots heads algebra rigid complete declared choices reducer root
          normalizes headTypingUnique fuel depth problem computed
      · exact inPlaceIntersectSearch_headDrop fuel problem rest fired

/-- **A round keeps the class**: every progress of a `MillerNormal` store is `MillerNormal`. -/
def KeepsMillerNormal
    (round : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
      Round S.levels (weightRank facts roots heads algebra rigid complete) problem) : Prop :=
  ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (update : Update S.levels problem)
    (smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
      (weightRank facts roots heads algebra rigid complete problem)),
    MillerNormal problem → round problem = .progress update smaller → MillerNormal update.remaining

include rigid in
/-- **The general round keeps the class wherever the cumulative round does.** -/
theorem generalRound_keeps (fuel : Nat)
    (base : KeepsMillerNormal facts roots heads algebra rigid complete fun problem =>
      cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem) :
    KeepsMillerNormal facts roots heads algebra rigid complete fun problem =>
      generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  intro Θ problem update smaller held fired
  dsimp only at fired
  unfold generalRound at fired
  cases computed : cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | progress first firstSmaller =>
      rw [computed] at fired
      cases fired
      exact base problem _ _ held computed
  | refuted absent =>
      rw [computed] at fired
      cases fired
  | stuck =>
      rw [computed] at fired
      dsimp only at fired
      split at fired
      · rename_i found rule
        cases fired
        exact millerNormal_of_headDrop rigid held (generalIntersectRule_headDrop facts roots heads algebra rigid complete
          declared choices reducer root normalizes headTypingUnique fuel problem rule)
      · cases fired

include rigid in
/-- **The older round keeps the class wherever the cumulative round does.** -/
theorem olderRound_keeps (fuel : Nat)
    (base : KeepsMillerNormal facts roots heads algebra rigid complete fun problem =>
      cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem) :
    KeepsMillerNormal facts roots heads algebra rigid complete fun problem =>
      olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  intro Θ problem update smaller held fired
  dsimp only at fired
  unfold olderRound at fired
  cases computed : generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | progress first firstSmaller =>
      rw [computed] at fired
      cases fired
      exact generalRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete fuel base problem _ _ held computed
  | refuted absent =>
      rw [computed] at fired
      cases fired
  | stuck =>
      rw [computed] at fired
      dsimp only at fired
      split at fired
      · rename_i found rule
        cases fired
        exact millerNormal_of_headDrop rigid held (rotateIntersectSearch_headDrop facts roots heads algebra rigid
          complete declared choices reducer root normalizes headTypingUnique fuel problem _ rule)
      · cases fired

include rigid in
/-- **The last round keeps the class wherever the cumulative round does.** -/
theorem inPlaceRound_keeps (fuel : Nat)
    (base : KeepsMillerNormal facts roots heads algebra rigid complete fun problem =>
      cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem) :
    KeepsMillerNormal facts roots heads algebra rigid complete fun problem =>
      inPlaceRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  intro Θ problem update smaller held fired
  dsimp only at fired
  unfold inPlaceRound at fired
  cases computed : olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | progress first firstSmaller =>
      rw [computed] at fired
      cases fired
      exact olderRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete fuel base problem _ _ held computed
  | refuted absent =>
      rw [computed] at fired
      cases fired
  | stuck =>
      rw [computed] at fired
      dsimp only at fired
      split at fired
      · rename_i found rule
        cases fired
        exact millerNormal_of_headDrop rigid held (inPlaceIntersectSearch_headDrop facts roots heads algebra rigid
          complete declared choices reducer root normalizes headTypingUnique fuel problem _ rule)
      · cases fired

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- **Acceptance for the last family, reduced to firing on the class and closure of the cumulative round.** If the last
round is eventually not stuck on every nonempty `MillerNormal` store, and the cumulative round keeps the class at every
budget, then the last family decides every store of the dynamic pattern fragment whose opened sides have β-normal
reducts, with a principal answer or a certified refutation, and the same outcome at every larger joint budget. -/
theorem inPlace_decided_of_cumulative
    (firing : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, MillerNormal problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        inPlaceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck)
    (closure : ∀ fuel, KeepsMillerNormal facts roots heads algebra rigid complete fun problem =>
      cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem)
    (opened : OpenedNormal problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((inPlaceFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((inPlaceFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver budget) problem budget ∧
      ((∃ state finished, run ((inPlaceFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
              .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent, run ((inPlaceFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger = .refuted absent)) :=
  (inPlaceSettledOfConst facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete stable (fun problem => MillerNormal problem)
    (fun held nonempty => by
      obtain ⟨bound, fires⟩ := firing held nonempty
      exact ⟨bound, fun larger enough => ⟨fires larger enough, fun {update} {smaller} fired =>
        inPlaceRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete larger (closure larger) _ update smaller held fired⟩⟩)).decided
    ⟨stratifiedMiller_of_fragment inside, opened⟩

end ContextualDependentAcceptance3
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
