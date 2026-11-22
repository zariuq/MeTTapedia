import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance3
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralAnywhere
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentMillerClosurePermuted

/-!
# A conditional decision for the anywhere family, on the permuted class

The corrected class is `PermutedNormal`: the permuted Miller class (`ContextualDependentMillerClosure.PermutedMiller`),
with β-normal reducts of every opened side. Every intersection rule of the anywhere family **drops an equation of the
store under a pattern answer** (`Drop`): the general, older and in-place rules drop the first equation
(`HeadDrop`), and the anywhere rule drops the first equation of a rotation (`anywhereSearch_drop`). A drop keeps the
class (`permutedNormal_of_drop`), so every anywhere round keeps it wherever the cumulative round does
(`anywhereRound_keeps`).

**The reduction** (`anywhere_decided_of_cumulative`): if, on `PermutedNormal` stores, the anywhere round is eventually
not stuck (firing) and the cumulative round keeps the class (closure of the R86–R110 rules), then the anywhere family
decides every store of the dynamic pattern fragment whose opened sides have β-normal reducts, with a principal answer
or a certified refutation, at every large joint budget.

Unlike `ContextualDependentAcceptance3.inPlace_decided_of_cumulative` on `MillerNormal`, whose closure hypothesis the
reorder witness refutes (`ContextualDependentMillerClosure.ReorderControls.cumulativeRound_not_keeps`), the closure
hypothesis here survives the witness: its residual store is in the permuted class
(`ContextualDependentMillerClosure.ReorderControls.reorder_residual_permuted`). At the tower the two hypotheses do not
both hold: the tower is strongly normalizing, so every store has normal reducts, and the conclusion would decide
`crossStore`, in the fragment, solvable and without principal answer
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). For every store, runs are exact; on
`crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`).
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

/-- **The corrected class of the reduction**: the permuted Miller class, with β-normal reducts of every opened side. -/
def PermutedNormal {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  PermutedMiller S.levels problem ∧ OpenedNormal problem

theorem PermutedNormal.of_millerNormal {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (held : MillerNormal problem) : PermutedNormal problem :=
  ⟨.of_stratifiedMiller held.1, held.2⟩

/-- **An update drops an equation of the store under a pattern answer**: in some order of the store, the first
equation is made valid by a pattern answer and the residual store is the others, instantiated. -/
def Drop {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (update : Update S.levels problem) : Prop :=
  ∃ (first : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ)) (σ : update.target ⟶ Θ),
    (first :: rest).Perm problem ∧ σ = update.answer ∧ update.remaining = (frames S.levels).applyStore σ rest ∧
    (∀ {Δ : Context S.R} (τ : Δ ⟶ update.target), (frames S.levels).Solves τ (first.1.reindex σ, first.2.reindex σ)) ∧
    Nonempty (PatternAnswer S.R (bodyFlexible (o := Θ.arity) 0) (bodyFlexible (o := update.target.arity) 0)
      σ.substitution)

theorem drop_of_headDrop {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {update : Update S.levels problem}
    (drops : HeadDrop problem update) : Drop problem update := by
  obtain ⟨first, rest, σ, rfl, answer, remaining, valid, pattern⟩ := drops
  exact ⟨first, rest, σ, List.Perm.refl _, answer, remaining, valid, pattern⟩

/-- **A drop at a permutation of the store is a drop of the store.** -/
theorem drop_rephrase {Θ : Context S.R} {problem problem' : EquationStore (TotalTerm Θ)}
    (perm : problem'.Perm problem) (same : (frames S.levels).Equivalent problem problem')
    {update : Update S.levels problem'} (drops : HeadDrop problem' update) : Drop problem (update.rephrase same) := by
  obtain ⟨first, rest, σ, rfl, answer, remaining, valid, pattern⟩ := drops
  exact ⟨first, rest, σ, perm, answer, remaining, valid, pattern⟩

/-- **A drop keeps the corrected class.** -/
theorem permutedNormal_of_drop (rigid : ∀ name, S.roles name = .rigid) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} {update : Update S.levels problem} (held : PermutedNormal problem)
    (drops : Drop problem update) : PermutedNormal update.remaining := by
  obtain ⟨first, rest, σ, perm, _, remaining, valid, ⟨answer⟩⟩ := drops
  have permuted : PermutedMiller S.levels (first :: rest) := held.1.perm perm.symm
  have opened : OpenedNormal (first :: rest) := held.2.perm perm
  rw [remaining]
  refine ⟨permutedMiller_answer_drop rigid σ answer permuted opened valid, ?_⟩
  exact openedNormal_applyStore rigid σ answer
    (fun equation member => permuted.sides_of_mem (List.mem_cons_of_mem _ member))
    fun equation member => opened equation (List.mem_cons_of_mem _ member)

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
/-- **Every progress of the anywhere rule drops an equation under a pattern answer.** -/
theorem anywhereSearch_drop (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    ∀ (rotations : List Nat) {found : SitedProgress facts roots heads algebra rigid complete problem},
      anywhereSearch facts roots heads algebra rigid complete declared choices reducer root normalizes
        headTypingUnique fuel problem rotations = some found → Drop problem found.val
  | [], _, fired => by cases fired
  | k :: rest, found, fired => by
      simp only [anywhereSearch] at fired
      split at fired
      · rename_i inner computed
        cases fired
        exact drop_rephrase (List.rotate_perm problem k) (equivalent_perm (List.rotate_perm problem k).symm)
          (inPlaceIntersectSearch_headDrop facts roots heads algebra rigid complete declared choices reducer root
            normalizes headTypingUnique fuel (problem.rotate k) _ computed)
      · exact anywhereSearch_drop fuel problem rest fired

/-- **A round keeps the corrected class**: every progress of a `PermutedNormal` store is `PermutedNormal`. -/
def KeepsPermutedNormal
    (round : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
      Round S.levels (weightRank facts roots heads algebra rigid complete) problem) : Prop :=
  ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (update : Update S.levels problem)
    (smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
      (weightRank facts roots heads algebra rigid complete problem)),
    PermutedNormal problem → round problem = .progress update smaller → PermutedNormal update.remaining

include rigid in
theorem generalRound_keepsPermuted (fuel : Nat)
    (base : KeepsPermutedNormal facts roots heads algebra rigid complete fun problem =>
      cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem) :
    KeepsPermutedNormal facts roots heads algebra rigid complete fun problem =>
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
        exact permutedNormal_of_drop rigid held (drop_of_headDrop (generalIntersectRule_headDrop facts roots heads
          algebra rigid complete declared choices reducer root normalizes headTypingUnique fuel problem rule))
      · cases fired

include rigid in
theorem olderRound_keepsPermuted (fuel : Nat)
    (base : KeepsPermutedNormal facts roots heads algebra rigid complete fun problem =>
      cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem) :
    KeepsPermutedNormal facts roots heads algebra rigid complete fun problem =>
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
      exact generalRound_keepsPermuted facts roots heads algebra rigid complete declared choices reducer root normalizes
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
        exact permutedNormal_of_drop rigid held (drop_of_headDrop (rotateIntersectSearch_headDrop facts roots heads
          algebra rigid complete declared choices reducer root normalizes headTypingUnique fuel problem _ rule))
      · cases fired

include rigid in
theorem inPlaceRound_keepsPermuted (fuel : Nat)
    (base : KeepsPermutedNormal facts roots heads algebra rigid complete fun problem =>
      cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem) :
    KeepsPermutedNormal facts roots heads algebra rigid complete fun problem =>
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
      exact olderRound_keepsPermuted facts roots heads algebra rigid complete declared choices reducer root normalizes
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
        exact permutedNormal_of_drop rigid held (drop_of_headDrop (inPlaceIntersectSearch_headDrop facts roots heads
          algebra rigid complete declared choices reducer root normalizes headTypingUnique fuel problem _ rule))
      · cases fired

include rigid in
/-- **The anywhere round keeps the corrected class wherever the cumulative round does.** -/
theorem anywhereRound_keeps (fuel : Nat)
    (base : KeepsPermutedNormal facts roots heads algebra rigid complete fun problem =>
      cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem) :
    KeepsPermutedNormal facts roots heads algebra rigid complete fun problem =>
      anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  intro Θ problem update smaller held fired
  dsimp only at fired
  unfold anywhereRound at fired
  cases computed : inPlaceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | progress first firstSmaller =>
      rw [computed] at fired
      cases fired
      exact inPlaceRound_keepsPermuted facts roots heads algebra rigid complete declared choices reducer root normalizes
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
        exact permutedNormal_of_drop rigid held (anywhereSearch_drop facts roots heads algebra rigid complete declared
          choices reducer root normalizes headTypingUnique fuel problem _ rule)
      · cases fired

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- **Conditional decision for the anywhere family, from firing on the corrected class and closure of the cumulative
round.** If the anywhere round is eventually not stuck on every nonempty `PermutedNormal` store, and the cumulative
round keeps the class at every budget, then the anywhere family decides every store of the dynamic pattern fragment
whose opened sides have β-normal reducts, with a principal answer or a certified refutation, and the same outcome at
every larger joint budget. At the tower's setting the conclusion fails on `crossStore`
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`), so there the hypotheses do not both hold.
For every store, runs are exact; on `crossStore` they stop postponed
(`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem anywhere_decided_of_cumulative
    (firing : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedNormal problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck)
    (closure : ∀ fuel, KeepsPermutedNormal facts roots heads algebra rigid complete fun problem =>
      cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem)
    (opened : OpenedNormal problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((anywhereFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((anywhereFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver budget) problem budget ∧
      ((∃ state finished, run ((anywhereFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
              .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent, run ((anywhereFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger = .refuted absent)) :=
  (anywhereSettledOfConst facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete stable (fun problem => PermutedNormal problem)
    (fun held nonempty => by
      obtain ⟨bound, fires⟩ := firing held nonempty
      exact ⟨bound, fun larger enough => ⟨fires larger enough, fun {update} {smaller} fired =>
        anywhereRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete larger (closure larger) _ update smaller held fired⟩⟩)).decided
    ⟨permutedMiller_of_fragment inside, opened⟩

end ContextualDependentAcceptance3
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
