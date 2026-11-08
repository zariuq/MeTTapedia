import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance3Anywhere
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralDeadBinder

/-!
# Acceptance for the dead-binder family, on the permuted class

Every progress of the dead-binder rule **drops an equation of the store under a pattern answer** (`deadSearch_drop`):
in-place intersection drops the first equation of the store read without its dead binder, and the answer that makes
the reduced equation valid makes the equation itself valid, since the binder comes back
(`ContextualDependentIntersectionGeneral.solves_of_reduced`). So the dead-binder round keeps the corrected class
wherever the cumulative round does (`deadRound_keeps`), and acceptance for the dead-binder family reduces to firing and
the closure of the cumulative round on `PermutedNormal` (`dead_decided_of_cumulative`), as for the anywhere family.
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

/-- **A drop at a permutation of the store is a drop of the store.** -/
theorem Drop.rephrase {Θ : Context S.R} {problem problem' : EquationStore (TotalTerm Θ)}
    (perm : problem'.Perm problem) (same : (frames S.levels).Equivalent problem problem')
    {update : Update S.levels problem'} (drops : Drop problem' update) : Drop problem (update.rephrase same) := by
  obtain ⟨first, rest, σ, perm', answer, remaining, valid, pattern⟩ := drops
  exact ⟨first, rest, σ, perm'.trans perm, answer, remaining, valid, pattern⟩

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

include rigid in
/-- **Intersection behind a dead binder drops the equation under a pattern answer.** -/
theorem deadAt_drop (fuel : Nat) {Θ : Context S.R} :
    ∀ (stored : EquationStore (TotalTerm Θ)) {found : SitedProgress facts roots heads algebra rigid complete stored},
      deadAt facts roots heads algebra rigid complete declared choices reducer root normalizes headTypingUnique
        strengthening fuel stored = some found → Drop stored found.val
  | [], _, fired => by cases fired
  | equation :: rest, found, fired => by
      simp only [deadAt] at fired
      split at fired
      · cases fired
      · rename_i dead _
        obtain ⟨inner, computed, rfl⟩ := Option.map_eq_some_iff.mp fired
        obtain ⟨first, rest', σ, same, answer, remaining, valid, pattern⟩ :=
          inPlaceIntersectSearch_headDrop facts roots heads algebra rigid complete declared choices reducer root
            normalizes headTypingUnique fuel (dead.reduced :: rest) _ computed
        obtain ⟨rfl, rfl⟩ := List.cons.inj same
        exact ⟨equation, rest, σ, List.Perm.refl _, answer, remaining, fun τ =>
          (solves_reindex σ τ _ _).mpr (solves_of_reduced dead (τ ≫ σ) ((solves_reindex σ τ _ _).mp (valid τ))),
          pattern⟩

include rigid in
/-- **Every progress of the dead-binder rule drops an equation under a pattern answer.** -/
theorem deadSearch_drop (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    ∀ (rotations : List Nat) {found : SitedProgress facts roots heads algebra rigid complete problem},
      deadSearch facts roots heads algebra rigid complete declared choices reducer root normalizes headTypingUnique
        strengthening fuel problem rotations = some found → Drop problem found.val
  | [], _, fired => by cases fired
  | k :: rest, found, fired => by
      simp only [deadSearch] at fired
      split at fired
      · rename_i inner computed
        cases fired
        exact Drop.rephrase (List.rotate_perm problem k) (equivalent_perm (List.rotate_perm problem k).symm)
          (deadAt_drop facts roots heads algebra rigid complete declared choices reducer root normalizes
            headTypingUnique strengthening fuel (problem.rotate k) computed)
      · exact deadSearch_drop fuel problem rest fired

include rigid in
/-- **The dead-binder round keeps the corrected class wherever the cumulative round does.** -/
theorem deadRound_keeps (fuel : Nat)
    (base : KeepsPermutedNormal facts roots heads algebra rigid complete fun problem =>
      cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem) :
    KeepsPermutedNormal facts roots heads algebra rigid complete fun problem =>
      deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  intro Θ problem update smaller held fired
  dsimp only at fired
  unfold deadRound at fired
  cases computed : anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | progress first firstSmaller =>
      rw [computed] at fired
      cases fired
      exact anywhereRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
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
        exact permutedNormal_of_drop rigid held (deadSearch_drop facts roots heads algebra rigid complete declared
          choices reducer root normalizes headTypingUnique strengthening fuel problem _ rule)
      · cases fired

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- **Acceptance for the dead-binder family, reduced to firing on the corrected class and closure of the cumulative
round.** -/
theorem dead_decided_of_cumulative
    (firing : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedNormal problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck)
    (closure : ∀ fuel, KeepsPermutedNormal facts roots heads algebra rigid complete fun problem =>
      cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem)
    (opened : OpenedNormal problem) :
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
  (deadSettledOfConst facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening stable (fun problem => PermutedNormal problem)
    (fun held nonempty => by
      obtain ⟨bound, fires⟩ := firing held nonempty
      exact ⟨bound, fun larger enough => ⟨fires larger enough, fun {update} {smaller} fired =>
        deadRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening larger (closure larger) _ update smaller held
          fired⟩⟩)).decided
    ⟨permutedMiller_of_fragment inside, opened⟩

end ContextualDependentAcceptance3
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
