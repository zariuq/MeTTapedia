import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveFragmentPruneKept

/-!
# One-equation stores: every solved answer leaves nothing

On a store with one equation, every solved answer of the pattern rule and of the prune rule leaves
the empty store, at every budget. The pattern step's answers are finished by construction; the other
equations of the store are instantiated by the answer, and here there are none; pruning and
exchanging keep a one-equation store a one-equation store, on which the final pattern search then
finishes.

So the class of one-equation stores on which, from some budget on, the distinct-locals rule fires,
or the pattern rule fires, or it does not and the prune rule does, is closed under every answer,
and the rigid round **settles** on it. Decisiveness on a one-equation store at one joint budget
therefore reduces to the eventual firing of one of these rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDecisiveFragment

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentScope ContextualDependentConversionBudget
open ContextualDependentGeneralPattern ContextualDependentWorklist ContextualDependentPatternSolver
open ContextualDependentUpdate ContextualDependentPrune

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (rigid : ∀ name, S.roles name = .rigid) (facts : FormFacts S.R S.roles)
  (complete : AlgorithmicComplete S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-! ## The pattern rule -/

/-- **A solved answer of the pattern rule on one reading of a lone equation leaves nothing.** -/
theorem tryActive_single_finishes (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    {scopeType : TypeOver (extend Γ type)} (scope : Spine scopeType) (active : Active scope.target)
    (equation : Equation (TotalTerm (extend Γ type)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution) :
    ∀ {update : Update S.levels [equation]} {smaller : update.target.arity < (extend Γ type).arity},
      tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal fuel
        type scope active equation view [] = some (.solved update smaller) → update.remaining = [] := by
  intro update smaller
  unfold tryActive
  split
  · intro fired; nomatch fired
  split
  · intro fired; nomatch fired
  split
  · intro fired; nomatch fired
  try dsimp only
  split
  · rename_i result finished _
    try dsimp only
    split
    · intro fired
      cases fired
      exact (List.nil_append result.update.remaining).trans finished
    · intro fired; nomatch fired
  · intro fired; nomatch fired
  · split <;> (intro fired; nomatch fired)

/-- **A solved answer of the pattern rule on a lone equation leaves nothing.** -/
theorem tryEquation_single_finishes (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (equation : Equation (TotalTerm (extend Γ type))) :
    ∀ {update : Update S.levels [equation]} {smaller : update.target.arity < (extend Γ type).arity},
      tryEquation rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        fuel type equation [] = some (.solved update smaller) → update.remaining = [] := by
  intro update smaller
  unfold tryEquation
  split
  · intro fired; nomatch fired
  · rename_i scope active view _
    split
    · rename_i found first
      intro fired
      cases fired
      exact tryActive_single_finishes rigid facts complete roots heads algebra declared choices reducer normalizes
        certifyNormal fuel type scope active equation view first
    · exact tryActive_single_finishes rigid facts complete roots heads algebra declared choices reducer normalizes
        certifyNormal fuel type scope ⟨active.type, active.right, active.left⟩ equation
        (fun solution => (view solution).trans (toScoped_swap scope active solution).symm)

/-- **A solved answer of the pattern search on a one-equation store leaves nothing.** -/
theorem searchStore_single_finishes (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) :
    ∀ (problem : EquationStore (TotalTerm (extend Γ type))), problem.length = 1 →
    ∀ {update : Update S.levels problem} {smaller : update.target.arity < (extend Γ type).arity},
      searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        fuel type problem = some (.solved update smaller) → update.remaining = []
  | [equation], _ => by
      simp only [searchStore]
      split
      · rename_i found first
        intro fired
        cases fired
        exact tryEquation_single_finishes rigid facts complete roots heads algebra declared choices reducer root
          normalizes certifyNormal fuel type equation first
      · intro fired
        cases fired
  | [], one => absurd one (by simp)
  | _ :: _ :: _, one => absurd one (by simp)

/-- The same, for a store known to have one equation. -/
theorem searchStore_length_one_finishes (fuel : Nat) {Γ : Context S.R} {type : TypeOver Γ}
    {problem : EquationStore (TotalTerm (extend Γ type))}
    {update : Update S.levels problem} {smaller : update.target.arity < (extend Γ type).arity}
    (fired : searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      fuel type problem = some (.solved update smaller)) (one : problem.length = 1) :
    update.remaining = [] :=
  searchStore_single_finishes rigid facts complete roots heads algebra declared choices reducer root normalizes
    certifyNormal fuel type problem one fired

/-- **A solved answer of the pattern rule on a one-equation store leaves nothing.** -/
theorem patternRule_single_finishes (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    ∀ {update : Update S.levels [equation]} {smaller : update.target.arity < Θ.arity},
      patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        fuel [equation] = some (.solved update smaller) → update.remaining = [] := by
  intro update smaller
  unfold patternRule
  split
  · intro fired; nomatch fired
  · rename_i view read
    clear read
    rcases view with ⟨base, type, same⟩
    subst same
    exact searchStore_single_finishes rigid facts complete roots heads algebra declared choices reducer root
      normalizes certifyNormal fuel type [equation] rfl

/-! ## The prune rule -/

set_option maxHeartbeats 1000000 in
/-- **A solved answer of the prune rule on one recognized pattern of a lone equation leaves
nothing**: pruning and exchanging keep one equation, and the pattern search then finishes it. -/
theorem tryPrune_single_finishes (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀)
    (newer : TypeOver (extend Γ₀ older)) {scopeType : TypeOver (extend (extend Γ₀ older) newer)}
    (scope : Spine scopeType) (active : Active scope.target)
    (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (spine : Spine newer) (recognized : Recognized spine scope active) :
    ∀ {update : Update S.levels [equation]} {smaller : update.target.arity < (extend (extend Γ₀ older) newer).arity},
      tryPrune rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel older newer scope active equation view [] spine recognized =
          some (.solved update smaller) → update.remaining = [] := by
  intro update smaller
  unfold tryPrune
  try dsimp only
  split
  · intro fired; nomatch fired
  split
  · intro fired; nomatch fired
  split
  · intro fired; nomatch fired
  split
  · intro fired; nomatch fired
  split
  swap
  · intro fired; nomatch fired
  split
  swap
  · intro fired; nomatch fired
  try dsimp only
  split
  swap
  · intro fired; nomatch fired
  split
  swap
  · intro fired; nomatch fired
  try dsimp only
  split
  · intro fired; nomatch fired
  split
  · intro fired; nomatch fired
  split
  · intro fired; nomatch fired
  split
  · intro fired; nomatch fired
  split
  swap
  · intro fired; nomatch fired
  split
  swap
  · intro fired; nomatch fired
  split
  swap
  · intro fired; nomatch fired
  try dsimp only
  split
  swap
  · intro fired; nomatch fired
  try dsimp only
  split
  · intro fired; nomatch fired
  · rename_i solved _ searched
    intro fired
    cases fired
    have done := searchStore_length_one_finishes rigid facts complete roots heads algebra declared choices reducer root
      normalizes certifyNormal fuel searched rfl
    exact done
  · intro fired; nomatch fired

/-- **A solved answer of the prune rule on one reading of a lone equation leaves nothing.** -/
theorem pruneActive_single_finishes (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀)
    (newer : TypeOver (extend Γ₀ older)) {scopeType : TypeOver (extend (extend Γ₀ older) newer)}
    (scope : Spine scopeType) (active : Active scope.target)
    (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution) :
    ∀ {update : Update S.levels [equation]} {smaller : update.target.arity < (extend (extend Γ₀ older) newer).arity},
      pruneActive rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel older newer scope active equation view [] = some (.solved update smaller) →
          update.remaining = [] := by
  intro update smaller
  unfold pruneActive
  split
  · intro fired; nomatch fired
  split
  · intro fired; nomatch fired
  split
  · intro fired; nomatch fired
  · exact tryPrune_single_finishes rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel older newer scope active equation view _ _

/-- **A solved answer of the prune rule on a lone equation leaves nothing.** -/
theorem pruneEquation_single_finishes (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀)
    (newer : TypeOver (extend Γ₀ older)) (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer))) :
    ∀ {update : Update S.levels [equation]} {smaller : update.target.arity < (extend (extend Γ₀ older) newer).arity},
      pruneEquation rigid facts complete roots heads algebra declared choices reducer root normalizes
        certifyNormal headTypingUnique fuel older newer equation [] = some (.solved update smaller) →
          update.remaining = [] := by
  intro update smaller
  unfold pruneEquation
  split
  · intro fired; nomatch fired
  · rename_i scope active view _
    split
    · rename_i found first
      intro fired
      cases fired
      exact pruneActive_single_finishes rigid facts complete roots heads algebra declared choices reducer root
        normalizes certifyNormal headTypingUnique fuel older newer scope active equation view first
    · exact pruneActive_single_finishes rigid facts complete roots heads algebra declared choices reducer root
        normalizes certifyNormal headTypingUnique fuel older newer scope ⟨active.type, active.right, active.left⟩ equation
        (fun solution => (view solution).trans (toScoped_swap scope active solution).symm)

/-- **A solved answer of the prune search on a one-equation store leaves nothing.** -/
theorem pruneSearch_single_finishes (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀)
    (newer : TypeOver (extend Γ₀ older)) (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer))) :
    ∀ {update : Update S.levels [equation]} {smaller : update.target.arity < (extend (extend Γ₀ older) newer).arity},
      pruneSearch rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel older newer [equation] = some (.solved update smaller) → update.remaining = [] := by
  intro update smaller
  simp only [pruneSearch]
  split
  · rename_i found first
    intro fired
    cases fired
    exact pruneEquation_single_finishes rigid facts complete roots heads algebra declared choices reducer root
      normalizes certifyNormal headTypingUnique fuel older newer equation first
  · intro fired
    cases fired

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
/-- A computation at the two newest declarations whose solved answers on one-equation stores leave
nothing leaves nothing on a one-equation store. -/
theorem throughTwo_single {Θ : Context S.R} (outer : Newest Θ) (inner : Newest outer.base)
    (equation : Equation (TotalTerm Θ))
    (solve : {Γ₀ : Context S.R} → (older : TypeOver Γ₀) → (newer : TypeOver (extend Γ₀ older)) →
      (stored : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) → Option (Found stored))
    (finishes : ∀ {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
      (single : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
      {update : Update S.levels [single]} {smaller : update.target.arity < (extend (extend Γ₀ older) newer).arity},
      solve older newer [single] = some (.solved update smaller) → update.remaining = []) :
    ∀ {update : Update S.levels [equation]} {smaller : update.target.arity < Θ.arity},
      throughTwo outer inner [equation] solve = some (.solved update smaller) → update.remaining = [] := by
  cases outer with
  | mk base newer same =>
      cases inner with
      | mk base₀ older same₀ =>
          change base = extend base₀ older at same₀
          subst same₀
          subst same
          exact finishes older newer equation

/-- **A solved answer of the prune rule on a one-equation store leaves nothing.** -/
theorem pruneRule_single_finishes (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    ∀ {update : Update S.levels [equation]} {smaller : update.target.arity < Θ.arity},
      pruneRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel [equation] = some (.solved update smaller) → update.remaining = [] := by
  intro update smaller
  unfold pruneRule
  split
  · intro fired; nomatch fired
  split
  · intro fired; nomatch fired
  exact throughTwo_single _ _ equation _ (fun older newer single => pruneSearch_single_finishes rigid facts complete
    roots heads algebra declared choices reducer root normalizes certifyNormal headTypingUnique fuel older newer single)

/-! ## Settling one-equation stores -/

/-- **One-equation stores on which a rule eventually fires**, and empty stores: from some budget on,
the distinct-locals rule fires, or the pattern rule fires, or it does not and the prune rule does. -/
def SingleFiring {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) : Prop :=
  problem.length ≤ 1 ∧ (problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
    (ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared choices
      reducer root larger problem).isSome ∨
    (ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared choices
        reducer root larger problem = none ∧
      ((patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          larger problem).isSome ∨
        (patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
            larger problem = none ∧
          (pruneRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
            headTypingUnique larger problem).isSome))))

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- **The rigid round settles on one-equation stores on which a rule eventually fires.** Every
solved answer there leaves the empty store, so the class is closed under answers without further
hypotheses; eventual constancy of every rule does the rest. -/
def singleSettled : ContextualDependentDecisiveDriver.Settled
    (rigidFamily rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      headTypingUnique) :=
  settledWhereRuleFires rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
    headTypingUnique stable
    (fun problem => SingleFiring rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique problem)
    (by
      intro Γ problem inside nonempty
      obtain ⟨short, firing⟩ := inside
      obtain ⟨bound, fires⟩ := firing nonempty
      obtain ⟨equation, rfl⟩ : ∃ equation, problem = [equation] := by
        match problem, short, nonempty with
        | [equation], _, _ => exact ⟨equation, rfl⟩
        | [], _, empty => exact absurd rfl empty
        | _ :: _ :: _, long, _ => simp at long
      refine ⟨bound, fun larger enough => ?_⟩
      rcases fires larger enough with locals | ⟨noLocals, firing⟩
      · exact .inl locals
      · refine .inr ⟨noLocals, ?_, ?_⟩
        · unfold firstRule
          rcases firing with pattern | ⟨noPattern, prune⟩
          · obtain ⟨found, computed⟩ := Option.isSome_iff_exists.mp pattern
            rw [computed]
            rfl
          · rw [noPattern]
            obtain ⟨found, computed⟩ := Option.isSome_iff_exists.mp prune
            dsimp only
            rw [computed]
            rfl
        · intro update smaller fired
          have finished : update.remaining = [] := by
            unfold firstRule at fired
            rcases firing with pattern | ⟨noPattern, prune⟩
            · obtain ⟨found, computed⟩ := Option.isSome_iff_exists.mp pattern
              rw [computed] at fired
              cases fired
              exact patternRule_single_finishes rigid facts complete roots heads algebra declared choices reducer
                root normalizes certifyNormal larger equation computed
            · rw [noPattern] at fired
              obtain ⟨found, computed⟩ := Option.isSome_iff_exists.mp prune
              dsimp only at fired
              rw [computed] at fired
              cases fired
              exact pruneRule_single_finishes rigid facts complete roots heads algebra declared choices reducer
                root normalizes certifyNormal headTypingUnique larger equation computed
          refine ⟨by rw [finished]; exact Nat.zero_le _, fun nonempty => absurd finished nonempty⟩)

include stable in
/-- **Decisiveness on a one-equation store at one joint budget**, as soon as a rule eventually fires
on it: from one budget on, used both for the executables and for the rounds, the rigid solver reaches
the same outcome, a principal answer or a certified refutation. -/
theorem single_decided {Γ : Context S.R} {equation : Equation (TotalTerm Γ)}
    (firing : ∃ bound, ∀ larger, bound ≤ larger →
      (ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared choices
        reducer root larger [equation]).isSome ∨
      (ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared choices
          reducer root larger [equation] = none ∧
        ((patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
            larger [equation]).isSome ∨
          (patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
              larger [equation] = none ∧
            (pruneRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
              headTypingUnique larger [equation]).isSome)))) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((rigidFamily rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique).solver larger) [equation] larger =
        run ((rigidFamily rigid facts complete roots heads algebra declared choices reducer root normalizes
          certifyNormal headTypingUnique).solver budget) [equation] budget ∧
      ((∃ state finished, run ((rigidFamily rigid facts complete roots heads algebra declared choices reducer root
            normalizes certifyNormal headTypingUnique).solver larger) [equation] larger = .solved state finished ∧
          (frames S.levels).Principal [equation] state.answer) ∨
        (∃ absent, run ((rigidFamily rigid facts complete roots heads algebra declared choices reducer root normalizes
          certifyNormal headTypingUnique).solver larger) [equation] larger = .refuted absent)) :=
  (singleSettled rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
    headTypingUnique stable).decided ⟨by simp, fun _ => firing⟩

end ContextualDependentDecisiveFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
