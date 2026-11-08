import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveFragmentInstances

/-!
# A pattern answer found at one budget is kept at every larger budget

When, at one budget, every executable on the pattern rule's path succeeds — annotation comparison,
both spine discoveries, both normalizations of the opened sides, and the recovery of the answer —
the rule returns the same answer at every larger budget: each of those results is kept, and the
readers on the path do not depend on the budget.

For a single-equation store this gives a budget from which the pattern rule fires with a fixed
principal answer, which is what the settling criterion needs.
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
variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
/-- A finished normalization of an endpoint is kept. -/
theorem normalizeAt_kept {C : Context S.R} {type : TypeOver C} (term : Term C type) {budget : Nat}
    (finished : (ContextualDependentNormalization.reduceTerm root facts roots heads budget ⟨type, term⟩).isSome) :
    ∀ larger, budget ≤ larger →
      ContextualDependentPatternSolver.normalizeAt facts roots heads root larger term =
        ContextualDependentPatternSolver.normalizeAt facts roots heads root budget term := by
  obtain ⟨result, computed⟩ := Option.isSome_iff_exists.mp finished
  intro larger enough
  apply Subtype.ext
  apply Term.ext
  change (ContextualDependentNormalization.termAt root facts roots heads larger ⟨type, term⟩).2.code =
    (ContextualDependentNormalization.termAt root facts roots heads budget ⟨type, term⟩).2.code
  unfold ContextualDependentNormalization.termAt
  rw [reduceTerm_mono root facts roots heads _ computed enough, computed]

include stable

omit [DecidableRel S.R.cumulative] in
theorem compareTypes_kept {Γ : Context S.R} (first second : TypeOver Γ) {budget : Nat}
    (accepted : (ContextualDependentEta.Conversion.compareTypes facts roots heads algebra reducer budget first second).isSome) :
    ∀ larger, budget ≤ larger →
      ContextualDependentEta.Conversion.compareTypes facts roots heads algebra reducer larger first second =
        ContextualDependentEta.Conversion.compareTypes facts roots heads algebra reducer budget first second := by
  intro larger enough
  unfold ContextualDependentEta.Conversion.compareTypes at accepted ⊢
  cases computed : ExecutableConversion.types S.R reducer budget Γ.raw first.code second.code with
  | none => rw [computed] at accepted; cases accepted
  | some certificate => rw [types_mono reducer stable computed enough]

/-- **The scoped reading found at one budget is kept** when its comparison, discovery and both
normalizations succeeded there. -/
theorem viewEquation_kept {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) {budget : Nat}
    (same : PLift (TypeEq S.R Θ.raw equation.2.1.code equation.1.1.code))
    (compared : ContextualDependentEta.Conversion.compareTypes facts roots heads algebra reducer budget equation.2.1
      equation.1.1 = some same)
    {scope : Spine equation.1.1}
    (discovered : ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer budget
      (lamDepth equation.1.2.code) equation.1.1 = some scope)
    (leftFinished : (ContextualDependentNormalization.reduceTerm root facts roots heads budget
      ⟨scope.result, scope.openFunction equation.1.2⟩).isSome)
    (rightFinished : (ContextualDependentNormalization.reduceTerm root facts roots heads budget
      ⟨scope.result, scope.openFunction (equation.2.2.convertType equation.1.1 same.down)⟩).isSome) :
    ∀ larger, budget ≤ larger →
      viewEquation facts roots heads algebra declared choices reducer root larger equation =
        viewEquation facts roots heads algebra declared choices reducer root budget equation := by
  intro larger enough
  have leftSame := normalizeAt_kept facts roots heads root (scope.openFunction equation.1.2) leftFinished larger enough
  have rightSame := normalizeAt_kept facts roots heads root
    (scope.openFunction (equation.2.2.convertType equation.1.1 same.down)) rightFinished larger enough
  unfold viewEquation
  simp only [Option.bind_eq_bind]
  erw [compareTypes_kept facts roots heads algebra reducer stable equation.2.1 equation.1.1
    (by rw [compared]; rfl) larger enough, compared]
  simp only [Option.bind_some]
  erw [discover_mono facts roots heads algebra declared choices reducer stable _ equation.1.1 discovered enough,
    discovered]
  simp only [Option.bind_some]
  show some _ = some _
  congr 1
  refine Sigma.ext rfl (heq_of_eq (PSigma.ext ?_ (proof_irrel_heq _ _)))
  change (⟨scope.result,
      (ContextualDependentPatternSolver.normalizeAt facts roots heads root larger (scope.openFunction equation.1.2)).1,
      (ContextualDependentPatternSolver.normalizeAt facts roots heads root larger
        (scope.openFunction (equation.2.2.convertType equation.1.1 same.down))).1⟩ : Active scope.target) =
    ⟨scope.result,
      (ContextualDependentPatternSolver.normalizeAt facts roots heads root budget (scope.openFunction equation.1.2)).1,
      (ContextualDependentPatternSolver.normalizeAt facts roots heads root budget
        (scope.openFunction (equation.2.2.convertType equation.1.1 same.down))).1⟩
  rw [leftSame, rightSame]

/-- **The pattern rule on one reading is kept** once its spine discovery and recovery succeeded. -/
theorem tryActive_kept {Γ : Context S.R} (type : TypeOver Γ) {scopeType : TypeOver (extend Γ type)}
    (scope : Spine scopeType) (active : Active scope.target) (equation : Equation (TotalTerm (extend Γ type)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ type))) {budget : Nat} {headIndex : Fin scope.target.arity}
    {arguments : List (Fin scope.target.arity)} (read : readApplication active.left.code = some (headIndex, arguments))
    {spine : Spine type}
    (discovered : ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer budget
      arguments.length type = some spine)
    {found : Recognized spine scope active} (recognized : recognize spine scope active = some found)
    {recovery : ContextualDependentTypedInversion.Recovery found.pattern.bodyInclusion spine.result found.right.code}
    (recovered : ContextualDependentTypedInversion.recover facts roots heads algebra declared choices reducer budget
      found.pattern.bodyInclusion spine.result found.right.code = some recovery) :
    ∀ larger, budget ≤ larger →
      tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal larger type
          scope active equation view rest =
        tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal budget type
          scope active equation view rest := by
  intro larger enough
  unfold tryActive
  rw [read]
  dsimp only
  erw [discover_mono facts roots heads algebra declared choices reducer stable _ type discovered enough, discovered]
  dsimp only
  rw [recognized]
  dsimp only
  unfold Pattern.step
  erw [ContextualDependentRecoveryBudget.recover_mono facts roots heads algebra declared choices reducer stable
    recovered enough, recovered]

omit stable in
/-- **The pattern rule on one equation is kept** once its reading is kept and its first orientation
fires. -/
theorem tryEquation_kept {Γ : Context S.R} (type : TypeOver Γ) (equation : Equation (TotalTerm (extend Γ type)))
    (rest : EquationStore (TotalTerm (extend Γ type))) {budget : Nat}
    {reading : (scope : Spine equation.1.1) × (active : Active scope.target) ×'
      ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
        (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution}
    (viewed : viewEquation facts roots heads algebra declared choices reducer root budget equation = some reading)
    (viewKept : ∀ larger, budget ≤ larger →
      viewEquation facts roots heads algebra declared choices reducer root larger equation =
        viewEquation facts roots heads algebra declared choices reducer root budget equation)
    {found : Found (equation :: rest)}
    (fires : tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal budget
      type reading.1 reading.2.1 equation reading.2.2 rest = some found)
    (activeKept : ∀ larger, budget ≤ larger →
      tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal larger type
          reading.1 reading.2.1 equation reading.2.2 rest =
        tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal budget type
          reading.1 reading.2.1 equation reading.2.2 rest) :
    ∀ larger, budget ≤ larger →
      tryEquation rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal larger
          type equation rest = some found := by
  intro larger enough
  unfold tryEquation
  rw [viewKept larger enough, viewed]
  dsimp only
  rw [activeKept larger enough, fires]

omit stable in
/-- The search through a one-equation store is kept once its equation fires. -/
theorem searchStore_singleton_kept {Γ : Context S.R} (type : TypeOver Γ) (equation : Equation (TotalTerm (extend Γ type)))
    {budget : Nat} {found : Found [equation]}
    (fires : ∀ larger, budget ≤ larger →
      tryEquation rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal larger
        type equation [] = some found) :
    ∀ larger, budget ≤ larger →
      searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal larger
        type [equation] = some found := by
  intro larger enough
  simp only [searchStore]
  rw [fires larger enough]

omit stable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
theorem throughNewest_eq {Θ : Context S.R} (view : Newest Θ) (problem : EquationStore (TotalTerm Θ))
    (first second : (stored : EquationStore (TotalTerm (extend view.base view.type))) → Option (Found stored))
    (same : first (view.same ▸ problem) = second (view.same ▸ problem)) :
    throughNewest view problem first = throughNewest view problem second := by
  rcases view with ⟨base, type, equal⟩
  subst equal
  exact same

/-- The newest declaration, once read, is kept. -/
theorem newestOf_kept {Θ : Context S.R} {budget : Nat} {view : Newest Θ}
    (read : ContextualDependentWorklist.newestOf facts roots heads algebra declared choices reducer budget Θ = some view) :
    ∀ larger, budget ≤ larger →
      ContextualDependentWorklist.newestOf facts roots heads algebra declared choices reducer larger Θ = some view := by
  intro larger enough
  rcases Θ with ⟨arity, raw, formed⟩
  cases raw with
  | nil => cases read
  | snoc raw code =>
      simp only [ContextualDependentWorklist.newestOf] at read ⊢
      obtain ⟨checked, computed, returned⟩ := Option.bind_eq_some_iff.mp read
      exact Option.bind_eq_some_iff.mpr ⟨checked,
        ContextualDependentRecoveryBudget.formType_mono facts roots heads algebra declared choices reducer stable computed
          enough, returned⟩

/-- **The pattern rule is kept** once its newest declaration is read and its search is kept. -/
theorem patternRule_kept {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) {budget : Nat} {view : Newest Θ}
    (read : ContextualDependentWorklist.newestOf facts roots heads algebra declared choices reducer budget Θ = some view)
    {found : Found (view.same ▸ problem)}
    (searched : ∀ larger, budget ≤ larger →
      searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal larger
        view.type (view.same ▸ problem) = some found) :
    ∀ larger, budget ≤ larger →
      patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal larger
          problem =
        patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal budget
          problem := by
  intro larger enough
  unfold patternRule
  rw [newestOf_kept facts roots heads algebra declared choices reducer stable read larger enough, read]
  dsimp only
  apply throughNewest_eq
  rw [searched larger enough, searched budget le_rfl]

omit stable in
/-- The distinct-locals rule on a one-equation store is kept once its reading is kept. -/
theorem localsRule_singleton_kept {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) {budget : Nat}
    (viewKept : ∀ larger, budget ≤ larger →
      viewEquation facts roots heads algebra declared choices reducer root larger equation =
        viewEquation facts roots heads algebra declared choices reducer root budget equation) :
    ∀ larger, budget ≤ larger →
      ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared choices reducer
          root larger [equation] =
        ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared choices reducer
          root budget [equation] := by
  intro larger enough
  simp only [ContextualDependentRigidDecomposition.localsRule]
  unfold ContextualDependentRigidDecomposition.localsClash
  erw [viewKept larger enough]

end ContextualDependentDecisiveFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
