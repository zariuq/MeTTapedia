import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveFragmentEventual
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveDriver

/-!
# The pattern rule is eventually constant, and settles wherever it fires

On every store, at every budget large enough, the general pattern step, the pattern rule on one
equation in both orientations, the search through the store, and the pattern rule at the newest
declaration all return the same result, success or failure: each is built from eventually constant
executables and budget-free readers (`recognize`, the occurs check, the refutation test).

Consequently the rigid round **settles**, in the sense of `Settled`, on every class of stores on
which, at each nonempty store, the distinct-locals rule or the pattern rule eventually fires, and
on which a progressing round stays in the class. What remains to settle a store-defined class is
that the pattern rule fires on it, which is a statement about recognition, and that the class is
closed under the answer.
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
open ContextualDependentUpdate

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

section Rule

include stable

/-- **The general pattern step is eventually constant.** -/
theorem step_const {Γ : Context S.R} {type : TypeOver Γ} {spine : Spine type} {scopeType : TypeOver (extend Γ type)}
    {scope : Spine scopeType} (pattern : Pattern spine scope)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom)) :
    EventuallyConst fun fuel =>
      Pattern.step facts roots heads algebra declared (ContextualDependentScopeConsequence.root_reflection rigid)
        complete rigid normalizes certifyNormal choices reducer fuel pattern right := by
  obtain ⟨threshold, same⟩ := (recover_const facts roots heads algebra declared choices reducer stable
    pattern.bodyInclusion spine.result right.code).spec
  refine ⟨threshold, fun fuel enough => ?_⟩
  dsimp only
  unfold Pattern.step
  erw [same fuel enough]

/-- **The pattern rule on one scoped reading is eventually constant.** -/
theorem tryActive_const {Γ : Context S.R} (type : TypeOver Γ) {scopeType : TypeOver (extend Γ type)}
    (scope : Spine scopeType) (active : Active scope.target) (equation : Equation (TotalTerm (extend Γ type)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ type))) :
    EventuallyConst fun fuel =>
      tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal fuel type
        scope active equation view rest := by
  cases read : readApplication active.left.code with
  | none =>
      refine ⟨0, fun fuel _ => ?_⟩
      dsimp only
      unfold tryActive
      rw [read]
  | some found =>
      obtain ⟨headIndex, arguments⟩ := found
      obtain ⟨t₁, discovered⟩ := (discover_const facts roots heads algebra declared choices reducer stable
        arguments.length type).spec
      cases spineFound : ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer
          t₁ arguments.length type with
      | none =>
          refine ⟨t₁, fun fuel enough => ?_⟩
          dsimp only
          unfold tryActive
          rw [read]
          dsimp only
          erw [discovered fuel enough, spineFound]
      | some spine =>
          cases recognized : recognize spine scope active with
          | none =>
              refine ⟨t₁, fun fuel enough => ?_⟩
              dsimp only
              unfold tryActive
              rw [read]
              dsimp only
              erw [discovered fuel enough, spineFound]
              dsimp only
              rw [recognized]
          | some found =>
              obtain ⟨t₂, stepped⟩ := (step_const rigid facts complete roots heads algebra declared choices reducer
                normalizes certifyNormal stable found.pattern found.right).spec
              refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
              dsimp only
              unfold tryActive
              rw [read]
              dsimp only
              erw [discovered fuel (le_of_max_le_left enough), spineFound, discovered _ (le_max_left _ _), spineFound]
              dsimp only
              rw [recognized]
              dsimp only
              erw [stepped fuel (le_of_max_le_right enough), stepped _ (le_max_right _ _)]

/-- **The pattern rule on one store equation, in both orientations, is eventually constant.** -/
theorem tryEquation_const {Γ : Context S.R} (type : TypeOver Γ) (equation : Equation (TotalTerm (extend Γ type)))
    (rest : EquationStore (TotalTerm (extend Γ type))) :
    EventuallyConst fun fuel =>
      tryEquation rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal fuel
        type equation rest := by
  obtain ⟨t₁, viewed⟩ := (viewEquation_const facts roots heads algebra declared choices reducer root stable
    equation).spec
  cases reading : viewEquation facts roots heads algebra declared choices reducer root t₁ equation with
  | none =>
      refine ⟨t₁, fun fuel enough => ?_⟩
      dsimp only
      unfold tryEquation
      erw [viewed fuel enough, reading]
  | some found =>
      obtain ⟨scope, active, view⟩ := found
      obtain ⟨t₂, first⟩ := (tryActive_const rigid facts complete roots heads algebra declared choices reducer
        normalizes certifyNormal stable type scope active equation view rest).spec
      obtain ⟨t₃, second⟩ := (tryActive_const rigid facts complete roots heads algebra declared choices reducer
        normalizes certifyNormal stable type scope ⟨active.type, active.right, active.left⟩ equation
        (fun solution => (view solution).trans (toScoped_swap scope active solution).symm) rest).spec
      refine ⟨max t₁ (max t₂ t₃), fun fuel enough => ?_⟩
      have e₁ : t₁ ≤ fuel := by omega
      have e₂ : t₂ ≤ fuel := by omega
      have e₃ : t₃ ≤ fuel := by omega
      have f₁ : t₁ ≤ max t₁ (max t₂ t₃) := by omega
      have f₂ : t₂ ≤ max t₁ (max t₂ t₃) := by omega
      have f₃ : t₃ ≤ max t₁ (max t₂ t₃) := by omega
      dsimp only
      unfold tryEquation
      erw [viewed fuel e₁, reading, viewed _ f₁, reading]
      dsimp only
      erw [first fuel e₂, first _ f₂, second fuel e₃, second _ f₃]

/-- **The search through the store is eventually constant.** -/
theorem searchStore_const {Γ : Context S.R} (type : TypeOver Γ) :
    ∀ problem : EquationStore (TotalTerm (extend Γ type)), EventuallyConst fun fuel =>
      searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal fuel
        type problem
  | [] => ⟨0, fun _ _ => rfl⟩
  | equation :: rest => by
      obtain ⟨t₁, first⟩ := (tryEquation_const rigid facts complete roots heads algebra declared choices reducer root
        normalizes certifyNormal stable type equation rest).spec
      obtain ⟨t₂, later⟩ := (searchStore_const type rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      simp only [searchStore]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

omit stable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
theorem throughNewest_const {Θ : Context S.R} (view : Newest Θ) (problem : EquationStore (TotalTerm Θ))
    (solve : Nat → (stored : EquationStore (TotalTerm (extend view.base view.type))) → Option (Found stored))
    (constant : ∀ stored, EventuallyConst fun fuel => solve fuel stored) :
    EventuallyConst fun fuel => throughNewest view problem (solve fuel) := by
  rcases view with ⟨base, type, same⟩
  subst same
  exact constant problem

/-- **The pattern rule is eventually constant on every store.** -/
theorem patternRule_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal fuel
        problem := by
  obtain ⟨t₁, newest⟩ := (newestOf_const facts roots heads algebra declared choices reducer stable Θ).spec
  cases found : newestOf facts roots heads algebra declared choices reducer t₁ Θ with
  | none =>
      refine ⟨t₁, fun fuel enough => ?_⟩
      dsimp only
      unfold patternRule
      erw [newest fuel enough, found]
  | some view =>
      obtain ⟨t₂, searched⟩ := (throughNewest_const view problem (fun fuel => searchStore rigid facts complete roots heads
        algebra declared choices reducer root normalizes certifyNormal fuel view.type)
        (searchStore_const rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          stable view.type)).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      unfold patternRule
      erw [newest fuel (le_of_max_le_left enough), found, newest _ (le_max_left _ _), found]
      dsimp only
      exact (searched fuel (le_of_max_le_right enough)).trans (searched _ (le_max_right _ _)).symm

end Rule

/-! ## Settling the rigid round wherever the locals or pattern rule fires -/

section Settle

variable (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-- The rigid round at every budget, as a fuel-indexed family. -/
def rigidFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := size
  round fuel := ContextualDependentRigidDecomposition.rigidRound rigid complete facts roots heads algebra declared
    choices reducer root normalizes certifyNormal headTypingUnique fuel

/-- **The rigid round settles wherever the distinct-locals rule or the pattern rule fires.** Let a
class of stores be given such that at every nonempty store of it, from some budget on, either the
distinct-locals rule fires, or it does not and the pattern rule fires with every solved answer staying
in the class. Then the rigid round settles on the class: eventually the same round at every larger
budget, not stuck, and staying in the class. -/
def settledWhereFiring (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        (ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared choices
          reducer root larger problem).isSome ∨
        (ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared choices
            reducer root larger problem = none ∧
          (patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
            larger problem).isSome ∧
          ∀ {update : Update S.levels problem} {smaller : update.target.arity < Γ.arity},
            patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
              larger problem = some (.solved update smaller) → holds update.remaining)) :
    ContextualDependentDecisiveDriver.Settled
      (rigidFamily rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        headTypingUnique) where
  holds := holds
  settles := by
    intro Γ problem inside nonempty
    obtain ⟨t₁, localsSame⟩ := (localsRule_const facts roots heads algebra declared choices reducer root stable rigid
      complete problem).spec
    obtain ⟨t₂, patternSame⟩ := (patternRule_const rigid facts complete roots heads algebra declared choices reducer root
      normalizes certifyNormal stable problem).spec
    obtain ⟨bound, firing⟩ := eventual inside nonempty
    let threshold := max bound (max t₁ t₂)
    have localsAt : ∀ larger, threshold ≤ larger →
        ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared choices reducer
          root larger problem =
        ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared choices reducer
          root threshold problem := fun larger enough =>
      (localsSame larger (by omega)).trans (localsSame threshold (by omega)).symm
    have patternAt : ∀ larger, threshold ≤ larger →
        patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal larger
          problem =
        patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          threshold problem := fun larger enough =>
      (patternSame larger (by omega)).trans (patternSame threshold (by omega)).symm
    have firingAt := firing threshold (le_max_left _ _)
    have roundAt : ∀ larger, threshold ≤ larger →
        (rigidFamily rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique).round larger problem =
        (rigidFamily rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique).round threshold problem := by
      intro larger enough
      change ContextualDependentRigidDecomposition.rigidRound rigid complete facts roots heads algebra declared choices
          reducer root normalizes certifyNormal headTypingUnique larger problem =
        ContextualDependentRigidDecomposition.rigidRound rigid complete facts roots heads algebra declared choices
          reducer root normalizes certifyNormal headTypingUnique threshold problem
      unfold ContextualDependentRigidDecomposition.rigidRound
      rw [localsAt larger enough]
      cases locals : ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared
          choices reducer root threshold problem with
      | some absent => rfl
      | none =>
          dsimp only
          unfold fullRound
          rw [patternAt larger enough]
          rcases firingAt with fired | ⟨_, fired, _⟩
          · rw [locals] at fired; cases fired
          · cases pattern : patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes
                certifyNormal threshold problem with
            | none => rw [pattern] at fired; cases fired
            | some found => cases found <;> rfl
    refine ⟨threshold, ?_, roundAt, ?_⟩
    · change ContextualDependentRigidDecomposition.rigidRound rigid complete facts roots heads algebra declared choices
          reducer root normalizes certifyNormal headTypingUnique threshold problem ≠ .stuck
      unfold ContextualDependentRigidDecomposition.rigidRound
      cases locals : ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared
          choices reducer root threshold problem with
      | some absent => intro impossible; cases impossible
      | none =>
          dsimp only
          unfold fullRound
          rcases firingAt with fired | ⟨_, fired, _⟩
          · rw [locals] at fired; cases fired
          · cases pattern : patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes
                certifyNormal threshold problem with
            | none => rw [pattern] at fired; cases fired
            | some found => cases found <;> (intro impossible; cases impossible)
    · intro update smaller progressed
      change ContextualDependentRigidDecomposition.rigidRound rigid complete facts roots heads algebra declared choices
          reducer root normalizes certifyNormal headTypingUnique threshold problem = .progress update smaller at progressed
      unfold ContextualDependentRigidDecomposition.rigidRound at progressed
      cases locals : ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared
          choices reducer root threshold problem with
      | some absent => rw [locals] at progressed; cases progressed
      | none =>
          rw [locals] at progressed
          dsimp only at progressed
          unfold fullRound at progressed
          rcases firingAt with fired | ⟨_, fired, closed⟩
          · rw [locals] at fired; cases fired
          · cases pattern : patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes
                certifyNormal threshold problem with
            | none => rw [pattern] at fired; cases fired
            | some found =>
                cases found with
                | solved solved smaller' =>
                    rw [pattern] at progressed
                    cases progressed
                    exact closed pattern
                | refuted absent => rw [pattern] at progressed; cases progressed

end Settle

end ContextualDependentDecisiveFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
