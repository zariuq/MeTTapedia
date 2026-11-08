import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveFragmentRules

/-!
# The prune rule is eventually constant

The prune rule recognizes a pattern for the newest metavariable, reads the older metavariable's
application, discovers its spine, deletes the binders outside the intersection, forms the pruned
type, discovers its spine, and runs the pattern search after exchanging. Spine discovery and type
formation keep their successful results, the pattern search is eventually constant, and every other
step is a reader that does not use the budget. So the prune rule, on one recognized pattern, on one
reading, on one equation in both orientations, through the store, and at the two newest
declarations, is **eventually constant on every store**.
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

/-- A sequence that agrees, from some budget on, with an eventually constant one is eventually
constant. -/
theorem EventuallyConst.of_eventually_eq {α : Sort*} {f g : Nat → α} (threshold : Nat)
    (same : ∀ fuel, threshold ≤ fuel → f fuel = g fuel) (constant : EventuallyConst g) : EventuallyConst f := by
  obtain ⟨t, kept⟩ := constant
  refine ⟨max threshold t, fun fuel enough => ?_⟩
  rw [same fuel (le_of_max_le_left enough), same _ (le_max_left _ _), kept fuel (le_of_max_le_right enough),
    kept _ (le_max_right _ _)]

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
variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))
include stable

set_option maxHeartbeats 1000000 in
/-- **The prune rule on one recognized pattern is eventually constant.** -/
theorem tryPrune_const {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    {scopeType : TypeOver (extend (extend Γ₀ older) newer)} (scope : Spine scopeType)
    (active : Active scope.target) (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer)))
    (spine : Spine newer) (recognized : Recognized spine scope active) :
    EventuallyConst fun fuel =>
      tryPrune rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel older newer scope active equation view rest spine recognized := by
  have discovering : ∀ (Γ : Context S.R) (count : Nat) (whole : TypeOver Γ), ∃ threshold, ∀ fuel, threshold ≤ fuel →
      ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel count whole =
        ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer threshold count
          whole :=
    fun _ count whole => (discover_const facts roots heads algebra declared choices reducer stable count whole).spec
  have forming : ∀ (Γ : Context S.R) (code : Tm Head Γ.arity), ∃ threshold, ∀ fuel, threshold ≤ fuel →
      ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ code =
        ContextualDependentPruning.formType facts roots heads algebra declared choices reducer threshold Γ code :=
    fun _ code => (formType_const facts roots heads algebra declared choices reducer stable code).spec
  have searching : ∀ (Γ : Context S.R) (type : TypeOver Γ) (store : EquationStore (TotalTerm (extend Γ type))),
      ∃ threshold, ∀ fuel, threshold ≤ fuel →
        searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal fuel
            type store =
          searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
            threshold type store :=
    fun _ type store => (searchStore_const rigid facts complete roots heads algebra declared choices reducer root
      normalizes certifyNormal stable type store).spec
  choose discoverAt discoverSame using discovering
  choose formAt formSame using forming
  choose searchAt searchSame using searching
  unfold tryPrune
  try dsimp only
  -- the older metavariable's application
  split
  · exact EventuallyConst.const _
  -- its spine
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [discoverSame _ _ _ fuel enough]) ?_
  split
  · exact EventuallyConst.const _
  -- its arguments as locals, and their positions
  split
  · exact EventuallyConst.const _
  split
  · exact EventuallyConst.const _
  -- distinct arguments, compatible binders, the same type, the same side
  split
  swap
  · exact EventuallyConst.const _
  split
  swap
  · exact EventuallyConst.const _
  try dsimp only
  split
  swap
  · exact EventuallyConst.const _
  split
  swap
  · exact EventuallyConst.const _
  try dsimp only
  -- the deleted binders
  split
  · exact EventuallyConst.const _
  -- the pruned type
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [formSame _ _ fuel enough]) ?_
  split
  · exact EventuallyConst.const _
  -- its spine, and the kept positions
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [discoverSame _ _ _ fuel enough]) ?_
  split
  · exact EventuallyConst.const _
  split
  · exact EventuallyConst.const _
  -- distinct kept positions, compatible binders, the same result, covering
  split
  swap
  · exact EventuallyConst.const _
  split
  swap
  · exact EventuallyConst.const _
  split
  swap
  · exact EventuallyConst.const _
  try dsimp only
  split
  swap
  · exact EventuallyConst.const _
  try dsimp only
  -- the pattern search after exchanging
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by erw [searchSame _ _ _ fuel enough]) ?_
  split <;> exact EventuallyConst.const _

/-- **The prune rule on one scoped reading is eventually constant.** -/
theorem pruneActive_const {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    {scopeType : TypeOver (extend (extend Γ₀ older) newer)} (scope : Spine scopeType)
    (active : Active scope.target) (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) :
    EventuallyConst fun fuel =>
      pruneActive rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel older newer scope active equation view rest := by
  cases read : readApplication active.left.code with
  | none =>
      refine ⟨0, fun fuel _ => ?_⟩
      dsimp only
      unfold pruneActive
      rw [read]
  | some found =>
      obtain ⟨headIndex, arguments⟩ := found
      obtain ⟨t₁, discovered⟩ := (discover_const facts roots heads algebra declared choices reducer stable
        arguments.length newer).spec
      cases spineFound : ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer
          t₁ arguments.length newer with
      | none =>
          refine ⟨t₁, fun fuel enough => ?_⟩
          dsimp only
          unfold pruneActive
          rw [read]
          dsimp only
          erw [discovered fuel enough, spineFound]
      | some spine =>
          cases recognized : recognize spine scope active with
          | none =>
              refine ⟨t₁, fun fuel enough => ?_⟩
              dsimp only
              unfold pruneActive
              rw [read]
              dsimp only
              erw [discovered fuel enough, spineFound]
              dsimp only
              rw [recognized]
          | some found =>
              obtain ⟨t₂, pruned⟩ := (tryPrune_const rigid facts complete roots heads algebra declared choices reducer
                root normalizes certifyNormal headTypingUnique stable older newer scope active equation view rest spine
                found).spec
              refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
              dsimp only
              unfold pruneActive
              rw [read]
              dsimp only
              erw [discovered fuel (le_of_max_le_left enough), spineFound, discovered _ (le_max_left _ _), spineFound]
              dsimp only
              rw [recognized]
              dsimp only
              erw [pruned fuel (le_of_max_le_right enough), pruned _ (le_max_right _ _)]

/-- **The prune rule on one store equation, in both orientations, is eventually constant.** -/
theorem pruneEquation_const {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) :
    EventuallyConst fun fuel =>
      pruneEquation rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel older newer equation rest := by
  obtain ⟨t₁, viewed⟩ := (viewEquation_const facts roots heads algebra declared choices reducer root stable
    equation).spec
  cases reading : viewEquation facts roots heads algebra declared choices reducer root t₁ equation with
  | none =>
      refine ⟨t₁, fun fuel enough => ?_⟩
      dsimp only
      unfold pruneEquation
      erw [viewed fuel enough, reading]
  | some found =>
      obtain ⟨scope, active, view⟩ := found
      obtain ⟨t₂, first⟩ := (pruneActive_const rigid facts complete roots heads algebra declared choices reducer root
        normalizes certifyNormal headTypingUnique stable older newer scope active equation view rest).spec
      obtain ⟨t₃, second⟩ := (pruneActive_const rigid facts complete roots heads algebra declared choices reducer root
        normalizes certifyNormal headTypingUnique stable older newer scope ⟨active.type, active.right, active.left⟩
        equation (fun solution => (view solution).trans (toScoped_swap scope active solution).symm) rest).spec
      refine ⟨max t₁ (max t₂ t₃), fun fuel enough => ?_⟩
      have e₁ : t₁ ≤ fuel := by omega
      have e₂ : t₂ ≤ fuel := by omega
      have e₃ : t₃ ≤ fuel := by omega
      have f₁ : t₁ ≤ max t₁ (max t₂ t₃) := by omega
      have f₂ : t₂ ≤ max t₁ (max t₂ t₃) := by omega
      have f₃ : t₃ ≤ max t₁ (max t₂ t₃) := by omega
      dsimp only
      unfold pruneEquation
      erw [viewed fuel e₁, reading, viewed _ f₁, reading]
      dsimp only
      erw [first fuel e₂, first _ f₂, second fuel e₃, second _ f₃]

/-- **The prune search through the store is eventually constant.** -/
theorem pruneSearch_const {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older)) :
    ∀ problem : EquationStore (TotalTerm (extend (extend Γ₀ older) newer)), EventuallyConst fun fuel =>
      pruneSearch rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel older newer problem
  | [] => ⟨0, fun _ _ => rfl⟩
  | equation :: rest => by
      obtain ⟨t₁, first⟩ := (pruneEquation_const rigid facts complete roots heads algebra declared choices reducer root
        normalizes certifyNormal headTypingUnique stable older newer equation rest).spec
      obtain ⟨t₂, later⟩ := (pruneSearch_const older newer rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      simp only [pruneSearch]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

/-- **The prune rule is eventually constant on every store.** -/
theorem pruneRule_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      pruneRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel problem := by
  obtain ⟨t₁, outerSame⟩ := (newestOf_const facts roots heads algebra declared choices reducer stable Θ).spec
  cases outer : newestOf facts roots heads algebra declared choices reducer t₁ Θ with
  | none =>
      refine ⟨t₁, fun fuel enough => ?_⟩
      dsimp only
      unfold pruneRule
      erw [outerSame fuel enough, outer]
  | some outerView =>
      obtain ⟨t₂, innerSame⟩ := (newestOf_const facts roots heads algebra declared choices reducer stable
        outerView.base).spec
      cases inner : newestOf facts roots heads algebra declared choices reducer t₂ outerView.base with
      | none =>
          refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
          dsimp only
          unfold pruneRule
          erw [outerSame fuel (le_of_max_le_left enough), outer, outerSame _ (le_max_left _ _), outer]
          dsimp only
          erw [innerSame fuel (le_of_max_le_right enough), inner, innerSame _ (le_max_right _ _), inner]
      | some innerView =>
          obtain ⟨t₃, through⟩ := (throughTwo_const outerView innerView problem
            (fun fuel {_} older newer stored => pruneSearch rigid facts complete roots heads algebra declared choices
              reducer root normalizes certifyNormal headTypingUnique fuel older newer stored)
            (fun older newer stored => pruneSearch_const rigid facts complete roots heads algebra declared choices
              reducer root normalizes certifyNormal headTypingUnique stable older newer stored)).spec
          refine ⟨max t₁ (max t₂ t₃), fun fuel enough => ?_⟩
          have e₁ : t₁ ≤ fuel := by omega
          have e₂ : t₂ ≤ fuel := by omega
          have e₃ : t₃ ≤ fuel := by omega
          dsimp only
          unfold pruneRule
          erw [outerSame fuel e₁, outer, outerSame _ (by omega), outer]
          dsimp only
          erw [innerSame fuel e₂, inner, innerSame _ (by omega), inner]
          dsimp only
          exact (through fuel e₃).trans (through _ (by omega)).symm

end ContextualDependentDecisiveFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
