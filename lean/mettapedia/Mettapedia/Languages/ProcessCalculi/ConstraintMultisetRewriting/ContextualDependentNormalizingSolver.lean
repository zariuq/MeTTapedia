import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidDecomposition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentContextNormalizationTower
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalizingCertify
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveDriver

/-!
# A solver that normalizes annotations before spine discovery and type formation

Spine discovery reads Π binders syntactically, and synthesis has no rule for an introduction at a
synthesis position, so an annotation or a declaration carrying a redex (`fst (pair a b)`, a
β-redex) blocks the pattern, prune and exchange rules at every budget. Instantiation can create such
redexes. The **normalizing round** therefore first prepares the store:

* every declaration of the context is normalized, through the typed comparison of telescopes;
* every annotation and every side of every equation is normalized;

each by an update with exactly the original solutions, and an unfinished run keeps its input. It
then runs the rigid round on the prepared store. The rank is unchanged by preparation, so the
composite is again a worklist solver, and the driver's guarantees hold for it.

In the cumulative tower, for every store there is a budget from which the prepared context and
every annotation and side of the prepared store are normal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentNormalizing

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Preparation -/

section Preparation

variable (root : ExecutableReduction.RootEvaluator S.R)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)
  (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)

/-- Normalize the declarations of the context, when the run finishes. -/
def contextStep (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Update S.levels problem :=
  match ContextualDependentContextNormalization.normalize root rootComplete facts roots heads fuel Θ.raw Θ.formed with
  | none => Update.pending S.levels problem
  | some normalized => normalized.update problem

/-- **Preparation**: normalize the context's declarations, then every annotation and side of the
store. -/
def prepare (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Update S.levels problem :=
  (contextStep root rootComplete facts roots heads fuel problem).then
    (ContextualDependentNormalization.update root facts roots heads fuel
      (contextStep root rootComplete facts roots heads fuel problem).remaining)

theorem contextStep_size (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    size (contextStep root rootComplete facts roots heads fuel problem).remaining = size problem := by
  unfold contextStep
  split
  · rfl
  · simp only [size, ContextualDependentContextNormalization.Normalized.update, Frames.applyStore, List.length_map]
    rfl

/-- **Preparation keeps the rank.** -/
theorem prepare_size (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    size (prepare root rootComplete facts roots heads fuel problem).remaining = size problem := by
  have context := contextStep_size root rootComplete facts roots heads fuel problem
  simp only [size] at context ⊢
  change ((contextStep root rootComplete facts roots heads fuel problem).target.arity,
    (ContextualDependentNormalization.storeAt root facts roots heads fuel
      (contextStep root rootComplete facts roots heads fuel problem).remaining).length) = _
  rw [ContextualDependentNormalization.storeAt_length]
  exact context

/-- The prepared context is the normalized context when context normalization finishes. -/
theorem prepare_target (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    {normalized : ContextualDependentContextNormalization.Normalized (S := S) Θ.raw}
    (finished : ContextualDependentContextNormalization.normalize root rootComplete facts roots heads fuel Θ.raw
      Θ.formed = some normalized) :
    (prepare root rootComplete facts roots heads fuel problem).target = normalized.context := by
  change (contextStep root rootComplete facts roots heads fuel problem).target = _
  unfold contextStep
  rw [finished]
  rfl

/-- The prepared store is the normalization of the transported store. -/
theorem prepare_remaining (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    (prepare root rootComplete facts roots heads fuel problem).remaining =
      ContextualDependentNormalization.storeAt root facts roots heads fuel
        (contextStep root rootComplete facts roots heads fuel problem).remaining := rfl


/-- Two normalizations of one telescope with the same declarations are the same. -/
theorem normalized_ext {n : Nat} {original : Ctx Head n}
    {first second : ContextualDependentContextNormalization.Normalized (S := S) original}
    (same : first.raw = second.raw) : first = second := by
  cases first
  cases second
  cases same
  rfl

/-- **Context normalization keeps a finished result** at the next budget. -/
theorem contextNormalize_succ (fuel : Nat) {n : Nat} (raw : Ctx Head n) :
    ∀ (formed : CtxFormed S.R raw) (result : ContextualDependentContextNormalization.Normalized (S := S) raw),
      ContextualDependentContextNormalization.normalize root rootComplete facts roots heads fuel raw formed =
          some result →
        ContextualDependentContextNormalization.normalize root rootComplete facts roots heads (fuel + 1) raw formed =
          some result := by
  induction raw with
  | nil =>
      intro formed result computed
      simpa only [ContextualDependentContextNormalization.normalize] using computed
  | snoc raw type ih =>
      intro formed result computed
      simp only [ContextualDependentContextNormalization.normalize] at computed ⊢
      split at computed
      · cases computed
      · rename_i prior priorRun
        rw [ih _ prior priorRun]
        dsimp only
        split at computed
        · cases computed
        · rename_i reduced reducedRun
          have reducedRun' := ContextualDependentReductionBudget.success_succ S.R root reducedRun
          split
          · rename_i missing
            rw [reducedRun'] at missing
            cases missing
          · rename_i reduced' reducedRun''
            rw [reducedRun'] at reducedRun''
            obtain rfl := Option.some.inj reducedRun''
            exact computed

/-- Context normalization keeps a finished result at every larger budget. -/
theorem contextNormalize_mono {fuel larger : Nat} {n : Nat} {raw : Ctx Head n} {formed : CtxFormed S.R raw}
    {result : ContextualDependentContextNormalization.Normalized (S := S) raw}
    (computed : ContextualDependentContextNormalization.normalize root rootComplete facts roots heads fuel raw formed =
      some result) (enough : fuel ≤ larger) :
    ContextualDependentContextNormalization.normalize root rootComplete facts roots heads larger raw formed =
      some result := by
  induction enough with
  | refl => exact computed
  | step _ ih => exact contextNormalize_succ root rootComplete facts roots heads _ raw formed result ih

/-- With a finished context normalization, preparation is that transport followed by store
normalization. -/
theorem prepare_eq (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    {normalized : ContextualDependentContextNormalization.Normalized (S := S) Θ.raw}
    (finished : ContextualDependentContextNormalization.normalize root rootComplete facts roots heads fuel Θ.raw
      Θ.formed = some normalized) :
    prepare root rootComplete facts roots heads fuel problem =
      (normalized.update problem).then
        (ContextualDependentNormalization.update root facts roots heads fuel (normalized.update problem).remaining) := by
  have step : contextStep root rootComplete facts roots heads fuel problem = normalized.update problem := by
    unfold contextStep
    rw [finished]
  unfold prepare
  rw [step]

end Preparation

/-! ## The normalizing round -/

section Round

variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
  (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-- **One normalizing round**: prepare the store, then run the rigid round on the prepared store. -/
def normalizingRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels size problem :=
  match ContextualDependentRigidDecomposition.rigidRound rigid complete facts roots heads algebra declared choices
      reducer root normalizes certifyNormal headTypingUnique fuel
      (prepare root rootComplete facts roots heads fuel problem).remaining with
  | .progress update smaller =>
      .progress ((prepare root rootComplete facts roots heads fuel problem).then update)
        (by rw [prepare_size] at smaller; exact smaller)
  | .refuted absent =>
      .refuted fun solvable => absent ((prepare root rootComplete facts roots heads fuel problem).solvable_iff.mp solvable)
  | .stuck => .stuck

/-- **The normalizing solver** at one budget. -/
def normalizingSolver (fuel : Nat) : Solver S.levels where
  rank := size
  round := normalizingRound rigid complete facts roots heads algebra declared choices reducer root rootComplete
    normalizes certifyNormal headTypingUnique fuel

/-- **The normalizing solver as a fuel-indexed family**, for the joint-budget driver. -/
def family : ContextualDependentDecisiveDriver.Family S.levels where
  rank := size
  round fuel := normalizingRound rigid complete facts roots heads algebra declared choices reducer root rootComplete
    normalizes certifyNormal headTypingUnique fuel

/-- **Every refutation of the normalizing round is a refutation of the prepared store** by the rigid
round, which is certified. -/
theorem normalizingRound_refuted {fuel : Nat} {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {absent : ¬ (frames S.levels).Solvable problem}
    (refuted : normalizingRound rigid complete facts roots heads algebra declared choices reducer root rootComplete
      normalizes certifyNormal headTypingUnique fuel problem = .refuted absent) :
    ∃ absent', ContextualDependentRigidDecomposition.rigidRound rigid complete facts roots heads algebra declared choices
      reducer root normalizes certifyNormal headTypingUnique fuel
      (prepare root rootComplete facts roots heads fuel problem).remaining = .refuted absent' := by
  unfold normalizingRound at refuted
  split at refuted
  · cases refuted
  · rename_i absent' computed
    exact ⟨absent', computed⟩
  · cases refuted

/-- The normalizing round makes progress, refutes or is stuck exactly when the rigid round does on
the prepared store. -/
theorem normalizingRound_stuck_iff {fuel : Nat} {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    normalizingRound rigid complete facts roots heads algebra declared choices reducer root rootComplete
        normalizes certifyNormal headTypingUnique fuel problem = .stuck ↔
      ContextualDependentRigidDecomposition.rigidRound rigid complete facts roots heads algebra declared choices
        reducer root normalizes certifyNormal headTypingUnique fuel
        (prepare root rootComplete facts roots heads fuel problem).remaining = .stuck := by
  unfold normalizingRound
  split <;> simp_all

end Round

/-! ## Normal preparation in the tower -/

section Tower

variable {L : Type} [UniverseLevel.LevelOrder L] (valuation : Nat → L)

/-- The root-free evaluator of the tower proposes no root step, and the tower has none. -/
theorem tower_rootComplete :
    ∀ {n : Nat} (term : Tm (LevelTower.Head L) n), (fun _ => none : ExecutableReduction.RootEvaluator
      (TowerModel.setting valuation).R) term = none →
      ∀ target, ¬ (TowerModel.setting valuation).R.computation.step term target :=
  fun _ _ _ impossible => impossible.elim

/-- **Eventually, preparation normalizes the context**: from some budget on, the prepared store
lives over a context whose every declaration is normal. -/
theorem prepared_context_normal {Θ : Context (TowerModel.setting valuation).R}
    (problem : EquationStore (TotalTerm Θ)) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      ContextualDependentNormalSelection.NormalContext (S := TowerModel.setting valuation)
        (prepare (S := TowerModel.setting valuation) (fun _ => none) (tower_rootComplete valuation) TowerModel.facts
          TowerModel.roots TowerModel.heads larger problem).target.raw := by
  obtain ⟨fuel, finishes⟩ := ContextualDependentContextNormalizationTower.context_eventually_normalizes valuation Θ
  refine ⟨fuel, fun larger enough => ?_⟩
  obtain ⟨normalized, computed⟩ := Option.isSome_iff_exists.mp (finishes larger enough)
  rw [prepare_target (S := TowerModel.setting valuation) (fun _ => none) (tower_rootComplete valuation)
    TowerModel.facts TowerModel.roots TowerModel.heads larger problem computed]
  exact normalized.normal

/-- On a typed term the tower's normalizer eventually finishes, and keeps finishing. -/
theorem reduceTerm_eventually {Γ : Context (TowerModel.setting valuation).R} (original : TotalTerm Γ) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      (ContextualDependentNormalization.reduceTerm (S := TowerModel.setting valuation) (fun _ => none)
        TowerModel.facts TowerModel.roots TowerModel.heads larger original).isSome = true := by
  obtain ⟨f₁, _, _, stable₁⟩ := ContextualDependentTowerBudget.typed_eventually_stable Γ.formed original.1.formed
  obtain ⟨f₂, _, _, stable₂⟩ := ContextualDependentTowerBudget.typed_eventually_stable Γ.formed original.2.typed
  refine ⟨max f₁ f₂, fun larger enough => ?_⟩
  refine (ContextualDependentNormalization.reduceTerm_success_iff (S := TowerModel.setting valuation) (fun _ => none)
    TowerModel.facts TowerModel.roots TowerModel.heads larger original).mpr ⟨?_, ?_⟩
  · change (ContextualDependentTowerBudget.reducer larger original.1.code).isSome = true
    rw [stable₁ larger ((Nat.le_max_left _ _).trans enough)]
    rfl
  · change (ContextualDependentTowerBudget.reducer larger original.2.code).isSome = true
    rw [stable₂ larger ((Nat.le_max_right _ _).trans enough)]
    rfl

/-- Equations whose annotations and sides are normal. -/
def NormalEquation {Γ : Context (TowerModel.setting valuation).R} (equation : Equation (TotalTerm Γ)) : Prop :=
  ContextualDependentNormalChecking.Normal (S := TowerModel.setting valuation) equation.1.1.code ∧
  ContextualDependentNormalChecking.Normal (S := TowerModel.setting valuation) equation.1.2.code ∧
  ContextualDependentNormalChecking.Normal (S := TowerModel.setting valuation) equation.2.1.code ∧
  ContextualDependentNormalChecking.Normal (S := TowerModel.setting valuation) equation.2.2.code

/-- **Eventually, store normalization normalizes every annotation and side** of a store. -/
theorem storeAt_normal_eventually {Γ : Context (TowerModel.setting valuation).R} :
    ∀ problem : EquationStore (TotalTerm Γ), ∃ fuel, ∀ larger, fuel ≤ larger →
      ∀ equation ∈ ContextualDependentNormalization.storeAt (S := TowerModel.setting valuation) (fun _ => none)
        TowerModel.facts TowerModel.roots TowerModel.heads larger problem, NormalEquation valuation equation
  | [] => ⟨0, fun _ _ _ member => absurd member List.not_mem_nil⟩
  | equation :: rest => by
      obtain ⟨f₀, restNormal⟩ := storeAt_normal_eventually rest
      obtain ⟨f₁, leftFinishes⟩ := reduceTerm_eventually valuation equation.1
      obtain ⟨f₂, rightFinishes⟩ := reduceTerm_eventually valuation equation.2
      refine ⟨max f₀ (max f₁ f₂), fun larger enough other member => ?_⟩
      rcases List.mem_cons.mp member with rfl | later
      · have left := ContextualDependentNormalization.termAt_normal_of_success (S := TowerModel.setting valuation)
          (fun _ => none) TowerModel.facts TowerModel.roots TowerModel.heads (tower_rootComplete valuation) equation.1
          (leftFinishes larger (by omega))
        have right := ContextualDependentNormalization.termAt_normal_of_success (S := TowerModel.setting valuation)
          (fun _ => none) TowerModel.facts TowerModel.roots TowerModel.heads (tower_rootComplete valuation) equation.2
          (rightFinishes larger (by omega))
        exact ⟨left.1, left.2, right.1, right.2⟩
      · exact restNormal larger (by omega) other later

/-- **Eventually, the prepared store has normal annotations and sides over a normal context**: from
some budget on, spine discovery and type formation in the normalizing round read only normal codes. -/
theorem prepared_normal {Θ : Context (TowerModel.setting valuation).R} (problem : EquationStore (TotalTerm Θ)) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      ContextualDependentNormalSelection.NormalContext (S := TowerModel.setting valuation)
        (prepare (S := TowerModel.setting valuation) (fun _ => none) (tower_rootComplete valuation) TowerModel.facts
          TowerModel.roots TowerModel.heads larger problem).target.raw ∧
      ∀ equation ∈ (prepare (S := TowerModel.setting valuation) (fun _ => none) (tower_rootComplete valuation)
          TowerModel.facts TowerModel.roots TowerModel.heads larger problem).remaining,
        NormalEquation valuation equation := by
  obtain ⟨f₁, finishes⟩ := ContextualDependentContextNormalizationTower.context_eventually_normalizes valuation Θ
  obtain ⟨normalized, computed⟩ := Option.isSome_iff_exists.mp (finishes f₁ le_rfl)
  obtain ⟨f₂, storeNormal⟩ := storeAt_normal_eventually valuation (normalized.update problem).remaining
  refine ⟨max f₁ f₂, fun larger enough => ?_⟩
  have stable := contextNormalize_mono (S := TowerModel.setting valuation) (fun _ => none) (tower_rootComplete valuation)
    TowerModel.facts TowerModel.roots TowerModel.heads computed (le_of_max_le_left enough)
  rw [prepare_eq (S := TowerModel.setting valuation) (fun _ => none) (tower_rootComplete valuation) TowerModel.facts
    TowerModel.roots TowerModel.heads larger problem stable]
  exact ⟨normalized.normal, storeNormal larger (le_of_max_le_right enough)⟩

end Tower

end ContextualDependentNormalizing
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
