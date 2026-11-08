import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidDecomposition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRecoveryBudget

/-!
# Eventual constancy of the solver's executables

`Settled` asks the round to be eventually the same at every larger budget. A failed executable
call matters as much as a successful one: a round that falls through one rule at a small budget may
take that rule at a larger one. This module proves **eventual constancy**, success and failure alike,
for every input, of the executables and readings the rules are built from:

* every executable whose successful results are kept at larger budgets is eventually constant
  (either it succeeds at some budget and keeps that result, or it never succeeds);
* type formation, recovery, annotation comparison and spine discovery are kept, hence eventually
  constant;
* bounded normalization of an endpoint returns the endpoint until the normalizer finishes, and the
  normal form after: eventually constant;
* the scoped reading of a store equation and the distinct-locals rule are eventually constant on
  every equation and every store.

No normality, typing or fragment condition is assumed: these hold on every input, for every reducer
whose successful runs are kept.
-/

set_option autoImplicit false

universe u

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDecisiveFragment

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentConversionBudget

/-! ## Eventually constant sequences -/

/-- **Eventually constant**: the same value at every budget from some budget on. -/
def EventuallyConst {α : Sort u} (f : Nat → α) : Prop := ∃ threshold, ∀ fuel, threshold ≤ fuel → f fuel = f threshold

theorem EventuallyConst.const {α : Sort u} (a : α) : EventuallyConst fun _ : Nat => a := ⟨0, fun _ _ => rfl⟩

/-- The defining property, with the sequence applied. -/
theorem EventuallyConst.spec {α : Sort u} {f : Nat → α} (constant : EventuallyConst f) :
    ∃ threshold, ∀ fuel, threshold ≤ fuel → f fuel = f threshold := constant

/-- From some budget on, two eventually constant sequences are both constant. -/
theorem EventuallyConst.later {α : Sort u} {f : Nat → α} (constant : EventuallyConst f) :
    ∃ threshold, ∀ fuel larger, threshold ≤ fuel → threshold ≤ larger → f fuel = f larger := by
  obtain ⟨threshold, same⟩ := constant
  exact ⟨threshold, fun fuel larger h₁ h₂ => (same fuel h₁).trans (same larger h₂).symm⟩

/-- **Kept results are eventually constant**: a partial computation whose successful results are
kept at every larger budget either succeeds at some budget and keeps that result, or never
succeeds. -/
theorem EventuallyConst.of_mono {α : Type u} {f : Nat → Option α}
    (mono : ∀ {fuel larger : Nat} {result : α}, f fuel = some result → fuel ≤ larger → f larger = some result) :
    EventuallyConst f := by
  by_cases succeeds : ∃ fuel, (f fuel).isSome
  · obtain ⟨fuel, found⟩ := succeeds
    obtain ⟨result, computed⟩ := Option.isSome_iff_exists.mp found
    exact ⟨fuel, fun larger enough => (mono computed enough).trans computed.symm⟩
  · refine ⟨0, fun fuel _ => ?_⟩
    have never : ∀ budget, f budget = none := fun budget => by
      cases computed : f budget with
      | none => rfl
      | some _ => exact absurd ⟨budget, by rw [computed]; rfl⟩ succeeds
    rw [never fuel, never 0]

/-! ## The executables -/

section Executables

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
variable (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))
include stable

omit [DecidableRel S.R.cumulative] in
theorem types_mono {n fuel larger : Nat} {Γ : Ctx Head n} {first second : Tm Head n}
    {result : ExecutableConversion.Certificate S.R (.types Γ first second)}
    (accepted : ExecutableConversion.types S.R reducer fuel Γ first second = some result) (enough : fuel ≤ larger) :
    ExecutableConversion.types S.R reducer larger Γ first second = some result := by
  induction enough with
  | refl => exact accepted
  | @step larger _ ih => exact (all_success_succ S.R reducer stable).2.2.2 larger n Γ first second result ih

omit [DecidableRel S.R.cumulative] in
/-- Annotation comparison is eventually constant. -/
theorem compareTypes_const {Γ : Context S.R} (first second : TypeOver Γ) :
    EventuallyConst fun fuel =>
      ContextualDependentEta.Conversion.compareTypes facts roots heads algebra reducer fuel first second := by
  have typesConst : EventuallyConst fun fuel => ExecutableConversion.types S.R reducer fuel Γ.raw first.code second.code :=
    EventuallyConst.of_mono fun computed enough => types_mono reducer stable computed enough
  obtain ⟨threshold, same⟩ := typesConst.spec

  refine ⟨threshold, fun fuel enough => ?_⟩
  dsimp only
  unfold ContextualDependentEta.Conversion.compareTypes
  erw [same fuel enough]

/-- Type formation is eventually constant. -/
theorem formType_const {Γ : Context S.R} (code : Tm Head Γ.arity) :
    EventuallyConst fun fuel =>
      ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ code :=
  EventuallyConst.of_mono fun computed enough =>
    ContextualDependentRecoveryBudget.formType_mono facts roots heads algebra declared choices reducer stable computed enough

/-- Spine discovery keeps its spines. -/
theorem discover_mono (count : Nat) :
    ∀ {Γ : Context S.R} (whole : TypeOver Γ) {fuel larger : Nat} {spine : Spine whole},
      ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel count whole =
          some spine → fuel ≤ larger →
        ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer larger count whole =
          some spine := by
  induction count with
  | zero => intro Γ whole fuel larger spine computed _; exact computed
  | succ count ih =>
      intro Γ whole fuel larger spine computed enough
      obtain ⟨code, level, universeWitness, formed⟩ := whole
      cases code with
      | pi domain codomain =>
          simp only [ContextualDependentPiSpineDiscovery.discover] at computed ⊢
          obtain ⟨first, firstRun, afterOne⟩ := Option.bind_eq_some_iff.mp computed
          obtain ⟨second, secondRun, afterTwo⟩ := Option.bind_eq_some_iff.mp afterOne
          obtain ⟨rest, restRun, returned⟩ := Option.bind_eq_some_iff.mp afterTwo
          exact Option.bind_eq_some_iff.mpr ⟨first,
            ContextualDependentRecoveryBudget.formType_mono facts roots heads algebra declared choices reducer stable
              firstRun enough,
            Option.bind_eq_some_iff.mpr ⟨second,
              ContextualDependentRecoveryBudget.formType_mono facts roots heads algebra declared choices reducer stable
                secondRun enough,
              Option.bind_eq_some_iff.mpr ⟨rest, ih second.val restRun enough, returned⟩⟩⟩
      | _ => simp [ContextualDependentPiSpineDiscovery.discover] at computed

/-- Spine discovery is eventually constant. -/
theorem discover_const (count : Nat) {Γ : Context S.R} (whole : TypeOver Γ) :
    EventuallyConst fun fuel =>
      ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel count whole :=
  EventuallyConst.of_mono fun computed enough => discover_mono facts roots heads algebra declared choices reducer stable
    count whole computed enough

/-- Recovery is eventually constant. -/
theorem recover_const {Γ Δ : Context S.R} (selection : ContextualDependentTypedInversion.Inclusion Γ Δ)
    (type : TypeOver Γ) (target : Tm Head Δ.arity) :
    EventuallyConst fun fuel =>
      ContextualDependentTypedInversion.recover facts roots heads algebra declared choices reducer fuel selection type
        target :=
  EventuallyConst.of_mono fun computed enough =>
    ContextualDependentRecoveryBudget.recover_mono facts roots heads algebra declared choices reducer stable computed
      enough

/-- The newest declaration is eventually read the same way. -/
theorem newestOf_const (Θ : Context S.R) :
    EventuallyConst fun fuel =>
      ContextualDependentWorklist.newestOf facts roots heads algebra declared choices reducer fuel Θ := by
  rcases Θ with ⟨arity, raw, formed⟩
  cases raw with
  | nil => exact ⟨0, fun _ _ => rfl⟩
  | snoc raw code =>
      obtain ⟨threshold, same⟩ := (formType_const facts roots heads algebra declared choices reducer stable
        (Γ := ⟨_, raw, ContextualDependentWorklist.formedPrefix (S := S) formed⟩) code).spec
      refine ⟨threshold, fun fuel enough => ?_⟩
      dsimp only
      simp only [ContextualDependentWorklist.newestOf]
      erw [same fuel enough]

end Executables

/-! ## Bounded normalization of endpoints -/

section Normalization

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (root : ExecutableReduction.RootEvaluator S.R)
  (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)

/-- Bounded reduction of an endpoint keeps its results. -/
theorem reduceTerm_mono {Γ : Context S.R} (original : TotalTerm Γ) {fuel larger : Nat}
    {result : ContextualDependentNormalization.Normalized root original}
    (computed : ContextualDependentNormalization.reduceTerm root facts roots heads fuel original = some result)
    (enough : fuel ≤ larger) :
    ContextualDependentNormalization.reduceTerm root facts roots heads larger original = some result := by
  have kept : ∀ {n : Nat} {term : Tm Head n} {found : ExecutableReduction.Result S.R term},
      ExecutableReduction.normalize S.R root fuel term = some found →
        ExecutableReduction.normalize S.R root larger term = some found := by
    intro n term found accepted
    induction enough with
    | refl => exact accepted
    | step _ ih => exact ContextualDependentReductionBudget.success_succ S.R root ih
  unfold ContextualDependentNormalization.reduceTerm at computed ⊢
  split at computed
  · cases computed
  · rename_i annotation annotationRun
    split at computed
    · cases computed
    · rename_i value valueRun
      split
      · rename_i missing
        rw [kept annotationRun] at missing
        cases missing
      · rename_i annotation' annotationRun'
        rw [kept annotationRun] at annotationRun'
        obtain rfl := Option.some.inj annotationRun'
        split
        · rename_i missing
          rw [kept valueRun] at missing
          cases missing
        · rename_i value' valueRun'
          rw [kept valueRun] at valueRun'
          obtain rfl := Option.some.inj valueRun'
          exact computed

/-- **Bounded normalization of an endpoint is eventually constant**: the endpoint until the
normalizer finishes, its normal form after. -/
theorem termAt_const {Γ : Context S.R} (original : TotalTerm Γ) :
    EventuallyConst fun fuel => ContextualDependentNormalization.termAt root facts roots heads fuel original := by
  obtain ⟨threshold, same⟩ := (EventuallyConst.of_mono (f := fun fuel =>
    ContextualDependentNormalization.reduceTerm root facts roots heads fuel original)
    fun computed enough => reduceTerm_mono root facts roots heads original computed enough).spec
  refine ⟨threshold, fun fuel enough => ?_⟩
  dsimp only
  unfold ContextualDependentNormalization.termAt
  erw [same fuel enough]

/-- The normalized endpoint of the solver's reading is eventually constant. -/
theorem normalizeAt_const {C : Context S.R} {type : TypeOver C} (term : Term C type) :
    EventuallyConst fun fuel => ContextualDependentPatternSolver.normalizeAt facts roots heads root fuel term := by
  obtain ⟨threshold, same⟩ := (termAt_const root facts roots heads (⟨type, term⟩ : TotalTerm C)).spec
  refine ⟨threshold, fun fuel enough => ?_⟩
  apply Subtype.ext
  apply Term.ext
  change (ContextualDependentNormalization.termAt root facts roots heads fuel ⟨type, term⟩).2.code =
    (ContextualDependentNormalization.termAt root facts roots heads threshold ⟨type, term⟩).2.code
  erw [same fuel enough]

end Normalization

/-! ## The scoped reading and the distinct-locals rule -/

section Reading

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
variable (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))
include stable

/-- **The scoped reading of every store equation is eventually constant.** -/
theorem viewEquation_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      ContextualDependentPatternSolver.viewEquation facts roots heads algebra declared choices reducer root fuel equation := by
  obtain ⟨t₁, compared⟩ := (compareTypes_const facts roots heads algebra reducer stable equation.2.1 equation.1.1).spec
  cases comparison : ContextualDependentEta.Conversion.compareTypes facts roots heads algebra reducer t₁ equation.2.1
      equation.1.1 with
  | none =>
      refine ⟨t₁, fun fuel enough => ?_⟩
      dsimp only
      unfold ContextualDependentPatternSolver.viewEquation
      simp only [Option.bind_eq_bind]
      erw [compared fuel enough, comparison]
      rfl
  | some same =>
      obtain ⟨t₂, discovered⟩ := (discover_const facts roots heads algebra declared choices reducer stable
        (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.1).spec
      cases found : ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer t₂
          (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.1 with
      | none =>
          refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
          dsimp only
          unfold ContextualDependentPatternSolver.viewEquation
          simp only [Option.bind_eq_bind]
          erw [compared fuel (le_of_max_le_left enough), comparison, compared (max t₁ t₂) (le_max_left _ _), comparison]
          simp only [Option.bind_some]
          erw [discovered fuel (le_of_max_le_right enough), found, discovered (max t₁ t₂) (le_max_right _ _), found]
          rfl
      | some scope =>
          obtain ⟨t₃, leftSame⟩ := (normalizeAt_const root facts roots heads (scope.openFunction equation.1.2)).spec
          obtain ⟨t₄, rightSame⟩ := (normalizeAt_const root facts roots heads
            (scope.openFunction (equation.2.2.convertType equation.1.1 same.down))).spec
          refine ⟨max (max t₁ t₂) (max t₃ t₄), fun fuel enough => ?_⟩
          have e₁ : t₁ ≤ fuel := by omega
          have e₂ : t₂ ≤ fuel := by omega
          have e₃ : t₃ ≤ fuel := by omega
          have e₄ : t₄ ≤ fuel := by omega
          have f₁ : t₁ ≤ max (max t₁ t₂) (max t₃ t₄) := by omega
          have f₂ : t₂ ≤ max (max t₁ t₂) (max t₃ t₄) := by omega
          have f₃ : t₃ ≤ max (max t₁ t₂) (max t₃ t₄) := by omega
          have f₄ : t₄ ≤ max (max t₁ t₂) (max t₃ t₄) := by omega
          dsimp only
          unfold ContextualDependentPatternSolver.viewEquation
          simp only [Option.bind_eq_bind]
          erw [compared fuel e₁, comparison, compared _ f₁, comparison]
          simp only [Option.bind_some]
          erw [discovered fuel e₂, found, discovered _ f₂, found]
          simp only [Option.bind_some]
          show some _ = some _
          congr 1
          refine Sigma.ext rfl (heq_of_eq (PSigma.ext ?_ (proof_irrel_heq _ _)))
          change (⟨scope.result,
              (ContextualDependentPatternSolver.normalizeAt facts roots heads root fuel (scope.openFunction equation.1.2)).1,
              (ContextualDependentPatternSolver.normalizeAt facts roots heads root fuel
                (scope.openFunction (equation.2.2.convertType equation.1.1 same.down))).1⟩ : ContextualDependentScope.Active scope.target) =
            ⟨scope.result,
              (ContextualDependentPatternSolver.normalizeAt facts roots heads root (max (max t₁ t₂) (max t₃ t₄))
                (scope.openFunction equation.1.2)).1,
              (ContextualDependentPatternSolver.normalizeAt facts roots heads root (max (max t₁ t₂) (max t₃ t₄))
                (scope.openFunction (equation.2.2.convertType equation.1.1 same.down))).1⟩
          rw [leftSame fuel e₃, leftSame _ f₃, rightSame fuel e₄, rightSame _ f₄]

variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)

/-- The distinct-locals test on one equation is eventually constant. -/
theorem localsClash_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      ContextualDependentRigidDecomposition.localsClash rigid complete facts roots heads algebra declared choices
        reducer root fuel equation rest := by
  obtain ⟨threshold, same⟩ := (viewEquation_const facts roots heads algebra declared choices reducer root stable
    equation).spec
  refine ⟨threshold, fun fuel enough => ?_⟩
  dsimp only
  unfold ContextualDependentRigidDecomposition.localsClash
  erw [same fuel enough]

/-- **The distinct-locals rule is eventually constant on every store.** -/
theorem localsRule_const {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), EventuallyConst fun fuel =>
      ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared choices reducer
        root fuel problem
  | [] => ⟨0, fun _ _ => rfl⟩
  | equation :: rest => by
      obtain ⟨t₁, first⟩ := (localsClash_const facts roots heads algebra declared choices reducer root stable rigid
        complete equation rest).spec
      obtain ⟨t₂, later⟩ := (localsRule_const rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      simp only [ContextualDependentRigidDecomposition.localsRule]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

end Reading

end ContextualDependentDecisiveFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
