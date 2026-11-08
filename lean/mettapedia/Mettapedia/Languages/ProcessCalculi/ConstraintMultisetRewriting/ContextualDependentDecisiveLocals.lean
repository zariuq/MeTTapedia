import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveDriver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentExecutableDiscovery
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidDecomposition

/-!
# Decisiveness on stores with distinct rigid locals

The first semantic class on which the acceptance theorem is instantiated, in the cumulative tower
with the actual normalizer and universe choices.

A store equation **equates distinct rigid locals** when its two annotations are equal types, its
annotation is a normal type with at least as many leading Π binders as its left side has leading
abstractions, and, opened under every telescope of its annotation of that length, its two sides
reduce to two distinct locals of the telescope. The definition reads only the store, not the
solver.

On every store containing such an equation, the rigid solver refutes the store at one joint budget,
with a certified refutation, and keeps that outcome at every larger joint budget. The proof uses
eventual success of the solver's executable entry points: annotation comparison, spine discovery
and the normalizer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDecisiveLocals

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentScope ContextualDependentPiSpine
open ContextualDependentGeneralPattern ContextualDependentWorklist ContextualDependentDecisiveDriver
open ContextualDependentExecutableJoin ContextualDependentExecutableConversion ContextualDependentExecutableChecking
open ContextualDependentExecutableDiscovery ContextualDependentRigidDecomposition

variable {L : Type} [UniverseLevel.LevelOrder L]
variable [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative]

local instance settingHeadEq (valuation : Nat → L) : DecidableRel (TowerModel.setting valuation).R.headEq :=
  inferInstanceAs (DecidableRel (LevelTower.rules L).headEq)

local instance settingUniverse (valuation : Nat → L) (head : LevelTower.Head L) :
    Decidable ((TowerModel.setting valuation).R.isUniverse head) :=
  inferInstanceAs (Decidable ((LevelTower.rules L).isUniverse head))

local instance settingCumulative (valuation : Nat → L) : DecidableRel (TowerModel.setting valuation).R.cumulative :=
  inferInstanceAs (DecidableRel (LevelTower.rules L).cumulative)

variable (valuation : Nat → L)

/-- **An equation between distinct rigid locals**, read from the store alone. -/
def DistinctLocals {Θ : Context (LevelTower.rules L)} (equation : Equation (TotalTerm Θ)) : Prop :=
  ∃ same : TypeEq (LevelTower.rules L) Θ.raw equation.2.1.code equation.1.1.code,
    Normal (LevelTower.rules L) equation.1.1.code ∧
    ContextualDependentPatternSolver.lamDepth equation.1.2.code ≤ piDepth equation.1.1.code ∧
    ∀ scope : Spine equation.1.1, scope.length = ContextualDependentPatternSolver.lamDepth equation.1.2.code →
      ∃ first second : scope.Local, first ≠ second ∧
        Star (R := LevelTower.rules L) (scope.openFunction equation.1.2).code (.var (scope.localIndex first)) ∧
        Star (R := LevelTower.rules L) (scope.openFunction (equation.2.2.convertType equation.1.1 same)).code
          (.var (scope.localIndex second))

/-- The rigid round of the tower at every budget, as a fuel-indexed family. -/
def family (rigid : ∀ name, (TowerModel.setting valuation).roles name = .rigid)
    (normalizes : ∀ {Θ : Context (TowerModel.setting valuation).R} {type : TypeOver Θ} (term : Term Θ type),
      ∃ code : Tm (LevelTower.Head L) Θ.arity,
        ContextualDependentNormalChecking.Normal (S := TowerModel.setting valuation) code ∧
        Equal (TowerModel.setting valuation).R Θ.raw term.code code type.code)
    (certifyNormal : ∀ {n : Nat} (term : Tm (LevelTower.Head L) n),
      Option (PLift (ContextualDependentNormalChecking.Normal (S := TowerModel.setting valuation) term))) :
    Family (TowerModel.setting valuation).levels where
  rank := ContextualDependentWorklist.size
  round fuel := rigidRound (S := TowerModel.setting valuation) rigid TowerModel.complete TowerModel.facts
    TowerModel.roots TowerModel.heads TowerModel.algebra declared tc red (fun _ => none) normalizes certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique fuel

/-! ## The normalizer of the scoped reading -/

omit [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative] in
theorem normalizeAt_eventually {C : Context (LevelTower.rules L)} {type : TypeOver C} (term : Term C type)
    {target : Tm (LevelTower.Head L) C.arity} (reaches : Star (R := LevelTower.rules L) term.code target)
    (normal : Normal (LevelTower.rules L) target) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      (ContextualDependentPatternSolver.normalizeAt (S := TowerModel.setting valuation) TowerModel.facts
        TowerModel.roots TowerModel.heads (fun _ => none) larger term).1.code = target := by
  obtain ⟨fA, annotation, _, _, stableA⟩ := red_eventually C.formed type.formed
  obtain ⟨fV, value, normalV, starV, stableV⟩ := red_eventually C.formed term.typed
  have valueIsTarget : value.val = target := by
    obtain ⟨common, toCommon, fromTarget⟩ := confluent empty_root starV reaches
    rw [normal.star_eq fromTarget] at toCommon
    exact (normalV.star_eq toCommon).symm
  refine ⟨fA + fV, fun larger enough => ?_⟩
  have runA : ExecutableReduction.normalize (TowerModel.setting valuation).R (fun _ => none) larger type.code =
      some annotation := stableA larger (by omega)
  have runV : ExecutableReduction.normalize (TowerModel.setting valuation).R (fun _ => none) larger term.code =
      some value := stableV larger (by omega)
  have reduced : ∃ result, ContextualDependentNormalization.reduceTerm (S := TowerModel.setting valuation)
      (fun _ => none) TowerModel.facts TowerModel.roots TowerModel.heads larger ⟨type, term⟩ = some result ∧
      result.value.2.code = value.val := by
    unfold ContextualDependentNormalization.reduceTerm
    split
    · rename_i missing
      simp [runA] at missing
    · split
      · rename_i missing
        simp [runV] at missing
      · rename_i found
        rw [runV] at found
        obtain rfl := Option.some.inj found
        exact ⟨_, rfl, rfl⟩
  obtain ⟨result, computed, code⟩ := reduced
  have codeOf : (ContextualDependentPatternSolver.normalizeAt (S := TowerModel.setting valuation) TowerModel.facts
      TowerModel.roots TowerModel.heads (fun _ => none) larger term).1.code =
      (ContextualDependentNormalization.termAt (S := TowerModel.setting valuation) (fun _ => none) TowerModel.facts
        TowerModel.roots TowerModel.heads larger ⟨type, term⟩).2.code := rfl
  rw [codeOf]
  unfold ContextualDependentNormalization.termAt
  rw [computed]
  exact code.trans valueIsTarget

omit [UniverseLevel.LevelOrder L] [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative] in
theorem asLocal_localIndex {rules : Rules (LevelTower.Head L)} {Γ : Context rules} {scopeType : TypeOver Γ}
    (scope : Spine scopeType) (position : scope.Local) :
    asLocal scope (.var (scope.localIndex position)) = some position := by
  simp only [asLocal, localOf, Spine.localIndex, Equiv.symm_apply_apply]
  rfl

/-! ## The distinct-locals rule eventually fires -/

/-- **The distinct-locals rule eventually fires** on an equation between distinct rigid locals. -/
theorem localsClash_eventually (rigid : ∀ name, (TowerModel.setting valuation).roles name = .rigid)
    {Θ : Context (LevelTower.rules L)} (equation : Equation (TotalTerm Θ)) (distinct : DistinctLocals equation)
    (rest : EquationStore (TotalTerm Θ)) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      (localsClash (S := TowerModel.setting valuation) rigid TowerModel.complete TowerModel.facts TowerModel.roots
        TowerModel.heads TowerModel.algebra declared tc red (fun _ => none) larger equation rest).isSome := by
  obtain ⟨same, normal, deep, locals⟩ := distinct
  obtain ⟨f₁, compared, stable₁⟩ := compareTypes_eventually valuation equation.2.1 equation.1.1 same
  obtain ⟨f₂, scope, stable₂⟩ := discover_eventually valuation _ equation.1.1 normal deep
  have length := ContextualDependentPiSpineDiscovery.discovered_length (S := TowerModel.setting valuation)
    TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra declared tc red f₂ _ equation.1.1 scope
    (stable₂ f₂ le_rfl)
  obtain ⟨first, second, different, leftReaches, rightReaches⟩ := locals scope length
  obtain ⟨f₃, leftStable⟩ := normalizeAt_eventually valuation _ leftReaches
    (ContextualDependentNormalObservations.normal_var (S := TowerModel.setting valuation) rigid _)
  obtain ⟨f₄, rightStable⟩ := normalizeAt_eventually valuation _ rightReaches
    (ContextualDependentNormalObservations.normal_var (S := TowerModel.setting valuation) rigid _)
  refine ⟨f₁ + f₂ + f₃ + f₄, fun larger enough => ?_⟩
  have compared' := stable₁ larger (by omega)
  have discovered' := stable₂ larger (by omega)
  have leftCode := leftStable larger (by omega)
  have rightCode := rightStable larger (by omega)
  unfold localsClash ContextualDependentPatternSolver.viewEquation
  simp only [Option.bind_eq_bind]
  erw [compared']
  simp only [Option.bind_some]
  erw [discovered']
  simp only [Option.bind_some, pure]
  split
  · rename_i leftFirst rightSecond leftFound rightFound
    erw [leftCode, asLocal_localIndex] at leftFound
    erw [rightCode, asLocal_localIndex] at rightFound
    obtain rfl := Option.some.inj leftFound
    obtain rfl := Option.some.inj rightFound
    split
    · rfl
    · rename_i notDifferent
      exact absurd different notDifferent
  · rename_i notBoth
    refine absurd ?_ (notBoth first second ?_)
    · erw [rightCode, asLocal_localIndex]
    · erw [leftCode, asLocal_localIndex]

/-- The distinct-locals search eventually fires on every store containing such an equation. -/
theorem localsRule_eventually (rigid : ∀ name, (TowerModel.setting valuation).roles name = .rigid)
    {Θ : Context (LevelTower.rules L)} :
    ∀ (problem : EquationStore (TotalTerm Θ)), (∃ equation ∈ problem, DistinctLocals equation) →
      ∃ fuel, ∀ larger, fuel ≤ larger →
        (localsRule (S := TowerModel.setting valuation) rigid TowerModel.complete TowerModel.facts TowerModel.roots
          TowerModel.heads TowerModel.algebra declared tc red (fun _ => none) larger problem).isSome
  | [], ⟨_, member, _⟩ => absurd member (List.not_mem_nil)
  | first :: rest, ⟨equation, member, distinct⟩ => by
      rcases List.mem_cons.mp member with rfl | later
      · obtain ⟨fuel, fires⟩ := localsClash_eventually valuation rigid equation distinct rest
        refine ⟨fuel, fun larger enough => ?_⟩
        obtain ⟨absent, computed⟩ := Option.isSome_iff_exists.mp (fires larger enough)
        simp only [localsRule, computed]
        rfl
      · obtain ⟨fuel, fires⟩ := localsRule_eventually rigid rest ⟨equation, later, distinct⟩
        refine ⟨fuel, fun larger enough => ?_⟩
        obtain ⟨absent, computed⟩ := Option.isSome_iff_exists.mp (fires larger enough)
        simp only [localsRule]
        split
        · rfl
        · rw [computed]
          rfl

variable (rigid : ∀ name, (TowerModel.setting valuation).roles name = .rigid)
  (normalizes : ∀ {Θ : Context (TowerModel.setting valuation).R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm (LevelTower.Head L) Θ.arity,
      ContextualDependentNormalChecking.Normal (S := TowerModel.setting valuation) code ∧
      Equal (TowerModel.setting valuation).R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm (LevelTower.Head L) n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := TowerModel.setting valuation) term)))

/-- **The stores with distinct rigid locals** form a class on which the rigid round settles. -/
def settled : Settled (family valuation rigid normalizes certifyNormal) where
  holds problem := ∃ equation ∈ problem, DistinctLocals equation
  settles := by
    intro Γ problem inside _
    obtain ⟨threshold, fires⟩ := localsRule_eventually valuation rigid problem inside
    obtain ⟨absent, computed⟩ := Option.isSome_iff_exists.mp (fires threshold le_rfl)
    have atBudget : ∀ fuel, threshold ≤ fuel →
        (family valuation rigid normalizes certifyNormal).round fuel problem = .refuted absent.down := by
      intro fuel enough
      obtain ⟨absent', computed'⟩ := Option.isSome_iff_exists.mp (fires fuel enough)
      change rigidRound (S := TowerModel.setting valuation) rigid TowerModel.complete TowerModel.facts
        TowerModel.roots TowerModel.heads TowerModel.algebra declared tc red (fun _ => none) normalizes certifyNormal
        ContextualDependentNormalCheckingTower.head_typing_unique fuel problem = _
      unfold rigidRound
      rw [computed']
      rfl
    refine ⟨threshold, ?_, fun fuel enough => ?_, fun progressed => ?_⟩
    · rw [atBudget threshold le_rfl]
      intro stuck
      cases stuck
    · rw [atBudget fuel enough, atBudget threshold le_rfl]
    · rw [atBudget threshold le_rfl] at progressed
      cases progressed

/-- **Decisiveness on stores with distinct rigid locals**: at one joint budget, and at every larger
one, the rigid solver refutes the store with a certified refutation, and the outcome does not
change. -/
theorem decided {Θ : Context (LevelTower.rules L)} {problem : EquationStore (TotalTerm Θ)}
    (inside : ∃ equation ∈ problem, DistinctLocals equation) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((family valuation rigid normalizes certifyNormal).solver larger) problem larger =
        run ((family valuation rigid normalizes certifyNormal).solver budget) problem budget ∧
      ∃ absent, run ((family valuation rigid normalizes certifyNormal).solver larger) problem larger = .refuted absent := by
  obtain ⟨budget, eventual⟩ := (settled valuation rigid normalizes certifyNormal).decided inside
  obtain ⟨threshold, fires⟩ := localsRule_eventually valuation rigid problem inside
  obtain ⟨absent, _⟩ := Option.isSome_iff_exists.mp (fires threshold le_rfl)
  refine ⟨budget, fun larger enough => ?_⟩
  obtain ⟨same, outcome⟩ := eventual larger enough
  refine ⟨same, ?_⟩
  rcases outcome with ⟨state, _, _, principal⟩ | refuted
  · exact absurd ⟨_, state.answer, principal.sound⟩ absent.down
  · exact refuted

end ContextualDependentDecisiveLocals
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
