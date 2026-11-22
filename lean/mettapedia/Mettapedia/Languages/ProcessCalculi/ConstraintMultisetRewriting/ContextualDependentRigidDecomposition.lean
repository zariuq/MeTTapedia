import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternSolverPrune

/-!
# Rigid equations between local variables

Two distinct rigid local variables of an equation's own telescope are never equal, at any
type and under any solution in any future context: every outer solution renames the
telescope's locals to distinct locals of the reindexed telescope, both sides stay
normal, and typed-equal normal forms have the same support. No inhabitation premise is
used.

The executable rule reads each store equation under its telescope with the solver's
own scoped reading, and refutes the store when the two normalized sides are distinct
local variables. A **rigid round** tries this rule before the full solver's round.
Every refutation of the rigid round is certified, and every progress is a round of the
full solver.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRigidDecomposition

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentScope
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

omit [UniverseLevel.LevelOrder L] in
theorem localIndex_injective {rules : Rules Head} {Γ : Context rules} {scopeType : TypeOver Γ}
    (scope : Spine scopeType) : Function.Injective scope.localIndex := by
  intro first second same
  unfold Spine.localIndex at same
  exact Sum.inr_injective (scope.originEquiv.injective same)

variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)

include rigid complete in
/-- **Distinct rigid locals are never equal**: `λ x̄. xᵢ ≐ λ x̄. xⱼ` with `i ≠ j` has no solution
in any future context. -/
theorem distinct_locals_refuted {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target) (first second : scope.Local) (different : first ≠ second)
    (leftCode : active.left.code = .var (scope.localIndex first))
    (rightCode : active.right.code = .var (scope.localIndex second))
    {Δ : Context S.R} (solution : Δ ⟶ Γ) : ¬ (scope.toScoped active).Holds solution := by
  intro held
  rw [Spine.toScoped_holds_iff] at held
  change Equal S.R (scope.reindex solution).target.raw (subst (scope.map solution).substitution active.left.code)
      (subst (scope.map solution).substitution active.right.code)
      (subst (scope.map solution).substitution active.type.code) at held
  rw [leftCode, rightCode] at held
  change Equal S.R (scope.reindex solution).target.raw ((scope.map solution).substitution (scope.localIndex first))
      ((scope.map solution).substitution (scope.localIndex second))
      (subst (scope.map solution).substitution active.type.code) at held
  rw [map_localRead scope solution first first, map_localRead scope solution first second] at held
  have supports := ContextualDependentNormalSupport.equal_support rigid complete
    (scope.reindex solution).target.formed held
    (ContextualDependentNormalObservations.normal_var rigid _) (ContextualDependentNormalObservations.normal_var rigid _)
  simp only [Tm.support, Finset.singleton_inj] at supports
  rw [localRead_local, localRead_local] at supports
  exact different ((scope.localReindexEquiv solution).symm.injective (localIndex_injective _ supports))

/-- Read a code as a rigid local of a telescope. -/
def asLocal {rules : Rules Head} {Γ : Context rules} {scopeType : TypeOver Γ} (scope : Spine scopeType) :
    Tm Head scope.target.arity → Option scope.Local
  | .var index => localOf scope index
  | _ => none

omit [UniverseLevel.LevelOrder L] in
theorem asLocal_spec {rules : Rules Head} {Γ : Context rules} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    {code : Tm Head scope.target.arity} {position : scope.Local} (found : asLocal scope code = some position) :
    code = .var (scope.localIndex position) := by
  cases code with
  | var index =>
      simp only [asLocal, localOf] at found
      cases origin : scope.originEquiv.symm index with
      | inl _ => rw [origin] at found; cases found
      | inr other =>
          rw [origin] at found
          cases found
          unfold Spine.localIndex
          rw [← origin, Equiv.apply_symm_apply]
  | _ => cases found

variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
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

/-- The rule on one store equation: refute when its normalized sides are distinct rigid locals. -/
def localsClash (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ)) : Option (PLift (¬ (frames S.levels).Solvable (equation :: rest))) :=
  match ContextualDependentPatternSolver.viewEquation facts roots heads algebra declared choices reducer root fuel
      equation with
  | none => none
  | some ⟨scope, active, view⟩ =>
      letI := localDecidableEq scope
      match leftFound : asLocal scope active.left.code, rightFound : asLocal scope active.right.code with
      | some first, some second =>
          if different : first ≠ second then
            some ⟨(ContextualDependentPatternSolver.View.refutes (S := S) ⟨scope.toScoped active, view⟩
              (fun solution => distinct_locals_refuted rigid complete scope active first second different
                (asLocal_spec scope leftFound) (asLocal_spec scope rightFound) solution) rest)⟩
          else none
      | _, _ => none

/-- Search the store for an equation between distinct rigid locals. -/
def localsRule (fuel : Nat) {Θ : Context S.R} :
    (problem : EquationStore (TotalTerm Θ)) → Option (PLift (¬ (frames S.levels).Solvable problem))
  | [] => none
  | equation :: rest =>
      match localsClash rigid complete facts roots heads algebra declared choices reducer root fuel equation rest with
      | some absent => some absent
      | none =>
          (localsRule fuel rest).map fun absent => ⟨fun ⟨Δ, solution, modeled⟩ =>
            absent.down ⟨Δ, solution, fun other member => modeled other (List.mem_cons_of_mem _ member)⟩⟩

/-- **One rigid round**: refute distinct rigid locals, otherwise run the full solver's round. -/
def rigidRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels ContextualDependentWorklist.size problem :=
  match localsRule rigid complete facts roots heads algebra declared choices reducer root fuel problem with
  | some absent => .refuted absent.down
  | none => ContextualDependentPatternSolver.fullRound rigid facts complete roots heads algebra declared choices
      reducer root normalizes certifyNormal headTypingUnique fuel problem

/-- **The rigid solver** for the worklist driver. -/
def rigidSolver (fuel : Nat) : Solver S.levels where
  rank := ContextualDependentWorklist.size
  round := rigidRound rigid complete facts roots heads algebra declared choices reducer root normalizes certifyNormal
    headTypingUnique fuel

theorem localsRule_nil (fuel : Nat) {Θ : Context S.R} :
    localsRule rigid complete facts roots heads algebra declared choices reducer root fuel
      ([] : EquationStore (TotalTerm Θ)) = none := rfl

theorem rigidRound_nil (fuel : Nat) {Θ : Context S.R} :
    rigidRound rigid complete facts roots heads algebra declared choices reducer root normalizes certifyNormal
      headTypingUnique fuel ([] : EquationStore (TotalTerm Θ)) = .stuck := by
  unfold rigidRound
  rw [localsRule_nil]
  exact ContextualDependentPatternSolver.fullRound_nil rigid facts complete roots heads algebra declared choices
    reducer root normalizes certifyNormal headTypingUnique fuel

/-- **Every refutation of the rigid round is certified**: distinct rigid locals, or a certified
refutation of the full solver's round. -/
theorem rigidRound_refuted_grounds (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {absent : ¬ (frames S.levels).Solvable problem}
    (refuted : rigidRound rigid complete facts roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel problem = .refuted absent) :
    (∃ absent', localsRule rigid complete facts roots heads algebra declared choices reducer root fuel problem =
        some absent') ∨
      ContextualDependentPatternSolver.fullRound rigid facts complete roots heads algebra declared choices reducer
        root normalizes certifyNormal headTypingUnique fuel problem = .refuted absent := by
  unfold rigidRound at refuted
  cases found : localsRule rigid complete facts roots heads algebra declared choices reducer root fuel problem with
  | some absent' => exact .inl ⟨absent', rfl⟩
  | none =>
      rw [found] at refuted
      exact .inr refuted

end ContextualDependentRigidDecomposition
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
