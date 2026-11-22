import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidDecompositionSpine

/-!
# Rigid–rigid decomposition inside the solver

The decomposition rule reads a store equation under its telescope with the solver's own scoped
reading. When both normalized sides apply the same rigid local `h : (a : D) → E` and the equation
sits at a rigid base type, it replaces the equation by the argument equation `λ x̄. a ≐ λ x̄. b` at
`D`, closed with the executable universe joins. The replacement has exactly the original solutions
in every future context (`decompose_scoped`), so it is an update that loses nothing.

A rank-respecting round must remove a declaration or an equation, so the rule continues on the
decomposed store at once: the argument equation is refuted when it equates distinct rigid locals, or
the pattern rule solves the newest metavariable. Otherwise the decomposition is not committed. The
**decomposition round** tries this rule and then the rigid round; every refutation it reports is
certified and every progress removes a declaration or is a progress of the rigid round.
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

section Reading

variable {rules : Rules Head} {Γ : Context rules} {scopeType : TypeOver Γ} (scope : Spine scopeType)

/-- Read `h a` with `h` a rigid local of the telescope. -/
def asLocalApplication : Tm Head scope.target.arity → Option (scope.Local × Tm Head scope.target.arity)
  | .app (.var index) argument => (localOf scope index).map fun position => (position, argument)
  | _ => none

omit [UniverseLevel.LevelOrder L] in
theorem asLocalApplication_spec {code : Tm Head scope.target.arity} {position : scope.Local}
    {argument : Tm Head scope.target.arity} (found : asLocalApplication scope code = some (position, argument)) :
    code = .app (.var (scope.localIndex position)) argument := by
  cases code with
  | app function argument' =>
      cases function with
      | var index =>
          simp only [asLocalApplication, Option.map_eq_some_iff, Prod.mk.injEq] at found
          obtain ⟨position', located, rfl, rfl⟩ := found
          rw [asLocal_spec scope (show asLocal scope (.var index) = some position' from located)]
      | _ => simp [asLocalApplication] at found
  | _ => simp [asLocalApplication] at found

/-- Decide that a code is a rigid base type of the telescope. -/
def isRigidBase : Tm Head scope.target.arity → Bool
  | .id _ _ _ => true
  | .head _ => true
  | .var index => (localOf scope index).isSome
  | _ => false

omit [UniverseLevel.LevelOrder L] in
theorem isRigidBase_spec {code : Tm Head scope.target.arity} (accepted : isRigidBase scope code = true) :
    RigidBase scope code := by
  cases code with
  | id X a b => exact .inl ⟨X, a, b, rfl⟩
  | head u => exact .inr (.inl ⟨u, rfl⟩)
  | var index =>
      obtain ⟨position, located⟩ := Option.isSome_iff_exists.mp accepted
      exact .inr (.inr ⟨position, asLocal_spec scope (show asLocal scope (.var index) = some position from located)⟩)
  | _ => simp [isRigidBase] at accepted

end Reading

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

/-- **Decomposition of one scoped equation**: the argument equation, with exactly the same solutions. -/
def decomposeActive (fuel : Nat) {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target) :
    Option {argument : Active scope.target // ∀ {Δ : Context S.R} (solution : Δ ⟶ Γ),
      (scope.toScoped active).Holds solution ↔ (scope.toScoped argument).Holds solution} :=
  letI := localDecidableEq scope
  match leftFound : asLocalApplication scope active.left.code,
      rightFound : asLocalApplication scope active.right.code with
  | some (head, left), some (head', right) =>
      if same : head = head' then
        match headShape : Ctx.lookup scope.target.raw (scope.localIndex head) with
        | .pi domain codomain =>
            if base : isRigidBase scope active.type.code = true then
              match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
                  scope.target domain with
              | none => none
              | some argumentType =>
                  have leftCode := asLocalApplication_spec scope leftFound
                  have rightCode : active.right.code = .app (.var (scope.localIndex head)) right := by
                    rw [same]
                    exact asLocalApplication_spec scope rightFound
                  have typedLeft := active.left.typed
                  have typedRight := active.right.typed
                  have leftArgument := (application_below facts scope.target.formed (scope.localIndex head) headShape
                    (by rw [leftCode] at typedLeft; exact typedLeft)).1
                  have rightArgument := (application_below facts scope.target.formed (scope.localIndex head) headShape
                    (by rw [rightCode] at typedRight; exact typedRight)).1
                  let argument : Active scope.target :=
                    ⟨argumentType.val, ⟨left, by rw [argumentType.property]; exact leftArgument⟩,
                      ⟨right, by rw [argumentType.property]; exact rightArgument⟩⟩
                  some ⟨argument, fun solution =>
                    decompose_scoped facts roots heads algebra complete scope head active argument
                      (by rw [headShape]; exact congrArg (fun code => Tm.pi code codomain) argumentType.property.symm)
                      leftCode rightCode (isRigidBase_spec scope base) solution⟩
            else none
        | _ => none
      else none
  | _, _ => none

omit [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
/-- A scoped reading with a closed form gives an equivalent store equation in its place. -/
theorem replace_equivalent {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} {constraint : Scoped Θ}
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ Θ),
      (frames S.levels).Models solution [equation] ↔ constraint.Holds solution)
    {closed : Active Θ} (computed : constraint.closeWith S.levels choices = some closed)
    (rest : EquationStore (TotalTerm Θ)) :
    (frames S.levels).Equivalent (equation :: rest) (closed.equation :: rest) := by
  intro Δ solution
  have first : (frames S.levels).Models solution [equation] ↔ (frames S.levels).Models solution [closed.equation] :=
    (view solution).trans ((Scoped.closeWith_holds_iff S.levels choices constraint computed solution).symm.trans
      (Active.holds_iff_models S.levels closed solution))
  have split := fun (head : Equation (TotalTerm Θ)) =>
    Frames.models_append (X := frames S.levels) solution [head] rest
  exact (split equation).trans ((and_congr_left fun _ => first).trans (split closed.equation).symm)

/-- **Decomposition of one store equation**, continued on the decomposed store by the distinct-locals
rule and the pattern rule. -/
def decomposeEquation (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ)) : Option (ContextualDependentPatternSolver.Found (equation :: rest)) :=
  match ContextualDependentPatternSolver.viewEquation facts roots heads algebra declared choices reducer root fuel
      equation with
  | none => none
  | some ⟨scope, active, view⟩ =>
      match decomposeActive facts complete roots heads algebra declared choices reducer fuel scope active with
      | none => none
      | some ⟨argument, sameSolutions⟩ =>
          match computed : (scope.toScoped argument).closeWith S.levels choices with
          | none => none
          | some closed =>
              let moved : Update S.levels (equation :: rest) :=
                (Update.pending S.levels (closed.equation :: rest)).rephrase
                  (replace_equivalent choices (fun solution => (view solution).trans (sameSolutions solution))
                    computed rest)
              match localsRule rigid complete facts roots heads algebra declared choices reducer root fuel
                  (closed.equation :: rest) with
              | some absent => some (.refuted fun solvable => absent.down (moved.solvable_iff.mp solvable))
              | none =>
                  match ContextualDependentPatternSolver.patternRule rigid facts complete roots heads algebra declared
                      choices reducer root normalizes certifyNormal fuel (closed.equation :: rest) with
                  | some (.solved solved smaller) => some (.solved (moved.then solved) smaller)
                  | some (.refuted absent) => some (.refuted fun solvable => absent (moved.solvable_iff.mp solvable))
                  | none => none

/-- Search the store for an equation on which decomposition decides. -/
def decomposeSearch (fuel : Nat) {Θ : Context S.R} :
    (problem : EquationStore (TotalTerm Θ)) → Option (ContextualDependentPatternSolver.Found problem)
  | [] => none
  | equation :: rest =>
      match decomposeEquation rigid facts complete roots heads algebra declared choices reducer root normalizes
          certifyNormal fuel equation rest with
      | some found => some found
      | none => (decomposeSearch fuel rest).map (ContextualDependentPatternSolver.Found.keepLeft equation)

/-- **One decomposition round**: decomposition, then the rigid round. -/
def decomposeRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels ContextualDependentWorklist.size problem :=
  match decomposeSearch rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal fuel problem with
  | some (.solved update smaller) => .progress update (Prod.Lex.left _ _ smaller)
  | some (.refuted absent) => .refuted absent
  | none => rigidRound rigid complete facts roots heads algebra declared choices reducer root normalizes certifyNormal
      headTypingUnique fuel problem

/-- **The decomposition solver** for the worklist driver. -/
def decomposeSolver (fuel : Nat) : Solver S.levels where
  rank := ContextualDependentWorklist.size
  round := decomposeRound rigid facts complete roots heads algebra declared choices reducer root normalizes
    certifyNormal headTypingUnique fuel

theorem decomposeRound_nil (fuel : Nat) {Θ : Context S.R} :
    decomposeRound rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      headTypingUnique fuel ([] : EquationStore (TotalTerm Θ)) = .stuck := by
  unfold decomposeRound
  exact rigidRound_nil rigid complete facts roots heads algebra declared choices reducer root normalizes certifyNormal
    headTypingUnique fuel

end ContextualDependentRigidDecomposition
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
