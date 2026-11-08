import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidDecomposition

/-!
# Rigid–rigid decomposition at a local head

An equation `λ x̄. h a ≐ λ x̄. h b` whose two sides apply the same rigid local `h` of the
telescope, at a rigid base type, has exactly the solutions of the argument equation
`λ x̄. a ≐ λ x̄. b` at the domain of `h`, in every future context.

* **Congruence** gives one direction.
* **Spine injectivity** gives the other. The algorithmic equality, which is complete, compares
  two applications of one variable at a base type as spines, and a spine comparison compares the
  arguments at the domain the head's type assigns. A base type is an identity type, a universe or
  a neutral type: at none of them is an application η-expanded.
* A rigid base type stays one under every outer solution: identity types and universes are kept by
  substitution, and a type headed by a local of the telescope stays headed by a local.

No inhabitation premise is used, and the argument terms are arbitrary, not necessarily normal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRigidDecomposition

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentScope ContextualDependentPiSpine ContextualDependentGeneralPattern

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- A type at which no term is η-expanded: an identity type, a head, or a neutral type. -/
def BaseType (S : Setting Head L) {n : Nat} (C : Tm Head n) : Prop :=
  (∃ X a b, C = .id X a b) ∨ (∃ u, C = .head u) ∨ Neutral S.roles C

theorem BaseType.whnf {n : Nat} {C : Tm Head n} (base : BaseType S C) : Whnf S.R S.roles C := by
  rcases base with ⟨X, a, b, rfl⟩ | ⟨u, rfl⟩ | neutral
  · exact id_whnf S.shape X a b
  · exact head_whnf S.shape u
  · exact neutral.whnf S.shape

/-- A spine comparison of two applications of one variable compares the arguments at the
domain of the variable's weak-head type. -/
theorem spinesW_arguments {n : Nat} {Γ : Ctx Head n} (head : Fin n) {a b U : Tm Head n}
    (spines : Algorithmic S.R S.roles (.spinesW Γ (.app (.var head) a) (.app (.var head) b) U)) :
    ∃ A B, RedTy S.R S.roles Γ (Ctx.lookup Γ head) (.pi A B) ∧ Algorithmic S.R S.roles (.terms Γ a b A) := by
  cases spines with
  | spinesW inner _ _ =>
      cases inner with
      | app functions arguments =>
          cases functions with
          | spinesW headInner headRed _ =>
              cases headInner with
              | var index => exact ⟨_, _, headRed, arguments⟩

/-- **Spine injectivity at a base type**: two applications of one variable that are
algorithmically equal at a base type have algorithmically equal arguments. -/
theorem head_arguments {n : Nat} {Γ : Ctx Head n} (head : Fin n) {a b C : Tm Head n} (base : BaseType S C)
    (derivation : Algorithmic S.R S.roles (.terms Γ (.app (.var head) a) (.app (.var head) b) C)) :
    ∃ A B, RedTy S.R S.roles Γ (Ctx.lookup Γ head) (.pi A B) ∧ Algorithmic S.R S.roles (.terms Γ a b A) := by
  cases derivation with
  | terms typeRed _ leftRed rightRed inner =>
      have typeSame := WhRed.eq_of_whnf (S := S) base.whnf typeRed.red
      have leftSame := WhRed.eq_of_whnf (S := S) ((Neutral.app (Neutral.var head)).whnf S.shape) leftRed.red
      have rightSame := WhRed.eq_of_whnf (S := S) ((Neutral.app (Neutral.var head)).whnf S.shape) rightRed.red
      subst typeSame
      subst leftSame
      subst rightSame
      cases inner with
      | univ _ _ _ types =>
          cases types with
          | neutralTypes _ _ _ spines => exact spinesW_arguments head spines
      | eta =>
          rcases base with ⟨_, _, _, impossible⟩ | ⟨_, impossible⟩ | neutral
          · cases impossible
          · cases impossible
          · exact absurd rfl (neutral.not_former.2.1 _ _)
      | sigmaEta =>
          rcases base with ⟨_, _, _, impossible⟩ | ⟨_, impossible⟩ | neutral
          · cases impossible
          · cases impossible
          · exact absurd rfl (neutral.not_former.2.2.1 _ _)
      | spine _ _ _ _ _ spines => exact spinesW_arguments head spines

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra complete in
/-- **Spine injectivity, typed**: if two applications of a variable usable at a function type are
equal at a base type, their arguments are equal at its domain. -/
theorem equal_arguments_of_base {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (head : Fin n)
    {D : Tm Head n} {E : Tm Head (n + 1)} (headType : TypeLe S.R Γ (Ctx.lookup Γ head) (.pi D E))
    (functionType : IsType S.R Γ (.pi D E)) {a b C : Tm Head n} (base : BaseType S C)
    (same : Equal S.R Γ (.app (.var head) a) (.app (.var head) b) C) : Equal S.R Γ a b D := by
  obtain ⟨A, B, reduced, arguments⟩ := head_arguments head base (complete formed same)
  have sameArguments := Algorithmic.sound_terms facts roots heads algebra formed arguments
  obtain ⟨s, hs, _, _, toPi⟩ := reduced.sort
  have below : TypeLe S.R Γ (.pi A B) (.pi D E) := .conv (.symm toPi) hs headType
  exact Equal.convType sameArguments (TypeLe.pi_parts (S := S) facts below functionType formed).1

include facts roots heads algebra complete in
/-- **Decomposition at a base type**: two applications of a variable of a function type are equal
exactly when their arguments are. -/
theorem decompose_iff {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (head : Fin n)
    {D : Tm Head n} {E : Tm Head (n + 1)} (headTyped : Typed S.R Γ (.var head) (.pi D E))
    {a b C : Tm Head n} (base : BaseType S C) (resultType : TypeEq S.R Γ (inst0 a E) C) :
    Equal S.R Γ (.app (.var head) a) (.app (.var head) b) C ↔ Equal S.R Γ a b D := by
  constructor
  · intro same
    exact equal_arguments_of_base facts roots heads algebra complete formed head (Typed.generation headTyped)
      (Typed.isType (S := S) headTyped formed) base same
  · intro same
    exact Equal.convType (.appCong (.refl headTyped) same) resultType

/-! ## Decomposition of a scoped equation -/

/-- A rigid base type of a telescope: an identity type, a head, or a local of the telescope. -/
def RigidBase {rules : Rules Head} {Γ : Context rules} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (C : Tm Head scope.target.arity) : Prop :=
  (∃ X a b, C = .id X a b) ∨ (∃ u, C = .head u) ∨ ∃ position : scope.Local, C = .var (scope.localIndex position)

/-- A rigid base type stays a base type under every outer solution. -/
theorem RigidBase.subst {Γ : Context S.R} {scopeType : TypeOver Γ} {scope : Spine scopeType}
    {C : Tm Head scope.target.arity} (base : RigidBase scope C) {Δ : Context S.R} (solution : Δ ⟶ Γ) :
    BaseType S (Presentation.subst (scope.map solution).substitution C) := by
  rcases base with ⟨X, a, b, rfl⟩ | ⟨u, rfl⟩ | ⟨position, rfl⟩
  · exact .inl ⟨_, _, _, rfl⟩
  · exact .inr (.inl ⟨u, rfl⟩)
  · refine .inr (.inr ?_)
    change Neutral S.roles ((scope.map solution).substitution (scope.localIndex position))
    rw [map_localRead scope solution position position]
    exact .var _

include facts in
/-- The type of an application of a local at a rigid base type is above the codomain instantiated
at the argument. -/
theorem application_below {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (head : Fin n)
    {D : Tm Head n} {E : Tm Head (n + 1)} (headType : Ctx.lookup Γ head = .pi D E) {a C : Tm Head n}
    (typed : Typed S.R Γ (.app (.var head) a) C) :
    Typed S.R Γ a D ∧ Below S.R Γ (inst0 a E) C := by
  obtain ⟨A₀, B₀, typedHead, typedArgument, le⟩ := Typed.generation typed
  have headLe : TypeLe S.R Γ (Ctx.lookup Γ head) (.pi A₀ B₀) := Typed.generation typedHead
  rw [headType] at headLe
  obtain ⟨domains, codomains⟩ := TypeLe.pi_parts (S := S) facts headLe (Typed.isType (S := S) typedHead formed) formed
  have typedArgument' : Typed S.R Γ a D := Typed.convType typedArgument (TypeEq.symm domains)
  have instantiated : Below S.R Γ (inst0 a E) (inst0 a B₀) :=
    Derivable.substitutes codomains (SubstMor.single typedArgument')
  exact ⟨typedArgument', .subTrans instantiated (TypeLe.toBelow le (Typed.isType (S := S) typed formed))⟩

include facts roots heads algebra complete in
/-- **Decomposition of a scoped equation**: `λ x̄. h a ≐ λ x̄. h b`, with `h` a local of the
telescope of function type and the equation at a rigid base type, has exactly the solutions of
`λ x̄. a ≐ λ x̄. b` at the domain of `h`, in every future context. -/
theorem decompose_scoped {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (head : scope.Local) {E : Tm Head (scope.target.arity + 1)} (equation argument : Active scope.target)
    (headType : Ctx.lookup scope.target.raw (scope.localIndex head) = .pi argument.type.code E)
    (leftCode : equation.left.code = .app (.var (scope.localIndex head)) argument.left.code)
    (rightCode : equation.right.code = .app (.var (scope.localIndex head)) argument.right.code)
    (base : RigidBase scope equation.type.code) {Δ : Context S.R} (solution : Δ ⟶ Γ) :
    (scope.toScoped equation).Holds solution ↔ (scope.toScoped argument).Holds solution := by
  rw [Spine.toScoped_holds_iff, Spine.toScoped_holds_iff]
  have typedLeft := equation.left.typed
  rw [leftCode] at typedLeft
  obtain ⟨_, below⟩ := application_below facts scope.target.formed (scope.localIndex head) headType typedLeft
  have headTyped := (scope.map solution).typed (scope.localIndex head)
  rw [headType, map_localRead scope solution head head] at headTyped
  have mapped : ∀ code : Tm Head scope.target.arity,
      Presentation.subst (scope.map solution).substitution (.app (.var (scope.localIndex head)) code) =
        .app (.var (localRead scope solution head (scope.localIndex head))) (Presentation.subst (scope.map solution).substitution code) := by
    intro code
    change Tm.app ((scope.map solution).substitution (scope.localIndex head))
      (Presentation.subst (scope.map solution).substitution code) = _
    rw [map_localRead scope solution head head]
  change Equal S.R (scope.reindex solution).target.raw (Presentation.subst (scope.map solution).substitution equation.left.code)
      (Presentation.subst (scope.map solution).substitution equation.right.code) (Presentation.subst (scope.map solution).substitution equation.type.code) ↔
    Equal S.R (scope.reindex solution).target.raw (Presentation.subst (scope.map solution).substitution argument.left.code)
      (Presentation.subst (scope.map solution).substitution argument.right.code) (Presentation.subst (scope.map solution).substitution argument.type.code)
  rw [leftCode, rightCode, mapped, mapped]
  have below' : Below S.R (scope.reindex solution).target.raw
      (Presentation.subst (scope.map solution).substitution (inst0 argument.left.code E))
      (Presentation.subst (scope.map solution).substitution equation.type.code) :=
    Derivable.substitutes below (scope.map solution).typed
  rw [subst_inst0] at below'
  constructor
  · intro same
    exact equal_arguments_of_base facts roots heads algebra complete (scope.reindex solution).target.formed _
      (Typed.generation headTyped) (Typed.isType (S := S) headTyped (scope.reindex solution).target.formed)
      (base.subst solution) same
  · intro same
    exact .subEq (.appCong (.refl headTyped) same) below'

end ContextualDependentRigidDecomposition
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
