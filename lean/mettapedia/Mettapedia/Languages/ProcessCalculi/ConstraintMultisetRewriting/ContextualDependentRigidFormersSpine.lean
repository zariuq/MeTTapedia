import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidDecompositionRule
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaExpansion

/-!
# Neutral spines with two arguments

R84 decomposed `λ x̄. h a ≐ λ x̄. h b`, a local applied to one argument at a rigid base type. Here the
local takes **two arguments**, at a non-dependent type `h : (y : D₁) → D₂ → E`: at a rigid base type,
`λ x̄. h a₁ a₂ ≐ λ x̄. h b₁ b₂` has exactly the solutions of `a₁ ≐ b₁` at `D₁` and `a₂ ≐ b₂` at `D₂`,
in every future context (`decompose_two_scoped`): head equality, then argumentwise.

* One direction is spine injectivity: completeness gives an algorithmic derivation, which at a base
  type compares the two spines argument by argument (`head_two`), and soundness turns each argument
  comparison into a typed equality at the domain the head assigns.
* The other is congruence, twice, followed by subsumption to the equation's type (`two_below`).

The **spine rule** decomposes such an equation and examines the decomposed store at once with the
distinct-locals rule, a rigid clash, and the first of the pattern, prune and exchange rules; the
**spine round** extends the occurs-free η round by it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRigidFormers

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentScope ContextualDependentPiSpine ContextualDependentGeneralPattern
open ContextualDependentRigidDecomposition

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- Two applications of one local, each to two arguments. -/
abbrev twice {n : Nat} (head : Fin n) (first second : Tm Head n) : Tm Head n := .app (.app (.var head) first) second

/-- A spine comparison of two double applications of one variable compares the arguments in turn. -/
theorem spinesW_two {n : Nat} {Γ : Ctx Head n} (head : Fin n) {a₁ a₂ b₁ b₂ U : Tm Head n}
    (spines : Algorithmic S.R S.roles (.spinesW Γ (twice head a₁ a₂) (twice head b₁ b₂) U)) :
    ∃ A₁ B₁ A₂ B₂, RedTy S.R S.roles Γ (Ctx.lookup Γ head) (.pi A₁ B₁) ∧
      Algorithmic S.R S.roles (.terms Γ a₁ b₁ A₁) ∧ RedTy S.R S.roles Γ (inst0 a₁ B₁) (.pi A₂ B₂) ∧
      Algorithmic S.R S.roles (.terms Γ a₂ b₂ A₂) := by
  cases spines with
  | spinesW inner _ _ =>
      cases inner with
      | app functions second =>
          cases functions with
          | spinesW inner₁ red₁ _ =>
              cases inner₁ with
              | app headSpines first =>
                  cases headSpines with
                  | spinesW headInner headRed _ =>
                      cases headInner with
                      | var index => exact ⟨_, _, _, _, headRed, first, red₁, second⟩

/-- **Spine injectivity at a base type, two arguments**. -/
theorem head_two {n : Nat} {Γ : Ctx Head n} (head : Fin n) {a₁ a₂ b₁ b₂ C : Tm Head n} (base : BaseType S C)
    (derivation : Algorithmic S.R S.roles (.terms Γ (twice head a₁ a₂) (twice head b₁ b₂) C)) :
    ∃ A₁ B₁ A₂ B₂, RedTy S.R S.roles Γ (Ctx.lookup Γ head) (.pi A₁ B₁) ∧
      Algorithmic S.R S.roles (.terms Γ a₁ b₁ A₁) ∧ RedTy S.R S.roles Γ (inst0 a₁ B₁) (.pi A₂ B₂) ∧
      Algorithmic S.R S.roles (.terms Γ a₂ b₂ A₂) := by
  cases derivation with
  | terms typeRed _ leftRed rightRed inner =>
      have neutral : ∀ x y : Tm Head n, Whnf S.R S.roles (twice head x y) :=
        fun x y => ((Neutral.app (Neutral.app (Neutral.var head))).whnf S.shape)
      have typeSame := WhRed.eq_of_whnf (S := S) base.whnf typeRed.red
      have leftSame := WhRed.eq_of_whnf (S := S) (neutral a₁ a₂) leftRed.red
      have rightSame := WhRed.eq_of_whnf (S := S) (neutral b₁ b₂) rightRed.red
      subst typeSame
      subst leftSame
      subst rightSame
      cases inner with
      | univ _ _ _ types =>
          cases types with
          | neutralTypes _ _ _ spines => exact spinesW_two head spines
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
      | spine _ _ _ _ _ spines => exact spinesW_two head spines

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (complete : AlgorithmicComplete S.R S.roles)


/-- The non-dependent second domain, opened at the first argument. -/
theorem open_second {n : Nat} (a₁ D₂ : Tm Head n) (E : Tm Head (n + 2)) :
    inst0 a₁ (.pi (rename wk D₂) E) = .pi D₂ (Presentation.subst (liftSub (subst0 a₁)) E) := by
  change Tm.pi (inst0 a₁ (rename wk D₂)) (Presentation.subst (liftSub (subst0 a₁)) E) = _
  rw [inst0_rename_wk]

include facts in
/-- **The type of a double application of a local of a non-dependent binary type**: both arguments
at their domains, and the application's type above the codomain instantiated at both. -/
theorem two_below {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (head : Fin n) {D₁ D₂ : Tm Head n}
    {E : Tm Head (n + 2)} (headType : Ctx.lookup Γ head = .pi D₁ (.pi (rename wk D₂) E))
    {a₁ a₂ C : Tm Head n} (typed : Typed S.R Γ (twice head a₁ a₂) C) :
    Typed S.R Γ a₁ D₁ ∧ Typed S.R Γ a₂ D₂ ∧
      Below S.R Γ (inst0 a₂ (Presentation.subst (liftSub (subst0 a₁)) E)) C := by
  obtain ⟨A, B, tF, ta₂, le⟩ := Typed.generation typed
  obtain ⟨ta₁, firstBelow⟩ := application_below facts formed head headType tF
  rw [open_second] at firstBelow
  obtain ⟨domains, codomains⟩ := TypeLe.pi_parts (S := S) facts (TypeLe.of_below firstBelow)
    (Typed.isType (S := S) tF formed) formed
  have ta₂' : Typed S.R Γ a₂ D₂ := Typed.convType ta₂ (TypeEq.symm domains)
  have instantiated : Below S.R Γ (inst0 a₂ (Presentation.subst (liftSub (subst0 a₁)) E)) (inst0 a₂ B) :=
    Derivable.substitutes codomains (SubstMor.single ta₂')
  exact ⟨ta₁, ta₂', .subTrans instantiated (TypeLe.toBelow le (Typed.isType (S := S) typed formed))⟩

include facts roots heads algebra complete in
/-- **Spine injectivity, typed, two arguments**: two double applications of a variable of a
non-dependent binary type that are equal at a base type have equal arguments at the domains. -/
theorem equal_arguments_two {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (head : Fin n)
    {D₁ D₂ : Tm Head n} {E : Tm Head (n + 2)} (headTyped : Typed S.R Γ (.var head) (.pi D₁ (.pi (rename wk D₂) E)))
    {a₁ a₂ b₁ b₂ C : Tm Head n} (base : BaseType S C)
    (same : Equal S.R Γ (twice head a₁ a₂) (twice head b₁ b₂) C) :
    Equal S.R Γ a₁ b₁ D₁ ∧ Equal S.R Γ a₂ b₂ D₂ := by
  obtain ⟨A₁, B₁, A₂, B₂, headRed, firsts, secondRed, seconds⟩ := head_two head base (complete formed same)
  have headLe : TypeLe S.R Γ (Ctx.lookup Γ head) (.pi D₁ (.pi (rename wk D₂) E)) := Typed.generation headTyped
  obtain ⟨s, hs, _, _, toPi⟩ := headRed.sort
  have firstLe : TypeLe S.R Γ (.pi A₁ B₁) (.pi D₁ (.pi (rename wk D₂) E)) := .conv (.symm toPi) hs headLe
  obtain ⟨firstDomains, firstCodomains⟩ := TypeLe.pi_parts (S := S) facts firstLe
    (Typed.isType (S := S) headTyped formed) formed
  have firstsEqual := Algorithmic.sound_terms facts roots heads algebra formed firsts
  have ta₁ := (Algorithmic.terms_typed firsts).1
  have openedBelow : Below S.R Γ (inst0 a₁ B₁) (inst0 a₁ (.pi (rename wk D₂) E)) :=
    Derivable.substitutes firstCodomains (SubstMor.single ta₁)
  rw [open_second] at openedBelow
  obtain ⟨t, ht, _, _, toSecond⟩ := secondRed.sort
  have secondLe : TypeLe S.R Γ (.pi A₂ B₂) (.pi D₂ (Presentation.subst (liftSub (subst0 a₁)) E)) :=
    .conv (.symm toSecond) ht (TypeLe.of_below openedBelow)
  have secondType : IsType S.R Γ (.pi D₂ (Presentation.subst (liftSub (subst0 a₁)) E)) := by
    have opened := Typed.isType (S := S) (Derivable.appElim headTyped (Typed.convType ta₁ firstDomains)) formed
    rw [open_second] at opened
    exact opened
  obtain ⟨secondDomains, _⟩ := TypeLe.pi_parts (S := S) facts secondLe secondType formed
  exact ⟨Equal.convType firstsEqual firstDomains,
    Equal.convType (Algorithmic.sound_terms facts roots heads algebra formed seconds) secondDomains⟩

/-- Substitution commutes with opening the second binder at the first argument. -/
theorem subst_open_second {n m : Nat} (σ : Sub Head n m) (a : Tm Head n) (E : Tm Head (n + 2)) :
    Presentation.subst (liftSub σ) (Presentation.subst (liftSub (subst0 a)) E) =
      Presentation.subst (liftSub (subst0 (Presentation.subst σ a))) (Presentation.subst (liftSub (liftSub σ)) E) := by
  rw [subst_comp, subst_comp]
  apply subst_ext
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · rfl
  · refine Fin.cases ?_ (fun earlier => ?_) prior
    · change Presentation.subst (liftSub σ) (rename wk a) =
        Presentation.subst (liftSub (subst0 (Presentation.subst σ a))) (rename wk (Tm.var 0))
      rw [subst_liftSub_wk, subst_liftSub_wk]
      rfl
    · change Presentation.subst (liftSub σ) (rename wk (Tm.var earlier)) =
        Presentation.subst (liftSub (subst0 (Presentation.subst σ a))) (rename wk (rename wk (σ earlier)))
      rw [subst_liftSub_wk, subst_liftSub_wk]
      change rename wk (σ earlier) = rename wk (inst0 (Presentation.subst σ a) (rename wk (σ earlier)))
      rw [inst0_rename_wk]

include facts roots heads algebra complete in
/-- **Decomposition of a scoped equation, two arguments**: `λ x̄. h a₁ a₂ ≐ λ x̄. h b₁ b₂`, with `h` a
local of the telescope of non-dependent binary type and the equation at a rigid base type, has
exactly the solutions of `λ x̄. a₁ ≐ λ x̄. b₁` and `λ x̄. a₂ ≐ λ x̄. b₂` at the domains of `h`, in every
future context. -/
theorem decompose_two_scoped {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (head : scope.Local) {E : Tm Head (scope.target.arity + 2)} (equation first second : Active scope.target)
    (headType : Ctx.lookup scope.target.raw (scope.localIndex head) =
      .pi first.type.code (.pi (rename wk second.type.code) E))
    (leftCode : equation.left.code = twice (scope.localIndex head) first.left.code second.left.code)
    (rightCode : equation.right.code = twice (scope.localIndex head) first.right.code second.right.code)
    (base : RigidBase scope equation.type.code) {Δ : Context S.R} (solution : Δ ⟶ Γ) :
    (scope.toScoped equation).Holds solution ↔
      (scope.toScoped first).Holds solution ∧ (scope.toScoped second).Holds solution := by
  rw [Spine.toScoped_holds_iff, Spine.toScoped_holds_iff, Spine.toScoped_holds_iff]
  have typedLeft := equation.left.typed
  rw [leftCode] at typedLeft
  obtain ⟨_, _, below⟩ := two_below facts scope.target.formed (scope.localIndex head) headType typedLeft
  have headTyped := (scope.map solution).typed (scope.localIndex head)
  rw [headType, map_localRead scope solution head head] at headTyped
  change Typed S.R (scope.reindex solution).target.raw (.var (localRead scope solution head (scope.localIndex head)))
    (.pi (Presentation.subst (scope.map solution).substitution first.type.code)
      (.pi (Presentation.subst (liftSub (scope.map solution).substitution) (rename wk second.type.code))
        (Presentation.subst (liftSub (liftSub (scope.map solution).substitution)) E))) at headTyped
  rw [subst_liftSub_wk] at headTyped
  have mapped : ∀ x y : Tm Head scope.target.arity,
      Presentation.subst (scope.map solution).substitution (twice (scope.localIndex head) x y) =
        twice (localRead scope solution head (scope.localIndex head))
          (Presentation.subst (scope.map solution).substitution x) (Presentation.subst (scope.map solution).substitution y) := by
    intro x y
    change Tm.app (Tm.app ((scope.map solution).substitution (scope.localIndex head))
      (Presentation.subst (scope.map solution).substitution x)) (Presentation.subst (scope.map solution).substitution y) = _
    rw [map_localRead scope solution head head]
  change Equal S.R (scope.reindex solution).target.raw (Presentation.subst (scope.map solution).substitution equation.left.code)
      (Presentation.subst (scope.map solution).substitution equation.right.code)
      (Presentation.subst (scope.map solution).substitution equation.type.code) ↔
    Equal S.R (scope.reindex solution).target.raw (Presentation.subst (scope.map solution).substitution first.left.code)
        (Presentation.subst (scope.map solution).substitution first.right.code)
        (Presentation.subst (scope.map solution).substitution first.type.code) ∧
      Equal S.R (scope.reindex solution).target.raw (Presentation.subst (scope.map solution).substitution second.left.code)
        (Presentation.subst (scope.map solution).substitution second.right.code)
        (Presentation.subst (scope.map solution).substitution second.type.code)
  rw [leftCode, rightCode, mapped, mapped]
  have below' := Derivable.substitutes below (scope.map solution).typed
  change Below S.R (scope.reindex solution).target.raw
    (Presentation.subst (scope.map solution).substitution
      (inst0 second.left.code (Presentation.subst (liftSub (subst0 first.left.code)) E)))
    (Presentation.subst (scope.map solution).substitution equation.type.code) at below'
  rw [subst_inst0, subst_open_second] at below'
  constructor
  · intro same
    exact equal_arguments_two facts roots heads algebra complete (scope.reindex solution).target.formed _ headTyped
      (base.subst solution) same
  · rintro ⟨firsts, seconds⟩
    have inner := Derivable.appCong (.refl headTyped) firsts
    rw [open_second] at inner
    exact .subEq (Derivable.appCong inner seconds) below'

/-! ## The spine rule -/

section Reading

variable {rules : Rules Head} {Γ : Context rules} {scopeType : TypeOver Γ} (scope : Spine scopeType)

/-- Read `h a₁ a₂` with `h` a rigid local of the telescope. -/
def asTwice : Tm Head scope.target.arity →
    Option (scope.Local × Tm Head scope.target.arity × Tm Head scope.target.arity)
  | .app (.app (.var index) first) second => (localOf scope index).map fun position => (position, first, second)
  | _ => none

omit [UniverseLevel.LevelOrder L] in
theorem asTwice_spec {code : Tm Head scope.target.arity} {position : scope.Local}
    {first second : Tm Head scope.target.arity} (found : asTwice scope code = some (position, first, second)) :
    code = twice (scope.localIndex position) first second := by
  cases code with
  | app function second' =>
      cases function with
      | app inner first' =>
          cases inner with
          | var index =>
              simp only [asTwice, Option.map_eq_some_iff, Prod.mk.injEq] at found
              obtain ⟨position', located, rfl, rfl, rfl⟩ := found
              rw [asLocal_spec scope (show asLocal scope (.var index) = some position' from located)]
          | _ => simp [asTwice] at found
      | _ => simp [asTwice] at found
  | _ => simp [asTwice] at found

end Reading

/-- **A scoped equation between two double applications of one local** of non-dependent binary type,
at a rigid base type, read from its codes. -/
structure TwoShape {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target) where
  head : scope.Local
  left₁ : Tm Head scope.target.arity
  left₂ : Tm Head scope.target.arity
  right₁ : Tm Head scope.target.arity
  right₂ : Tm Head scope.target.arity
  domain₁ : Tm Head scope.target.arity
  domain₂ : Tm Head scope.target.arity
  codomain : Tm Head (scope.target.arity + 2)
  headType : Ctx.lookup scope.target.raw (scope.localIndex head) = .pi domain₁ (.pi (rename wk domain₂) codomain)
  leftCode : active.left.code = twice (scope.localIndex head) left₁ left₂
  rightCode : active.right.code = twice (scope.localIndex head) right₁ right₂
  base : RigidBase scope active.type.code

variable [DecidableEq Head]

omit facts roots heads algebra complete in
/-- Read a double application of one local on both sides; no budget. -/
def twoShape {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType) (active : Active scope.target) :
    Option (TwoShape scope active) :=
  letI := localDecidableEq scope
  match leftFound : asTwice scope active.left.code, rightFound : asTwice scope active.right.code with
  | some (head, a₁, a₂), some (head', b₁, b₂) =>
      if same : head = head' then
        match headShape : Ctx.lookup scope.target.raw (scope.localIndex head) with
        | .pi D₁ (.pi D₂' E) =>
            match ContextualDependentInPlace.strengthenCode D₂' with
            | none => none
            | some D₂ =>
                if base : isRigidBase scope active.type.code = true then
                  some ⟨head, a₁, a₂, b₁, b₂, D₁, D₂.val, E, by rw [headShape, D₂.property],
                    asTwice_spec scope leftFound, by rw [same]; exact asTwice_spec scope rightFound,
                    isRigidBase_spec scope base⟩
                else none
        | _ => none
      else none
  | _, _ => none

omit [DecidableEq Head] in
include facts in
theorem TwoShape.leftTyped {Γ : Context S.R} {scopeType : TypeOver Γ} {scope : Spine scopeType}
    {active : Active scope.target} (shape : TwoShape scope active) :
    Typed S.R scope.target.raw shape.left₁ shape.domain₁ ∧ Typed S.R scope.target.raw shape.left₂ shape.domain₂ := by
  have typed := active.left.typed
  rw [shape.leftCode] at typed
  obtain ⟨first, second, _⟩ := two_below facts scope.target.formed _ shape.headType typed
  exact ⟨first, second⟩

omit [DecidableEq Head] in
include facts in
theorem TwoShape.rightTyped {Γ : Context S.R} {scopeType : TypeOver Γ} {scope : Spine scopeType}
    {active : Active scope.target} (shape : TwoShape scope active) :
    Typed S.R scope.target.raw shape.right₁ shape.domain₁ ∧ Typed S.R scope.target.raw shape.right₂ shape.domain₂ := by
  have typed := active.right.typed
  rw [shape.rightCode] at typed
  obtain ⟨first, second, _⟩ := two_below facts scope.target.formed _ shape.headType typed
  exact ⟨first, second⟩

variable [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (declared : DeclaredTypesFormed S.R) (choices : ExecutableChecking.HeadChoices S.R)
  (reducer : ExecutableReduction.Reducer S.R)

/-- **The two-argument decomposition of one scoped equation**: the two argument equations at the
domains, with exactly the same solutions; only the formation of the domains reads the budget. -/
def decomposeTwoActive (fuel : Nat) {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target) :
    Option {pair : Active scope.target × Active scope.target // ∀ {Δ : Context S.R} (solution : Δ ⟶ Γ),
      (scope.toScoped active).Holds solution ↔
        (scope.toScoped pair.1).Holds solution ∧ (scope.toScoped pair.2).Holds solution} :=
  match twoShape scope active with
  | none => none
  | some shape =>
      (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel scope.target
          shape.domain₁).bind fun first =>
        (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel scope.target
            shape.domain₂).map fun second =>
          let pieces : Active scope.target × Active scope.target :=
            (⟨first.val, ⟨shape.left₁, by rw [first.property]; exact (shape.leftTyped facts).1⟩,
                ⟨shape.right₁, by rw [first.property]; exact (shape.rightTyped facts).1⟩⟩,
              ⟨second.val, ⟨shape.left₂, by rw [second.property]; exact (shape.leftTyped facts).2⟩,
                ⟨shape.right₂, by rw [second.property]; exact (shape.rightTyped facts).2⟩⟩)
          ⟨pieces, fun solution => decompose_two_scoped facts roots heads algebra complete scope shape.head
            active pieces.1 pieces.2 (by rw [shape.headType, first.property, second.property]) shape.leftCode
            shape.rightCode shape.base solution⟩

end ContextualDependentRigidFormers
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
