import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentOccursFull

/-!
# The occurs check for an occurrence that a renaming carries back

The occurs checks of the tower refuse `V ≐ T` when the same code `V`, weakened past the binders it lies under,
occurs in `T` along type-former positions. A pattern equation can hold the unknown of its pattern at **other
variables**: `λ x. Q x ≐ λ x. Π (y : A). Q y` holds `Q y` where the pattern is `Q x`. No weakening of `Q x` is `Q y`,
so those checks do not read it; the equation has no solution all the same.

The argument is the one of the occurs checks, with one more step. Let `T` hold a type `V'` along type-former
positions, in the context `Γ'` that the passed codomains extend (`Along`). If a renaming of contexts `ρ : Γ' → Γ`
carries `V'` back to `V`, then the normal form `N'` of `V'` is carried to a normal form of `V` (`Long.type_rename`)
with the same number of nodes (`nodes_rename`), while the normal form of `T` keeps every former it passes and has
strictly more nodes than `N'` (`normal_along`). Equal normal types have the same number of nodes, so `V` is never
equal to `T` (`renamed_occurrence_not_typeEq`).

The renaming need not be injective. For one codomain it is the map that sends the bound variable to a variable `x`
of the declared type of the domain (`mergeAt`, `mergeAt_ctxRen`): `V ≐ Π (y : D). B` and `V ≐ Σ (y : D). B` have no
solution when `B` with `y` replaced by `x` is `V` (`codomain_pattern_not_typeEq`).

A renaming of the whole context of the occurrence is not always there: in `G y ≐ Π (z : y). G x` the bound variable
`z : y` has no image. The two sides are still images of one type under two renamings of contexts, here `G w` over
one variable `w`, and the same count applies (`instances_not_typeEq`).

**Control.** An occurrence that passes no former is not refused: a type is equal to itself (`improper_equal`).

This module states the semantic refutation. It is not a rule of the solver: the reader of the shape from the codes
of an equation, its stability under substitution, and the round are not built here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentOccursRenamed

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentInPlace ContextualDependentRigidFormers ContextualDependentEtaExpansion
open ContextualDependentConversionBudget ContextualDependentEtaLong ContextualDependentOccursCheck
open ContextualDependentRecognitionConversion ContextualDependentOccursFull

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Occurrences along type-former positions, with their contexts -/

/-- **`T` over `Γ` holds `V'` over `Γ'` along type-former positions**: `V'` is `T`, or lies in the domain or the
codomain of a Π or Σ type, or in the carrier of an identity type. A codomain extends the context by its domain. The
flag records that at least one former was passed. -/
inductive Along : Bool → {n : Nat} → Ctx Head n → Tm Head n → {m : Nat} → Ctx Head m → Tm Head m → Prop
  | here {n : Nat} (Γ : Ctx Head n) (T : Tm Head n) : Along false Γ T Γ T
  | domain (isPi : Bool) {proper : Bool} {n m : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
      {Γ' : Ctx Head m} {V' : Tm Head m} : Along proper Γ A Γ' V' → Along true Γ (binder isPi A B) Γ' V'
  | codomain (isPi : Bool) {proper : Bool} {n m : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
      {Γ' : Ctx Head m} {V' : Tm Head m} : Along proper (.snoc Γ A) B Γ' V' → Along true Γ (binder isPi A B) Γ' V'
  | carrier {proper : Bool} {n m : Nat} {Γ : Ctx Head n} {A x y : Tm Head n} {Γ' : Ctx Head m} {V' : Tm Head m} :
      Along proper Γ A Γ' V' → Along true Γ (.id A x y) Γ' V'

section Normal

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **Normal forms along the positions**: the context of the occurrence is formed and the occurrence is a type
there, and for every normal form `N'` of the occurrence, `T` has a normal form with at least as many nodes as `N'`,
and strictly more when a former was passed. -/
theorem normal_along {proper : Bool} {n m : Nat} {Γ : Ctx Head n} {T : Tm Head n} {Γ' : Ctx Head m}
    {V' : Tm Head m} (along : Along proper Γ T Γ' V') :
    CtxFormed S.R Γ → IsType S.R Γ T →
      CtxFormed S.R Γ' ∧ IsType S.R Γ' V' ∧
        ∀ N' : Tm Head m, Long S.R S.roles (.type Γ' N') → TypeEq S.R Γ' V' N' →
          ∃ W, Long S.R S.roles (.type Γ W) ∧ TypeEq S.R Γ T W ∧ nodes N' ≤ nodes W ∧
            (proper = true → nodes N' < nodes W) := by
  induction along with
  | here Γ T =>
      intro formed isType
      exact ⟨formed, isType, fun N' lN VN => ⟨N', lN, VN, le_refl _, fun h => absurd h (by decide)⟩⟩
  | domain isPi _ ih =>
      intro formed isType
      obtain ⟨isA, _⟩ := binder_parts_typed isPi isType
      obtain ⟨formed', isV', build⟩ := ih formed isA
      refine ⟨formed', isV', fun N' lN VN => ?_⟩
      obtain ⟨WA, lWA, AWA, le, _⟩ := build N' lN VN
      obtain ⟨W, lW, TW, larger⟩ :=
        normal_binder facts roots heads algebra rigid complete isPi formed lWA AWA isType
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩
  | codomain isPi _ ih =>
      intro formed isType
      obtain ⟨isA, v, hv, tB⟩ := binder_parts_typed isPi isType
      obtain ⟨formed', isV', build⟩ := ih (formed.snoc isA) ⟨v, hv, tB⟩
      refine ⟨formed', isV', fun N' lN VN => ?_⟩
      obtain ⟨WB, lWB, BWB, le, _⟩ := build N' lN VN
      obtain ⟨W, lW, TW, larger⟩ :=
        normal_codomain facts roots heads algebra rigid complete isPi formed lWB BWB isType
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩
  | carrier _ ih =>
      intro formed isType
      obtain ⟨u, hu, tId⟩ := isType
      obtain ⟨formed', isV', build⟩ := ih formed ⟨u, hu, (id_typed tId).1⟩
      refine ⟨formed', isV', fun N' lN VN => ?_⟩
      obtain ⟨WA, lWA, AWA, le, _⟩ := build N' lN VN
      obtain ⟨W, lW, TW, larger⟩ :=
        normal_carrier facts roots heads algebra rigid complete formed lWA AWA ⟨u, hu, tId⟩
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩

include facts roots heads algebra rigid complete in
/-- **The occurs check for a renamed occurrence**: a type is never equal to a type that holds, past at least one
former, a type that a renaming of contexts carries back to it. -/
theorem renamed_occurrence_not_typeEq {n m : Nat} {Γ : Ctx Head n} {V T : Tm Head n} {Γ' : Ctx Head m}
    {V' : Tm Head m} (along : Along true Γ T Γ' V') {ρ : Ren m n} (compatible : CtxRen Γ' Γ ρ)
    (back : Presentation.rename ρ V' = V) (formed : CtxFormed S.R Γ) (isT : IsType S.R Γ T) :
    ¬ TypeEq S.R Γ V T := by
  intro same
  obtain ⟨formed', isV', build⟩ := normal_along facts roots heads algebra rigid complete along formed isT
  obtain ⟨N', lN', atN'⟩ := long_type_exists facts roots heads algebra rigid complete formed' isV'
  obtain ⟨u, hu, tV'⟩ := isV'
  have VN' : TypeEq S.R Γ' V' N' := ⟨u, hu, (atN' hu tV').2⟩
  obtain ⟨W, lW, TW, _, larger⟩ := build N' lN' VN'
  have lN : Long S.R S.roles (.type Γ (Presentation.rename ρ N')) := lN'.type_rename facts compatible formed' formed
  have VN : TypeEq S.R Γ V (Presentation.rename ρ N') := back ▸ VN'.rename compatible
  have NW : TypeEq S.R Γ (Presentation.rename ρ N') W :=
    TypeEq.trans S.levels VN.symm (TypeEq.trans S.levels same TW)
  have equalNodes := nodes_of_same (long_type_unique facts roots heads algebra complete formed lN lW NW)
  rw [nodes_rename] at equalNodes
  have := larger rfl
  omega

include facts roots heads algebra rigid complete in
/-- **The occurs check for two instances of one type**: let `V` over `Γ` and `V'` over `Γ'` be the images of one
type `P` under two renamings of contexts. A type that holds `V'` past at least one former is never equal to `V`. -/
theorem instances_not_typeEq {n m k : Nat} {Γ : Ctx Head n} {V T : Tm Head n} {Γ' : Ctx Head m} {V' : Tm Head m}
    (along : Along true Γ T Γ' V') {G : Ctx Head k} {P : Tm Head k} {ρ : Ren k n} {ρ' : Ren k m}
    (compatible : CtxRen G Γ ρ) (compatible' : CtxRen G Γ' ρ') (first : Presentation.rename ρ P = V)
    (second : Presentation.rename ρ' P = V') (formedG : CtxFormed S.R G) (isP : IsType S.R G P)
    (formed : CtxFormed S.R Γ) (isT : IsType S.R Γ T) : ¬ TypeEq S.R Γ V T := by
  intro same
  obtain ⟨formed', _, build⟩ := normal_along facts roots heads algebra rigid complete along formed isT
  obtain ⟨N, lN, atN⟩ := long_type_exists facts roots heads algebra rigid complete formedG isP
  obtain ⟨u, hu, tP⟩ := isP
  have PN : TypeEq S.R G P N := ⟨u, hu, (atN hu tP).2⟩
  have lN' : Long S.R S.roles (.type Γ' (Presentation.rename ρ' N)) :=
    lN.type_rename facts compatible' formedG formed'
  have VN' : TypeEq S.R Γ' V' (Presentation.rename ρ' N) := second ▸ PN.rename compatible'
  obtain ⟨W, lW, TW, _, larger⟩ := build _ lN' VN'
  have lN1 : Long S.R S.roles (.type Γ (Presentation.rename ρ N)) := lN.type_rename facts compatible formedG formed
  have VN : TypeEq S.R Γ V (Presentation.rename ρ N) := first ▸ PN.rename compatible
  have NW : TypeEq S.R Γ (Presentation.rename ρ N) W :=
    TypeEq.trans S.levels VN.symm (TypeEq.trans S.levels same TW)
  have equalNodes := nodes_of_same (long_type_unique facts roots heads algebra complete formed lN1 lW NW)
  rw [nodes_rename] at equalNodes
  have more := larger rfl
  rw [nodes_rename] at more
  omega

end Normal

/-! ## One codomain: the bound variable sent to a variable of the domain's type -/

/-- The renaming that sends the newest variable to `x` and keeps the others. -/
def mergeAt {n : Nat} (x : Fin n) : Ren (n + 1) n := fun index => Fin.cases x (fun prior => prior) index

@[simp] theorem mergeAt_zero {n : Nat} (x : Fin n) : mergeAt x 0 = x := rfl

@[simp] theorem mergeAt_succ {n : Nat} (x prior : Fin n) : mergeAt x prior.succ = prior := by
  simp [mergeAt]

omit [UniverseLevel.LevelOrder L] in
/-- Weakening and then merging is the identity. -/
theorem rename_mergeAt_wk {n : Nat} (x : Fin n) (term : Tm Head n) :
    Presentation.rename (mergeAt x) (Presentation.rename wk term) = term := by
  rw [rename_comp]
  have identity : (fun index => mergeAt x (wk index)) = idRen := by
    funext index
    simp [wk, idRen]
  rw [identity, rename_id]

omit [UniverseLevel.LevelOrder L] in
/-- **Merging is a renaming of contexts**, from the context extended by the declared type of `x`. -/
theorem mergeAt_ctxRen {n : Nat} (Γ : Ctx Head n) (x : Fin n) :
    CtxRen (.snoc Γ (Ctx.lookup Γ x)) Γ (mergeAt x) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · show Ctx.lookup Γ x = Presentation.rename (mergeAt x) (Presentation.rename wk (Ctx.lookup Γ x))
    rw [rename_mergeAt_wk]
  · intro prior
    show Ctx.lookup Γ (mergeAt x prior.succ) =
      Presentation.rename (mergeAt x) (Presentation.rename wk (Ctx.lookup Γ prior))
    rw [rename_mergeAt_wk, mergeAt_succ]

section Codomain

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **A pattern against a former that holds it at the bound variable**: `V ≐ Π (y : D). B` and `V ≐ Σ (y : D). B`
never hold when `D` is the declared type of a variable `x` and `B` with `y` replaced by `x` is `V`. -/
theorem codomain_pattern_not_typeEq (isPi : Bool) {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    (x : Fin n) {D V : Tm Head n} {B : Tm Head (n + 1)} (declared : Ctx.lookup Γ x = D)
    (back : Presentation.rename (mergeAt x) B = V) (isT : IsType S.R Γ (binder isPi D B)) :
    ¬ TypeEq S.R Γ V (binder isPi D B) := by
  subst declared
  exact renamed_occurrence_not_typeEq facts roots heads algebra rigid complete (.codomain isPi (.here _ _))
    (mergeAt_ctxRen Γ x) back formed isT

end Codomain

/-- **Control**: an occurrence that passes no former is not refused; a type is equal to itself. -/
theorem improper_equal {n : Nat} {Γ : Ctx Head n} {T : Tm Head n} (isT : IsType S.R Γ T) :
    Along false Γ T Γ T ∧ CtxRen Γ Γ idRen ∧ Presentation.rename idRen T = T ∧ TypeEq S.R Γ T T :=
  ⟨.here Γ T, CtxRen.id Γ, rename_id T, isT.refl⟩

end ContextualDependentOccursRenamed
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
