import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeHeads
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRank
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPiShape

/-!
# The inclusion of one universe in the next is injective on codes

In a cumulative tower a code of a universe is a code of every larger universe, and two codes can be compared at any
universe that holds both. The comparison does not depend on that choice.

* **Equal types are equal at every universe at which both are typed** (`equal_at_universe`): the η-long normal forms
  of the two types agree up to heads (`long_type_unique`), and a normal type is equal to a type that is the same up
  to heads at every universe at which it is typed (`Long.sameEqual`).
* **The inclusion of a universe in a larger one is injective on codes** (`universe_injective`): two terms typed at a
  universe and equal at another universe are equal at the first.
* **Under a telescope** (`Lowers`, `Lowers.reflects`): `Π x̄. U` below `Π x̄. V` with the same binders. Two terms of
  the smaller type that are equal at the larger are equal at the smaller, by η for functions.
* The smaller type is usable at the larger (`Lowers.usable`), so the two equalities are equivalent on terms of the
  smaller type (`Lowers.equal_iff`); the relation is kept by substitution (`Lowers.subst`).
* **Normal forms** (`Lowers.long`, `Lowers.normalForm`): an η-long normal form at the smaller type is one at the
  larger type, so the normal weight of a term is the same at both.

Reading: the universe written on an equation between two types carries no information beyond "both sides are types
of it". The least universe that holds both sides is a normal form of the annotation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentUniverseInjective

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentEtaLong ContextualDependentCumulative ContextualDependentRank

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## The telescope relation -/

/-- **`small` is `large` with the universe at the end of its telescope of Π types lowered.** -/
inductive Lowers (R : Rules Head) : {n : Nat} → Tm Head n → Tm Head n → Prop where
  | sort {n : Nat} {u v : Head} : R.isUniverse u → R.isUniverse v → R.cumulative u v →
      Lowers R (.head u : Tm Head n) (.head v)
  | pi {n : Nat} {A : Tm Head n} {small large : Tm Head (n + 1)} :
      Lowers R small large → Lowers R (.pi A small) (.pi A large)

/-- The relation is kept by substitution. -/
theorem Lowers.subst {R : Rules Head} {n : Nat} {small large : Tm Head n} (lowers : Lowers R small large) :
    ∀ {m : Nat} (σ : Sub Head n m), Lowers R (Presentation.subst σ small) (Presentation.subst σ large) := by
  induction lowers with
  | sort hu hv c => intro m σ; exact .sort hu hv c
  | pi _ ih => intro m σ; exact .pi (ih (liftSub σ))

/-- **Equality at the larger type of two terms of the smaller type holds at the smaller type.** -/
def Reflects (R : Rules Head) {n : Nat} (Γ : Ctx Head n) (small large : Tm Head n) : Prop :=
  CtxFormed R Γ → ∀ {s t : Tm Head n}, Typed R Γ s small → Typed R Γ t small → Equal R Γ s t large →
    Equal R Γ s t small

/-- **Under a binder**: by η for functions, from the applications to a fresh variable. -/
theorem Reflects.pi {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {small large : Tm Head (n + 1)}
    (inner : Reflects S.R (.snoc Γ A) small large) : Reflects S.R Γ (.pi A small) (.pi A large) := by
  intro formed s t ts tt equal
  obtain ⟨u, _, tPi⟩ := Typed.isType ts formed
  have generation : GenerationAt S.R _ (.pi _ _) (.head u) := Typed.generation tPi
  obtain ⟨u₁, _, _, tA, hu₁, _, _, _, _⟩ := generation
  refine .etaPi ts tt (inner (formed.snoc ⟨u₁, hu₁, tA⟩) ?_ ?_ ?_)
  · have applied := Derivable.appElim (ts.rename (CtxRen.wk Γ A))
      (Derivable.var (R := S.R) (Γ := .snoc Γ A) 0)
    simpa only [Presentation.rename, Ctx.lookup, Products.fresh_instantiation] using applied
  · have applied := Derivable.appElim (tt.rename (CtxRen.wk Γ A))
      (Derivable.var (R := S.R) (Γ := .snoc Γ A) 0)
    simpa only [Presentation.rename, Ctx.lookup, Products.fresh_instantiation] using applied
  · have compared := Derivable.appCong (equal.rename (CtxRen.wk Γ A))
      (Derivable.refl (Derivable.var (R := S.R) (Γ := .snoc Γ A) 0))
    simpa only [Presentation.rename, Ctx.lookup, Products.fresh_instantiation] using compared

/-- **The smaller type is usable at the larger.** -/
theorem Lowers.usable {n : Nat} {small large : Tm Head n} (lowers : Lowers S.R small large) :
    ∀ {Γ : Ctx Head n}, IsType S.R Γ small → IsType S.R Γ large → Below S.R Γ small large := by
  induction lowers with
  | sort _ _ c => intro Γ _ _; exact .subUniv c
  | pi _ ih =>
      intro Γ isSmall isLarge
      obtain ⟨u, hu, tSmall⟩ := isSmall
      obtain ⟨v, hv, tLarge⟩ := isLarge
      have first : GenerationAt S.R _ (.pi _ _) (.head u) := Typed.generation tSmall
      have second : GenerationAt S.R _ (.pi _ _) (.head v) := Typed.generation tLarge
      obtain ⟨u₁, u₂, _, tA, hu₁, tB, hu₂, _, _⟩ := first
      obtain ⟨_, v₂, _, _, _, tB', hv₂, _, _⟩ := second
      exact .subPi tSmall hu tLarge hv (.refl tA) hu₁ (ih ⟨u₂, hu₂, tB⟩ ⟨v₂, hv₂, tB'⟩)

section Universe

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
include facts roots heads algebra rigid complete

/-- **Equal types are equal at every universe at which both are typed.** -/
theorem equal_at_universe {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {s t : Tm Head n} {u : Head}
    (hu : S.R.isUniverse u) (ts : Typed S.R Γ s (.head u)) (tt : Typed S.R Γ t (.head u))
    (equal : TypeEq S.R Γ s t) : Equal S.R Γ s t (.head u) := by
  obtain ⟨Z, lZ, atZ⟩ := long_type_exists facts roots heads algebra rigid complete formed ⟨u, hu, ts⟩
  obtain ⟨W, lW, atW⟩ := long_type_exists facts roots heads algebra rigid complete formed ⟨u, hu, tt⟩
  obtain ⟨tZ, eZ⟩ := atZ hu ts
  obtain ⟨_, eW⟩ := atW hu tt
  have sZ : TypeEq S.R Γ s Z := ⟨u, hu, eZ⟩
  have tW : TypeEq S.R Γ t W := ⟨u, hu, eW⟩
  have same := long_type_unique facts roots heads algebra complete formed lZ lW
    (TypeEq.trans S.levels (TypeEq.trans S.levels sZ.symm equal) tW)
  exact .trans eZ (.trans (Long.sameEqual facts heads lZ formed same hu tZ) (.symm eW))

/-- **The inclusion of a universe in a larger one is injective on codes**: two terms typed at a universe and equal
at another universe are equal at the first. No order between the two universes is assumed. -/
theorem universe_injective {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {s t : Tm Head n} {u v : Head}
    (hu : S.R.isUniverse u) (hv : S.R.isUniverse v) (ts : Typed S.R Γ s (.head u)) (tt : Typed S.R Γ t (.head u))
    (equal : Equal S.R Γ s t (.head v)) : Equal S.R Γ s t (.head u) :=
  equal_at_universe facts roots heads algebra rigid complete formed hu ts tt ⟨v, hv, equal⟩

/-- **Under a telescope**: two terms of the smaller type that are equal at the larger are equal at the smaller. -/
theorem Lowers.reflects {n : Nat} {small large : Tm Head n} (lowers : Lowers S.R small large) :
    ∀ {Γ : Ctx Head n}, Reflects S.R Γ small large := by
  induction lowers with
  | sort hu hv _ =>
      intro Γ formed s t ts tt equal
      exact universe_injective facts roots heads algebra rigid complete formed hu hv ts tt equal
  | pi _ ih => intro Γ; exact Reflects.pi ih

/-- **The two equalities are equivalent** on terms of the smaller type. -/
theorem Lowers.equal_iff {n : Nat} {small large : Tm Head n} (lowers : Lowers S.R small large) {Γ : Ctx Head n}
    (formed : CtxFormed S.R Γ) (isSmall : IsType S.R Γ small) (isLarge : IsType S.R Γ large) {s t : Tm Head n}
    (ts : Typed S.R Γ s small) (tt : Typed S.R Γ t small) :
    Equal S.R Γ s t large ↔ Equal S.R Γ s t small :=
  ⟨lowers.reflects facts roots heads algebra rigid complete formed ts tt,
    fun equal => .subEq equal (lowers.usable isSmall isLarge)⟩

omit roots heads algebra rigid complete in
/-- **An η-long normal form at the smaller type is one at the larger type.** -/
theorem Lowers.long {n : Nat} {small large : Tm Head n} (lowers : Lowers S.R small large) :
    ∀ {Γ : Ctx Head n} {v : Tm Head n}, CtxFormed S.R Γ → IsType S.R Γ small → IsType S.R Γ large →
      Long S.R S.roles (.term Γ v small) → Long S.R S.roles (.term Γ v large) := by
  induction lowers with
  | @sort n u w hu hw c =>
      intro Γ v formed _ _ long
      cases long with
      | univ _ _ typed lv => exact .univ hw (universe_typeEq (S := S) Γ hw) (Derivable.cumul typed c) lv
      | lam e _ _ _ => exact absurd e.symm (TypeEq.pi_ne_head facts formed)
      | pair e _ _ _ => exact absurd e.symm (TypeEq.sigma_ne_head facts formed)
      | refl e _ _ => exact absurd e.symm (TypeEq.id_ne_head facts formed)
      | neutral ls le typed _ =>
          exact .neutral ls (.subTrans le (.subUniv c)) (Derivable.cumul typed c)
            ⟨fun _ _ e => TypeEq.pi_ne_head facts formed e.symm, fun _ _ e => TypeEq.sigma_ne_head facts formed e.symm⟩
  | @pi n A small large inner ih =>
      intro Γ v formed isSmall isLarge long
      have typedLarge : Typed S.R Γ v (.pi A large) :=
        .sub long.typed ((Lowers.pi inner).usable isSmall isLarge)
      obtain ⟨u, hu, tSmall⟩ := isSmall
      obtain ⟨w, hw, tLarge⟩ := isLarge
      have first : GenerationAt S.R _ (.pi _ _) (.head u) := Typed.generation tSmall
      have second : GenerationAt S.R _ (.pi _ _) (.head w) := Typed.generation tLarge
      obtain ⟨u₁, u₂, _, tA, hu₁, tB, hu₂, _, _⟩ := first
      obtain ⟨_, w₂, _, _, _, tB', hw₂, _, _⟩ := second
      have isA : IsType S.R Γ A := ⟨u₁, hu₁, tA⟩
      cases long with
      | univ _ e _ _ => exact absurd e (TypeEq.pi_ne_head facts formed)
      | lam e _ _ lb =>
          obtain ⟨eA, eB⟩ := TypeEq.pi_injective facts e formed
          have there := CtxEq.snoc (CtxEq.refl Γ formed) eA
          have back := CtxEq.snoc (CtxEq.refl Γ formed) eA.symm
          have moved := (lb.stable S.levels there back).convType S.levels eB.symm
          exact .lam (IsType.refl ⟨w, hw, tLarge⟩) isA typedLarge
            (ih (formed.snoc isA) ⟨u₂, hu₂, tB⟩ ⟨w₂, hw₂, tB'⟩ moved)
      | pair e _ _ _ => exact absurd e (TypeEq.pi_ne_sigma facts formed)
      | refl e _ _ => exact absurd e (TypeEq.pi_ne_id facts formed)
      | neutral _ _ _ base => exact absurd (IsType.refl ⟨u, hu, tSmall⟩) (base.1 A small)

omit roots heads algebra rigid complete in
/-- **A normal form at the smaller type is a normal form at the larger type.** -/
theorem Lowers.normalForm {n : Nat} {small large : Tm Head n} (lowers : Lowers S.R small large) {Γ : Ctx Head n}
    (formed : CtxFormed S.R Γ) (isSmall : IsType S.R Γ small) (isLarge : IsType S.R Γ large) {t v : Tm Head n}
    (normal : NormalForm S.R S.roles Γ t v small) : NormalForm S.R S.roles Γ t v large :=
  ⟨lowers.long facts formed isSmall isLarge normal.1,
    .subEq normal.2 (lowers.usable isSmall isLarge)⟩

end Universe

end ContextualDependentUniverseInjective
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
