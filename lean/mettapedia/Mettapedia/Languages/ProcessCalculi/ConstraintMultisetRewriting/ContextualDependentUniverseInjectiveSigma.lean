import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUniverseInjective

/-!
# The inclusion of universes is injective through the components of Σ types

`ContextualDependentUniverseInjective.Lowers` lowers the universe at the end of a telescope of Π types. A universe
can also be written above a declaration at a component of a Σ type: an unknown `p : Σ (_ : U0). U0` is equated at
`Σ (_ : U0). U1`. This module states the relation that reaches those positions and proves that it reflects
equality.

* `LowersWithin`: `small` is `large` with one universe lowered, at the end of a telescope of Π types or at a
  component of a Σ type, nested.
* **`LowersWithin.reflects`**: two terms of the smaller type that are equal at the larger type are equal at the
  smaller. The statement is generalized over substitutions, because the second component of a Σ type is read at an
  instance.
* `LowersWithin.usable`, **`LowersWithin.equal_iff`**: the smaller type is usable at the larger, so an equation
  between two terms of the smaller type has the same solutions read at either type.
* `Lowers.within`: the telescope relation is a case of it. `Lowers.not_sigma`: the telescope relation does not reach
  a component of a Σ type (negative control); `LowersWithin.pairs` (positive control).

* `LowersWithin.long`, `LowersWithin.normalForm`: an η-long normal form at the smaller type is one at the larger
  type, so a side keeps its normal weight when the equation is read at the smaller type.

These are the statements the reading at the least annotation (`ContextualDependentEtaDepth.lowerUpdate`) uses of
`Lowers`. That reading is built on `Lowers` and does not use this relation: the search for the lowered annotation
through the components of a Σ type and the round are not done for it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentUniverseInjective

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEtaLong ContextualDependentCumulative ContextualDependentRank

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **`small` is `large` with one universe lowered**, at the end of a telescope of Π types or at a component of a
Σ type, nested. -/
inductive LowersWithin (R : Rules Head) : {n : Nat} → Tm Head n → Tm Head n → Prop where
  | sort {n : Nat} {u v : Head} : R.isUniverse u → R.isUniverse v → R.cumulative u v →
      LowersWithin R (.head u : Tm Head n) (.head v)
  | pi {n : Nat} {A : Tm Head n} {small large : Tm Head (n + 1)} :
      LowersWithin R small large → LowersWithin R (.pi A small) (.pi A large)
  | sigmaFirst {n : Nat} {small large : Tm Head n} {B : Tm Head (n + 1)} :
      LowersWithin R small large → LowersWithin R (.sigma small B) (.sigma large B)
  | sigmaSecond {n : Nat} {A : Tm Head n} {small large : Tm Head (n + 1)} :
      LowersWithin R small large → LowersWithin R (.sigma A small) (.sigma A large)

/-- The telescope relation is a case of the relation. -/
theorem Lowers.within {R : Rules Head} {n : Nat} {small large : Tm Head n} (lowers : Lowers R small large) :
    LowersWithin R small large := by
  induction lowers with
  | sort hu hv c => exact .sort hu hv c
  | pi _ ih => exact .pi ih

/-- The relation is kept by substitution. -/
theorem LowersWithin.subst {R : Rules Head} {n : Nat} {small large : Tm Head n}
    (lowers : LowersWithin R small large) :
    ∀ {m : Nat} (σ : Sub Head n m), LowersWithin R (Presentation.subst σ small) (Presentation.subst σ large) := by
  induction lowers with
  | sort hu hv c => intro m σ; exact .sort hu hv c
  | pi _ ih => intro m σ; exact .pi (ih (liftSub σ))
  | sigmaFirst _ ih => intro m σ; exact .sigmaFirst (ih σ)
  | sigmaSecond _ ih => intro m σ; exact .sigmaSecond (ih (liftSub σ))

/-- **Negative control**: the telescope relation does not reach a component of a Σ type. -/
theorem Lowers.not_sigma {R : Rules Head} {n : Nat} {A A' : Tm Head n} {B B' : Tm Head (n + 1)} :
    ¬ Lowers R (.sigma A B) (.sigma A' B') := by
  intro lowers
  cases lowers

/-- **Positive control**: a pair type of two universes, with its second component lowered. -/
theorem LowersWithin.pairs {R : Rules Head} {n : Nat} {u v : Head} (hu : R.isUniverse u) (hv : R.isUniverse v)
    (c : R.cumulative u v) :
    LowersWithin R (.sigma (.head u) (.head u) : Tm Head n) (.sigma (.head u) (.head v)) :=
  .sigmaSecond (.sort hu hv c)

/-- **The smaller type is usable at the larger.** -/
theorem LowersWithin.usable {n : Nat} {small large : Tm Head n} (lowers : LowersWithin S.R small large) :
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
  | sigmaFirst _ ih =>
      intro Γ isSmall isLarge
      obtain ⟨u, hu, tSmall⟩ := isSmall
      obtain ⟨v, hv, tLarge⟩ := isLarge
      have first : GenerationAt S.R _ (.sigma _ _) (.head u) := Typed.generation tSmall
      have second : GenerationAt S.R _ (.sigma _ _) (.head v) := Typed.generation tLarge
      obtain ⟨u₁, u₂, _, tA, hu₁, tB, hu₂, _, _⟩ := first
      obtain ⟨v₁, _, _, tA', hv₁, _, _, _, _⟩ := second
      exact .subSigma tSmall hu tLarge hv (ih ⟨u₁, hu₁, tA⟩ ⟨v₁, hv₁, tA'⟩) (.subEqual (.refl tB) hu₂)
  | sigmaSecond _ ih =>
      intro Γ isSmall isLarge
      obtain ⟨u, hu, tSmall⟩ := isSmall
      obtain ⟨v, hv, tLarge⟩ := isLarge
      have first : GenerationAt S.R _ (.sigma _ _) (.head u) := Typed.generation tSmall
      have second : GenerationAt S.R _ (.sigma _ _) (.head v) := Typed.generation tLarge
      obtain ⟨u₁, u₂, _, tA, hu₁, tB, hu₂, _, _⟩ := first
      obtain ⟨_, v₂, _, _, _, tB', hv₂, _, _⟩ := second
      exact .subSigma tSmall hu tLarge hv (.subEqual (.refl tA) hu₁) (ih ⟨u₂, hu₂, tB⟩ ⟨v₂, hv₂, tB'⟩)

section Universe

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
include facts roots heads algebra rigid complete

/-- **Two terms of the smaller type that are equal at the larger type are equal at the smaller**, at every
instance of the two types. -/
theorem LowersWithin.reflects {n : Nat} {small large : Tm Head n} (lowers : LowersWithin S.R small large) :
    ∀ {m : Nat} (σ : Sub Head n m) {Γ : Ctx Head m},
      Reflects S.R Γ (Presentation.subst σ small) (Presentation.subst σ large) := by
  induction lowers with
  | sort hu hv _ =>
      intro m σ Γ formed s t ts tt equal
      exact universe_injective facts roots heads algebra rigid complete formed hu hv ts tt equal
  | @pi n A small large _ ih =>
      intro m σ Γ
      show Reflects S.R Γ (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) small))
        (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) large))
      exact Reflects.pi (ih (liftSub σ))
  | @sigmaFirst n small large B _ ih =>
      intro m σ Γ formed s t ts tt equal
      have ts' : Typed S.R Γ s (.sigma (Presentation.subst σ small) (Presentation.subst (liftSub σ) B)) := ts
      have tt' : Typed S.R Γ t (.sigma (Presentation.subst σ small) (Presentation.subst (liftSub σ) B)) := tt
      have equal' : Equal S.R Γ s t
          (.sigma (Presentation.subst σ large) (Presentation.subst (liftSub σ) B)) := equal
      exact .etaSigma ts' tt'
        (ih σ formed (Derivable.fstElim ts') (Derivable.fstElim tt') (Derivable.fstCong equal'))
        (Derivable.sndCong equal')
  | @sigmaSecond n A small large _ ih =>
      intro m σ Γ formed s t ts tt equal
      have ts' : Typed S.R Γ s (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) small)) := ts
      have tt' : Typed S.R Γ t (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) small)) := tt
      have equal' : Equal S.R Γ s t
          (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) large)) := equal
      obtain ⟨u, _, tSigma⟩ := Typed.isType ts' formed
      have generation : GenerationAt S.R _ (.sigma _ _) (.head u) := Typed.generation tSigma
      obtain ⟨_, u₂, _, _, _, tB, hu₂, _, _⟩ := generation
      have firsts : Equal S.R Γ (.fst s) (.fst t) (Presentation.subst σ A) := Derivable.fstCong equal'
      have typedSnd : Typed S.R Γ (.snd t) (inst0 (.fst s) (Presentation.subst (liftSub σ) small)) :=
        Typed.convType (Derivable.sndElim tt')
          ⟨u₂, hu₂, .symm (Typed.instantiateEq tB (Derivable.fstElim ts') firsts)⟩
      have typedFst : Typed S.R Γ (.snd s) (inst0 (.fst s) (Presentation.subst (liftSub σ) small)) :=
        Derivable.sndElim ts'
      have seconds : Equal S.R Γ (.snd s) (.snd t) (inst0 (.fst s) (Presentation.subst (liftSub σ) large)) :=
        Derivable.sndCong equal'
      rw [inst0_subst_liftSub] at typedSnd typedFst seconds
      have inner := ih (consSub (.fst s) σ) formed typedFst typedSnd seconds
      rw [← inst0_subst_liftSub] at inner
      exact .etaSigma ts' tt' firsts inner

/-- **The two equalities are equivalent** on terms of the smaller type: an equation between two terms of the
smaller type has the same solutions read at either type. -/
theorem LowersWithin.equal_iff {n : Nat} {small large : Tm Head n} (lowers : LowersWithin S.R small large)
    {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (isSmall : IsType S.R Γ small) (isLarge : IsType S.R Γ large)
    {s t : Tm Head n} (ts : Typed S.R Γ s small) (tt : Typed S.R Γ t small) :
    Equal S.R Γ s t large ↔ Equal S.R Γ s t small := by
  have reflected := lowers.reflects facts roots heads algebra rigid complete (ids (Head := Head)) (Γ := Γ)
  rw [subst_ids, subst_ids] at reflected
  exact ⟨fun equal => reflected formed ts tt equal, fun equal => .subEq equal (lowers.usable isSmall isLarge)⟩

omit roots heads algebra rigid complete in
/-- **An η-long normal form at the smaller type is one at the larger type**, at every instance of the two types. -/
theorem LowersWithin.long {n : Nat} {small large : Tm Head n} (lowers : LowersWithin S.R small large) :
    ∀ {m : Nat} (σ : Sub Head n m) {Γ : Ctx Head m} {v : Tm Head m}, CtxFormed S.R Γ →
      IsType S.R Γ (Presentation.subst σ small) → IsType S.R Γ (Presentation.subst σ large) →
      Long S.R S.roles (.term Γ v (Presentation.subst σ small)) →
      Long S.R S.roles (.term Γ v (Presentation.subst σ large)) := by
  induction lowers with
  | @sort n u w hu hw c =>
      intro m σ Γ v formed _ _ long
      have long' : Long S.R S.roles (.term Γ v (.head u)) := long
      show Long S.R S.roles (.term Γ v (.head w))
      cases long' with
      | univ _ _ typed lv => exact .univ hw (universe_typeEq (S := S) Γ hw) (Derivable.cumul typed c) lv
      | lam e _ _ _ => exact absurd e.symm (TypeEq.pi_ne_head facts formed)
      | pair e _ _ _ => exact absurd e.symm (TypeEq.sigma_ne_head facts formed)
      | refl e _ _ => exact absurd e.symm (TypeEq.id_ne_head facts formed)
      | neutral ls le typed _ =>
          exact .neutral ls (.subTrans le (.subUniv c)) (Derivable.cumul typed c)
            ⟨fun _ _ e => TypeEq.pi_ne_head facts formed e.symm, fun _ _ e => TypeEq.sigma_ne_head facts formed e.symm⟩
  | @pi n A small large inner ih =>
      intro m σ Γ v formed isSmall isLarge long
      have below := ((LowersWithin.pi (A := A) inner).subst σ).usable isSmall isLarge
      have isSmall' : IsType S.R Γ
          (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) small)) := isSmall
      have isLarge' : IsType S.R Γ
          (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) large)) := isLarge
      have long' : Long S.R S.roles
          (.term Γ v (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) small))) := long
      have typedLarge : Typed S.R Γ v
          (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) large)) := .sub long'.typed below
      obtain ⟨u, hu, tSmall⟩ := isSmall'
      obtain ⟨w, hw, tLarge⟩ := isLarge'
      have first : GenerationAt S.R _ (.pi _ _) (.head u) := Typed.generation tSmall
      have second : GenerationAt S.R _ (.pi _ _) (.head w) := Typed.generation tLarge
      obtain ⟨u₁, u₂, _, tA, hu₁, tB, hu₂, _, _⟩ := first
      obtain ⟨_, w₂, _, _, _, tB', hw₂, _, _⟩ := second
      have isA : IsType S.R Γ (Presentation.subst σ A) := ⟨u₁, hu₁, tA⟩
      show Long S.R S.roles
        (.term Γ v (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) large)))
      cases long' with
      | univ _ e _ _ => exact absurd e (TypeEq.pi_ne_head facts formed)
      | lam e _ _ lb =>
          obtain ⟨eA, eB⟩ := TypeEq.pi_injective facts e formed
          have there := CtxEq.snoc (CtxEq.refl Γ formed) eA
          have back := CtxEq.snoc (CtxEq.refl Γ formed) eA.symm
          have moved := (lb.stable S.levels there back).convType S.levels eB.symm
          exact .lam (IsType.refl ⟨w, hw, tLarge⟩) isA typedLarge
            (ih (liftSub σ) (formed.snoc isA) ⟨u₂, hu₂, tB⟩ ⟨w₂, hw₂, tB'⟩ moved)
      | pair e _ _ _ => exact absurd e (TypeEq.pi_ne_sigma facts formed)
      | refl e _ _ => exact absurd e (TypeEq.pi_ne_id facts formed)
      | neutral _ _ _ base => exact absurd (IsType.refl ⟨u, hu, tSmall⟩) (base.1 _ _)
  | @sigmaFirst n small large B inner ih =>
      intro m σ Γ v formed isSmall isLarge long
      have below := ((LowersWithin.sigmaFirst (B := B) inner).subst σ).usable isSmall isLarge
      have isSmall' : IsType S.R Γ
          (.sigma (Presentation.subst σ small) (Presentation.subst (liftSub σ) B)) := isSmall
      have isLarge' : IsType S.R Γ
          (.sigma (Presentation.subst σ large) (Presentation.subst (liftSub σ) B)) := isLarge
      have long' : Long S.R S.roles
          (.term Γ v (.sigma (Presentation.subst σ small) (Presentation.subst (liftSub σ) B))) := long
      have typedLarge : Typed S.R Γ v
          (.sigma (Presentation.subst σ large) (Presentation.subst (liftSub σ) B)) := .sub long'.typed below
      obtain ⟨u, hu, tSmall⟩ := isSmall'
      obtain ⟨w, hw, tLarge⟩ := isLarge'
      have first : GenerationAt S.R _ (.sigma _ _) (.head u) := Typed.generation tSmall
      have second : GenerationAt S.R _ (.sigma _ _) (.head w) := Typed.generation tLarge
      obtain ⟨u₁, _, _, tA, hu₁, _, _, _, _⟩ := first
      obtain ⟨w₁, _, _, tA', hw₁, _, _, _, _⟩ := second
      show Long S.R S.roles
        (.term Γ v (.sigma (Presentation.subst σ large) (Presentation.subst (liftSub σ) B)))
      cases long' with
      | univ _ e _ _ => exact absurd e (TypeEq.sigma_ne_head facts formed)
      | lam e _ _ _ => exact absurd e.symm (TypeEq.pi_ne_sigma facts formed)
      | pair e _ la lb =>
          obtain ⟨eA, eB⟩ := TypeEq.sigma_injective facts e formed
          have la₁ := la.convType S.levels eA.symm
          obtain ⟨x, hx, eBody⟩ := eB
          have eInst : TypeEq S.R Γ (inst0 _ (Presentation.subst (liftSub σ) B)) (inst0 _ _) :=
            ⟨x, hx, eBody.substitute (SubstMor.single la₁.typed)⟩
          exact .pair (IsType.refl ⟨w, hw, tLarge⟩) typedLarge
            (ih σ formed ⟨u₁, hu₁, tA⟩ ⟨w₁, hw₁, tA'⟩ la₁) (lb.convType S.levels eInst.symm)
      | refl e _ _ => exact absurd e (TypeEq.sigma_ne_id facts formed)
      | neutral _ _ _ base => exact absurd (IsType.refl ⟨u, hu, tSmall⟩) (base.2 _ _)
  | @sigmaSecond n A small large inner ih =>
      intro m σ Γ v formed isSmall isLarge long
      have below := ((LowersWithin.sigmaSecond (A := A) inner).subst σ).usable isSmall isLarge
      have isSmall' : IsType S.R Γ
          (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) small)) := isSmall
      have isLarge' : IsType S.R Γ
          (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) large)) := isLarge
      have long' : Long S.R S.roles
          (.term Γ v (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) small))) := long
      have typedLarge : Typed S.R Γ v
          (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) large)) := .sub long'.typed below
      obtain ⟨u, hu, tSmall⟩ := isSmall'
      obtain ⟨w, hw, tLarge⟩ := isLarge'
      have first : GenerationAt S.R _ (.sigma _ _) (.head u) := Typed.generation tSmall
      have second : GenerationAt S.R _ (.sigma _ _) (.head w) := Typed.generation tLarge
      obtain ⟨_, u₂, _, _, _, tB, hu₂, _, _⟩ := first
      obtain ⟨_, w₂, _, _, _, tB', hw₂, _, _⟩ := second
      show Long S.R S.roles
        (.term Γ v (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) large)))
      cases long' with
      | univ _ e _ _ => exact absurd e (TypeEq.sigma_ne_head facts formed)
      | lam e _ _ _ => exact absurd e.symm (TypeEq.pi_ne_sigma facts formed)
      | pair e _ la lb =>
          obtain ⟨eA, eB⟩ := TypeEq.sigma_injective facts e formed
          have la₁ := la.convType S.levels eA.symm
          have single := SubstMor.single la₁.typed
          obtain ⟨x, hx, eBody⟩ := eB
          have eInst : TypeEq S.R Γ (inst0 _ (Presentation.subst (liftSub σ) small)) (inst0 _ _) :=
            ⟨x, hx, eBody.substitute single⟩
          have lb₁ : Long S.R S.roles (.term Γ _ (inst0 _ (Presentation.subst (liftSub σ) small))) :=
            lb.convType S.levels eInst.symm
          have isS : IsType S.R Γ (inst0 _ (Presentation.subst (liftSub σ) small)) :=
            ⟨u₂, hu₂, tB.substitute single⟩
          have isL : IsType S.R Γ (inst0 _ (Presentation.subst (liftSub σ) large)) :=
            ⟨w₂, hw₂, tB'.substitute single⟩
          rw [inst0_subst_liftSub] at lb₁ isS isL
          have lb₂ := ih (consSub _ σ) formed isS isL lb₁
          rw [← inst0_subst_liftSub] at lb₂
          exact .pair (IsType.refl ⟨w, hw, tLarge⟩) typedLarge la₁ lb₂
      | refl e _ _ => exact absurd e (TypeEq.sigma_ne_id facts formed)
      | neutral _ _ _ base => exact absurd (IsType.refl ⟨u, hu, tSmall⟩) (base.2 _ _)

omit roots heads algebra rigid complete in
/-- **A normal form at the smaller type is a normal form at the larger type.** -/
theorem LowersWithin.normalForm {n : Nat} {small large : Tm Head n} (lowers : LowersWithin S.R small large)
    {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (isSmall : IsType S.R Γ small) (isLarge : IsType S.R Γ large)
    {t v : Tm Head n} (normal : NormalForm S.R S.roles Γ t v small) : NormalForm S.R S.roles Γ t v large := by
  have long := lowers.long facts (ids (Head := Head)) (Γ := Γ) (v := v) formed
  rw [subst_ids, subst_ids] at long
  exact ⟨long isSmall isLarge normal.1, .subEq normal.2 (lowers.usable isSmall isLarge)⟩

end Universe

end ContextualDependentUniverseInjective
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
