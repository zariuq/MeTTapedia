import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Widening
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.BelowDecidability
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalChecking

/-!
# Joins of telescopes, and what a wider telescope keeps

Two telescopes that differ only at universe declarations have a **join** (`JoinOf`): the same telescope, with a
least upper bound of the two universes at each such declaration. Both telescopes narrow their join
(`JoinOf.narrows_left`, `JoinOf.narrows_right`).

Narrowing keeps every judgment (`typed_narrow` and its siblings). The converse fails in general: a judgment of the
narrow telescope can mention a type of it only. For **types of the wide telescope**, the judgments a type checker
uses come back:

* **reduction to a weak-head form** (`redTy_wide`): weak-head reduction does not read the telescope, and typing is kept
  along it (`WhRed.preserve`);
* **type equality** (`typeEq_wide`): through the tree's reflection of equality by narrowing
  (`ContextualDependentCumulative.equal_of_narrows`), at a common universe;
* **subtyping** (`below_wide`): by induction on the algorithmic equality of the type with itself, whose cases are the
  shapes of its weak-head form (a universe, a head, a dependent function or pair type, a rigid type). A universe is
  usable at the universes above it; a dependent function type at function types with an equal domain and a codomain
  above; a dependent pair type componentwise; a rigid type at the types equal to it. Each comes back by the two facts
  above, and the codomain by induction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ContextualDependentCumulative

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Joins of telescopes -/

section Join

/-- **`w` is a least upper bound of the universes `u` and `v`.** -/
def IsLub (R : Rules Head) (w u v : Head) : Prop :=
  R.cumulative u w ∧ R.cumulative v w ∧
    ∀ r, R.isUniverse r → R.cumulative u r → R.cumulative v r → R.cumulative w r

/-- **`J` joins `Γ₁` and `Γ₂`**: the same telescope, except at universe declarations, where `J` declares a least
upper bound of the two universes (the larger one when they are comparable). -/
inductive JoinOf (R : Rules Head) : {n : Nat} → Ctx Head n → Ctx Head n → Ctx Head n → Prop where
  | nil : JoinOf R .nil .nil .nil
  | same {n : Nat} {Γ₁ Γ₂ J : Ctx Head n} (A : Tm Head n) : JoinOf R Γ₁ Γ₂ J →
      JoinOf R (.snoc Γ₁ A) (.snoc Γ₂ A) (.snoc J A)
  | join {n : Nat} {Γ₁ Γ₂ J : Ctx Head n} {u v w : Head} : JoinOf R Γ₁ Γ₂ J → R.isUniverse u → R.isUniverse v →
      R.isUniverse w → IsLub R w u v → JoinOf R (.snoc Γ₁ (.head u)) (.snoc Γ₂ (.head v)) (.snoc J (.head w))

variable {S : Setting Head L}

/-- The left telescope narrows the join. -/
theorem JoinOf.narrows_left {n : Nat} {Γ₁ Γ₂ J : Ctx Head n} (j : JoinOf S.R Γ₁ Γ₂ J) : CtxNarrows S.R J Γ₁ := by
  induction j with
  | nil => exact .nil
  | same A _ ih => exact .same A ih
  | join _ _ _ _ lub ih => exact .lower ih lub.1

/-- The right telescope narrows the join. -/
theorem JoinOf.narrows_right {n : Nat} {Γ₁ Γ₂ J : Ctx Head n} (j : JoinOf S.R Γ₁ Γ₂ J) : CtxNarrows S.R J Γ₂ := by
  induction j with
  | nil => exact .nil
  | same A _ ih => exact .same A ih
  | join _ _ _ _ lub ih => exact .lower ih lub.2.1

/-- **A declaration of the join** is the common one, or a least upper bound of the two universes. -/
theorem JoinOf.lookup {n : Nat} {Γ₁ Γ₂ J : Ctx Head n} (j : JoinOf S.R Γ₁ Γ₂ J) :
    ∀ i, (Ctx.lookup J i = Ctx.lookup Γ₁ i ∧ Ctx.lookup Γ₂ i = Ctx.lookup Γ₁ i) ∨
      ∃ u v w, Ctx.lookup Γ₁ i = .head u ∧ Ctx.lookup Γ₂ i = .head v ∧ Ctx.lookup J i = .head w ∧
        S.R.isUniverse u ∧ S.R.isUniverse v ∧ S.R.isUniverse w ∧ IsLub S.R w u v := by
  induction j with
  | nil => intro i; exact i.elim0
  | same A _ ih =>
      intro i
      refine Fin.cases (.inl ⟨rfl, rfl⟩) (fun k => ?_) i
      rw [Ctx.lookup_snoc_succ, Ctx.lookup_snoc_succ, Ctx.lookup_snoc_succ]
      rcases ih k with ⟨eJ, e₂⟩ | ⟨u, v, w, e₁, e₂, eJ, hu, hv, hw, lub⟩
      · exact .inl ⟨by rw [eJ], by rw [e₂]⟩
      · exact .inr ⟨u, v, w, by rw [e₁]; rfl, by rw [e₂]; rfl, by rw [eJ]; rfl, hu, hv, hw, lub⟩
  | join _ hu hv hw lub ih =>
      intro i
      refine Fin.cases (.inr ⟨_, _, _, rfl, rfl, rfl, hu, hv, hw, lub⟩) (fun k => ?_) i
      rw [Ctx.lookup_snoc_succ, Ctx.lookup_snoc_succ, Ctx.lookup_snoc_succ]
      rcases ih k with ⟨eJ, e₂⟩ | ⟨u', v', w', e₁, e₂, eJ, hu', hv', hw', lub'⟩
      · exact .inl ⟨by rw [eJ], by rw [e₂]⟩
      · exact .inr ⟨u', v', w', by rw [e₁]; rfl, by rw [e₂]; rfl, by rw [eJ]; rfl, hu', hv', hw', lub'⟩

/-- The larger of two comparable universes is their least upper bound. -/
theorem isLub_left {u v : Head} (hu : S.R.isUniverse u) (le : S.R.cumulative v u) : IsLub S.R u u v :=
  ⟨S.levels.cumulative_refl hu, le, fun _ _ c _ => c⟩

theorem isLub_right {u v : Head} (hv : S.R.isUniverse v) (le : S.R.cumulative u v) : IsLub S.R v u v :=
  ⟨le, S.levels.cumulative_refl hv, fun _ _ _ c => c⟩

end Join

/-! ## What a wider telescope keeps -/

section Wide

variable {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots in
/-- **Reduction to a weak-head form, in a telescope where the type is a type.** -/
theorem redTy_wide {n : Nat} {W : Ctx Head n} (formedW : CtxFormed S.R W) {X Y : Tm Head n}
    (red : WhRed S.R S.roles X Y) (isX : IsType S.R W X) : RedTy S.R S.roles W X Y := by
  obtain ⟨u, hu, tX⟩ := isX
  obtain ⟨tY, eXY⟩ := WhRed.preserve facts roots formedW red tX
  exact ⟨red, u, hu, tX, tY, eXY⟩

/-- Reduction to a weak-head form is kept by narrowing. -/
theorem RedTy.narrow {n : Nat} {W Γ : Ctx Head n} (narrows : CtxNarrows S.R W Γ) {X Y : Tm Head n}
    (red : RedTy S.R S.roles W X Y) : RedTy S.R S.roles Γ X Y := by
  obtain ⟨u, hu, tX, tY, eXY⟩ := red.sort
  exact ⟨red.red, u, hu, typed_narrow narrows tX, typed_narrow narrows tY, equal_narrow narrows eXY⟩

include facts roots heads algebra rigid complete in
/-- **Type equality comes back to the wide telescope** for types of the wide telescope. -/
theorem typeEq_wide {n : Nat} {W Γ : Ctx Head n} (narrows : CtxNarrows S.R W Γ) (formedW : CtxFormed S.R W)
    (formedΓ : CtxFormed S.R Γ) {X Y : Tm Head n} (isX : IsType S.R W X) (isY : IsType S.R W Y)
    (equal : TypeEq S.R Γ X Y) : TypeEq S.R W X Y := by
  obtain ⟨a, ha, tX⟩ := isX
  obtain ⟨b, hb, tY⟩ := isY
  obtain ⟨w, joined⟩ := S.levels.join_exists ha hb
  obtain ⟨aw, bw⟩ := S.levels.join_upper joined
  have hw := (S.levels.join_level joined).1
  have tXw : Typed S.R W X (.head w) := Derivable.cumul tX aw
  have tYw : Typed S.R W Y (.head w) := Derivable.cumul tY bw
  obtain ⟨u, hu, eXY⟩ := equal
  have atW : Equal S.R Γ X Y (.head w) :=
    ContextualDependentUniverseInjective.universe_injective facts roots heads algebra rigid complete formedΓ hw hu
      (typed_narrow narrows tXw) (typed_narrow narrows tYw) eXY
  exact ⟨w, hw, equal_of_narrows facts roots heads algebra rigid complete narrows formedW formedΓ tXw tYw atW⟩

/-- **Subtyping in a wider telescope**, as a motive over the algorithmic equality of a type with itself. -/
def BelowWide : AlgorithmicStatement Head → Prop
  | .types Γ A _ => ∀ {W : Ctx Head _}, CtxNarrows S.R W Γ → CtxFormed S.R W → CtxFormed S.R Γ →
      IsType S.R W A → ∀ {B}, IsType S.R W B → Below S.R Γ A B → Below S.R W A B
  | .typesW Γ A _ => ∀ {W : Ctx Head _}, CtxNarrows S.R W Γ → CtxFormed S.R W → CtxFormed S.R Γ →
      IsType S.R W A → ∀ {B}, IsType S.R W B → Below S.R Γ A B → Below S.R W A B
  | _ => True

include facts roots heads algebra rigid complete in
/-- The motive holds along every algorithmic derivation. -/
theorem belowWide_of_algorithmic {st : AlgorithmicStatement Head} (derivation : Algorithmic S.R S.roles st) :
    BelowWide (S := S) st := by
  induction derivation with
  | types rA _ _ _ _ ih =>
      intro W narrows formedW formedΓ isA B isB le
      have rAW := redTy_wide facts roots formedW rA.red isA
      have le' : Below S.R _ _ B := .subTrans (TypeEq.below (TypeEq.symm rA.typeEq)) le
      exact .subTrans (TypeEq.below rAW.typeEq) (ih narrows formedW formedΓ rAW.targetType isB le')
  | @heads n Γ h h' u _ _ _ _ =>
      intro W narrows formedW formedΓ isH B isB le
      rcases S.levels.universe_decided h with hh | nh
      · obtain ⟨v, hv, eB, c⟩ := (Below.universe_iff facts algebra formedΓ hh).1 le
        obtain ⟨v₀, rB, hv₀⟩ := IsType.universe_whnf facts formedΓ (isType_narrow narrows isB) hv eB
        have c₀ : S.R.cumulative h v₀ :=
          algebra.same_right c (TypeEq.head_injective facts (TypeEq.trans S.levels (TypeEq.symm eB) rB.typeEq)
            formedΓ)
        have rBW := redTy_wide facts roots formedW rB.red isB
        exact (Below.universe_iff facts algebra formedW hh).2 ⟨v₀, hv₀, rBW.typeEq, c₀⟩
      · have e := (RigidShape.below_iff facts (.head nh) formedΓ).1 le
        exact TypeEq.below (typeEq_wide facts roots heads algebra rigid complete narrows formedW formedΓ isH isB e)
  | @pi n Γ A₁ A₁' B₁ B₁' isA₁ _ _ _ ihB =>
      intro W narrows formedW formedΓ isPi B isB le
      have isPiΓ := isType_narrow narrows isPi
      obtain ⟨A₂, B₂, eB, eDom, leCod⟩ := (Below.pi_iff facts formedΓ isPiΓ).1 le
      rcases IsType.pi_or facts formedΓ (isType_narrow narrows isB) with ⟨A₂', B₂', rB⟩ | notPi
      · obtain ⟨eDom₂, eCod₂⟩ := TypeEq.pi_injective facts
          (TypeEq.trans S.levels (TypeEq.symm rB.typeEq) eB) formedΓ
        have eA₁A₂' : TypeEq S.R Γ A₁ A₂' := TypeEq.trans S.levels eDom (TypeEq.symm eDom₂)
        have leB₁B₂' : Below S.R (.snoc Γ A₁) B₁ B₂' :=
          .subTrans leCod (Below.ctxConv (TypeEq.below (TypeEq.symm eCod₂)) (TypeEq.symm eA₁A₂'))
        have rBW := redTy_wide facts roots formedW rB.red isB
        obtain ⟨isA₁W, isB₁W⟩ := IsType.pi_parts isPi
        obtain ⟨isA₂'W, ⟨u₂, hu₂, tB₂'⟩⟩ := IsType.pi_parts rBW.targetType
        have eA₁A₂'W : TypeEq S.R W A₁ A₂' :=
          typeEq_wide facts roots heads algebra rigid complete narrows formedW formedΓ isA₁W isA₂'W eA₁A₂'
        have isB₂'W : IsType S.R (.snoc W A₁) B₂' := ⟨u₂, hu₂, Typed.ctxBelow tB₂' (TypeEq.below eA₁A₂'W)⟩
        have leW := ihB (.same A₁ narrows) (formedW.snoc isA₁W) (formedΓ.snoc isA₁) isB₁W isB₂'W leB₁B₂'
        exact (Below.pi_iff facts formedW isPi).2 ⟨A₂', B₂', rBW.typeEq, eA₁A₂'W, leW⟩
      · exact absurd eB (notPi A₂ B₂)
  | @sigma n Γ A₁ A₁' B₁ B₁' isA₁ _ _ ihA ihB =>
      intro W narrows formedW formedΓ isSigma B isB le
      have isSigmaΓ := isType_narrow narrows isSigma
      obtain ⟨A₂, B₂, eB, leDom, leCod⟩ := (Below.sigma_iff facts formedΓ isSigmaΓ).1 le
      rcases IsType.sigma_or facts formedΓ (isType_narrow narrows isB) with ⟨A₂', B₂', rB⟩ | notSigma
      · obtain ⟨eDom₂, eCod₂⟩ := TypeEq.sigma_injective facts
          (TypeEq.trans S.levels (TypeEq.symm rB.typeEq) eB) formedΓ
        have leA₁A₂' : Below S.R Γ A₁ A₂' := .subTrans leDom (TypeEq.below (TypeEq.symm eDom₂))
        have leB₁B₂' : Below S.R (.snoc Γ A₁) B₁ B₂' :=
          .subTrans leCod (Below.ctxBelow (TypeEq.below (TypeEq.symm eCod₂)) leA₁A₂')
        have rBW := redTy_wide facts roots formedW rB.red isB
        obtain ⟨isA₁W, isB₁W⟩ := IsType.sigma_parts isSigma
        obtain ⟨isA₂'W, ⟨u₂, hu₂, tB₂'⟩⟩ := IsType.sigma_parts rBW.targetType
        have leA₁A₂'W := ihA narrows formedW formedΓ isA₁W isA₂'W leA₁A₂'
        have isB₂'W : IsType S.R (.snoc W A₁) B₂' := ⟨u₂, hu₂, Typed.ctxBelow tB₂' leA₁A₂'W⟩
        have leW := ihB (.same A₁ narrows) (formedW.snoc isA₁W) (formedΓ.snoc isA₁) isB₁W isB₂'W leB₁B₂'
        exact (Below.sigma_iff facts formedW isSigma).2 ⟨A₂', B₂', rBW.typeEq, leA₁A₂'W, leW⟩
      · exact absurd eB (notSigma A₂ B₂)
  | id _ _ _ _ _ _ =>
      intro W narrows formedW formedΓ isId B isB le
      exact TypeEq.below (typeEq_wide facts roots heads algebra rigid complete narrows formedW formedΓ isId isB
        ((RigidShape.below_iff facts .id formedΓ).1 le))
  | inductiveType role _ =>
      intro W narrows formedW formedΓ isT B isB le
      exact TypeEq.below (typeEq_wide facts roots heads algebra rigid complete narrows formedW formedΓ isT isB
        ((RigidShape.below_iff facts (.inductiveType role) formedΓ).1 le))
  | neutralTypes nA _ _ _ _ =>
      intro W narrows formedW formedΓ isA B isB le
      exact TypeEq.below (typeEq_wide facts roots heads algebra rigid complete narrows formedW formedΓ isA isB
        ((RigidShape.below_iff facts (.neutral nA) formedΓ).1 le))
  | terms => trivial
  | univ => trivial
  | eta => trivial
  | sigmaEta => trivial
  | refl => trivial
  | spine => trivial
  | var => trivial
  | const => trivial
  | app => trivial
  | fst => trivial
  | snd => trivial
  | spinesW => trivial

include facts roots heads algebra rigid complete in
/-- **Subtyping is reflected by narrowing**, for types of the wide telescope. -/
theorem below_wide {n : Nat} {W Γ : Ctx Head n} (narrows : CtxNarrows S.R W Γ) (formedW : CtxFormed S.R W)
    (formedΓ : CtxFormed S.R Γ) {A B : Tm Head n} (isA : IsType S.R W A) (isB : IsType S.R W B)
    (le : Below S.R Γ A B) : Below S.R W A B :=
  belowWide_of_algorithmic facts roots heads algebra rigid complete
    (complete.types (isType_narrow narrows isA).refl formedΓ) narrows formedW formedΓ isA isB le

end Wide

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
