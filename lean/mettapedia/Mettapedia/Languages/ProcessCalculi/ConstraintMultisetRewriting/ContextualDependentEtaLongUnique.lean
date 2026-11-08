import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaLong

/-!
# Equal η-long normal forms are the same term

Two η-long β-normal forms that are equal in the typed βη equality are syntactically equal up to
the package's head equality (`long_unique`, `long_type_unique`).

The proof follows a derivation of the algorithmic equality between them, which completeness
supplies. Normal forms are weak-head normal, so the comparison reduces nothing; the type directs
which comparison is made, and each one finds the same former on both sides: abstractions at a
dependent function type, pairs at a dependent pair type, reflexivity or the same neutral spine
at an identity type, types at a universe, and the same neutral spine elsewhere. The argument of
an application is compared at the domain of the type the head assigns, which is principal for
both spines, so the arguments are normal at that domain.

No hypothesis on the roles of constants is used: a normal neutral term has a rigid head by
definition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaLong

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- An abstraction renamed past a fresh variable and applied to it reduces to its body. -/
theorem whRed_eta_lam {R : Rules Head} {roles : Roles Head} {n : Nat} (b : Tm Head (n + 1)) :
    WhRed R roles (.app (Presentation.rename wk (.lam b)) (.var 0)) b := by
  have step := WhStep.beta (R := R) (roles := roles) (Presentation.rename (liftRen wk) b) (.var 0)
  rw [inst0_var_rename_liftRen_wk] at step
  exact Relation.ReflTransGen.single step

/-- The two contexts that differ in their last entry by an equal type, in both directions. -/
theorem ctxEq_last {R : Rules Head} {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed R Γ)
    {A A' : Tm Head n} (equal : TypeEq R Γ A A') :
    CtxEq R (.snoc Γ A) (.snoc Γ A') ∧ CtxEq R (.snoc Γ A') (.snoc Γ A) :=
  ⟨.snoc (CtxEq.refl Γ formed) equal.symm, .snoc (CtxEq.refl Γ formed) equal⟩

/-- What a derivation of the algorithmic equality says about normal forms of its sides. -/
def UniqueAt (S : Setting Head L) : AlgorithmicStatement Head → Prop
  | .types Γ A B => CtxFormed S.R Γ → ∀ {V W}, WhRed S.R S.roles A V → WhRed S.R S.roles B W →
      Long S.R S.roles (.type Γ V) → Long S.R S.roles (.type Γ W) → SameUpToHeads S.R V W
  | .typesW Γ A B => CtxFormed S.R Γ → Long S.R S.roles (.type Γ A) →
      Long S.R S.roles (.type Γ B) → SameUpToHeads S.R A B
  | .terms Γ t u A => CtxFormed S.R Γ → ∀ {v w}, WhRed S.R S.roles t v → WhRed S.R S.roles u w →
      Long S.R S.roles (.term Γ v A) → Long S.R S.roles (.term Γ w A) → SameUpToHeads S.R v w
  | .termsW Γ t u A => CtxFormed S.R Γ → Long S.R S.roles (.term Γ t A) →
      Long S.R S.roles (.term Γ u A) → SameUpToHeads S.R t u
  | .spines Γ t u _ => CtxFormed S.R Γ → ∀ {U₁ U₂}, Long S.R S.roles (.spine Γ t U₁) →
      Long S.R S.roles (.spine Γ u U₂) → SameUpToHeads S.R t u
  | .spinesW Γ t u _ => CtxFormed S.R Γ → ∀ {U₁ U₂}, Long S.R S.roles (.spine Γ t U₁) →
      Long S.R S.roles (.spine Γ u U₂) → SameUpToHeads S.R t u

section Shapes

/-- A normal type that is neutral is a neutral spine. -/
theorem Long.spine_of_neutral {n : Nat} {Γ : Ctx Head n} {V : Tm Head n}
    (long : Long S.R S.roles (.type Γ V)) (neutral : Neutral S.roles V) :
    ∃ U, Long S.R S.roles (.spine Γ V U) := by
  cases long with
  | head => exact absurd rfl (neutral.not_former.1 _)
  | pi => exact absurd rfl (neutral.not_former.2.1 _ _)
  | sigma => exact absurd rfl (neutral.not_former.2.2.1 _ _)
  | id => exact absurd rfl (neutral.not_former.2.2.2 _ _ _)
  | neutralType ls _ _ => exact ⟨_, ls⟩

variable (facts : FormFacts S.R S.roles)
include facts

/-- At a universe, a normal term is a normal type. -/
theorem Long.type_of_universe {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {t : Tm Head n}
    {h : Head} (hu : S.R.isUniverse h) (long : Long S.R S.roles (.term Γ t (.head h))) :
    Long S.R S.roles (.type Γ t) := by
  cases long with
  | univ _ _ _ lt => exact lt
  | lam e _ _ _ => exact absurd e.symm (TypeEq.pi_ne_head facts formed)
  | pair e _ _ _ => exact absurd e.symm (TypeEq.sigma_ne_head facts formed)
  | refl e _ _ => exact absurd e.symm (TypeEq.id_ne_head facts formed)
  | neutral ls le _ _ => exact .neutralType ls hu le

/-- At a dependent function type, a normal term is an abstraction. -/
theorem Long.lam_of_pi {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {t A : Tm Head n}
    {B : Tm Head (n + 1)} (long : Long S.R S.roles (.term Γ t (.pi A B))) :
    ∃ (b : Tm Head (n + 1)) (A₁ : Tm Head n) (B₁ : Tm Head (n + 1)), t = .lam b ∧
      TypeEq S.R Γ (.pi A B) (.pi A₁ B₁) ∧ IsType S.R Γ A₁ ∧
      Long S.R S.roles (.term (.snoc Γ A₁) b B₁) := by
  cases long with
  | univ _ e _ _ => exact absurd e (TypeEq.pi_ne_head facts formed)
  | lam e isA _ lb => exact ⟨_, _, _, rfl, e, isA, lb⟩
  | pair e _ _ _ => exact absurd e (TypeEq.pi_ne_sigma facts formed)
  | refl e _ _ => exact absurd e (TypeEq.pi_ne_id facts formed)
  | neutral _ _ typed base =>
      exact absurd (IsType.refl (Typed.isType typed formed)) (base.1 A B)

/-- At a dependent pair type, a normal term is a pair. -/
theorem Long.pair_of_sigma {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {t A : Tm Head n}
    {B : Tm Head (n + 1)} (long : Long S.R S.roles (.term Γ t (.sigma A B))) :
    ∃ (a b A₁ : Tm Head n) (B₁ : Tm Head (n + 1)), t = .pair a b ∧
      TypeEq S.R Γ (.sigma A B) (.sigma A₁ B₁) ∧ Long S.R S.roles (.term Γ a A₁) ∧
      Long S.R S.roles (.term Γ b (inst0 a B₁)) := by
  cases long with
  | univ _ e _ _ => exact absurd e (TypeEq.sigma_ne_head facts formed)
  | lam e _ _ _ => exact absurd e.symm (TypeEq.pi_ne_sigma facts formed)
  | pair e _ la lb => exact ⟨_, _, _, _, rfl, e, la, lb⟩
  | refl e _ _ => exact absurd e (TypeEq.sigma_ne_id facts formed)
  | neutral _ _ typed base =>
      exact absurd (IsType.refl (Typed.isType typed formed)) (base.2 A B)

/-- At an identity type, a normal reflexivity has a normal point. -/
theorem Long.refl_of_id {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {z C x y : Tm Head n}
    (long : Long S.R S.roles (.term Γ (.refl z) (.id C x y))) :
    ∃ A₁ x₁ y₁, TypeEq S.R Γ (.id C x y) (.id A₁ x₁ y₁) ∧ Long S.R S.roles (.term Γ z A₁) := by
  cases long with
  | univ _ e _ _ => exact absurd e (TypeEq.id_ne_head facts formed)
  | refl e _ lz => exact ⟨_, _, _, e, lz⟩
  | neutral ls _ _ _ => cases ls

/-- At a type whose values are compared as spines, a normal term is neutral. -/
theorem Long.spine_of_spineType {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {t A : Tm Head n} (spine : SpineType S.R S.roles A) (form : SpineForm S.roles t)
    (long : Long S.R S.roles (.term Γ t A)) : ∃ U, Long S.R S.roles (.spine Γ t U) := by
  cases long with
  | univ hu e _ _ =>
      exact absurd hu (SpineType.not_universe
        (SpineType.of_typeEq facts spine e formed (.inl ⟨_, rfl⟩)))
  | lam e _ _ _ =>
      exact absurd (SpineType.of_typeEq facts spine e formed (.inr (.inl ⟨_, _, rfl⟩)))
        SpineType.not_pi
  | pair e _ _ _ =>
      exact absurd (SpineType.of_typeEq facts spine e formed (.inr (.inr (.inl ⟨_, _, rfl⟩))))
        SpineType.not_sigma
  | refl _ _ _ => exact absurd form SpineForm.not_refl
  | neutral ls _ _ _ => exact ⟨_, ls⟩

variable (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
include roots heads algebra

/-- The domain the head of two compared spines assigns is the domain of every type of either
spine that is a dependent function type: the assigned type is principal for both. -/
theorem spinesW_pi_domains {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {f g A A₁ A₂ F G : Tm Head n} {B B₁ B₂ : Tm Head (n + 1)}
    (derivation : Algorithmic S.R S.roles (.spinesW Γ f g (.pi A B)))
    (tf : Typed S.R Γ f F) (eF : TypeEq S.R Γ F (.pi A₁ B₁))
    (tg : Typed S.R Γ g G) (eG : TypeEq S.R Γ G (.pi A₂ B₂)) :
    TypeEq S.R Γ A A₁ ∧ TypeEq S.R Γ A A₂ := by
  cases derivation with
  | @spinesW _ _ _ _ U₀ _ d r _ =>
  obtain ⟨tf₀, tg₀, _⟩ := Algorithmic.sound facts roots heads algebra d formed
  obtain ⟨_, _, _, principalF, principalG⟩ :=
    Algorithm.sound facts roots heads algebra d.refines formed tf₀ tg₀
  obtain ⟨u, hu, e⟩ := r.typeEq.symm
  have toPi : ∀ {X A' : Tm Head n} {B' : Tm Head (n + 1)}, TypeLe S.R Γ U₀ X →
      TypeEq S.R Γ X (.pi A' B') → TypeEq S.R Γ A A' := by
    intro X A' B' le eX
    obtain ⟨s, hs, eX'⟩ := eX
    have chain : TypeLe S.R Γ (.pi A B) (.pi A' B') :=
      .conv e hu (le.trans (TypeLe.of_equal eX' hs))
    exact (TypeLe.pi_parts facts chain (TypeEq.isType ⟨s, hs, eX'⟩ formed).2 formed).1
  exact ⟨toPi (principalF tf) eF, toPi (principalG tg) eG⟩

/-- **Normal forms of the two sides of an algorithmic comparison are the same.** -/
theorem unique_of_algorithmic {st : AlgorithmicStatement Head}
    (derivation : Algorithmic S.R S.roles st) : UniqueAt S st := by
  have soundTerms := fun {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n} (formed : CtxFormed S.R Γ)
      (d : Algorithmic S.R S.roles (.terms Γ t u A)) =>
    Algorithmic.sound_terms facts roots heads algebra formed d
  have soundTypes := fun {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} (formed : CtxFormed S.R Γ)
      (d : Algorithmic S.R S.roles (.types Γ A B)) =>
    Algorithmic.sound_types facts roots heads algebra formed d
  induction derivation with
  | types rA rB fA fB _ ih =>
      intro formed V W hV hW lV lW
      obtain rfl := WhRed.whnf_unique S.shape rA.red hV fA.whnf (lV.type_whnf S.shape)
      obtain rfl := WhRed.whnf_unique S.shape rB.red hW fB.whnf (lW.type_whnf S.shape)
      exact ih formed lV lW
  | heads same _ _ _ => exact fun _ _ _ => .head same
  | pi isA dA _ ihA ihB =>
      intro formed lV lW
      cases lV with
      | neutralType ls _ _ => cases ls
      | pi lA lB _ =>
      cases lW with
      | neutralType ls _ _ => cases ls
      | pi lA' lB' _ =>
      have eA := soundTypes formed dA
      obtain ⟨there, back⟩ := ctxEq_last formed eA
      exact .pi (ihA formed .refl .refl lA lA')
        (ihB (.snoc formed isA) .refl .refl lB ((lB'.stable S.levels) back there))
  | sigma isA dA _ ihA ihB =>
      intro formed lV lW
      cases lV with
      | neutralType ls _ _ => cases ls
      | sigma lA lB _ =>
      cases lW with
      | neutralType ls _ _ => cases ls
      | sigma lA' lB' _ =>
      have eA := soundTypes formed dA
      obtain ⟨there, back⟩ := ctxEq_last formed eA
      exact .sigma (ihA formed .refl .refl lA lA')
        (ihB (.snoc formed isA) .refl .refl lB ((lB'.stable S.levels) back there))
  | id dA _ _ ihA ihx ihy =>
      intro formed lV lW
      cases lV with
      | neutralType ls _ _ => cases ls
      | id lA lx ly _ =>
      cases lW with
      | neutralType ls _ _ => cases ls
      | id lA' lx' ly' _ =>
      have eA := soundTypes formed dA
      exact .id (ihA formed .refl .refl lA lA')
        (ihx formed .refl .refl lx (lx'.convType S.levels eA.symm))
        (ihy formed .refl .refl ly (ly'.convType S.levels eA.symm))
  | inductiveType _ _ => exact fun _ _ _ => SameUpToHeads.rfl' _
  | neutralTypes nA nB _ _ ih =>
      intro formed lV lW
      obtain ⟨_, ls⟩ := lV.spine_of_neutral nA
      obtain ⟨_, ls'⟩ := lW.spine_of_neutral nB
      exact ih formed ls ls'
  | terms rA _ rt ru d ih =>
      intro formed v w hv hw lv lw
      obtain rfl := WhRed.whnf_unique S.shape rt.red hv d.termsW_whnf.1 (lv.whnf S.shape)
      obtain rfl := WhRed.whnf_unique S.shape ru.red hw d.termsW_whnf.2 (lw.whnf S.shape)
      exact ih formed (lv.convType S.levels rA.typeEq) (lw.convType S.levels rA.typeEq)
  | univ hu _ _ _ ih =>
      intro formed lt lu
      exact ih formed (lt.type_of_universe facts formed hu) (lu.type_of_universe facts formed hu)
  | eta isA _ _ _ _ _ ih =>
      intro formed lf lg
      obtain ⟨b, A₁, B₁, rfl, e₁, _, lb⟩ := lf.lam_of_pi facts formed
      obtain ⟨c, A₂, B₂, rfl, e₂, _, lc⟩ := lg.lam_of_pi facts formed
      obtain ⟨eA₁, eB₁⟩ := TypeEq.pi_injective facts e₁ formed
      obtain ⟨eA₂, eB₂⟩ := TypeEq.pi_injective facts e₂ formed
      obtain ⟨to₁, from₁⟩ := ctxEq_last formed eA₁
      obtain ⟨to₂, from₂⟩ := ctxEq_last formed eA₂
      have lb' := ((lb.stable S.levels) from₁ to₁).convType S.levels eB₁.symm
      have lc' := ((lc.stable S.levels) from₂ to₂).convType S.levels eB₂.symm
      exact .lam (ih (.snoc formed isA) (whRed_eta_lam b) (whRed_eta_lam c) lb' lc')
  | @sigmaEta _ _ _ _ _ B tp _ tq _ d₁ _ ih₁ ih₂ =>
      intro formed lp lq
      obtain ⟨a, b, A₁, B₁, rfl, e₁, la, lb⟩ := lp.pair_of_sigma facts formed
      obtain ⟨a', b', A₂, B₂, rfl, e₂, la', lb'⟩ := lq.pair_of_sigma facts formed
      obtain ⟨eA₁, eB₁⟩ := TypeEq.sigma_injective facts e₁ formed
      obtain ⟨eA₂, eB₂⟩ := TypeEq.sigma_injective facts e₂ formed
      have la₀ := la.convType S.levels eA₁.symm
      have la₀' := la'.convType S.levels eA₂.symm
      obtain ⟨s, hs, tSigma⟩ := Typed.isType tp formed
      obtain ⟨_, ⟨v, hv, family⟩⟩ := IsType.sigma_parts ⟨s, hs, tSigma⟩
      have first := (Typed.fstPair_preserve facts formed (.fstElim tp)).2
      have first' := (Typed.fstPair_preserve facts formed (.fstElim tq)).2
      have across : Equal S.R _ (.fst (.pair a b)) (.fst (.pair a' b')) _ := soundTerms formed d₁
      have toLeft : TypeEq S.R _ (inst0 a B₁) (inst0 (.fst (.pair a b)) B) :=
        TypeEq.trans S.levels (TypeEq.instantiate eB₁ la₀.typed).symm
          (TypeEq.of_instantiateEq family hv la₀.typed (.symm first))
      have toRight : TypeEq S.R _ (inst0 a' B₂) (inst0 (.fst (.pair a b)) B) :=
        TypeEq.trans S.levels (TypeEq.instantiate eB₂ la₀'.typed).symm
          (TypeEq.of_instantiateEq family hv la₀'.typed (.trans (.symm first') (.symm across)))
      exact .pair
        (ih₁ formed (.single (.fstPair _ _)) (.single (.fstPair _ _)) la₀ la₀')
        (ih₂ formed (.single (.sndPair _ _)) (.single (.sndPair _ _))
          (lb.convType S.levels toLeft) (lb'.convType S.levels toRight))
  | refl _ _ _ ih =>
      intro formed lx lx'
      obtain ⟨A₁, _, _, e₁, lz⟩ := lx.refl_of_id facts formed
      obtain ⟨A₂, _, _, e₂, lz'⟩ := lx'.refl_of_id facts formed
      exact .refl (ih formed .refl .refl
        (lz.convType S.levels (TypeEq.id_injective facts e₁ formed).1.symm)
        (lz'.convType S.levels (TypeEq.id_injective facts e₂ formed).1.symm))
  | spine sA fT fU _ _ _ ih =>
      intro formed lt lu
      obtain ⟨_, ls⟩ := lt.spine_of_spineType facts formed sA fT
      obtain ⟨_, ls'⟩ := lu.spine_of_spineType facts formed sA fU
      exact ih formed ls ls'
  | var i => exact fun _ _ _ _ _ => .var i
  | const _ _ => exact fun _ _ _ _ _ => .const _
  | app df _ ihf iha =>
      intro formed U₁ U₂ ll lr
      cases ll with
      | app lf eF la _ =>
      cases lr with
      | app lg eG lb _ =>
      obtain ⟨e₁, e₂⟩ := spinesW_pi_domains facts roots heads algebra formed df
        lf.spine_typed eF lg.spine_typed eG
      exact .app (ihf formed lf lg)
        (iha formed .refl .refl (la.convType S.levels e₁.symm) (lb.convType S.levels e₂.symm))
  | fst _ ih =>
      intro formed U₁ U₂ ll lr
      cases ll with
      | fst lp _ _ =>
      cases lr with
      | fst lq _ _ => exact .fst (ih formed lp lq)
  | snd _ ih =>
      intro formed U₁ U₂ ll lr
      cases ll with
      | snd lp _ _ =>
      cases lr with
      | snd lq _ _ => exact .snd (ih formed lp lq)
  | spinesW _ _ _ ih => exact ih

variable (complete : AlgorithmicComplete S.R S.roles)
include complete

/-- **Reflection for normal forms**: two η-long normal forms equal in the typed βη equality are
syntactically equal, up to the package's head equality. -/
theorem long_unique {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {v w A : Tm Head n}
    (lv : Long S.R S.roles (.term Γ v A)) (lw : Long S.R S.roles (.term Γ w A))
    (equal : Equal S.R Γ v w A) : SameUpToHeads S.R v w :=
  unique_of_algorithmic facts roots heads algebra (complete formed equal) formed .refl .refl lv lw

/-- Reflection for normal types. -/
theorem long_type_unique {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {V W : Tm Head n}
    (lV : Long S.R S.roles (.type Γ V)) (lW : Long S.R S.roles (.type Γ W))
    (equal : TypeEq S.R Γ V W) : SameUpToHeads S.R V W :=
  unique_of_algorithmic facts roots heads algebra (complete.types equal formed) formed .refl .refl lV lW

end Shapes

end ContextualDependentEtaLong
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
