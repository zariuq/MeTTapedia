import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Families
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.StuckRel
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Root

/-!
# Stuck and type-like terms on the value side

A *type-like* term is weak-head normal and has the form of a type: a head, a
type former or `holds` of a code. A *stuck* term is an application or a
projection of a type-like or stuck term. Over every realizer algebra:

* neither is daimonic, related at an inductive type, a meaning of a code or an
  interpreted type (`TypeLike.not_daimonic`, `Stuck.not_indRel`,
  `Stuck.not_truth`, `Stuck.not_interp`);
* so a pack relates any two stuck terms as soon as it relates two
  (`SInterp.stuck`), and a pack is the pack of a universe below the level or
  relates any two type-like terms as soon as it relates two
  (`SInterp.typeLike`);
* a pack at a level therefore relates two type-like terms that are related to
  type-like terms of one pack and one shape (`InterpAt.typeLike_coherent`).

Heads that the package identifies have one pack and one shape at each level:
universes of one level, or two leaves (`head_coherent`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (World Morph Truth TypeLike Stuck)
open Realizability (Daimonic)

variable {Head L : Type} [LevelOrder L] {V : Model Head L}

/-! ## Stuck and type-like terms are neither values of inductive types nor codes -/

section Laws

variable (laws : V.Laws)
include laws

/-- A type-like term is not daimonic. -/
theorem TypeLike.not_daimonic {n : Nat} {t : Tm Head n} (like : TypeLike V.toModel t) :
    ¬ Daimonic V.roles V.star t := by
  intro daimonic
  have former := laws.daimonic_not_former daimonic
  cases like with
  | holds c => exact laws.daimonic_ne_holds daimonic rfl
  | head h => exact former.1 h rfl
  | pi A B => exact former.2.1 A B rfl
  | sigma A B => exact former.2.2.1 A B rfl
  | id A a b => exact former.2.2.2 A a b rfl

/-- A daimonic term is not stuck: the head of a stuck spine is `holds`, which is
rigid, while a daimonic spine is headed by the daimon or by a computing
constant. -/
theorem Daimonic.not_stuck {n : Nat} {t : Tm Head n} (daimonic : Daimonic V.roles V.star t) :
    ¬ Stuck V.toModel t := by
  induction daimonic with
  | star => intro stuck; cases stuck
  | app daimonic ih =>
      intro stuck
      cases stuck with
      | appLike _ like => exact TypeLike.not_daimonic laws like daimonic
      | appStuck _ stuck => exact ih stuck
  | fst daimonic ih =>
      intro stuck
      cases stuck with
      | fstLike like => exact TypeLike.not_daimonic laws like daimonic
      | fstStuck stuck => exact ih stuck
  | snd daimonic ih =>
      intro stuck
      cases stuck with
      | sndLike like => exact TypeLike.not_daimonic laws like daimonic
      | sndStuck stuck => exact ih stuck
  | stuck role _ _ _ =>
      intro stuck
      rw [stuck.head_const (Consistency.head_of_constSpine rfl), laws.values.holds] at role
      cases role
  | typeStuck role _ _ _ _ _ =>
      intro stuck
      rw [stuck.head_const (Consistency.head_of_constSpine rfl), laws.values.holds] at role
      cases role

/-- A stuck term is related at no inductive type. -/
theorem Stuck.not_indRel {T : DeclName} {cs : List (DeclName × List (Field Head))}
    (role : V.roles T = .inductive cs) {n : Nat} {field : Tm Head 0 → Pack V n}
    {t t' : Tm Head n} (stuck : Stuck V.toModel t) : ¬ IndRel V cs field t t' := by
  have normal := stuck.whnf laws.values
  intro related
  cases related with
  | ctor mem red _ _ =>
      exact Consistency.ne_holds_of_constructor laws.values (laws.declared.arity role mem)
        (stuck.head_const (Consistency.head_of_constSpine (Consistency.WhRed.of_whnf normal red)))
  | star red daimonic _ _ =>
      rw [Consistency.WhRed.of_whnf normal red] at daimonic
      exact Daimonic.not_stuck laws daimonic stuck

/-- A type-like term is related at no inductive type. -/
theorem TypeLike.not_indRel {T : DeclName} {cs : List (DeclName × List (Field Head))}
    (role : V.roles T = .inductive cs) {n : Nat} {field : Tm Head 0 → Pack V n}
    {t t' : Tm Head n} (like : TypeLike V.toModel t) : ¬ IndRel V cs field t t' := by
  have normal := like.whnf laws.values
  intro related
  cases related with
  | ctor mem red _ _ =>
      exact Consistency.ne_holds_of_constructor laws.values (laws.declared.arity role mem)
        (like.head_const (Consistency.head_of_constSpine (Consistency.WhRed.of_whnf normal red)))
  | star red daimonic _ _ =>
      rw [Consistency.WhRed.of_whnf normal red] at daimonic
      exact TypeLike.not_daimonic laws like daimonic

/-- A stuck term has no meaning as a code. -/
theorem Stuck.not_truth {n : Nat} {ξ : World V.reading n} {t : Tm Head n}
    (stuck : Stuck V.toModel t) {X : V.alg.Cand} : ¬ Truth V.reading ξ t X := by
  have normal := stuck.whnf laws.values
  intro truth
  cases truth with
  | imp red _ _ =>
      exact Consistency.ne_holds_of_constructor laws.values laws.values.truth.imp
        (stuck.head_const (Consistency.head_of_constSpine (args := [_, _])
          (Consistency.WhRed.of_whnf normal red)))
  | all carrier red _ =>
      exact Consistency.ne_holds_of_constructor laws.values (laws.values.truth.all carrier)
        (stuck.head_const (Consistency.head_of_constSpine (args := [_])
          (Consistency.WhRed.of_whnf normal red)))
  | eq carrier red _ _ =>
      exact Consistency.ne_holds_of_constructor laws.values (laws.values.truth.eq carrier)
        (stuck.head_const (Consistency.head_of_constSpine (args := [_, _])
          (Consistency.WhRed.of_whnf normal red)))
  | generic red _ =>
      exact stuck.head_not_var
        (Consistency.head_of_varSpine (Consistency.WhRed.of_whnf normal red))
  | neutral red neutral =>
      rw [Consistency.WhRed.of_whnf normal red] at neutral
      exact Daimonic.not_stuck laws neutral stuck

/-- A type-like term has no meaning as a code. -/
theorem TypeLike.not_truth {n : Nat} {ξ : World V.reading n} {t : Tm Head n}
    (like : TypeLike V.toModel t) {X : V.alg.Cand} : ¬ Truth V.reading ξ t X := by
  have normal := like.whnf laws.values
  intro truth
  cases truth with
  | imp red _ _ =>
      exact Consistency.ne_holds_of_constructor laws.values laws.values.truth.imp
        (like.head_const (Consistency.head_of_constSpine (args := [_, _])
          (Consistency.WhRed.of_whnf normal red)))
  | all carrier red _ =>
      exact Consistency.ne_holds_of_constructor laws.values (laws.values.truth.all carrier)
        (like.head_const (Consistency.head_of_constSpine (args := [_])
          (Consistency.WhRed.of_whnf normal red)))
  | eq carrier red _ _ =>
      exact Consistency.ne_holds_of_constructor laws.values (laws.values.truth.eq carrier)
        (like.head_const (Consistency.head_of_constSpine (args := [_, _])
          (Consistency.WhRed.of_whnf normal red)))
  | generic red _ =>
      exact like.head_not_var
        (Consistency.head_of_varSpine (Consistency.WhRed.of_whnf normal red))
  | neutral red neutral =>
      rw [Consistency.WhRed.of_whnf normal red] at neutral
      exact TypeLike.not_daimonic laws like neutral

/-- A stuck term is not an interpreted type. -/
theorem Stuck.not_interp {l : L} {below : L → IPack V} {n : Nat} {ξ : World V.reading n}
    {t : Tm Head n} (stuck : Stuck V.toModel t) {P : Pack V n} :
    ¬ SInterp V l below ξ t P := by
  have normal := stuck.whnf laws.values
  intro interp
  cases interp with
  | sort _ _ red =>
      have e := Consistency.WhRed.of_whnf normal red
      cases stuck <;> cases e
  | ground _ red =>
      have e := Consistency.WhRed.of_whnf normal red
      cases stuck <;> cases e
  | pi red =>
      have e := Consistency.WhRed.of_whnf normal red
      cases stuck <;> cases e
  | sigma red =>
      have e := Consistency.WhRed.of_whnf normal red
      cases stuck <;> cases e
  | ident red =>
      have e := Consistency.WhRed.of_whnf normal red
      cases stuck <;> cases e
  | ind red => exact stuck.not_const _ (Consistency.WhRed.of_whnf normal red).symm
  | prop red => exact stuck.not_const _ (Consistency.WhRed.of_whnf normal red).symm
  | holds red _ =>
      have e := Consistency.WhRed.of_whnf normal red
      rw [← e] at stuck
      exact Consistency.not_const_of_app_stuck stuck _ rfl
  | rigid red _ _ notHolds =>
      exact notHolds (stuck.head_const
        (Consistency.head_of_constSpine (Consistency.WhRed.of_whnf normal red)))
  | daimon red daimonic =>
      rw [Consistency.WhRed.of_whnf normal red] at daimonic
      exact Daimonic.not_stuck laws daimonic stuck

/-- The levels below a level interpret no stuck term. -/
theorem levelsBelow_stuck {l : L} (k : L) {n : Nat} {ξ : World V.reading n}
    {x : Tm Head n} {Q : Pack V n} (stuck : Stuck V.toModel x) :
    ¬ levelsBelow V l k ξ x Q :=
  fun h => Stuck.not_interp laws stuck ((levelsBelow_iff (levelsBelow_lt h) ξ x Q).mp h)

end Laws

/-! ## Stuck and type-like terms in packs -/

section Relations

variable {l : L} {below : L → IPack V}

/-- A pack of the model relates any two stuck terms as soon as it relates two,
when no stuck term is interpreted below. -/
theorem SInterp.stuck (laws : V.Laws)
    (belowStuck : ∀ k {n : Nat} {ξ : World V.reading n} {x : Tm Head n} {Q : Pack V n},
      Stuck V.toModel x → ¬ below k ξ x Q)
    {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}
    (interp : SInterp V l below ξ A P) :
    ∀ {x y x' y' : Tm Head n}, Stuck V.toModel x → Stuck V.toModel y →
      Stuck V.toModel x' → Stuck V.toModel y' → P.rel x y → P.rel x' y' := by
  induction interp with
  | @sort n ξ A u isUniverse level red =>
      intro x y x' y' sx _ _ _ h
      obtain ⟨Q, hx, -⟩ := h (Morph.id ξ)
      rw [rename_id] at hx
      exact absurd hx (belowStuck _ sx)
  | ground => exact fun _ _ _ _ _ => trivial
  | pi _ P _ _ _ _ codIH =>
      intro x y x' y' sx sy sx' sy' h m ξ' ρ w a b ha hab
      exact codIH w ha (.appStuck a (sx.rename ρ)) (.appStuck b (sy.rename ρ))
        (.appStuck a (sx'.rename ρ)) (.appStuck b (sy'.rename ρ)) (h w ha hab)
  | @sigma n ξ A dom cod red P domInterp codInterp codRespect domIH codIH =>
      intro x y x' y' sx sy sx' sy'
      have fx : Stuck V.toModel (.fst x) := .fstStuck sx
      have fy : Stuck V.toModel (.fst y) := .fstStuck sy
      have fx' : Stuck V.toModel (.fst x') := .fstStuck sx'
      have fy' : Stuck V.toModel (.fst y') := .fstStuck sy'
      have first := @domIH _ _ _ (Morph.id ξ)
      rintro ⟨hp, hpq, hc⟩
      have hp' : (P.dom (Morph.id ξ)).Val (.fst x') := first fx fy fx' fx' hpq
      refine ⟨hp', first fx fy fx' fy' hpq, ?_⟩
      rw [← codRespect (Morph.id ξ) hp hp' (first fx fy fx fx' hpq)]
      exact codIH (Morph.id ξ) hp (.sndStuck sx) (.sndStuck sy) (.sndStuck sx') (.sndStuck sy')
        hc
  | ident => exact fun _ _ _ _ _ => trivial
  | ind _ role =>
      intro x y x' y' sx _ _ _ h
      exact absurd h (Stuck.not_indRel laws role sx)
  | prop =>
      intro x y x' y' sx _ _ _
      rintro ⟨_, hx, -⟩
      exact absurd hx (Stuck.not_truth laws sx)
  | holds => exact fun _ _ _ _ _ => trivial
  | rigid => exact fun _ _ _ _ _ => trivial
  | daimon => exact fun _ _ _ _ _ => trivial

/-- A pack of the model is the pack of a universe below the level, or relates
any two type-like terms as soon as it relates two, when no stuck term is
interpreted below. -/
theorem SInterp.typeLike (laws : V.Laws)
    (belowStuck : ∀ k {n : Nat} {ξ : World V.reading n} {x : Tm Head n} {Q : Pack V n},
      Stuck V.toModel x → ¬ below k ξ x Q)
    {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}
    (interp : SInterp V l below ξ A P) :
    (∃ k, k < l ∧ P = universePack V (below k) ξ) ∨
      ∀ {x y x' y' : Tm Head n}, TypeLike V.toModel x → TypeLike V.toModel y →
        TypeLike V.toModel x' → TypeLike V.toModel y' → P.rel x y → P.rel x' y' := by
  cases interp with
  | sort _ level _ => exact .inl ⟨_, level, rfl⟩
  | ground => exact .inr fun _ _ _ _ _ => trivial
  | pi _ P _ codInterp _ =>
      refine .inr fun lx ly lx' ly' h => ?_
      intro m ξ' ρ w a b ha hab
      exact SInterp.stuck laws belowStuck (codInterp w ha) (.appLike a (lx.rename ρ))
        (.appLike b (ly.rename ρ)) (.appLike a (lx'.rename ρ)) (.appLike b (ly'.rename ρ))
        (h w ha hab)
  | @sigma n ξ A dom cod red P domInterp codInterp codRespect =>
      refine .inr fun {x y x' y'} lx ly lx' ly' => ?_
      have fx : Stuck V.toModel (.fst x) := .fstLike lx
      have fy : Stuck V.toModel (.fst y) := .fstLike ly
      have fx' : Stuck V.toModel (.fst x') := .fstLike lx'
      have fy' : Stuck V.toModel (.fst y') := .fstLike ly'
      have first : ∀ {x y x' y' : Tm Head n}, Stuck V.toModel x → Stuck V.toModel y →
          Stuck V.toModel x' → Stuck V.toModel y' → (P.dom (Morph.id ξ)).rel x y →
            (P.dom (Morph.id ξ)).rel x' y' :=
        SInterp.stuck laws belowStuck (domInterp (Morph.id ξ))
      rintro ⟨hp, hpq, hc⟩
      have hp' : (P.dom (Morph.id ξ)).Val (.fst x') := first fx fy fx' fx' hpq
      refine ⟨hp', first fx fy fx' fy' hpq, ?_⟩
      rw [← codRespect (Morph.id ξ) hp hp' (first fx fy fx fx' hpq)]
      exact SInterp.stuck laws belowStuck (codInterp (Morph.id ξ) hp) (.sndLike lx)
        (.sndLike ly) (.sndLike lx') (.sndLike ly') hc
  | ident => exact .inr fun _ _ _ _ _ => trivial
  | ind _ role =>
      exact .inr fun lx _ _ _ h => absurd h (TypeLike.not_indRel laws role lx)
  | prop =>
      refine .inr fun lx _ _ _ => ?_
      rintro ⟨_, hx, -⟩
      exact absurd hx (TypeLike.not_truth laws lx)
  | holds => exact .inr fun _ _ _ _ _ => trivial
  | rigid => exact .inr fun _ _ _ _ _ => trivial
  | daimon => exact .inr fun _ _ _ _ _ => trivial

end Relations

/-! ## Coherent types in a universe -/

/-- A universe relates `x` to `y'` when it relates `x` to some `x'` and some `y`
to `y'`, and `x` and `y` have one pack and one shape wherever both are
interpreted: shapes compose through `y`. -/
theorem universePack.rel_coherent (laws : V.Laws) {I : IPack V}
    (facts : InterpFacts V I) {n : Nat} {ξ : World V.reading n} {x x' y y' : Tm Head n}
    (coherent : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
      ∀ {Q₁ Q₂ : Pack V m}, I ξ' (Presentation.rename ρ x) Q₁ →
        I ξ' (Presentation.rename ρ y) Q₂ →
          Q₁ = Q₂ ∧ Shape V I .pair ξ' (Presentation.rename ρ x) (Presentation.rename ρ y))
    (hx : (universePack V I ξ).rel x x') (hy : (universePack V I ξ).rel y y') :
    (universePack V I ξ).rel x y' := by
  intro m ξ' ρ w
  obtain ⟨Q₁, h₁, -, -⟩ := hx w
  obtain ⟨Q₂, h₂, h₂', s₂⟩ := hy w
  obtain ⟨rfl, s⟩ := coherent w h₁ h₂
  exact ⟨Q₁, h₁, h₂', s.trans laws facts s₂ ⟨_, h₁⟩ ⟨_, h₂'⟩⟩

/-- A pack at a level relates two type-like terms `x` and `y'` when it relates
`x` to a type-like `x'` and some `y` to `y'`, provided `x` and `y` have one pack
and one shape at each level wherever both are interpreted. -/
theorem InterpAt.typeLike_coherent (laws : V.Laws) {l : L} {n : Nat} {ξ : World V.reading n}
    {A : Tm Head n} {P : Pack V n} (interp : InterpAt V l ξ A P)
    {x x' y y' : Tm Head n} (lx : TypeLike V.toModel x) (lx' : TypeLike V.toModel x')
    (ly' : TypeLike V.toModel y')
    (coherent : ∀ {k : L} {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
      ∀ {Q₁ Q₂ : Pack V m}, InterpAt V k ξ' (Presentation.rename ρ x) Q₁ →
        InterpAt V k ξ' (Presentation.rename ρ y) Q₂ →
          Q₁ = Q₂ ∧ Shape V (InterpAt V k) .pair ξ' (Presentation.rename ρ x)
            (Presentation.rename ρ y)) :
    P.rel x x' → P.rel y y' → P.rel x y' := by
  rcases SInterp.typeLike laws (levelsBelow_stuck laws) interp with ⟨k, lt, rfl⟩ | alike
  · rw [levelsBelow_eq lt]
    exact universePack.rel_coherent laws (InterpAt.facts laws k)
      fun w _ _ first second => coherent w first second
  · exact fun h _ => alike lx lx' lx ly' h

/-! ## Heads -/

/-- Heads that are the same up to the package's head equality have one pack at
each level. -/
theorem head_same (laws : V.Laws) {h h' : Head} (same : V.rules.headEq h h') {l : L} {n : Nat}
    {ξ : World V.reading n} {P₁ P₂ : Pack V n}
    (first : InterpAt V l ξ (.head h) P₁) (second : InterpAt V l ξ (.head h') P₂) :
    P₁ = P₂ := by
  obtain ⟨universes, level⟩ := V.levels.headEq_level same
  rcases SInterp.head_inv laws first .refl with ⟨hu, _, rfl⟩ | ⟨hu, rfl⟩ <;>
    rcases SInterp.head_inv laws second .refl with ⟨hu', _, rfl⟩ | ⟨hu', rfl⟩
  · exact congrArg (fun k => universePack V (levelsBelow V l k) ξ) level
  · exact absurd (universes.mp hu) hu'
  · exact absurd (universes.mpr hu') hu
  · rfl

/-- Heads that are the same up to the package's head equality have one pack and
one shape at each level: universes of one level, or two leaves. -/
theorem head_coherent (laws : V.Laws) {h h' : Head} (same : V.rules.headEq h h') {l : L}
    {n : Nat} {ξ : World V.reading n} {P₁ P₂ : Pack V n}
    (first : InterpAt V l ξ (.head h) P₁) (second : InterpAt V l ξ (.head h') P₂) :
    P₁ = P₂ ∧ Shape V (InterpAt V l) .pair ξ (.head h) (.head h') := by
  obtain ⟨universes, level⟩ := V.levels.headEq_level same
  refine ⟨head_same laws same first second, ?_⟩
  rcases V.levels.universe_decided h with hu | hu
  · exact .univ .refl .refl hu (universes.mp hu) level
  · exact .total (Shape.of_methodForm laws first .refl (.inl ⟨h, rfl, hu⟩))
      (Shape.of_methodForm laws second .refl
        (.inl ⟨h', rfl, fun hu' => hu (universes.mpr hu')⟩))

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
