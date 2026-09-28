import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Decoding
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.InterpPER

/-!
# Stuck terms in the partial equivalences of the model

A stuck term is neither a numeral, nor a code, nor an interpreted type. So a
partial equivalence of the model that relates a stuck term to itself relates
it to every stuck term: the equivalences of the numbers, the codes and the
universes relate no stuck term, the others relate all terms or none, and
functions and pairs reduce the question to stuck eliminations.

The same holds for a type-like term and its decoding, except in a universe,
where the two must have one interpretation. That case is supplied by the
coherence of decoding.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {M : Model Head L}

theorem Stuck.head_not_var {n : Nat} {t : Tm Head n} (stuck : Stuck M t) :
    ∀ {i : Fin n}, (headArgs t).1 ≠ .var i := by
  induction stuck with
  | appLike a like =>
      intro i e
      simp only [headArgs] at e
      cases like <;> cases e
  | appStuck a _ ih => intro i e; simp only [headArgs] at e; exact ih e
  | fstLike _ => intro i e; cases e
  | fstStuck _ _ => intro i e; cases e
  | sndLike _ => intro i e; cases e
  | sndStuck _ _ => intro i e; cases e

theorem TypeLike.not_const {n : Nat} {t : Tm Head n} (like : TypeLike M t) (c : DeclName) :
    t ≠ .const c := by
  cases like <;> intro e <;> cases e

theorem Stuck.not_const {n : Nat} {t : Tm Head n} (stuck : Stuck M t) (c : DeclName) :
    t ≠ .const c := by
  cases stuck <;> intro e <;> cases e

/-- The function of an application whose function is type-like or stuck is
not a constant. -/
theorem not_const_of_app_stuck {n : Nat} {t a : Tm Head n} (stuck : Stuck M (.app t a)) :
    ∀ c, t ≠ .const c := by
  cases stuck with
  | appLike _ like => exact like.not_const
  | appStuck _ s => exact s.not_const

theorem head_of_constSpine {n : Nat} {c : DeclName} {args : List (Tm Head n)}
    {t : Tm Head n} (e : appSpine (.const c) args = t) : (headArgs t).1 = .const c := by
  rw [← e, headArgs_appSpine (by trivial)]

theorem head_of_varSpine {n : Nat} {i : Fin n} {args : List (Tm Head n)}
    {t : Tm Head n} (e : appSpine (.var i) args = t) : (headArgs t).1 = .var i := by
  rw [← e, headArgs_appSpine (by trivial)]

theorem TypeLike.head_not_var {n : Nat} {t : Tm Head n} (like : TypeLike M t) {i : Fin n} :
    (headArgs t).1 ≠ .var i := by
  cases like <;> intro e <;> cases e

section Laws

variable (laws : M.Laws)
include laws

/-- A constructor of the setting is not `holds`, which is rigid. -/
theorem ne_holds_of_constructor {c : DeclName} {k : Nat} (role : M.roles c = .constructor k) :
    c ≠ M.holds := by
  intro e
  rw [e, laws.holds] at role
  cases role

theorem Stuck.not_numVal {n : Nat} {t : Tm Head n} (stuck : Stuck M t) {k : Nat} :
    ¬ NumVal M.reading t k := by
  intro value
  cases value with
  | zero red =>
      have e := WhRed.of_whnf (stuck.whnf laws) red
      exact stuck.not_const _ e.symm
  | suc red _ =>
      have e := WhRed.of_whnf (stuck.whnf laws) red
      exact ne_holds_of_constructor laws laws.reading.suc
        (stuck.head_const (head_of_constSpine (args := [_]) e))

theorem Stuck.not_truth {n : Nat} {ξ : World M.reading n} {t : Tm Head n} (stuck : Stuck M t)
    {P : Prop} : ¬ Truth M.reading ξ t P := by
  intro truth
  cases truth with
  | imp red _ _ =>
      have e := WhRed.of_whnf (stuck.whnf laws) red
      exact ne_holds_of_constructor laws laws.reading.imp
        (stuck.head_const (head_of_constSpine (args := [_, _]) e))
  | all carrier red _ =>
      have e := WhRed.of_whnf (stuck.whnf laws) red
      exact ne_holds_of_constructor laws (laws.reading.all carrier)
        (stuck.head_const (head_of_constSpine (args := [_]) e))
  | eq carrier red _ _ =>
      have e := WhRed.of_whnf (stuck.whnf laws) red
      exact ne_holds_of_constructor laws (laws.reading.eq carrier)
        (stuck.head_const (head_of_constSpine (args := [_, _]) e))
  | generic red _ =>
      have e := WhRed.of_whnf (stuck.whnf laws) red
      exact stuck.head_not_var (head_of_varSpine e)
  | neutral _ neutral => exact neutral.elim

theorem TypeLike.not_numVal {n : Nat} {t : Tm Head n} (like : TypeLike M t) {k : Nat} :
    ¬ NumVal M.reading t k := by
  intro value
  cases value with
  | zero red =>
      have e := WhRed.of_whnf (like.whnf laws) red
      exact like.not_const _ e.symm
  | suc red _ =>
      have e := WhRed.of_whnf (like.whnf laws) red
      exact ne_holds_of_constructor laws laws.reading.suc
        (like.head_const (head_of_constSpine (args := [_]) e))

theorem TypeLike.not_truth {n : Nat} {ξ : World M.reading n} {t : Tm Head n} (like : TypeLike M t)
    {P : Prop} : ¬ Truth M.reading ξ t P := by
  intro truth
  cases truth with
  | imp red _ _ =>
      have e := WhRed.of_whnf (like.whnf laws) red
      exact ne_holds_of_constructor laws laws.reading.imp
        (like.head_const (head_of_constSpine (args := [_, _]) e))
  | all carrier red _ =>
      have e := WhRed.of_whnf (like.whnf laws) red
      exact ne_holds_of_constructor laws (laws.reading.all carrier)
        (like.head_const (head_of_constSpine (args := [_]) e))
  | eq carrier red _ _ =>
      have e := WhRed.of_whnf (like.whnf laws) red
      exact ne_holds_of_constructor laws (laws.reading.eq carrier)
        (like.head_const (head_of_constSpine (args := [_, _]) e))
  | generic red _ =>
      have e := WhRed.of_whnf (like.whnf laws) red
      exact like.head_not_var (head_of_varSpine e)
  | neutral _ neutral => exact neutral.elim

/-- A stuck term is not an interpreted type. -/
theorem Stuck.not_interp {l : L} {below : L → IRel M.reading} {n : Nat} {ξ : World M.reading n}
    {t : Tm Head n} (stuck : Stuck M t) {R : Rel Head n} : ¬ Interp M l below ξ t R := by
  intro interp
  cases interp with
  | sort _ _ red =>
      have e := WhRed.of_whnf (stuck.whnf laws) red
      cases stuck <;> cases e
  | ground _ red =>
      have e := WhRed.of_whnf (stuck.whnf laws) red
      cases stuck <;> cases e
  | pi red =>
      have e := WhRed.of_whnf (stuck.whnf laws) red
      cases stuck <;> cases e
  | sigma red =>
      have e := WhRed.of_whnf (stuck.whnf laws) red
      cases stuck <;> cases e
  | ident red =>
      have e := WhRed.of_whnf (stuck.whnf laws) red
      cases stuck <;> cases e
  | num red =>
      have e := WhRed.of_whnf (stuck.whnf laws) red
      exact stuck.not_const _ e.symm
  | prop red =>
      have e := WhRed.of_whnf (stuck.whnf laws) red
      exact stuck.not_const _ e.symm
  | holds red _ =>
      have e := WhRed.of_whnf (stuck.whnf laws) red
      rw [← e] at stuck
      exact not_const_of_app_stuck stuck _ rfl
  | rigid red _ _ notHolds =>
      have e := WhRed.of_whnf (stuck.whnf laws) red
      exact notHolds (stuck.head_const (head_of_constSpine e))

end Laws

/-! ## Stuck terms in the partial equivalences -/

section Relations

variable (laws : M.Laws) {l : L} {below : L → IRel M.reading}
include laws

/-- A partial equivalence of the model that relates a stuck term to itself
relates it to every stuck term. -/
theorem Interp.stuck
    (belowStuck : ∀ k {n : Nat} {ξ : World M.reading n} {x : Tm Head n} {R' : Rel Head n},
      Stuck M x → ¬ below k ξ x R') :
    ∀ {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n}, Interp M l below ξ A R →
      ∀ {x y : Tm Head n}, Stuck M x → Stuck M y → R x x → R x y
  | _, ξ, _, _, .sort _ _ _, x, _, sx, _, hxx => by
      obtain ⟨R', hx, _⟩ := hxx (Morph.id ξ)
      rw [rename_id] at hx
      exact absurd hx (belowStuck _ sx)
  | _, _, _, _, .ground _ _, _, _, _, _, _ => trivial
  | _, _, _, _, .pi _ P _ codInterp _, _, _, sx, sy, hxx => by
      intro w a b ha _
      exact Interp.stuck belowStuck (codInterp w ha) (.appStuck a (sx.rename _))
        (.appStuck b (sy.rename _)) (hxx w ha ha)
  | _, ξ, _, _, .sigma _ P domInterp codInterp _, _, _, sx, sy, hxx => by
      obtain ⟨hp, hd, hc⟩ := hxx
      exact ⟨hp, Interp.stuck belowStuck (domInterp (Morph.id ξ)) (.fstStuck sx) (.fstStuck sy) hd,
        Interp.stuck belowStuck (codInterp (Morph.id ξ) hp) (.sndStuck sx) (.sndStuck sy) hc⟩
  | _, _, _, _, .ident _ _ _ _ _, _, _, _, _, hxx => hxx
  | _, _, _, _, .num _, _, _, sx, _, hxx => by
      obtain ⟨k, hk, _⟩ := hxx
      exact absurd hk (sx.not_numVal laws)
  | _, _, _, _, .prop _, _, _, sx, _, hxx => by
      obtain ⟨P, hP, _⟩ := hxx
      exact absurd hP (sx.not_truth laws)
  | _, _, _, _, .holds _ _, _, _, _, _, hxx => hxx
  | _, _, _, _, .rigid _ _ _ _, _, _, _, _, _ => trivial

/-- A partial equivalence of the model that relates two type-like terms each to
itself relates them to each other, provided that at a universe the two have
one interpretation at every world. -/
theorem Interp.typeLike
    (belowStuck : ∀ k {n : Nat} {ξ : World M.reading n} {x : Tm Head n} {R' : Rel Head n},
      Stuck M x → ¬ below k ξ x R') :
    ∀ {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n}, Interp M l below ξ A R →
      ∀ {x y : Tm Head n}, TypeLike M x → TypeLike M y →
      (∀ k {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ → ∀ {R₁ R₂ : Rel Head m},
        below k ξ' (Presentation.rename ρ x) R₁ → below k ξ' (Presentation.rename ρ y) R₂ →
          R₁ = R₂) →
      R x x → R y y → R x y
  | _, _, _, _, .sort _ _ _, _, _, _, _, coherent, hxx, hyy => by
      intro w
      obtain ⟨R₁, hx, _⟩ := hxx w
      obtain ⟨R₂, hy, _⟩ := hyy w
      rw [coherent _ w hx hy] at hx
      exact ⟨R₂, hx, hy⟩
  | _, _, _, _, .ground _ _, _, _, _, _, _, _, _ => trivial
  | _, _, _, _, .pi _ P _ codInterp _, _, _, lx, ly, _, hxx, _ => by
      intro w a b ha _
      exact Interp.stuck laws belowStuck (codInterp w ha) (.appLike a (lx.rename _))
        (.appLike b (ly.rename _)) (hxx w ha ha)
  | _, ξ, _, _, .sigma _ P domInterp codInterp _, _, _, lx, ly, _, hxx, _ => by
      obtain ⟨hp, hd, hc⟩ := hxx
      exact ⟨hp, Interp.stuck laws belowStuck (domInterp (Morph.id ξ)) (.fstLike lx)
          (.fstLike ly) hd,
        Interp.stuck laws belowStuck (codInterp (Morph.id ξ) hp) (.sndLike lx) (.sndLike ly) hc⟩
  | _, _, _, _, .ident _ _ _ _ _, _, _, _, _, _, hxx, _ => hxx
  | _, _, _, _, .num _, _, _, lx, _, _, hxx, _ => by
      obtain ⟨k, hk, _⟩ := hxx
      exact absurd hk (lx.not_numVal laws)
  | _, _, _, _, .prop _, _, _, lx, _, _, hxx, _ => by
      obtain ⟨P, hP, _⟩ := hxx
      exact absurd hP (lx.not_truth laws)
  | _, _, _, _, .holds _ _, _, _, _, _, _, hxx, _ => hxx
  | _, _, _, _, .rigid _ _ _ _, _, _, _, _, _, _, _ => trivial

/-- The levels below a level interpret no stuck term. -/
theorem levelsBelow_stuck (k : L) {n : Nat} {ξ : World M.reading n} {x : Tm Head n} {R' : Rel Head n}
    (stuck : Stuck M x) : ¬ levelsBelow M l k ξ x R' := by
  intro h
  have hk := levelsBelow_lt h
  have h' := (levelsBelow_iff M hk ξ x R').mp h
  exact stuck.not_interp laws h'

end Relations

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
