import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.TruthLaws

/-!
# Determinism of truth, and generics read as themselves

When the code constructors and the constructors of the numbers are
constructors, their spines are weak-head normal, and so are generics applied
to arguments. Weak-head reduction is deterministic, so a code has at most one
truth value and a term at most one meaning at a carrier. At a function on a
data carrier two readings agree at every value, because every value is the
value of a closed term.

A generic applied to arguments reads, at the generic carrier that remains, as
its own meaning applied to the arguments' meanings. In particular a generic
reads as its meaning.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

variable {Head : Type} {S : Reading Head}

/-! ## The size of a carrier -/

/-- The number of constructors of a carrier. -/
def Carrier.size : {k : Kind} → Carrier k → Nat
  | _, .prop => 1
  | _, .rigid _ => 1
  | _, .num => 1
  | _, .arr A B => A.size + B.size + 1

theorem Carrier.size_dom {k k' : Kind} (A : Carrier k) (B : Carrier k') :
    A.size < (Carrier.arr A B).size :=
  Nat.lt_succ_of_le (Nat.le_add_right _ _)

theorem Carrier.size_cod {k k' : Kind} (A : Carrier k) (B : Carrier k') :
    B.size < (Carrier.arr A B).size :=
  Nat.lt_succ_of_le (Nat.le_add_left _ _)

/-! ## Determinism -/

mutual

theorem Truth.deterministic (laws : S.Laws) : ∀ {n : Nat} {ξ : World S n} {t : Tm Head n}
    {P P' : S.P}, Truth S ξ t P → Truth S ξ t P' → P = P'
  | _, _, _, _, _, .imp red p q, second => by
      cases second with
      | imp red' p' q' =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_imp _ _) (laws.whnf_imp _ _)
          cases e
          rw [Truth.deterministic laws p p', Truth.deterministic laws q q']
      | all carrier red' _ =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_imp _ _)
            (laws.whnf_all carrier _)
          cases e
      | eq carrier red' _ _ =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_imp _ _)
            (laws.whnf_eq carrier _ _)
          cases e
          rw [laws.impNotEq] at carrier
          cases carrier
      | generic red' _ =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_imp _ _)
            (laws.whnf_generic _ _)
          exact absurd (show appSpine (.const S.imp) [_, _] = _ from e) constSpine_ne_varSpine
      | neutral red' neutral =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_imp _ _)
            (laws.neutral_whnf neutral)
          exact absurd e.symm (laws.neutral_ne_imp neutral)
  | _, _, _, _, _, .all carrier red f, second => by
      cases second with
      | imp red' _ _ =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_all carrier _)
            (laws.whnf_imp _ _)
          cases e
      | all carrier' red' f' =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_all carrier _)
            (laws.whnf_all carrier' _)
          cases e
          rw [carrier] at carrier'
          cases carrier'
          rw [Read.deterministic laws f f']
      | eq carrier' red' _ _ =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_all carrier _)
            (laws.whnf_eq carrier' _ _)
          cases e
      | generic red' _ =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_all carrier _)
            (laws.whnf_generic _ _)
          exact absurd (show appSpine (.const _) [_] = _ from e) constSpine_ne_varSpine
      | neutral red' neutral =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_all carrier _)
            (laws.neutral_whnf neutral)
          exact absurd e.symm (laws.neutral_ne_all neutral carrier)
  | _, _, _, _, _, .eq carrier red x y, second => by
      cases second with
      | imp red' _ _ =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_eq carrier _ _)
            (laws.whnf_imp _ _)
          cases e
          rw [laws.impNotEq] at carrier
          cases carrier
      | all carrier' red' _ =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_eq carrier _ _)
            (laws.whnf_all carrier' _)
          cases e
      | eq carrier' red' x' y' =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_eq carrier _ _)
            (laws.whnf_eq carrier' _ _)
          cases e
          rw [carrier] at carrier'
          cases carrier'
          rw [Read.deterministic laws x x', Read.deterministic laws y y']
      | generic red' _ =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_eq carrier _ _)
            (laws.whnf_generic _ _)
          exact absurd (show appSpine (.const _) [_, _] = _ from e) constSpine_ne_varSpine
      | neutral red' neutral =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_eq carrier _ _)
            (laws.neutral_whnf neutral)
          exact absurd e.symm (laws.neutral_ne_eq neutral carrier)
  | _, _, _, _, _, .generic red apply, second => by
      cases second with
      | imp red' _ _ =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_generic _ _)
            (laws.whnf_imp _ _)
          exact absurd (show appSpine (.const S.imp) [_, _] = _ from e.symm) constSpine_ne_varSpine
      | all carrier' red' _ =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_generic _ _)
            (laws.whnf_all carrier' _)
          exact absurd (show appSpine (.const _) [_] = _ from e.symm) constSpine_ne_varSpine
      | eq carrier' red' _ _ =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_generic _ _)
            (laws.whnf_eq carrier' _ _)
          exact absurd (show appSpine (.const _) [_, _] = _ from e.symm) constSpine_ne_varSpine
      | generic red' apply' =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_generic _ _)
            (laws.whnf_generic _ _)
          obtain ⟨e₁, e₂⟩ := appSpine_injective (by trivial) (by trivial) e
          cases e₁
          subst e₂
          exact Apply.deterministic laws apply apply'
      | neutral red' neutral =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_generic _ _)
            (laws.neutral_whnf neutral)
          exact absurd e.symm (laws.neutral_ne_var neutral)
  | _, _, _, _, _, .neutral red neutral, second => by
      cases second with
      | imp red' _ _ =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.neutral_whnf neutral)
            (laws.whnf_imp _ _)
          exact absurd e (laws.neutral_ne_imp neutral)
      | all carrier' red' _ =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.neutral_whnf neutral)
            (laws.whnf_all carrier' _)
          exact absurd e (laws.neutral_ne_all neutral carrier')
      | eq carrier' red' _ _ =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.neutral_whnf neutral)
            (laws.whnf_eq carrier' _ _)
          exact absurd e (laws.neutral_ne_eq neutral carrier')
      | generic red' _ =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.neutral_whnf neutral)
            (laws.whnf_generic _ _)
          exact absurd e (laws.neutral_ne_var neutral)
      | neutral _ _ => rfl

theorem Read.deterministic (laws : S.Laws) : ∀ {n : Nat} {ξ : World S n} {t : Tm Head n}
    {k : Kind} {A : Carrier k} {v v' : A.V S}, Read S ξ t A v → Read S ξ t A v' → v = v'
  | _, _, _, _, _, _, _, .prop truth, second => by
      cases second with
      | prop truth' => exact Truth.deterministic laws truth truth'
  | _, _, _, _, _, _, _, @Read.rigid _ _ _ _ _ _T _u, second => by
      cases second
      rfl
  | _, _, _, _, _, _, _, .data _, second => by
      cases second
      rfl
  | _, _, _, _, _, _, _, .dataArg read, second => by
      cases second with
      | dataArg read' =>
          funext q
          obtain ⟨s, related, rfl⟩ := dataValue_surjective q
          have e := Read.deterministic laws (read (Morph.id _) (related.rename₂ Fin.elim0))
            (read' (Morph.id _) (related.rename₂ Fin.elim0))
          rw [dataValue_rename related Fin.elim0] at e
          exact e
  | _, _, _, _, _, _, _, .genericArg read, second => by
      cases second with
      | genericArg read' =>
          funext v
          exact Read.deterministic laws (read v) (read' v)

theorem Apply.deterministic (laws : S.Laws) : ∀ {n : Nat} {ξ : World S n} {A : Carrier .gen}
    {v : A.V S} {args : List (Tm Head n)} {P P' : S.P},
    Apply S ξ A v args P → Apply S ξ A v args P' → P = P'
  | _, _, _, _, _, _, _, .done, .done => rfl
  | _, _, _, _, _, _, _, .arg read rest, .arg read' rest' => by
      have e := Read.deterministic laws read read'
      subst e
      exact Apply.deterministic laws rest rest'

end

/-! ## Generics read as themselves -/

/-- A generic meaning applied to some arguments, with the carrier and meaning
that remain. -/
inductive Partial (S : Reading Head) : {n : Nat} → World S n → (A : Carrier .gen) → A.V S →
    List (Tm Head n) → (B : Carrier .gen) → B.V S → Prop where
  | nil {n : Nat} {ξ : World S n} {A : Carrier .gen} {v : A.V S} : Partial S ξ A v [] A v
  | cons {n : Nat} {ξ : World S n} {k : Kind} {A₁ : Carrier k} {A₂ : Carrier .gen}
      {φ : (Carrier.arr A₁ A₂).V S} {a : Tm Head n} {args : List (Tm Head n)} {v₁ : A₁.V S}
      {B : Carrier .gen} {w : B.V S} :
      Read S ξ a A₁ v₁ → Partial S ξ A₂ (φ v₁) args B w →
      Partial S ξ (.arr A₁ A₂) φ (a :: args) B w

theorem Partial.apply : ∀ {n : Nat} {ξ : World S n} {A : Carrier .gen} {v : A.V S}
    {args : List (Tm Head n)} {P : S.P}, Partial S ξ A v args .prop P →
      Apply S ξ A v args P
  | _, _, _, _, _, _, .nil => .done
  | _, _, _, _, _, _, .cons read rest => .arg read (Partial.apply rest)

theorem Partial.append : ∀ {n : Nat} {ξ : World S n} {A : Carrier .gen} {v : A.V S}
    {args : List (Tm Head n)} {k : Kind} {A₁ : Carrier k} {B : Carrier .gen}
    {w : (Carrier.arr A₁ B).V S},
    Partial S ξ A v args (.arr A₁ B) w → ∀ {b : Tm Head n} {v₁ : A₁.V S},
      Read S ξ b A₁ v₁ → Partial S ξ A v (args ++ [b]) B (w v₁)
  | _, _, _, _, _, _, _, _, _, .nil, _, _, read => .cons read .nil
  | _, _, _, _, _, _, _, _, _, .cons read' rest, _, _, read =>
      .cons read' (Partial.append rest read)

theorem Partial.rename {n m : Nat} {ξ : World S n} {ξ' : World S m} {ρ : Ren n m}
    (morph : Morph ξ ξ' ρ) {A : Carrier .gen} {v : A.V S} {args : List (Tm Head n)}
    {B : Carrier .gen} {w : B.V S} (part : Partial S ξ A v args B w) :
    Partial S ξ' A v (args.map (Presentation.rename ρ)) B w := by
  induction part with
  | nil => exact .nil
  | cons read _ ih => exact .cons (read.rename morph) ih

/-- A generic applied to arguments reads, at the generic carrier that remains,
as its meaning applied to theirs. -/
theorem Read.generic_spine : ∀ (B : Carrier .gen) {n : Nat} {ξ : World S n} {i : Fin n}
    {args : List (Tm Head n)} {w : B.V S},
    Partial S ξ (ξ i).1 (ξ i).2 args B w → Read S ξ (appSpine (.var i) args) B w
  | .prop, _, _, _, _, _, part => .prop (.generic .refl part.apply)
  | .rigid _, _, _, _, _, _, _ => .rigid
  | @Carrier.arr .data .gen A₁ B', _, ξ, i, args, w, part =>
      .dataArg fun {m ξ' ρ} morph {s} related => by
        rw [rename_appSpine, ← appSpine_concat]
        have part' := (part.rename morph).append (Read.data (ξ := ξ') related)
        rw [← morph i] at part'
        exact Read.generic_spine B' part'
  | @Carrier.arr .gen .gen A₁ B', _, ξ, i, args, w, part =>
      .genericArg fun v => by
        rw [rename_appSpine, ← appSpine_concat]
        have self : Partial S (ξ.snoc ⟨A₁, v⟩) ((ξ.snoc ⟨A₁, v⟩) 0).1 ((ξ.snoc ⟨A₁, v⟩) 0).2
            [] A₁ v := .nil
        have zero := Read.generic_spine A₁ (i := 0) self
        have part' := (part.rename (Morph.wk ξ ⟨A₁, v⟩)).append (b := .var 0) zero
        exact Read.generic_spine B' part'
termination_by B => B.size
decreasing_by
  · exact Carrier.size_cod _ _
  · exact Carrier.size_dom _ _
  · exact Carrier.size_cod _ _

/-- A generic reads as its meaning. -/
theorem Read.generic' {n : Nat} (ξ : World S n) {i : Fin n} {A : Carrier .gen} {v : A.V S}
    (at_i : ξ i = ⟨A, v⟩) : Read S ξ (.var i) A v := by
  have part : Partial S ξ (ξ i).1 (ξ i).2 [] A v := by
    rw [at_i]
    exact .nil
  exact Read.generic_spine (args := []) A part

theorem Read.generic {n : Nat} (ξ : World S n) (i : Fin n) :
    Read S ξ (.var i) (ξ i).1 (ξ i).2 :=
  Read.generic' ξ rfl

/-- A generic of carrier `prop` reads as its truth value. -/
theorem Read.generic_prop {n : Nat} (ξ : World S n) {i : Fin n} {P : S.P}
    (at_i : ξ i = ⟨.prop, P⟩) : Read S ξ (.var i) .prop P :=
  Read.generic' ξ at_i

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
