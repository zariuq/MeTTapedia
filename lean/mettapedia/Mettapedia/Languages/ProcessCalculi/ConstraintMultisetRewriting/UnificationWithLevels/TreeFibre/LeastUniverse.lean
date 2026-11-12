import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Widening

/-!
# The least universe of a normal type

A normal type of a formed telescope is a type of a least universe: a universe `ℓ` such that the type lies in `U_ℓ`
and `ℓ` lies below every universe the type lies in (`least_universe`). It is read off the normal form: a head is in
the universe that types it; a Π or Σ type in the join of its parts' least universes; an identity type in its type's;
a neutral type in the universe its spine's principal type is equal to.

This is the principal-universe lemma for normal forms. With `typed_widen` it says how a widened declaration moves
the least universe: by at most up to the widened universe. It is the first half of deciding incomparable codomains
by a greatest lower bound; the second half, that the least universes of the solutions lie below a greatest lower
bound of the two codomains, is a statement about the level order, not proved here.

The head typing is assumed functional (`headTypingUnique`), as in the tower.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ContextualDependentEtaLong ContextualDependentCumulative ContextualDependentUniverseInjective

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **`ℓ` is the least universe of `V` over `Γ`.** -/
def LeastUniverse {n : Nat} (Γ : Ctx Head n) (V : Tm Head n) (ℓ : Head) : Prop :=
  S.R.isUniverse ℓ ∧ Typed S.R Γ V (.head ℓ) ∧ ∀ u, S.R.isUniverse u → Typed S.R Γ V (.head u) → S.R.cumulative ℓ u

variable (facts : FormFacts S.R S.roles) (algebra : CumulativeAlgebra S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

include facts algebra in
/-- A neutral type has a least universe: the one its spine's principal type is equal to. -/
theorem least_universe_spine {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {V U : Tm Head n} {top : Head}
    (spine : Long S.R S.roles (.spine Γ V U)) (htop : S.R.isUniverse top) (le : Below S.R Γ U (.head top)) :
    ∃ ℓ, LeastUniverse (S := S) Γ V ℓ := by
  obtain ⟨k, hk, eU, _⟩ := Below.universe_target facts le formed htop (IsType.refl (IsType.head_of_universe htop))
  refine ⟨k, hk, Typed.convType spine.spine_typed eU, fun u _ typed => ?_⟩
  have principal : Below S.R Γ U (.head u) := spine_principal facts V formed spine typed
  obtain ⟨x, _, eX, c⟩ := Below.universe_cumulative facts algebra principal formed hk eU
  exact algebra.same_right c (TypeEq.head_injective facts eX.symm formed)

include facts algebra headTypingUnique in
/-- **The least universe of a normal type.** -/
theorem least_universe : ∀ {n : Nat} (V : Tm Head n) {Γ : Ctx Head n}, CtxFormed S.R Γ →
    Long S.R S.roles (.type Γ V) → ∃ ℓ, LeastUniverse (S := S) Γ V ℓ := by
  intro n V
  induction V with
  | head h =>
      intro Γ formed long
      obtain ⟨u₀, hu₀, typed₀⟩ := long.isType
      obtain ⟨k, typing, _⟩ := head_typed_cumulative facts algebra formed hu₀ typed₀
      refine ⟨k, S.levels.ground_typing typing, Derivable.headType typing, fun u hu typed => ?_⟩
      obtain ⟨k', typing', c⟩ := head_typed_cumulative facts algebra formed hu typed
      rw [headTypingUnique typing typing']
      exact c
  | pi A B ihA ihB =>
      intro Γ formed long
      cases long with
      | pi lA lB _ =>
          obtain ⟨ℓA, uA, tA, leastA⟩ := ihA formed lA
          obtain ⟨ℓB, uB, tB, leastB⟩ := ihB (formed.snoc lA.isType) lB
          obtain ⟨w, join⟩ := S.levels.join_exists uA uB
          refine ⟨w, (S.levels.join_level join).1, Derivable.piForm tA uA tB uB join, fun u hu typed => ?_⟩
          have generation : GenerationAt S.R Γ (.pi A B) (.head u) := Typed.generation typed
          obtain ⟨u₁, u₂, w', tA', hu₁, tB', hu₂, join', le⟩ := generation
          have cw := typeLe_head_cumulative facts algebra formed (S.levels.join_level join').1 hu le
          obtain ⟨c₁, c₂⟩ := S.levels.join_upper join'
          exact algebra.join_least join (algebra.trans (leastA u₁ hu₁ tA') (algebra.trans c₁ cw))
            (algebra.trans (leastB u₂ hu₂ tB') (algebra.trans c₂ cw))
      | neutralType ls _ _ => cases ls
  | sigma A B ihA ihB =>
      intro Γ formed long
      cases long with
      | sigma lA lB _ =>
          obtain ⟨ℓA, uA, tA, leastA⟩ := ihA formed lA
          obtain ⟨ℓB, uB, tB, leastB⟩ := ihB (formed.snoc lA.isType) lB
          obtain ⟨w, join⟩ := S.levels.join_exists uA uB
          refine ⟨w, (S.levels.join_level join).1, Derivable.sigmaForm tA uA tB uB join, fun u hu typed => ?_⟩
          have generation : GenerationAt S.R Γ (.sigma A B) (.head u) := Typed.generation typed
          obtain ⟨u₁, u₂, w', tA', hu₁, tB', hu₂, join', le⟩ := generation
          have cw := typeLe_head_cumulative facts algebra formed (S.levels.join_level join').1 hu le
          obtain ⟨c₁, c₂⟩ := S.levels.join_upper join'
          exact algebra.join_least join (algebra.trans (leastA u₁ hu₁ tA') (algebra.trans c₁ cw))
            (algebra.trans (leastB u₂ hu₂ tB') (algebra.trans c₂ cw))
      | neutralType ls _ _ => cases ls
  | id A a b ihA _ _ =>
      intro Γ formed long
      cases long with
      | id lA la lb _ =>
          obtain ⟨ℓA, uA, tA, leastA⟩ := ihA formed lA
          refine ⟨ℓA, uA, Derivable.idForm tA uA la.typed lb.typed, fun u hu typed => ?_⟩
          have generation : GenerationAt S.R Γ (.id A a b) (.head u) := Typed.generation typed
          obtain ⟨u₁, tA', hu₁, _, _, le⟩ := generation
          exact algebra.trans (leastA u₁ hu₁ tA') (typeLe_head_cumulative facts algebra formed hu₁ hu le)
      | neutralType ls _ _ => cases ls
  | var i =>
      intro Γ formed long
      cases long with
      | neutralType ls htop le => exact least_universe_spine facts algebra formed ls htop le
  | const c =>
      intro Γ formed long
      cases long with
      | neutralType ls htop le => exact least_universe_spine facts algebra formed ls htop le
  | app f a _ _ =>
      intro Γ formed long
      cases long with
      | neutralType ls htop le => exact least_universe_spine facts algebra formed ls htop le
  | fst p _ =>
      intro Γ formed long
      cases long with
      | neutralType ls htop le => exact least_universe_spine facts algebra formed ls htop le
  | snd p _ =>
      intro Γ formed long
      cases long with
      | neutralType ls htop le => exact least_universe_spine facts algebra formed ls htop le
  | lam _ _ =>
      intro Γ _ long
      cases long with
      | neutralType ls _ _ => cases ls
  | pair _ _ _ _ =>
      intro Γ _ long
      cases long with
      | neutralType ls _ _ => cases ls
  | refl _ _ =>
      intro Γ _ long
      cases long with
      | neutralType ls _ _ => cases ls

include facts algebra in
/-- **Least universes and widening**: over a narrowing below `u`, a normal type of the wide telescope whose least
universe in the narrow one lies below `u` has its least universe in the wide one below `u`. -/
theorem least_universe_widen {n : Nat} {Γ Δ : Ctx Head n} {u : Head} (hu : S.R.isUniverse u)
    (nb : NarrowsBelow S.R u Γ Δ) (formedΓ : CtxFormed S.R Γ) (formedΔ : CtxFormed S.R Δ) {V : Tm Head n}
    (long : Long S.R S.roles (.type Γ V)) {ℓΔ ℓΓ : Head} (narrowLeast : LeastUniverse (S := S) Δ V ℓΔ)
    (wideLeast : LeastUniverse (S := S) Γ V ℓΓ) (below : S.R.cumulative ℓΔ u) : S.R.cumulative ℓΓ u := by
  have narrowTyped : Typed S.R Δ V (.head u) := Derivable.cumul narrowLeast.2.1 below
  exact wideLeast.2.2 u hu (typed_widen facts algebra V hu nb formedΓ formedΔ long narrowTyped)

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
