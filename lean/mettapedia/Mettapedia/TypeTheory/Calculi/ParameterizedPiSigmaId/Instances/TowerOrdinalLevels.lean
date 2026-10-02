import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.BelowDecidability
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerDecidability
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerEmbedding
import Mettapedia.TypeTheory.UniverseLevel.Notation

/-!
# Universes at closed levels, and the tower over the ordinal notations below ε₀

**Over any level order.** In the tower over a level order, the universe at a closed level is
a type of the universe at the successor level. In a formed context, a universe is a member of
another exactly when its level is strictly below the other's (`LevelTower.universeAt_mem_iff`),
usable at another exactly when its level is at most the other's
(`LevelTower.universeAt_below_iff`), and equal to another as a type exactly when the levels
are equal (`LevelTower.universeAt_typeEq_iff`). No universe is a member of itself.

**Over the ordinal notations.** The tower over the ordinal notations has a universe at every
level below ε₀. The universe at `ω` is a type of the universe at `ω + 1`; every finite
universe is a member of it and is usable at it; it is usable at no finite universe and is not
a member of itself.

The consequences of the normalization model hold at these levels as at the finite ones:
the typed equality of the tower over the ordinal notations is decided, and whether a type
is usable at another is decided.

Positive examples: `(u ω) : (u (ω + 1))`, `(u 7) : (u ω)`, `(u 7) ⊑ (u ω)`. Negative
examples: `(u ω) ⊑ (u 7)` fails, and `(u ω) : (u ω)` fails.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TowerModel

/-! ## Universes at closed levels, over any level order -/

namespace LevelTower

variable {L : Type} [LevelOrder L] {n : Nat} {Γ : Ctx (LevelTower.Head L) n}

/-- The universe at a closed level. -/
abbrev universeAt (c : L) : Tm (LevelTower.Head L) n := .head (.sort (.const c))

/-- The universe at a level is a type of the universe at the successor level. -/
theorem universeAt_typed (c : L) :
    Typed (LevelTower.rules L) Γ (universeAt c) (universeAt (LevelOrder.succ c)) :=
  Derivable.cumul (.headType (LevelTower.HeadTyping.sort _)) fun _ => le_refl _

/-- A universe is usable at every universe at a level above its own. -/
theorem universeAt_below {c d : L} (le : c ≤ d) :
    Below (LevelTower.rules L) Γ (universeAt c) (universeAt d) :=
  .subUniv fun _ => le

/-- A universe is a member of every universe at a strictly higher level. -/
theorem universeAt_mem {c d : L} (lt : c < d) :
    Typed (LevelTower.rules L) Γ (universeAt c) (universeAt d) :=
  Derivable.cumul (.headType (LevelTower.HeadTyping.sort _)) fun _ =>
    LevelOrder.succ_le_of_lt lt

/-- A universe is usable at another exactly when its level is at most the other's. -/
theorem universeAt_below_iff (formed : CtxFormed (LevelTower.rules L) Γ) {c d : L} :
    Below (LevelTower.rules L) Γ (universeAt c) (universeAt d) ↔ c ≤ d := by
  refine ⟨fun le => ?_, universeAt_below⟩
  obtain ⟨v, _, eV, below⟩ :=
    (Below.universe_iff (S := setting fun _ => (LevelOrder.bot : L)) TowerModel.facts
      algebra formed (LevelTower.IsUniverse.sort _)).1 le
  have raise : (LevelTower.rules L).cumulative (.sort (.const c)) (.sort (.const d)) :=
    algebra.same_right below
      (HeadSame.symm (levels fun _ => (LevelOrder.bot : L))
        (LevelTower.head_injective eV formed))
  exact raise fun _ => LevelOrder.bot

/-- A universe is a member of another exactly when its level is strictly below the
other's. -/
theorem universeAt_mem_iff (formed : CtxFormed (LevelTower.rules L) Γ) {c d : L} :
    Typed (LevelTower.rules L) Γ (universeAt c) (universeAt d) ↔ c < d := by
  refine ⟨fun typed => ?_, universeAt_mem⟩
  obtain ⟨u, headTyping, le⟩ := Typed.generation typed
  cases headTyping with
  | sort _ =>
    have below : Below (LevelTower.rules L) Γ (.head (.sort (.succ (.const c)))) (universeAt d) :=
      TypeLe.toBelow le
        (IsType.head_of_universe (S := setting fun _ => (LevelOrder.bot : L))
          (LevelTower.IsUniverse.sort _))
    obtain ⟨v, _, eV, raised⟩ :=
      (Below.universe_iff (S := setting fun _ => (LevelOrder.bot : L)) TowerModel.facts
        algebra formed (LevelTower.IsUniverse.sort _)).1 below
    have raise : (LevelTower.rules L).cumulative (.sort (.succ (.const c))) (.sort (.const d)) :=
      algebra.same_right raised
        (HeadSame.symm (levels fun _ => (LevelOrder.bot : L))
          (LevelTower.head_injective eV formed))
    exact LevelOrder.lt_of_succ_le (raise fun _ => LevelOrder.bot)

/-- Two universes are equal as types exactly when their levels are equal. -/
theorem universeAt_typeEq_iff (formed : CtxFormed (LevelTower.rules L) Γ) {c d : L} :
    TypeEq (LevelTower.rules L) Γ (universeAt c) (universeAt d) ↔ c = d := by
  constructor
  · intro equal
    rcases LevelTower.head_injective equal formed with same | same
    · cases same
      rfl
    · exact same fun _ => LevelOrder.bot
  · rintro rfl
    exact IsType.refl
      (IsType.head_of_universe (S := setting fun _ => (LevelOrder.bot : L))
        (LevelTower.IsUniverse.sort _))

/-- No universe is a member of itself. -/
theorem universeAt_not_mem_self (formed : CtxFormed (LevelTower.rules L) Γ) (c : L) :
    ¬ Typed (LevelTower.rules L) Γ (universeAt c) (universeAt c) := fun typed =>
  lt_irrefl _ ((universeAt_mem_iff formed).mp typed)

/-- A universe and the universe at the successor level are distinct types. -/
theorem universeAt_succ_ne (formed : CtxFormed (LevelTower.rules L) Γ) (c : L) :
    ¬ TypeEq (LevelTower.rules L) Γ (universeAt c) (universeAt (LevelOrder.succ c)) :=
  fun equal => ne_of_lt (LevelOrder.lt_succ c) ((universeAt_typeEq_iff formed).mp equal)

end LevelTower

/-! ## The tower over the ordinal notations -/

namespace OrdinalTower

/-- The rule package of the tower over the ordinal notations below ε₀. -/
abbrev rules : Rules (LevelTower.Head Level) := LevelTower.rules Level

variable {n : Nat} {Γ : Ctx (LevelTower.Head Level) n}

/-- The universe at a closed level. -/
abbrev universeAt (c : Level) : Tm (LevelTower.Head Level) n := LevelTower.universeAt c

/-! ## The universe at `ω` -/

/-- `(u ω) : (u (ω + 1))`. -/
theorem universe_omega_typed :
    Typed rules Γ (universeAt Level.omega) (universeAt (Level.succ Level.omega)) :=
  LevelTower.universeAt_typed Level.omega

/-- Every finite universe is a member of the universe at `ω`. -/
theorem universe_ofNat_mem_omega (k : Nat) :
    Typed rules Γ (universeAt (Level.ofNat k)) (universeAt Level.omega) :=
  LevelTower.universeAt_mem (Level.ofNat_lt_omega k)

/-- Every finite universe is usable at the universe at `ω`. -/
theorem universe_ofNat_below_omega (k : Nat) :
    Below rules Γ (universeAt (Level.ofNat k)) (universeAt Level.omega) :=
  LevelTower.universeAt_below (le_of_lt (Level.ofNat_lt_omega k))

/-- The universe at `ω` is usable at no finite universe. -/
theorem universe_omega_not_below_ofNat (formed : CtxFormed rules Γ) (k : Nat) :
    ¬ Below rules Γ (universeAt Level.omega) (universeAt (Level.ofNat k)) := fun below =>
  not_le_of_gt (Level.ofNat_lt_omega k) ((LevelTower.universeAt_below_iff formed).mp below)

/-- The universe at `ω` is not a member of itself. -/
theorem universe_omega_not_mem_self (formed : CtxFormed rules Γ) :
    ¬ Typed rules Γ (universeAt Level.omega) (universeAt Level.omega) := fun typed =>
  lt_irrefl _ ((LevelTower.universeAt_mem_iff formed).mp typed)

/-- The universes at `ω` and at `ω + 1` are distinct types. -/
theorem universe_omega_ne_succ (formed : CtxFormed rules Γ) :
    ¬ TypeEq rules Γ (universeAt Level.omega) (universeAt (Level.succ Level.omega)) :=
  LevelTower.universeAt_succ_ne formed Level.omega

/-! ## Decisions -/

/-- The typed equality of the tower over the ordinal notations is decided between two
terms of a type. -/
theorem equal_decide {t u T : Tm (LevelTower.Head Level) n} (formed : CtxFormed rules Γ)
    (typedT : Typed rules Γ t T) (typedU : Typed rules Γ u T) :
    Equal rules Γ t u T ∨ ¬ Equal rules Γ t u T :=
  LevelTower.equal_decide formed typedT typedU

/-- A typing of the tower over the natural numbers is a typing of the tower over the
ordinal notations, with its numerals read as finite levels. -/
theorem typed_ofNat {t A : Tm (LevelTower.Head Nat) n} {Δ : Ctx (LevelTower.Head Nat) n}
    (typed : Typed (LevelTower.rules Nat) Δ t A) :
    Typed rules (Δ.mapHead (LevelTower.Head.map (LevelOrder.Embedding.ofNat Level)))
      (t.mapHead (LevelTower.Head.map (LevelOrder.Embedding.ofNat Level)))
      (A.mapHead (LevelTower.Head.map (LevelOrder.Embedding.ofNat Level))) :=
  LevelTower.derivable_ofNat Level typed

end OrdinalTower

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
