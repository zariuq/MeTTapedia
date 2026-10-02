import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.WrittenDomains

/-!
# Written domains in the cumulative tower

In the cumulative tower the identity on the ground type and the identity on the
lowest universe erase to the same term, and each is typed, yet they are equal at
no type; and a λ whose written domain disagrees with the domain it is checked at
is rejected, though its erasure is typed there.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

/-! ## Controls in the cumulative tower -/

section Tower

open Mettapedia.TypeTheory.UniverseLevel
open TowerModel

/-- The ground type of the tower, and the arrows on it and on the lowest
universe. -/
abbrev groundType : Tm Tower.Head 0 := .head .legacyGround
abbrev groundArrow : Tm Tower.Head 0 := .pi (.head .legacyGround) (.head .legacyGround)
abbrev universeArrow : Tm Tower.Head 0 :=
  .pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))

/-- The identity with its domain written as the ground type, the identity with
its domain written as the lowest universe, and the identity with no domain
written. -/
def groundIdentity : ATm Tower.Head 0 := .lamTyped (.head .legacyGround) (.var 0)
def universeIdentity : ATm Tower.Head 0 := .lamTyped (.head (.sort Tower.zero)) (.var 0)
def bareIdentity : ATm Tower.Head 0 := .lamBare (.var 0)

theorem groundArrow_typed :
    Typed Tower.rules .nil groundArrow (.head (.sort (.max Tower.zero Tower.zero))) :=
  .piForm (.headType .legacyGround) (.sort _) (.headType .legacyGround) (.sort _)
    (.sorts _ _)

theorem universeArrow_typed :
    Typed Tower.rules .nil universeArrow
      (.head (.sort (.max (.succ Tower.zero) (.succ Tower.zero)))) :=
  .piForm (.headType (.sort _)) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

/-- Positive: the identity with the ground type written is typed at the arrow on
the ground type. -/
theorem groundIdentity_typed : ATyped Tower.rules .nil groundIdentity groundArrow :=
  .lamTyped (.headType .legacyGround) (.sort _) (.refl (.headType .legacyGround))
    groundArrow_typed (.sort _) (.var 0)

theorem bareIdentity_typed : ATyped Tower.rules .nil bareIdentity groundArrow :=
  .lamBare groundArrow_typed (.sort _) (.var 0)

theorem universeIdentity_typed : ATyped Tower.rules .nil universeIdentity universeArrow :=
  .lamTyped (.headType (.sort _)) (.sort _) (.refl (.headType (.sort _)))
    universeArrow_typed (.sort _) (.var 0)

/-- Positive: a written domain that agrees does not change equality. -/
theorem bare_equal_ground : AEqual Tower.rules .nil bareIdentity groundIdentity groundArrow :=
  AEqual.of_erase_eq bareIdentity_typed groundIdentity_typed rfl

/-- Two universes of the tower are the same head exactly when their levels
have the same canonical form. -/
theorem Tower.headSame_sort_iff (l l' : LevelExpr Nat) :
    HeadSame Tower.rules (.sort l) (.sort l') ↔ LevelNF.normalize l = LevelNF.normalize l' := by
  rw [LevelNF.normalize_eq_iff]
  constructor
  · rintro (same | equal)
    · cases same
      exact fun _ => rfl
    · exact equal
  · exact .inr

/-- Negative: the identity on the lowest universe, with that universe written,
is not typed at the arrow on the next universe. -/
theorem universeIdentity_rejected_at_raised_arrow :
    ¬ ATyped Tower.rules .nil universeIdentity
      (.pi (.head (.sort (.succ Tower.zero))) (.head (.sort (.succ Tower.zero)))) := by
  refine ATyped.lamTyped_head_mismatch (S := setting fun _ => 0) facts roots .nil
    .refl .refl ?_
  show ¬ HeadSame Tower.rules _ _
  rw [Tower.headSame_sort_iff, LevelNF.normalize_eq_iff]
  intro same
  exact absurd (same fun _ => 0) (by simp [LevelExpr.eval, LevelTower.zero])

private theorem ground_ne_universe {n : Nat} {Γ : Ctx Tower.Head n}
    (formed : CtxFormed Tower.rules Γ) :
    ¬ TypeEq Tower.rules Γ (.head .legacyGround) (.head (.sort Tower.zero)) := by
  intro equal
  rcases LevelTower.head_injective equal formed with same | same
  · cases same
  · exact same

/-- Negative: the written domain is a contract. The identity with the ground
type written is not typed at the arrow on the lowest universe, although its
erasure is. -/
theorem groundIdentity_rejected_at_universeArrow :
    ¬ ATyped Tower.rules .nil groundIdentity universeArrow ∧
      Typed Tower.rules .nil groundIdentity.erase universeArrow := by
  refine ⟨fun typing => ?_, universeIdentity_typed.erase⟩
  obtain ⟨_, agree, _⟩ :=
    ATyped.lamTyped_inv (S := setting fun _ => 0) facts typing .nil
  exact ground_ne_universe .nil agree

/-- Negative: equal erasures do not make written terms equal. The two written
identities erase to the same term and are each typed, but are equal at no
type. -/
theorem ground_universe_unequal :
    groundIdentity.erase = universeIdentity.erase ∧
      ATyped Tower.rules .nil groundIdentity groundArrow ∧
      ATyped Tower.rules .nil universeIdentity universeArrow ∧
      ∀ T, ¬ AEqual Tower.rules .nil groundIdentity universeIdentity T := by
  refine ⟨rfl, groundIdentity_typed, universeIdentity_typed, fun T equal => ?_⟩
  exact ground_ne_universe .nil
    (ATyped.writtenDomains_agree (S := setting fun _ => 0) facts .nil
      equal.1 equal.2.1)

end Tower

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
