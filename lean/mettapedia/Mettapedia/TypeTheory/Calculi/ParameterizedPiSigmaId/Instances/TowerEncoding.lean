import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TermEncoding

/-!
# Encoding the cumulative tower by numbers

Universe-level expressions and the heads of the cumulative tower are encoded
injectively by natural numbers, proved without choice. So the tower's heads,
and its terms, are countably many.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniverseLevel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TermEncoding

/-- The encoding of a level expression: a tag for the former, paired with the
encodings of its parts. -/
def LevelExpr.encode : LevelExpr Nat → Nat
  | .const c => pairing 0 c
  | .param i => pairing 1 i
  | .succ e => pairing 2 e.encode
  | .max a b => pairing 3 (pairing a.encode b.encode)

theorem LevelExpr.encode_injective : Function.Injective LevelExpr.encode := by
  intro x y h
  induction x generalizing y with
  | const c =>
      cases y with
      | const c' => rw [(pairing_injective h).2]
      | _ => exact absurd (pairing_injective h).1 (by decide)
  | param i =>
      cases y with
      | param i' => rw [(pairing_injective h).2]
      | _ => exact absurd (pairing_injective h).1 (by decide)
  | succ e ih =>
      cases y with
      | succ e' => rw [ih (pairing_injective h).2]
      | _ => exact absurd (pairing_injective h).1 (by decide)
  | max a b iha ihb =>
      cases y with
      | max a' b' =>
          obtain ⟨ea, eb⟩ := pairing_injective (pairing_injective h).2
          rw [iha ea, ihb eb]
      | _ => exact absurd (pairing_injective h).1 (by decide)

instance LevelExpr.instCountable : Countable (LevelExpr Nat) :=
  ⟨⟨LevelExpr.encode, LevelExpr.encode_injective⟩⟩

end Mettapedia.TypeTheory.UniverseLevel

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

open Mettapedia.TypeTheory.UniverseLevel
open TermEncoding

/-- The encoding of a head of the tower. -/
def Tower.Head.encode : Tower.Head → Nat
  | .legacyGround => 0
  | .sort level => pairing 0 level.encode

theorem Tower.Head.encode_injective : Function.Injective Tower.Head.encode := by
  intro x y h
  cases x with
  | legacyGround =>
      cases y with
      | legacyGround => rfl
      | sort => exact absurd h.symm (pairing_ne_zero _ _)
  | sort level =>
      cases y with
      | legacyGround => exact absurd h (pairing_ne_zero _ _)
      | sort level' => rw [LevelExpr.encode_injective (pairing_injective h).2]

/-- The heads of the tower are countably many, and so are its terms. -/
instance Tower.Head.instCountable : Countable Tower.Head :=
  ⟨⟨Tower.Head.encode, Tower.Head.encode_injective⟩⟩

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
