import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
import Mettapedia.TypeTheory.UniverseLevel.Syntax

/-! # Syntax of the cumulative tower -/

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace LevelTower

open Mettapedia.TypeTheory.UniverseLevel

/-- The heads of the tower: an opaque legacy ground head plus explicit predicative
universe levels. -/
inductive Head (L : Type) where
  | legacyGround
  | sort : LevelExpr L → Head L
  deriving DecidableEq, Repr

abbrev Tm (L : Type) (n : Nat) := Presentation.Tm (Head L) n
abbrev Ctx (L : Type) (n : Nat) := Presentation.Ctx (Head L) n

end LevelTower

namespace Tower

abbrev Head := LevelTower.Head Nat
abbrev Tm (n : Nat) := LevelTower.Tm Nat n
abbrev Ctx (n : Nat) := LevelTower.Ctx Nat n

end Tower

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
