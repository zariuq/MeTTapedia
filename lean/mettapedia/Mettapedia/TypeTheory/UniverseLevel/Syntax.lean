/-! # Syntax of explicit universe levels -/

namespace Mettapedia.TypeTheory.UniverseLevel

/-- Level expressions over the levels `L`: the kernel's admitted level language.
`param i` is a level *variable* — needed for universe polymorphism
(schema-level rules quantify over levels); `const c` a closed level. -/
inductive LevelExpr (L : Type) where
  | const : L → LevelExpr L
  | param : Nat → LevelExpr L
  | succ : LevelExpr L → LevelExpr L
  | max : LevelExpr L → LevelExpr L → LevelExpr L
  deriving DecidableEq, Repr

end Mettapedia.TypeTheory.UniverseLevel
