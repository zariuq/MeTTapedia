/-!
# Shared Process Algebra Vocabulary

Minimal typeclasses for the common algebraic structure shared by
π-calculus, ρ-calculus, and MQ-calculus:

- `HasPar` — parallel composition
- `HasNu` — restriction / new-name
- `HasNil` — inactive process
-/

universe u

namespace ProcessCalculi

/-- Typeclass for process types with parallel composition. -/
class HasPar (α : Type u) where
  /-- Parallel composition of two processes -/
  par : α → α → α

/-- Typeclass for process types with restriction (new-name binding). -/
class HasNu (α : Type u) where
  /-- Restriction operator -/
  nu : α → α

/-- Typeclass for process types with an inactive (nil) process. -/
class HasNil (α : Type u) where
  /-- The inactive process -/
  nil : α

end ProcessCalculi
