import Mathlib.Logic.Small.Defs

/-!
# Controls for reading universe levels

Theorems whose meaning depends on universe levels, for the reading of Lean in Egal.

`type_witness` holds of every type in `Type u`: some type in `Type u` equals it.  Its proof
uses that the type lies in the universe; of an arbitrary set the statement is false, so a
reading that takes a type binder for any set cannot state it.  The reading states it with the
level quantified and the type a member of the level's universe.

`small_self` (Mathlib) is the same fact up to equivalence; its level enters through the level
argument of the constant `Small`.
-/

set_option autoImplicit false

universe u

namespace Mettapedia.Languages.Lean.Declarations.UniverseControls

/-- A type of `Type u` equals some type of `Type u`: the witness is the type itself, which the
universe holds. -/
theorem type_witness (α : Type u) : ∃ β : Type u, β = α := ⟨α, rfl⟩

/-- The level as a value: `Small.{u} α` says some type of `Type u` is equivalent to `α`. -/
example (α : Type u) : Small.{u} α := small_self α

/-- The level is content: a type one universe up need not be small one universe down.  The
universe `Type u` lies in `Type (u + 1)` and is not `u`-small. -/
example : ¬ Small.{u} (Type u) := not_small_type

end Mettapedia.Languages.Lean.Declarations.UniverseControls
