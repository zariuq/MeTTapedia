import Mettapedia.UniversalAlgebra.EquationSystemInterpretation

/-!
# The interpretability preorder of equation systems

Equation systems over varying signatures can be compared by explicit
algebraic interpretations.  The induced relation is a preorder: identity
interpretations witness reflexivity and composition witnesses transitivity.

This order is specific to finitary equational theories.  It is not silently
identified with proof-theoretic interpretability for arithmetic or with the
more permissive semantic-simulation order on NIK theory objects.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.EquationSystem

universe u

/-- An equation system bundled with its (possibly different) finitary
signature. -/
structure Object : Type (u + 1) where
  signature : Signature.{u}
  system : EquationSystem signature

/-- `host` interprets `guest` when there is an explicit algebraic
interpretation from the guest equation system into the host equation system. -/
def Interprets (host guest : Object.{u}) : Prop :=
  Nonempty (Interpretation guest.system host.system)

theorem interprets_refl (object : Object.{u}) : Interprets object object :=
  ⟨Interpretation.id object.system⟩

theorem interprets_trans {first second third : Object.{u}}
    (secondInterpretsFirst : Interprets second first)
    (thirdInterpretsSecond : Interprets third second) :
    Interprets third first := by
  rcases secondInterpretsFirst with ⟨firstSecond⟩
  rcases thirdInterpretsSecond with ⟨secondThird⟩
  exact ⟨firstSecond.comp secondThird⟩

/-- A type synonym carrying the algebraic-interpretability preorder. -/
def InterpretabilityOrder := Object.{u}

namespace InterpretabilityOrder

variable {S T : Signature.{u}}

instance : Preorder (InterpretabilityOrder.{u}) where
  le guest host := Interprets host guest
  le_refl := interprets_refl
  le_trans _first _second _third := interprets_trans

/-- Construct an object of the interpretability order without hiding its
signature or equation system. -/
def of (system : EquationSystem S) : InterpretabilityOrder :=
  ⟨S, system⟩

theorem le_iff {source : EquationSystem S} {target : EquationSystem T} :
    of source ≤ of target ↔ source.IsInterpretableIn target :=
  Iff.rfl

end InterpretabilityOrder

end Mettapedia.UniversalAlgebra.EquationSystem
