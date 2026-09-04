import Mettapedia.UniversalAlgebra.Model

/-!
# Equation systems and model-theoretic consequence

An `EquationSystem` is occurrence-bearing input data: a finite list of
equations over a fixed signature.  It is not identified with its deductive
closure, a chosen rewrite orientation, or a categorical algebraic theory.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

universe u v

variable {S : Signature.{u}}

/-- An equation between two terms over one signature. -/
abbrev Equation (S : Signature.{u}) := Term S × Term S

/-- A finite occurrence-bearing system of equations. -/
@[ext] structure EquationSystem (S : Signature.{u}) : Type u where
  equations : List (Equation S)

instance : Membership (Equation S) (EquationSystem S) :=
  ⟨fun system equation => equation ∈ system.equations⟩

/-- An equation holds in a model when every valuation gives equal results. -/
def Equation.Holds {Carrier : Type v} (model : Model S Carrier)
    (equation : Equation S) : Prop :=
  ∀ valuation : Nat → Carrier,
    equation.1.evaluate model valuation = equation.2.evaluate model valuation

/-- A model satisfies every equation occurrence in the system. -/
def Model.Satisfies {Carrier : Type v} (model : Model S Carrier)
    (system : EquationSystem S) : Prop :=
  ∀ equation ∈ system, equation.Holds model

/-- Semantic consequence over models in a selected carrier universe. -/
def EntailsAt (system : EquationSystem S)
    (equation : Equation S) : Prop :=
  ∀ (Carrier : Type v) (model : Model S Carrier),
    model.Satisfies system → equation.Holds model

/-- The legacy same-universe specialization of `EntailsAt`. -/
def Entails (system : EquationSystem S) (equation : Equation S) : Prop :=
  EntailsAt.{u, u} system equation

end Mettapedia.UniversalAlgebra
