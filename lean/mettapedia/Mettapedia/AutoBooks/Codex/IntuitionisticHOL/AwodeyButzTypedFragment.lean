import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzOperations

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v w z

/--
The simple typed fragment currently supported by the live topological route:
propositions and base sorts, but not yet arrow types.
-/
inductive SimpleTy (Base : Type u) where
  | prop : SimpleTy Base
  | base : Base → SimpleTy Base
  deriving DecidableEq, Repr

namespace SimpleTy

variable {Base : Type u}

/-- Embed the supported fragment into the full HOL simple type syntax. -/
def toTy : SimpleTy Base → Ty Base
  | .prop => .prop
  | .base b => .base b

end SimpleTy

/--
First live typed topological interpretation for the Awodey-Butz route.

This records only the semantic objects and constants that can already be
interpreted with the current archive-free etale-space foundation.
-/
structure SimpleTopologicalInterpretation
    (Base : Type u) (Const : Ty Base → Type v)
    (X : Type w) [TopologicalSpace X] where
  propSpace : EtaleSpace.{w, z} X
  baseSpace : Base → EtaleSpace.{w, z} X
  constProp : Const (.prop) → propSpace.GlobalSection
  constBase : {b : Base} → Const (.base b) → (baseSpace b).GlobalSection

namespace SimpleTopologicalInterpretation

variable {Base : Type u} {Const : Ty Base → Type v}
variable {X : Type w} [TopologicalSpace X]

/-- Interpret a supported simple type as an etale space over the base. -/
def space (I : SimpleTopologicalInterpretation Base Const X) :
    SimpleTy Base → EtaleSpace.{w, z} X
  | .prop => I.propSpace
  | .base b => I.baseSpace b

/-- Interpret a constant of a supported simple type as a global section. -/
def constSection (I : SimpleTopologicalInterpretation Base Const X) :
    (τ : SimpleTy Base) → Const τ.toTy → (I.space τ).GlobalSection
  | .prop, c => I.constProp c
  | .base _, c => I.constBase c

/--
Interpret a simple-type context by iterated fiber products over the base space.

The empty context is the terminal etale space over the base.
-/
def ctxSpace (I : SimpleTopologicalInterpretation Base Const X) : List (SimpleTy Base) → EtaleSpace X
  | [] => EtaleSpace.terminal X
  | τ :: Γ => EtaleSpace.prod (I.space τ) (I.ctxSpace Γ)

@[simp] theorem ctxSpace_nil (I : SimpleTopologicalInterpretation Base Const X) :
    I.ctxSpace [] = EtaleSpace.terminal X :=
  rfl

@[simp] theorem ctxSpace_cons (I : SimpleTopologicalInterpretation Base Const X)
    (τ : SimpleTy Base) (Γ : List (SimpleTy Base)) :
    I.ctxSpace (τ :: Γ) = EtaleSpace.prod (I.space τ) (I.ctxSpace Γ) :=
  rfl

end SimpleTopologicalInterpretation

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
