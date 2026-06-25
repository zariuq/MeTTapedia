import Mettapedia.Logic.HOL.Semantics.Extensionality

/-!
# Closed HOL Formula Satisfaction

Pure semantic vocabulary for closed Church-style HOL formulas at Henkin models.
PLN world-model bridges can count this relation, but the relation itself belongs
to the HOL semantic layer.
-/

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Public HOL query alias: closed Church-style HOL formulas. -/
abbrev HOLQuery (Const : Ty Base → Type v) := ClosedFormula Const

/-- Closed-formula satisfaction at a pointed Henkin model. -/
def holSatisfies
    (M : HenkinModel.{u, v, w} Base Const) (φ : HOLQuery Const) : Prop :=
  HenkinModel.models M φ

end Mettapedia.Logic.HOL
