import Mettapedia.Logic.HOL
import Mettapedia.Logic.PLNWorldModelHOL

namespace Mettapedia.Logic.PLNHigherOrderHOLCore

universe u v

open Mettapedia.Logic.HOL

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Higher-order PLN queries are closed Church-style HOL formulas. -/
abbrev HOLQuery (Const : Ty Base → Type v) :=
  _root_.Mettapedia.Logic.PLNWorldModelHOL.HOLQuery (Base := Base) Const

/-- Higher-order PLN states are multisets of pointed Henkin models. -/
abbrev HOLState (Base : Type u) (Const : Ty Base → Type v) :=
  _root_.Mettapedia.Logic.PLNWorldModelHOL.HOLState Base Const

/-- A HOL formula is provable when it is derivable from no assumptions. -/
abbrev HOLProvable (φ : HOLQuery Const) : Prop :=
  _root_.Mettapedia.Logic.HOL.Derivation.Theorem Const φ

/-- Provable HOL implication is the proof-theoretic core of the HO PLN layer. -/
def HOLProvImp (φ ψ : HOLQuery Const) : Prop :=
  HOLProvable (Const := Const) (.imp φ ψ)

/-- Provable HOL equality at closed type-correct terms. -/
def HOLProvEq {τ : Ty Base} (t u : Term Const [] τ) : Prop :=
  HOLProvable (Const := Const) (.eq t u)

abbrev holProvImp_refl :=
  @_root_.Mettapedia.Logic.HOL.Derivation.theorem_imp_refl

abbrev holProvImp_top :=
  @_root_.Mettapedia.Logic.HOL.Derivation.theorem_imp_top

abbrev holProvImp_trans :=
  @_root_.Mettapedia.Logic.HOL.Derivation.theorem_imp_trans

end Mettapedia.Logic.PLNHigherOrderHOLCore
