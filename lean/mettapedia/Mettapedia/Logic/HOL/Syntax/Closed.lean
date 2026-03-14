import Mettapedia.Logic.HOL.Syntax.Subst

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Closed typed HOL terms. -/
abbrev ClosedTerm (Const : Ty Base → Type v) (τ : Ty Base) := Term Const [] τ

/-- The empty valuation for closed syntax. -/
def emptyValuation : ∀ {τ}, Var ([] : Ctx Base) τ → α
  | _, v => nomatch v

end Mettapedia.Logic.HOL
