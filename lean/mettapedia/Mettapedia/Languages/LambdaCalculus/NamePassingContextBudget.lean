import Mettapedia.Languages.LambdaCalculus.NamePassingContexts

/-!
# Structural budgets of scoped clients

Budgets count authored constructor occurrences, including stored sibling
expressions. They are additive under one-hole composition and do not count
the inserted component. They price tests, not their eventual executions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.LambdaCalculus.NamePassing

open Mettapedia.OSLF.Binding

variable {Srt : Type} {nm : Srt}

def nodeCount : {Γ : List Srt} → Expr nm Γ → Nat
  | _, .var _ => 1
  | _, .lam body => nodeCount body + 1
  | _, .app function _ => nodeCount function + 1
  | _, .defn value body => nodeCount value + nodeCount body + 1
  | _, .carrier _ value body => nodeCount value + nodeCount body + 1

theorem nodeCount_rename {Γ Δ : List Srt}
    (names : (s : Srt) → Var Γ s → Var Δ s) (source : Expr nm Γ) :
    nodeCount (rename names source) = nodeCount source := by
  induction source generalizing Δ <;> simp only [rename, nodeCount, *]

namespace Context

def budget {Γ : List Srt} : {Δ : List Srt} → Context nm Γ Δ → Nat
  | _, .hole => 0
  | _, .reindex _ inner => budget inner + 1
  | _, .lam inner => budget inner + 1
  | _, .app inner _ => budget inner + 1
  | _, .defValue inner body => budget inner + nodeCount body + 1
  | _, .defBody value inner => nodeCount value + budget inner + 1
  | _, .carrierValue _ inner body => budget inner + nodeCount body + 1
  | _, .carrierBody _ value inner => nodeCount value + budget inner + 1

theorem budget_compose {Γ Δ Θ : List Srt} (outer : Context nm Δ Θ) (inner : Context nm Γ Δ) :
    (outer.compose inner).budget = outer.budget + inner.budget := by
  induction outer <;> simp only [compose, budget, *] <;> omega

end Context

end Mettapedia.Languages.LambdaCalculus.NamePassing
