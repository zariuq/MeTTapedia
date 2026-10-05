import Mettapedia.Languages.LambdaCalculus.NamePassingEnvironmentEquations

/-!
# Scoped clients of the name-passing lambda fragment

One-hole contexts include every expression position, not only active evaluation
positions. Reindexing is explicit, so inserting an open component beneath a
binder uses a supplied capture-avoiding name map. Context composition retains
the intermediate scope. These are syntactic clients, independent of compilation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.LambdaCalculus.NamePassing

open Mettapedia.OSLF.Binding

variable {Srt : Type} {nm : Srt}

inductive Context (nm : Srt) (Γ : List Srt) : List Srt → Type where
  | hole : Context nm Γ Γ
  | reindex {Δ Θ} (names : (s : Srt) → Var Δ s → Var Θ s) :
      Context nm Γ Δ → Context nm Γ Θ
  | lam {Δ} : Context nm Γ (nm :: Δ) → Context nm Γ Δ
  | app {Δ} : Context nm Γ Δ → Var Δ nm → Context nm Γ Δ
  | defValue {Δ} : Context nm Γ Δ → Expr nm (nm :: Δ) → Context nm Γ Δ
  | defBody {Δ} : Expr nm Δ → Context nm Γ (nm :: Δ) → Context nm Γ Δ
  | carrierValue {Δ} : Var Δ nm → Context nm Γ Δ → Expr nm Δ → Context nm Γ Δ
  | carrierBody {Δ} : Var Δ nm → Expr nm Δ → Context nm Γ Δ → Context nm Γ Δ

namespace Context

def plug {Γ : List Srt} : {Δ : List Srt} → Context nm Γ Δ → Expr nm Γ → Expr nm Δ
  | _, .hole, term => term
  | _, .reindex names inner, term => rename names (plug inner term)
  | _, .lam inner, term => .lam (plug inner term)
  | _, .app inner argument, term => .app (plug inner term) argument
  | _, .defValue inner body, term => .defn (plug inner term) body
  | _, .defBody value inner, term => .defn value (plug inner term)
  | _, .carrierValue name inner body, term => .carrier name (plug inner term) body
  | _, .carrierBody name value inner, term => .carrier name value (plug inner term)

def compose {Γ Δ : List Srt} : {Θ : List Srt} →
    Context nm Δ Θ → Context nm Γ Δ → Context nm Γ Θ
  | _, .hole, inner => inner
  | _, .reindex names outer, inner => .reindex names (compose outer inner)
  | _, .lam outer, inner => .lam (compose outer inner)
  | _, .app outer argument, inner => .app (compose outer inner) argument
  | _, .defValue outer body, inner => .defValue (compose outer inner) body
  | _, .defBody value outer, inner => .defBody value (compose outer inner)
  | _, .carrierValue name outer body, inner => .carrierValue name (compose outer inner) body
  | _, .carrierBody name value outer, inner => .carrierBody name value (compose outer inner)

@[simp] theorem plug_compose {Γ Δ Θ : List Srt} (outer : Context nm Δ Θ)
    (inner : Context nm Γ Δ) (term : Expr nm Γ) :
    (outer.compose inner).plug term = outer.plug (inner.plug term) := by
  induction outer <;> simp only [compose, plug, *]

@[simp] theorem compose_hole {Γ Δ : List Srt} (context : Context nm Γ Δ) :
    context.compose .hole = context := by
  induction context <;> simp only [compose, *]

theorem compose_assoc {Γ Δ Θ Ξ : List Srt} (outer : Context nm Θ Ξ)
    (middle : Context nm Δ Θ) (inner : Context nm Γ Δ) :
    (outer.compose middle).compose inner = outer.compose (middle.compose inner) := by
  induction outer <;> simp only [compose, *]

theorem plug_structural {Γ Δ : List Srt} (context : Context nm Γ Δ)
    {left right : Expr nm Γ} (equal : Environment.StructuralEq left right) :
    Environment.StructuralEq (context.plug left) (context.plug right) := by
  induction context with
  | hole => exact equal
  | reindex names _ ih => exact ih.rename names
  | lam _ ih => exact .lam ih
  | app _ argument ih => exact .app argument ih
  | defValue _ body ih => exact .defn ih (.refl body)
  | defBody value _ ih => exact .defn (.refl value) ih
  | carrierValue name _ body ih => exact .carrier name ih (.refl body)
  | carrierBody name value _ ih => exact .carrier name (.refl value) ih

end Context

end Mettapedia.Languages.LambdaCalculus.NamePassing
