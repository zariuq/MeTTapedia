import Mettapedia.Languages.MeTTa.PureKernel.Renaming

namespace Mettapedia.Languages.MeTTa.PureKernel.Context

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Renaming

/-- Telescope-style contexts, indexed by number of bound variables. -/
inductive Ctx : Nat → Type where
  | nil : Ctx 0
  | snoc : Ctx n → PureTm n → Ctx (n + 1)
deriving Repr

def lookup : Ctx n → Fin n → PureTm n
  | .nil, i => nomatch i
  | .snoc Γ A, i =>
      Fin.cases (rename wk A) (fun j => rename wk (lookup Γ j)) i

@[simp] theorem lookup_snoc_zero (Γ : Ctx n) (A : PureTm n) :
    lookup (.snoc Γ A) 0 = rename wk A := rfl

@[simp] theorem lookup_snoc_succ (Γ : Ctx n) (A : PureTm n) (i : Fin n) :
    lookup (.snoc Γ A) i.succ = rename wk (lookup Γ i) := rfl

/-- Context morphism induced by a renaming, stated as lookup compatibility. -/
def CtxRen (Γ : Ctx n) (Δ : Ctx m) (ρ : Ren n m) : Prop :=
  ∀ i : Fin n, lookup Δ (ρ i) = rename ρ (lookup Γ i)

/-- Lift a context renaming morphism through one binder extension. -/
theorem CtxRen.snoc {Γ : Ctx n} {Δ : Ctx m} {ρ : Ren n m}
    (hρ : CtxRen Γ Δ ρ) (A : PureTm n) :
    CtxRen (.snoc Γ A) (.snoc Δ (rename ρ A)) (liftRen ρ) := by
  intro i
  refine Fin.cases ?_ ?_ i
  ·
    calc
      lookup (.snoc Δ (rename ρ A)) (liftRen ρ 0)
          = rename wk (rename ρ A) := by
              simp [lookup_snoc_zero, liftRen]
      _ = rename (fun x => wk (ρ x)) A := by
            simp [rename_comp]
      _ = rename (fun x => liftRen ρ (wk x)) A := by
            apply rename_ext
            intro x
            simp [wk, liftRen]
      _ = rename (liftRen ρ) (rename wk A) := by
            simp [rename_comp]
      _ = rename (liftRen ρ) (lookup (.snoc Γ A) 0) := by
            simp [lookup_snoc_zero]
  · intro j
    calc
      lookup (.snoc Δ (rename ρ A)) (liftRen ρ j.succ)
          = rename wk (lookup Δ (ρ j)) := by
              simp [lookup_snoc_succ, liftRen]
      _ = rename wk (rename ρ (lookup Γ j)) := by
            simp [hρ j]
      _ = rename (fun x => wk (ρ x)) (lookup Γ j) := by
            simp [rename_comp]
      _ = rename (fun x => liftRen ρ (wk x)) (lookup Γ j) := by
            apply rename_ext
            intro x
            simp [wk, liftRen]
      _ = rename (liftRen ρ) (rename wk (lookup Γ j)) := by
            simp [rename_comp]
      _ = rename (liftRen ρ) (lookup (.snoc Γ A) j.succ) := by
            simp [lookup_snoc_succ]

end Mettapedia.Languages.MeTTa.PureKernel.Context
