namespace Curriculum.BindersDeBruijn

inductive Tm where
  | var : Nat -> Tm
  | lam : Tm -> Tm
  | app : Tm -> Tm -> Tm
  deriving DecidableEq, Repr

open Tm

def shiftAbove (cut inc : Nat) : Tm -> Tm
  | var k => if k < cut then var k else var (k + inc)
  | lam b => lam (shiftAbove (cut + 1) inc b)
  | app f a => app (shiftAbove cut inc f) (shiftAbove cut inc a)

def shift (inc : Nat) : Tm -> Tm :=
  shiftAbove 0 inc

def subst (j : Nat) (s : Tm) : Tm -> Tm
  | var k => if k = j then s else var k
  | lam b => lam (subst (j + 1) (shift 1 s) b)
  | app f a => app (subst j s f) (subst j s a)

theorem shift_keeps_bound_var_under_lam :
    shift 1 (lam (var 0)) = lam (var 0) := by
  rfl

theorem shift_moves_free_var_under_lam :
    shift 1 (lam (var 1)) = lam (var 2) := by
  rfl

theorem subst_hits_target :
    subst 0 (var 42) (var 0) = var 42 := by
  rfl

theorem subst_skips_bound_var_under_lam :
    subst 0 (var 42) (lam (var 0)) = lam (var 0) := by
  rfl

theorem subst_traverses_application :
    subst 0 (var 7) (app (var 0) (lam (var 1))) =
      app (var 7) (lam (var 8)) := by
  rfl

end Curriculum.BindersDeBruijn
