namespace Curriculum.BindersDeBruijnNegative

inductive Tm where
  | var : Nat -> Tm
  | lam : Tm -> Tm
  deriving DecidableEq, Repr

open Tm

def shiftAbove (cut inc : Nat) : Tm -> Tm
  | var k => if k < cut then var k else var (k + inc)
  | lam b => lam (shiftAbove (cut + 1) inc b)

def shift (inc : Nat) : Tm -> Tm :=
  shiftAbove 0 inc

theorem bad_capture_claim :
    shift 1 (lam (var 1)) = lam (var 1) := by
  rfl

end Curriculum.BindersDeBruijnNegative
