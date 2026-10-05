import Mathlib.Algebra.Ring.Defs

/-!
# BinEvNat — Nat-valued Binary Evidence Counts

Kernel-checkable binary evidence pairs. The pseudo-count IS the evidence
(Morita et al. 2008): ESS = pos + neg.

Componentwise addition and tensor multiplication form a `CommSemiring`.
The laws do not authorize revising dependent observations; provenance and
independence remain separate admission conditions.
-/

namespace Mettapedia.PLN.Evidence

structure BinEvNat where
  pos : Nat
  neg : Nat
  deriving DecidableEq, BEq, Repr

instance : Add BinEvNat := ⟨fun a b => ⟨a.pos + b.pos, a.neg + b.neg⟩⟩
instance : Zero BinEvNat := ⟨⟨0, 0⟩⟩

@[ext] theorem BinEvNat.ext {a b : BinEvNat} (hp : a.pos = b.pos) (hn : a.neg = b.neg) :
    a = b := by cases a; cases b; simp_all

instance : AddCommMonoid BinEvNat where
  add_assoc a b c := BinEvNat.ext (Nat.add_assoc ..) (Nat.add_assoc ..)
  zero_add a := BinEvNat.ext (Nat.zero_add ..) (Nat.zero_add ..)
  add_zero a := BinEvNat.ext (Nat.add_zero ..) (Nat.add_zero ..)
  add_comm a b := BinEvNat.ext (Nat.add_comm ..) (Nat.add_comm ..)
  nsmul := nsmulRec

def BinEvNat.ess (e : BinEvNat) : Nat := e.pos + e.neg

def BinEvNat.strength (e : BinEvNat) : Nat × Nat := (e.pos, e.pos + e.neg)

/-- Coordinatewise tensor composition. The multiplicative unit has one
count in each coordinate; this operation is distinct from revision addition. -/
def BinEvNat.tensor (left right : BinEvNat) : BinEvNat :=
  ⟨left.pos * right.pos, left.neg * right.neg⟩

instance : Mul BinEvNat := ⟨BinEvNat.tensor⟩
instance : One BinEvNat := ⟨⟨1, 1⟩⟩

@[simp] theorem BinEvNat.mul_pos (left right : BinEvNat) :
    (left * right).pos = left.pos * right.pos := rfl

@[simp] theorem BinEvNat.mul_neg (left right : BinEvNat) :
    (left * right).neg = left.neg * right.neg := rfl

instance : CommMonoid BinEvNat where
  mul_assoc left middle right := BinEvNat.ext (Nat.mul_assoc ..) (Nat.mul_assoc ..)
  one_mul value := BinEvNat.ext (Nat.one_mul ..) (Nat.one_mul ..)
  mul_one value := BinEvNat.ext (Nat.mul_one ..) (Nat.mul_one ..)
  mul_comm left right := BinEvNat.ext (Nat.mul_comm ..) (Nat.mul_comm ..)

instance : CommSemiring BinEvNat where
  __ := (inferInstance : AddCommMonoid BinEvNat)
  __ := (inferInstance : CommMonoid BinEvNat)
  left_distrib left middle right :=
    BinEvNat.ext (Nat.mul_add ..) (Nat.mul_add ..)
  right_distrib left middle right :=
    BinEvNat.ext (Nat.add_mul ..) (Nat.add_mul ..)
  zero_mul value := BinEvNat.ext (Nat.zero_mul ..) (Nat.zero_mul ..)
  mul_zero value := BinEvNat.ext (Nat.mul_zero ..) (Nat.mul_zero ..)

theorem exact_evidence_zero_divisors :
    (⟨1, 0⟩ : BinEvNat) ≠ 0 ∧ (⟨0, 1⟩ : BinEvNat) ≠ 0 ∧
      (⟨1, 0⟩ : BinEvNat) * ⟨0, 1⟩ = 0 := by decide +kernel

theorem count_addition_not_idempotent :
    (⟨2, 3⟩ : BinEvNat) + ⟨2, 3⟩ = ⟨4, 6⟩ ∧
      (⟨2, 3⟩ : BinEvNat) + ⟨2, 3⟩ ≠ ⟨2, 3⟩ := by decide +kernel

theorem exact_evidence_tensor_control :
    (⟨2, 3⟩ : BinEvNat) * ⟨5, 7⟩ = ⟨10, 21⟩ := by decide +kernel

end Mettapedia.PLN.Evidence
