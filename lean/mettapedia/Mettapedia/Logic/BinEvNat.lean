import Mathlib.Algebra.Group.Defs

/-!
# BinEvNat — Nat-valued Binary Evidence Counts

Kernel-checkable binary evidence pairs. The pseudo-count IS the evidence
(Morita et al. 2008): ESS = pos + neg.

Forms an `AddCommMonoid` under componentwise addition — independent
observations combine commutatively and associatively.
-/

namespace Mettapedia.Logic

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

end Mettapedia.Logic
