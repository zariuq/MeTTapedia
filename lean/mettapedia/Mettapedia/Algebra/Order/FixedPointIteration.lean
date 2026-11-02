import Mathlib.Order.FixedPoints
import Mathlib.Order.OrderIsoNat

/-!
# Bottom and top iteration of monotone maps

The iterations are independent of a symbolic representation. A stable bottom
iterate is the least fixed point; a stable top iterate is the greatest. The
appropriate chain condition gives eventual stabilization. No fairness or bound
on the work of one iteration is inferred from these order laws.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Order.FixedPointIteration

variable {L : Type} [CompleteLattice L]

def iterateFrom (operator : L →o L) (initial : L) : Nat → L
  | 0 => initial
  | n + 1 => operator (iterateFrom operator initial n)

theorem iterateFrom_mono (operator : L →o L) (initial : L) (ascending : initial ≤ operator initial) :
    Monotone (iterateFrom operator initial) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => exact ascending
  | succ n ih => exact operator.monotone ih

theorem bottom_le_lfp (operator : L →o L) (n : Nat) : iterateFrom operator ⊥ n ≤ operator.lfp := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    change operator (iterateFrom operator ⊥ n) ≤ operator.lfp
    rw [← operator.map_lfp]
    exact operator.monotone ih

theorem stable_bottom_is_lfp (operator : L →o L) (n : Nat)
    (stable : iterateFrom operator ⊥ (n + 1) = iterateFrom operator ⊥ n) :
    iterateFrom operator ⊥ n = operator.lfp := by
  apply le_antisymm (bottom_le_lfp operator n)
  exact operator.lfp_le_fixed stable

theorem bottom_eventually_lfp [WellFoundedGT L] (operator : L →o L) :
    ∃ n, ∀ k, n ≤ k → iterateFrom operator ⊥ k = operator.lfp := by
  obtain ⟨n, stable⟩ := WellFoundedGT.monotone_chain_condition
    (⟨iterateFrom operator ⊥, iterateFrom_mono operator ⊥ bot_le⟩ : Nat →o L)
  have fixed : iterateFrom operator ⊥ n = operator.lfp :=
    stable_bottom_is_lfp operator n (stable (n + 1) (Nat.le_succ n)).symm
  exact ⟨n, fun k hk => (stable k hk).symm.trans fixed⟩

theorem gfp_le_top (operator : L →o L) (n : Nat) : operator.gfp ≤ iterateFrom operator ⊤ n := by
  induction n with
  | zero => exact le_top
  | succ n ih =>
    change operator.gfp ≤ operator (iterateFrom operator ⊤ n)
    rw [← operator.map_gfp]
    exact operator.monotone ih

theorem stable_top_is_gfp (operator : L →o L) (n : Nat)
    (stable : iterateFrom operator ⊤ (n + 1) = iterateFrom operator ⊤ n) :
    iterateFrom operator ⊤ n = operator.gfp := by
  exact le_antisymm (operator.le_gfp stable.ge) (gfp_le_top operator n)

theorem top_antitone (operator : L →o L) : Antitone (iterateFrom operator ⊤) := by
  apply antitone_nat_of_succ_le
  intro n
  induction n with
  | zero => exact le_top
  | succ n ih => exact operator.monotone ih

theorem top_eventually_gfp [WellFoundedLT L] (operator : L →o L) :
    ∃ n, ∀ k, n ≤ k → iterateFrom operator ⊤ k = operator.gfp := by
  obtain ⟨n, stable⟩ := WellFoundedGT.monotone_chain_condition
    (⟨fun k => iterateFrom (L := L) operator (⊤ : L) k, top_antitone operator⟩ : Nat →o OrderDual L)
  have fixed : iterateFrom operator ⊤ n = operator.gfp :=
    stable_top_is_gfp operator n (stable (n + 1) (Nat.le_succ n)).symm
  exact ⟨n, fun k hk => (stable k hk).symm.trans fixed⟩

end Mettapedia.Algebra.Order.FixedPointIteration
