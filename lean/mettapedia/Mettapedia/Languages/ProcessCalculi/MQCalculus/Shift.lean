import Mettapedia.Languages.ProcessCalculi.MQCalculus.Syntax

/-!
# MQ-Calculus: Shift Function

Defines the wire-index shifting function and proves all equational laws.

## Definition (paper Section 2)

```
shift(c, MQNil)         = MQNil
shift(c, P | Q)         = shift(c,P) | shift(c,Q)
shift(c, ν P)           = ν shift(c+1, P)
shift(c, gate s; P)     = gate s; shift(c, P)   -- gate labels are absolute
shift(c, out i)         = if i < c then out i else out (i+1)
shift(c, in i {P,Q})    = if i < c then in i {shift(c,P), shift(c,Q)}
                           else       in (i+1) {shift(c,P), shift(c,Q)}
```

## References

- Stay & Meredith (2026), Section 2
-/

namespace Mettapedia.Languages.ProcessCalculi.MQCalculus

open Process

/-- `shift c P` increments every wire index ≥ c by 1 in P. -/
def shift (c : ℕ) : Process → Process
  | MQNil       => MQNil
  | MQPar p q   => MQPar (shift c p) (shift c q)
  | MQNu p      => MQNu (shift (c + 1) p)
  | MQGate s p  => MQGate s (shift c p)
  | MQOut i     => if i < c then MQOut i else MQOut (i + 1)
  | MQIn i p q  => if i < c
                   then MQIn i (shift c p) (shift c q)
                   else MQIn (i + 1) (shift c p) (shift c q)

/-! ## Equational laws (all sorry-free) -/

@[simp] theorem shift_MQNil (c : ℕ) : shift c MQNil = MQNil := rfl

@[simp] theorem shift_MQPar (c : ℕ) (p q : Process) :
    shift c (p ‖ q) = shift c p ‖ shift c q := rfl

@[simp] theorem shift_MQNu (c : ℕ) (p : Process) :
    shift c (MQNu p) = MQNu (shift (c + 1) p) := rfl

@[simp] theorem shift_MQGate (c : ℕ) (s : String) (p : Process) :
    shift c (MQGate s p) = MQGate s (shift c p) := rfl

@[simp] theorem shift_MQOut_lt (c i : ℕ) (h : i < c) :
    shift c (MQOut i) = MQOut i := by simp [shift, h]

@[simp] theorem shift_MQOut_ge (c i : ℕ) (h : ¬ i < c) :
    shift c (MQOut i) = MQOut (i + 1) := by simp [shift, h]

@[simp] theorem shift_MQIn_lt (c i : ℕ) (h : i < c) (p q : Process) :
    shift c (MQIn i p q) = MQIn i (shift c p) (shift c q) := by simp [shift, h]

@[simp] theorem shift_MQIn_ge (c i : ℕ) (h : ¬ i < c) (p q : Process) :
    shift c (MQIn i p q) = MQIn (i + 1) (shift c p) (shift c q) := by simp [shift, h]

theorem shift_zero_MQOut (i : ℕ) : shift 0 (MQOut i) = MQOut (i + 1) := by simp [shift]
theorem shift_zero_MQIn (i : ℕ) (p q : Process) :
    shift 0 (MQIn i p q) = MQIn (i + 1) (shift 0 p) (shift 0 q) := by simp [shift]

/-- `shift c (shift d P) = shift (d+1) (shift c P)` when `c ≤ d`. -/
theorem shift_comm (p : Process) (c d : ℕ) (hcd : c ≤ d) :
    shift c (shift d p) = shift (d + 1) (shift c p) := by
  induction p generalizing c d with
  | MQNil => rfl
  | MQPar p q ihp ihq => simp [ihp c d hcd, ihq c d hcd]
  | MQNu p ih => simp; exact ih (c + 1) (d + 1) (Nat.succ_le_succ hcd)
  | MQGate s p ih => simp [ih c d hcd]
  | MQOut i =>
    by_cases h1 : i < d <;> by_cases h3 : i < c
    · -- i < c ≤ d: both shifts are no-ops on i
      simp [shift, h1, h3, Nat.lt_succ_of_lt h1]
    · -- c ≤ i < d: outer shift increments i, inner doesn't; d+1 sees i+1 < d+1
      have hci : c ≤ i := Nat.le_of_not_lt h3
      simp only [shift, if_pos h1, if_neg h3,
                 if_pos (show i + 1 < d + 1 from by omega)]
    · exact absurd (Nat.lt_of_lt_of_le h3 hcd) h1
    · -- d ≤ i: both shifts increment
      have hdi : d ≤ i := Nat.le_of_not_lt h1
      have hci : c ≤ i := Nat.le_of_not_lt h3
      simp only [shift, if_neg h1, if_neg h3,
                 if_neg (show ¬ (i + 1 < c) from by omega),
                 if_neg (show ¬ (i + 1 < d + 1) from by omega)]
  | MQIn i p q ihp ihq =>
    by_cases h1 : i < d <;> by_cases h3 : i < c
    · simp [shift, h1, h3, ihp c d hcd, ihq c d hcd, Nat.lt_succ_of_lt h1]
    · have hci : c ≤ i := Nat.le_of_not_lt h3
      simp only [shift, if_pos h1, if_neg h3,
                 if_pos (show i + 1 < d + 1 from by omega),
                 ihp c d hcd, ihq c d hcd]
    · exact absurd (Nat.lt_of_lt_of_le h3 hcd) h1
    · have hdi : d ≤ i := Nat.le_of_not_lt h1
      have hci : c ≤ i := Nat.le_of_not_lt h3
      simp only [shift, if_neg h1, if_neg h3,
                 if_neg (show ¬ (i + 1 < c) from by omega),
                 if_neg (show ¬ (i + 1 < d + 1) from by omega),
                 ihp c d hcd, ihq c d hcd]

end Mettapedia.Languages.ProcessCalculi.MQCalculus
