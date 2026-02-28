import Mettapedia.Languages.ProcessCalculi.MQCalculus.Shift

/-!
# MQ-Calculus: Structural Congruence

Structural congruence `≡ₘ` for MQ-calculus, following Stay & Meredith (2026), Section 2.

## Axioms

```
P | Q  ≡  Q | P
(P | Q) | R  ≡  P | (Q | R)
ν 0  ≡  0
ν (shift(0,P) | Q)  ≡  P | ν Q
```
-/

namespace Mettapedia.Languages.ProcessCalculi.MQCalculus

open Process

/-- Structural congruence for MQ-calculus processes. -/
inductive SC : Process → Process → Prop where
  | refl  (p : Process) : SC p p
  | symm  (p q : Process) : SC p q → SC q p
  | trans (p q r : Process) : SC p q → SC q r → SC p r
  | par_comm  (p q : Process) : SC (p ‖ q) (q ‖ p)
  | par_assoc (p q r : Process) : SC ((p ‖ q) ‖ r) (p ‖ (q ‖ r))
  | nu_nil : SC (.MQNu .MQNil) .MQNil
  | scope_extrusion (p q : Process) :
      SC (.MQNu (shift 0 p ‖ q)) (p ‖ .MQNu q)
  | par_cong_l (p p' q : Process) : SC p p' → SC (p ‖ q) (p' ‖ q)
  | par_cong_r (p q q' : Process) : SC q q' → SC (p ‖ q) (p ‖ q')
  | nu_cong   (p p' : Process)    : SC p p' → SC (.MQNu p) (.MQNu p')
  | gate_cong (g : GateSpec) (p p' : Process) :
      SC p p' → SC (.MQGate g p) (.MQGate g p')
  | in_cong_zero (i : ℕ) (p p' q : Process) :
      SC p p' → SC (.MQIn i p q) (.MQIn i p' q)
  | in_cong_one (i : ℕ) (p q q' : Process) :
      SC q q' → SC (.MQIn i p q) (.MQIn i p q')

notation:50 p " ≡ₘ " q => SC p q

theorem SC_equivalence : Equivalence SC where
  refl  := SC.refl
  symm  := SC.symm _ _
  trans := SC.trans _ _ _

theorem par_cong (p p' q q' : Process) (hp : p ≡ₘ p') (hq : q ≡ₘ q') :
    p ‖ q ≡ₘ p' ‖ q' :=
  SC.trans _ _ _ (SC.par_cong_l p p' q hp) (SC.par_cong_r p' q q' hq)

theorem scope_extrusion_symm (p q : Process) :
    p ‖ .MQNu q ≡ₘ .MQNu (shift 0 p ‖ q) :=
  SC.symm _ _ (SC.scope_extrusion p q)

/-! ## Structural inversion lemmas -/

/-- SC preserves the "is MQOut i" predicate in both directions. -/
theorem SC_MQOut_iff (i : ℕ) {p q : Process} (h : SC p q) : p = MQOut i ↔ q = MQOut i := by
  induction h with
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  | par_comm _ _ => constructor <;> intro h <;> cases h
  | par_assoc _ _ _ => constructor <;> intro h <;> cases h
  | nu_nil => constructor <;> intro h <;> cases h
  | scope_extrusion _ _ => constructor <;> intro h <;> cases h
  | par_cong_l _ _ _ _ _ => constructor <;> intro h <;> cases h
  | par_cong_r _ _ _ _ _ => constructor <;> intro h <;> cases h
  | nu_cong _ _ _ _ => constructor <;> intro h <;> cases h
  | gate_cong _ _ _ _ _ => constructor <;> intro h <;> cases h
  | in_cong_zero _ _ _ _ _ _ => constructor <;> intro h <;> cases h
  | in_cong_one _ _ _ _ _ _ => constructor <;> intro h <;> cases h

/-- If `MQOut i ≡ₘ p` then `p = MQOut i`. -/
theorem SC_MQOut_inv (i : ℕ) {p : Process} (h : SC (MQOut i) p) : p = MQOut i :=
  (SC_MQOut_iff i h).mp rfl

end Mettapedia.Languages.ProcessCalculi.MQCalculus
