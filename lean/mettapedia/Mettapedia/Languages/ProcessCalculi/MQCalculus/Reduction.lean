import Mettapedia.Languages.ProcessCalculi.MQCalculus.CommRule
import Mettapedia.Languages.ProcessCalculi.Common.Common

/-!
# MQ-Calculus: Full Reduction Relation

`Reduces` (one step) and `MultiStep` (reflexive-transitive closure).
Following Stay & Meredith (2026), Section 3.

## Note on notation

`MQPar` is used directly in constructor types to avoid a conflict between
the `‖` parallel-composition notation and Mathlib's `‖·‖` norm notation
(both use U+2016 DOUBLE VERTICAL LINE as a token).
-/

namespace Mettapedia.Languages.ProcessCalculi.MQCalculus

open Process

inductive Reduces : Process → Process → Prop where
  | comm (i : ℕ) (p q : Process) (b : MeasurementBranch) :
      CommReduction i p q b →
      Reduces (MQPar (MQOut i) (MQIn i p q)) b.result
  | sc (p p' q' q : Process) :
      SC p p' → Reduces p' q' → SC q' q → Reduces p q
  | par_l  (p p' q : Process) : Reduces p p' → Reduces (MQPar p q) (MQPar p' q)
  | par_r  (p q q' : Process) : Reduces q q' → Reduces (MQPar p q) (MQPar p q')
  | nu_step  (p p' : Process) : Reduces p p' → Reduces (MQNu p) (MQNu p')
  | gate_step (g : GateSpec) (p p' : Process) :
      Reduces p p' → Reduces (MQGate g p) (MQGate g p')

theorem comm_zero (i : ℕ) (p q : Process) :
    Reduces (MQPar (MQOut i) (MQIn i p q)) p :=
  Reduces.comm i p q _ (.outcome_zero i p q)

theorem comm_one (i : ℕ) (p q : Process) :
    Reduces (MQPar (MQOut i) (MQIn i p q)) q :=
  Reduces.comm i p q _ (.outcome_one i p q)

/-! ## Irreducibility lemmas -/

/-- No constructor of `Reduces` has `MQOut i` as LHS (even via SC, since SC fixes MQOut). -/
theorem mq_out_reduces_false {p q : Process} (h : Reduces p q) : ∀ i, p = MQOut i → False := by
  induction h with
  | comm _ _ _ _ _ => intro i heq; cases heq
  | sc _ _ _ _ h1 _ _ ih =>
    intro i heq; subst heq; exact ih i (SC_MQOut_inv i h1)
  | par_l _ _ _ _ _ => intro i heq; cases heq
  | par_r _ _ _ _ _ => intro i heq; cases heq
  | nu_step _ _ _ _ => intro i heq; cases heq
  | gate_step _ _ _ _ _ => intro i heq; cases heq

/-- `MQOut i` is irreducible: it cannot step to any process. -/
theorem mq_out_irreducible (i : ℕ) {q : Process} (h : Reduces (MQOut i) q) : False :=
  mq_out_reduces_false h i rfl

theorem reduce_via_sc_l (p p' q : Process) :
    SC p p' → Reduces p' q → Reduces p q :=
  fun h hr => Reduces.sc p p' q q h hr (SC.refl q)

theorem reduce_via_sc_r (p q' q : Process) :
    Reduces p q' → SC q' q → Reduces p q :=
  fun hr h => Reduces.sc p p q' q (SC.refl p) hr h

inductive MultiStep : Process → Process → Prop where
  | refl (p : Process) : MultiStep p p
  | step (p q r : Process) : Reduces p q → MultiStep q r → MultiStep p r

notation:50 p " →* " q => MultiStep p q

theorem MultiStep.one {p q : Process} (h : Reduces p q) : p →* q :=
  .step p q q h (.refl q)

theorem MultiStep.trans {p q r : Process} (h1 : p →* q) (h2 : q →* r) : p →* r := by
  induction h1 with
  | refl => exact h2
  | step p' q' _ hr _ ih => exact .step p' q' r hr (ih h2)

theorem MultiStep.par_l {p p' : Process} (q : Process) (h : p →* p') :
    MQPar p q →* MQPar p' q := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ hr _ ih => exact .step _ _ _ (Reduces.par_l _ _ _ hr) ih

theorem MultiStep.par_r (p : Process) {q q' : Process} (h : q →* q') :
    MQPar p q →* MQPar p q' := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ hr _ ih => exact .step _ _ _ (Reduces.par_r _ _ _ hr) ih

/-! ## Common Infrastructure Instances -/

open _root_.ProcessCalculi

instance : HasPar Process where
  par := MQPar

instance : HasNil Process where
  nil := MQNil

instance : HasNu Process where
  nu := MQNu

instance : HasSC Process where
  sc := SC
  sc_refl := SC.refl
  sc_symm := SC.symm
  sc_trans := SC.trans

end Mettapedia.Languages.ProcessCalculi.MQCalculus
