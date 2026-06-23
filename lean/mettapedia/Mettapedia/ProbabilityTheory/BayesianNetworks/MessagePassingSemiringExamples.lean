import Init.Data.Nat.MinMax
import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassingLiterature

/-!
# Tiny Semiring Examples for Belief Propagation

This module gives a small executable example showing that the abstract BP update
equations really do different work when instantiated with different semiring
carriers.

We use the same one-factor, two-variable graph in two carriers:

* ordinary `Nat`, where factor-to-variable updates sum over hidden states;
* `MaxTimesNat`, where addition is `max`, so the same update keeps only the
  best hidden state.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

open scoped Classical BigOperators

namespace MessagePassingSemiringExamples

open MessagePassing

/-- A tiny commutative semiring whose additive operation is `max` and whose
multiplicative operation is ordinary natural-number multiplication. -/
structure MaxTimesNat where
  toNat : Nat
  deriving DecidableEq, Repr

@[ext] theorem MaxTimesNat.ext {a b : MaxTimesNat} (h : a.toNat = b.toNat) : a = b := by
  cases a
  cases b
  simp at h
  simp [h]

instance : Zero MaxTimesNat := ⟨⟨0⟩⟩
instance : One MaxTimesNat := ⟨⟨1⟩⟩
instance : Add MaxTimesNat := ⟨fun a b => ⟨max a.toNat b.toNat⟩⟩
instance : Mul MaxTimesNat := ⟨fun a b => ⟨a.toNat * b.toNat⟩⟩

@[simp] theorem toNat_zero : (0 : MaxTimesNat).toNat = 0 := rfl
@[simp] theorem toNat_one : (1 : MaxTimesNat).toNat = 1 := rfl
@[simp] theorem toNat_add (a b : MaxTimesNat) : (a + b).toNat = max a.toNat b.toNat := rfl
@[simp] theorem toNat_mul (a b : MaxTimesNat) : (a * b).toNat = a.toNat * b.toNat := rfl

instance : CommSemiring MaxTimesNat where
  add := (· + ·)
  add_assoc a b c := by
    ext
    simp [Nat.max_assoc]
  zero := 0
  zero_add a := by
    ext
    simp
  add_zero a := by
    ext
    simp
  nsmul n a := if n = 0 then 0 else a
  nsmul_zero a := by
    ext
    simp
  nsmul_succ n a := by
    by_cases h : n = 0
    · subst h
      ext
      simp
    · ext
      simp [h]
  add_comm a b := by
    ext
    simp [Nat.max_comm]
  mul := (· * ·)
  left_distrib a b c := by
    ext
    simp
  right_distrib a b c := by
    ext
    simp
  zero_mul a := by
    ext
    simp
  mul_zero a := by
    ext
    simp
  mul_assoc a b c := by
    ext
    simp [Nat.mul_assoc]
  one := 1
  one_mul a := by
    ext
    simp
  mul_one a := by
    ext
    simp
  mul_comm a b := by
    ext
    simp [Nat.mul_comm]

inductive DemoVar
  | hidden
  | target
  deriving DecidableEq, Fintype, Repr

inductive DemoFactor
  | pair
  deriving DecidableEq, Fintype, Repr

def pairScope : Finset DemoVar := {DemoVar.hidden, DemoVar.target}

theorem pairScope_mem_hidden : DemoVar.hidden ∈ pairScope := by
  simp [pairScope]

theorem pairScope_mem_target : DemoVar.target ∈ pairScope := by
  simp [pairScope]

theorem pairScope_erase_target : pairScope.erase DemoVar.target = {DemoVar.hidden} := by
  ext v
  cases v <;> simp [pairScope]

/-- A tiny shared weight table. The target state `true` has two competing hidden
explanations with weights `2` and `3`. -/
def rawPotential (xTarget xHidden : Bool) : Nat :=
  if xTarget then
    if xHidden then 3 else 2
  else
    if xHidden then 1 else 1

def pairPotentialNat (x : ∀ v ∈ pairScope, Bool) : Nat :=
  rawPotential
    (x DemoVar.target (by simp [pairScope]))
    (x DemoVar.hidden (by simp [pairScope]))

def pairPotentialMax (x : ∀ v ∈ pairScope, Bool) : MaxTimesNat :=
  ⟨pairPotentialNat x⟩

def sumProductFg : FactorGraph DemoVar Nat where
  stateSpace := fun _ => Bool
  factors := DemoFactor
  scope := fun _ => pairScope
  potential := fun _ => pairPotentialNat

def maxProductFg : FactorGraph DemoVar MaxTimesNat where
  stateSpace := fun _ => Bool
  factors := DemoFactor
  scope := fun _ => pairScope
  potential := fun _ => pairPotentialMax

instance : ∀ v : DemoVar, Fintype (sumProductFg.stateSpace v) := by
  intro v
  dsimp [sumProductFg]
  infer_instance

instance : ∀ v : DemoVar, DecidableEq (sumProductFg.stateSpace v) := by
  intro v
  dsimp [sumProductFg]
  infer_instance

instance : Fintype sumProductFg.factors := by
  dsimp [sumProductFg]
  infer_instance

instance : DecidableEq sumProductFg.factors := by
  dsimp [sumProductFg]
  infer_instance

instance : ∀ v : DemoVar, Fintype (maxProductFg.stateSpace v) := by
  intro v
  dsimp [maxProductFg]
  infer_instance

instance : ∀ v : DemoVar, DecidableEq (maxProductFg.stateSpace v) := by
  intro v
  dsimp [maxProductFg]
  infer_instance

instance : Fintype maxProductFg.factors := by
  dsimp [maxProductFg]
  infer_instance

instance : DecidableEq maxProductFg.factors := by
  dsimp [maxProductFg]
  infer_instance

noncomputable def sumProductMessageToTarget :
    Bool → Nat :=
  MessagePassing.SumProduct.factorToVar
    (fg := sumProductFg)
    (MessagePassing.unitVarToFactor (fg := sumProductFg))
    DemoFactor.pair
    DemoVar.target
    (by simp [sumProductFg, pairScope])

noncomputable def maxProductMessageToTarget :
    Bool → MaxTimesNat :=
  MessagePassing.MaxProduct.factorToVar
    (fg := maxProductFg)
    (MessagePassing.unitVarToFactor (fg := maxProductFg))
    DemoFactor.pair
    DemoVar.target
    (by simp [maxProductFg, pairScope])

theorem sumProductMessageToTarget_eq :
    sumProductMessageToTarget = fun xTarget => if xTarget then 5 else 2 := by
  funext xTarget
  have h :=
    MessagePassing.factorToVarUpdate_eq_sum_of_otherScopeSingleton
      (fg := sumProductFg)
      (μ := MessagePassing.unitVarToFactor (fg := sumProductFg))
      (f := DemoFactor.pair) (v := DemoVar.target) (u := DemoVar.hidden)
      (hv := by simp [sumProductFg, pairScope])
      (hSingle := pairScope_erase_target)
  cases xTarget with
  | false =>
      simpa [sumProductMessageToTarget, MessagePassing.SumProduct.factorToVar,
        MessagePassing.unitVarToFactor, sumProductFg, pairPotentialNat, rawPotential, pairScope]
        using! congrArg (fun φ => φ false) h
  | true =>
      simpa [sumProductMessageToTarget, MessagePassing.SumProduct.factorToVar,
        MessagePassing.unitVarToFactor, sumProductFg, pairPotentialNat, rawPotential, pairScope]
        using! congrArg (fun φ => φ true) h

theorem maxProductMessageToTarget_eq :
    maxProductMessageToTarget = fun xTarget => if xTarget then ⟨3⟩ else ⟨1⟩ := by
  funext xTarget
  have h :=
    MessagePassing.factorToVarUpdate_eq_sum_of_otherScopeSingleton
      (fg := maxProductFg)
      (μ := MessagePassing.unitVarToFactor (fg := maxProductFg))
      (f := DemoFactor.pair) (v := DemoVar.target) (u := DemoVar.hidden)
      (hv := by simp [maxProductFg, pairScope])
      (hSingle := pairScope_erase_target)
  cases xTarget with
  | false =>
      simpa [maxProductMessageToTarget, MessagePassing.MaxProduct.factorToVar,
        MessagePassing.unitVarToFactor, maxProductFg, pairPotentialMax, pairPotentialNat,
        rawPotential, pairScope]
        using! congrArg (fun φ => φ false) h
  | true =>
      simpa [maxProductMessageToTarget, MessagePassing.MaxProduct.factorToVar,
        MessagePassing.unitVarToFactor, maxProductFg, pairPotentialMax, pairPotentialNat,
        rawPotential, pairScope]
        using! congrArg (fun φ => φ true) h

theorem sumProductMessage_true :
    sumProductMessageToTarget true = 5 := by
  simp [sumProductMessageToTarget_eq]

theorem maxProductMessage_true :
    (maxProductMessageToTarget true).toNat = 3 := by
  simp [maxProductMessageToTarget_eq]

theorem semiring_outputs_diverge :
    sumProductMessageToTarget true ≠ (maxProductMessageToTarget true).toNat := by
  simp [sumProductMessage_true, maxProductMessage_true]

end MessagePassingSemiringExamples

end Mettapedia.ProbabilityTheory.BayesianNetworks
