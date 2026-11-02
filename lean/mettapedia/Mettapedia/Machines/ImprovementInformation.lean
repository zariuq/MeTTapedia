import Mettapedia.Machines.KeyedImprovementTransactions
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Information sufficient for a keyed improvement

The key and candidate are shared context. A worker that still has the live
store needs only the comparison bit to select the correct update. Its exact
validity region is equality of that bit, not equality of the old payload.

A source primitive-count observer distinguishes missing insertion from existing
replacement. A consumer without the old store needs still more information:
for natural-number candidate `c`, the result has exactly `c + 2` classes.
These are interface-relative bounds, not bounds on total implementation memory.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.KeyedImprovement.Information

open Transactions

variable {Key Value : Type} [DecidableEq Key] [LinearOrder Value]

omit [LinearOrder Value] in
@[simp] theorem executePlan_flag (store : Store Key Value) (key : Key)
    (candidate : Value) (bit : Bool) : (executePlan store key candidate bit).2 = bit := by
  cases bit <;> simp [executePlan]

/-- Necessary as well as sufficient: the return flag is part of the observer. -/
theorem plan_exact_iff (store : Store Key Value) (key : Key) (candidate : Value) (bit : Bool) :
    executePlan store key candidate bit = improve store key candidate ↔
      bit = branch (store key) candidate := by
  rw [← planned_branch_exact store key candidate]
  constructor
  · intro h
    simpa using congrArg Prod.snd h
  · rintro rfl
    rfl

/-- This ticket deliberately retains no old payload or occurrence name. -/
structure DecisionTicket (Key Value : Type) where
  key : Key
  candidate : Value
  bit : Bool

def prepareDecision (store : Store Key Value) (key : Key) (candidate : Value) :
    DecisionTicket Key Value := ⟨key, candidate, branch (store key) candidate⟩

def tryDecision (store : Store Key Value) (ticket : DecisionTicket Key Value) :
    Option (Store Key Value × Bool) :=
  if ticket.bit = branch (store ticket.key) ticket.candidate then
    some (executePlan store ticket.key ticket.candidate ticket.bit)
  else none

theorem decision_admitted_iff (store : Store Key Value) (ticket : DecisionTicket Key Value) :
    (tryDecision store ticket).isSome = true ↔
      ticket.bit = branch (store ticket.key) ticket.candidate := by
  simp [tryDecision]

theorem decision_accepted_exact (store : Store Key Value) (ticket : DecisionTicket Key Value)
    (result : Store Key Value × Bool) (h : tryDecision store ticket = some result) :
    result = improve store ticket.key ticket.candidate := by
  unfold tryDecision at h
  split at h
  next same =>
    exact (Option.some.inj h).symm.trans ((plan_exact_iff _ _ _ _).2 same)
  next => simp at h

/-- No rejected bit can safely be executed with the same return convention. -/
theorem decision_refused_inexact (store : Store Key Value) (ticket : DecisionTicket Key Value)
    (h : tryDecision store ticket = none) :
    executePlan store ticket.key ticket.candidate ticket.bit ≠
      improve store ticket.key ticket.candidate := by
  intro exactPlan
  have := (plan_exact_iff _ _ _ _).1 exactPlan
  simp [tryDecision, this] at h

def decisionRepresentative (candidate : Nat) (bit : Bool) : Option Nat :=
  if bit then none else some candidate

@[simp] theorem decision_representative (candidate : Nat) (bit : Bool) :
    branch (decisionRepresentative candidate bit) candidate = bit := by
  cases bit <;> simp [decisionRepresentative, branch]

theorem decision_requires_two_codes {Code : Type} [Fintype Code] (candidate : Nat)
    (encode : Option Nat → Code) (decode : Code → Bool)
    (correct : ∀ old, decode (encode old) = branch old candidate) :
    2 ≤ Fintype.card Code := by
  have injective : Function.Injective (fun bit => encode (decisionRepresentative candidate bit)) := by
    intro a b same
    simpa only [decision_representative] using
      (correct _).symm.trans ((congrArg decode same).trans (correct _))
  simpa using Fintype.card_le_of_injective _ injective

/-- One bit suffices for one fixed comparison. Answering every future
candidate comparison distinguishes the entire old value, including absence. -/
theorem decision_family_injective :
    Function.Injective (fun old : Option Nat => fun candidate => branch old candidate) := by
  intro a b same
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => have := congrFun same b; simp [branch] at this
  | some a =>
    cases b with
    | none => have := congrFun same a; simp [branch] at this
    | some b =>
      have ha := congrFun same a
      have hb := congrFun same b
      simp [branch] at ha hb
      congr 1
      omega

/-! ## Source-work observations -/

inductive SourcePlan
  | keep | insertMissing | replaceExisting
  deriving DecidableEq

instance : Fintype SourcePlan := ⟨{.keep, .insertMissing, .replaceExisting}, by
  intro p; cases p <;> simp⟩

@[simp] theorem sourcePlan_card : Fintype.card SourcePlan = 3 := by decide

def sourcePlan (candidate : Nat) : Option Nat → SourcePlan
  | none => .insertMissing
  | some old => if candidate < old then .replaceExisting else .keep

def SourcePlan.changed : SourcePlan → Bool
  | .keep => false
  | _ => true

/-- One read, followed by zero, one, or two writes. -/
def SourcePlan.debit : SourcePlan → Nat
  | .keep => 1
  | .insertMissing => 2
  | .replaceExisting => 3

theorem sourcePlan_changed (candidate : Nat) (old : Option Nat) :
    (sourcePlan candidate old).changed = branch old candidate := by
  cases old with
  | none => rfl
  | some n => by_cases h : candidate < n <;> simp [sourcePlan, branch, h, SourcePlan.changed]

def planRepresentative (candidate : Nat) : SourcePlan → Option Nat
  | .keep => some candidate
  | .insertMissing => none
  | .replaceExisting => some (candidate + 1)

@[simp] theorem plan_representative (candidate : Nat) (p : SourcePlan) :
    sourcePlan candidate (planRepresentative candidate p) = p := by
  cases p <;> simp [sourcePlan, planRepresentative]

theorem debit_injective : Function.Injective SourcePlan.debit := by
  intro a b h
  cases a <;> cases b <;> simp_all [SourcePlan.debit]

theorem source_debit_requires_three_codes {Code : Type} [Fintype Code]
    (candidate : Nat) (encode : Option Nat → Code) (decode : Code → Nat)
    (correct : ∀ old, decode (encode old) = (sourcePlan candidate old).debit) :
    3 ≤ Fintype.card Code := by
  have inj : Function.Injective (fun p => encode (planRepresentative candidate p)) := by
    intro a b h
    apply debit_injective
    have ha := correct (planRepresentative candidate a)
    have hb := correct (planRepresentative candidate b)
    simpa only [plan_representative] using ha.symm.trans ((congrArg decode h).trans hb)
  simpa using Fintype.card_le_of_injective _ inj

/-- Erasing presence loses the source-work observation even when the decision agrees. -/
theorem changed_cannot_recover_debit (candidate : Nat) :
    ¬ ∃ recover : Bool → Nat, ∀ old,
      recover (branch old candidate) = (sourcePlan candidate old).debit := by
  rintro ⟨recover, correct⟩
  have a := correct none
  have b := correct (some (candidate + 1))
  simp [branch, sourcePlan, SourcePlan.debit] at a b
  omega

/-! ## Result information without access to the old slot -/

def slotResult (candidate : Nat) : Option Nat → Option Nat × Bool
  | none => (some candidate, true)
  | some old => if candidate < old then (some candidate, true) else (some old, false)

def resultCode (candidate : Nat) : Option Nat → Fin (candidate + 2)
  | none => ⟨candidate + 1, by omega⟩
  | some old => if h : old ≤ candidate then ⟨old, by omega⟩ else ⟨candidate + 1, by omega⟩

def decodeResult (candidate : Nat) (code : Fin (candidate + 2)) : Option Nat × Bool :=
  if code.val ≤ candidate then (some code.val, false) else (some candidate, true)

theorem result_decode_exact (candidate : Nat) (old : Option Nat) :
    decodeResult candidate (resultCode candidate old) = slotResult candidate old := by
  cases old with
  | none => simp [decodeResult, resultCode, slotResult]
  | some n =>
    by_cases h : n ≤ candidate
    · simp [decodeResult, resultCode, slotResult, h, Nat.not_lt.mpr h]
    · simp [decodeResult, resultCode, slotResult, h, Nat.lt_of_not_ge h]

theorem decodeResult_injective (candidate : Nat) : Function.Injective (decodeResult candidate) := by
  intro a b h
  apply Fin.ext
  unfold decodeResult at h
  split at h <;> split at h <;> simp_all only [Prod.mk.injEq, Option.some.injEq,
    Bool.false_eq_true, Bool.true_eq_false, and_false, and_true]
  all_goals omega

theorem resultCode_eq_iff (candidate : Nat) (a b : Option Nat) :
    resultCode candidate a = resultCode candidate b ↔ slotResult candidate a = slotResult candidate b := by
  constructor
  · intro h
    simpa only [result_decode_exact] using congrArg (decodeResult candidate) h
  · intro h
    apply decodeResult_injective
    simpa only [result_decode_exact] using h

def resultRepresentative (candidate : Nat) (code : Fin (candidate + 2)) : Option Nat :=
  if code.val ≤ candidate then some code.val else none

@[simp] theorem result_representative (candidate : Nat) (code : Fin (candidate + 2)) :
    resultCode candidate (resultRepresentative candidate code) = code := by
  apply Fin.ext
  by_cases h : code.val ≤ candidate
  · simp [resultRepresentative, resultCode, h]
  · simp only [resultRepresentative, if_neg h, resultCode]
    omega

theorem result_requires_codes {Code : Type} [Fintype Code] (candidate : Nat)
    (encode : Option Nat → Code) (decode : Code → Option Nat × Bool)
    (correct : ∀ old, decode (encode old) = slotResult candidate old) :
    candidate + 2 ≤ Fintype.card Code := by
  have inj : Function.Injective (fun i => encode (resultRepresentative candidate i)) := by
    intro a b h
    have values := (correct _).symm.trans ((congrArg decode h).trans (correct _))
    simpa only [result_representative] using (resultCode_eq_iff candidate _ _).2 values
  simpa using Fintype.card_le_of_injective _ inj

theorem result_requires_bits (candidate bits : Nat)
    (encode : Option Nat → (Fin bits → Bool)) (decode : (Fin bits → Bool) → Option Nat × Bool)
    (correct : ∀ old, decode (encode old) = slotResult candidate old) :
    candidate + 2 ≤ 2 ^ bits := by
  simpa using result_requires_codes candidate encode decode correct

namespace Controls

theorem payload_change_same_region :
    (tryDecision (fun _ : Unit => some 8) (prepareDecision (fun _ => some 10) () 7)).isSome = true ∧
    (Transactions.tryCommit (fun _ : Unit => some 8) (Transactions.prepare (fun _ => some 10) () 7)).isNone = true := by
  decide

theorem crossing_region_refused :
    (tryDecision (fun _ : Unit => some 5) (prepareDecision (fun _ => some 10) () 7)).isNone = true := by
  decide

theorem same_decision_different_work :
    branch none 7 = branch (some 10) 7 ∧ sourcePlan 7 none ≠ sourcePlan 7 (some 10) := by decide

theorem keep_bit_loses_result :
    branch (some 3) 7 = branch (some 5) 7 ∧ slotResult 7 (some 3) ≠ slotResult 7 (some 5) := by decide

theorem changed_context_distinguishes :
    resultCode 7 (some 10) = resultCode 7 (some 12) ∧
    branch (some 10) 11 ≠ branch (some 12) 11 := by decide

end Controls
end Mettapedia.Machines.KeyedImprovement.Information
