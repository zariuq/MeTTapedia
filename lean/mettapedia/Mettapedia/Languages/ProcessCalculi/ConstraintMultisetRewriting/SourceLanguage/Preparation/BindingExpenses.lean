import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.BindingTemplates

/-!
# Quoting and metering the prepared instruction stream

The measured realization interprets the same instruction sequence as
the plain realization. A declined instruction keeps the charge of all
calls already made. The complete stream's quotation is computed at
preparation, allowing entry to reject a short work budget before any
instruction is attempted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.BindingExpenses

open Mettapedia.OSLF.Binding
open BindingPlans BindingTemplates

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}

structure Charged (A : Type) where
  answer : Except Refusal A
  elapsed : Nat

def Charged.bind {A B : Type} (first : Charged A) (next : A → Charged B) : Charged B :=
  match first.answer with
  | .error reason => ⟨.error reason, first.elapsed⟩
  | .ok value =>
    let later := next value
    ⟨later.answer, first.elapsed + later.elapsed⟩

instance : Monad Charged where
  pure value := ⟨.ok value, 0⟩
  bind := Charged.bind
  map fn result := ⟨result.answer.map fn, result.elapsed⟩

private theorem bind_error {A B : Type} (failure : Refusal) (elapsed : Nat) (next : A → Charged B) :
    (⟨Except.error failure, elapsed⟩ : Charged A) >>= next = ⟨.error failure, elapsed⟩ := rfl

private theorem bind_ok {A B : Type} (value : A) (elapsed : Nat) (next : A → Charged B) :
    (⟨Except.ok value, elapsed⟩ : Charged A) >>= next = ⟨(next value).answer, elapsed + (next value).elapsed⟩ := rfl

private theorem map_eq {A B : Type} (fn : A → B) (result : Charged A) :
    fn <$> result = ⟨result.answer.map fn, result.elapsed⟩ := rfl

private theorem except_error {A B : Type} (failure : Refusal) (next : A → Except Refusal B) :
    Except.error failure >>= next = Except.error failure := rfl

private theorem except_ok {A B : Type} (value : A) (next : A → Except Refusal B) :
    Except.ok value >>= next = next value := rfl

attribute [local simp] bind_error bind_ok map_eq except_error except_ok

structure Prices (κ : Keys S) (Γ : Ctx S) (star : S.Srt) where
  openScope : Nat
  hold : Operand κ Γ star → Nat

variable (templates : Templates κ Γ star) (prices : Prices κ Γ star)

def pricedHold (operand : Operand κ Γ star) (table : templates.Table) (entry : List Nat) :
    Charged templates.Value :=
  ⟨templates.hold operand table entry, prices.hold operand⟩

def pricedOpen (table : templates.Table) (offset scope : Nat) (parent : Option Nat) : Charged templates.Table :=
  ⟨templates.openScope table offset scope parent, prices.openScope⟩

def bindingQuote (code : List (Binding κ Γ star)) : Nat :=
  (code.map fun binding => prices.hold binding.value + prices.openScope + prices.hold binding.pattern).sum

def planQuote (plan : Plan κ Γ star) : Nat :=
  bindingQuote prices plan.code + prices.hold plan.result

theorem quote_le_size (plan : Plan κ Γ star) (rate : Nat)
    (opening : prices.openScope ≤ rate)
    (held : ∀ operand, prices.hold operand ≤ rate *
      (1 + (operand.assemble.nodes + 2 * operand.names.length))) :
    planQuote prices plan ≤ rate * plan.size := by
  let contribution (operand : Operand κ Γ star) := operand.assemble.nodes + 2 * operand.names.length
  have bindingBound (binding : Binding κ Γ star) :
      prices.hold binding.value + prices.openScope + prices.hold binding.pattern ≤
        rate * (3 + (contribution binding.pattern + contribution binding.value)) := by
    have next := Nat.add_le_add (Nat.add_le_add (held binding.value) opening) (held binding.pattern)
    change _ ≤ rate * (1 + contribution binding.value) + rate + rate * (1 + contribution binding.pattern) at next
    simp only [Nat.mul_add, Nat.mul_one] at next ⊢
    omega
  have listBound (code : List (Binding κ Γ star)) : bindingQuote prices code ≤
      rate * (3 * code.length + (code.map fun row => contribution row.pattern + contribution row.value).sum) := by
    induction code with
    | nil => simp [bindingQuote]
    | cons first later ih =>
      have combined := Nat.add_le_add (bindingBound first) ih
      simp only [bindingQuote, List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one] at combined ⊢
      omega
  have total := Nat.add_le_add (listBound plan.code) (held plan.result)
  change _ ≤ rate * (3 * plan.code.length + (plan.code.map (fun row => contribution row.pattern +
    contribution row.value)).sum) + rate * (1 + contribution plan.result) at total
  change _ ≤ rate * (3 * plan.code.length + 1 + ((plan.code.map (fun row => contribution row.pattern +
    contribution row.value)).sum + contribution plan.result))
  simp only [planQuote, Nat.mul_add, Nat.mul_one] at total ⊢
  omega

theorem measured_bindings (origin : Nat) (entry : List Nat) (code : List (Binding κ Γ star))
    (offset : Nat) (table : templates.Table) :
    let actual := runBindingsWith (pricedHold templates prices) (pricedOpen templates prices)
      origin entry code offset table
    actual.answer = runBindings templates origin entry code offset table ∧
      actual.elapsed ≤ bindingQuote prices code := by
  induction code generalizing offset table with
  | nil => exact ⟨rfl, Nat.le_refl _⟩
  | cons binding rest ih =>
    rw [runBindings_cons]
    simp only [runBindingsWith, pricedHold, pricedOpen, bindingQuote, List.map_cons, List.sum_cons]
    cases received : templates.hold binding.value table entry with
    | error reason => simp; omega
    | ok value =>
      simp only [bind_ok, except_ok]
      cases opened : templates.openScope table offset (origin + offset) binding.parent with
      | error reason => simp; omega
      | ok next =>
        simp only [bind_ok, except_ok]
        cases patterned : templates.hold binding.pattern next entry with
        | error reason => simp; omega
        | ok pattern =>
          simp only [bind_ok, except_ok, map_eq]
          have later := ih (offset + 1) next
          exact ⟨congrArg (Except.map _) later.1, by
            have pays := later.2
            unfold bindingQuote at pays
            omega⟩

def measure (plan : Plan κ Γ star) (origin : Nat) (entry : List Nat) (offset : Nat)
    (table : templates.Table) : Charged ((templates.Table × List (templates.Value × templates.Value)) × templates.Value) :=
  runWith (pricedHold templates prices) (pricedOpen templates prices) plan origin entry offset table

theorem measured_plan (plan : Plan κ Γ star) (origin : Nat) (entry : List Nat) (offset : Nat)
    (table : templates.Table) :
    let result := measure templates prices plan origin entry offset table
    result.answer = BindingTemplates.run templates plan origin entry offset table ∧
      result.elapsed ≤ planQuote prices plan := by
  have ⟨same, bounded⟩ := measured_bindings templates prices origin entry plan.code offset table
  let earlier := runBindingsWith (pricedHold templates prices) (pricedOpen templates prices)
    origin entry plan.code offset table
  change earlier.answer = _ at same
  change earlier.elapsed ≤ bindingQuote prices plan.code at bounded
  rw [run_parts, ← same]
  change (earlier >>= fun state => Prod.mk state <$> pricedHold templates prices plan.result state.1 entry).answer =
    _ ∧ (earlier >>= fun state => Prod.mk state <$> pricedHold templates prices plan.result state.1 entry).elapsed ≤ _
  cases prior : earlier with
  | mk answer elapsed =>
    have bound : elapsed ≤ bindingQuote prices plan.code := by simpa only [prior] using bounded
    cases answer with
    | error reason =>
      simp only [bind_error, except_error, true_and, planQuote]
      exact bound.trans (Nat.le_add_right _ _)
    | ok state =>
      simp only [bind_ok, except_ok, map_eq, pricedHold, planQuote]
      exact ⟨rfl, Nat.add_le_add_right bound _⟩

structure QuotedPlan (prices : Prices κ Γ star) where
  plan : Plan κ Γ star
  work : Nat
  exactWork : work = planQuote prices plan

def reserve (plan : Plan κ Γ star) : QuotedPlan prices := ⟨plan, planQuote prices plan, rfl⟩

def attempt (quoted : QuotedPlan prices) (work origin : Nat) (entry : List Nat)
    (offset : Nat) (table : templates.Table) :
    Charged ((templates.Table × List (templates.Value × templates.Value)) × templates.Value) :=
  if quoted.work ≤ work then measure templates prices quoted.plan origin entry offset table
  else ⟨.error .credit, 0⟩

theorem attempt_bound (quoted : QuotedPlan prices) (work origin : Nat) (entry : List Nat)
    (offset : Nat) (table : templates.Table) :
    (attempt templates prices quoted work origin entry offset table).elapsed ≤ work := by
  by_cases enough : quoted.work ≤ work
  · rw [attempt, if_pos enough]
    exact ((measured_plan templates prices quoted.plan origin entry offset table).2.trans
      (quoted.exactWork ▸ enough))
  · simp [attempt, enough]

theorem attempt_exact (quoted : QuotedPlan prices) (work origin : Nat) (entry : List Nat)
    (offset : Nat) (table : templates.Table) (enough : quoted.work ≤ work) :
    (attempt templates prices quoted work origin entry offset table).answer =
      BindingTemplates.run templates quoted.plan origin entry offset table := by
  rw [attempt, if_pos enough]
  exact (measured_plan templates prices quoted.plan origin entry offset table).1

theorem short_reservation_spends_no_template_work (quoted : QuotedPlan prices) (work origin : Nat)
    (entry : List Nat) (offset : Nat) (table : templates.Table) (short : work < quoted.work) :
    attempt templates prices quoted work origin entry offset table = ⟨.error .credit, 0⟩ := by
  simp [attempt, Nat.not_le.mpr short]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.BindingExpenses
