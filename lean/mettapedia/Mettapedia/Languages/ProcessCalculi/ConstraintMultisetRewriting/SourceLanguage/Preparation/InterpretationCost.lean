import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.PreparedWork

/-!
# Interpretive work in the deterministic binding fragment

The source tariff counts opening a binder, producing an operand,
constructing data and accessing authored name occurrences. These
counts are defined on the source fragment, independently of lowering.
The prepared interpreter meters the very instructions it runs, including
all attempts before a refusal. Lexical layout and constructor selection
happen during preparation.

The unit-handle instance also fits the original charged source run.
The general tariff makes data construction and access work explicit
when a representation must pay more than a move of a retained handle.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.InterpretationCost

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open BindingPlans BindingTemplates BindingSimulation
open Evaluation (Evaluator)
open Machine (State Scheduler)

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt} {Ty Storage : Type}
  {ending : ExitKind} {code : Comp κ Γ star Ty}

structure Tariff where
  opening : Nat
  operand : Nat
  constructorWork : Nat
  access : Nat

def Tariff.authored (tariff : Tariff) (datum : Data κ Γ star) : Nat :=
  tariff.operand + tariff.constructorWork * termSize datum + tariff.access * (support datum).length

def sourceWork (tariff : Tariff) (body : Fragment κ Γ star Ty ending code) : Nat :=
  body.bindings * tariff.opening + body.operandWeight tariff.authored

def Tariff.prepared (tariff : Tariff) : BindingExpenses.Prices κ Γ star where
  openScope := tariff.opening
  hold operand := tariff.operand + tariff.constructorWork * operand.assemble.nodes +
    tariff.access * operand.names.length

private theorem bindingQuote_eq (prices : BindingExpenses.Prices κ Γ star) (bindings : List (Binding κ Γ star)) :
    BindingExpenses.bindingQuote prices bindings =
      bindings.length * prices.openScope +
        (bindings.map fun row => prices.hold row.pattern + prices.hold row.value).sum := by
  induction bindings with
  | nil => simp [BindingExpenses.bindingQuote]
  | cons binding later ih =>
    change prices.hold binding.value + prices.openScope + prices.hold binding.pattern +
      BindingExpenses.bindingQuote prices later = _
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.add_mul, Nat.one_mul]
    rw [ih]
    omega

theorem preparation_discharges_the_source_tariff [DecidableEq κ.Key] (tariff : Tariff)
    (body : Fragment κ Γ star Ty ending code) (context : Context κ) (offset : Nat) :
    BindingExpenses.planQuote tariff.prepared (lower body context offset) ≤ sourceWork tariff body := by
  have adequate (context : Context κ) (datum : Data κ Γ star) :
      tariff.prepared.hold (Operand.compile context datum) ≤ tariff.authored datum := by
    simp only [Tariff.prepared, Tariff.authored, Operand.compile_nodes]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Operand.compile_slots_le context datum)) _
  have operands := lower_operandWeight_le tariff.prepared.hold tariff.authored adequate body context offset
  have quote : BindingExpenses.planQuote tariff.prepared (lower body context offset) =
      body.bindings * tariff.opening + (lower body context offset).operandWeight tariff.prepared.hold := by
    rw [BindingExpenses.planQuote, bindingQuote_eq, lower_length, Plan.operandWeight, Nat.add_assoc]
    rfl
  rw [quote]
  exact Nat.add_le_add_left operands _

/-- The measured prepared body has its usual answer and uses only
productive source work. In particular the upper bound has no dispatch
fee per source reduction or per datum. -/
theorem prepared_optimal [DecidableEq κ.Key] (tariff : Tariff) (body : Fragment κ Γ star Ty ending code)
    (context : Context κ) (origin offset : Nat) (entry : List Nat)
    (templates : Templates κ Γ star) (table : templates.Table) :
    let plan := lower body context offset
    let spent := BindingExpenses.measure templates tariff.prepared plan origin entry offset table
    spent.answer = BindingTemplates.run templates plan origin entry offset table ∧
      spent.elapsed ≤ sourceWork tariff body := by
  obtain ⟨answer, counted⟩ :=
    BindingExpenses.measured_plan templates tariff.prepared (lower body context offset) origin entry offset table
  exact ⟨answer, counted.trans (preparation_discharges_the_source_tariff tariff body context offset)⟩

/-- Including the final source service adds its own tariff once. An
insufficient reservation or a failed template is also included. -/
theorem checked_preparation_optimal [DecidableEq κ.Key] (tariff : Tariff)
    (body : Fragment κ Γ star Ty ending code) (templates : Templates κ Γ star) (solver : Solver κ Γ star)
    (around : Surrounding κ Γ star Ty) (world : ExecutionWorld Storage)
    (knowledge : List (Constraint κ Γ star)) (frames : List (Frame κ Γ star Ty))
    (cells : List (Data κ Γ star × Comp κ Γ star Ty)) (entry : List Nat) (table : templates.Table)
    (publication work credit : Nat) :
    let plan := lower body [] 0
    let reserved := BindingExpenses.reserve tariff.prepared plan
    (PreparedWork.activate templates tariff.prepared solver reserved around world knowledge frames cells entry table
      publication work credit).elapsed ≤ sourceWork tariff body + publication := by
  let plan := lower body [] 0
  let reserved := BindingExpenses.reserve tariff.prepared plan
  change (PreparedWork.activate templates tariff.prepared solver reserved around world knowledge frames cells entry table
    publication work credit).elapsed ≤ _
  by_cases ready : reserved.plan.sourceDebit ≤ credit ∧ reserved.work + publication ≤ work
  · rw [PreparedWork.activate, if_pos ready]
    have bounded := (prepared_optimal tariff body [] world.scope 0 entry templates table).2
    exact Nat.add_le_add bounded (by split; exact Nat.le_refl _; exact Nat.zero_le _)
  · rw [PreparedWork.activate, if_neg ready]
    exact Nat.zero_le _

def handleTariff : Tariff := ⟨1, 1, 0, 0⟩

private theorem handle_operands (body : Fragment κ Γ star Ty ending code) :
    body.operandWeight handleTariff.authored = 2 * body.bindings + 1 := by
  induction body with
  | hold => simp [Fragment.operandWeight, Fragment.bindings, handleTariff, Tariff.authored]
  | call => simp [Fragment.operandWeight, Fragment.bindings, handleTariff, Tariff.authored]
  | binding site pattern producer continuation producerIH bodyIH =>
    simp only [Fragment.operandWeight, Fragment.bindings, producerIH, bodyIH]
    have one : handleTariff.authored pattern = 1 := by simp [handleTariff, Tariff.authored]
    omega

private theorem handle_source_work (body : Fragment κ Γ star Ty ending code) :
    sourceWork handleTariff body = 3 * body.bindings + 1 := by
  rw [sourceWork, handle_operands]
  change body.bindings * 1 + (2 * body.bindings + 1) = _
  omega

variable {D : Discipline S Γ star} {program : Program κ Γ star D.Ty}
  {supply : Nat → Term S Γ star} {strategy : Strategy κ Γ star D.Ty}

private theorem move_pays_two {before next : Config κ Γ star D.Ty} {chargeEntry : Charge (Data κ Γ star)}
    (move : ChargedStep D program supply strategy before chargeEntry next) :
    2 ≤ chargeEntry.units := by
  cases move
  simp only [Charge.units, charge]
  omega

theorem source_pays_two_per_move {before after : Config κ Γ star D.Ty} {work : List (Charge (Data κ Γ star))}
    (run : ChargedRun D program supply strategy before work after) :
    2 * work.length ≤ units work := by
  induction run with
  | stop => simp [units]
  | advance moved _ ih =>
    have costs := move_pays_two moved
    simp only [List.length_cons, units, List.map_cons, List.sum_cons] at ih ⊢
    omega

variable {machine : Evaluator κ D Storage} (schedule : Scheduler machine strategy)

theorem runs_at_productive_cost [DecidableEq κ.Key] {comp : Comp κ Γ star D.Ty}
    (tariff : Tariff) (body : Fragment κ Γ star D.Ty ending comp)
    (compiled : compile comp = some (lower body [] 0))
    (around : Surrounding κ Γ star D.Ty) (kept : Keeps machine strategy schedule around)
    (templates : Templates κ Γ star) (table : templates.Table)
    (world : ExecutionWorld Storage) (knowledge : List (Constraint κ Γ star))
    (frames : List (Frame κ Γ star D.Ty)) (cells : List (Data κ Γ star × Comp κ Γ star D.Ty))
    (entry : List Nat) (publication work credit : Nat)
    {result : PreparedBodies.Publication κ Γ star D.Ty Storage} :
    let attempt := PreparedWork.activate templates tariff.prepared machine.solver
      (BindingExpenses.reserve tariff.prepared (lower body [] 0)) around world knowledge frames cells entry table
      publication work credit
    attempt.answer = .ok result →
      Reaches schedule result.debit (PreparedBodies.entryState around world knowledge comp frames cells entry)
        result.state ∧ attempt.elapsed ≤ sourceWork tariff body + publication := by
  dsimp only
  intro published
  have accepted := PreparedWork.activate_sound templates tariff.prepared machine.solver
    (BindingExpenses.reserve tariff.prepared (lower body [] 0)) around world knowledge frames cells entry table
    publication work credit published
  exact ⟨(PreparedBodies.activate_exact kept templates compiled world knowledge frames cells entry
    table credit accepted).2,
    checked_preparation_optimal tariff body templates machine.solver around world knowledge frames cells entry
      table publication work credit⟩

/-- In the retained-handle cost model, the same inequality holds
against the original charged run, with multiplier one. A prepared
prefix here makes progress, as required by the hybrid driver. -/
theorem handle_cost_le_charged_source [DecidableEq κ.Key] {comp : Comp κ Γ star D.Ty}
    (body : Fragment κ Γ star D.Ty ending comp) (positive : 0 < body.moves)
    {before after : State κ Γ star D.Ty Storage} (reached : Reaches schedule body.moves before after)
    (context : Context κ) (origin offset : Nat) (entry : List Nat)
    (templates : Templates κ Γ star) (table : templates.Table) :
    (BindingExpenses.measure templates handleTariff.prepared (lower body context offset)
      origin entry offset table).elapsed ≤ units (Machine.run machine strategy schedule body.moves before).2 := by
  have priced := (prepared_optimal handleTariff body context origin offset entry templates table).2
  rw [handle_source_work] at priced
  have quoted := Machine.run_charged machine strategy schedule body.moves before
  have enough := source_pays_two_per_move quoted
  rw [reached.debit] at enough
  apply priced.trans
  apply Nat.le_trans _ enough
  rw [Fragment.moves_eq] at positive ⊢
  cases ending <;> simp only [ExitKind.debit] at positive ⊢ <;> omega

structure Interpretation (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty Storage : Type) where
  state : State κ Γ star Ty Storage
  sourceCharges : List (Charge (Data κ Γ star))
  dispatches : Nat

/-- The syntax-driven reference goes through the ordinary reduction
dispatcher for each successful step. The accounting records those
entries alongside its actual result and charge trace. -/
def interpreted (fuel : Nat) (state : State κ Γ star D.Ty Storage) : Interpretation κ Γ star D.Ty Storage :=
  let run := Machine.run machine strategy schedule fuel state
  ⟨run.1, run.2, run.2.length⟩

theorem interpretation_has_positive_overhead {comp : Comp κ Γ star D.Ty}
    (tariff : Tariff) (body : Fragment κ Γ star D.Ty ending comp) (positive : 0 < body.moves)
    {before after : State κ Γ star D.Ty Storage} (execution : Reaches schedule body.moves before after)
    (dispatchPrice : Nat) (paid : 0 < dispatchPrice) :
    let ordinary := interpreted schedule body.moves before
    ordinary.state = after ∧ ordinary.dispatches = body.moves ∧
      sourceWork tariff body < sourceWork tariff body + dispatchPrice * ordinary.dispatches := by
  refine ⟨execution.state, execution.debit, ?_⟩
  change sourceWork tariff body < sourceWork tariff body +
    dispatchPrice * (Machine.run machine strategy schedule body.moves before).2.length
  rw [execution.debit]
  exact Nat.lt_add_of_pos_right (Nat.mul_pos paid positive)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.InterpretationCost
