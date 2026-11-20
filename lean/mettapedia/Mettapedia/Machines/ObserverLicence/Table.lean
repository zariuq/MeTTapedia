import Mettapedia.Machines.ObserverLicence.Presentations
import Mettapedia.Machines.BoundedSearchPortfolio
import Mettapedia.Machines.ObserverLicence.WeightedCounts

/-!
# Observer requirements and the distinction between equality and choice

The table describes mathematical observers, not syntax positions. Unordered
first-witness selection refines a permitted choice; it does not make two
different witnesses equal. A declared order changes that contract. Effects,
raises, unstable reads, incomplete inner aggregates and an unlicensed
continuation boundary prevent speculative admission. A native classifier must
establish those properties; this table does not infer them from a call's name.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ObserverLicence

universe u v
variable {α : Type u} {β : Type v}

inductive ProducerOrder where
  | bag
  | declared
  deriving DecidableEq, Repr

inductive ProducerClass where
  | pure
  | totalArithmetic
  | stableRead
  | writing
  | raising
  deriving DecidableEq, Repr

def ProducerClass.quiet : ProducerClass → Bool
  | .pure | .totalArithmetic | .stableRead => true
  | .writing | .raising => false

inductive Consumer where
  | once
  | select (number : Nat)
  | collapse
  | count
  | existence
  | foldOrdered
  | foldCommuting
  deriving DecidableEq, Repr

inductive ObservationRequirement where
  | chosenWitness
  | nonemptiness
  | orderedPrefix
  | answerBag
  | orderedSequence
  deriving DecidableEq, Repr

structure Requirements where
  agreement : ObservationRequirement
  demand : Option Nat
  deriving DecidableEq, Repr

def requirements (order : ProducerOrder) : Consumer → Requirements
  | .once => ⟨if order = .bag then .chosenWitness else .orderedPrefix, some 1⟩
  | .select number =>
      ⟨if order = .bag then .chosenWitness else .orderedPrefix, some number⟩
  | .collapse => ⟨if order = .bag then .answerBag else .orderedSequence, none⟩
  | .count | .foldCommuting => ⟨.answerBag, none⟩
  | .existence => ⟨.nonemptiness, some 1⟩
  | .foldOrdered => ⟨.orderedSequence, none⟩

/-- Whole-region speculative eligibility. The two boundary bits are separate
obligations: purity of a generator does not certify an enclosing aggregate or
goals between its return and the observer's commit. -/
def admitsPortfolio (order : ProducerOrder) (kind : ProducerClass) (observer : Consumer)
    (innerAggregatesComplete boundaryLicensed : Bool) : Bool :=
  match observer with
  | .select 0 => true
  | .once | .select _ =>
      kind.quiet && innerAggregatesComplete && boundaryLicensed && decide (order = .bag)
  | .existence => kind.quiet && innerAggregatesComplete && boundaryLicensed
  | .collapse | .count | .foldOrdered | .foldCommuting => false

/-- A complete pure drain may forget order only for an unordered producer or
an observer with a permutation law. An arbitrary fold remains conservative. -/
def admitsUnorderedDrain (order : ProducerOrder) (kind : ProducerClass)
    (observer : Consumer) (innerAggregatesComplete boundaryLicensed : Bool) : Bool :=
  kind.quiet && innerAggregatesComplete && boundaryLicensed &&
    match observer with
    | .count | .existence | .foldCommuting => true
    | .collapse => decide (order = .bag)
    | .once | .select _ | .foldOrdered => false

structure LicenceKey where
  order : ProducerOrder
  producer : ProducerClass
  consumer : Consumer
  innerAggregatesComplete : Bool
  boundaryLicensed : Bool
  deriving DecidableEq, Repr

inductive ExecutionKind where
  | source
  | completePermutation
  | witnessPortfolio
  | countFusion
  | preferredCountFusion
  deriving DecidableEq, Repr

/-- One observer-admission decision for native clients. Representability,
allocation and exact source/authority validation are independent checks. -/
def admission (key : LicenceKey) : ExecutionKind → Bool
  | .source => true
  | .completePermutation => admitsUnorderedDrain key.order key.producer key.consumer
      key.innerAggregatesComplete key.boundaryLicensed
  | .witnessPortfolio => admitsPortfolio key.order key.producer key.consumer
      key.innerAggregatesComplete key.boundaryLicensed
  | .countFusion | .preferredCountFusion =>
      key.producer.quiet && key.innerAggregatesComplete && key.boundaryLicensed &&
        decide (key.consumer = .count)

theorem ordered_first_never_gets_a_choice_licence (kind : ProducerClass) (inner boundary : Bool) :
    admission ⟨.declared, kind, .once, inner, boundary⟩ .witnessPortfolio = false := by
  simp [admission, admitsPortfolio]

theorem a_count_licence_retains_completion (order : ProducerOrder) (kind : ProducerClass)
    (inner boundary : Bool) :
    (requirements order .count).demand = none ∧
      admission ⟨order, kind, .count, inner, boundary⟩ .witnessPortfolio = false := by
  exact ⟨rfl, rfl⟩

theorem no_observer_can_hide_changed_effects {Effect : Type*}
    (observer : List α → β) (answers : List α) (first second : List Effect)
    (different : first ≠ second) :
    (observer answers, first) ≠ (observer answers, second) := by
  intro same
  exact different (congrArg Prod.snd same)

/-- Proof-valued semantic cells shared by admission consumers. The fold cell
requires commuting accumulator actions, not merely commutative payloads. -/
structure LicenceTable (α : Type u) (β : Type v) where
  bagOnce : ∀ (answers : Multiset α) value,
    Observes (.bag answers) once (some value) ↔ value ∈ answers
  bagNone : ∀ answers : Multiset α, Observes (.bag answers) once none ↔ answers = 0
  orderedOnce : ∀ (answers : List α) result,
    Observes (.ordered answers) once result ↔ answers.head? = result
  bagSelect : ∀ (answers : Multiset α) number selected,
    Observes (.bag answers) (select number) selected ↔
      ∃ suffix : List α, ((selected ++ suffix : List α) : Multiset α) = answers ∧
        selected.length = min number answers.card
  orderedSelect : ∀ (answers : List α) number result,
    Observes (.ordered answers) (select number) result ↔ answers.take number = result
  bagCollapse : ∀ source result : List α,
    Observes (.bag (source : Multiset α)) collapse result ↔ result.Perm source
  orderedCollapse : ∀ answers result : List α,
    Observes (.ordered answers) collapse result ↔ answers = result
  count : BagInvariant (ObserverLicence.count : List α → Nat)
  existence : BagInvariant (existsAnswer : List α → Bool)
  fold : ∀ (step : β → α → β), Commutes step → ∀ initial,
    BagInvariant (fun answers => answers.foldl step initial)
  weightedCount : ∀ {Reply : Type} (weighted : List (Reply × Nat)),
    WeightedCounts.rawCount weighted = (WeightedCounts.expand weighted).foldl (fun total _ => total + 1) 0
  preferredWeightedCount : ∀ {Reply : Type} (isError : Reply → Bool) (weighted : List (Reply × Nat)),
    WeightedCounts.preferredCount (WeightedCounts.summarize isError weighted) =
      (RuntimePlumbing.SuccessPriority.select isError (WeightedCounts.expand weighted)).length
  inhabited : ∀ (producer : Producer α) (observer : List α → β),
    ∃ result, Observes producer observer result

theorem licenceTable (α : Type u) (β : Type v) : LicenceTable α β := {
  bagOnce := bag_once_some
  bagNone := bag_once_none
  orderedOnce := ordered_once
  bagSelect := bag_select_iff
  orderedSelect := ordered_select
  bagCollapse := collapse_superpose
  orderedCollapse := ordered_collapse
  count := count_invariant
  existence := exists_invariant
  fold := fold_invariant
  weightedCount := WeightedCounts.raw_count_fusion
  preferredWeightedCount := WeightedCounts.preferred_count_exact
  inhabited := observation_exists
}

theorem declared_once_refuses_portfolio (kind : ProducerClass) (inner boundary : Bool) :
    admitsPortfolio .declared kind .once inner boundary = false := by
  simp [admitsPortfolio]

theorem nonzero_portfolio_requires_quiet (order : ProducerOrder) (kind : ProducerClass)
    (observer : Consumer) (inner boundary : Bool)
    (nonzero : observer ≠ .select 0)
    (admitted : admitsPortfolio order kind observer inner boundary = true) :
    kind.quiet = true ∧ inner = true ∧ boundary = true := by
  cases observer <;> simp_all [admitsPortfolio]

theorem writes_refuse_speculation (order : ProducerOrder) (observer : Consumer)
    (nonzero : observer ≠ .select 0) (inner boundary : Bool) :
    admitsPortfolio order .writing observer inner boundary = false := by
  cases observer <;> simp_all [admitsPortfolio, ProducerClass.quiet]

theorem raises_refuse_speculation (order : ProducerOrder) (observer : Consumer)
    (nonzero : observer ≠ .select 0) (inner boundary : Bool) :
    admitsPortfolio order .raising observer inner boundary = false := by
  cases observer <;> simp_all [admitsPortfolio, ProducerClass.quiet]

theorem zero_demand_does_not_need_a_purity_claim (order : ProducerOrder)
    (kind : ProducerClass) (inner boundary : Bool) :
    admitsPortfolio order kind (.select 0) inner boundary = true := rfl

theorem count_on_an_ordered_producer_forgets_order (answers : List α) (number : Nat) :
    Observes (.ordered answers) count number ↔
      Observes (.bag (answers : Multiset α)) count number :=
  invariant_refinement answers count count_invariant number

theorem existence_on_an_ordered_producer_forgets_order (answers : List α) (found : Bool) :
    Observes (.ordered answers) existsAnswer found ↔
      Observes (.bag (answers : Multiset α)) existsAnswer found :=
  invariant_refinement answers existsAnswer exists_invariant found

theorem commuting_fold_on_an_ordered_producer_forgets_order (answers : List α)
    (step : β → α → β) (commutes : Commutes step) (initial result : β) :
    Observes (.ordered answers) (fun xs => xs.foldl step initial) result ↔
      Observes (.bag (answers : Multiset α)) (fun xs => xs.foldl step initial) result :=
  invariant_refinement answers _ (fold_invariant step commutes initial) result

def firstFatal {Error : Type v} : List (Except Error α) → Except Error (Option α)
  | [] => .ok none
  | .ok value :: _ => .ok (some value)
  | .error fault :: _ => .error fault

namespace Controls

theorem same_licence_for_three_quiet_classes :
    admitsPortfolio .bag .pure .once true true = true ∧
      admitsPortfolio .bag .totalArithmetic .once true true = true ∧
      admitsPortfolio .bag .stableRead .once true true = true := by decide

theorem an_outer_once_does_not_erase_aggregate_or_boundary_obligations :
    admitsPortfolio .bag .pure .once false true = false ∧
      admitsPortfolio .bag .pure .once true false = false := by decide

theorem complete_count_is_not_a_first_witness :
    admitsPortfolio .bag .pure .count true true = false ∧
      admitsUnorderedDrain .declared .pure .count true true = true := by decide

theorem a_raise_and_a_success_are_not_interchangeable :
    ([Except.ok 7, Except.error 3] : List (Except Nat Nat)).Perm
      [.error 3, .ok 7] ∧
      firstFatal ([Except.ok 7, Except.error 3] : List (Except Nat Nat)) = .ok (some 7) ∧
      firstFatal ([Except.error 3, Except.ok 7] : List (Except Nat Nat)) = .error 3 :=
  ⟨List.Perm.swap _ _ [], rfl, rfl⟩

theorem count_existence_and_fold_need_different_completion :
    existsAnswer ([7] : List Nat) = existsAnswer [7, 8] ∧
      count ([7] : List Nat) ≠ count [7, 8] ∧
      ([7] : List Nat).foldl (· + ·) 0 ≠ [7, 8].foldl (· + ·) 0 ∧
      collapse ([7] : List Nat) ≠ collapse [7, 8] := by decide

theorem an_unfinished_short_select_is_not_a_complete_answer :
    ¬ Observes (.bag (([1, 2] : List Nat) : Multiset Nat)) (select 2) [1] := by
  rw [bag_select_iff]
  rintro ⟨_, _, impossible⟩
  contradiction

end Controls

end Mettapedia.Machines.ObserverLicence
