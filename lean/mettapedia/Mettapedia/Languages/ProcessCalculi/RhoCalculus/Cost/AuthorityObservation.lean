import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ResourceTransition
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Authority receipts and lossy pricing observations

Exact funded transitions retain event identities, causal predecessors, and
occurrence-level funding contributions in their canonical receipt.  Raw
signature totals and numerical valuations are derived from that receipt.

The direction is deliberate: authority evidence determines pricing data;
pricing data is not used to reconstruct authority evidence.

The authority receipt is the finest account of a funded run.  The spend total
and the number of firings are that account read through a monoid
homomorphism.
-/

open CategoryTheory

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

namespace ReceiptEmission

/-- Forget event identity, causality, location, and funding factorisation,
retaining only the commutative raw spend total. -/
def aggregate
    (receipt : ReceiptEmission EventId Ground Location) : CostSig Ground :=
  (receipt.map fun event => event.label.rawSpend).sum

@[simp]
theorem aggregate_nil :
    aggregate ([] : ReceiptEmission EventId Ground Location) = 0 :=
  rfl

@[simp]
theorem aggregate_append
    (first second : ReceiptEmission EventId Ground Location) :
    aggregate (first ++ second) = aggregate first + aggregate second := by
  simp [aggregate, List.sum_append]

/-- Aggregation is a monoid homomorphism from ordered receipts to commutative
raw spend.  The homomorphism is intentionally not asserted to be injective. -/
def aggregateMonoidHom :
    FreeMonoid (EmittedEvent EventId Ground Location) →*
      Multiplicative (CostSig Ground) where
  toFun receipt := Multiplicative.ofAdd (aggregate (FreeMonoid.toList receipt))
  map_one' := rfl
  map_mul' first second := by
    rw [FreeMonoid.toList_mul, aggregate_append]
    rfl

/-- Aggregation out of the opposite monoid, which is how a one-object category
composes.  The target is commutative, so the order does not matter. -/
def aggregateOppositeMonoidHom :
    MulOpposite (FreeMonoid (EmittedEvent EventId Ground Location)) →*
      Multiplicative (CostSig Ground) :=
  aggregateMonoidHom.fromOpposite fun _ _ => Commute.all _ _

/-- Counting the events of a receipt is a monoid homomorphism. -/
def countMonoidHom :
    FreeMonoid (EmittedEvent EventId Ground Location) →* Multiplicative Nat where
  toFun receipt := Multiplicative.ofAdd (FreeMonoid.toList receipt).length
  map_one' := rfl
  map_mul' first second := by
    rw [FreeMonoid.toList_mul, List.length_append]
    rfl

end ReceiptEmission

namespace CostPath

/-- The authority-relevant receipt projected from an exact funded path.  It
retains occurrence identity, causal predecessors, and located contributions. -/
def authorityReceipt
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    ReceiptEmission Nat String RawCostName :=
  path.emission

@[simp]
theorem authorityReceipt_done
    {nextId : Nat} {components : List RawTraceComponent}
    (supported : TraceComponentsWellFormed components)
    (bounded : TraceComponentsBefore nextId components) :
    authorityReceipt (CostPath.done supported bounded) = [] :=
  rfl

@[simp]
theorem authorityReceipt_append
    {startId middleId finalId : Nat}
    {source middle target : List RawTraceComponent}
    (first : CostPath startId source middleId middle)
    (second : CostPath middleId middle finalId target) :
    authorityReceipt (first.append second) =
      authorityReceipt first ++ authorityReceipt second :=
  emission_append first second

/-- Raw signature accounting factors through the exact authority receipt. -/
theorem rawAccount_eq_authorityReceipt_aggregate
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    path.rawAccount = path.authorityReceipt.aggregate := by
  unfold rawAccount authorityReceipt ReceiptEmission.aggregate
  rw [path.emission_rawSpends_eq_steps]

/-- Additive pricing is a fold of the authority receipt's declared lossy
aggregate. -/
theorem additiveValue_eq_authorityReceipt_fold
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    {Delta : Type*} [AddCommMonoid Delta] (weight : String → Delta) :
    path.additiveValue weight =
      CostSig.additiveFold weight path.authorityReceipt.aggregate := by
  simp only [additiveValue, rawAccount_eq_authorityReceipt_aggregate]

/-- Multiplicative and quantale-valued pricing factors through the same
declared aggregate. -/
theorem multiplicativeValue_eq_authorityReceipt_fold
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    {Delta : Type*} [CommMonoid Delta] (weight : String → Delta) :
    path.multiplicativeValue weight =
      CostSig.multiplicativeFold weight path.authorityReceipt.aggregate := by
  simp only [multiplicativeValue, rawAccount_eq_authorityReceipt_aggregate]

end CostPath

namespace ResourceTransition

open Mettapedia.Effects

/-- The exact authority receipt is an account of funded runs: the word of
the emitted events, with identities, causes and located contributions, in
runtime emission order. -/
def authorityAccount :
    RunAccount FundedState (FreeMonoid (EmittedEvent Nat String RawCostName)) where
  of path := FreeMonoid.ofList (CostPath.authorityReceipt path)
  of_id _ := rfl
  of_comp first second := by
    change FreeMonoid.ofList
        (CostPath.authorityReceipt (CostPath.append first second)) = _
    rw [CostPath.authorityReceipt_append]
    rfl

/-- The spend total is the authority receipt, aggregated. -/
theorem spendAccount_eq_authorityAccount_map :
    spendAccount = authorityAccount.map ReceiptEmission.aggregateMonoidHom := by
  refine RunAccount.ext ?_
  funext source target transition
  change Multiplicative.ofAdd (CostPath.rawAccount transition) =
    Multiplicative.ofAdd (CostPath.authorityReceipt transition).aggregate
  rw [CostPath.rawAccount_eq_authorityReceipt_aggregate]

/-- The number of firings is the authority receipt, counted. -/
theorem firingAccount_eq_authorityAccount_map :
    firingAccount = authorityAccount.map ReceiptEmission.countMonoidHom := by
  refine RunAccount.ext ?_
  funext source target transition
  change Multiplicative.ofAdd (CostPath.depth transition) =
    Multiplicative.ofAdd (CostPath.emission transition).length
  rw [CostPath.emission_length_eq_depth]

/-- Exact authority receipts form a functor out of funded resource-state
transitions.  The opposite monoid compensates for the conventional order of
composition in a one-object category, while the underlying receipt remains in
runtime emission order. -/
def authorityReceiptFunctor :
    FundedState ⥤
      SingleObj
        (MulOpposite (FreeMonoid (EmittedEvent Nat String RawCostName))) :=
  authorityAccount.toFunctor

/-- The existing raw-account functor is the lossy monoidal observation of the
exact authority-receipt functor, on every funded transition. -/
theorem rawAccountFunctor_map_factors_through_authorityReceipt
    {source target : FundedState} (transition : source ⟶ target) :
    rawAccountFunctor.map transition =
      (authorityReceiptFunctor ⋙
        (ReceiptEmission.aggregateOppositeMonoidHom
          (EventId := Nat) (Ground := String) (Location := RawCostName)).toFunctor).map
        transition := by
  change Multiplicative.ofAdd transition.rawAccount =
    Multiplicative.ofAdd transition.authorityReceipt.aggregate
  rw [CostPath.rawAccount_eq_authorityReceipt_aggregate]

end ResourceTransition

namespace FundedExecution

/-- Authority evidence returned with a parameterized computation. -/
def authorityReceipt
    (execution : FundedExecution source target Result) :
    ReceiptEmission Nat String RawCostName :=
  execution.transition.authorityReceipt

@[simp]
theorem pure_authorityReceipt (state : FundedState) (result : Result) :
    authorityReceipt (Mettapedia.Effects.Execution.pure state result) = [] :=
  rfl

/-- Parameterized bind concatenates authority evidence before any pricing
observation is taken. -/
@[simp]
theorem bind_authorityReceipt {source middle target : FundedState}
    (first : FundedExecution source middle Result)
    (next : Result → FundedExecution middle target NextResult) :
    authorityReceipt (first.bind next) =
      first.authorityReceipt ++ (next first.result).authorityReceipt :=
  CostPath.authorityReceipt_append first.transition
    (next first.result).transition

/-- A computation's raw price input is determined by its authority receipt. -/
theorem rawAccount_eq_authorityReceipt_aggregate
    (execution : FundedExecution source target Result) :
    execution.transition.rawAccount = execution.authorityReceipt.aggregate :=
  CostPath.rawAccount_eq_authorityReceipt_aggregate execution.transition

end FundedExecution

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
