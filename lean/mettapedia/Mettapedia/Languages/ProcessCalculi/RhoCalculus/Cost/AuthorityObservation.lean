import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ResourceTransition
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Authority receipts and lossy pricing observations

Exact funded transitions retain event identities, causal predecessors, and
occurrence-level funding contributions in their canonical receipt.  Raw
signature totals and numerical valuations are derived from that receipt.

The direction is deliberate: authority evidence determines pricing data;
pricing data is not used to reconstruct authority evidence.
-/

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

/-- Aggregation is a monoid homomorphism from ordered receipts, viewed in the
opposite monoid to match categorical composition, to commutative raw spend.
The homomorphism is intentionally not asserted to be injective. -/
def aggregateOppositeMonoidHom :
    MulOpposite (FreeMonoid (EmittedEvent EventId Ground Location)) →*
      Multiplicative (CostSig Ground) where
  toFun receipt :=
    Multiplicative.ofAdd (aggregate (FreeMonoid.toList receipt.unop))
  map_one' := by
    rfl
  map_mul' first second := by
    simp [FreeMonoid.toList_mul, aggregate_append, add_comm]

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

open CategoryTheory

/-- Exact authority receipts form a functor out of funded resource-state
transitions.  The opposite monoid compensates for the conventional order of
composition in a one-object category, while the underlying receipt remains in
runtime emission order. -/
def authorityReceiptFunctor :
    FundedState ⥤
      SingleObj
        (MulOpposite (FreeMonoid (EmittedEvent Nat String RawCostName))) where
  obj _ := SingleObj.star _
  map path := MulOpposite.op (FreeMonoid.ofList path.authorityReceipt)
  map_id state := by
    apply MulOpposite.unop_injective
    change FreeMonoid.ofList (CostPath.emission (𝟙 state)) = 1
    rw [ResourceTransition.identity_emission]
    rfl
  map_comp first second := by
    change MulOpposite.op
        (FreeMonoid.ofList
          (CostPath.authorityReceipt (CostPath.append first second))) =
      MulOpposite.op (FreeMonoid.ofList second.authorityReceipt) *
        MulOpposite.op (FreeMonoid.ofList first.authorityReceipt)
    rw [CostPath.authorityReceipt_append]
    rfl

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
    (pure state result).authorityReceipt = [] :=
  rfl

/-- Parameterized bind concatenates authority evidence before any pricing
observation is taken. -/
@[simp]
theorem bind_authorityReceipt {source middle target : FundedState}
    (first : FundedExecution source middle Result)
    (next : Result → FundedExecution middle target NextResult) :
    (first.bind next).authorityReceipt =
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
