import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts

/-!
# Relations between set-coded functions on retained domains

An application can observe two different function sets only at inputs
admitted by their respective retained domains. The relation is indexed by
both domains and by input/output relations; it does not identify functions
whose graphs differ outside the observations being compared.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts

open ZFSetDependentProducts (graph mem_graph)

universe u

/-- Heterogeneous observation of set-coded functions. The domains are part
of the relation, not erased annotations on otherwise equal function sets. -/
def TraceFunctionRelated (leftDomain rightDomain : ZFSet.{u})
    (inputRelation outputRelation : ZFSet.{u} → ZFSet.{u} → Prop)
    (left right : ZFSet.{u}) : Prop :=
  ∀ x ∈ leftDomain, ∀ y ∈ rightDomain, inputRelation x y →
    outputRelation (traceApp left x) (traceApp right y)

/-- For actual traced graphs, the observational condition is exactly the
pointwise relation on admitted inputs. -/
theorem traceFunctionRelated_graph_iff
    (leftDomain rightDomain : ZFSet.{u})
    (inputRelation outputRelation : ZFSet.{u} → ZFSet.{u} → Prop)
    (left right : ZFSet.{u} → ZFSet.{u}) :
    TraceFunctionRelated leftDomain rightDomain inputRelation outputRelation
      (traceLam (graph leftDomain left)) (traceLam (graph rightDomain right)) ↔
    ∀ x ∈ leftDomain, ∀ y ∈ rightDomain,
      inputRelation x y → outputRelation (left x) (right y) := by
  constructor
  · intro related x insideLeft y insideRight inputRelated
    simpa only [traceApp_graph_beta left insideLeft,
      traceApp_graph_beta right insideRight] using
      related x insideLeft y insideRight inputRelated
  · intro related x insideLeft y insideRight inputRelated
    rw [traceApp_graph_beta left insideLeft, traceApp_graph_beta right insideRight]
    exact related x insideLeft y insideRight inputRelated

/-- At one retained domain, equality observations recover equality of the
traced graph values. This does not apply when the domains differ. -/
theorem traceLam_graph_eq_of_related_eq (domain : ZFSet.{u})
    (left right : ZFSet.{u} → ZFSet.{u})
    (related : TraceFunctionRelated domain domain Eq Eq
      (traceLam (graph domain left)) (traceLam (graph domain right))) :
    traceLam (graph domain left) = traceLam (graph domain right) := by
  have pointwise : ∀ x ∈ domain, left x = right x := by
    intro x inside
    exact (traceFunctionRelated_graph_iff domain domain Eq Eq left right).mp
      related x inside x inside rfl
  apply congrArg traceLam
  apply ZFSet.ext
  intro pair
  simp only [mem_graph]
  constructor
  · rintro ⟨x, inside, equal⟩
    exact ⟨x, inside, by rw [← pointwise x inside]; exact equal⟩
  · rintro ⟨x, inside, equal⟩
    exact ⟨x, inside, by rw [pointwise x inside]; exact equal⟩

#print axioms traceFunctionRelated_graph_iff
#print axioms traceLam_graph_eq_of_related_eq

end Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts
