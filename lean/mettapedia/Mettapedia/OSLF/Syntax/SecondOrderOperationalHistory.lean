import Mettapedia.OSLF.Syntax.SecondOrderOperationalEventObject
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalModelHistory

/-!
# Authored event histories over equation-class contexts

Each equation-class context has the free path category of its retained
firing trees. A contextual assignment maps whole paths by mapping their
states and each individual firing, preserving the empty history and ordered
composition. This is the history structure associated with the same
operational presheaf that supplies the Chapter 7 event graph.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelHistory

variable (S : Signature) {M : List (MetaArity S)}
variable (equations : List (EqAxiom S M))
variable (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M))
variable (sort : S.Srt)

/-- Free finite histories over the actual individual firings at an authored
equation-class context. Parallel firings remain parallel path generators. -/
noncomputable abbrev authoredHistoryAt
    (context : (EquationContexts
      (authoredEquationPresentation S equations))ᵒᵖ) :=
  HistoryCategory rules
    ((authoredQuotientOperationalPresheaf S equations rules).obj context).model
    [] sort

/-- The event objects of the authored presheaf are precisely the generating
edges of its finite-history category, with endpoints and individual evidence
retained. This is an equivalence of carriers, not a quotient by endpoints. -/
noncomputable def authoredEventEdgeEquiv
    (context : (EquationContexts
      (authoredEquationPresentation S equations))ᵒᵖ) :
    (authoredEvents S equations rules sort).obj context ≃
      Σ source : State rules
          ((authoredQuotientOperationalPresheaf S equations rules).obj context).model
          [] sort,
        Σ target : State rules
            ((authoredQuotientOperationalPresheaf S equations rules).obj context).model
            [] sort,
          source ⟶ target where
  toFun
    | ⟨⟨source, target⟩, event⟩ =>
        ⟨⟨source⟩, ⟨⟨target⟩, event⟩⟩
  invFun
    | ⟨⟨source⟩, ⟨⟨target⟩, event⟩⟩ =>
        ⟨(source, target), event⟩
  left_inv
    | ⟨⟨_, _⟩, _⟩ => rfl
  right_inv
    | ⟨⟨_⟩, ⟨⟨_⟩, _⟩⟩ => rfl

/-- Every authored contextual assignment induces the specified map on
whole ordered firing histories. -/
noncomputable def authoredHistoryContextMap
    {first last : (EquationContexts
      (authoredEquationPresentation S equations))ᵒᵖ}
    (assignment : first ⟶ last) :
    authoredHistoryAt S equations rules sort first ⥤
      authoredHistoryAt S equations rules sort last :=
  relativeMapHistories rules
    ((authoredQuotientOperationalPresheaf S equations rules).map assignment)
    [] sort

/-- On one authored firing, the path map uses precisely the interpretation's
evidence action. The rule occurrence is not reduced to an endpoint pair. -/
theorem authoredHistoryContextMap_generator
    {first last : (EquationContexts
      (authoredEquationPresentation S equations))ᵒᵖ}
    (assignment : first ⟶ last)
    {source target : State rules
      ((authoredQuotientOperationalPresheaf S equations rules).obj first).model
      [] sort}
    (event : source ⟶ target) :
    (authoredHistoryContextMap S equations rules sort assignment).map
      event.toPath =
        Quiver.Hom.toPath
          ((relativeMapGenerators rules
            ((authoredQuotientOperationalPresheaf S equations rules).map assignment)
            [] sort).map event) :=
  relativeMapHistories_generator rules
    ((authoredQuotientOperationalPresheaf S equations rules).map assignment)
    [] sort event

/-- The edge-carrier equivalence commutes with every authored context
assignment. In particular the whole-path action uses the same event map
as the equation-class graph, including the identity of each firing. -/
theorem authoredEventEdgeEquiv_contextMap
    {first last : (EquationContexts
      (authoredEquationPresentation S equations))ᵒᵖ}
    (assignment : first ⟶ last)
    (event : (authoredEvents S equations rules sort).obj first) :
    (authoredEventEdgeEquiv S equations rules sort last)
      ((authoredEvents S equations rules sort).map assignment event) =
    ⟨(relativeMapGenerators rules
        ((authoredQuotientOperationalPresheaf S equations rules).map assignment)
        [] sort).obj
        ((authoredEventEdgeEquiv S equations rules sort first) event).1,
      ⟨(relativeMapGenerators rules
          ((authoredQuotientOperationalPresheaf S equations rules).map assignment)
          [] sort).obj
          ((authoredEventEdgeEquiv S equations rules sort first) event).2.1,
        (relativeMapGenerators rules
          ((authoredQuotientOperationalPresheaf S equations rules).map assignment)
          [] sort).map
          ((authoredEventEdgeEquiv S equations rules sort first) event).2.2⟩⟩ := by
  rcases event with ⟨⟨source, target⟩, evidence⟩
  rfl

/-- The identity context assignment leaves every history unchanged. -/
theorem authoredHistoryContextMap_id
    (context : (EquationContexts
      (authoredEquationPresentation S equations))ᵒᵖ) :
    authoredHistoryContextMap S equations rules sort (𝟙 context) =
      𝟭 (authoredHistoryAt S equations rules sort context) := by
  change relativeMapHistories rules
      ((authoredQuotientOperationalPresheaf S equations rules).map (𝟙 context))
      [] sort = _
  rw [(authoredQuotientOperationalPresheaf S equations rules).map_id context]
  exact relativeMapHistories_id rules
    ((authoredQuotientOperationalPresheaf S equations rules).obj context)
    [] sort

/-- Contextual substitution on finite histories composes strictly, including
the underlying program-state maps and retained firing occurrences. -/
theorem authoredHistoryContextMap_comp
    {first middle last : (EquationContexts
      (authoredEquationPresentation S equations))ᵒᵖ}
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    authoredHistoryContextMap S equations rules sort (earlier ≫ later) =
      authoredHistoryContextMap S equations rules sort earlier ⋙
        authoredHistoryContextMap S equations rules sort later := by
  simp only [authoredHistoryContextMap, Functor.map_comp]
  exact relativeMapHistories_comp rules
    ((authoredQuotientOperationalPresheaf S equations rules).map earlier)
    ((authoredQuotientOperationalPresheaf S equations rules).map later)
    [] sort

end Mettapedia.OSLF.Binding.SecondOrderContext

#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredHistoryContextMap_generator
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredEventEdgeEquiv_contextMap
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredHistoryContextMap_id
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredHistoryContextMap_comp
