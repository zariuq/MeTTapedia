import Mettapedia.OSLF.Syntax.SecondOrderOperationalPresheaf
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalModelPresheaf
import Mettapedia.OSLF.Syntax.FreePresheafEventImage
import Mettapedia.OSLF.Syntax.PresheafEventGraphTransport

/-!
# Individual operational events over equation-class contexts

At a selected program sort, an operational model supplies a state set and a
set of individual closed firing trees with source and target in that state
set. Both are functorial in model maps. Applying these functors to the
authored operational presheaf yields event and state presheaves on the
equation-class context category; the endpoint maps remain natural.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.Binding.FreePresheafEventExtension
open Mettapedia.OSLF.Binding.FreePresheafEventImage

variable {S : Signature} {M : List (MetaArity S)}
variable (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M))
variable (equations : List (EqAxiom S M)) (sort : S.Srt)

/-- Individual closed firing evidence, including both endpoint values and
the complete ordered rule-constructor tree. -/
abbrev ClosedEvent (model : SubstitutionOperationalModel rules equations) : Type :=
  Σ endpoints : model.base.algebra.substitution.Carrier [] sort ×
      model.base.algebra.substitution.Carrier [] sort,
    model.model.evidence.carrier () ⟨[], sort, endpoints⟩

/-- One chosen sort of program states, functorial under every lawful model
map. -/
def statesOfSort : SubstitutionOperationalModel rules equations ⥤ Type where
  obj model := model.base.algebra.substitution.Carrier [] sort
  map interpretation := TypeCat.ofHom interpretation.base.raw.map
  map_id model := by
    apply ConcreteCategory.hom_ext
    intro term
    rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro term
    rfl

/-- The complete individual closed firing trees are functorial. A model map
transports its proof tree and both endpoints together. -/
def eventsOfSort : SubstitutionOperationalModel rules equations ⥤ Type where
  obj model := ClosedEvent rules equations sort model
  map interpretation := TypeCat.ofHom fun event =>
    ⟨(interpretation.base.raw.map event.1.1,
        interpretation.base.raw.map event.1.2),
      interpretation.evidence.toFun ()
        (⟨[], sort, event.1⟩ : Judgment _) event.2⟩
  map_id model := by
    apply ConcreteCategory.hom_ext
    intro event
    cases event
    rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro event
    cases event
    rfl

/-- Every retained event has a natural source endpoint. -/
def eventSource : eventsOfSort rules equations sort ⟶
    statesOfSort rules equations sort where
  app model := TypeCat.ofHom (fun event => event.1.1)
  naturality first second interpretation := by
    apply ConcreteCategory.hom_ext
    intro event
    rfl

/-- Every retained event has a natural target endpoint. -/
def eventTarget : eventsOfSort rules equations sort ⟶
    statesOfSort rules equations sort where
  app model := TypeCat.ofHom (fun event => event.1.2)
  naturality first second interpretation := by
    apply ConcreteCategory.hom_ext
    intro event
    rfl

/-- Authored equation contexts carry the state presheaf at the selected
sort. Its values are contextual term classes modulo authored equations. -/
noncomputable def authoredStates (S : Signature)
    {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (sort : S.Srt) :
    (EquationContexts (authoredEquationPresentation S equations))ᵒᵖ ⥤ Type :=
  authoredQuotientOperationalPresheaf S equations rules ⋙
    statesOfSort rules equations sort

/-- Authored equation contexts carry the individual firing-event presheaf.
The event set is retained even when several firings share endpoints. -/
noncomputable def authoredEvents (S : Signature)
    {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (sort : S.Srt) :
    (EquationContexts (authoredEquationPresentation S equations))ᵒᵖ ⥤ Type :=
  authoredQuotientOperationalPresheaf S equations rules ⋙
    eventsOfSort rules equations sort

/-- The event source is a natural transformation over the authored
equation-class context category. -/
noncomputable def authoredEventSource (S : Signature)
    {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (sort : S.Srt) :
    authoredEvents S equations rules sort ⟶
      authoredStates S equations rules sort :=
  Functor.whiskerLeft (authoredQuotientOperationalPresheaf S equations rules)
    (eventSource rules equations sort)

/-- The event target is natural over the same equation-class contexts. -/
noncomputable def authoredEventTarget (S : Signature)
    {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (sort : S.Srt) :
    authoredEvents S equations rules sort ⟶
      authoredStates S equations rules sort :=
  Functor.whiskerLeft (authoredQuotientOperationalPresheaf S equations rules)
    (eventTarget rules equations sort)

/-- A closed program of the selected sort is represented by one contextual
metavariable of empty dependency arity in the authored equation category. -/
def authoredProgramObject (S : Signature)
    {M : List (MetaArity S)}
    (equations : List (EqAxiom S M)) (sort : S.Srt) :
    EquationContexts (authoredEquationPresentation S equations) :=
  (authoredEquationPresentation S equations).quotientFunctor.obj
    (single S [] sort)

/-- The state presheaf is the Yoneda representation of the authored program
object. The comparison is natural under equation-class contextual maps, so
the event endpoints above land in the actual classifier's program object. -/
noncomputable def authoredStatesRepresentedIso (S : Signature)
    {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (sort : S.Srt) :
    yoneda.obj (authoredProgramObject S equations sort) ≅
      authoredStates S equations rules sort := by
  let P := authoredEquationPresentation S equations
  refine NatIso.ofComponents
    (fun context => (equationTermsRepresented P context.unop.as [] sort).toIso)
    ?_
  intro first last assignment
  apply ConcreteCategory.hom_ext
  intro term
  cases assignment with
  | op assignment =>
    induction assignment using Quot.ind with
    | _ rawAssignment =>
        induction term using Quot.ind with
        | _ rawTerm =>
            convert equationTermsRepresented_comp P rawAssignment [] sort rawTerm using 1
            all_goals
              dsimp [authoredStates, authoredQuotientOperationalPresheaf,
                authoredEquationQuotientModelPresheaf,
                freeSubstitutionOperationalFunctor, statesOfSort,
                authoredEquationModelMapQuot, authoredEquationModelMap,
                SubstitutionOperationalModel.lift, authoredProgramObject,
                yoneda, P]
              rfl

/-- The actual authored rule trees form a graph over the equation-class
program states. No two rule occurrences are identified by this construction. -/
noncomputable def authoredEventGraph (S : Signature)
    {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (sort : S.Srt) : Graph (authoredStates S equations rules sort) where
  edge := authoredEvents S equations rules sort
  source := authoredEventSource S equations rules sort
  target := authoredEventTarget S equations rules sort

/-- The same event graph over the represented program object. This is the
incidence map that the operational classifier must preserve. -/
noncomputable def authoredRepresentedEventGraph (S : Signature)
    {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (sort : S.Srt) :
    Graph (yoneda.obj (authoredProgramObject S equations sort)) :=
  Mettapedia.OSLF.Binding.PresheafEventGraphTransport.changeVertex
    (authoredStatesRepresentedIso S equations rules sort).symm
    (authoredEventGraph S equations rules sort)

/-- The endpoint observation is formed only after retaining the event graph.
The pointwise image exists in this presheaf target. -/
noncomputable def authoredReduction (S : Signature)
    {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (sort : S.Srt) :
    Subfunctor (FunctorToTypes.prod
      (authoredStates S equations rules sort)
      (authoredStates S equations rules sort)) :=
  endpointImage (authoredEventGraph S equations rules sort)

/-- A reduction observation at a context is exactly the existence of a
firing event with those endpoints; the event itself remains in the graph. -/
theorem authoredReduction_iff (S : Signature)
    {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (sort : S.Srt)
    (context : (EquationContexts
      (authoredEquationPresentation S equations))ᵒᵖ)
    (source target : (authoredStates S equations rules sort).obj context) :
    (source, target) ∈
      (authoredReduction S equations rules sort).obj context ↔
    ∃ event : (authoredEvents S equations rules sort).obj context,
      (authoredEventSource S equations rules sort).app context event = source ∧
      (authoredEventTarget S equations rules sort).app context event = target :=
  mem_endpointImage_iff (authoredEventGraph S equations rules sort)
    context (source, target)

/-- The endpoint image of the authored graph is precisely the least
rule-generated one-step relation on the quotient binding clone. -/
theorem authoredReduction_iff_reduces (S : Signature)
    {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (sort : S.Srt)
    (context : (EquationContexts
      (authoredEquationPresentation S equations))ᵒᵖ)
    (source target : (authoredStates S equations rules sort).obj context) :
    (source, target) ∈
      (authoredReduction S equations rules sort).obj context ↔
    Reduces rules (A := (authoredEquationModelAt S equations context.unop.as).algebra)
      (⟨[], sort, (source, target)⟩ : Judgment _) := by
  rw [authoredReduction_iff]
  constructor
  · rintro ⟨⟨⟨before, after⟩, tree⟩, sameSource, sameTarget⟩
    change before = source at sameSource
    change after = target at sameTarget
    subst before
    subst after
    exact ⟨tree⟩
  · rintro ⟨tree⟩
    exact ⟨⟨(source, target), tree⟩, rfl, rfl⟩

end Mettapedia.OSLF.Binding.SecondOrderContext

#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredEvents
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredEventSource
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredEventTarget
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredStatesRepresentedIso
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredRepresentedEventGraph
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredReduction_iff
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredReduction_iff_reduces
