import Mettapedia.OSLF.Syntax.ContextualLocatedEvents

/-!
# Equation classes of located operational events

The located event object retains its rule instance and chosen structural
occurrence. Equations act on its endpoints: the term quotient is a presheaf,
and quotienting the two natural endpoint maps gives an internal graph over
equation-class states. At the empty context its endpoint image is exactly the
existing step-modulo-equations relation. An equation changes which states an
event connects, but it creates no new event without a firing witness.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualEquationClassEvents

open CategoryTheory

variable {S : Signature} {M : List (MetaArity S)}

/-- The intrinsically scoped equation-class terms vary over substitutions. -/
def termQPresheaf (equations : List (EqAxiom S M)) (sort : S.Srt) :
    (Syntactic.Ctxt S)ᵒᵖ ⥤ Type where
  obj X := TermQ equations X.unop.vars sort
  map f := TypeCat.ofHom (bindQ (E := equations) f.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro q
    refine Quotient.inductionOn q ?_
    intro t
    exact congrArg (Quotient.mk _) (bind_id t)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro q
    refine Quotient.inductionOn q ?_
    intro t
    exact congrArg (Quotient.mk _) ((bind_comp f.unop g.unop t).symm)

/-- Sending a raw term to its equation class is natural in substitution. -/
def quotientNatural (equations : List (EqAxiom S M)) (sort : S.Srt) :
    Syntactic.termPresheaf S sort ⟶ termQPresheaf equations sort where
  app X := TypeCat.ofHom (fun t => Quotient.mk (eqSetoid equations X.unop.vars sort) t)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro t
    rfl

/-- The source-class map of the retained located-event graph. -/
def sourceNatural (equations : List (EqAxiom S M))
    (rule : UnpositionedRewrite (withMetas S M)) (sort : S.Srt) :
    ContextualLocatedEvents.instancePresheaf rule sort ⟶
      termQPresheaf equations sort :=
  ContextualLocatedEvents.sourceNatural rule sort ≫ quotientNatural equations sort

/-- The target-class map of the same event graph. -/
def targetNatural (equations : List (EqAxiom S M))
    (rule : UnpositionedRewrite (withMetas S M)) (sort : S.Srt) :
    ContextualLocatedEvents.instancePresheaf rule sort ⟶
      termQPresheaf equations sort :=
  ContextualLocatedEvents.targetNatural rule sort ≫ quotientNatural equations sort

/-- At closed contexts, the endpoint image of the class graph is precisely
the original equation-closed contextual-step relation. The occurrence itself
remains part of the edge object, so parallel firings need not be identified. -/
theorem closed_class_endpoints_iff_stepModE
    (equations : List (EqAxiom S M))
    (rule : UnpositionedRewrite (withMetas S M)) (sort : S.Srt)
    (source target : Term S [] sort) :
    (∃ event : ContextualLocatedEvents.Instance rule [] sort,
      (Quotient.mk (eqSetoid equations [] sort) event.source) =
        Quotient.mk (eqSetoid equations [] sort) source ∧
      (Quotient.mk (eqSetoid equations [] sort) event.target) =
        Quotient.mk (eqSetoid equations [] sort) target) ↔
      rule.StepModE equations source target := by
  constructor
  · rintro ⟨event, left, right⟩
    exact ⟨event.source, event.target,
      Quotient.exact left.symm,
      (ContextualLocatedEvents.closed_endpoints_iff_step rule sort
        event.source event.target).mp ⟨event, rfl, rfl⟩,
      Quotient.exact right⟩
  · rintro ⟨source', target', before, step, after⟩
    obtain ⟨event, left, right⟩ :=
      (ContextualLocatedEvents.closed_endpoints_iff_step rule sort
        source' target').mpr step
    refine ⟨event, ?_, ?_⟩
    · rw [left]
      exact Quotient.sound (EqClosure.symm before)
    · rw [right]
      exact Quotient.sound after

/-- A presentation event retains the index of the authored rule that fired. -/
abbrev PresentationInstance (presentation : UnpositionedPresentation S)
    (Γ : Ctx S) (sort : S.Srt) : Type :=
  (i : Fin presentation.rules.length) ×
    ContextualLocatedEvents.Instance (presentation.rules.get i) Γ sort

namespace PresentationInstance

def source {presentation : UnpositionedPresentation S}
    {Γ : Ctx S} {sort : S.Srt}
    (event : PresentationInstance presentation Γ sort) : Term S Γ sort :=
  event.2.source

def target {presentation : UnpositionedPresentation S}
    {Γ : Ctx S} {sort : S.Srt}
    (event : PresentationInstance presentation Γ sort) : Term S Γ sort :=
  event.2.target

def map {presentation : UnpositionedPresentation S}
    {Γ Δ : Ctx S} {sort : S.Srt} (sigma : Sub S Γ Δ)
    (event : PresentationInstance presentation Γ sort) :
    PresentationInstance presentation Δ sort :=
  ⟨event.1, event.2.map sigma⟩

theorem source_map {presentation : UnpositionedPresentation S}
    {Γ Δ : Ctx S} {sort : S.Srt} (sigma : Sub S Γ Δ)
    (event : PresentationInstance presentation Γ sort) :
    (map sigma event).source = bind sigma event.source :=
  ContextualLocatedEvents.Instance.source_map sigma event.2

theorem target_map {presentation : UnpositionedPresentation S}
    {Γ Δ : Ctx S} {sort : S.Srt} (sigma : Sub S Γ Δ)
    (event : PresentationInstance presentation Γ sort) :
    (map sigma event).target = bind sigma event.target :=
  ContextualLocatedEvents.Instance.target_map sigma event.2

theorem map_id {presentation : UnpositionedPresentation S}
    {Γ : Ctx S} {sort : S.Srt}
    (event : PresentationInstance presentation Γ sort) :
    map (fun _ v => .var v) event = event := by
  cases event with
  | mk i firing =>
      simp only [map, ContextualLocatedEvents.Instance.map_id]

theorem map_comp {presentation : UnpositionedPresentation S}
    {Γ Δ Θ : Ctx S} {sort : S.Srt}
    (sigma : Sub S Γ Δ) (tau : Sub S Δ Θ)
    (event : PresentationInstance presentation Γ sort) :
    map tau (map sigma event) =
      map (fun s v => bind tau (sigma s v)) event := by
  cases event with
  | mk i firing =>
      simp only [map, ContextualLocatedEvents.Instance.map_comp]

end PresentationInstance

/-- The event object of an unconditional authored presentation over all
syntactic contexts. Distinct rule occurrences remain distinct edges. -/
def presentationEventPresheaf (presentation : UnpositionedPresentation S)
    (sort : S.Srt) : (Syntactic.Ctxt S)ᵒᵖ ⥤ Type where
  obj X := PresentationInstance presentation X.unop.vars sort
  map f := TypeCat.ofHom (PresentationInstance.map f.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro event
    exact PresentationInstance.map_id event
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro event
    exact (PresentationInstance.map_comp f.unop g.unop event).symm

def presentationSourceNatural (presentation : UnpositionedPresentation S)
    (sort : S.Srt) :
    presentationEventPresheaf presentation sort ⟶
      termQPresheaf presentation.eqs sort where
  app X := TypeCat.ofHom (fun event =>
    Quotient.mk (eqSetoid presentation.eqs X.unop.vars sort) event.source)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro event
    exact congrArg (Quotient.mk _) (PresentationInstance.source_map f.unop event)

def presentationTargetNatural (presentation : UnpositionedPresentation S)
    (sort : S.Srt) :
    presentationEventPresheaf presentation sort ⟶
      termQPresheaf presentation.eqs sort where
  app X := TypeCat.ofHom (fun event =>
    Quotient.mk (eqSetoid presentation.eqs X.unop.vars sort) event.target)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro event
    exact congrArg (Quotient.mk _) (PresentationInstance.target_map f.unop event)

/-- At the closed context, the presentation's class-event endpoint image is
exactly its full union-of-rules step-modulo-equations relation. -/
theorem authored_class_endpoints_iff_stepModE
    (presentation : UnpositionedPresentation S) (sort : S.Srt)
    (source target : Term S [] sort) :
    (∃ event : PresentationInstance presentation [] sort,
      (Quotient.mk (eqSetoid presentation.eqs [] sort) event.source) =
        Quotient.mk (eqSetoid presentation.eqs [] sort) source ∧
      (Quotient.mk (eqSetoid presentation.eqs [] sort) event.target) =
        Quotient.mk (eqSetoid presentation.eqs [] sort) target) ↔
      presentation.StepModE source target := by
  constructor
  · rintro ⟨⟨i, event⟩, left, right⟩
    exact ⟨i, (closed_class_endpoints_iff_stepModE presentation.eqs
      (presentation.rules.get i) sort source target).mp ⟨event, left, right⟩⟩
  · rintro ⟨i, step⟩
    obtain ⟨event, left, right⟩ :=
      (closed_class_endpoints_iff_stepModE presentation.eqs
        (presentation.rules.get i) sort source target).mpr step
    exact ⟨⟨i, event⟩, left, right⟩

/-- Equations alone cannot fabricate an operational event at any context. -/
theorem no_presentation_event_of_empty_rules
    (presentation : UnpositionedPresentation S)
    (empty : presentation.rules = []) (Γ : Ctx S) (sort : S.Srt) :
    ¬ Nonempty (PresentationInstance presentation Γ sort) := by
  rintro ⟨⟨i, _⟩⟩
  have impossible : i.val < 0 := by simpa [empty] using i.isLt
  omega

namespace RhoExample

open Mettapedia.OSLF.Binding.RhoSchema

/-- The actual authored rho communication modulo parallel equations is a
retained class event, even when the source writes input before output. -/
theorem source_order_communication_event :
    ∃ event : PresentationInstance rho.toUnpositioned [] Srt.pr,
      Quotient.mk (eqSetoid rho.toUnpositioned.eqs [] Srt.pr) event.source =
        Quotient.mk (eqSetoid rho.toUnpositioned.eqs [] Srt.pr)
          (parT commInput commOutput) ∧
      Quotient.mk (eqSetoid rho.toUnpositioned.eqs [] Srt.pr) event.target =
        Quotient.mk (eqSetoid rho.toUnpositioned.eqs [] Srt.pr) commTarget :=
  (authored_class_endpoints_iff_stepModE rho.toUnpositioned Srt.pr
    (parT commInput commOutput) commTarget).mpr
      unpositioned_input_output_communicates

end RhoExample

end Mettapedia.OSLF.Binding.ContextualEquationClassEvents
