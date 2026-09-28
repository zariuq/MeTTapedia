import Mettapedia.OSLF.Syntax.ContextualEquationClassEvents
import Mettapedia.OSLF.Syntax.RhoEventMultiplicity
import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# The endpoint image of a contextual operational graph

The authored event presheaf keeps rule identity and a selected linear location.
Its paired endpoint map lands in the product of equation-class term presheaves.
The image is a subfunctor: a pair belongs exactly when an authored event has
those endpoints. This makes the reduction subobject in a concrete presheaf
model without identifying the subobject with the event object itself.

This model is not asserted to be the free finite-limit cartesian-closed
classifying theory of the presentation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualReductionSubobject

open CategoryTheory
open Mettapedia.OSLF.Binding.ContextualEquationClassEvents

variable {S : Signature}

private theorem bindQ_id {M : List (MetaArity S)}
    (equations : List (EqAxiom S M)) {Γ : Ctx S} {sort : S.Srt}
    (q : TermQ equations Γ sort) :
    bindQ (E := equations) (fun _ v => .var v) q = q := by
  refine Quotient.inductionOn q ?_
  intro t
  exact congrArg (Quotient.mk _) (bind_id t)

private theorem bindQ_comp {M : List (MetaArity S)}
    (equations : List (EqAxiom S M)) {Γ Δ Θ : Ctx S} {sort : S.Srt}
    (sigma : Sub S Γ Δ) (tau : Sub S Δ Θ)
    (q : TermQ equations Γ sort) :
    bindQ (E := equations) tau (bindQ (E := equations) sigma q) =
      bindQ (E := equations) (fun s v => bind tau (sigma s v)) q := by
  refine Quotient.inductionOn q ?_
  intro t
  exact congrArg (Quotient.mk _) (bind_comp sigma tau t)

/-- Pairs of equation-class terms vary by substitution in both coordinates. -/
def pairPresheaf (presentation : UnpositionedPresentation S) (sort : S.Srt) :
    (Syntactic.Ctxt S)ᵒᵖ ⥤ Type where
  obj X := TermQ presentation.eqs X.unop.vars sort ×
    TermQ presentation.eqs X.unop.vars sort
  map f := TypeCat.ofHom (fun pair =>
    (bindQ (E := presentation.eqs) f.unop pair.1,
      bindQ (E := presentation.eqs) f.unop pair.2))
  map_id X := by
    apply ConcreteCategory.hom_ext
    rintro ⟨source, target⟩
    exact Prod.ext (bindQ_id presentation.eqs source)
      (bindQ_id presentation.eqs target)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨source, target⟩
    exact Prod.ext
      ((bindQ_comp presentation.eqs f.unop g.unop source).symm)
      ((bindQ_comp presentation.eqs f.unop g.unop target).symm)

/-- The paired endpoint map before taking its image. -/
def endpointsNatural (presentation : UnpositionedPresentation S) (sort : S.Srt) :
    presentationEventPresheaf presentation sort ⟶
      pairPresheaf presentation sort where
  app X := TypeCat.ofHom (fun event =>
    (Quotient.mk (eqSetoid presentation.eqs X.unop.vars sort) event.source,
      Quotient.mk (eqSetoid presentation.eqs X.unop.vars sort) event.target))
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro event
    exact Prod.ext
      (congrArg (Quotient.mk _) (PresentationInstance.source_map f.unop event))
      (congrArg (Quotient.mk _) (PresentationInstance.target_map f.unop event))

/-- An endpoint pair is reducible when it is the image of a retained event. -/
def stepSubfunctor (presentation : UnpositionedPresentation S) (sort : S.Srt) :
    Subfunctor (pairPresheaf presentation sort) where
  obj X := { pair | ∃ event : PresentationInstance presentation X.unop.vars sort,
    Quotient.mk (eqSetoid presentation.eqs X.unop.vars sort) event.source = pair.1 ∧
    Quotient.mk (eqSetoid presentation.eqs X.unop.vars sort) event.target = pair.2 }
  map := by
    intro X Y f pair membership
    obtain ⟨event, source_eq, target_eq⟩ := membership
    refine ⟨PresentationInstance.map f.unop event, ?_, ?_⟩
    · change Quotient.mk (eqSetoid presentation.eqs Y.unop.vars sort)
        (PresentationInstance.map f.unop event).source =
          bindQ (E := presentation.eqs) f.unop pair.1
      rw [PresentationInstance.source_map, ← source_eq]
      rfl
    · change Quotient.mk (eqSetoid presentation.eqs Y.unop.vars sort)
        (PresentationInstance.map f.unop event).target =
          bindQ (E := presentation.eqs) f.unop pair.2
      rw [PresentationInstance.target_map, ← target_eq]
      rfl

/-- A retained event gives a point of the reduction subobject. -/
def incidence (presentation : UnpositionedPresentation S) (sort : S.Srt) :
    presentationEventPresheaf presentation sort ⟶
      (stepSubfunctor presentation sort).toFunctor where
  app X := TypeCat.ofHom (fun event =>
    ⟨(Quotient.mk (eqSetoid presentation.eqs X.unop.vars sort) event.source,
      Quotient.mk (eqSetoid presentation.eqs X.unop.vars sort) event.target),
      ⟨event, rfl, rfl⟩⟩)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro event
    apply Subtype.ext
    exact Prod.ext
      (congrArg (Quotient.mk _) (PresentationInstance.source_map f.unop event))
      (congrArg (Quotient.mk _) (PresentationInstance.target_map f.unop event))

/-- Pointwise, every reducible pair has an authored occurrence above it. -/
theorem incidence_surjective (presentation : UnpositionedPresentation S)
    (sort : S.Srt) (X : (Syntactic.Ctxt S)ᵒᵖ) :
    Function.Surjective ((incidence presentation sort).app X) := by
  rintro ⟨pair, membership⟩
  obtain ⟨event, source_eq, target_eq⟩ := membership
  refine ⟨event, ?_⟩
  apply Subtype.ext
  exact Prod.ext source_eq target_eq

/-- The original endpoint map factors through its reduction subobject. -/
theorem endpoints_factorization (presentation : UnpositionedPresentation S)
    (sort : S.Srt) :
    incidence presentation sort ≫ (stepSubfunctor presentation sort).ι =
      endpointsNatural presentation sort := by
  ext X event
  rfl

/-- The inclusion forgets membership evidence but is injective at each
context; event multiplicity is lost in the preceding incidence map. -/
theorem inclusion_injective (presentation : UnpositionedPresentation S)
    (sort : S.Srt) (X : (Syntactic.Ctxt S)ᵒᵖ) :
    Function.Injective ((stepSubfunctor presentation sort).ι.app X) :=
  Subtype.val_injective

/-- The reduction subfunctor is the least subfunctor containing every
authored endpoint pair. This is the image property in the present presheaf
model; it is not a free classifying-category property. -/
theorem stepSubfunctor_le_iff (presentation : UnpositionedPresentation S)
    (sort : S.Srt) (other : Subfunctor (pairPresheaf presentation sort)) :
    stepSubfunctor presentation sort ≤ other ↔
      ∀ (X : (Syntactic.Ctxt S)ᵒᵖ)
        (event : (presentationEventPresheaf presentation sort).obj X),
        (endpointsNatural presentation sort).app X event ∈ other.obj X := by
  constructor
  · intro included X event
    apply included X
    exact ⟨event, rfl, rfl⟩
  · intro contains X pair membership
    obtain ⟨event, source_eq, target_eq⟩ := membership
    have endpoints_eq :
        (endpointsNatural presentation sort).app X event = pair :=
      Prod.ext source_eq target_eq
    rw [← endpoints_eq]
    exact contains X event

/-- At the empty context, the image-subobject membership is exactly the
authored step relation modulo the authored equations. -/
theorem closed_membership_iff_stepModE
    (presentation : UnpositionedPresentation S) (sort : S.Srt)
    (source target : Term S [] sort) :
    (stepSubfunctor presentation sort).obj
      (Opposite.op (Syntactic.Ctxt.mk ([] : Ctx S)))
      (Quotient.mk (eqSetoid presentation.eqs [] sort) source,
        Quotient.mk (eqSetoid presentation.eqs [] sort) target) ↔
      presentation.StepModE source target := by
  exact authored_class_endpoints_iff_stepModE presentation sort source target

/-- Equations without authored rules give an empty operational image. -/
theorem no_membership_of_empty_rules
    (presentation : UnpositionedPresentation S)
    (empty : presentation.rules = [])
    (X : (Syntactic.Ctxt S)ᵒᵖ) (sort : S.Srt)
    (pair : (pairPresheaf presentation sort).obj X) :
    ¬ (stepSubfunctor presentation sort).obj X pair := by
  rintro ⟨event, _, _⟩
  exact no_presentation_event_of_empty_rules presentation empty X.unop.vars sort
    ⟨event⟩

namespace RhoExample

open Mettapedia.OSLF.Binding.RhoSchema

/-- The authored communication belongs to the image-subobject, including
the parallel equations used to recognize the source order. -/
theorem source_order_communication_member :
    (stepSubfunctor rho.toUnpositioned Srt.pr).obj
      (Opposite.op (Syntactic.Ctxt.mk ([] : Ctx sig)))
      (Quotient.mk (eqSetoid rho.toUnpositioned.eqs [] Srt.pr)
          (parT commInput commOutput),
        Quotient.mk (eqSetoid rho.toUnpositioned.eqs [] Srt.pr) commTarget) :=
  (closed_membership_iff_stepModE rho.toUnpositioned Srt.pr
    (parT commInput commOutput) commTarget).mpr
      unpositioned_input_output_communicates

/-- Two authored copies of COMM retain different rule indices, although the
endpoint-image map identifies their class pairs. -/
theorem duplicated_communication_incidence_not_injective :
    ¬ Function.Injective
      ((incidence duplicatedCommunication Srt.pr).app
        (Opposite.op (Syntactic.Ctxt.mk ([] : Ctx sig)))) := by
  obtain ⟨⟨index, firing⟩, _, _⟩ :=
    ContextualEquationClassEvents.RhoExample.source_order_communication_event
  fin_cases index
  let first : PresentationInstance duplicatedCommunication [] Srt.pr :=
    ⟨⟨0, by decide⟩, firing⟩
  let second : PresentationInstance duplicatedCommunication [] Srt.pr :=
    ⟨⟨1, by decide⟩, firing⟩
  intro injective
  have equal : first = second := injective rfl
  have indices := congrArg Sigma.fst equal
  have impossible : (0 : Fin 2) = 1 := indices
  cases impossible

end RhoExample

end Mettapedia.OSLF.Binding.ContextualReductionSubobject
