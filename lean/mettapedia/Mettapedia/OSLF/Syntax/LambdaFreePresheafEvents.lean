import Mettapedia.OSLF.Syntax.LambdaDerivationGraph
import Mathlib.CategoryTheory.Subfunctor.Subobject

/-!
# Free adjoining of the Chapter 7 lambda derivation events

The four-rule lambda derivation graph is a concrete generator for the
existing free graph extension over a fixed presheaf of programs. Its universal
property retains each proof-relevant firing. Erasing that event identity gives
exactly the least contextual reduction subobject, at every context.

This is the free event-graph layer, not a free finite-limit cartesian-closed
classifying category for the full lambda presentation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaFreePresheafEvents

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaCategoricalModel
open Mettapedia.OSLF.Binding.LambdaReductionSubobject
open Mettapedia.OSLF.Binding.LambdaDerivationGraph
open Mettapedia.OSLF.Binding.FreePresheafEventExtension
open Mettapedia.OSLF.Binding.BinderLocalPremise

/-- Freely adjoining the four source rule events is left adjoint to forgetting
their chosen interpretation in a graph over the same program presheaf. -/
def eventAdjunction : free graph ⊣ forget graph :=
  freeAdjunction graph

/-- The graph generated from no prior events is initial among graph models
equipped with interpretations of the four source rule constructors. -/
def freelyGeneratedInitial :
    IsInitial (freeObject graph (emptyGraph Programs)) :=
  freeGeneratedIsInitial graph

/-- The free graph contains a transported copy of every original lambda
derivation. This map remembers the entire event tree. -/
def generatorInclusion :
    graph ⟶ (freeObject graph (emptyGraph Programs)).graph :=
  graphInr (emptyGraph Programs) graph

/-- Forget the newly adjoined event's derivation tree while retaining its
point in the least contextual reduction subfunctor. -/
def freeIncidence :
    (freeObject graph (emptyGraph Programs)).graph.edge ⟶
      reduction.toFunctor where
  app X := TypeCat.ofHom (fun
    | .inl old => old.elim
    | .inr authored => incidence.app X authored)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro event
    cases event with
    | inl old => exact old.elim
    | inr authored =>
        exact congrArg
          (fun morphism : eventPresheaf.obj X ⟶ reduction.toFunctor.obj Y =>
            morphism authored)
          (incidence.naturality f)

/-- Every member of the least reduction relation has a source event in the
freely generated graph. -/
theorem freeIncidence_surjective (X : Base) :
    Function.Surjective (freeIncidence.app X) := by
  intro pair
  obtain ⟨event, equal⟩ := incidence_surjective X pair
  exact ⟨Sum.inr event, equal⟩

/-- The endpoint map of the freely adjoined graph is natural. -/
def freeEndpoints :
    (freeObject graph (emptyGraph Programs)).graph.edge ⟶
      rootPairsPresheaf sig :=
  freeIncidence ≫ reduction.ι

/-- The factorization above really pairs the source and target maps of the
freely generated graph; no independent endpoint interpretation is inserted. -/
theorem freeEndpoints_agrees_graph (X : Base)
    (event : (freeObject graph (emptyGraph Programs)).graph.edge.obj X) :
    freeEndpoints.app X event =
      (⟨Srt.term,
        (freeObject graph (emptyGraph Programs)).graph.source.app X event,
        (freeObject graph (emptyGraph Programs)).graph.target.app X event⟩ :
        rootPairs sig X.unop.vars) := by
  cases event with
  | inl old => exact old.elim
  | inr authored => rfl

/-- The image of free-event endpoints is the exact least relation generated
by beta and its three contextual congruence rules. -/
theorem freeEndpoints_range :
    Subfunctor.range freeEndpoints = reduction := by
  ext X pair
  constructor
  · rintro ⟨event, equal⟩
    rw [← equal]
    exact (freeIncidence.app X event).property
  · intro membership
    obtain ⟨event, equal⟩ :=
      freeIncidence_surjective X ⟨pair, membership⟩
    exact ⟨event, congrArg Subtype.val equal⟩

/-- Under the subfunctor/subobject correspondence, the endpoint image is
precisely the categorical reduction subobject. -/
theorem freeEndpoints_subobjectImage :
    Subfunctor.orderIsoSubobject (rootPairsPresheaf sig)
      (Subfunctor.range freeEndpoints) = categoricalSubobject := by
  rw [freeEndpoints_range]
  rfl

/-- Two distinct source derivations with one endpoint pair remain distinct
when freely adjoined; the free construction does not quotient their identity. -/
theorem omega_tickets_remain_distinct :
    (Sum.inr leftOmegaEvent :
      (freeObject graph (emptyGraph Programs)).graph.edge.obj
        (Opposite.op ⟨([] : Ctx sig)⟩)) ≠
      Sum.inr rightOmegaEvent := by
  intro equal
  exact omega_events_distinct (Sum.inr.inj equal)

/-- Those distinct free events still have the same endpoint image. -/
theorem omega_tickets_same_endpoints :
    freeEndpoints.app (Opposite.op ⟨([] : Ctx sig)⟩)
        (Sum.inr leftOmegaEvent) =
      freeEndpoints.app (Opposite.op ⟨([] : Ctx sig)⟩)
        (Sum.inr rightOmegaEvent) := by
  rcases omega_events_same_endpoints with ⟨sourceEq, targetEq⟩
  change (⟨Srt.term, source leftOmegaEvent, target leftOmegaEvent⟩ :
      rootPairs sig []) =
    ⟨Srt.term, source rightOmegaEvent, target rightOmegaEvent⟩
  exact congrArg
    (fun p : Term sig [] .term × Term sig [] .term =>
      (⟨Srt.term, p⟩ : rootPairs sig []))
    (Prod.ext sourceEq targetEq)

/-- The free graph's endpoint map is not monic. The source's relation
subobject is its image, rather than this proof-relevant event object. -/
theorem freeEndpoints_not_mono : ¬ Mono freeEndpoints := by
  intro mono
  let X : Base := Opposite.op ⟨([] : Ctx sig)⟩
  have componentMono : Mono (freeEndpoints.app X) :=
    (NatTrans.mono_iff_mono_app (f := freeEndpoints)).mp mono X
  have injective : Function.Injective (freeEndpoints.app X) :=
    (mono_iff_injective _).mp componentMono
  exact omega_tickets_remain_distinct
    (injective omega_tickets_same_endpoints)

end Mettapedia.OSLF.Binding.LambdaFreePresheafEvents
