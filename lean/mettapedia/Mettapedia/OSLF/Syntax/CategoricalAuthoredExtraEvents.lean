import Mettapedia.OSLF.Syntax.CategoricalAuthoredOperationalModels

/-!
# Boundary example: ordinary interpretations may add firing events

For a presentation with no operational rules, an interpretation may add a
new event at an existing endpoint pair. The inclusion preserves the whole
authored model, yet is not event-surjective. The collapse map preserves the
same structure, yet is not event-injective. Coverage and injectivity must
therefore be separate qualifications, not requirements on every model map.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalAuthoredExtraEvents

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.CategoricalAuthoredRuleInterpretation
open Mettapedia.OSLF.Binding.CategoricalAuthoredProgramCarrierMaps
open Mettapedia.OSLF.Binding.CategoricalAuthoredOperationalModels
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u
variable {S : Signature} {schema : List (MetaArity S)}
variable {equations : EquationPresentation S schema}

/-- Add one distinct firing with exactly the endpoints of an existing one.
There are no rules whose actions would need extension to the new input. -/
def withExtraEvent
    (X : PresentedModel (D := Type u) equations [])
    (seed : X.event) : PresentedModel (D := Type u) equations [] where
  base := X.base
  satisfies := X.satisfies
  event := X.event ⊕ PUnit.{u+1}
  endpoints := _root_.TypeCat.ofHom fun
    | Sum.inl original => X.endpoints original
    | Sum.inr _ => X.endpoints seed
  action index := Fin.elim0 index

/-- An ordinary model map can include the old event evidence while leaving
one lawful target event uncovered. -/
noncomputable def extraInclusion
    (X : PresentedModel (D := Type u) equations [])
    (seed : X.event) :
    PresentedModel.Hom X (withExtraEvent X seed) where
  base := ModelWithPrograms.Hom.id X.base
  event := _root_.TypeCat.ofHom Sum.inl
  endpoints_comm := by
    dsimp only [withExtraEvent]
    rw [ModelWithPrograms.Hom.endpointMap_id]
    simp only [Category.comp_id]
    apply _root_.TypeCat.Hom.ext
    rfl
  premiseMap index := Fin.elim0 index
  conclusion_comm index := Fin.elim0 index
  action_comm index := Fin.elim0 index

/-- This interpretation preserves every authored operation but does not
cover the extra target firing. -/
theorem extraInclusion_not_surjective
    (X : PresentedModel (D := Type u) equations [])
    (seed : X.event) :
    ¬ Function.Surjective (extraInclusion X seed).event := by
  intro covers
  obtain ⟨source, impossible⟩ := covers (Sum.inr PUnit.unit)
  cases impossible

/-- A lawful map may also identify two different firing witnesses that
produce the same endpoint pair. -/
noncomputable def extraCollapse
    (X : PresentedModel (D := Type u) equations [])
    (seed : X.event) :
    PresentedModel.Hom (withExtraEvent X seed) X where
  base := ModelWithPrograms.Hom.id X.base
  event := _root_.TypeCat.ofHom
    (Sum.elim id (fun _ => seed))
  endpoints_comm := by
    dsimp only [withExtraEvent]
    rw [ModelWithPrograms.Hom.endpointMap_id]
    simp only [Category.comp_id]
    apply _root_.TypeCat.Hom.ext
    apply _root_.TypeCat.Fun.ext
    funext event
    cases event <;> rfl
  premiseMap index := Fin.elim0 index
  conclusion_comm index := Fin.elim0 index
  action_comm index := Fin.elim0 index

theorem extraCollapse_not_injective
    (X : PresentedModel (D := Type u) equations [])
    (seed : X.event) :
    ¬ Function.Injective (extraCollapse X seed).event := by
  intro injective
  have impossible := injective (a₁ := Sum.inl seed)
    (a₂ := Sum.inr PUnit.unit) rfl
  cases impossible

end Mettapedia.OSLF.Binding.CategoricalAuthoredExtraEvents
