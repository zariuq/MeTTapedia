import Mettapedia.OSLF.Syntax.CategoricalAuthoredRuleInterpretation
import Mettapedia.OSLF.Syntax.CategoricalBindingInterpretationMaps
import Mettapedia.OSLF.Syntax.CategoricalScopedEventBaseChange

/-!
# Binding interpretations with a common program carrier

An authored multisorted language needs a distinguished program object to
compare the endpoints of rules at different sorts. This module makes its
maps part of the varying-base interpretation category. The map on each
sort commutes with its embedding into programs; it need not be injective.
The contextual event-function transport required by conditional premises is
independent additional operational data.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalAuthoredProgramCarrierMaps

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.CategoricalAuthoredRuleInterpretation

universe u v
variable {S : Signature} {schema : List (MetaArity S)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

/-- A binding model and a program object observing all of its authored
sorts. Equations and operational rule actions are imposed in later layers. -/
structure ModelWithPrograms (S : Signature) (D : Type u)
    [Category.{v} D] [CartesianMonoidalCategory D] where
  binding : Model S D
  carrier : ProgramCarrier binding

namespace ModelWithPrograms

variable {X Y Z : ModelWithPrograms S D}

/-- A varying-base map preserves every contextual binding assignment and
commutes with embedding each sort into the common program carrier. -/
structure Hom (X Y : ModelWithPrograms S D) where
  binding : CategoricalBindingInterpretationMaps.Hom X.binding Y.binding
  program : X.carrier.program ⟶ Y.carrier.program
  sort_comm : ∀ sort : S.Srt,
    binding.underlying.sort sort ≫ Y.carrier.embedSort sort =
      X.carrier.embedSort sort ≫ program

/-- The induced map of source-target program pairs. -/
def Hom.endpointMap (f : Hom X Y) :
    EndpointPairs X.binding X.carrier ⟶
      EndpointPairs Y.binding Y.carrier :=
  f.program ⊗ₘ f.program

/-- Context variables and metavariable assignments move together under a
binding interpretation map. -/
def Hom.parameterMap (f : Hom X Y) (Γ : Ctx S) :
    Parameters (schema := schema) X.binding Γ ⟶
      Parameters (schema := schema) Y.binding Γ :=
  Model.ctxMap f.binding.underlying.sort Γ ⊗ₘ
    Model.familyMap f.binding.underlying.power schema

@[ext] theorem Hom.ext {f g : Hom X Y}
    (binding : f.binding = g.binding)
    (program : f.program = g.program) : f = g := by
  cases f
  cases g
  cases binding
  cases program
  rfl

def Hom.id (X : ModelWithPrograms S D) : Hom X X where
  binding := CategoricalBindingInterpretationMaps.Hom.id X.binding
  program := 𝟙 X.carrier.program
  sort_comm := by
    intro sort
    simp [CategoricalBindingInterpretationMaps.Hom.id]

def Hom.comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  binding := CategoricalBindingInterpretationMaps.Hom.comp f.binding g.binding
  program := f.program ≫ g.program
  sort_comm := by
    intro sort
    calc
      (f.binding.underlying.sort sort ≫
          g.binding.underlying.sort sort) ≫
          Z.carrier.embedSort sort =
        f.binding.underlying.sort sort ≫
          (g.binding.underlying.sort sort ≫
            Z.carrier.embedSort sort) := Category.assoc _ _ _
      _ = f.binding.underlying.sort sort ≫
            (Y.carrier.embedSort sort ≫ g.program) := by
              rw [g.sort_comm sort]
      _ = (f.binding.underlying.sort sort ≫
            Y.carrier.embedSort sort) ≫ g.program :=
          (Category.assoc _ _ _).symm
      _ = (X.carrier.embedSort sort ≫ f.program) ≫ g.program := by
            rw [f.sort_comm sort]
      _ = X.carrier.embedSort sort ≫ (f.program ≫ g.program) :=
          Category.assoc _ _ _

noncomputable instance : Category (ModelWithPrograms S D) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intro X Y f
    apply Hom.ext
    · apply CategoricalBindingInterpretationMaps.Hom.ext
      exact Category.id_comp f.binding.underlying
    · simp [Hom.comp, Hom.id]
  comp_id := by
    intro X Y f
    apply Hom.ext
    · apply CategoricalBindingInterpretationMaps.Hom.ext
      exact Category.comp_id f.binding.underlying
    · simp [Hom.comp, Hom.id]
  assoc := by
    intro X Y Z W f g h
    apply Hom.ext
    · apply CategoricalBindingInterpretationMaps.Hom.ext
      exact Category.assoc f.binding.underlying
        g.binding.underlying h.binding.underlying
    · exact Category.assoc f.program g.program h.program

theorem Hom.id_comp (f : Hom X Y) : (Hom.id X).comp f = f :=
  Category.id_comp (show X ⟶ Y from f)

theorem Hom.comp_id (f : Hom X Y) : f.comp (Hom.id Y) = f :=
  Category.comp_id (show X ⟶ Y from f)

theorem Hom.comp_assoc (f : Hom X Y) (g : Hom Y Z)
    {W : ModelWithPrograms S D} (h : Hom Z W) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  Category.assoc (show X ⟶ Y from f)
    (show Y ⟶ Z from g) (show Z ⟶ W from h)

theorem Hom.endpointMap_id (X : ModelWithPrograms S D) :
    (Hom.id X).endpointMap = 𝟙 _ := by
  simp [Hom.endpointMap, Hom.id]

theorem Hom.endpointMap_comp (f : Hom X Y) (g : Hom Y Z) :
    (f.comp g).endpointMap = f.endpointMap ≫ g.endpointMap := by
  simp [Hom.endpointMap, Hom.comp, tensorHom_comp_tensorHom]

theorem Hom.parameterMap_id (X : ModelWithPrograms S D)
    (Γ : Ctx S) :
    (Hom.id X).parameterMap (schema := schema) Γ = 𝟙 _ := by
  change Model.ctxMap (fun _ => 𝟙 _) Γ ⊗ₘ
      Model.familyMap (fun _ _ => 𝟙 _) schema = 𝟙 _
  rw [Model.ctxMap_id, Model.familyMap_id, id_tensorHom_id]

theorem Hom.parameterMap_comp (f : Hom X Y) (g : Hom Y Z)
    (Γ : Ctx S) :
    (f.comp g).parameterMap (schema := schema) Γ =
      f.parameterMap (schema := schema) Γ ≫
        g.parameterMap (schema := schema) Γ := by
  change Model.ctxMap
      (fun sort => f.binding.underlying.sort sort ≫
        g.binding.underlying.sort sort) Γ ⊗ₘ
      Model.familyMap
        (fun context sort => f.binding.underlying.power context sort ≫
          g.binding.underlying.power context sort) schema =
      (Model.ctxMap f.binding.underlying.sort Γ ⊗ₘ
        Model.familyMap f.binding.underlying.power schema) ≫
      (Model.ctxMap g.binding.underlying.sort Γ ⊗ₘ
        Model.familyMap g.binding.underlying.power schema)
  rw [Model.ctxMap_comp, Model.familyMap_comp,
    tensorHom_comp_tensorHom]

end ModelWithPrograms

end Mettapedia.OSLF.Binding.CategoricalAuthoredProgramCarrierMaps

#print axioms Mettapedia.OSLF.Binding.CategoricalAuthoredProgramCarrierMaps.ModelWithPrograms.Hom.parameterMap_comp
