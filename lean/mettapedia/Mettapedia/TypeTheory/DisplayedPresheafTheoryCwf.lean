import Mettapedia.TypeTheory.DisplayedPresheafCwf
import Mettapedia.TypeTheory.DisplayedPresheafTheoryRestriction
import Mettapedia.GSLT.Core.ContextualPseudoCwfMorphism

/-!
# Theory restriction as a structured native CwF morphism

An arbitrary functor of syntax categories acts by actual precomposition on
presheaf contexts, displayed evidence families and their sections. This
constructs the family-valued natural action and verifies preservation of
the chosen terminal context, comprehension, projections and generic variables.
The strict morphism consequently supplies the existing coherent pseudo-CwF
action, rather than independently assuming its preservation fields.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafTheoryCwf

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafCwf DisplayedPresheafTheoryRestriction

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]

/-- Expose the existing display-map category at the concrete native CwF;
the operations are exactly the generic TypeOver operations. -/
instance nativeTypeCategory (P : Cᵒᵖ ⥤ Type u) :
    Category.{u} (TypeOver (presheafCwf.{u, u, u} C) P) :=
  TypeOver.instCategory (C := presheafCwf.{u, u, u} C) (Γ := P)

instance nativeTerminalTypeCategory (P : Cᵒᵖ ⥤ Type u) :
    Category.{u} (TypeOver (presheafCwfWithTerminal.{u, u, u} C).toCwf P) :=
  TypeOver.instCategory (C := (presheafCwfWithTerminal.{u, u, u} C).toCwf) (Γ := P)

/-- The context map uses the supplied theory functor on every contextual
object and every natural substitution component. -/
def contextFunctor (F : C ⥤ D) :
    (presheafCwf.{u, u, u} D).base.Context ⥤
      (presheafCwf.{u, u, u} C).base.Context where
  obj context := ⟨F.op ⋙ context.val⟩
  map substitution := Functor.whiskerLeft F.op substitution
  map_id := by intro context; rfl
  map_comp := by intro source middle target first second; rfl

/-- Both evidence families and their supplied sections are translated. -/
def familyMorphism (F : C ⥤ D) :
    CwfFamilyMorphism (presheafCwf.{u, u, u} D) (presheafCwf.{u, u, u} C) where
  base := contextFunctor F
  family := {
    app := fun context => {
      onIndex := restrictFamily F context.unop.val
      onFibre := restrictTerm F context.unop.val }
    naturality := by
      intro source target substitution
      apply IndexedFamily.Hom.ext
      · rfl
      · intro family term; rfl }

@[simp] theorem familyMorphism_type (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) : (familyMorphism F).mapType A = restrictFamily F P A := rfl

@[simp] theorem familyMorphism_term (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (term : A.sections) :
    (familyMorphism F).mapTerm term = restrictTerm F P A term := rfl

@[simp] theorem familyMorphism_identity_type (P : Cᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) : (familyMorphism (𝟭 C)).mapType A = A := rfl

@[simp] theorem familyMorphism_identity_term (P : Cᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (term : A.sections) :
    (familyMorphism (𝟭 C)).mapTerm term = term := rfl

theorem familyMorphism_composite_type {E : Type u} [Category.{u} E]
    (F : C ⥤ D) (G : D ⥤ E) (P : Eᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    (familyMorphism (F ⋙ G)).mapType A =
      (familyMorphism F).mapType ((familyMorphism G).mapType A) := rfl

theorem familyMorphism_composite_term {E : Type u} [Category.{u} E]
    (F : C ⥤ D) (G : D ⥤ E) (P : Eᵒᵖ ⥤ Type u) (A : DisplayedFamily P)
    (term : A.sections) :
    (familyMorphism (F ⋙ G)).mapTerm term =
      (familyMorphism F).mapTerm ((familyMorphism G).mapTerm term) := rfl

/-- The displayed total context is preserved including its arrow action. -/
theorem total_restriction (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    F.op ⋙ totalSpace A = totalSpace (restrictFamily F P A) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro source target arrow
  apply heq_of_eq
  apply ConcreteCategory.hom_ext
  intro receipt
  rfl

/-- Theory restriction is a strict CwF morphism for the chosen displayed
presheaf comprehension structure and chosen constant terminal context. -/
def strictMorphism (F : C ⥤ D) :
    StrictCwfMorphism (presheafCwfWithTerminal.{u, u, u} D)
      (presheafCwfWithTerminal.{u, u, u} C) where
  toFamilyMorphism := familyMorphism F
  empty_preserved := by rfl
  extension_preserved := by
    intro context family
    apply congrArg ContextualBase.Context.mk
    exact total_restriction F context family
  projection_preserved := by
    intro context family
    rfl
  variable_preserved := by
    intro context family
    rfl

/-- The selected empty-context substitution is preserved as well as its
terminal object. -/
theorem terminal_substitution (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) :
    Functor.whiskerLeft F.op ((presheafCwfWithTerminal D).toEmpty P) =
      (presheafCwfWithTerminal C).toEmpty (F.op ⋙ P) := rfl

/-- Both coordinates of the chosen extension substitution commute with
the supplied theory restriction, at every contextual point. -/
theorem extension_substitution (F : C ⥤ D) {P Q : Dᵒᵖ ⥤ Type u}
    (substitution : Q ⟶ P) (A : DisplayedFamily P) :
    Functor.whiskerLeft F.op
        (TypeOver.extensionSubstitution (C := presheafCwf D) substitution A) =
      TypeOver.extensionSubstitution (C := presheafCwf C)
        (Functor.whiskerLeft F.op substitution) (restrictFamily F P A) := rfl

/-- The strict comprehension comparison is the already constructed
displayed-total comparison, including its actual component maps. -/
theorem comprehension_comparison (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) :
    ((strictMorphism F).comprehensionIso P A).inv = (totalComparison F P A).hom := rfl

/-- The coherent pseudo action is the canonical one induced by the
constructed strict morphism, with its existing substitution comparisons. -/
def pseudoMorphism (F : C ⥤ D) :
    PseudoCwfMorphism (presheafCwfWithTerminal.{u, u, u} D)
      (presheafCwfWithTerminal.{u, u, u} C) :=
  (strictMorphism F).toPseudo

@[simp] theorem pseudoMorphism_type (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) : (pseudoMorphism F).mapType A = restrictFamily F P A :=
  StrictCwfMorphism.toPseudo_mapType (strictMorphism F) A

end Mettapedia.TypeTheory.DisplayedPresheafTheoryCwf
