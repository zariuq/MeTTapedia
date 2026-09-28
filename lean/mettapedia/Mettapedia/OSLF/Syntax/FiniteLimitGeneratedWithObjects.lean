import Mettapedia.OSLF.Syntax.FiniteLimitGeneratedYoneda
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Finite-limit closure with selected semantic objects

Represented contexts alone need not contain the state, event, and reduction
objects of an operational language. Given a specified collection of presheaf
objects, this construction closes the representables and those objects under
finite limits. Its universal claim is the minimality of that object property;
it makes no claim of a free hom-set property for model interpretations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.FiniteLimitYoneda

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding

variable (C : Type) [SmallCategory C]

/-- Representables together with explicitly chosen operational objects. -/
def WithObjectsSeed (extra : Set (Presheaf C)) :
    ObjectProperty (Presheaf C) :=
  fun F => (Representable C) F ∨ F ∈ extra

/-- The finite-limit closure of those specified objects. -/
def GeneratedWithObjects (extra : Set (Presheaf C)) :
    ObjectProperty (Presheaf C) :=
  (WithObjectsSeed C extra).limitsClosure finiteLimitDiagram

theorem representedWithObjects (extra : Set (Presheaf C)) (X : C) :
    GeneratedWithObjects C extra (yoneda.obj X) := by
  apply ObjectProperty.limitsClosure.of_mem
  exact Or.inl (by change (yoneda.obj X).IsRepresentable; infer_instance)

theorem extraInGenerated (extra : Set (Presheaf C))
    {F : Presheaf C} (h : F ∈ extra) :
    GeneratedWithObjects C extra F := by
  apply ObjectProperty.limitsClosure.of_mem
  exact Or.inr h

instance (extra : Set (Presheaf C)) :
    HasTerminal (GeneratedWithObjects C extra).FullSubcategory := by
  change HasLimitsOfShape (finiteLimitDiagram FiniteLimitShape.terminal)
    (GeneratedWithObjects C extra).FullSubcategory
  have : (GeneratedWithObjects C extra).IsClosedUnderLimitsOfShape
      (finiteLimitDiagram FiniteLimitShape.terminal) := by
    unfold GeneratedWithObjects
    infer_instance
  apply hasLimitsOfShape_of_closedUnderLimits

instance (extra : Set (Presheaf C)) :
    HasBinaryProducts (GeneratedWithObjects C extra).FullSubcategory := by
  change HasLimitsOfShape (finiteLimitDiagram FiniteLimitShape.binaryProduct)
    (GeneratedWithObjects C extra).FullSubcategory
  have : (GeneratedWithObjects C extra).IsClosedUnderLimitsOfShape
      (finiteLimitDiagram FiniteLimitShape.binaryProduct) := by
    unfold GeneratedWithObjects
    infer_instance
  apply hasLimitsOfShape_of_closedUnderLimits

instance (extra : Set (Presheaf C)) :
    HasEqualizers (GeneratedWithObjects C extra).FullSubcategory := by
  change HasLimitsOfShape (finiteLimitDiagram FiniteLimitShape.equalizer)
    (GeneratedWithObjects C extra).FullSubcategory
  have : (GeneratedWithObjects C extra).IsClosedUnderLimitsOfShape
      (finiteLimitDiagram FiniteLimitShape.equalizer) := by
    unfold GeneratedWithObjects
    infer_instance
  apply hasLimitsOfShape_of_closedUnderLimits

instance (extra : Set (Presheaf C)) :
    HasFiniteLimits (GeneratedWithObjects C extra).FullSubcategory := by
  have : HasFiniteProducts (GeneratedWithObjects C extra).FullSubcategory :=
    hasFiniteProducts_of_has_binary_and_terminal
  exact hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- It is least among isomorphism-closed properties containing both the
representables and the selected objects and closed under these shapes. -/
theorem generatedWithObjects_le (extra : Set (Presheaf C))
    (Q : ObjectProperty (Presheaf C)) [Q.IsClosedUnderIsomorphisms]
    [∀ shape, Q.IsClosedUnderLimitsOfShape (finiteLimitDiagram shape)]
    (hrep : Representable C ≤ Q)
    (additional : ∀ F ∈ extra, Q F) :
    GeneratedWithObjects C extra ≤ Q := by
  apply ObjectProperty.limitsClosure_le
  intro F h
  rcases h with h | h
  · exact hrep F h
  · exact additional F h

/-- The base category still embeds by its actual representables after the
additional semantic objects are included. -/
def intoGeneratedWithObjects (extra : Set (Presheaf C)) :
    C ⥤ (GeneratedWithObjects C extra).FullSubcategory where
  obj X := ⟨yoneda.obj X, representedWithObjects C extra X⟩
  map f := ObjectProperty.homMk (yoneda.map f)
  map_id X := by
    apply ObjectProperty.hom_ext
    change yoneda.map (𝟙 X) = 𝟙 (yoneda.obj X)
    simp
  map_comp f g := by
    apply ObjectProperty.hom_ext
    change yoneda.map (f ≫ g) = yoneda.map f ≫ yoneda.map g
    simp

theorem intoGeneratedWithObjects_comp_inclusion
    (extra : Set (Presheaf C)) :
    intoGeneratedWithObjects C extra ⋙
      (GeneratedWithObjects C extra).ι = yoneda := rfl

instance intoGeneratedWithObjects_faithful
    (extra : Set (Presheaf C)) :
    (intoGeneratedWithObjects C extra).Faithful where
  map_injective := by
    intro X Y f g equal
    apply yoneda.map_injective
    exact congrArg
      (fun h : (intoGeneratedWithObjects C extra).obj X ⟶
          (intoGeneratedWithObjects C extra).obj Y => h.hom) equal

instance intoGeneratedWithObjects_full
    (extra : Set (Presheaf C)) :
    (intoGeneratedWithObjects C extra).Full where
  map_surjective := by
    intro X Y arrow
    obtain ⟨f, hf⟩ := yoneda.map_surjective arrow.hom
    refine ⟨f, ?_⟩
    apply ObjectProperty.hom_ext
    exact hf

theorem intoGeneratedWithObjects_preservesFiniteProducts
    (extra : Set (Presheaf C)) :
    PreservesFiniteProducts (intoGeneratedWithObjects C extra) := by
  have : PreservesFiniteProducts
      (intoGeneratedWithObjects C extra ⋙
        (GeneratedWithObjects C extra).ι) := by
    rw [intoGeneratedWithObjects_comp_inclusion]
    infer_instance
  exact preservesFiniteProducts_of_reflects_of_preserves
    (intoGeneratedWithObjects C extra)
    (GeneratedWithObjects C extra).ι

theorem intoGeneratedWithObjects_preservesExistingFiniteLimitsOfShape
    (extra : Set (Presheaf C))
    (J : Type) [SmallCategory J] [FinCategory J]
    [HasLimitsOfShape J C] :
    PreservesLimitsOfShape J (intoGeneratedWithObjects C extra) := by
  have : PreservesLimitsOfShape J
      (intoGeneratedWithObjects C extra ⋙
        (GeneratedWithObjects C extra).ι) := by
    rw [intoGeneratedWithObjects_comp_inclusion]
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (intoGeneratedWithObjects C extra)
    (GeneratedWithObjects C extra).ι

/-- A mono between generated presheaves is pointwise injective. The
representables in the generated category test every presheaf element by the
Yoneda lemma, so the full-subcategory inclusion preserves monomorphisms. -/
theorem inclusion_preserves_mono (extra : Set (Presheaf C))
    {A B : (GeneratedWithObjects C extra).FullSubcategory}
    (f : A ⟶ B) [Mono f] :
    Mono ((GeneratedWithObjects C extra).ι.map f) := by
  change Mono f.hom
  apply (NatTrans.mono_iff_mono_app f.hom).2
  intro X
  apply (mono_iff_injective (f.hom.app X)).2
  intro a b equal
  let representedX := (intoGeneratedWithObjects C extra).obj X.unop
  let first : representedX ⟶ A :=
    ObjectProperty.homMk (yonedaEquiv.symm a)
  let second : representedX ⟶ A :=
    ObjectProperty.homMk (yonedaEquiv.symm b)
  have composed : first ≫ f = second ≫ f := by
    apply ObjectProperty.hom_ext
    apply yonedaEquiv.injective
    change yonedaEquiv (yonedaEquiv.symm a ≫ f.hom) =
      yonedaEquiv (yonedaEquiv.symm b ≫ f.hom)
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using equal
  have same : first = second := (cancel_mono f).mp composed
  have elements := congrArg
    (fun arrow : representedX ⟶ A => yonedaEquiv arrow.hom) same
  change yonedaEquiv (yonedaEquiv.symm a) =
    yonedaEquiv (yonedaEquiv.symm b) at elements
  simpa only [Equiv.apply_symm_apply] using elements

end Mettapedia.OSLF.FiniteLimitYoneda
