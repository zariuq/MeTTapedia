import Mettapedia.OSLF.Syntax.CategoricalBindingEquationEquivalence
import Mettapedia.OSLF.Syntax.CategoricalContextualEquationSoundness

/-!
# Contextual satisfaction preserves the authored model category

The contextual contract includes arbitrary captured ambient parameters. For
authored presentations it is equivalent to the original global satisfaction
contract. This comparison retains the underlying binding interpretation and
every assignment-preserving map, including noninvertible maps.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalContextualSatisfactionEquivalence

open _root_.CategoryTheory
open CategoricalBindingModel
open CategoricalBindingInterpretationMaps
open CategoricalBindingEquationEquivalence
open SecondOrderContext

universe u v

variable {S : Signature} {schema : List (MetaArity S)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

/-- The preserved original global contract quantifies bodies only in their
declared dependency contexts. Its maps are the original interpretation maps. -/
structure DependencySatisfyingInterpretation (P : EquationPresentation S schema) where
  interpretation : Interpretation S D
  satisfies : interpretation.model.DependencySatisfies P

instance (P : EquationPresentation S schema) :
    Category (DependencySatisfyingInterpretation (D := D) P) where
  Hom M N := M.interpretation ⟶ N.interpretation
  id M := 𝟙 M.interpretation
  comp f g := f ≫ g
  id_comp := by intros; exact Category.id_comp _
  comp_id := by intros; exact Category.comp_id _
  assoc := by intros; exact Category.assoc _ _ _

/-- Models satisfying contextual equation instances at every stage, with the
same underlying assignment-preserving interpretation maps. -/
structure ContextualSatisfyingInterpretation (P : EquationPresentation S schema) where
  interpretation : Interpretation S D
  satisfies : interpretation.model.ContextualSatisfies P

instance (P : EquationPresentation S schema) :
    Category (ContextualSatisfyingInterpretation (D := D) P) where
  Hom M N := M.interpretation ⟶ N.interpretation
  id M := 𝟙 M.interpretation
  comp f g := f ≫ g
  id_comp := by intros; exact Category.id_comp _
  comp_id := by intros; exact Category.comp_id _
  assoc := by intros; exact Category.assoc _ _ _

/-- Retain only the underlying interpretation of a contextual model. -/
def underlyingContextual (P : EquationPresentation S schema) :
    ContextualSatisfyingInterpretation (D := D) P ⥤ Interpretation S D where
  obj M := M.interpretation
  map f := f

/-- Retain only the underlying interpretation of an original model. -/
def underlyingOriginal (P : EquationPresentation S schema) :
    DependencySatisfyingInterpretation (D := D) P ⥤ Interpretation S D where
  obj M := M.interpretation
  map f := f

/-- Contextual instances include every original equation instance, for any
equation presentation. All interpretation maps are retained. -/
def forgetContextual (P : EquationPresentation S schema) :
    ContextualSatisfyingInterpretation (D := D) P ⥤ DependencySatisfyingInterpretation (D := D) P where
  obj M := ⟨M.interpretation, Model.Satisfies.toDependencySatisfies _ M.satisfies⟩
  map f := f

/-- For an authored presentation, original global satisfaction derives the
entire contextual contract. This changes no interpretation or morphism. -/
def contextualizeAuthored (equations : List (EqAxiom S schema)) :
    DependencySatisfyingInterpretation (D := D) (authoredEquationPresentation S equations) ⥤
      ContextualSatisfyingInterpretation (D := D) (authoredEquationPresentation S equations) where
  obj M := ⟨M.interpretation,
    (M.interpretation.model.authored_contextualSatisfies_iff equations).mpr M.satisfies⟩
  map f := f

/-- Forgetting contextual satisfaction retains the original interpretation. -/
theorem forgetContextual_obj_interpretation (P : EquationPresentation S schema)
    (M : ContextualSatisfyingInterpretation (D := D) P) :
    ((forgetContextual P).obj M).interpretation = M.interpretation := rfl

/-- Forgetting contextual satisfaction retains every model map. -/
theorem forgetContextual_map (P : EquationPresentation S schema)
    {M N : ContextualSatisfyingInterpretation (D := D) P} (f : M ⟶ N) :
    (forgetContextual P).map f = f := rfl

/-- Deriving contextual satisfaction retains the original interpretation. -/
theorem contextualizeAuthored_obj_interpretation (equations : List (EqAxiom S schema))
    (M : DependencySatisfyingInterpretation (D := D) (authoredEquationPresentation S equations)) :
    ((contextualizeAuthored equations).obj M).interpretation = M.interpretation := rfl

/-- Deriving contextual satisfaction retains every model map. -/
theorem contextualizeAuthored_map (equations : List (EqAxiom S schema))
    {M N : DependencySatisfyingInterpretation (D := D) (authoredEquationPresentation S equations)}
    (f : M ⟶ N) :
    (contextualizeAuthored equations).map f = f := rfl

/-- The authored model-contract comparison has a natural unit with identity
underlying interpretation components. -/
def authoredUnitIso (equations : List (EqAxiom S schema)) :
    𝟭 (DependencySatisfyingInterpretation (D := D) (authoredEquationPresentation S equations)) ≅
      contextualizeAuthored equations ⋙ forgetContextual (authoredEquationPresentation S equations) :=
  NatIso.ofComponents (fun M =>
    { hom := 𝟙 M.interpretation
      inv := 𝟙 M.interpretation
      hom_inv_id := Category.id_comp _
      inv_hom_id := Category.id_comp _ }) (by
        intro M N f
        exact (Category.comp_id f).trans (Category.id_comp f).symm)

/-- The reverse authored comparison has a natural counit with identity
underlying interpretation components. -/
def authoredCounitIso (equations : List (EqAxiom S schema)) :
    forgetContextual (authoredEquationPresentation S equations) ⋙ contextualizeAuthored equations ≅
      𝟭 (ContextualSatisfyingInterpretation (D := D) (authoredEquationPresentation S equations)) :=
  NatIso.ofComponents (fun M =>
    { hom := 𝟙 M.interpretation
      inv := 𝟙 M.interpretation
      hom_inv_id := Category.id_comp _
      inv_hom_id := Category.id_comp _ }) (by
        intro M N f
        exact (Category.comp_id f).trans (Category.id_comp f).symm)

/-- The authored satisfaction contracts give equivalent categories on all
assignment-preserving maps, without an invertibility restriction. -/
def authoredEquivalence (equations : List (EqAxiom S schema)) :
    DependencySatisfyingInterpretation (D := D) (authoredEquationPresentation S equations) ≌
      ContextualSatisfyingInterpretation (D := D) (authoredEquationPresentation S equations) where
  functor := contextualizeAuthored equations
  inverse := forgetContextual (authoredEquationPresentation S equations)
  unitIso := authoredUnitIso equations
  counitIso := authoredCounitIso equations
  functor_unitIso_comp := by intro M; exact Category.id_comp _

/-- The forward equivalence commutes exactly with forgetting to the
underlying interpretation, on objects and morphisms. -/
theorem authoredEquivalence_underlying (equations : List (EqAxiom S schema)) :
    (authoredEquivalence (D := D) equations).functor ⋙
        underlyingContextual (authoredEquationPresentation S equations) =
      underlyingOriginal (authoredEquationPresentation S equations) := rfl

/-- The inverse equivalence commutes exactly with forgetting to the
underlying interpretation, on objects and morphisms. -/
theorem authoredEquivalence_inverse_underlying (equations : List (EqAxiom S schema)) :
    (authoredEquivalence (D := D) equations).inverse ⋙
        underlyingOriginal (authoredEquationPresentation S equations) =
      underlyingContextual (authoredEquationPresentation S equations) := rfl

/-- The explicit contextual view retains the actual canonical satisfying
interpretation, with its full ambient instance law. -/
def contextualToCanonical (P : EquationPresentation S schema) :
    ContextualSatisfyingInterpretation (D := D) P ⥤
      CategoricalBindingEquationEquivalence.SatisfyingInterpretation (D := D) P where
  obj M := ⟨M.interpretation, M.satisfies⟩
  map f := f

/-- The canonical model category supplies the same explicit contextual view. -/
def canonicalToContextual (P : EquationPresentation S schema) :
    CategoricalBindingEquationEquivalence.SatisfyingInterpretation (D := D) P ⥤
      ContextualSatisfyingInterpretation (D := D) P where
  obj M := ⟨M.interpretation, M.satisfies⟩
  map f := f

/-- The explicit contextual view and canonical model category agree on all
objects and maps. -/
def contextualCanonicalEquivalence (P : EquationPresentation S schema) :
    ContextualSatisfyingInterpretation (D := D) P ≌
      CategoricalBindingEquationEquivalence.SatisfyingInterpretation (D := D) P where
  functor := contextualToCanonical P
  inverse := canonicalToContextual P
  unitIso := NatIso.ofComponents (fun M =>
    { hom := 𝟙 M.interpretation
      inv := 𝟙 M.interpretation
      hom_inv_id := Category.id_comp _
      inv_hom_id := Category.id_comp _ }) (by
        intro M N f
        exact (Category.comp_id f).trans (Category.id_comp f).symm)
  counitIso := NatIso.ofComponents (fun M =>
    { hom := 𝟙 M.interpretation
      inv := 𝟙 M.interpretation
      hom_inv_id := Category.id_comp _
      inv_hom_id := Category.id_comp _ }) (by
        intro M N f
        exact (Category.comp_id f).trans (Category.id_comp f).symm)
  functor_unitIso_comp := by intro M; exact Category.id_comp _

/-- The canonical full-context authored model category is equivalent to the
preserved genuine dependency-only global model category, on every map. -/
def authoredCanonicalEquivalence (equations : List (EqAxiom S schema)) :
    DependencySatisfyingInterpretation (D := D) (authoredEquationPresentation S equations) ≌
      CategoricalBindingEquationEquivalence.SatisfyingInterpretation (D := D)
        (authoredEquationPresentation S equations) :=
  (authoredEquivalence equations).trans
    (contextualCanonicalEquivalence (authoredEquationPresentation S equations))

/-- Forget the full canonical contract while retaining the interpretation. -/
def underlyingCanonical (P : EquationPresentation S schema) :
    CategoricalBindingEquationEquivalence.SatisfyingInterpretation (D := D) P ⥤
      Interpretation S D where
  obj M := M.interpretation
  map f := f

/-- The actual canonical comparison retains the interpretation on every
object and every morphism. -/
theorem authoredCanonicalEquivalence_underlying (equations : List (EqAxiom S schema)) :
    (authoredCanonicalEquivalence (D := D) equations).functor ⋙
        underlyingCanonical (authoredEquationPresentation S equations) =
      underlyingOriginal (authoredEquationPresentation S equations) := rfl

/-- The inverse actual canonical comparison likewise retains every
underlying interpretation and every morphism. -/
theorem authoredCanonicalEquivalence_inverse_underlying (equations : List (EqAxiom S schema)) :
    (authoredCanonicalEquivalence (D := D) equations).inverse ⋙
        underlyingOriginal (authoredEquationPresentation S equations) =
      underlyingCanonical (authoredEquationPresentation S equations) := rfl

end Mettapedia.OSLF.Binding.CategoricalContextualSatisfactionEquivalence
