import Mettapedia.TypeTheory.CwfInhabitationInstitution
import Mettapedia.Logic.InstitutionCategory
import Mettapedia.GSLT.Core.ContextualProfileInclusions

/-!
# The simple-to-dependent route between CwF inhabitation institutions

The canonical simply typed families CwF and dependent families CwF have the
same contexts and substitutions.  Constant-family inclusion therefore gives
an exact institution comorphism between their global-inhabitation logics.

This is a semantic conservativity result for the simple fragment, not an
equivalence of the two type theories.  A varying family over `Bool` supplies
the negative control: its inhabitation depends on the selected global point,
whereas the inhabitation of every translated simple type is point-independent.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CwfSimpleDependentInstitution

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.Logic
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.CwfInhabitationInstitution

universe u

/-- The global-inhabitation institution of the canonical simply typed
families CwF. -/
abbrev simpleInstitution :=
  ofCwf (SimpleFamiliesCwfWithTerminal.{u})

/-- The global-inhabitation institution of the canonical dependent families
CwF. -/
abbrev dependentInstitution :=
  ofCwf (familiesCwfWithTerminal.{u})

/-- Contexts translate by the existing constant-family profile inclusion;
the opposite is forced by sentence variance. -/
def mapSignature :
    Signature (SimpleFamiliesCwfWithTerminal.{u}) ⥤
      Signature (familiesCwfWithTerminal.{u}) :=
  simpleToDependentBaseFunctor.op

/-- A simply typed sentence becomes the corresponding constant dependent
family. -/
def mapSentence :
    simpleInstitution.sentence ⟶
      mapSignature ⋙ dependentInstitution.sentence where
  app context := TypeCat.ofHom fun type => constantFamily type
  naturality := by
    intro source target substitution
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext type
    rfl

/-- Global substitutions are unchanged by the simple-to-dependent base
inclusion. -/
def mapModel :
    mapSignature.op ⋙ dependentInstitution.model ⟶
      simpleInstitution.model where
  app context :=
    (Discrete.functor fun global :
        SimpleFamiliesCwfWithTerminal.toCwf.Sub
          SimpleFamiliesCwfWithTerminal.empty context.unop.unop.val =>
      Discrete.mk global).toCatHom
  naturality := by
    intro source target substitution
    apply Cat.Hom.ext
    apply Discrete.functor_ext
    intro global
    rfl

/-- Constant-family inclusion is an exact institution comorphism. -/
def simpleToDependent :
    Institution.Comorphism simpleInstitution dependentInstitution where
  mapSignature := mapSignature
  mapSentence := mapSentence
  mapModel := mapModel
  satisfaction_condition := by
    intro context targetModel sourceType
    rfl

/-- The route preserves and reflects satisfaction at every global point. -/
theorem satisfaction_iff
    (context : Signature (SimpleFamiliesCwfWithTerminal.{u}))
    (global : dependentInstitution.model.obj
      (Opposite.op (mapSignature.obj context)))
    (type : simpleInstitution.sentence.obj context) :
    dependentInstitution.satisfies (mapSignature.obj context) global
        (mapSentence.app context type) ↔
      simpleInstitution.satisfies context
        ((mapModel.app (Opposite.op context)).toFunctor.obj global) type :=
  simpleToDependent.satisfaction_condition context global type

/-- Every simple global model is literally the reduct of the same global
substitution on the dependent side. -/
theorem coversModels : simpleToDependent.CoversModels := by
  intro context sourceModel
  exact ⟨sourceModel, rfl⟩

/-- Hence semantic consequence is exact on the constant-family image. -/
theorem entails_iff
    (context : Signature (SimpleFamiliesCwfWithTerminal.{u}))
    (premises : Set (simpleInstitution.sentence.obj context))
    (conclusion : simpleInstitution.sentence.obj context) :
    simpleInstitution.Entails context premises conclusion ↔
      dependentInstitution.Entails (mapSignature.obj context)
        (Set.image (mapSentence.app context) premises)
        (mapSentence.app context conclusion) :=
  Institution.Comorphism.entails_mapped_iff_of_coversModels
    simpleToDependent coversModels context premises conclusion

/-! ## Point-sensitive dependency is genuinely new -/

/-- The Boolean context, regarded as a dependent-institution signature. -/
def boolContext : Signature (familiesCwfWithTerminal.{0}) :=
  Opposite.op ⟨Bool⟩

/-- The global point selecting `false`. -/
def falseGlobal : dependentInstitution.model.obj
    (Opposite.op boolContext) :=
  Discrete.mk fun _ => false

/-- The global point selecting `true`. -/
def trueGlobal : dependentInstitution.model.obj
    (Opposite.op boolContext) :=
  Discrete.mk fun _ => true

/-- Positive control: the varying family has a term at its singleton fibre. -/
theorem varying_satisfied_at_false :
    dependentInstitution.satisfies boolContext falseGlobal
      varyingBoolFamily := by
  exact ⟨fun _ => PUnit.unit⟩

/-- Negative control: the same family has no term at its empty fibre. -/
theorem varying_not_satisfied_at_true :
    ¬ dependentInstitution.satisfies boolContext trueGlobal
      varyingBoolFamily := by
  rintro ⟨term⟩
  exact nomatch term PUnit.unit

/-- A translated simple type cannot observe which global Boolean point was
chosen: its dependent family is constant. -/
theorem translated_satisfaction_point_independent (type : Type) :
    dependentInstitution.satisfies boolContext falseGlobal
        (constantFamily type) ↔
      dependentInstitution.satisfies boolContext trueGlobal
        (constantFamily type) :=
  Iff.rfl

/-- No translated simple sentence reproduces the point-sensitive
inhabitation pattern of the varying dependent family. -/
theorem varying_observation_not_in_simple_image :
    ¬ ∃ type : Type,
      (dependentInstitution.satisfies boolContext falseGlobal
          (constantFamily type) ↔
        dependentInstitution.satisfies boolContext falseGlobal
          varyingBoolFamily) ∧
      (dependentInstitution.satisfies boolContext trueGlobal
          (constantFamily type) ↔
        dependentInstitution.satisfies boolContext trueGlobal
          varyingBoolFamily) := by
  rintro ⟨type, atFalse, atTrue⟩
  have constantAtFalse : dependentInstitution.satisfies boolContext falseGlobal
      (constantFamily type) := atFalse.mpr varying_satisfied_at_false
  have constantAtTrue : dependentInstitution.satisfies boolContext trueGlobal
      (constantFamily type) :=
    (translated_satisfaction_point_independent type).mp constantAtFalse
  exact varying_not_satisfied_at_true (atTrue.mp constantAtTrue)

#print axioms mapSentence
#print axioms mapModel
#print axioms simpleToDependent
#print axioms satisfaction_iff
#print axioms coversModels
#print axioms entails_iff
#print axioms varying_satisfied_at_false
#print axioms varying_not_satisfied_at_true
#print axioms translated_satisfaction_point_independent
#print axioms varying_observation_not_in_simple_image

end Mettapedia.TypeTheory.CwfSimpleDependentInstitution

/-! ## Both inhabitation logics as objects of the category of institutions -/


namespace Mettapedia.TypeTheory.CwfSimpleDependentInstitution

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.Logic
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.CwfInhabitationInstitution

universe u v w w'

/-- The heterogeneous-atlas institutionObject canonically generated by a CwF with a
terminal context. -/
def institutionObject (C : CwfWithTerminal.{u, v, w, w'}) :
    InstitutionCategory.Object.{u, v, w, v, v} where
  Signature := Cat.of (Signature C)
  logic := ofCwf C

/-- The simply typed families inhabitation logic as an atlas institutionObject. -/
abbrev simpleInstitutionObject :=
  institutionObject (SimpleFamiliesCwfWithTerminal.{u})

/-- The dependent families inhabitation logic as an atlas institutionObject. -/
abbrev dependentInstitutionObject :=
  institutionObject (familiesCwfWithTerminal.{u})

/-- Constant-family inclusion is a composable heterogeneous institution
route. -/
def simpleDependentRoute : simpleInstitutionObject ⟶ dependentInstitutionObject :=
  simpleToDependent

/-- The source Boolean context used to test the route's sentence fibre. -/
def simpleBoolContext : Signature (SimpleFamiliesCwfWithTerminal.{0}) :=
  Opposite.op ⟨Bool⟩

/-- Positive control: the heterogeneous route maps a simple type to exactly
its constant dependent family. -/
@[simp]
theorem simpleDependentRoute_mapSentence (type : Type) :
    simpleDependentRoute.mapSentence.app simpleBoolContext type =
      constantFamily type :=
  rfl

/-- Negative control: the sentence map is not surjective at the Boolean
context because the dependent fibre contains a genuinely varying family. -/
theorem simpleDependentRoute_sentence_not_surjective :
    ¬ Function.Surjective
      (fun type : simpleInstitutionObject.logic.sentence.obj simpleBoolContext =>
        simpleDependentRoute.mapSentence.app simpleBoolContext type) := by
  intro surjective
  rcases surjective varyingBoolFamily with ⟨type, equality⟩
  exact varyingBoolFamily_not_constant ⟨type, equality.symm⟩

/-- The theory graph has a route from the simple node to the dependent node, while
that route remains a proper embedding on the discriminating type fibre. -/
theorem simpleDependentRoute_is_proper :
    Nonempty (simpleInstitutionObject ⟶ dependentInstitutionObject) ∧
      ¬ Function.Surjective
        (fun type : simpleInstitutionObject.logic.sentence.obj simpleBoolContext =>
          simpleDependentRoute.mapSentence.app simpleBoolContext type) :=
  ⟨⟨simpleDependentRoute⟩,
    simpleDependentRoute_sentence_not_surjective⟩

#print axioms institutionObject
#print axioms simpleDependentRoute
#print axioms simpleDependentRoute_mapSentence
#print axioms simpleDependentRoute_sentence_not_surjective
#print axioms simpleDependentRoute_is_proper

end Mettapedia.TypeTheory.CwfSimpleDependentInstitution
