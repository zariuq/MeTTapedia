import Mettapedia.GSLT.Core.AuthoredClosedTheoryControls
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctor

/-!
# Complete interpretation and quotient-class separation

Two independently declared arrows are interpreted as identity and Boolean
negation. Their actual generated quotient classes are distinct, as witnessed
by the earned interpretation functor. A second declaration interpretation
identifies those same two arrows, so successful interpretation does not imply
reflection of the source equations.

The base diagram remains the complete category of types. Its unchanged maps
and the nonidentity declared negation are both recovered by the actual
quotient functor, rather than supplied as a functoriality assumption. The
interpreted generic function retains both values of its supplied argument.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedInterpretationControls

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation
open Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory
open AuthoredClosedTheoryControls

def separatingAssignment : Assignment (Type) syntaxSymbols (Type) where
  base := Functor.id (Type)
  object _ := Bool
  arrow name := ⟨Bool, Bool, if name then negate else 𝟙 Bool⟩

theorem separatingRealization : Realization syntaxSignature separatingAssignment where
  source _ := rfl
  target _ := rfl
  equation origin := origin.elim

def namedArrow (name : Bool) : RawHom Generated.dataObject Generated.dataObject :=
  ⟨.name name, ⟨by
    change Derivation syntaxSignature (.arrow contextCode contextCode (.name name))
    exact .arrowName (signature := syntaxSignature) name contextFormation contextFormation⟩⟩

def separatedArrow (name : Bool) : Generated.dataObject ⟶ Generated.dataObject :=
  classOf (namedArrow name)

theorem actual_negation_image :
    (functor separatingAssignment separatingRealization).map (separatedArrow true) = negate :=
  rawArrowValue_unique separatingAssignment separatingRealization (namedArrow true) negate rfl

theorem actual_identity_image :
    (functor separatingAssignment separatingRealization).map (separatedArrow false) = 𝟙 Bool :=
  rawArrowValue_unique separatingAssignment separatingRealization (namedArrow false) (𝟙 Bool) rfl

theorem supplied_false_changes_to_true :
    (functor separatingAssignment separatingRealization).map (separatedArrow true) false = true := by
  rw [actual_negation_image]
  rfl

theorem supplied_true_changes_to_false :
    (functor separatingAssignment separatingRealization).map (separatedArrow true) true = false := by
  rw [actual_negation_image]
  rfl

theorem no_generated_identity_negation_equation :
    ¬ Nonempty (Derivation syntaxSignature
      (.equation contextCode contextCode (.name false) (.name true))) := by
  rintro ⟨tree⟩
  have same : (𝟙 Bool : Bool ⟶ Bool) = negate :=
    Interprets.equal_arrows _ _ (sound separatingAssignment separatingRealization tree) rfl rfl
  have impossible : false = true := congrArg (fun arrow : Bool ⟶ Bool => arrow false) same
  exact Bool.false_ne_true impossible

theorem distinct_actual_quotient_classes : separatedArrow false ≠ separatedArrow true := by
  intro same
  exact no_generated_identity_negation_equation (classOf_eq_iff.mp same)

def collidingAssignment : Assignment (Type) syntaxSymbols (Type) where
  base := Functor.id (Type)
  object _ := Bool
  arrow _ := ⟨Bool, Bool, 𝟙 Bool⟩

theorem collidingRealization : Realization syntaxSignature collidingAssignment where
  source _ := rfl
  target _ := rfl
  equation origin := origin.elim

theorem colliding_arrow_image (name : Bool) :
    (functor collidingAssignment collidingRealization).map (separatedArrow name) = 𝟙 Bool :=
  rawArrowValue_unique collidingAssignment collidingRealization (namedArrow name) (𝟙 Bool) rfl

theorem collision_does_not_reflect_quotient_equality :
    (functor collidingAssignment collidingRealization).map (separatedArrow false) =
      (functor collidingAssignment collidingRealization).map (separatedArrow true) ∧
    separatedArrow false ≠ separatedArrow true :=
  ⟨(colliding_arrow_image false).trans (colliding_arrow_image true).symm,
    distinct_actual_quotient_classes⟩

theorem complete_base_diagram_recovered :
    baseFunctor syntaxSignature ⋙ functor separatingAssignment separatingRealization =
      Functor.id (Type) :=
  functor_base separatingAssignment separatingRealization

theorem nonidentity_base_arrow_recovered :
    (functor separatingAssignment separatingRealization).map
      (baseArrow (signature := syntaxSignature) negate) = negate :=
  functor_base_arrow separatingAssignment separatingRealization negate

def authoredFunction :
    RawHom Generated.dataObject (exponentialObject Generated.dataObject Generated.dataObject) :=
  ⟨annotatedAbstraction, ⟨by
    change Derivation syntaxSignature
      (.arrow contextCode (.exponential contextCode contextCode) annotatedAbstraction)
    exact annotatedAbstractionTyped⟩⟩

theorem complete_function_image :
    rawArrowValue separatingAssignment separatingRealization authoredFunction =
      abstraction (CartesianMonoidalCategory.snd Bool Bool) :=
  rawArrowValue_unique separatingAssignment separatingRealization authoredFunction _
    (separatingAssignment.evaluate_abstraction (CartesianMonoidalCategory.snd Bool Bool) rfl rfl rfl
      (separatingAssignment.evaluate_second rfl rfl))

def interpretedFunction (environment : Bool) : Bool ⟶ Bool :=
  rawArrowValue separatingAssignment separatingRealization authoredFunction environment

theorem generic_function_retains_each_argument :
    interpretedFunction false false = false ∧ interpretedFunction false true = true := by
  unfold interpretedFunction
  rw [complete_function_image]
  exact ⟨rfl, rfl⟩

theorem erased_generic_argument_rejected :
    interpretedFunction false false ≠ interpretedFunction false true := by
  rw [generic_function_retains_each_argument.1, generic_function_retains_each_argument.2]
  exact Bool.false_ne_true

end Mettapedia.GSLT.Core.RelativeClosedInterpretationControls
