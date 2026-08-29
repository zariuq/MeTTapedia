import Mettapedia.Computability.FragmentwiseComputationalTrinity
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Open-ended computational trinity

A comparison triangle describes one current relationship among operational,
logical, and spatial faces.  It is not a declaration that those faces are the
last possible language, type theory, or model.

`ComparisonMap` is a commuting development step between two triangles.
`Extension` strengthens such a step with pointwise injectivity, so earlier
distinctions remain available while the later faces may add new elements.
Neither structure includes surjectivity or a global closure claim.

Closure remains scoped.  A contextual constraint which covers every element
of an earlier face covers the image of that face after transport.  It covers
the entire later face only when a separate pointwise-surjectivity premise is
supplied.  The canary exhibits an injective extension from a one-point trinity
to a Boolean trinity: the old point remains represented, while the new point
is not licensed by old coverage.  Thus open development does not silently
install a closed-world assumption.
-/

namespace Mettapedia.Computability.OpenComputationalTrinity

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.Computability.FragmentwiseComputationalTrinity

universe u v w

variable {Context : Type u} [Category.{v} Context]

/-- A structure-preserving development step between two current trinity
comparisons over the same context category. -/
structure ComparisonMap
    (earlier later : Comparison.{u, v, w} Context) where
  program : earlier.program ⟶ later.program
  logic : earlier.logic ⟶ later.logic
  space : earlier.space ⟶ later.space
  programLogic :
    earlier.programToLogic ≫ logic = program ≫ later.programToLogic
  logicSpace :
    earlier.logicToSpace ≫ space = logic ≫ later.logicToSpace

namespace ComparisonMap

variable {earlier middle later : Comparison.{u, v, w} Context}

/-- The direct operational-to-spatial square follows from the two adjacent
squares and the coherence triangles. -/
theorem programSpace (development : ComparisonMap earlier later) :
    earlier.programToSpace ≫ development.space =
      development.program ≫ later.programToSpace := by
  calc
    earlier.programToSpace ≫ development.space =
        (earlier.programToLogic ≫ earlier.logicToSpace) ≫
          development.space := by rw [earlier.coherence]
    _ = earlier.programToLogic ≫
        (earlier.logicToSpace ≫ development.space) := by
      simp only [Category.assoc]
    _ = earlier.programToLogic ≫
        (development.logic ≫ later.logicToSpace) := by
      rw [development.logicSpace]
    _ = (earlier.programToLogic ≫ development.logic) ≫
        later.logicToSpace := by simp only [Category.assoc]
    _ = (development.program ≫ later.programToLogic) ≫
        later.logicToSpace := by rw [development.programLogic]
    _ = development.program ≫
        (later.programToLogic ≫ later.logicToSpace) := by
      simp only [Category.assoc]
    _ = development.program ≫ later.programToSpace := by
      rw [later.coherence]

/-- A comparison is a valid development stage of itself. -/
def identity (comparison : Comparison.{u, v, w} Context) :
    ComparisonMap comparison comparison where
  program := 𝟙 comparison.program
  logic := 𝟙 comparison.logic
  space := 𝟙 comparison.space
  programLogic := by simp
  logicSpace := by simp

/-- Commuting development steps compose. -/
def comp (first : ComparisonMap earlier middle)
    (second : ComparisonMap middle later) : ComparisonMap earlier later where
  program := first.program ≫ second.program
  logic := first.logic ≫ second.logic
  space := first.space ≫ second.space
  programLogic := by
    calc
      earlier.programToLogic ≫ (first.logic ≫ second.logic) =
          (earlier.programToLogic ≫ first.logic) ≫ second.logic := by
        simp only [Category.assoc]
      _ = (first.program ≫ middle.programToLogic) ≫ second.logic := by
        rw [first.programLogic]
      _ = first.program ≫ (middle.programToLogic ≫ second.logic) := by
        simp only [Category.assoc]
      _ = first.program ≫ (second.program ≫ later.programToLogic) := by
        rw [second.programLogic]
      _ = (first.program ≫ second.program) ≫ later.programToLogic := by
        simp only [Category.assoc]
  logicSpace := by
    calc
      earlier.logicToSpace ≫ (first.space ≫ second.space) =
          (earlier.logicToSpace ≫ first.space) ≫ second.space := by
        simp only [Category.assoc]
      _ = (first.logic ≫ middle.logicToSpace) ≫ second.space := by
        rw [first.logicSpace]
      _ = first.logic ≫ (middle.logicToSpace ≫ second.space) := by
        simp only [Category.assoc]
      _ = first.logic ≫ (second.logic ≫ later.logicToSpace) := by
        rw [second.logicSpace]
      _ = (first.logic ≫ second.logic) ≫ later.logicToSpace := by
        simp only [Category.assoc]

end ComparisonMap

/-- An open extension preserves every earlier generalized element
injectively.  It may still add elements because surjectivity is deliberately
absent. -/
structure Extension
    (earlier later : Comparison.{u, v, w} Context) where
  toComparisonMap : ComparisonMap earlier later
  program_injective : ∀ context,
    Function.Injective (toComparisonMap.program.app context)
  logic_injective : ∀ context,
    Function.Injective (toComparisonMap.logic.app context)
  space_injective : ∀ context,
    Function.Injective (toComparisonMap.space.app context)

namespace Extension

variable {earlier middle later : Comparison.{u, v, w} Context}

/-- Pointwise-injective extensions compose without gaining a surjectivity
claim. -/
def comp (first : Extension earlier middle)
    (second : Extension middle later) : Extension earlier later where
  toComparisonMap := first.toComparisonMap.comp second.toComparisonMap
  program_injective := by
    intro context left right equality
    apply first.program_injective context
    apply second.program_injective context
    exact equality
  logic_injective := by
    intro context left right equality
    apply first.logic_injective context
    apply second.logic_injective context
    exact equality
  space_injective := by
    intro context left right equality
    apply first.space_injective context
    apply second.space_injective context
    exact equality

/-- A later operational element is genuinely new at a context when it is not
represented by any earlier operational element. -/
def AddsProgramAt (extension : Extension earlier later)
    (context : Contextᵒᵖ) : Prop :=
  ∃ laterProgram : later.program.obj context,
    ¬ ∃ earlierProgram : earlier.program.obj context,
      extension.toComparisonMap.program.app context earlierProgram =
        laterProgram

end Extension

/-! ## Scoped coverage and its exact transfer premise -/

namespace Constraint

variable {sourceFace targetFace : Face.{u, v, w} Context}

/-- A contextual constraint covers one named context when it holds for every
generalized element at that context. -/
def CoversAt (constraint : Constraint sourceFace)
    (context : Contextᵒᵖ) : Prop :=
  ∀ element, constraint.holds context element

/-- Earlier coverage transfers to complete later coverage when the face map
is pointwise surjective at the named context.  Surjectivity is the explicit
extra premise which a closed-world reading would otherwise hide. -/
theorem pushforward_coversAt_of_surjective
    (interpretation : sourceFace ⟶ targetFace)
    (sourceConstraint : Constraint sourceFace)
    (context : Contextᵒᵖ)
    (covered : CoversAt sourceConstraint context)
    (surjective : Function.Surjective (interpretation.app context)) :
    CoversAt (sourceConstraint.pushforward interpretation) context := by
  intro targetElement
  obtain ⟨sourceElement, rfl⟩ := surjective targetElement
  exact ⟨sourceElement, covered sourceElement, rfl⟩

/-- If the later face contains a genuinely new element, no transported
earlier constraint can claim complete coverage of the later face. -/
theorem pushforward_not_coversAt_of_new_element
    (interpretation : sourceFace ⟶ targetFace)
    (sourceConstraint : Constraint sourceFace)
    (context : Contextᵒᵖ)
    (newElement : targetFace.obj context)
    (notRepresented :
      ¬ ∃ sourceElement,
        interpretation.app context sourceElement = newElement) :
    ¬ CoversAt (sourceConstraint.pushforward interpretation) context := by
  intro covers
  rcases covers newElement with ⟨sourceElement, _, represented⟩
  exact notRepresented ⟨sourceElement, represented⟩

end Constraint

/-! ## Positive and negative open-development canaries -/

namespace Canary

abbrev CanaryContext := Discrete Unit

private def here : CanaryContextᵒᵖ :=
  Opposite.op (Discrete.mk Unit.unit)

def unitFace : Face CanaryContext :=
  (Functor.const CanaryContextᵒᵖ).obj Unit

def boolFace : Face CanaryContext :=
  (Functor.const CanaryContextᵒᵖ).obj Bool

def unitComparison : Comparison CanaryContext where
  program := unitFace
  logic := unitFace
  space := unitFace
  programToLogic := 𝟙 unitFace
  logicToSpace := 𝟙 unitFace
  programToSpace := 𝟙 unitFace
  coherence := by simp

def boolComparison : Comparison CanaryContext where
  program := boolFace
  logic := boolFace
  space := boolFace
  programToLogic := 𝟙 boolFace
  logicToSpace := 𝟙 boolFace
  programToSpace := 𝟙 boolFace
  coherence := by simp

/-- Embed the earlier point as `false`; `true` remains genuinely new. -/
def pointToBool : unitFace ⟶ boolFace :=
  (Functor.const CanaryContextᵒᵖ).map (↾(fun _ : Unit => false))

def pointBooleanDevelopment : ComparisonMap unitComparison boolComparison where
  program := pointToBool
  logic := pointToBool
  space := pointToBool
  programLogic := by simp [pointToBool, unitComparison, boolComparison]
  logicSpace := by simp [pointToBool, unitComparison, boolComparison]

/-- The development preserves every old distinction on all three faces. -/
def pointBooleanExtension : Extension unitComparison boolComparison where
  toComparisonMap := pointBooleanDevelopment
  program_injective := by
    intro context left right equality
    change Unit at left right
    exact Subsingleton.elim left right
  logic_injective := by
    intro context left right equality
    change Unit at left right
    exact Subsingleton.elim left right
  space_injective := by
    intro context left right equality
    change Unit at left right
    exact Subsingleton.elim left right

/-- The unique earlier operational element is covered. -/
def unitCoverage : Constraint unitComparison.program where
  holds _ element := element = Unit.unit
  map_closed := by
    rintro source target substitution ⟨⟩ admitted
    rfl

theorem unitCoverage_covers : Constraint.CoversAt unitCoverage here := by
  rintro ⟨⟩
  rfl

/-- Positive control: old content remains represented after extension. -/
theorem old_point_remains_covered :
    (unitCoverage.pushforward pointBooleanDevelopment.program).holds
      here false := by
  exact ⟨Unit.unit, rfl, rfl⟩

/-- Negative control: the extension contains a program not represented by the
earlier program face. -/
theorem extension_adds_true_program :
    pointBooleanExtension.AddsProgramAt here := by
  refine ⟨true, ?_⟩
  rintro ⟨earlier, represented⟩
  change false = true at represented
  cases represented

/-- Therefore complete coverage of the earlier face does not become complete
coverage of the later face. -/
theorem old_coverage_does_not_install_CWA :
    ¬ Constraint.CoversAt
      (unitCoverage.pushforward pointBooleanDevelopment.program) here := by
  apply Constraint.pushforward_not_coversAt_of_new_element
    pointBooleanDevelopment.program unitCoverage here true
  rintro ⟨earlier, represented⟩
  change false = true at represented
  cases represented

end Canary

#print axioms ComparisonMap.programSpace
#print axioms ComparisonMap.comp
#print axioms Extension.comp
#print axioms Constraint.pushforward_coversAt_of_surjective
#print axioms Constraint.pushforward_not_coversAt_of_new_element
#print axioms Canary.old_point_remains_covered
#print axioms Canary.extension_adds_true_program
#print axioms Canary.old_coverage_does_not_install_CWA

end Mettapedia.Computability.OpenComputationalTrinity
