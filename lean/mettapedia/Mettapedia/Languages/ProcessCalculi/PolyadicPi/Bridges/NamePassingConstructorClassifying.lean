import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingContinuationOperations
import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretationClosed
import Mettapedia.GSLT.Core.LambdaTheory
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# The closed and finite-limit constructor interpretation

The five independently declared source constructor headers generate an actual
cartesian closed category with finite limits. The target primitive arrows
supply a locally checked realization through the computed continuation arrows.
The resulting quotient functor preserves finite limits and the canonical
exponential comparison. Names map to the target name object, and terms map
to its actual name-to-process function object.

The object and hom universes of the target remain independent. The empty base
diagram and the finite constructor names are genuinely lifted to its hom
universe. This constructor completion has no authored operational-edge sort
or extra static equations; their classifying comparison remains a separate
obligation of the full process-theory interpretation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingConstructorClassifying

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open NamePassingContinuationOperations

universe u v

inductive ObjectName where
  | names
  | terms

inductive Constructor where
  | reference
  | abstraction
  | application
  | definition
  | carrier

abbrev Base := ULiftHom.{v} (ULift.{v} (Discrete Empty))

instance : IsEmpty Base.{v} :=
  ⟨fun object => isEmptyElim (ULiftHom.objDown object).down⟩

def symbols : Symbols.{v} where
  ObjectName := ULift.{v} ObjectName
  ArrowName := ULift.{v} Constructor
  EquationName := ULift.{v} Empty

def names : ObjectCode Base.{v} symbols.{v} := .name ⟨.names⟩
def terms : ObjectCode Base.{v} symbols.{v} := .name ⟨.terms⟩

def constructorSource : Constructor → ObjectCode Base.{v} symbols.{v}
  | .reference => names
  | .abstraction => .exponential names terms
  | .application => .product terms names
  | .definition => .product terms (.exponential names terms)
  | .carrier => .product names (.product terms terms)

def signature : Signature (C := Base.{v}) (symbols := symbols.{v}) where
  objectRank _ := 0
  arrowRank _ := 1
  source origin := constructorSource origin.down
  target _ := terms
  source_before origin := by
    cases origin with
    | up origin =>
      cases origin <;> simp [constructorSource, names, terms, ObjectCode.before]
  target_before _ := by simp [terms, ObjectCode.before]
  equationRank origin := nomatch origin.down
  equationSource origin := nomatch origin.down
  equationTarget origin := nomatch origin.down
  left origin := nomatch origin.down
  right origin := nomatch origin.down
  equation_before origin := nomatch origin.down

private def namesFormed : Derivation signature.{v} (.object names) :=
  .objectName (signature := signature) (ULift.up ObjectName.names)

private def termsFormed : Derivation signature.{v} (.object terms) :=
  .objectName (signature := signature) (ULift.up ObjectName.terms)

def headers : HeaderFormation signature.{v} where
  source origin := by
    change Derivation signature (.object (constructorSource origin.down))
    cases origin with
    | up origin =>
      cases origin with
      | reference => exact namesFormed
      | abstraction => exact .exponentialObject namesFormed termsFormed
      | application => exact .productObject termsFormed namesFormed
      | definition => exact .productObject termsFormed (.exponentialObject namesFormed termsFormed)
      | carrier => exact .productObject namesFormed (.productObject termsFormed termsFormed)
  target _ := termsFormed
  left origin := nomatch origin.down
  right origin := nomatch origin.down

def nameObject : GeneratedCategory.Object signature.{v} := ⟨names, ⟨namesFormed⟩⟩
def termObject : GeneratedCategory.Object signature.{v} := ⟨terms, ⟨termsFormed⟩⟩

def constructorDomain (constructor : Constructor) : GeneratedCategory.Object signature.{v} :=
  ⟨constructorSource constructor, ⟨headers.source (ULift.up constructor)⟩⟩

def constructorArrow (constructor : Constructor) :
    GeneratedCategory.RawHom (constructorDomain.{v} constructor) termObject.{v} :=
  ⟨.name (ULift.up constructor), ⟨.arrowName (signature := signature) (ULift.up constructor)
    (headers.source (ULift.up constructor)) (headers.target (ULift.up constructor))⟩⟩

def sourceTheory : Mettapedia.GSLT.Core.LambdaTheory.{v, v} :=
  Mettapedia.GSLT.Core.LambdaTheory.ofCategory (GeneratedCategory.Object signature.{v})

variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]

private def emptyBaseFunctor : Base.{v} ⥤ C where
  obj object := isEmptyElim object
  map {source} _ := isEmptyElim source
  map_id object := isEmptyElim object
  map_comp {source} _ _ := isEmptyElim source

def constructorValue (operations : Operations C) : Constructor → Interpretation.ArrowValue C
  | .reference => ⟨operations.names, operations.termObject, operations.reference⟩
  | .abstraction => ⟨operations.boundBodyObject, operations.termObject, operations.abstraction⟩
  | .application => ⟨operations.termObject ⊗ operations.names, operations.termObject, operations.application⟩
  | .definition => ⟨operations.termObject ⊗ operations.boundBodyObject, operations.termObject, operations.definition⟩
  | .carrier => ⟨operations.names ⊗ (operations.termObject ⊗ operations.termObject),
      operations.termObject, operations.carrier⟩

def assignment (operations : Operations C) : Interpretation.Assignment Base.{v} symbols.{v} C where
  base := emptyBaseFunctor
  object origin := match origin.down with
    | .names => operations.names
    | .terms => operations.termObject
  arrow origin := constructorValue operations origin.down

/-- Only the five local constructor header reads are checked here. Whole
syntax soundness and constructor/limit/closed preservation are supplied by
the earned interpretation theorem, not by any field of this realization. -/
theorem realization (operations : Operations C) :
    Interpretation.Realization signature.{v} (assignment operations) where
  source origin := by cases origin with | up origin => cases origin <;> rfl
  target origin := by cases origin with | up origin => cases origin <;> rfl
  equation origin := nomatch origin.down

set_option backward.isDefEq.respectTransparency false in
def constructorMap (operations : Operations C) :
    Mettapedia.GSLT.Core.LambdaTheoryMap sourceTheory.{v}
      (Mettapedia.GSLT.Core.LambdaTheory.ofCategory C) where
  functor := Interpretation.functor (assignment operations) (realization operations)
  preservesFiniteLimits := Interpretation.functor_preservesFiniteLimits
    (assignment operations) (realization operations)
  preservesExponentials := Interpretation.functor_closed
    (assignment operations) (realization operations)

theorem name_object_readout (operations : Operations C) :
    (constructorMap operations).functor.obj nameObject.{v} = operations.names := by
  exact Interpretation.objectValue_unique (assignment operations) (realization operations) nameObject _ rfl

/-- The interpreted term sort is genuinely an exponential object. It is
not replaced by the target process object. -/
theorem term_object_readout (operations : Operations C) :
    (constructorMap operations).functor.obj termObject.{v} =
      (operations.names ⟶[C] operations.processes) := by
  exact Interpretation.objectValue_unique (assignment operations) (realization operations) termObject _ rfl

theorem complete_constructor_readout (operations : Operations C) (constructor : Constructor) :
    ((⟨(constructorMap operations).functor.obj (constructorDomain constructor),
      (constructorMap operations).functor.obj termObject,
      (constructorMap operations).functor.map (GeneratedCategory.classOf (constructorArrow constructor))⟩ :
        Interpretation.ArrowValue C)) = constructorValue operations constructor := by
  have whole := Interpretation.functor_complete_readout (assignment operations) (realization operations)
    (constructorArrow constructor)
  have primitive : (assignment operations).evaluateArrow (constructorArrow constructor).code =
      some (constructorValue operations constructor) := rfl
  exact Option.some.inj (whole.symm.trans primitive)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingConstructorClassifying
