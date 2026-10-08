import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentSpecifications
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentEvidenceControls
import Mettapedia.TypeTheory.DisplayedPresheafEvidenceApplication

/-!
# Dependent specification readouts of actual compiler certificates

The target caller family is authored independently as a representable on
the compiled program's admissibly indexed element category. A source caller
certificate maps to the corresponding compiled-program arrow. Native sum elimination extends that map
to every retained receipt.

A native function specification additionally returns a caller witness and
an element of `Fin (n + 1)` for each natural argument `n`. Its application
computes the exact translated witness and index. These are semantic native
certificates alongside the actual public-return comparison, not a claim
that the rho program evaluates naturals or checks certificates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentSpecificationControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSliceSubstitution
open DisplayedPresheafSlicePi DisplayedPresheafPi DisplayedPresheafEvidenceApplication
open NamePassingDependentEvidence NamePassingDependentEvidenceControls
open NamePassingDependentSpecifications NamePassingObserverAdequacy

abbrev targetPoint : compiledPrograms.Elements := compilerMap.mapElements.obj sourcePoint

def callerSpecification : DisplayedFamily compiledPrograms :=
  coyoneda.obj (Opposite.op targetPoint)

def sourceCallerReadout : insertionFamily ⟶ reindexDisplayed compilerMap callerSpecification where
  app _ := TypeCat.ofHom (fun origin => compilerMap.mapElements.map origin)
  naturality before after arrow := by
    ext origin
    exact (compilerMap.mapElements.map_comp origin arrow).symm

def callerReadout : compiledFamily insertionFamily ⟶ callerSpecification :=
  realize sourceCallerReadout

theorem callerReadout_computes (point : sourcePrograms.Elements)
    (origin : insertionFamily.obj point) :
    callerReadout.app (compilerMap.mapElements.obj point)
        ((carry insertionFamily).app point origin) = compilerMap.mapElements.map origin :=
  realization_computes sourceCallerReadout point origin

theorem callerReadout_distinguishes_origins :
    callerReadout.app targetPoint ((carry insertionFamily).app sourcePoint immediateOrigin) ≠
      callerReadout.app targetPoint ((carry insertionFamily).app sourcePoint renamedOrigin) := by
  rw [callerReadout_computes, callerReadout_computes]
  intro same
  apply origins_distinct
  apply Subtype.ext
  exact congrArg (fun arrow => arrow.val) same

abbrev arguments : DisplayedFamily compiledPrograms :=
  (Functor.const compiledPrograms.Elements).obj Nat

def argumentSection (n : Nat) : arguments.sections where
  val _ := n
  property _ := rfl

def argumentValue (point : (totalSpace arguments).Elements) : Nat := point.2.2

/-- Natural arguments are unchanged by the actual contextual arrows. -/
theorem argument_preserved {before after : (totalSpace arguments).Elements}
    (arrow : before ⟶ after) : argumentValue before = argumentValue after :=
  congrArg (fun value : (totalSpace arguments).obj after.1 => value.2) arrow.property

def answers : DisplayedFamily (totalSpace arguments) where
  obj point := callerSpecification.obj ((totalProjection arguments).mapElements.obj point) ×
    Fin (argumentValue point + 1)
  map arrow := TypeCat.ofHom (fun answer =>
    ⟨callerSpecification.map ((totalProjection arguments).mapElements.map arrow) answer.1,
      Fin.cast (congrArg (fun n : Nat => n + 1) (argument_preserved arrow)) answer.2⟩)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro answer
    apply Prod.ext
    · exact callerSpecification.map_id_apply _ answer.1
    · apply Fin.ext
      rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro answer
    apply Prod.ext
    · exact callerSpecification.map_comp_apply
        ((totalProjection arguments).mapElements.map first)
        ((totalProjection arguments).mapElements.map second) answer.1
    · apply Fin.ext
      rfl

def answerBody : reindexDisplayed (totalProjection arguments) callerSpecification ⟶ answers where
  app point := TypeCat.ofHom (fun origin => ⟨origin, ⟨argumentValue point, Nat.lt_succ_self _⟩⟩)
  naturality before after arrow := by
    apply ConcreteCategory.hom_ext
    intro origin
    apply Prod.ext
    · rfl
    · apply Fin.ext
      exact (argument_preserved arrow).symm

noncomputable def functionConstructor : callerSpecification ⟶ piDisplayed arguments answers :=
  abstractFamily arguments answers answerBody

theorem functionConstructor_evaluation :
    (reindexFunctor (totalProjection arguments)).map functionConstructor ≫
      (displayedProductAdjunction arguments).counit.app answers = answerBody := by
  exact abstractFamily_evaluation arguments answers answerBody

theorem functionConstructor_value (point : (totalSpace arguments).Elements)
    (origin : callerSpecification.obj ((totalProjection arguments).mapElements.obj point)) :
    ((displayedProductAdjunction arguments).counit.app answers).app point
        (functionConstructor.app ((totalProjection arguments).mapElements.obj point) origin) =
      (⟨origin, ⟨argumentValue point, Nat.lt_succ_self _⟩⟩ : answers.obj point) :=
  abstractFamily_value arguments answers answerBody point origin

theorem functionConstructor_application (point : compiledPrograms.Elements)
    (origin : callerSpecification.obj point) (n : Nat) :
    (applyAt arguments answers (argumentSection n)).app point
        (functionConstructor.app point origin) =
      (⟨origin, ⟨n, Nat.lt_succ_self n⟩⟩ :
        answers.obj ((sectionLift arguments (argumentSection n)).mapElements.obj point)) :=
  functionConstructor_value ((sectionLift arguments (argumentSection n)).mapElements.obj point) origin

noncomputable def functionReadout :
    compiledFamily insertionFamily ⟶ piDisplayed arguments answers :=
  realize (sourceCallerReadout ≫ (reindexFunctor compilerMap).map functionConstructor)

theorem functionReadout_factors : functionReadout = callerReadout ≫ functionConstructor :=
  realization_naturality sourceCallerReadout functionConstructor

/-- Evaluation of the dependent specification returns the supplied target
caller witness and the argument itself, in its argument-dependent finite type. -/
theorem functionReadout_application (point : sourcePrograms.Elements)
    (origin : insertionFamily.obj point) (n : Nat) :
    (applyAt arguments answers (argumentSection n)).app (compilerMap.mapElements.obj point)
      (functionReadout.app (compilerMap.mapElements.obj point)
        ((carry insertionFamily).app point origin)) =
      (⟨compilerMap.mapElements.map origin, ⟨n, Nat.lt_succ_self n⟩⟩ :
        answers.obj ((sectionLift arguments (argumentSection n)).mapElements.obj
          (compilerMap.mapElements.obj point))) := by
  have computes := realization_computes
    (sourceCallerReadout ≫ (reindexFunctor compilerMap).map functionConstructor) point origin
  change functionReadout.app (compilerMap.mapElements.obj point)
      ((carry insertionFamily).app point origin) =
    functionConstructor.app (compilerMap.mapElements.obj point) (compilerMap.mapElements.map origin)
      at computes
  exact (congrArg ((applyAt arguments answers (argumentSection n)).app
    (compilerMap.mapElements.obj point)) computes).trans
      (functionConstructor_application (compilerMap.mapElements.obj point)
        (compilerMap.mapElements.map origin) n)

theorem application_keeps_distinct_origins (n : Nat) :
    (applyAt arguments answers (argumentSection n)).app targetPoint
        (functionReadout.app targetPoint ((carry insertionFamily).app sourcePoint immediateOrigin)) ≠
      (applyAt arguments answers (argumentSection n)).app targetPoint
        (functionReadout.app targetPoint ((carry insertionFamily).app sourcePoint renamedOrigin)) := by
  rw [functionReadout_application, functionReadout_application]
  intro same
  apply callerReadout_distinguishes_origins
  rw [callerReadout_computes, callerReadout_computes]
  exact congrArg Prod.fst same

theorem function_certificate_and_actual_return (n : Nat) :
    ((applyAt arguments answers (argumentSection n)).app targetPoint
      (functionReadout.app targetPoint ((carry insertionFamily).app sourcePoint renamedOrigin))).2.val = n ∧
      ProtocolMayReturn targetPoint.2 := by
  constructor
  · exact congrArg (fun answer => answer.2.val)
      (functionReadout_application sourcePoint renamedOrigin n)
  · exact both_certificates_return

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentSpecificationControls
