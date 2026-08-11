import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.GSLT.LanguageDef.NIKGSLT

/-!
# NIK authority diagrams as indexed operational GSLTs

An authored NIK authority diagram already contains more than a behavioral
map between checker machines: Boolean replay commutes, source steps map to
target steps, and every target step leaving a translated checker state lifts
to a source step.  These are exactly the obligations of a covered operational
translation.

This module exposes that fact once.  It gives an authority diagram the same
indexed operational command semantics and OSLF-generated native types as any
other covered GSLT diagram; it does not add a second checker relation or infer
semantic authority from operational replay.
-/

namespace Mettapedia.GSLT.LanguageDef.NIKGSLT.Indexed

open CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily

universe uKind uClaim uCertificate

namespace CheckerTranslation

variable {Kind : Type uKind} {family : AuthorityFamily Kind}
    {source target : Kind}

/-- A lawful checker translation is an exact covered operational translation
between its two checker GSLTs. -/
def toCoveredTranslation
    (translation : CheckerTranslation family source target) :
    CoveredTranslation (fiberTheory family source)
      (fiberTheory family target) where
  mapTerm := translation.stateMap
  mapEquiv := by
    intro left right equivalent
    cases equivalent
    rfl
  cover :=
    { mapStep := translation.step_map
      liftStep := by
        intro state targetNext step
        obtain ⟨sourceNext, sourceStep, targetEq⟩ :=
          translation.step_cover step
        exact ⟨sourceNext, sourceStep, targetEq.symm⟩ }

@[simp]
theorem toCoveredTranslation_mapTerm
    (translation : CheckerTranslation family source target)
    (state : (fiberTheory family source).Term) :
    translation.toCoveredTranslation.mapTerm state =
      translation.stateMap state :=
  rfl

end CheckerTranslation

namespace AuthorityDiagram

variable {Index : Type uKind} [CategoryTheory.Category Index]
    (diagram : AuthorityDiagram Index)

/-- The authority-bearing diagram, viewed in the stronger covered operational
category.  The objects and transition functions are definitionally the same
checker machines used by NIK. -/
def toCoveredOperationalDiagram : IndexedOperational.CoveredDiagram Index where
  obj kind := ⟨fiberTheory diagram.family kind⟩
  map route := (diagram.transport route).toCoveredTranslation
  map_id kind := by
    apply CoveredTranslation.ext
    funext state
    exact diagram.stateMap_id kind state
  map_comp earlier later := by
    apply CoveredTranslation.ext
    funext state
    exact diagram.stateMap_comp earlier later state

/-- Forget the local-reflection certificate to obtain the general forward
operational diagram consumed by the command calculus. -/
def toOperationalDiagram : IndexedOperational.Diagram Index :=
  diagram.toCoveredOperationalDiagram.toOperational

@[simp]
theorem toOperationalDiagram_obj (kind : Index) :
    (diagram.toOperationalDiagram.obj kind).theory =
      fiberTheory diagram.family kind :=
  rfl

@[simp]
theorem toOperationalDiagram_mapTerm
    {source target : Index} (route : source ⟶ target)
    (state : (fiberTheory diagram.family source).Term) :
    (diagram.toOperationalDiagram.map route).mapTerm state =
      (diagram.transport route).stateMap state :=
  rfl

/-- The single explicit command GSLT obtained from an authority diagram.
`via` is now language-visible control state, while fibre steps remain the
original checker transitions. -/
abbrev commandGSLT :=
  IndexedOperational.Command.commandGSLT diagram.toOperationalDiagram

/-- Every native NIK checker step embeds as an exact fibre step of the
indexed command GSLT. -/
theorem checkerStep_is_commandStep
    (kind : Index)
    {source target : (fiberTheory diagram.family kind).Term}
    (step : (fiberTheory diagram.family kind).Step source target) :
    (diagram.commandGSLT).Step
      (.at kind (Quotient.mk _ source))
      (.at kind (Quotient.mk _ target)) := by
  exact ⟨IndexedOperational.Command.Step.fibre
    (semanticStep_mk step)⟩

/-- Conversely, a command fibre step between authored checker states is an
actual step of the original NIK checker fibre.  Quotienting by the equality
equations of the atomic checker does not enlarge replay behavior. -/
theorem commandStep_between_checkerStates_iff
    (kind : Index)
    (source target : (fiberTheory diagram.family kind).Term) :
    (diagram.commandGSLT).Step
        (.at kind (Quotient.mk _ source))
        (.at kind (Quotient.mk _ target)) ↔
      (fiberTheory diagram.family kind).Step source target := by
  constructor
  · rintro ⟨commandStep⟩
    cases commandStep with
    | fibre semanticStep =>
        exact (semanticStep_mk_iff_step _ source target).mp semanticStep
  · exact diagram.checkerStep_is_commandStep kind

/-- The same checker step inhabits the exact target type generated by OSLF
for the unified NIK command machine. -/
theorem checkerStep_satisfies_generated_nativeType
    (kind : Index)
    {source target : (fiberTheory diagram.family kind).Term}
    (step : (fiberTheory diagram.family kind).Step source target) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      diagram.commandGSLT).satisfies
        (.at kind (Quotient.mk _ source))
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.exactTargetNativeType
          diagram.commandGSLT
          (.at kind (Quotient.mk _ target))).pred := by
  exact IndexedOperational.Command.fibre_satisfies_nativeType
    diagram.toOperationalDiagram (semanticStep_mk step)

/-- OSLF generates the predicate-valued native type of the exact NIK command
machine rather than a parallel hand-authored judgment language. -/
abbrev NativeType :=
  IndexedOperational.Command.NativeType diagram.toOperationalDiagram

end AuthorityDiagram

#print axioms AuthorityDiagram.commandStep_between_checkerStates_iff
#print axioms AuthorityDiagram.checkerStep_satisfies_generated_nativeType

end Mettapedia.GSLT.LanguageDef.NIKGSLT.Indexed
