import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.FiniteStaticCanonicalAction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.FiniteReflectiveInventory
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SynchronousStaticSourceTerm

/-!
# Typed finite synchronous static action on source equations

Every supported authored equation edge is carried to one actual reflective
edge between typed generated terms. Boundary values are arbitrary admitted
finite target terms; their typing is not restricted to an asynchronous image.
This is a static-frame action, not yet a retained-tree substitution operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.StaticSource
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open ContinuationDecorationProfile ReflectionExtension

variable {color : CostStaticColor} {free targetFree : FreeTypeContext}
  {support : ContextSupport.Support} {sourceBound targetBound : List TypeExpr}
  {sort : LangSort rhoSyncCalc}

/-- Exact canonical representatives are preserved in the shared action fibre. -/
theorem action_canonicalize_eq
    (left right : communicationDecoration.StaticSourceTerm FiniteWhole.sourceReflection
      color free support sourceBound targetBound sort)
    (thinning : CostStaticTypeThinning rhoSyncIGSLT color sourceBound targetBound)
    (assignment : SupportedOpenAssignment
      (communicationDecoration.costWholeReflectionProfile FiniteWhole.sourceReflection.1)
      communicationDecoration.costWholeLanguage (free.map (color.symbolsOf rhoSyncIGSLT))
      targetFree support)
    (same : canonicalize rhoReflectivePresentation left.term.1 =
      canonicalize rhoReflectivePresentation right.term.1) :
    canonicalize (FiniteStaticCanonicalAction.declaration rhoSyncIGSLT color)
      (left.actAvailable FiniteStaticTypingControls.synchronous_nonprincipal
        CanonicalInventory.synchronous_bareConstructorsAllowed thinning assignment).pattern =
    canonicalize (FiniteStaticCanonicalAction.declaration rhoSyncIGSLT color)
      (right.actAvailable FiniteStaticTypingControls.synchronous_nonprincipal
        CanonicalInventory.synchronous_bareConstructorsAllowed thinning assignment).pattern := by
  have leftAction := FiniteStaticCanonicalAction.canonicalize_action communicationDecoration
    CanonicalInventory.synchronous FiniteWhole.sourceReflection.2
    FiniteStaticTypingControls.synchronous_nonprincipal
    CanonicalInventory.synchronous_bareConstructorsAllowed
    CanonicalInventory.synchronous_reflectiveConstructorsAllowed
    FiniteReflectiveInventory.nameResultsQuoted (inner := []) (available := targetBound)
    thinning assignment left.term.2.1.1 left.safe left.supported.constructorsWithin
    left.term.2.1.2.2.1
  have rightAction := FiniteStaticCanonicalAction.canonicalize_action communicationDecoration
    CanonicalInventory.synchronous FiniteWhole.sourceReflection.2
    FiniteStaticTypingControls.synchronous_nonprincipal
    CanonicalInventory.synchronous_bareConstructorsAllowed
    CanonicalInventory.synchronous_reflectiveConstructorsAllowed
    FiniteReflectiveInventory.nameResultsQuoted (inner := []) (available := targetBound)
    thinning assignment right.term.2.1.1 right.safe right.supported.constructorsWithin
    right.term.2.1.2.2.1
  rw [same] at leftAction
  change canonicalize (FiniteStaticCanonicalAction.declaration rhoSyncIGSLT color)
      (FiniteStaticCanonicalAction.actionAt communicationDecoration color thinning assignment
        [] targetBound left.term.1) =
    canonicalize (FiniteStaticCanonicalAction.declaration rhoSyncIGSLT color)
      (FiniteStaticCanonicalAction.actionAt communicationDecoration color thinning assignment
        [] targetBound right.term.1)
  exact leftAction.trans rightAction.symm

/-- A source generator gives one target generator, whose endpoints already
carry the full target typing, metadata, object and reflective scope evidence. -/
theorem action_generator
    (left right : communicationDecoration.StaticSourceTerm FiniteWhole.sourceReflection
      color free support sourceBound targetBound sort)
    (thinning : CostStaticTypeThinning rhoSyncIGSLT color sourceBound targetBound)
    (assignment : SupportedOpenAssignment
      (communicationDecoration.costWholeReflectionProfile FiniteWhole.sourceReflection.1)
      communicationDecoration.costWholeLanguage (free.map (color.symbolsOf rhoSyncIGSLT))
      targetFree support)
    (generator : StaticSourceTerm.generator left right) :
    AvailableOpenPattern.equationGenerator
      (left.actAvailable FiniteStaticTypingControls.synchronous_nonprincipal
        CanonicalInventory.synchronous_bareConstructorsAllowed thinning assignment)
      (right.actAvailable FiniteStaticTypingControls.synchronous_nonprincipal
        CanonicalInventory.synchronous_bareConstructorsAllowed thinning assignment) := by
  have sourceSame := CanonicalInventory.synchronous.equationContextStep_canonicalize_eq
    (fun _ member => member) generator
  have same := action_canonicalize_eq left right thinning assignment
    (by simpa only [CanonicalMatch.derivedCanonicalize_eq] using sourceSame)
  apply ReflectiveEquationSemantics.ReflectiveEquationContextStep.reflectiveInContext .hole
    (FiniteStaticCanonicalAction.declaration_mem communicationDecoration color)
  exact same

/-- Every source path is transported through actual typed intermediate frames. -/
theorem action_equationSetoid
    (left right : communicationDecoration.StaticSourceTerm FiniteWhole.sourceReflection
      color free support sourceBound targetBound sort)
    (thinning : CostStaticTypeThinning rhoSyncIGSLT color sourceBound targetBound)
    (assignment : SupportedOpenAssignment
      (communicationDecoration.costWholeReflectionProfile FiniteWhole.sourceReflection.1)
      communicationDecoration.costWholeLanguage (free.map (color.symbolsOf rhoSyncIGSLT))
      targetFree support)
    (equivalent : StaticSourceTerm.equationSetoid.r left right) :
    (AvailableOpenPattern.equationSetoid communicationDecoration.costWholeLanguage targetFree
      targetBound [] (mapTypeExpr (color.symbolsOf rhoSyncIGSLT) (.base sort.1))).r
      (left.actAvailable FiniteStaticTypingControls.synchronous_nonprincipal
        CanonicalInventory.synchronous_bareConstructorsAllowed thinning assignment)
      (right.actAvailable FiniteStaticTypingControls.synchronous_nonprincipal
        CanonicalInventory.synchronous_bareConstructorsAllowed thinning assignment) := by
  induction equivalent with
  | rel left right edge =>
      exact Relation.EqvGen.rel _ _ (action_generator left right thinning assignment edge)
  | refl term => exact Relation.EqvGen.refl _
  | symm left right _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans left middle right _ _ first second => exact Relation.EqvGen.trans _ _ _ first second

/-- Normalization of an actual source frame is absorbed by its typed action
in one generated reflective edge. -/
theorem action_normalize_generator
    (term : communicationDecoration.StaticSourceTerm FiniteWhole.sourceReflection
      color free support sourceBound targetBound sort)
    (thinning : CostStaticTypeThinning rhoSyncIGSLT color sourceBound targetBound)
    (assignment : SupportedOpenAssignment
      (communicationDecoration.costWholeReflectionProfile FiniteWhole.sourceReflection.1)
      communicationDecoration.costWholeLanguage (free.map (color.symbolsOf rhoSyncIGSLT))
      targetFree support) :
    AvailableOpenPattern.equationGenerator
      ((normalize term).actAvailable FiniteStaticTypingControls.synchronous_nonprincipal
        CanonicalInventory.synchronous_bareConstructorsAllowed thinning assignment)
      (term.actAvailable FiniteStaticTypingControls.synchronous_nonprincipal
        CanonicalInventory.synchronous_bareConstructorsAllowed thinning assignment) :=
  action_generator (normalize term) term thinning assignment (normalize_generator term)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.StaticSource
