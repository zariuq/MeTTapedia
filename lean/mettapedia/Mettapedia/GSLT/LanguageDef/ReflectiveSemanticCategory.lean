import Mettapedia.GSLT.Core.GSLT
import Mettapedia.GSLT.LanguageDef.SemanticCategory
import Mettapedia.GSLT.LanguageDef.ReflectionExtension
import Mettapedia.GSLT.LanguageDef.ReflectiveEquationSemantics
import Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted
import Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Behavioral semantics of an explicitly interpreted presentation

A five-field language presents constructors, equations, rewrites, and
premises; it does not by itself choose how reflective matching or substitution
is interpreted.  This module pairs one exact interactive presentation with an
independently admitted interpretation and makes that dependent pair the sole
input to the semantic GSLT constructor in this layer.  Both the carrier's
quote-scope obligation and the rule/equation interpretation therefore name the
same admitted profile explicitly.
-/

namespace Mettapedia.GSLT.LanguageDef.ReflectiveSemanticCategory

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.GSLT.LanguageDef.ReflectiveEquationSemantics
open Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- An exact interactive presentation together with the admitted semantic
interpretation of its reflective declarations.  The dependent field prevents
an interpretation validated for one language from being attached to another.

The empty interpretation is a genuine selected point of the same fibre; it is
not an implicit fallback semantics. -/
structure InterpretedPresentation where
  presentation : InteractivePresentation
  interpretation : AdmittedProfile presentation.presentation.language

namespace InterpretedPresentation

/-- Explicitly select the reflection-free interpretation of a presentation. -/
def structural (presentation : InteractivePresentation) :
    InterpretedPresentation where
  presentation := presentation
  interpretation := emptyAdmitted presentation.presentation.language

end InterpretedPresentation

/-- Closed terms at the selected sort under an admitted reflection profile. -/
abbrev Term (presentation : InteractivePresentation)
    (reflection : AdmittedProfile presentation.presentation.language) :=
  ReflectiveWellSorted.ClosedTerm reflection.1
    presentation.presentation.language presentation.interactingLangSort

/-- One core or reflective equation generator inside the admitted carrier. -/
def presentedEquationGenerator
    (base : BasePremiseEvaluator) (presentation : InteractivePresentation)
    (reflection : AdmittedProfile presentation.presentation.language)
    (left right : Term presentation reflection) : Prop :=
  ReflectiveEquationContextStep reflection.1 base
    presentation.presentation.language left.1 right.1

/-- Static equivalence generated inside the admitted reflective carrier. -/
def presentedEquationSetoid
    (base : BasePremiseEvaluator) (presentation : InteractivePresentation)
    (reflection : AdmittedProfile presentation.presentation.language) :
    Setoid (Term presentation reflection) where
  r := Relation.EqvGen
    (presentedEquationGenerator base presentation reflection)
  iseqv :=
    { refl := Relation.EqvGen.refl
      symm := fun relation => Relation.EqvGen.symm _ _ relation
      trans := fun first second => Relation.EqvGen.trans _ _ _ first second }

/-- Least contextual reduction under the admitted rule interpretation. -/
def presentedPrimitiveStep
    (base : BasePremiseEvaluator) (presentation : InteractivePresentation)
    (reflection : AdmittedProfile presentation.presentation.language)
    (source target : Term presentation reflection) : Prop :=
  Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step
    (.reflection reflection.1) base
    presentation.presentation.language source.1 target.1

/-- Reflective reduction saturated by reflective static equivalence. -/
def presentedStep
    (base : BasePremiseEvaluator) (presentation : InteractivePresentation)
    (reflection : AdmittedProfile presentation.presentation.language)
    (source target : Term presentation reflection) : Prop :=
  ∃ redex contractum : Term presentation reflection,
    (presentedEquationSetoid base presentation reflection).r source redex ∧
    presentedPrimitiveStep base presentation reflection redex contractum ∧
    (presentedEquationSetoid base presentation reflection).r contractum target

theorem presentedStep_resp_left
    (base : BasePremiseEvaluator) (presentation : InteractivePresentation)
    (reflection : AdmittedProfile presentation.presentation.language) :
    ∀ {source source' target : Term presentation reflection},
      (presentedEquationSetoid base presentation reflection).r source source' →
      presentedStep base presentation reflection source target →
      ∃ target', presentedStep base presentation reflection source' target' ∧
        (presentedEquationSetoid base presentation reflection).r target target' := by
  intro source source' target sourceEquivalent
  rintro ⟨redex, contractum, redexEquivalent, primitive, targetEquivalent⟩
  refine ⟨target, ⟨redex, contractum, ?_, primitive, targetEquivalent⟩, ?_⟩
  · exact (presentedEquationSetoid base presentation reflection).iseqv.trans
      ((presentedEquationSetoid base presentation reflection).iseqv.symm
        sourceEquivalent) redexEquivalent
  · exact (presentedEquationSetoid base presentation reflection).iseqv.refl target

theorem presentedStep_resp_right
    (base : BasePremiseEvaluator) (presentation : InteractivePresentation)
    (reflection : AdmittedProfile presentation.presentation.language) :
    ∀ {source target target' : Term presentation reflection},
      presentedStep base presentation reflection source target →
      (presentedEquationSetoid base presentation reflection).r target target' →
      presentedStep base presentation reflection source target' := by
  intro source target target'
  rintro ⟨redex, contractum, redexEquivalent, primitive, targetEquivalent⟩
    equivalent
  exact ⟨redex, contractum, redexEquivalent, primitive,
    (presentedEquationSetoid base presentation reflection).iseqv.trans
      targetEquivalent equivalent⟩

/-- The one semantic GSLT constructor for an interpreted presentation.  Static
equations and directed reduction share the interpretation stored in the same
dependent package; OSLF may subsequently be generated from the resulting
GSLT without another language-specific semantics choice. -/
def InterpretedPresentation.toGSLTUsing
    (semantics : InterpretedPresentation)
    (base : BasePremiseEvaluator) : GSLT where
  Term := Term semantics.presentation semantics.interpretation
  equations := presentedEquationSetoid base semantics.presentation
    semantics.interpretation
  rewrites := presentedStep base semantics.presentation semantics.interpretation
  rewrites_resp_left := presentedStep_resp_left base semantics.presentation
    semantics.interpretation
  rewrites_resp_right := presentedStep_resp_right base semantics.presentation
    semantics.interpretation

/-- The one-sorted operational interface of an explicitly interpreted
presentation.  This is only an adapter around `toGSLTUsing`; it introduces no
second reduction or equation semantics. -/
def InterpretedPresentation.toRewriteSystemUsing
    (semantics : InterpretedPresentation)
    (base : BasePremiseEvaluator) : Mettapedia.OSLF.Framework.RewriteSystem :=
  gsltRewriteSystem (semantics.toGSLTUsing base)

/-- Generate OSLF only after the presentation's interpretation has been
selected and admitted.  The result is definitionally the sole abstract
`GSLT -> OSLF` construction. -/
def InterpretedPresentation.toOSLFUsing
    (semantics : InterpretedPresentation)
    (base : BasePremiseEvaluator) :
    Mettapedia.OSLF.Framework.OSLFTypeSystem
      (semantics.toRewriteSystemUsing base) :=
  gsltOSLF (semantics.toGSLTUsing base)

/-- Native types generated from the explicitly interpreted presentation. -/
def InterpretedPresentation.NativeTypeUsing
    (semantics : InterpretedPresentation)
    (base : BasePremiseEvaluator) :=
  Mettapedia.OSLF.Framework.NativeTypeOf (semantics.toOSLFUsing base)

@[simp]
theorem InterpretedPresentation.toOSLFUsing_eq_gsltOSLF
    (semantics : InterpretedPresentation)
    (base : BasePremiseEvaluator) :
    semantics.toOSLFUsing base = gsltOSLF (semantics.toGSLTUsing base) :=
  rfl

end Mettapedia.GSLT.LanguageDef.ReflectiveSemanticCategory
