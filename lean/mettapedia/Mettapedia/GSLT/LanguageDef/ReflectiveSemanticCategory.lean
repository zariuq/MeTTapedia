import Mettapedia.GSLT.Core.GSLT
import Mettapedia.GSLT.LanguageDef.SemanticCategory
import Mettapedia.GSLT.LanguageDef.ReflectionExtension
import Mettapedia.GSLT.LanguageDef.ReflectiveEquationSemantics
import Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted
import Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep

/-!
# Behavioral semantics of an admitted reflection extension

The ordinary semantic construction depends only on the five-field language.
This module gives the corresponding construction when an independently
admitted reflection profile is interpreted.  Both the carrier's quote-scope
obligation and the rule/equation interpretation name that profile explicitly.
-/

namespace Mettapedia.GSLT.LanguageDef.ReflectiveSemanticCategory

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.GSLT.LanguageDef.ReflectiveEquationSemantics
open Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.OSLF.MeTTaIL.Syntax

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

/-- The behavioral GSLT induced by a presentation and admitted reflection. -/
def presentedGSLT
    (base : BasePremiseEvaluator) (presentation : InteractivePresentation)
    (reflection : AdmittedProfile presentation.presentation.language) : GSLT where
  Term := Term presentation reflection
  equations := presentedEquationSetoid base presentation reflection
  rewrites := presentedStep base presentation reflection
  rewrites_resp_left := presentedStep_resp_left base presentation reflection
  rewrites_resp_right := presentedStep_resp_right base presentation reflection

end Mettapedia.GSLT.LanguageDef.ReflectiveSemanticCategory
