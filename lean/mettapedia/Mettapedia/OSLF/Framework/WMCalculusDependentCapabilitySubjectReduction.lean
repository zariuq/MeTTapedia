import Mettapedia.OSLF.Framework.WMCalculusNativeCapability

/-!
# Dependent supported-answer preservation under WM computation

A capability may depend on both the current state and the queried value.
When both arguments compute contextually, the WM core laws preserve their
denotations up to the appropriate sorted agreement. Observationally coherent
support therefore remains equivalent, and the same checked evidence value
inhabits the supported dependent answer graph after computation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusDependentCapabilitySubjectReduction

open _root_.CategoryTheory
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusSemantics.WMReading
open Mettapedia.OSLF.Framework.WMCalculusNativeCapability
open Mettapedia.OSLF.Framework.LangMorphism

private abbrev wmLanguage : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef :=
  wmExtVertexLanguageDefWithCong wmExtVertexMinimal

variable {State Query V : Type} {R : WMReading State Query V}
  (laws : R.CoreLaws) (capability : WMCapability R)
include laws

/-- A pair of independently contextual WM reductions preserves support.
The query side may compute too; its denotation is equal, while state
denotation need only agree observationally. -/
theorem support_iff_of_pair_steps
    {state₁ state₂ : WMTerm .state}
    {query₁ query₂ : WMTerm .query}
    (stateSteps : WMContextStepStar state₁ state₂)
    (querySteps : WMContextStepStar query₁ query₂) :
    capability.supports (R.denote state₁) (R.denote query₁) ↔
      capability.supports (R.denote state₂) (R.denote query₂) := by
  have stateAgree := laws.agree_of_contextStepStar stateSteps
  have queryEqual := laws.agree_of_contextStepStar querySteps
  change R.denote query₁ = R.denote query₂ at queryEqual
  rw [queryEqual]
  exact capability.respectsAgree _ _ _ stateAgree

/-- The extracted answer is stable when *both* the state term and the
query term compute. -/
theorem extraction_eq_of_pair_steps
    {state₁ state₂ : WMTerm .state}
    {query₁ query₂ : WMTerm .query}
    (stateSteps : WMContextStepStar state₁ state₂)
    (querySteps : WMContextStepStar query₁ query₂) :
    R.extract (R.denote state₁) (R.denote query₁) =
      R.extract (R.denote state₂) (R.denote query₂) := by
  have stateAgree := laws.agree_of_contextStepStar stateSteps
  have queryEqual := laws.agree_of_contextStepStar querySteps
  change R.denote query₁ = R.denote query₂ at queryEqual
  rw [queryEqual]
  exact stateAgree _

/-- Subject reduction for the dependent supported-answer family, with
the evidence value itself preserved rather than a fresh default answer. -/
theorem supportedGraph_pair_steps
    (X : Opposite (ConstructorObj wmLanguage))
    {state₁ state₂ : WMTerm .state}
    {query₁ query₂ : WMTerm .query}
    (stateSteps : WMContextStepStar state₁ state₂)
    (querySteps : WMContextStepStar query₁ query₂)
    (value : V) :
    ((R.denote state₁, R.denote query₁), value) ∈
        (supportedGraph capability).obj X ↔
      ((R.denote state₂, R.denote query₂), value) ∈
        (supportedGraph capability).obj X := by
  change
    (capability.supports (R.denote state₁) (R.denote query₁) ∧
      R.extract (R.denote state₁) (R.denote query₁) = value) ↔
    (capability.supports (R.denote state₂) (R.denote query₂) ∧
      R.extract (R.denote state₂) (R.denote query₂) = value)
  rw [support_iff_of_pair_steps laws capability stateSteps querySteps,
    extraction_eq_of_pair_steps laws stateSteps querySteps]

/-- The same result applies to reducts of the *authored* contextual
LanguageDef presentation, after its adequacy theorem reconstructs typed
WM terms from the resulting patterns. -/
theorem supportedGraph_authored_reducts
    (X : Opposite (ConstructorObj wmLanguage))
    (stateTerm : WMTerm .state) (queryTerm : WMTerm .query)
    {statePattern queryPattern : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (stateReduces : LangReducesStar
      wmLanguage (encodeWM stateTerm) statePattern)
    (queryReduces : LangReducesStar
      wmLanguage (encodeWM queryTerm) queryPattern)
    (value : V) :
    ∃ stateReduct : WMTerm .state,
      ∃ queryReduct : WMTerm .query,
        encodeWM stateReduct = statePattern ∧
        encodeWM queryReduct = queryPattern ∧
        (((R.denote stateTerm, R.denote queryTerm), value) ∈
            (supportedGraph capability).obj X ↔
          ((R.denote stateReduct, R.denote queryReduct), value) ∈
            (supportedGraph capability).obj X) := by
  obtain ⟨stateReduct, stateEncoded, stateAgree⟩ :=
    laws.contextual_reduct_agrees stateTerm stateReduces
  obtain ⟨queryReduct, queryEncoded, queryAgree⟩ :=
    laws.contextual_reduct_agrees queryTerm queryReduces
  refine ⟨stateReduct, queryReduct, stateEncoded, queryEncoded, ?_⟩
  have queryEqual : R.denote queryTerm = R.denote queryReduct := queryAgree
  change
    (capability.supports (R.denote stateTerm) (R.denote queryTerm) ∧
      R.extract (R.denote stateTerm) (R.denote queryTerm) = value) ↔
    (capability.supports (R.denote stateReduct) (R.denote queryReduct) ∧
      R.extract (R.denote stateReduct) (R.denote queryReduct) = value)
  rw [queryEqual]
  rw [capability.respectsAgree _ _ _ stateAgree, stateAgree]

end Mettapedia.OSLF.Framework.WMCalculusDependentCapabilitySubjectReduction
