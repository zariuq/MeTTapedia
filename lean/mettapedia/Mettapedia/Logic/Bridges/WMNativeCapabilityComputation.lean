import Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTIL
import Mettapedia.OSLF.Framework.WMCalculusDependentCapabilitySubjectReduction

/-!
# Proof-relevant capability answers under WM computation

Contextual computation of both sides of a WM request transports the actual
GSLT-IL chain witness, not only membership in its extensional answer graph.
The semantic middle request changes with the reduct, while its denotation
receipt, capability proof, and checked evidence value remain valid. The same
transport applies to reducts of the authored contextual LanguageDef through
its completeness theorem. This is extensional receipt transport, not a claim
to retain an operational derivation or occurrence trace.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.WMNativeCapabilityComputation

open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusSemantics.WMReading
open Mettapedia.OSLF.Framework.WMCalculusNativeCapability
open Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTIL

variable {State Query V : Type} {R : WMReading State Query V}
    (capability : WMCapability R)

/-- Transport a chained capability receipt between observationally agreeing
states and equal queries. The new middle request is the denotation of the
target terms, not an erased existential chosen after the fact. -/
def transportChainEvidenceOfAgree
    {state₁ state₂ : WMTerm .state} {query₁ query₂ : WMTerm .query}
    (stateAgree : R.Agree .state (R.denote state₁) (R.denote state₂))
    (queryEqual : R.denote query₁ = R.denote query₂)
    (answer : V) :
    (termCapabilityChain capability).evidence (state₁, query₁) answer →
      (termCapabilityChain capability).evidence (state₂, query₂) answer := by
  rintro ⟨request, pairReceipt, answerReceipt⟩
  cases pairReceipt.checked
  refine ⟨(R.denote state₂, R.denote query₂), ⟨rfl⟩, ?_⟩
  refine ⟨?_, ?_⟩
  · rw [← queryEqual]
    exact (capability.respectsAgree _ _ _ stateAgree).1 answerReceipt.supported
  · rw [← queryEqual, ← stateAgree (R.denote query₁)]
    exact answerReceipt.checked

/-- The receipt transport also runs backwards, because WM agreement is
symmetric. No reverse *operational step* is inferred. -/
def transportChainEvidenceOfAgreeSymm
    {state₁ state₂ : WMTerm .state} {query₁ query₂ : WMTerm .query}
    (stateAgree : R.Agree .state (R.denote state₁) (R.denote state₂))
    (queryEqual : R.denote query₁ = R.denote query₂)
    (answer : V) :
    (termCapabilityChain capability).evidence (state₂, query₂) answer →
      (termCapabilityChain capability).evidence (state₁, query₁) answer :=
  transportChainEvidenceOfAgree capability
    (R.agree_symm .state stateAgree) queryEqual.symm answer

/-- A chain witness has no occurrence multiplicity: the checked middle
request is forced by syntax, and the remaining proof fields are propositions.
This is why the two observational transports give an equivalence of fibres. -/
theorem chainEvidence_subsingleton
    (terms : WMTerm .state × WMTerm .query) (answer : V) :
    Subsingleton ((termCapabilityChain capability).evidence terms answer) := by
  constructor
  rintro ⟨request₁, pair₁, receipt₁⟩ ⟨request₂, pair₂, receipt₂⟩
  cases pair₁.checked
  cases pair₂.checked
  have pairsEqual : pair₁ = pair₂ := by
    cases pair₁
    cases pair₂
    rfl
  cases pairsEqual
  have receiptsEqual : receipt₁ = receipt₂ := by
    cases receipt₁
    cases receipt₂
    rfl
  cases receiptsEqual
  rfl

/-- Observational agreement induces an equivalence of the dependent
GSLT-IL evidence fibres at a fixed answer. The equivalence is not an
equivalence of execution traces, which these fibres do not store. -/
def chainEvidenceEquivOfAgree
    {state₁ state₂ : WMTerm .state} {query₁ query₂ : WMTerm .query}
    (stateAgree : R.Agree .state (R.denote state₁) (R.denote state₂))
    (queryEqual : R.denote query₁ = R.denote query₂)
    (answer : V) :
    (termCapabilityChain capability).evidence (state₁, query₁) answer ≃
      (termCapabilityChain capability).evidence (state₂, query₂) answer where
  toFun := transportChainEvidenceOfAgree capability stateAgree queryEqual answer
  invFun := transportChainEvidenceOfAgreeSymm capability stateAgree queryEqual answer
  left_inv := by
    intro witness
    exact (chainEvidence_subsingleton capability _ answer).allEq _ _
  right_inv := by
    intro witness
    exact (chainEvidence_subsingleton capability _ answer).allEq _ _

/-- Independent contextual reductions of state and query induce the
dependent receipt equivalence, at the same evidence value. -/
def chainEvidenceEquivOfPairSteps (laws : R.CoreLaws)
    {state₁ state₂ : WMTerm .state} {query₁ query₂ : WMTerm .query}
    (stateSteps : WMContextStepStar state₁ state₂)
    (querySteps : WMContextStepStar query₁ query₂)
    (answer : V) :
    (termCapabilityChain capability).evidence (state₁, query₁) answer ≃
      (termCapabilityChain capability).evidence (state₂, query₂) answer := by
  have stateAgree := laws.agree_of_contextStepStar stateSteps
  have queryEqual := laws.agree_of_contextStepStar querySteps
  change R.denote query₁ = R.denote query₂ at queryEqual
  exact chainEvidenceEquivOfAgree capability stateAgree queryEqual answer

/-- Authored contextual reductions reconstruct typed target terms and an
equivalence of their complete syntax-to-capability answer fibres. -/
theorem chainEvidenceEquivOfAuthoredReducts (laws : R.CoreLaws)
    (stateTerm : WMTerm .state) (queryTerm : WMTerm .query)
    {statePattern queryPattern : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (stateReduces : LangReducesStar
      (wmExtVertexLanguageDefWithCong
        Mettapedia.OSLF.Framework.WMCalculusLanguageDef.wmExtVertexMinimal)
      (encodeWM stateTerm) statePattern)
    (queryReduces : LangReducesStar
      (wmExtVertexLanguageDefWithCong
        Mettapedia.OSLF.Framework.WMCalculusLanguageDef.wmExtVertexMinimal)
      (encodeWM queryTerm) queryPattern)
    (answer : V) :
    ∃ stateReduct : WMTerm .state,
      ∃ queryReduct : WMTerm .query,
        encodeWM stateReduct = statePattern ∧
        encodeWM queryReduct = queryPattern ∧
        Nonempty ((termCapabilityChain capability).evidence
          (stateTerm, queryTerm) answer ≃
          (termCapabilityChain capability).evidence
            (stateReduct, queryReduct) answer) := by
  obtain ⟨stateReduct, stateSteps, stateEncoded⟩ :=
    wmContextStepStar_complete stateTerm stateReduces
  obtain ⟨queryReduct, querySteps, queryEncoded⟩ :=
    wmContextStepStar_complete queryTerm queryReduces
  exact ⟨stateReduct, queryReduct, stateEncoded, queryEncoded,
    ⟨chainEvidenceEquivOfPairSteps capability laws
      stateSteps querySteps answer⟩⟩

end Mettapedia.Logic.Bridges.WMNativeCapabilityComputation
