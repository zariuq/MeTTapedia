import Mettapedia.Logic.Bridges.WMNativeGSLTIL
import Mettapedia.OSLF.Framework.WMCalculusReadingMorphism

/-!
# Reading maps preserve the proof-relevant WM answer route

A WM-reading morphism acts on the dependent answer graph in the native
predicate category. Here the same morphism acts on the GSLT-IL route without
erasing its intermediate state-query request or either checked receipt.
It gives a forward map of evidence fibres. No converse or equivalence of
proof histories is inferred from mere operation preservation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.WMNativeGSLTILMorphism

open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusReadingMorphism
open Mettapedia.Logic.Bridges.WMNativeGSLTIL

variable {State₁ Query₁ V₁ State₂ Query₂ V₂ : Type}
  {source : WMReading State₁ Query₁ V₁}
  {target : WMReading State₂ Query₂ V₂}
  (hom : ReadingMorphism source target)

/-- The semantic request map underlying the native graph morphism. -/
def mapRequest (request : State₁ × Query₁) : State₂ × Query₂ :=
  (hom.mapState request.1, hom.mapQuery request.2)

/-- A checked answer receipt maps to a checked answer receipt for the
interpreted state-query pair and evidence value. -/
def mapAnswerReceipt (request : State₁ × Query₁) (answer : V₁) :
    AnswerReceipt source request answer →
      AnswerReceipt target (mapRequest hom request) (hom.mapEvidence answer)
  | receipt =>
      ⟨by
        change target.extract (hom.mapState request.1)
          (hom.mapQuery request.2) = hom.mapEvidence answer
        rw [← hom.extract_comm, receipt.checked]⟩

/-- The first route's denotation receipt maps along the same reading
morphism, rather than inventing a fresh unrelated middle object. -/
def mapTermPairReceipt
    (terms : WMTerm .state × WMTerm .query)
    (request : State₁ × Query₁) :
    TermPairReceipt source terms request →
      TermPairReceipt target terms (mapRequest hom request)
  | receipt =>
      ⟨by
        change (target.denote terms.1, target.denote terms.2) =
          (hom.mapState request.1, hom.mapQuery request.2)
        rw [← hom.denote_map terms.1, ← hom.denote_map terms.2]
        exact congrArg (mapRequest hom) receipt.checked⟩

/-- The GSLT-IL chain map retains its actual intermediate request and the
two component witnesses. It is not a function obtained by discarding the
relation's evidence family. -/
def mapTermAnswerEvidence
    (terms : WMTerm .state × WMTerm .query) (answer : V₁) :
    (termAnswerChain source).evidence terms answer →
      (termAnswerChain target).evidence terms (hom.mapEvidence answer)
  | ⟨request, pairReceipt, answerReceipt⟩ =>
      ⟨mapRequest hom request,
        mapTermPairReceipt hom terms request pairReceipt,
        mapAnswerReceipt hom request answer answerReceipt⟩

/-- Consequently, a source route with its checked witnesses always
produces a target route to the mapped evidence. Only this forward
implication is licensed for a general reading morphism. -/
theorem termAnswer_support_forward
    (terms : WMTerm .state × WMTerm .query) (answer : V₁) :
    Nonempty ((termAnswerChain source).evidence terms answer) →
      Nonempty ((termAnswerChain target).evidence terms
        (hom.mapEvidence answer)) := by
  rintro ⟨witness⟩
  exact ⟨mapTermAnswerEvidence hom terms answer witness⟩

end Mettapedia.Logic.Bridges.WMNativeGSLTILMorphism
