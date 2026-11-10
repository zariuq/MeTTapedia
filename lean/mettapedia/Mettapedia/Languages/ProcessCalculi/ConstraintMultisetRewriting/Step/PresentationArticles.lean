import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationCalculus
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationControls

/-!
# Checked transition articles interpret actual effects

The inference definition is extracted from `tcalc.module`. Its generic proof
checker validates a finite open article, and the semantic query gate checks
its premises. Their composite agrees with the effect's admitted events.
Closedness here concerns schema arguments: an object language may encode its
own variables as data, but undeclared schema holes cannot become proof inputs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Interface

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}

theorem article_iff_event (E : EffectCore X O State Firing) (allow : E.Admission)
    (code : Encoding State Firing) (decision : Decisions E allow)
    {s t : State} (f : Firing s)
    (valid : argumentsValidAt [("s", 0), ("f", 0), ("t", 0)]
      [code.state.view (sort := ()) s, code.firing.view (sort := ()) ⟨s, f⟩,
        code.state.view (sort := ()) t] = true) :
    let source := code.state.view (sort := ()) s
    let firing := code.firing.view (sort := ()) ⟨s, f⟩
    let target := code.state.view (sort := ()) t
    Calculus.checkArticle (effectQueries E allow code decision)
      [Calculus.prepared source firing target, Calculus.permitted source firing]
      (Calculus.transition source firing target) (Calculus.article source firing target) = true ↔
        ∃ event : E.Event allow s t, event.firing = f := by
  dsimp only
  rw [Calculus.article_iff_execution _ _ _ _ valid]
  exact execution_iff_event E allow code decision f

namespace ArticleControls

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Controls
open Calculus

def source : Pattern := storePattern []
def firing : Pattern := .apply "Tell" [source]
def target : Pattern := storePattern [(true, false)]
def wrongTarget : Pattern := storePattern [(false, true)]

theorem argument_domain :
    argumentsValidAt [("s", 0), ("f", 0), ("t", 0)] [source, firing, target] = true := by
  decide +kernel

theorem correct_article_accepted :
    checkArticle queries [prepared source firing target, permitted source firing]
      (transition source firing target) (article source firing target) = true := by
  apply execute_article _ _ _ _ argument_domain <;> decide +kernel

theorem correct_article_has_event :
    ∃ event : effect.Event permission [] [(true, false)], event.firing = () := by
  apply (article_iff_event effect permission encoding decisions () argument_domain).mp
  exact correct_article_accepted

/-- The structural checker alone accepts a rule instance with an untrue premise. -/
theorem structural_check_does_not_certify_premises :
    checkOpenRaw validated [prepared source firing wrongTarget, permitted source firing]
      (transition source firing wrongTarget) (article source firing wrongTarget) = true := by
  apply article_checked
  decide +kernel

theorem false_preparation_refused :
    checkArticle queries [prepared source firing wrongTarget, permitted source firing]
      (transition source firing wrongTarget) (article source firing wrongTarget) = false := by
  have refuses : checkMeaning queries (prepared source firing wrongTarget) = false := by
    decide +kernel
  simp [checkArticle, refuses]

theorem wrong_child_order_refused :
    checkOpenRaw validated [prepared source firing target, permitted source firing]
      (transition source firing target)
      (.node (invocation source firing target) [.premise 1, .premise 0]) = false := by
  simp [checkOpenRaw, instantiate_invocation, argument_domain, checkOpenRawChildren,
    prepared, permitted]

theorem missing_permission_refused :
    checkOpenRaw validated [prepared source firing target]
      (transition source firing target) (article source firing target) = false := by
  simp [article, checkOpenRaw, instantiate_invocation, argument_domain, checkOpenRawChildren]

theorem undeclared_hole_refused :
    checkOpenRaw validated [prepared source (.fvar "f") target, permitted source (.fvar "f")]
      (transition source (.fvar "f") target) (article source (.fvar "f") target) = false := by
  have invalid : argumentsValidAt [("s", 0), ("f", 0), ("t", 0)]
      [source, .fvar "f", target] = false := by decide +kernel
  simp [article, checkOpenRaw, instantiate_invocation, invalid]

theorem refused_permission_is_not_a_receipt :
    checkArticle queries
      [prepared target (.apply "Tell" [target]) (storePattern [(true, false), (true, false)]),
       permitted target (.apply "Tell" [target])]
      (transition target (.apply "Tell" [target]) (storePattern [(true, false), (true, false)]))
      (article target (.apply "Tell" [target]) (storePattern [(true, false), (true, false)])) = false := by
  have refuses : checkMeaning queries (permitted target (.apply "Tell" [target])) = false := by
    decide +kernel
  simp [checkArticle, refuses]

end ArticleControls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation
