import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT

/-!
# Authored rho COMM to the derived GSLT

The strict-core rho language is authored by `rhoCalc`.  Its derived process
judgment and quote-aware scope invariant identify its closed process carrier.
This file packages compiler agreement as a step of the GSLT mechanically
derived from that carrier and the authored contextual rules.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLTBridge

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem

/-- Every closed, quote-safe COMM contractum compiled from the single authored
rho declaration is a step of the GSLT derived from that declaration.

The witnesses expose both endpoints on the shared `Pattern` representation so
compiler agreement remains directly inspectable. -/
theorem compiledRhoComm_step
    {channel body payload : Pattern}
    {rest : List Pattern}
    (channelTyped :
      NameWellSorted rhoReflectivePresentation FreeSortContext.empty [] channel)
    (channelSafe : binderSafeAt "NQuote" 0 channel = true)
    (bodyTyped : ProcWellSorted rhoReflectivePresentation FreeSortContext.empty
      [rhoReflectivePresentation.nameSort] body)
    (bodySafe : binderSafeAt "NQuote" 1 body = true)
    (payloadTyped :
      ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] payload)
    (payloadSafe : binderSafeAt "NQuote" 0 payload = true)
    (restTyped :
      ProcListWellSorted rhoReflectivePresentation FreeSortContext.empty [] rest)
    (restSafe : binderSafeListAt "NQuote" 0 rest = true) :
    ∃ source target : RhoProcess,
      source.1 =
        .collection .hashBag
          ([.apply "PInput" [channel, .lambda none body],
            .apply "POutput" [channel, payload]] ++ rest) none ∧
      target.1 = applyBindingsForRule rhoCalc rhoCommRewrite
        (rhoCommBindings channel body payload rest) ∧
      rhoLanguageDefGSLT.Step source target := by
  have sourceTyped :
      ProcWellSorted rhoReflectivePresentation FreeSortContext.empty []
        (.collection .hashBag
          ([.apply "PInput" [channel, .lambda none body],
            .apply "POutput" [channel, payload]] ++ rest) none) := by
    exact .parallel
      (.cons (.input channelTyped bodyTyped)
        (.cons (.output channelTyped payloadTyped) restTyped))
  have sourceSafe :
      binderSafeAt "NQuote" 0
        (.collection .hashBag
          ([.apply "PInput" [channel, .lambda none body],
            .apply "POutput" [channel, payload]] ++ rest) none) = true := by
    simpa [binderSafeAt, binderSafeListAt] using
      ⟨⟨channelSafe, bodySafe⟩, ⟨⟨channelSafe, payloadSafe⟩, restSafe⟩⟩
  let source : RhoProcess :=
    ⟨.collection .hashBag
        ([.apply "PInput" [channel, .lambda none body],
          .apply "POutput" [channel, payload]] ++ rest) none,
      (rhoClosedTermWellSorted_process_iff _).mpr
        ⟨sourceTyped, sourceSafe⟩⟩
  have rawStep : RhoStep source.1
      (.collection .hashBag (semanticCommSubst body payload :: rest) none) := by
    exact RhoStep.comm channel body payload rest bodyTyped payloadTyped
  let target : RhoProcess := source.stepTarget rawStep
  have targetAgreement :
      target.1 = applyBindingsForRule rhoCalc rhoCommRewrite
        (rhoCommBindings channel body payload rest) := by
    rw [applyBindingsForRule_rhoComm_agrees_derived
      bodyTyped payloadTyped channel rest]
    rfl
  refine ⟨source, target, rfl, targetAgreement, ?_⟩
  exact rhoRewriteSystem_reduces_to_gsltStep rawStep

/-- Positive control: the closed nil channel, continuation, and payload
instantiate the authored-to-derived-GSLT bridge. -/
theorem compiledRhoComm_nil_step :
    ∃ source target : RhoProcess,
      source.1 =
        .collection .hashBag
          [.apply "PInput" [closedNilName.1, .lambda none (.apply "PZero" [])],
           .apply "POutput" [closedNilName.1, .apply "PZero" []]] none ∧
      target.1 = applyBindingsForRule rhoCalc rhoCommRewrite
        (rhoCommBindings closedNilName.1
          (.apply "PZero" []) (.apply "PZero" []) []) ∧
      rhoLanguageDefGSLT.Step source target := by
  apply compiledRhoComm_step
  · exact .quote (free := FreeSortContext.empty) .unit
  · decide +kernel
  · exact .unit (free := FreeSortContext.empty)
  · decide +kernel
  · exact .unit (free := FreeSortContext.empty)
  · decide +kernel
  · exact .nil
  · decide +kernel

/-- Negative boundary inherited from the authored strict core: compiling COMM
does not turn a free dropped quotation into an execution step. -/
theorem compiledRhoComm_preserves_freeDrop_inertness
    (channel : Pattern) (rest : List Pattern) :
    let freeDrop := .apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]
    applyBindingsForRule rhoCalc rhoCommRewrite
        (rhoCommBindings channel freeDrop (.apply "PZero" []) rest) =
      .collection .hashBag
        (semanticCommSubst freeDrop (.apply "PZero" []) :: rest) none := by
  exact rhoComm_free_drop_stays_inert channel rest

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLTBridge
