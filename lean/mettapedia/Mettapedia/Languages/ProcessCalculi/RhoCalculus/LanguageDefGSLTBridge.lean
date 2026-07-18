import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy
import Mettapedia.GSLT.Meredith.RhoExample

/-!
# Authored rho COMM to the committed GSLT

The strict-core rho language is authored by `rhoCalc`.  Its derived process
judgment supplies the induction principle used to prove that the compiled COMM
contractum is exactly the contractum of the existing paper-facing reduction.
This file packages that agreement as a step of the committed rho GSLT; it does
not introduce another term carrier, equation relation, or rewrite relation.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLTBridge

open Mettapedia.GSLT
open Mettapedia.GSLT.Meredith.RhoExample
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-- Every well-sorted COMM contractum compiled from the single authored rho
declaration is a step of the established rho GSLT. -/
theorem compiledRhoComm_is_rhoGSLTStep
    {free : FreeSortContext} {bound : List String} {body payload : Pattern}
    (bodyTyped : ProcWellSorted rhoReflectivePresentation free
      (rhoReflectivePresentation.nameSort :: bound) body)
    (payloadTyped : ProcWellSorted rhoReflectivePresentation free bound payload)
    (channel : Pattern) (rest : List Pattern) :
    rhoGSLT.Step
      (.collection .hashBag
        ([.apply "POutput" [channel, payload],
          .apply "PInput" [channel, .lambda none body]] ++ rest) none)
      (applyBindingsForRule rhoCalc rhoCommRewrite
        (rhoCommBindings channel body payload rest)) := by
  rw [applyBindingsForRule_rhoComm_agrees_derived
    bodyTyped payloadTyped channel rest]
  exact ⟨Reduces.comm⟩

/-- Positive control: the derived nil continuation and nil payload instantiate
the authored-to-GSLT COMM bridge without auxiliary semantic data. -/
theorem compiledRhoComm_nil_is_rhoGSLTStep (channel : Pattern) :
    rhoGSLT.Step
      (.collection .hashBag
        [.apply "POutput" [channel, .apply "PZero" []],
         .apply "PInput" [channel, .lambda none (.apply "PZero" [])]] none)
      (applyBindingsForRule rhoCalc rhoCommRewrite
        (rhoCommBindings channel (.apply "PZero" []) (.apply "PZero" []) [])) := by
  exact compiledRhoComm_is_rhoGSLTStep
    (free := FreeSortContext.empty) (bound := [])
    (bodyTyped := .unit) (payloadTyped := .unit) channel []

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
