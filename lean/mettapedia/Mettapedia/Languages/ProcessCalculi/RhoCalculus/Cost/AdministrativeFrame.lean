import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSeparation
import Mettapedia.GSLT.LanguageDef.CostNamespace

/-!
# Located interpretation of the administrative contact frame

A generated contact combines code and a funding stack. The concrete rho
runtime combines code with a purse at an explicit nominal location. The
interpretation below therefore retains that location as an index. It proves
context closure for already funded concrete firings, together with a control
showing why the location cannot be recovered from the stack-only readout.

This is the administrative frame comparison. Translation of arbitrary
generated code, signatures and their equations is a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

universe u

namespace CostStep

/-- A funded event remains possible in a larger parallel context, with the
same location, spend and chosen funding evidence. -/
theorem add_frame {Ground : Type u} {source target : CostConfig Ground}
    {location : CostName Ground} {spend : CostSig Ground}
    (step : CostStep source location spend target) (frame : CostConfig Ground) :
    CostStep (frame + source) location spend (frame + target) := by
  cases step with
  | @wholeRecvSend context available residual channel body payload outerSig valid cover =>
      simpa only [add_assoc] using CostStep.wholeRecvSend (context := frame + context) (body := body) (payload := payload) valid cover
  | @wholeSendRecv context available residual channel body payload outerSig valid cover =>
      simpa only [add_assoc] using CostStep.wholeSendRecv (context := frame + context) (body := body) (payload := payload) valid cover
  | @split context available residual channel body payload recvSeal sendSeal recvValid sendValid cover =>
      simpa only [add_assoc] using CostStep.split (context := frame + context) (body := body) (payload := payload) recvValid sendValid cover

end CostStep

/-- The generated contact's concrete interpretation at one retained nominal
location. It adds an actual purse occurrence, including when depleted. -/
def locatedContact {Ground : Type u} (location : CostName Ground)
    (code : CostTerm Ground) (stack : CostStack Ground) : CostTerm Ground :=
  .par code (.purse location stack)

/-- Administrative context closure lifts only a firing already justified by
its own funding. The outer stack is preserved exactly. -/
theorem locatedContact_step {Ground : Type u}
    {source target : CostTerm Ground} {location : CostName Ground} {spend : CostSig Ground}
    (step : CostStep source.components location spend target.components)
    (outerLocation : CostName Ground) (stack : CostStack Ground) :
    CostStep (locatedContact outerLocation source stack).components location spend
      (locatedContact outerLocation target stack).components := by
  simpa only [locatedContact, CostTerm.components, add_comm] using
    step.add_frame (CostTerm.purse outerLocation stack ::ₘ 0)

/-- Positive continuation control: an inner funded communication fires under
an arbitrary outer purse, and only its own cell is consumed. -/
theorem locatedContact_funded_communication {Ground : Type u}
    (channel outerLocation : CostName Ground) (signature : CostSig Ground)
    (valid : signature.RuntimeValid) (innerTail outerStack : CostStack Ground) :
    CostStep
      (locatedContact outerLocation
        (locatedContact channel
          (.signed (.par (.recv channel .nil) (.send channel .nil)) signature)
          (.cons signature innerTail)) outerStack).components
      channel signature
      (locatedContact outerLocation (.purse channel innerTail) outerStack).components := by
  apply locatedContact_step
  simpa [locatedContact, CostTerm.components, CostTerm.commSubst, CostTerm.substitute] using
    CostStep.wholeRecvSend_single_head 0 channel .nil .nil signature valid innerTail

/-- Unfunded code does not gain permission at a different nominal location
merely by being placed under an administrative contact. -/
theorem locatedContact_wrong_location {Ground : Type u}
    {code : CostTerm Ground} (codeOnly : code.PurseFree)
    {outerLocation location : CostName Ground} (different : location ≠ outerLocation)
    (stack : CostStack Ground) (spend : CostSig Ground) (target : CostConfig Ground) :
    ¬ CostStep (locatedContact outerLocation code stack).components location spend target := by
  apply CostStep.blocked_of_no_funding_at
  intro head tail member
  rcases Multiset.mem_add.mp member with inCode | inPurse
  · exact codeOnly.no_component_purse _ _ inCode
  · have same := Multiset.mem_singleton.mp inPurse
    exact different (CostTerm.purse.inj same).1

/-- Code-only payloads and locations put the contact interpretation in the
same resource-separated domain used by physical conservation. -/
theorem locatedContact_resourceSeparated {Ground : Type u}
    {code : CostTerm Ground} (codeOnly : code.PurseFree)
    {location : CostName Ground} (locationOnly : location.purseInventory = 0)
    (stack : CostStack Ground) :
    (locatedContact location code stack).components.ResourceSeparated := by
  change (code.components + (CostTerm.purse location stack ::ₘ 0)).ResourceSeparated
  rw [CostConfig.resourceSeparated_add_iff]
  refine ⟨codeOnly.components_resourceSeparated, ?_⟩
  intro term member
  have same := Multiset.mem_singleton.mp member
  simpa only [same, CostTerm.ResourceSeparated] using locationOnly

/-- Stack-only generated funding syntax. The nominal location remains in
the interpretation index; it is absent from this exact constructor row. -/
def fundingReadout {Ground : Type u} (encodeStack : CostStack Ground → Pattern)
    (purse : LocatedPurse Ground) : Pattern :=
  .apply costFundingConstructorName [encodeStack purse.stack]

/-- Two genuinely different located purses have the same stack-only readout. -/
theorem fundingReadout_location_loss {Ground : Type u}
    (encodeStack : CostStack Ground → Pattern)
    {left right : CostName Ground} (different : left ≠ right) (stack : CostStack Ground) :
    fundingReadout encodeStack ⟨left, stack⟩ = fundingReadout encodeStack ⟨right, stack⟩ ∧
      (⟨left, stack⟩ : LocatedPurse Ground) ≠ ⟨right, stack⟩ := by
  exact ⟨rfl, fun same => different (congrArg LocatedPurse.location same)⟩

/-- A location-free readout cannot supply a decoder that recovers every
original nominal authority. This does not rule out a located interpretation. -/
theorem no_location_recovery {Ground : Type u}
    (encodeStack : CostStack Ground → Pattern)
    {left right : CostName Ground} (different : left ≠ right) :
    ¬ ∃ recover : Pattern → CostName Ground,
      ∀ purse : LocatedPurse Ground, recover (fundingReadout encodeStack purse) = purse.location := by
  rintro ⟨recover, correct⟩
  exact different ((correct ⟨left, .empty⟩).symm.trans (correct ⟨right, .empty⟩))

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
