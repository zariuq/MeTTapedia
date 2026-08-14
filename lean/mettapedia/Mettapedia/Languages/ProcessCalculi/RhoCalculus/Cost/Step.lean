import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Basic
import Mathlib.Data.Multiset.Bind

/-!
# Concrete cost-accounted rho steps

This module presents the two communication shapes recognized by the concrete
cost-profile reducer: a single signed parallel redex and two separately signed
endpoints.  A step consumes exactly one head from each selected temporal stack,
and the selected heads must cover the communication signature as a multiset.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

/-- A structural-normal-form configuration of top-level cost terms. -/
abbrev CostConfig (Ground : Type u) := Multiset (CostTerm Ground)

/-- Flatten top-level cost parallel composition and erase only the cost-term
identity.  A depleted located purse remains an observable inert resource. -/
def CostTerm.components {Ground : Type u} : CostTerm Ground → CostConfig Ground
  | .nil => 0
  | .par left right => left.components + right.components
  | term => term ::ₘ 0

/-- One nominally located temporal purse. -/
structure LocatedPurse (Ground : Type u) where
  location : CostName Ground
  stack : CostStack Ground
  deriving DecidableEq

namespace LocatedPurse

/-- Embed a purse into the concrete wrapped-term syntax. -/
def toTerm {Ground : Type u} (purse : LocatedPurse Ground) : CostTerm Ground :=
  .purse purse.location purse.stack

/-- Embed a multiset of located purses into a top-level configuration. -/
def configComponents {Ground : Type u}
    (purses : Multiset (LocatedPurse Ground)) : CostConfig Ground :=
  purses.map toTerm

end LocatedPurse

/-- One selected purse occurrence, retaining the exact consumed head and the
tail exposed after the firing.  Head validity is intrinsic evidence. -/
structure SelectedPurseHead (Ground : Type u) where
  head : CostSig Ground
  tail : CostStack Ground
  head_valid : head.RuntimeValid

/-- Evidence that selected located purse heads exactly fund a demand.

`available` contains every purse before the step.  `chosen` records one head
and tail for each selected purse at `location`; `untouched` records every
unselected purse, including purses at other locations.  `residual` exposes the
selected tails at the same location and retains all untouched purses.
-/
structure LocatedTokenCover {Ground : Type u} (location : CostName Ground)
    (demand : CostSig Ground)
    (available residual : Multiset (LocatedPurse Ground)) : Type u where
  chosen : Multiset (SelectedPurseHead Ground)
  untouched : Multiset (LocatedPurse Ground)
  available_eq :
    available = chosen.map (fun choice =>
      ⟨location, CostStack.cons choice.head choice.tail⟩) + untouched
  residual_eq :
    residual = chosen.map (fun choice => ⟨location, choice.tail⟩) + untouched
  demand_eq : demand = (chosen.map SelectedPurseHead.head).sum

/-- One labelled, token-funded reduction of a normalized cost configuration. -/
inductive CostStep {Ground : Type u} :
    CostConfig Ground → CostName Ground → CostSig Ground → CostConfig Ground → Prop where
  /-- A receive/send pair inside one signed wrapper, in receive-first order. -/
  | wholeRecvSend
      {context : CostConfig Ground}
      {available residual : Multiset (LocatedPurse Ground)}
      {channel : CostName Ground}
      {body payload : CostTerm Ground}
      {outerSig : CostSig Ground}
      (signature_valid : outerSig.RuntimeValid)
      (cover : LocatedTokenCover channel outerSig available residual) :
      CostStep
        (context +
          (.signed (.par (.recv channel body) (.send channel payload)) outerSig ::ₘ 0) +
          LocatedPurse.configComponents available)
        channel
        outerSig
        (context + (body.commSubst payload).components +
          LocatedPurse.configComponents residual)

  /-- A receive/send pair inside one signed wrapper, in send-first order. -/
  | wholeSendRecv
      {context : CostConfig Ground}
      {available residual : Multiset (LocatedPurse Ground)}
      {channel : CostName Ground}
      {body payload : CostTerm Ground}
      {outerSig : CostSig Ground}
      (signature_valid : outerSig.RuntimeValid)
      (cover : LocatedTokenCover channel outerSig available residual) :
      CostStep
        (context +
          (.signed (.par (.send channel payload) (.recv channel body)) outerSig ::ₘ 0) +
          LocatedPurse.configComponents available)
        channel
        outerSig
        (context + (body.commSubst payload).components +
          LocatedPurse.configComponents residual)

  /-- Separately signed endpoints; the cost is the multiset sum of both seals. -/
  | split
      {context : CostConfig Ground}
      {available residual : Multiset (LocatedPurse Ground)}
      {channel : CostName Ground}
      {body payload : CostTerm Ground}
      {recvSeal sendSeal : CostSig Ground}
      (recv_seal_valid : recvSeal.RuntimeValid)
      (send_seal_valid : sendSeal.RuntimeValid)
      (cover : LocatedTokenCover channel (recvSeal + sendSeal) available residual) :
      CostStep
        (context + (.signed (.recv channel body) recvSeal ::ₘ 0) +
          (.signed (.send channel payload) sendSeal ::ₘ 0) +
          LocatedPurse.configComponents available)
        channel
        (recvSeal + sendSeal)
        (context + (body.commSubst payload).components +
          LocatedPurse.configComponents residual)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
