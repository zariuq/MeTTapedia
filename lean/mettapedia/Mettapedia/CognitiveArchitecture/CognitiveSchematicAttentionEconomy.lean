import Mettapedia.CognitiveArchitecture.AttentionEconomy
import Mettapedia.CognitiveArchitecture.CognitiveSchematic

/-!
# Cognitive schematics as attention-economy services

A request for service may name a cognitive schematic and promise a payment to
the provider.  The promise, a completed execution, and settlement are kept as
three different objects:

```text
service request = payment promise + candidate schematic
fulfillment     = one context + execution occurrence + achieved goal
settlement      = fulfillment + authorized funded redemption
```

This separation prevents attention currency from becoming semantic truth and
prevents a successful computation from silently authorizing a transfer.  A
service chain retains both payment promises rather than scalarizing them into
one unexplained charge; its operational component is ordinary proof-relevant
schematic composition.

The interface follows the request-for-service account in Goertzel et al.,
*Engineering General Intelligence, Part 2*, chapter 6, together with the
cognitive-schematic account in Part 1.  It formalizes a reusable contract
boundary, not a particular scheduler or credit-assignment heuristic.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CognitiveArchitecture.CognitiveSchematicAttentionEconomy

open Mettapedia.CognitiveArchitecture.AttentionEconomy
open Mettapedia.CognitiveArchitecture.CognitiveSchematic

universe uState uActor uCurrency uId

/-- A resource promise attached to a candidate cognitive schematic.  Merely
constructing this record proves neither achievement nor payment. -/
structure ServiceRequest
    (RequestId : Type uId) (Actor : Type uActor)
    (horizon : ImportanceHorizon) (Currency : Type uCurrency)
    (Source Target : Type uState) where
  payment : RequestForService RequestId Actor horizon Currency
  schematic : Schematic Source Target

namespace ServiceRequest

variable {RequestId : Type uId} {Actor : Type uActor}
variable {horizon : ImportanceHorizon} {Currency : Type uCurrency}
variable {Source Middle Target : Type uState}

/-- A service is fulfilled by one exact proof-relevant completion. -/
abbrev Fulfillment
    (request : ServiceRequest RequestId Actor horizon Currency Source Target) :=
  request.schematic.Completion

/-- A global may-achievement certificate produces one fulfillment for a
specified context occurrence. -/
def fulfillmentOfMay
    (request : ServiceRequest RequestId Actor horizon Currency Source Target)
    (certificate : request.schematic.MayAchieve)
    {source : Source} (contextWitness : request.schematic.context source) :
    request.Fulfillment :=
  Schematic.MayAchieve.complete certificate contextWitness

section Settlement

variable [AddCommGroup Currency] [LE Currency]

/-- Settlement requires both semantic fulfillment and an independently
authorized, funded redemption. -/
structure Settlement
    (request : ServiceRequest RequestId Actor horizon Currency Source Target)
    (fund : Fund horizon Actor Currency) where
  fulfillment : request.Fulfillment
  redemption : request.payment.Redemption fund

/-- The fund after an exact settlement. -/
def Settlement.after
    {request : ServiceRequest RequestId Actor horizon Currency Source Target}
    {fund : Fund horizon Actor Currency}
    (_settlement : request.Settlement fund) : Fund horizon Actor Currency :=
  request.payment.asTransfer.apply fund

/-- Settlement conserves the selected attention instrument. -/
@[simp] theorem Settlement.total_after
    {request : ServiceRequest RequestId Actor horizon Currency Source Target}
    {fund : Fund horizon Actor Currency}
    (settlement : request.Settlement fund) :
    Fund.total settlement.after = Fund.total fund :=
  Transfer.total_apply request.payment.asTransfer fund

/-- Settlement retains the exact achieved goal witness; payment does not
replace or reconstruct it. -/
def Settlement.achieved
    {request : ServiceRequest RequestId Actor horizon Currency Source Target}
    {fund : Fund horizon Actor Currency}
    (settlement : request.Settlement fund) :
    request.schematic.goal settlement.fulfillment.target :=
  settlement.fulfillment.goalWitness

end Settlement

/-! ## Chaining services without collapsing their contracts -/

/-- Two service requests compose operationally when the first goal supplies
the second context.  Their payment promises remain distinct fields. -/
structure Chain
    (first : ServiceRequest RequestId Actor horizon Currency Source Middle)
    (second : ServiceRequest RequestId Actor horizon Currency Middle Target) where
  handoff : forall {middle},
    first.schematic.goal middle -> second.schematic.context middle

namespace Chain

variable
    {first : ServiceRequest RequestId Actor horizon Currency Source Middle}
    {second : ServiceRequest RequestId Actor horizon Currency Middle Target}

/-- The operational candidate of a service chain. -/
def schematic (_chain : Chain first second) : Schematic Source Target :=
  first.schematic.chain second.schematic

/-- Must-achievement composes through the declared handoff. -/
def mustAchieve (chain : Chain first second)
    (firstCertificate : first.schematic.MustAchieve)
    (secondCertificate : second.schematic.MustAchieve) :
    chain.schematic.MustAchieve :=
  firstCertificate.chain secondCertificate chain.handoff

/-- May-achievement composes while retaining the middle state and both
execution occurrences. -/
def mayAchieve (chain : Chain first second)
    (firstCertificate : first.schematic.MayAchieve)
    (secondCertificate : second.schematic.MayAchieve) :
    chain.schematic.MayAchieve :=
  firstCertificate.chain secondCertificate chain.handoff

section Settlement

variable [AddCommGroup Currency] [LE Currency]

/-- A chain settlement retains one composite completion and two sequential
redemptions.  The second payment is admitted against the post-first-payment
fund, so no stale funding certificate is reused. -/
structure Settlement (chain : Chain first second)
    (fund : Fund horizon Actor Currency) where
  fulfillment : chain.schematic.Completion
  firstRedemption : first.payment.Redemption fund
  secondRedemption : second.payment.Redemption
    (first.payment.asTransfer.apply fund)

/-- Execute both promised transfers in their declared order. -/
def Settlement.after
    {chain : Chain first second} {fund : Fund horizon Actor Currency}
    (_settlement : chain.Settlement fund) : Fund horizon Actor Currency :=
  second.payment.asTransfer.apply
    (first.payment.asTransfer.apply fund)

/-- Sequential settlement conserves the exact selected fund. -/
@[simp] theorem Settlement.total_after
    {chain : Chain first second} {fund : Fund horizon Actor Currency}
    (settlement : chain.Settlement fund) :
    Fund.total settlement.after = Fund.total fund := by
  rw [Settlement.after, Transfer.total_apply, Transfer.total_apply]

end Settlement

end Chain

end ServiceRequest

/-! ## Positive and negative controls -/

namespace Canary

inductive Actor where
  | requester
  | analyst
  | planner
deriving DecidableEq, Repr

abbrev Currency := ℤ

def fund : Fund .shortTerm Actor Currency where
  balances := Finsupp.single .requester 10

def firstSchematic : Schematic Unit Bool where
  context := fun _ => PUnit
  procedure := fun _ target => PLift (target = true)
  goal := fun target => PLift (target = true)

def firstMay : firstSchematic.MayAchieve := by
  intro _ _
  exact ⟨true, ⟨⟨rfl⟩, ⟨rfl⟩⟩⟩

def secondSchematic : Schematic Bool Unit where
  context := fun source => PLift (source = true)
  procedure := fun source _ => PLift (source = true)
  goal := fun _ => PUnit

def secondMay : secondSchematic.MayAchieve := by
  intro source contextWitness
  exact ⟨(), ⟨contextWitness, PUnit.unit⟩⟩

def firstRequest :
    ServiceRequest ℕ Actor .shortTerm Currency Unit Bool where
  payment := ⟨1, .requester, .analyst, 2⟩
  schematic := firstSchematic

def secondRequest :
    ServiceRequest ℕ Actor .shortTerm Currency Bool Unit where
  payment := ⟨2, .requester, .planner, 3⟩
  schematic := secondSchematic

def serviceChain : firstRequest.Chain secondRequest where
  handoff := fun goalWitness => goalWitness

def chainFulfillment : serviceChain.schematic.Completion :=
  Schematic.MayAchieve.complete
    (serviceChain.mayAchieve firstMay secondMay)
    (source := ()) PUnit.unit

def firstRedemption : firstRequest.payment.Redemption fund where
  actor := .analyst
  authorized := rfl
  admission := by
    constructor <;> simp [fund, firstRequest,
      RequestForService.asTransfer]

def secondRedemption : secondRequest.payment.Redemption
    (firstRequest.payment.asTransfer.apply fund) where
  actor := .planner
  authorized := rfl
  admission := by
    constructor
    · change 0 ≤ (3 : ℤ)
      norm_num
    · simp [fund, firstRequest, secondRequest,
        RequestForService.asTransfer, Transfer.apply]

def chainSettlement : serviceChain.Settlement fund where
  fulfillment := chainFulfillment
  firstRedemption := firstRedemption
  secondRedemption := secondRedemption

/-- Positive control: a two-service chain both achieves its final goal and
settles two independently authorized payments conservatively. -/
theorem chained_service_achieves_and_conserves :
    Nonempty
      (serviceChain.schematic.goal chainSettlement.fulfillment.target) ∧
      Fund.total chainSettlement.after = Fund.total fund :=
  ⟨⟨chainSettlement.fulfillment.goalWitness⟩,
    chainSettlement.total_after⟩

def unavailableSchematic : Schematic Unit Unit where
  context := fun _ => PUnit
  procedure := fun _ _ => Empty
  goal := fun _ => PUnit

def paidButUnavailable :
    ServiceRequest ℕ Actor .shortTerm Currency Unit Unit where
  payment := ⟨3, .requester, .analyst, 1⟩
  schematic := unavailableSchematic

def unavailableRedemption : paidButUnavailable.payment.Redemption fund where
  actor := .analyst
  authorized := rfl
  admission := by
    constructor <;> simp [fund, paidButUnavailable,
      RequestForService.asTransfer]

/-- Negative control: funded authorization is not evidence that a service was
performed. -/
theorem payment_does_not_prove_service :
    Nonempty (paidButUnavailable.payment.Redemption fund) ∧
      IsEmpty paidButUnavailable.Fulfillment := by
  constructor
  · exact ⟨unavailableRedemption⟩
  · constructor
    intro fulfillment
    exact fulfillment.execution.elim

def achievableButUnfunded :
    ServiceRequest ℕ Actor .shortTerm Currency Unit Unit where
  payment := ⟨4, .requester, .planner, 11⟩
  schematic := Schematic.skip (fun _ : Unit => PUnit)

def achievableCompletion : achievableButUnfunded.Fulfillment :=
  Schematic.MayAchieve.complete
    (Schematic.skipMay (fun _ : Unit => PUnit))
    (source := ()) PUnit.unit

/-- Negative control: achievement does not mint funds or authorize an
overdraft. -/
theorem service_does_not_authorize_payment :
    Nonempty achievableButUnfunded.Fulfillment ∧
      IsEmpty (achievableButUnfunded.payment.Redemption fund) := by
  constructor
  · exact ⟨achievableCompletion⟩
  · constructor
    intro redemption
    have funded := redemption.admission.funded
    simp [fund, achievableButUnfunded,
      RequestForService.asTransfer] at funded

end Canary

/-! ## Axiom audit -/

#print axioms ServiceRequest.Settlement.total_after
#print axioms ServiceRequest.Chain.mustAchieve
#print axioms ServiceRequest.Chain.mayAchieve
#print axioms ServiceRequest.Chain.Settlement.total_after
#print axioms Canary.chained_service_achieves_and_conserves
#print axioms Canary.payment_does_not_prove_service
#print axioms Canary.service_does_not_authorize_payment

end Mettapedia.CognitiveArchitecture.CognitiveSchematicAttentionEconomy
