import Mettapedia.GSLT.Causality.ResourceAlternatives
import Mettapedia.GSLT.Causality.FundedAssayCompletion

/-!
# Probe delivery followed by a complementary assay

A request and an addressed offer are consumed by an actual delivery interaction.
Its production contains the assay message and a receipt retaining the provider,
requester and payload. The assay is an independently embedded complementary
receiver system. Delivery and testing have disjoint rule sites and are composed
as alternative resource interactions.

From a single offer and request, every first step is delivery. After that step,
every step is the admitted complementary guard firing. Both rules retain their
own origins. No claim identifies this resource protocol with a compiled rho
probe context or grants access to an external provider.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.AssayProbeDelivery

open ResourceInteraction OccurrenceHistory
open ComplementaryAssay (Verdict verdictOf)

universe u v w

inductive ProbeResource (X : Type u) (Providers : Type v) (Clients : Type w) where
  | request (session : Nat) (client : Clients)
  | offer (session : Nat) (provider : Providers) (value : X)
  | delivered (session : Nat) (provider : Providers) (client : Clients) (value : X)
  deriving DecidableEq

abbrev Resources (X : Type u) (Providers : Type v) (Clients : Type w) :=
  ComplementaryAssay.Resource X Clients ⊕ ProbeResource X Providers Clients

structure Delivery (X : Type u) (Providers : Type v) (Clients : Type w) where
  session : Nat
  provider : Providers
  client : Clients
  value : X

variable {X : Type u} {Providers : Type v} {Clients : Type w}

def deliverySystem : System.{max u v w, max u v w} (Resources X Providers Clients) where
  Site := ULift.{max u v w} Unit
  Instance := fun _ => Delivery X Providers Clients
  consume := fun firing =>
    {Sum.inr (.request firing.session firing.client),
      Sum.inr (.offer firing.session firing.provider firing.value)}
  read := fun _ => 0
  produce := fun firing =>
    {Sum.inl (.message firing.session firing.value),
      Sum.inr (.delivered firing.session firing.provider firing.client firing.value)}

def assaySystem (test : X → Bool) :
    System.{max u v w, max u v w} (Resources X Providers Clients) :=
  (ComplementaryAssay.system (Origins := Clients) test).raise.{max u w, max u w, v}.map Sum.inl

def system (test : X → Bool) :
    System.{max u v w, max u v w} (Resources X Providers Clients) :=
  (assaySystem test).alternatives deliverySystem

def waiting (session : Nat) (client : Clients) : Multiset (Resources X Providers Clients) :=
  marking (ComplementaryAssay.pending session client) {ProbeResource.request session client}

def offered (session : Nat) (provider : Providers) (client : Clients) (value : X) :
    Multiset (Resources X Providers Clients) :=
  marking (ComplementaryAssay.pending session client)
    {ProbeResource.request session client, ProbeResource.offer session provider value}

def received (session : Nat) (provider : Providers) (client : Clients) (value : X) :
    Multiset (Resources X Providers Clients) :=
  marking (ComplementaryAssay.ready session client value)
    {ProbeResource.delivered session provider client value}

def tested (test : X → Bool) (session : Nat) (provider : Providers)
    (client : Clients) (value : X) : Multiset (Resources X Providers Clients) :=
  marking (ComplementaryAssay.finished test session client value)
    {ProbeResource.delivered session provider client value}

def deliver (session : Nat) (provider : Providers) (client : Clients) (value : X) :
    Delivery X Providers Clients := ⟨session, provider, client, value⟩

theorem deliver_enabled (session : Nat) (provider : Providers) (client : Clients) (value : X) :
    deliverySystem.Enables (offered session provider client value)
      (site := ⟨()⟩) (deliver session provider client value) := by
  change marking 0 {ProbeResource.request session client, ProbeResource.offer session provider value}
      ≤ offered session provider client value
  exact (marking_le_iff _ _ _ _).2 ⟨zero_le, le_rfl⟩

theorem delivery_fields (session : Nat) (provider : Providers) (client : Clients) (value : X)
    {site : deliverySystem.Site} (firing : deliverySystem.Instance site)
    (enabled : deliverySystem.Enables (offered session provider client value)
      (site := site) firing) :
    firing.session = session ∧ firing.provider = provider ∧ firing.client = client ∧
      firing.value = value := by
  have request := Multiset.mem_of_le enabled
    (show Sum.inr (ProbeResource.request firing.session firing.client) ∈
      deliverySystem.consume (site := site) firing + deliverySystem.read (site := site) firing
      by simp [deliverySystem])
  have sameRequest : firing.session = session ∧ firing.client = client := by
    simpa [offered, marking, Multiset.disjSum, ComplementaryAssay.pending] using request
  have offer := Multiset.mem_of_le enabled
    (show Sum.inr (ProbeResource.offer firing.session firing.provider firing.value) ∈
      deliverySystem.consume (site := site) firing + deliverySystem.read (site := site) firing
      by simp [deliverySystem])
  have sameOffer : firing.session = session ∧ firing.provider = provider ∧ firing.value = value := by
    simpa [offered, marking, Multiset.disjSum, ComplementaryAssay.pending] using offer
  exact ⟨sameRequest.1, sameOffer.2.1, sameRequest.2, sameOffer.2.2⟩

theorem assay_pending_disabled (test : X → Bool) (session : Nat) (client : Clients)
    (frame : Multiset (ProbeResource X Providers Clients))
    {site : (assaySystem (Providers := Providers) test).Site}
    (firing : (assaySystem test).Instance site) :
    ¬ (assaySystem test).Enables (marking (ComplementaryAssay.pending session client) frame)
      firing := by
  intro enabled
  exact ComplementaryAssay.no_pending_enabled test session client firing.down
    (((ComplementaryAssay.system test).raise.{max u w, max u w, v}.map_inl_enables_frame _ _ firing).1 enabled)

theorem no_offer_delivery (assay : Multiset (ComplementaryAssay.Resource X Clients))
    (frame : Multiset (ProbeResource X Providers Clients))
    (noOffer : ∀ session provider value, ProbeResource.offer session provider value ∉ frame)
    {site : deliverySystem.Site} (firing : deliverySystem.Instance site) :
    ¬ deliverySystem.Enables (marking assay frame) (site := site) firing := by
  intro enabled
  have offer := Multiset.mem_of_le enabled
    (show Sum.inr (ProbeResource.offer firing.session firing.provider firing.value) ∈
      deliverySystem.consume (site := site) firing + deliverySystem.read (site := site) firing
      by simp [deliverySystem])
  have present : ProbeResource.offer firing.session firing.provider firing.value ∈ frame := by
    simpa [marking, Multiset.disjSum] using offer
  exact noOffer _ _ _ present

theorem waiting_stuck (test : X → Bool) (session : Nat) (client : Clients)
    {site : (system (Providers := Providers) test).Site}
    (firing : (system test).Instance site) :
    ¬ (system test).Enables (waiting session client) firing := by
  cases site with
  | inl site => exact assay_pending_disabled test session client _ firing
  | inr site => exact no_offer_delivery _ _ (by intros; simp) (site := site) firing

section Decidable

variable [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]

theorem deliver_fire (session : Nat) (provider : Providers) (client : Clients) (value : X) :
    deliverySystem.fire (offered session provider client value)
      (site := ⟨()⟩) (deliver session provider client value) = received session provider client value := by
  change marking (ComplementaryAssay.pending session client)
      {ProbeResource.request session client, ProbeResource.offer session provider value} -
    marking 0 {ProbeResource.request session client, ProbeResource.offer session provider value} +
    marking {ComplementaryAssay.Resource.message session value}
      {ProbeResource.delivered session provider client value} = _
  rw [marking_sub, marking_add]
  simp only [tsub_zero, tsub_self, zero_add]
  congr 1
  exact add_comm _ _

theorem delivery_fire (session : Nat) (provider : Providers) (client : Clients) (value : X)
    {site : deliverySystem.Site} (firing : deliverySystem.Instance site)
    (enabled : deliverySystem.Enables (offered session provider client value) (site := site) firing) :
    deliverySystem.fire (offered session provider client value) (site := site) firing =
      received session provider client value := by
  obtain ⟨sameSession, sameProvider, sameClient, sameValue⟩ :=
    delivery_fields session provider client value (site := site) firing enabled
  cases firing
  simp only at sameSession sameProvider sameClient sameValue
  subst_vars
  exact deliver_fire _ _ _ _

theorem assay_received_fire (test : X → Bool) (session : Nat) (provider : Providers)
    (client : Clients) (value : X) {site : (assaySystem (Providers := Providers) test).Site}
    (firing : (assaySystem test).Instance site)
    (enabled : (assaySystem test).Enables (received session provider client value) firing) :
    (assaySystem test).fire (received session provider client value) firing =
      tested test session provider client value := by
  have baseEnabled :=
    ((ComplementaryAssay.system test).raise.{max u w, max u w, v}.map_inl_enables_frame _ _ firing).1 enabled
  exact ((ComplementaryAssay.system test).raise.{max u w, max u w, v}.map_inl_fire_frame
    (ComplementaryAssay.ready session client value)
    {ProbeResource.delivered session provider client value} firing).trans
      (congrArg (fun endpoint => marking endpoint {ProbeResource.delivered session provider client value})
        (ComplementaryAssay.enabled_fire test firing.down baseEnabled))

theorem offered_step_iff (test : X → Bool) (session : Nat) (provider : Providers)
    (client : Clients) (value : X) (target : Multiset (Resources X Providers Clients)) :
    (system test).theory.rewrites (offered session provider client value) target ↔
      target = received session provider client value := by
  constructor
  · rintro ⟨site, firing, enabled, rfl⟩
    cases site with
    | inl site => exact False.elim (assay_pending_disabled test session client _ firing enabled)
    | inr site => exact delivery_fire session provider client value (site := site) firing enabled
  · intro endpoint
    exact ⟨.inr ⟨()⟩, deliver session provider client value,
      deliver_enabled session provider client value, endpoint.trans (deliver_fire _ _ _ _).symm⟩

theorem received_step_iff (test : X → Bool) (session : Nat) (provider : Providers)
    (client : Clients) (value : X) (target : Multiset (Resources X Providers Clients)) :
    (system test).theory.rewrites (received session provider client value) target ↔
      target = tested test session provider client value := by
  constructor
  · rintro ⟨site, firing, enabled, rfl⟩
    cases site with
    | inl site => exact assay_received_fire test session provider client value firing enabled
    | inr site =>
      exact False.elim (no_offer_delivery _ _ (by intros; simp) (site := site) firing enabled)
  · intro endpoint
    refine ⟨.inl ⟨⟨verdictOf (test value)⟩⟩,
      ⟨ComplementaryAssay.selected test session client value⟩, ?_, ?_⟩
    · exact ((ComplementaryAssay.system test).raise.{max u w, max u w, v}.map_inl_enables_frame _ _ _).2
        (ComplementaryAssay.selected_enabled test session client value)
    · exact endpoint.trans (assay_received_fire test session provider client value _
        (((ComplementaryAssay.system test).raise.{max u w, max u w, v}.map_inl_enables_frame _ _ _).2
          (ComplementaryAssay.selected_enabled test session client value))).symm

omit [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients] in
theorem tested_stuck (test : X → Bool) (session : Nat) (provider : Providers)
    (client : Clients) (value : X) {site : (system (Providers := Providers) test).Site}
    (firing : (system test).Instance site) :
    ¬ (system test).Enables (tested test session provider client value) firing := by
  cases site with
  | inl site =>
    intro enabled
    exact ComplementaryAssay.no_finished_enabled test session client value firing.down
      (((ComplementaryAssay.system test).raise.{max u w, max u w, v}.map_inl_enables_frame _ _ firing).1 enabled)
  | inr site => exact no_offer_delivery _ _ (by intros; simp) (site := site) firing

def outputs (resources : Multiset (Resources X Providers Clients)) :
    Multiset (Nat × Verdict × Clients × X) := ComplementaryAssay.outputs (leftPart resources)

omit [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients] in
@[simp] theorem outputs_offered (session : Nat) (provider : Providers) (client : Clients)
    (value : X) : outputs (offered session provider client value) = 0 := by
  rw [outputs, offered, leftPart_marking, ComplementaryAssay.outputs_pending]

omit [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients] in
@[simp] theorem outputs_received (session : Nat) (provider : Providers) (client : Clients)
    (value : X) : outputs (received session provider client value) = 0 := by
  rw [outputs, received, leftPart_marking, ComplementaryAssay.outputs_ready]

omit [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients] in
@[simp] theorem outputs_tested (test : X → Bool) (session : Nat) (provider : Providers)
    (client : Clients) (value : X) : outputs (tested test session provider client value) =
      { (session, verdictOf (test value), client, value) } := by
  rw [outputs, tested, leftPart_marking, ComplementaryAssay.outputs_finished]

end Decidable

end Mettapedia.GSLT.Causality.AssayProbeDelivery
