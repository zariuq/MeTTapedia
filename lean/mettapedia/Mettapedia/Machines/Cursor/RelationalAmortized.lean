import Mettapedia.Machines.Cursor.Amortized
import Mettapedia.Machines.Cursor.RelationalTransfer
import Mettapedia.Machines.Cursor.SequenceCost

/-!
# Resource bounds under relational cursor migration

Local simulation and local potential accounts imply a resource bound for every
finite interaction, including paused clients. Neither theorem requires a
canonical decoder. Migration charges include proposal work on refusals and the
conversion work of accepted offers, before charging the selected operation.

The concrete controls compare one-way list-to-slice promotion with repeatedly
materializing the residual in alternating representations. Both preserve the
same answers; only the first has a linear whole-traversal charge. The meters
count proposal inspections, protocol requests and materialized residual
children. They do not count allocator work, backing-prefix traversal during
conversion, machine instructions or elapsed time.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial

universe u

variable {Base : Type u} {Index : Base → Type u}
variable {P : IndexedPolynomial.{u,u,u,u} Base Index}
variable {Return : (base : Base) → Index base → Type u}
variable {source target : Provider P}

/-- A cost obligation at a related pair, separate from the semantic step law.
The potential belongs to the actual retained state, so suspended work retains
its credits. It need not be recoverable from the reference representation. -/
def RelationalAmortized (rel : StateRel source target)
    (sourceCost : Charge source) (targetCost : Charge target)
    (potential : Potential source) : Prop :=
  ∀ {base index} (left : source.State base index) (right : target.State base index),
    rel left right → ∀ request : P.Shape base index,
      sourceCost left request + potential (source.step left request).2 ≤
        targetCost right request + potential left

/-- Local accounting telescopes across arbitrary reply-dependent clients;
returning and running out of scheduler budget both retain the final potential. -/
theorem advance_relational_amortized
    (client : Client (P := P) (Return := Return))
    (rel : StateRel source target) (localLaw : Bisimulation rel)
    (sourceCost : Charge source) (targetCost : Charge target)
    (potential : Potential source)
    (localBound : RelationalAmortized rel sourceCost targetCost potential)
    (budget : Nat) {base : Base}
    {left : Packet source client base} {right : Packet target client base}
    (related : PacketRel client rel left right) :
    (advance source client sourceCost budget left).1 +
        outcomePotential client potential (advance source client sourceCost budget left).2 ≤
      (advance target client targetCost budget right).1 + potential left.2.2 := by
  induction budget generalizing left right with
  | zero => simp [advance, outcomePotential]
  | succ budget ih =>
      cases related with
      | @same index control left right related =>
          cases layer : client.str base index control with
          | mk shape children =>
              cases shape with
              | inl value => simp [advance, layer, outcomePotential]
              | inr request =>
                  dsimp only [withHoles] at children
                  obtain ⟨reply, left', right', leftStep, rightStep, nextRelated⟩ :=
                    localLaw left right related request
                  have next := ih (.same (children reply) nextRelated)
                  have debit := localBound left right related request
                  simp only [advance, layer]
                  dsimp only [withHoles]
                  rw [leftStep, rightStep]
                  rw [leftStep] at debit
                  dsimp only at next debit ⊢
                  omega

/-- The observable relation and resource guarantee are established together,
without replacing semantic equivalence by cost equality. -/
theorem advance_relational_resource_contract
    (client : Client (P := P) (Return := Return))
    (rel : StateRel source target) (localLaw : Bisimulation rel)
    (sourceCost : Charge source) (targetCost : Charge target)
    (potential : Potential source)
    (localBound : RelationalAmortized rel sourceCost targetCost potential)
    (budget : Nat) {base : Base}
    {left : Packet source client base} {right : Packet target client base}
    (related : PacketRel client rel left right) :
    OutcomeRel client rel (advance source client sourceCost budget left).2
        (advance target client targetCost budget right).2 ∧
      (advance source client sourceCost budget left).1 +
          outcomePotential client potential (advance source client sourceCost budget left).2 ≤
        (advance target client targetCost budget right).1 + potential left.2.2 :=
  ⟨advance_related client rel localLaw sourceCost targetCost budget related,
    advance_relational_amortized client rel localLaw sourceCost targetCost potential
      localBound budget related⟩

/-- The retained account composes across a later scheduler quantum. It
also preserves already-finished results and does not rerun their producer. -/
theorem resume_relational_resource_contract
    (client : Client (P := P) (Return := Return))
    (rel : StateRel source target) (localLaw : Bisimulation rel)
    (sourceCost : Charge source) (targetCost : Charge target)
    (potential : Potential source)
    (localBound : RelationalAmortized rel sourceCost targetCost potential)
    (budget initialCredit : Nat) {base : Base}
    (left : Nat × Outcome source client base) (right : Nat × Outcome target client base)
    (related : OutcomeRel client rel left.2 right.2)
    (account : left.1 + outcomePotential client potential left.2 ≤ right.1 + initialCredit) :
    OutcomeRel client rel (resume source client sourceCost budget left).2
        (resume target client targetCost budget right).2 ∧
      (resume source client sourceCost budget left).1 +
          outcomePotential client potential (resume source client sourceCost budget left).2 ≤
        (resume target client targetCost budget right).1 + initialCredit := by
  rcases left with ⟨leftSpent, leftOutcome⟩
  rcases right with ⟨rightSpent, rightOutcome⟩
  cases related with
  | @paused left right related =>
      have chunk := advance_relational_resource_contract client rel localLaw sourceCost
        targetCost potential localBound budget related
      constructor
      · exact chunk.1
      · dsimp only [resume]
        dsimp only [outcomePotential] at account
        have stepBound := chunk.2
        omega
  | done value related =>
      exact ⟨.done value related, account⟩

/-- Reverse graph relations may have many related target states. The
relational theorem does not have to select a preferred inverse of a decoder. -/
theorem Hom.inverse_bisimulation (h : Hom target source) :
    Bisimulation (fun left right => left = h.map right) := by
  intro base index left right related request
  subst left
  refine ⟨(target.step right request).1, h.map (target.step right request).2,
    (target.step right request).2, ?_, rfl, rfl⟩
  exact (h.step right request).symm

/-- Conversion can depend on both the old and proposed representation. -/
abbrev ConversionCharge (provider : Provider P) :=
  {base : Base} → {index : Index base} → provider.State base index →
    provider.State base index → P.Shape base index → Nat

/-- A refusal still pays the proposal's work. Only accepted offers pay the
conversion meter. These meters describe actual work, not an acceptance test. -/
def offerCharge (offer : Offer source) (proposalCost : Charge source)
    (conversionCost : ConversionCharge source) : Charge source :=
  fun state request => proposalCost state request +
    match offer state request with
    | none => 0
    | some next => conversionCost state next request

@[simp] theorem offerCharge_refused (offer : Offer source)
    (proposalCost : Charge source) (conversionCost : ConversionCharge source)
    {base : Base} {index : Index base} (state : source.State base index)
    (request : P.Shape base index) (refused : offer state request = none) :
    offerCharge offer proposalCost conversionCost state request = proposalCost state request := by
  simp [offerCharge, refused]

@[simp] theorem offerCharge_accepted (offer : Offer source)
    (proposalCost : Charge source) (conversionCost : ConversionCharge source)
    {base : Base} {index : Index base} (state next : source.State base index)
    (request : P.Shape base index) (accepted : offer state request = some next) :
    offerCharge offer proposalCost conversionCost state request =
      proposalCost state request + conversionCost state next request := by
  simp [offerCharge, accepted]

/-- A migration account pays for proposal and conversion before the selected
operation. Credit can fund a large conversion; alternatively a reference-side
allowance may fund repeated bounded proposals. -/
def MigrationAmortized (rel : StateRel source target) (offer : Offer source)
    (proposalCost : Charge source) (conversionCost : ConversionCharge source)
    (allowance : Charge target) (potential : Potential source) : Prop :=
  ∀ {base index} (left : source.State base index) (right : target.State base index),
    rel left right → ∀ request : P.Shape base index,
      offerCharge offer proposalCost conversionCost left request +
          potential (choose offer left request) ≤
        allowance right request + potential left

/-- Migration and operation accounts compose on the actual chosen residual,
which may have a different physical representation at every request. -/
theorem relational_amortized_switching
    (rel : StateRel source target) (offer : Offer source)
    (sound : RelationalSoundOffer rel offer)
    (proposalCost : Charge source) (conversionCost : ConversionCharge source)
    (operationCost : Charge source) (referenceCost allowance : Charge target)
    (potential : Potential source)
    (operationBound : RelationalAmortized rel operationCost referenceCost potential)
    (migrationBound : MigrationAmortized rel offer proposalCost conversionCost allowance potential) :
    RelationalAmortized (source := switchingProvider source offer) (target := target) rel
      (switchingCharge offer (offerCharge offer proposalCost conversionCost) operationCost)
      (fun right request => referenceCost right request + allowance right request) potential := by
  intro base index left right related request
  have chosen := choose_preserves_relation rel offer sound left right request related
  have op := operationBound (choose offer left request) right chosen request
  have migration := migrationBound left right related request
  dsimp only [switchingCharge, switchingProvider] at ⊢
  dsimp only at op migration ⊢
  omega

/-- The whole interaction includes every proposal and accepted conversion,
including those followed by an early client return or a scheduler pause. -/
theorem switching_advance_amortized
    (client : Client (P := P) (Return := Return))
    (rel : StateRel source target) (localLaw : Bisimulation rel)
    (offer : Offer source) (sound : RelationalSoundOffer rel offer)
    (proposalCost : Charge source) (conversionCost : ConversionCharge source)
    (operationCost : Charge source) (referenceCost allowance : Charge target)
    (potential : Potential source)
    (operationBound : RelationalAmortized rel operationCost referenceCost potential)
    (migrationBound : MigrationAmortized rel offer proposalCost conversionCost allowance potential)
    (budget : Nat) {base : Base}
    {left : Packet (switchingProvider source offer) client base}
    {right : Packet target client base}
    (related : PacketRel (source := switchingProvider source offer) (target := target)
      client rel left right) :
    let actual := advance (switchingProvider source offer) client
      (switchingCharge offer (offerCharge offer proposalCost conversionCost) operationCost)
      budget left
    let reference := advance target client
      (fun right request => referenceCost right request + allowance right request) budget right
    OutcomeRel (source := switchingProvider source offer) (target := target) client rel
        actual.2 reference.2 ∧
      actual.1 + outcomePotential (source := switchingProvider source offer) client potential actual.2 ≤
        reference.1 + potential left.2.2 :=
  advance_relational_resource_contract (source := switchingProvider source offer)
    (target := target) client rel
    (switching_bisimulation rel localLaw offer sound) _ _ potential
    (relational_amortized_switching rel offer sound proposalCost conversionCost operationCost
      referenceCost allowance potential operationBound migrationBound) budget related

/-- Receipt scaling scales accumulated work exactly; it leaves execution and
all client choices untouched. -/
theorem advance_charge_scale (client : Client (P := P) (Return := Return))
    (cost : Charge source) (factor budget : Nat) {base : Base}
    (packet : Packet source client base) :
    (advance source client (fun state request => factor * cost state request) budget packet).1 =
      factor * (advance source client cost budget packet).1 := by
  induction budget generalizing packet with
  | zero => simp [advance]
  | succ budget ih =>
      rcases packet with ⟨index, control, state⟩
      cases layer : client.str base index control with
      | mk shape children =>
          cases shape with
          | inl value => simp [advance, layer]
          | inr request =>
              dsimp only [withHoles] at children
              simp only [advance, layer]
              dsimp only [withHoles]
              rw [ih, Nat.mul_add]

/-- Independent receipt coordinates add, even when a client stops early. -/
theorem advance_charge_add (client : Client (P := P) (Return := Return))
    (first second : Charge source) (budget : Nat) {base : Base}
    (packet : Packet source client base) :
    (advance source client (fun state request => first state request + second state request)
        budget packet).1 =
      (advance source client first budget packet).1 +
        (advance source client second budget packet).1 := by
  induction budget generalizing packet with
  | zero => simp [advance]
  | succ budget ih =>
      rcases packet with ⟨index, control, state⟩
      cases layer : client.str base index control with
      | mk shape children =>
          cases shape with
          | inl value => simp [advance, layer]
          | inr request =>
              dsimp only [withHoles] at children
              simp only [advance, layer]
              dsimp only [withHoles]
              rw [ih]
              omega

namespace RelationalAmortizedControls

open Sequence

abbrev representations := Controls.representations
abbrev provider := familyProvider representations
abbrev decode : Hom provider (tails Nat) :=
  familyHom representations (tails Nat) Controls.representationHom

def related : StateRel provider (tails Nat) := fun left right => decode.map left = right

def inverseRelated : StateRel (tails Nat) provider :=
  fun left right => left = decode.map right

/-- Both concrete layouts genuinely realize the same duplicate-preserving
sequence, so this relation is not the graph of a function into physical state. -/
theorem inverse_relation_not_single_valued :
    ∃ (items : (tails Nat).State () ()) (first second : provider.State () ()),
      inverseRelated items first ∧ inverseRelated items second ∧ first ≠ second := by
  refine ⟨[7, 7, 9], ⟨false, [7, 7, 9]⟩,
    ⟨true, ⟨#[7, 7, 9], 0, 3⟩⟩, rfl, rfl, ?_⟩
  intro same
  have impossible := congrArg Sigma.fst same
  cases impossible

/-- A cost contract over this many-valued relation works for arbitrary
clients and both representations, without constructing an inverse decoder. -/
theorem inverse_relation_prefix_contract
    {Result : Unit → Unit → Type}
    (client : Client (P := protocol Nat) (Return := Result))
    (budget : Nat) (index : Unit) (control : client.V () index)
    (items : (tails Nat).State () index) (state : provider.State () index)
    (related : inverseRelated items state) :
    OutcomeRel client inverseRelated
        (advance (tails Nat) client (fun _ _ => 1) budget ⟨index, control, items⟩).2
        (advance provider client (fun _ _ => 1) budget ⟨index, control, state⟩).2 ∧
      (advance (tails Nat) client (fun _ _ => 1) budget ⟨index, control, items⟩).1 ≤
        (advance provider client (fun _ _ => 1) budget ⟨index, control, state⟩).1 := by
  have contract := advance_relational_resource_contract client inverseRelated
    decode.inverse_bisimulation (fun _ _ => 1) (fun _ _ => 1) (fun _ => 0)
    (by intro base index left right related request; simp) budget (.same control related)
  constructor
  · exact contract.1
  · have bound := contract.2
    cases outcome : (advance (tails Nat) client (fun _ _ => 1) budget
      ⟨index, control, items⟩).2 <;> simp [outcomePotential, outcome] at bound <;> exact bound

/-- Credit is carried only by a list awaiting promotion, and equals the
number of children that converting that list will copy. -/
def credit : Potential provider := fun state => match state with
  | ⟨false, items⟩ => items.length
  | ⟨true, _⟩ => 0

/-- Logical materialization volume is the current residual length, never
the original input length. Additional conversion work is outside this meter. -/
def copied : ConversionCharge provider := fun state _ _ => (decode.map state).length

/-- One proposal inspection, copied children on acceptance, one protocol
operation. Refusing a proposal therefore still costs two units in total. -/
def actualCost (offer : Offer provider) : Charge (switchingProvider provider offer) :=
  switchingCharge offer (offerCharge offer (fun _ _ => 1) copied) (fun _ _ => 1)

theorem operation_account :
    RelationalAmortized related (fun _ _ => 1) (fun _ _ => 1) credit := by
  intro base index left right _ request
  rcases left with ⟨backend, state⟩
  cases backend with
  | false => cases state <;> simp [credit, provider, familyProvider, representations,
      Controls.representations, tails]
  | true =>
      change 1 + credit ⟨true, ((slices Nat).step state request).2⟩ ≤ 1 + credit ⟨true, state⟩
      rfl

/-- Accepted promotion spends the list's credit once. Later refused
proposals pay their inspection from the explicit per-operation allowance. -/
theorem promotion_account :
    MigrationAmortized related Controls.promote (fun _ _ => 1) copied
      (fun _ _ => 1) credit := by
  intro base index left right _ request
  rcases left with ⟨backend, state⟩
  cases backend with
  | false =>
      simp [offerCharge, Controls.promote, copied, decode, familyHom,
        Controls.representationHom, Hom.id, choose, credit, Option.getD]
  | true =>
      simp [offerCharge, Controls.promote, choose, credit, Option.getD]

/-- Every finite interactive prefix pays at most two units per reference
request, plus the initial conversion credit. The client may stop or suspend
at any point, and may choose future requests from previous replies. -/
theorem promotion_prefix_bound
    {Result : Unit → Unit → Type}
    (client : Client (P := protocol Nat) (Return := Result))
    (budget : Nat) (index : Unit) (control : client.V () index)
    (state : provider.State () index) :
    (advance (switchingProvider provider Controls.promote) client (actualCost Controls.promote)
        budget ⟨index, control, state⟩).1 ≤
      2 * (advance (tails Nat) client (fun _ _ => 1)
        budget ⟨index, control, decode.map state⟩).1 + credit state := by
  have bound := (switching_advance_amortized client related (Hom.bisimulation decode)
    Controls.promote RelationalTransferControls.promotion_is_relationally_sound
    (fun _ _ => 1) copied (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1)
    credit operation_account promotion_account budget
    (left := ⟨index, control, state⟩)
    (right := ⟨index, control, decode.map state⟩) (.same control rfl)).2
  have scale := advance_charge_scale (source := tails Nat) client (fun _ _ => 1)
    2 budget (base := ()) ⟨index, control, decode.map state⟩
  dsimp only at bound scale
  change (advance (tails Nat) client (fun _ _ => 2)
      budget ⟨index, control, decode.map state⟩).1 = _ at scale
  change _ ≤ (advance (tails Nat) client (fun _ _ => 2)
      budget ⟨index, control, decode.map state⟩).1 + credit state at bound
  rw [scale] at bound
  change _ ≤ _
  exact Nat.le_trans (Nat.le_add_right _ _) bound

/-- Complete promotion is linear in input size in the declared meter,
including the final exhaustion request and refused proposals. -/
theorem promotion_complete_bound {Accumulator : Type}
    (consume : Accumulator → Nat → Accumulator) (items : List Nat) (initial : Accumulator) :
    (advance (switchingProvider provider Controls.promote) (Fold.client consume)
        (actualCost Controls.promote) (items.length + 2)
        (Fold.start _ consume ⟨false, items⟩ initial)).1 ≤ 3 * items.length + 2 := by
  have bound := promotion_prefix_bound (Fold.client consume) (items.length + 2) ()
    (.pulling initial) ⟨false, items⟩
  have reference := congrArg Prod.fst (Fold.complete_exact consume items initial)
  dsimp only [decode, familyHom, Controls.representationHom, Hom.id, credit] at bound
  change (advance (tails Nat) (Fold.client consume) (fun _ _ => 1)
    (items.length + 2) ⟨(), .pulling initial, items⟩).1 = items.length + 1 at reference
  rw [reference] at bound
  dsimp only [Fold.start] at ⊢
  omega

/-- This offer alternates real list and slice residuals. Every accepted
migration materializes the remaining children again. -/
def oscillate : Offer provider := fun state _ => match state with
  | ⟨false, items⟩ => some ⟨true, ⟨items.toArray, 0, items.length⟩⟩
  | ⟨true, view⟩ => some ⟨false, (sliceHom Nat).map view⟩

theorem oscillate_sound : SoundOffer decode oscillate := by
  intro base index state next request offered
  rcases state with ⟨backend, state⟩
  cases backend with
  | false =>
      have equal : (⟨true, ⟨state.toArray, 0, state.length⟩⟩ : provider.State base index) = next :=
        Option.some.inj offered
      rw [← equal]
      simp [decode, familyHom, Controls.representationHom, sliceHom, Hom.id]
      exact List.take_length
  | true =>
      have equal : (⟨false, (sliceHom Nat).map state⟩ : provider.State base index) = next :=
        Option.some.inj offered
      rw [← equal]
      rfl

theorem oscillate_relationally_sound : RelationalSoundOffer related oscillate :=
  (relationalSoundOffer_graph_iff decode oscillate).mpr oscillate_sound

/-- A semantics-preserving offer may incur residual-length work at every
request. The two fixed units account for proposal and provider operation. -/
theorem oscillate_step_charge {base index : Unit}
    (state : provider.State base index) (request : (protocol Nat).Shape base index) :
    actualCost oscillate state request = (decode.map state).length + 2 := by
  rcases state with ⟨backend, state⟩
  cases backend <;> simp [actualCost, switchingCharge, offerCharge, oscillate, copied]
  all_goals omega

/-- The exact accumulated oscillation meter still comes from execution of
the original adaptive client, rather than a separate cost-only recurrence. -/
theorem oscillate_prefix_exact
    {Result : Unit → Unit → Type}
    (client : Client (P := protocol Nat) (Return := Result))
    (budget : Nat) (packet : Packet (switchingProvider provider oscillate) client ()) :
    (advance (switchingProvider provider oscillate) client (actualCost oscillate)
        budget packet).1 =
      (advance (tails Nat) client (fun items _ => items.length + 2) budget
        ((switchingHom decode oscillate oscillate_sound).packet client packet)).1 := by
  apply Hom.advance_charge client (switchingHom decode oscillate oscillate_sound)
  intro base index state request
  exact oscillate_step_charge state request

/-- Oscillation over an entire input incurs a triangular copying term,
although the ordinary cursor executes only one request per element. -/
theorem oscillate_complete_exact {Accumulator : Type}
    (consume : Accumulator → Nat → Accumulator) (items : List Nat) (initial : Accumulator) :
    (advance (switchingProvider provider oscillate) (Fold.client consume)
        (actualCost oscillate) (items.length + 2)
        (Fold.start _ consume ⟨false, items⟩ initial)).1 =
      SequenceCost.triangular items.length + 2 * (items.length + 1) := by
  rw [oscillate_prefix_exact]
  change (advance (tails Nat) (Fold.client consume)
    (fun items _ => items.length + 2) (items.length + 2)
    (Fold.start _ consume items initial)).1 = _
  change (advance (tails Nat) (Fold.client consume)
    (fun state request => SequenceCost.copyingReference Nat state request + 2)
    (items.length + 2) (Fold.start _ consume items initial)).1 = _
  rw [advance_charge_add (source := tails Nat) (Fold.client consume)
    (SequenceCost.copyingReference Nat) (fun _ _ => 2)]
  rw [SequenceCost.fold_complete_visits consume items initial]
  have scale := advance_charge_scale (source := tails Nat) (Fold.client consume)
    (fun _ _ => 1) 2 (items.length + 2) (Fold.start _ consume items initial)
  change (advance (tails Nat) (Fold.client consume) (fun _ _ => 2)
    (items.length + 2) (Fold.start _ consume items initial)).1 = _ at scale
  rw [scale, Fold.complete_exact]

/-- For any proposed constant multiplicative bound against reference pulls,
a finite input defeats it while all returned answers remain correct. -/
theorem oscillation_has_no_uniform_factor (factor : Nat) :
    ∃ items : List Nat,
      factor * (advance (tails Nat) (Fold.client (fun n _ => n + 1)) (fun _ _ => 1)
          (items.length + 2) (Fold.start _ (fun n _ => n + 1) items 0)).1 <
        (advance (switchingProvider provider oscillate) (Fold.client (fun n _ => n + 1))
          (actualCost oscillate) (items.length + 2)
          (Fold.start _ (fun n _ => n + 1) ⟨false, items⟩ 0)).1 := by
  refine ⟨List.replicate (2 * factor + 1) 0, ?_⟩
  rw [oscillate_complete_exact, Fold.complete_exact]
  simp only [List.length_replicate]
  have triangle := SequenceCost.triangular_closed (2 * factor + 1)
  nlinarith

/-- The credit account that licenses one-way promotion rejects oscillation:
converting a slice back to a list both spends work and recreates unfunded credit. -/
theorem oscillation_is_not_prepaid :
    ¬ MigrationAmortized related oscillate (fun _ _ => 1) copied (fun _ _ => 1) credit := by
  intro account
  have impossible := account (base := ()) (index := ())
    ⟨true, ⟨#[7, 8, 9], 0, 3⟩⟩ [7, 8, 9] rfl ()
  change 7 ≤ 1 at impossible
  omega

/-- A stopped client performs no proposal at all. -/
theorem no_request_no_proposal :
    (advance (switchingProvider provider Controls.promote) Controls.answerClient
      (actualCost Controls.promote) 1
      (base := ()) ⟨(), Free.pure (protocol Nat) [], ⟨false, [7, 8, 9]⟩⟩).1 = 0 := rfl

/-- Refusal is not free: the already-promoted representation pays proposal
inspection and one request, but no copied children. -/
theorem refused_promotion_charged :
    (advance (switchingProvider provider Controls.promote) Controls.answerClient
      (actualCost Controls.promote) 2
      (base := ()) ⟨(), Controls.onePull, ⟨true, ⟨#[7, 8, 9], 0, 3⟩⟩⟩).1 = 2 := rfl

/-- Early return preserves answers but cannot refund a conversion already
performed before the first request. -/
theorem early_return_pays_conversion :
    (advance (switchingProvider provider Controls.promote) Controls.answerClient
      (actualCost Controls.promote) 2
      (base := ()) ⟨(), Controls.onePull, ⟨false, [7, 8, 9]⟩⟩).1 = 5 := rfl

end RelationalAmortizedControls

end Mettapedia.Machines.Cursor
