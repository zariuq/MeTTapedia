import Mettapedia.Machines.Cursor.Protocol

/-!
# Relational cursor refinement

Not every representation has a preferred function into one canonical store.
A relation between stores is enough: each request must produce the same
reply and related successor states. The relation then lifts to arbitrary
bounded clients, preserving termination versus suspension and live control.

This is a strong protocol-level bisimulation. Implementations may perform
different internal work inside an operation; divergent internal work must be
exposed through resumable replies before these total-step laws apply.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial

universe u

variable {Base : Type u} {Index : Base → Type u}
variable {P : IndexedPolynomial.{u,u,u,u} Base Index}

abbrev StateRel (source target : Provider P) :=
  {base : Base} → {index : Index base} → source.State base index →
    target.State base index → Prop

variable {source target : Provider P}

/-- Equal replies at a common request determine the same successor capability. -/
def Bisimulation (rel : StateRel source target) : Prop :=
  ∀ {base index} (left : source.State base index) (right : target.State base index),
    rel left right → ∀ request : P.Shape base index,
      ∃ (reply : P.Position request)
        (left' : source.State base (P.next request reply))
        (right' : target.State base (P.next request reply)),
        source.step left request = ⟨reply, left'⟩ ∧
        target.step right request = ⟨reply, right'⟩ ∧ rel left' right'

variable {Return : (base : Base) → Index base → Type u}
variable (C : Client (P := P) (Return := Return)) (rel : StateRel source target)

inductive PacketRel {base : Base} : Packet source C base → Packet target C base → Prop
  | same {index : Index base} (control : C.V base index)
      {left : source.State base index} {right : target.State base index}
      (related : rel left right) :
      PacketRel ⟨index, control, left⟩ ⟨index, control, right⟩

inductive OutcomeRel {base : Base} : Outcome source C base → Outcome target C base → Prop
  | paused {left right} (related : PacketRel C rel left right) :
      OutcomeRel (.paused left) (.paused right)
  | done {index : Index base} (value : Return base index)
      {left : source.State base index} {right : target.State base index}
      (related : rel left right) :
      OutcomeRel (.done ⟨index, value, left⟩) (.done ⟨index, value, right⟩)

/-- Local relational refinement preserves every bounded interaction, without
assuming either store is computably reconstructible from the other. -/
theorem advance_related (localLaw : Bisimulation rel)
    (leftCost : Charge source) (rightCost : Charge target)
    (budget : Nat) {base : Base} {left : Packet source C base} {right : Packet target C base}
    (related : PacketRel C rel left right) :
    OutcomeRel C rel (advance source C leftCost budget left).2
      (advance target C rightCost budget right).2 := by
  induction budget generalizing left right with
  | zero => exact .paused related
  | succ budget ih =>
      cases related with
      | @same index control left right related =>
          cases layer : C.str base index control with
          | mk shape children =>
              cases shape with
              | inl value =>
                  simp only [advance, layer]
                  exact .done value related
              | inr request =>
                  dsimp only [withHoles] at children
                  obtain ⟨reply, left', right', leftStep, rightStep, nextRelated⟩ :=
                    localLaw left right related request
                  simp only [advance, layer]
                  dsimp only [withHoles]
                  rw [leftStep, rightStep]
                  exact ih (.same (children reply) nextRelated)

/-- Functional representation maps are a special case of the relational law. -/
theorem Hom.bisimulation (h : Hom source target) :
    Bisimulation (fun left right => h.map left = right) := by
  intro base index left right related request
  subst right
  refine ⟨(source.step left request).1, (source.step left request).2,
    h.map (source.step left request).2, ?_, ?_, rfl⟩
  · rfl
  · exact (h.step left request).symm

/-- Both providers retain the same replies. Reversing the store relation
requires no preferred representative or inverse function. -/
theorem Bisimulation.symm (localLaw : Bisimulation rel) :
    Bisimulation (source := target) (target := source) (fun right left => rel left right) := by
  intro base index right left related request
  obtain ⟨reply, left', right', leftStep, rightStep, following⟩ :=
    localLaw left right related request
  exact ⟨reply, right', left', rightStep, leftStep, following⟩

theorem PacketRel.symm {base : Base}
    {left : Packet source C base} {right : Packet target C base}
    (related : PacketRel C rel left right) :
    PacketRel C (source := target) (target := source)
      (fun right left => rel left right) right left := by
  cases related with
  | same control related => exact .same control related

theorem OutcomeRel.symm {base : Base}
    {left : Outcome source C base} {right : Outcome target C base}
    (related : OutcomeRel C rel left right) :
    OutcomeRel C (source := target) (target := source)
      (fun right left => rel left right) right left := by
  cases related with
  | paused related => exact .paused (PacketRel.symm C rel related)
  | done value related => exact .done value related

/-- One independently calibrated metric agrees on related states at each
actual request. Transition refinement alone does not imply this law. -/
def ChargeRelated (leftCost : Charge source) (rightCost : Charge target) : Prop :=
  ∀ {base index} (left : source.State base index) (right : target.State base index),
    rel left right → ∀ request, leftCost left request = rightCost right request

theorem ChargeRelated.symm (leftCost : Charge source) (rightCost : Charge target)
    (localCharge : ChargeRelated rel leftCost rightCost) :
    ChargeRelated (source := target) (target := source)
      (fun right left => rel left right) rightCost leftCost := by
  intro base index right left related request
  exact (localCharge left right related request).symm

/-- Retain the already paid account together with the complete outcome.
The residual control, capability and provider state remain related. -/
def AccountRel {base : Base}
    (left : Nat × Outcome source C base) (right : Nat × Outcome target C base) : Prop :=
  left.1 = right.1 ∧ OutcomeRel C rel left.2 right.2

variable {middle : Provider P}

/-- Store comparisons compose through an actual intermediate store, without
selecting a canonical representative of either physical representation. -/
def StateRel.comp (first : StateRel source middle) (second : StateRel middle target) :
    StateRel source target :=
  fun left right => ∃ bridge, first left bridge ∧ second bridge right

theorem Bisimulation.comp (first : StateRel source middle) (second : StateRel middle target)
    (firstLaw : Bisimulation first) (secondLaw : Bisimulation second) :
    Bisimulation (StateRel.comp first second) := by
  intro base index left right related request
  obtain ⟨bridge, leftRelated, rightRelated⟩ := related
  obtain ⟨reply, left', bridge', leftStep, bridgeStep, leftFollowing⟩ :=
    firstLaw left bridge leftRelated request
  obtain ⟨otherReply, otherBridge, right', otherStep, rightStep, rightFollowing⟩ :=
    secondLaw bridge right rightRelated request
  have middleSame : (⟨reply, bridge'⟩ : Σ value, middle.State base (P.next request value)) =
      ⟨otherReply, otherBridge⟩ := bridgeStep.symm.trans otherStep
  obtain ⟨replySame, worldSame⟩ := Sigma.mk.inj_iff.mp middleSame
  cases replySame
  have worldEqual := eq_of_heq worldSame
  cases worldEqual
  exact ⟨reply, left', right', leftStep, rightStep,
    bridge', leftFollowing, rightFollowing⟩

theorem PacketRel.comp (first : StateRel source middle) (second : StateRel middle target)
    {base : Base} {left : Packet source C base} {bridge : Packet middle C base}
    {right : Packet target C base} (leftRelated : PacketRel C first left bridge)
    (rightRelated : PacketRel C second bridge right) :
    PacketRel C (StateRel.comp first second) left right := by
  cases leftRelated with
  | same control leftRelated =>
      cases rightRelated with
      | same _ rightRelated => exact .same control ⟨_, leftRelated, rightRelated⟩

theorem OutcomeRel.comp (first : StateRel source middle) (second : StateRel middle target)
    {base : Base} {left : Outcome source C base} {bridge : Outcome middle C base}
    {right : Outcome target C base} (leftRelated : OutcomeRel C first left bridge)
    (rightRelated : OutcomeRel C second bridge right) :
    OutcomeRel C (StateRel.comp first second) left right := by
  cases leftRelated with
  | paused leftRelated =>
      cases rightRelated with
      | paused rightRelated =>
          exact .paused (PacketRel.comp C first second leftRelated rightRelated)
  | done value leftRelated =>
      cases rightRelated with
      | done _ rightRelated => exact .done value ⟨_, leftRelated, rightRelated⟩

theorem ChargeRelated.comp (first : StateRel source middle) (second : StateRel middle target)
    (leftCost : Charge source) (middleCost : Charge middle) (rightCost : Charge target)
    (leftLaw : ChargeRelated first leftCost middleCost)
    (rightLaw : ChargeRelated second middleCost rightCost) :
    ChargeRelated (StateRel.comp first second) leftCost rightCost := by
  intro base index left right related request
  obtain ⟨bridge, leftRelated, rightRelated⟩ := related
  exact (leftLaw left bridge leftRelated request).trans
    (rightLaw bridge right rightRelated request)

/-- Composition retains the intermediate account, including its paid work
and exact completion or suspension status. No execution is performed here. -/
theorem AccountRel.comp (first : StateRel source middle) (second : StateRel middle target)
    {base : Base} {left : Nat × Outcome source C base} {bridge : Nat × Outcome middle C base}
    {right : Nat × Outcome target C base} (leftRelated : AccountRel C first left bridge)
    (rightRelated : AccountRel C second bridge right) :
    AccountRel C (StateRel.comp first second) left right :=
  ⟨leftRelated.1.trans rightRelated.1,
    OutcomeRel.comp C first second leftRelated.2 rightRelated.2⟩

/-- Retain both actual provider states and their established relation. This
carrier selects no representative from a relation's fibre. -/
abbrev RelatedStates {base : Base} {index : Index base} :=
  { pair : source.State base index × target.State base index // rel pair.1 pair.2 }

private theorem relatedReplies {base : Base} {index : Index base}
    (request : P.Shape base index)
    (left : Σ reply : P.Position request, source.State base (P.next request reply))
    (right : Σ reply : P.Position request, target.State base (P.next request reply))
    (common : ∃ (reply : P.Position request)
      (left' : source.State base (P.next request reply))
      (right' : target.State base (P.next request reply)),
      left = ⟨reply, left'⟩ ∧ right = ⟨reply, right'⟩ ∧ rel left' right') :
    ∃ same : left.1 = right.1, rel left.2 (same.symm ▸ right.2) := by
  obtain ⟨reply, left', right', rfl, rfl, following⟩ := common
  exact ⟨rfl, following⟩

/-- A constructive common provider executes the two supplied local steps.
The bisimulation supplies only reply equality and successor relatedness;
no state is selected from erased existential evidence. -/
def Bisimulation.coupledProvider (localLaw : Bisimulation rel) : Provider P where
  State _ _ := RelatedStates rel
  step state request := by
    let left := source.step state.val.1 request
    let right := target.step state.val.2 request
    have aligned : ∃ same : left.1 = right.1, rel left.2 (same.symm ▸ right.2) :=
      relatedReplies rel request left right
        (localLaw state.val.1 state.val.2 state.property request)
    have sameReply : left.1 = right.1 := by
      obtain ⟨same, _⟩ := aligned
      exact same
    have follows : rel left.2 (sameReply.symm ▸ right.2) := by
      obtain ⟨same, following⟩ := aligned
      exact following
    exact ⟨left.1, ⟨⟨left.2, sameReply.symm ▸ right.2⟩, follows⟩⟩

/-- Projection to the first physical representation preserves the actual
request, reply and successor capability. -/
def Bisimulation.leftProjection (localLaw : Bisimulation rel) :
    Hom (Bisimulation.coupledProvider rel localLaw) source where
  map state := state.val.1
  step state request := by
    rfl

/-- The second projection is lawful even when the relation is many-valued.
It transports only along the independently established reply equality. -/
def Bisimulation.rightProjection (localLaw : Bisimulation rel) :
    Hom (Bisimulation.coupledProvider rel localLaw) target where
  map state := state.val.2
  step state request := by
    have sameReply : (source.step state.val.1 request).1 =
        (target.step state.val.2 request).1 := by
      obtain ⟨same, _⟩ := relatedReplies rel request
        (source.step state.val.1 request) (target.step state.val.2 request)
        (localLaw state.val.1 state.val.2 state.property request)
      exact same
    apply Sigma.ext
    · exact sameReply
    · exact eqRec_heq (φ := fun reply => target.State _ (P.next request reply))
        sameReply.symm (target.step state.val.2 request).2

/-- The common provider retains a related pair after every transition. Its
projection span is a realization of the relation, not a selected inverse. -/
theorem Bisimulation.projections_related (localLaw : Bisimulation rel)
    {base : Base} {index : Index base}
    (state : (Bisimulation.coupledProvider rel localLaw).State base index) :
    rel ((Bisimulation.leftProjection rel localLaw).map state)
      ((Bisimulation.rightProjection rel localLaw).map state) := state.property



end Mettapedia.Machines.Cursor
