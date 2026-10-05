import Mettapedia.GSLT.Distinction.SpanTransport
import Mettapedia.GSLT.Logic.ObservationSpanControls
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Controls for two-sided span transport

| Control | Theorems |
|---|---|
| The forward observer's future-equal, past-different fibre | `forward_observer_fiber`, `forward_bisimilar`, `not_twoSided_bisimilar`, `relative_no_targetBack` |
| The same pair on a machine, with a cost simulation each way | `pastMachine_simulation`, `pastMachine_observe_eq`, `pastMachine_future_related`, `pastMachine_fiber`, `pastMachine_no_targetBack` |
| Finitely many successors, infinitely many predecessors | `toZero_successors_finite`, `toZero_predecessors_infinite`, `toZero_not_twoSided_finite` |
| Two different states that are two-sided bisimilar | `toZero_twoSided_bisimilar` |
| Incoming events: what endpoints, labels and occurrences keep | `endpoints_agree`, `different_labels_distinguished`, `duplicates_agree`, `duplicates_counted` |
| An added parallel occurrence | `added_occurrence_modal_laws`, `added_occurrence_not_matched` |
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.SpanTransport.Controls

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.GSLT.Core.NonFactorization (NonTrivialFiber)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-! ## The forward observer's fibre -/

namespace Passed

open Mettapedia.GSLT.ObservationSpans.Controls.DifferentPasts

/-- **The future-equal, past-different pair is a non-trivial fibre of the
forward observer**: the saturated relative observation identifies the entered
and the isolated terminal, and the past box separates them. -/
def forward_observer_fiber :
    NonTrivialFiber (relativeObserve admissible observations)
      (fun state => gsltBox theory (fun _ => False) state) where
  left := State.entered
  right := State.isolated
  sameShadow := observed_terminals_equal
  differentValue := by
    intro same
    exact past_box_distinguishes.2 (same ▸ past_box_distinguishes.1)

/-- The forward system: one label for the step. -/
def forward : System theory where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Unit
  act _ := step
  act_resp_left := by
    rintro _ _ _ target rfl acts
    exact ⟨target, acts, rfl⟩
  act_resp_right := by
    rintro _ _ _ _ acts rfl
    exact acts

theorem forward_agrees : StepAgreement forward :=
  fun _ _ => ⟨fun step => ⟨(), step⟩, fun ⟨_, step⟩ => step⟩

/-- The two terminals are forward bisimilar. -/
theorem forward_bisimilar : forward.Bisimilar State.entered State.isolated := by
  refine ⟨fun left right => view left = view right, ⟨?_, ?_, ?_⟩, rfl⟩
  · intro left right related _ next acts
    obtain ⟨next', step', related'⟩ := view_bisimulation.1 related acts
    exact ⟨next', step', related'⟩
  · intro left right related _ next acts
    obtain ⟨next', step', related'⟩ := view_bisimulation.2 related acts
    exact ⟨next', step', related'⟩
  · intro _ _ _ atom
    exact atom.elim

/-- **... and not two-sided bisimilar**: the entered terminal has a predecessor
and the isolated one has none. -/
theorem not_twoSided_bisimilar : ¬ (twoSided forward).Bisimilar State.entered State.isolated := by
  rintro ⟨relation, bisimulation, related⟩
  obtain ⟨_, pastForth, _⟩ := (twoSided_isBisimulation_iff forward relation).mp bisimulation
  obtain ⟨_, acts, _⟩ := pastForth related () (x' := State.predecessor) ⟨rfl, rfl⟩
  exact isolated_has_no_predecessor ⟨_, acts⟩

/-- The relative observation has the source back law and not the target back
law. -/
theorem relative_no_targetBack :
    SourceBack (gsltSpan theory) (relativeSpan admissible observations)
        (relativeGraph admissible observations) ∧
      ¬ TargetBack (gsltSpan theory) (relativeSpan admissible observations)
        (relativeGraph admissible observations) :=
  ⟨relative_sourceBack admissible observations,
    fun back => no_target_lifting ((spanMap_targetBack_iff (relativeMap admissible observations)).mp back)⟩

end Passed

/-! ## The same pair on a machine -/

namespace PastMachine

inductive Node where
  | predecessor | entered | isolated
  deriving DecidableEq

/-- The predecessor publishes one event and enters; both terminals finish. -/
def machine : Machine Node Unit Unit Empty where
  step
    | .predecessor => some (.publish [()] .entered)
    | .entered => some (.finish ())
    | .isolated => some (.finish ())

/-- The forward view: the two terminals look alike. -/
def view : Node → Bool
  | .predecessor => false
  | _ => true

def related (left right : Node) : Prop := view left = view right

theorem simulation_of_view : CostSimulation machine machine related 1 where
  silent := by
    intro state _ _ _ stepped
    cases state <;> cases stepped
  publish := by
    intro state state' events next relatedStates stepped
    cases state <;> cases stepped
    cases state' <;> cases relatedStates
    exact ⟨1, le_rfl, .entered, rfl, rfl⟩
  finish := by
    intro state state' verdict relatedStates stepped
    cases state <;> cases stepped <;> cases state' <;> cases relatedStates <;>
      exact ⟨1, le_rfl, rfl⟩
  fail := by
    intro state _ _ _ stepped
    cases state <;> cases stepped
  call := by
    intro state _ _ _ _ stepped
    cases state <;> cases stepped

/-- **A cost-one simulation each way**: the view relation is symmetric. -/
theorem pastMachine_simulation :
    CostSimulation machine machine related 1 ∧
      CostSimulation machine machine (fun state' state => related state state') 1 := by
  refine ⟨simulation_of_view, ?_⟩
  have symmetric : (fun state' state => related state state') = related := by
    funext left right
    exact propext ⟨Eq.symm, Eq.symm⟩
  rw [symmetric]
  exact simulation_of_view

/-- **Positive**: the predecessor's complete run is matched with an equal
observation. -/
theorem pastMachine_observe_eq :
    ∃ k ≤ 1 * 2, machine.observe k Node.predecessor = machine.observe 2 Node.predecessor :=
  simulation_of_view.observe_eq 2 (rfl : related Node.predecessor Node.predecessor) (by
    intro stuckAt stuck
    simp [Machine.run, machine] at stuck)

/-- No atomic observation. -/
def noAtoms : Empty → Node → Prop := fun atom _ => atom.elim

/-- Every future formula over published events agrees on the two terminals. -/
theorem pastMachine_future_related {formula : Tense Empty (List Unit)} (future : formula.IsFuture) :
    Tense.sat (machine.segments noAtoms) formula Node.entered ↔
      Tense.sat (machine.segments noAtoms) formula Node.isolated :=
  CostSimulation.future_related pastMachine_simulation.1 pastMachine_simulation.2 noAtoms noAtoms
    (fun atom => atom.elim) future (rfl : related Node.entered Node.isolated)

/-- No run segment publishing an event ends at the isolated terminal. -/
theorem no_segment_into_isolated (segment : Segment machine) (ends : segment.residual = .isolated) :
    segment.events = [] := by
  obtain ⟨start, fuel, events, residual, ran⟩ := segment
  change residual = .isolated at ends
  subst ends
  change events = []
  rcases fuel with _ | _ | fuel <;> cases start <;> simp_all [Machine.run, machine]

/-- The segment that publishes the event and enters. -/
def entry : Segment machine := ⟨.predecessor, 1, [()], .entered, by simp [Machine.run, machine]⟩

/-- The past formula: entered after publishing the event. -/
def enteredAfterEvent : Tense Empty (List Unit) := .past [()] .top

theorem entered_has_past : Tense.sat (machine.segments noAtoms) enteredAfterEvent Node.entered :=
  ⟨entry, rfl, rfl, trivial⟩

theorem isolated_has_no_past : ¬ Tense.sat (machine.segments noAtoms) enteredAfterEvent Node.isolated := by
  rintro ⟨segment, ends, reads, _⟩
  have none := no_segment_into_isolated segment ends
  change segment.events = [()] at reads
  rw [none] at reads
  cases reads

/-- **The machine's forward observer has the same fibre**: equal observations at
every fuel, and a past formula that separates them. -/
def pastMachine_fiber :
    NonTrivialFiber (fun state (fuel : ℕ) => machine.observe fuel state)
      (fun state => Tense.sat (machine.segments noAtoms) enteredAfterEvent state) where
  left := .entered
  right := .isolated
  sameShadow := by
    funext fuel
    cases fuel <;> simp [Machine.observe, Machine.run, machine, Outcome.status]
  differentValue := by
    intro same
    exact isolated_has_no_past (same ▸ entered_has_past)

/-- **Simulations each way give no target back law.** -/
theorem pastMachine_no_targetBack :
    ¬ (segmentRelation machine machine related).TargetBackOcc := by
  intro back
  obtain ⟨segment, ends, _, _, sameEvents⟩ :=
    back (x := Node.isolated) (y := Node.entered) rfl entry rfl
  have none := no_segment_into_isolated segment ends
  rw [none] at sameEvents
  cases sameEvents

end PastMachine

/-! ## Finitely many successors, infinitely many predecessors -/

namespace ToZero

/-- Every number steps to `0`. -/
abbrev theory : GSLT where
  Term := ℕ
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites _ target := target = 0
  rewrites_resp_left := by
    rintro _ _ target rfl step
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    rintro _ _ _ step rfl
    exact step

def system : System theory where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Unit
  act _ source target := theory.Step source target
  act_resp_left := by
    rintro _ _ _ target rfl acts
    exact ⟨target, acts, rfl⟩
  act_resp_right := by
    rintro _ _ _ _ acts rfl
    exact acts

theorem toZero_successors_finite : system.ImageFiniteModulo := by
  intro _ _
  refine ⟨{0}, Set.finite_singleton 0, ?_⟩
  intro target acts
  exact ⟨0, Set.mem_singleton 0, acts⟩

theorem toZero_predecessors_infinite : ¬ PredecessorFiniteModulo system := by
  intro finite
  obtain ⟨representatives, isFinite, covers⟩ := finite () 0
  apply Set.infinite_univ (α := ℕ)
  refine isFinite.subset fun n _ => ?_
  obtain ⟨representative, member, same⟩ := covers (source := n) rfl
  have equal : n = representative := same
  exact equal ▸ member

/-- **Positive**: two different nonzero numbers are two-sided bisimilar; neither
has a predecessor, and both step to `0`, whose predecessors match. -/
theorem toZero_twoSided_bisimilar : (twoSided system).Bisimilar (1 : ℕ) (2 : ℕ) := by
  refine ⟨fun left right => (left = (0 : ℕ) ↔ right = (0 : ℕ)), ?_, by decide⟩
  rw [twoSided_isBisimulation_iff]
  refine ⟨⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, ?_, ?_⟩
  · intro left right _ _ next acts
    have nextZero : next = (0 : ℕ) := acts
    exact ⟨(0 : ℕ), rfl, fun _ => rfl, fun _ => nextZero⟩
  · intro left right _ _ next acts
    have nextZero : next = (0 : ℕ) := acts
    exact ⟨(0 : ℕ), rfl, fun _ => nextZero, fun _ => rfl⟩
  · intro left right related _ previous acts
    have leftZero : left = (0 : ℕ) := acts
    exact ⟨previous, related.mp leftZero, Iff.rfl⟩
  · intro left right related _ previous acts
    have rightZero : right = (0 : ℕ) := acts
    exact ⟨previous, related.mpr rightZero, Iff.rfl⟩

/-- **The two-sided observation does not branch finitely.** -/
theorem toZero_not_twoSided_finite : ¬ (twoSided system).ImageFiniteModulo :=
  fun finite => toZero_predecessors_infinite ((twoSided_imageFiniteModulo_iff system).mp finite).2

end ToZero

/-! ## Incoming events: endpoints, labels and occurrences -/

namespace Incoming

/-- Two incoming events at `true`, read `false` and `true`. -/
def labelled : Labelled Bool Empty Bool where
  span := ⟨Bool, fun _ => false, fun _ => true⟩
  read := id
  observes atom _ := atom.elim

/-- Two incoming events at `true`, both read `false`. -/
def duplicated : Labelled Bool Empty Bool where
  span := ⟨Bool, fun _ => false, fun _ => true⟩
  read _ := false
  observes atom _ := atom.elim

/-- One incoming event at `true`, read `false`. -/
def single : Labelled Bool Empty Bool where
  span := ⟨Unit, fun _ => false, fun _ => true⟩
  read _ := false
  observes atom _ := atom.elim

/-- **Endpoints keep neither labels nor multiplicities**: equality has all four
state laws between the labelled pair and the single event, so every future
diamond and past box agrees. -/
theorem endpoints_agree :
    SourceForth labelled.span single.span Eq ∧ SourceBack labelled.span single.span Eq ∧
      TargetForth labelled.span single.span Eq ∧ TargetBack labelled.span single.span Eq := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x _ rfl a sourceEq
    exact ⟨(), sourceEq, rfl⟩
  · rintro x _ rfl b sourceEq
    exact ⟨false, sourceEq, rfl⟩
  · rintro x _ rfl a targetEq
    exact ⟨(), targetEq, rfl⟩
  · rintro x _ rfl b targetEq
    exact ⟨false, targetEq, rfl⟩

/-- **Labels survive**: the labelled past separates the differently labelled
pair from the single event. -/
theorem different_labels_distinguished :
    Tense.sat labelled (.past true .top) true ∧ ¬ Tense.sat single (.past true .top) true := by
  refine ⟨⟨true, rfl, rfl, trivial⟩, ?_⟩
  rintro ⟨_, _, readEq, _⟩
  cases readEq

/-- The duplicated pair related to the single event, keeping readings. -/
def duplicatesRelation : SpanRelation duplicated.span single.span where
  states := Eq
  events first second := duplicated.read first = single.read second
  source_rel _ _ _ := rfl
  target_rel _ _ _ := rfl

/-- **Duplicates agree on every labelled tense formula.** -/
theorem duplicates_agree (formula : Tense Empty Bool) (x : Bool) :
    Tense.sat duplicated formula x ↔ Tense.sat single formula x :=
  sat_related duplicated single duplicatesRelation (fun _ _ matched => matched)
    (fun atom => atom.elim)
    (fun _ _ same _ sourceEq => ⟨(), sourceEq.trans same, rfl⟩)
    (fun _ _ same _ sourceEq => ⟨false, sourceEq.trans same.symm, rfl⟩)
    (fun _ _ same _ targetEq => ⟨(), targetEq.trans same, rfl⟩)
    (fun _ _ same _ targetEq => ⟨false, targetEq.trans same.symm, rfl⟩)
    formula rfl

/-- **Occurrences survive**: two incoming events read `false` against one, so no
relation keeping readings matches the incoming fibres. -/
theorem duplicates_counted :
    Nat.card {a : Bool // duplicated.span.target a = true ∧ duplicated.read a = false} = 2 ∧
      Nat.card {b : Unit // single.span.target b = true ∧ single.read b = false} = 1 ∧
      ∀ relation : SpanRelation duplicated.span single.span,
        relation.Keeps duplicated.read single.read → relation.states true true →
          ¬ relation.InFibresMatch := by
  have two : Nat.card {a : Bool // duplicated.span.target a = true ∧ duplicated.read a = false} = 2 := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => ⟨rfl, rfl⟩), Nat.card_eq_fintype_card,
      Fintype.card_bool]
  have one : Nat.card {b : Unit // single.span.target b = true ∧ single.read b = false} = 1 := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => ⟨rfl, rfl⟩), Nat.card_unique]
  refine ⟨two, one, fun relation keeps related fibres => ?_⟩
  have same : Nat.card {a : Bool // duplicated.span.target a = true ∧ duplicated.read a = false} =
      Nat.card {b : Unit // single.span.target b = true ∧ single.read b = false} :=
    incoming_card_eq relation fibres keeps related false
  rw [two, one] at same
  cases same

end Incoming

/-! ## An added parallel occurrence -/

namespace Added

open Mettapedia.GSLT.ObservationSpans.Controls.AddedOccurrence

/-- Both modal laws hold for the inclusion that adds an occurrence. -/
theorem added_occurrence_modal_laws :
    SourceBack authored enlarged (graph inclusion) ∧ TargetBack authored enlarged (graph inclusion) :=
  ⟨(spanMap_sourceBack_iff inclusion).mpr sourceLifts,
    (spanMap_targetBack_iff inclusion).mpr targetLifts⟩

/-- **... and its outgoing fibres do not correspond**: one occurrence against
two. -/
theorem added_occurrence_not_matched : ¬ (SpanRelation.ofSpanMap inclusion).OutFibresMatch := by
  intro fibres
  obtain ⟨matching, _⟩ := fibres (rfl : graph inclusion false false)
  have same : Nat.card {a : Bool // a = false} = Nat.card {b : Bool × Bool // b.1 = false} :=
    Nat.card_congr matching
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at same
  revert same
  decide

end Added

end Mettapedia.GSLT.Distinction.SpanTransport.Controls
