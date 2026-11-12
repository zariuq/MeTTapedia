import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AnnotatedRunsFormedProjection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunBranchCollection

/-!
# The certified computation beside a client: the frame law through the partial tensor

## The frame law

For runs separated in the sense of R26's partial tensor (`Separated`), an observation of either
run is an observation of the tensor run, and the tensor run's final store is consistent, so the
observation is not vacuous (`observes_tensor`, `observes_tensor_right`). The hypotheses are
exactly `Separated`'s:

* **shared equations**: the joint store of both runs must be consistent. Equations may share the
  certified result variable; only joint consistency is asked;
* **predicate queries**: each run's queries are blind to the other's space;
* **guards**: each run is executable from its own configuration, so every guard is judged at its
  original cut. Absence and count guards are blind to the other's space; equality guards only
  gain entailments from more equations.

## Separating cases (`FrameControls`)

The certified computation is the projection of `exampleWire`, at occurrence `0` into the result
variable `0`.

* `unrelated_client`: a second, unrelated projection at occurrence `5` into variable `20`; the
  tensor runs and keeps both observations.
* `duplicate_answers_kept`: two worlds, each the certified computation, collected by R27's
  `collectWorlds` with the entailed closed answer as the observation: the complete collection
  counts the answer twice, and its set of answers has one element.
* `incompatible_shared_equations`: a client telling the shared result variable another wire's
  data runs alone, and the tensor does not run.
* `later_equation_cannot_repair_guard`: a guard asking whether the result is already the
  payload is refused at its own cut; the joint store entails it, and the order with the guard
  first still does not run. The separation hypothesis fails.
* `query_space_needed`: a client's predicate query that no computation is pending runs alone and
  is not blind to the certified space. Placed before the certified run, beside its pending
  occurrence, it is refused; placed after, it runs. This separates blindness from
  order-independence: the frame law asks for blindness so that the order does not matter.
* `dormant_row_present`, `row_poisons`, `row_refused`: a stored row whose pending computation
  would tell the result another wire's data is present throughout; the separated valid work runs
  beside it and keeps its observation; conjoining the row's condition leaves no solution; firing
  it is refused.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed

open Mettapedia.Logic.LP
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation (Tm)
open AnnotatedRuns
open MeTTaCalculus.OccurrenceCommits (regionOf)

/-! ## The frame law -/

section Frame

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T)

/-- The tensor run's final store refines both runs' final stores. -/
theorem tensor_refines {C₁ C₂ : Configuration T O} {r₁ r₂ : List (Firing T S O)}
    (separated : Separated A label C₁ r₁ C₂ r₂) :
    Executable A label (tensor C₁ C₂) (r₁ ++ r₂) ∧
      A.Refines (follow label (tensor C₁ C₂) (r₁ ++ r₂)).equations (follow label C₁ r₁).equations ∧
      A.Refines (follow label (tensor C₁ C₂) (r₁ ++ r₂)).equations (follow label C₂ r₂).equations := by
  obtain ⟨executes, same⟩ := tensor_executable A label C₁ r₁ C₂ r₂ separated
  refine ⟨executes, fun σ solved => ?_, fun σ solved => ?_⟩
  · exact ((A.models_append σ _ _).mp ((same.1 σ).mp solved)).1
  · exact ((A.models_append σ _ _).mp ((same.1 σ).mp solved)).2

/-- **The frame law of certified observations.** A separated client leaves every observation of
the certified run in force, at a consistent final store. -/
theorem observes_tensor {C₁ C₂ : Configuration T O} {r₁ r₂ : List (Firing T S O)}
    (separated : Separated A label C₁ r₁ C₂ r₂) {result answer : T}
    (observed : Observes A (follow label C₁ r₁).equations result answer) :
    Executable A label (tensor C₁ C₂) (r₁ ++ r₂) ∧
      A.Consistent (follow label (tensor C₁ C₂) (r₁ ++ r₂)).equations ∧
      Observes A (follow label (tensor C₁ C₂) (r₁ ++ r₂)).equations result answer := by
  obtain ⟨executes, left, _⟩ := tensor_refines A label separated
  exact ⟨executes, Executable.final_consistent A label executes, Observes.of_refines left observed⟩

/-- The client's observations are kept as well. -/
theorem observes_tensor_right {C₁ C₂ : Configuration T O} {r₁ r₂ : List (Firing T S O)}
    (separated : Separated A label C₁ r₁ C₂ r₂) {result answer : T}
    (observed : Observes A (follow label C₂ r₂).equations result answer) :
    Observes A (follow label (tensor C₁ C₂) (r₁ ++ r₂)).equations result answer :=
  Observes.of_refines (tensor_refines A label separated).2.2 observed

end Frame

/-! ## Separating cases -/

namespace FrameControls

open Projection

abbrev payload : Pattern := payloadPattern exampleWire
abbrev prog : Pattern := program exampleWire

/-- One label for both sides: the certified program at occurrence `0`, an unrelated copy at `5`. -/
def frameLabel : Nat → Pattern
  | 0 => evaluate prog (.var 0)
  | 5 => evaluate prog (.var 20)
  | _ => .const .anonymous

abbrev certified : List (Firing Pattern (Subst signature) Nat) := [projectionFiringAt 1 2 3 0]
abbrev copy : List (Firing Pattern (Subst signature) Nat) := [projectionFiringAt 21 22 23 5]

theorem certified_runs : Executable action frameLabel (startAt 0) certified :=
  projection_executes frameLabel (x := 1) (y := 2) (r := 3) (o := 0) (res := 0) holPattern payload
    (by decide) (by decide) (by decide) rfl hol_closed (payload_closed _)

theorem certified_observes :
    Observes action (follow frameLabel (startAt 0) certified).equations (.var 0) payload :=
  projection_observes frameLabel (x := 1) (y := 2) (r := 3) (o := 0) (res := 0) holPattern payload
    rfl hol_closed (payload_closed _)

theorem copy_runs : Executable action frameLabel (startAt 5) copy :=
  projection_executes frameLabel (x := 21) (y := 22) (r := 23) (o := 5) (res := 20) holPattern payload
    (by decide) (by decide) (by decide) rfl hol_closed (payload_closed _)

theorem copy_observes :
    Observes action (follow frameLabel (startAt 5) copy).equations (.var 20) payload :=
  projection_observes frameLabel (x := 21) (y := 22) (r := 23) (o := 5) (res := 20) holPattern payload
    rfl hol_closed (payload_closed _)

/-- The certified computation and an unrelated copy are separated. -/
theorem separated : Separated action frameLabel (startAt 0) certified (startAt 5) copy where
  left := certified_runs
  right := copy_runs
  apart := by decide
  leftBlind f member := blindTo_of_plain action frameLabel
    (by simp at member; subst member; rfl) (by simp at member; subst member; rfl)
  rightBlind g member := blindTo_of_plain action frameLabel
    (by simp at member; subst member; rfl) (by simp at member; subst member; rfl)
  joint := consistent_of_unified (fuel := 32) (by decide +kernel)

/-- **Positive control: an unrelated valid client.** The tensor runs, and both certified
observations hold in its final store. -/
theorem unrelated_client :
    Executable action frameLabel (tensor (startAt 0) (startAt 5)) (certified ++ copy) ∧
      action.Consistent (follow frameLabel (tensor (startAt 0) (startAt 5)) (certified ++ copy)).equations ∧
      Observes action (follow frameLabel (tensor (startAt 0) (startAt 5)) (certified ++ copy)).equations
        (.var 0) payload ∧
      Observes action (follow frameLabel (tensor (startAt 0) (startAt 5)) (certified ++ copy)).equations
        (.var 20) payload := by
  obtain ⟨executes, consistent, observed⟩ := observes_tensor action frameLabel separated certified_observes
  exact ⟨executes, consistent, observed, observes_tensor_right action frameLabel separated copy_observes⟩

/-! ### Duplicate answers through the branch collection -/

open AnnotatedRunBranchCollection (collectWorlds collectWorlds_count collectWorlds_eq_complete_iff
  RespectsClasses Closed terminalBranches mem_terminalBranches observeClass observeClass_mk)
open AnnotatedRunUnfolding (Terminal mem_frontier)

/-- **The entailed closed answer** of a set of solutions: the readback of a closed answer that
every solution gives the result variable `0`, when there is a solution. -/
noncomputable def entailedValue (solutions : Subst signature → Prop) :
    Option (Tm Presentation.Tower.Head 0) := by
  classical
  exact if h : ∃ t : Tm Presentation.Tower.Head 0, ∃ answer : Pattern,
      readback holCanonical answer = some t ∧ (∃ σ, solutions σ) ∧
        ∀ σ, solutions σ → σ.applyTerm (.var 0) = σ.applyTerm answer
    then some (Classical.choose h) else none

/-- The observation of a configuration: its entailed closed answer, if any. -/
noncomputable def observeAnswer (C : Configuration Pattern Nat) :
    Multiset (Tm Presentation.Tower.Head 0) :=
  ((entailedValue fun σ => action.Models σ C.equations).toList : Multiset _)

/-- The observation depends only on the solutions: it is an observation of branches. -/
theorem observeAnswer_respects : RespectsClasses action observeAnswer := by
  intro C D same
  have solutions : (fun σ => action.Models σ C.equations) = (fun σ => action.Models σ D.equations) :=
    funext fun σ => propext (same.1 σ)
  simp only [observeAnswer, solutions]

/-- A closed answer that reads back is fixed by every substitution, and the entailed answer is
unique: the certified run's store entails exactly the wire's value. -/
theorem entailed_certified :
    entailedValue (fun σ => action.Models σ (follow frameLabel (startAt 0) certified).equations) =
      some (NativeWireData.encode exampleWire) := by
  classical
  have exists_ : ∃ t : Tm Presentation.Tower.Head 0, ∃ answer : Pattern,
      readback holCanonical answer = some t ∧
        (∃ σ, action.Models σ (follow frameLabel (startAt 0) certified).equations) ∧
        ∀ σ, action.Models σ (follow frameLabel (startAt 0) certified).equations →
          σ.applyTerm (.var 0) = σ.applyTerm answer :=
    ⟨_, payload, payload_readback exampleWire,
      Executable.final_consistent action frameLabel certified_runs,
      fun σ solved => certified_observes σ solved⟩
  unfold entailedValue
  rw [dif_pos exists_]
  obtain ⟨answer, read, ⟨σ, solved⟩, observed⟩ := Classical.choose_spec exists_
  have closedAnswer := readback_applyTerm (m := 0) holCanonical σ
    (Fin.elim0 : Presentation.Sub Presentation.Tower.Head 0 0) (fun i => Fin.elim0 i) answer read
  rw [← observed σ solved, show σ.applyTerm (.var 0) = σ.applyTerm payload from
    certified_observes σ solved, payload_closed, payload_readback] at closedAnswer
  have identity : (Presentation.subst (Fin.elim0 : Presentation.Sub Presentation.Tower.Head 0 0)
      (Classical.choose exists_)) = Classical.choose exists_ := by
    have ids : (Fin.elim0 : Presentation.Sub Presentation.Tower.Head 0 0) = Presentation.ids := by
      funext i
      exact i.elim0
    rw [ids, Presentation.subst_ids]
  rw [identity] at closedAnswer
  exact congrArg some (Option.some.inj closedAnswer).symm

/-- The certified computation, alone, has one branch: its one firing. -/
theorem certified_branches :
    terminalBranches action frameLabel certified 1 (startAt 0) = {Quot.mk _ certified} := by
  ext trace
  rw [mem_terminalBranches, Finset.mem_singleton]
  constructor
  · rintro ⟨word, length, run, covered, terminal, rfl⟩
    match word, length, run, covered, terminal with
    | [], _, _, _, terminal =>
        exact absurd certified_runs.1 (terminal _ List.mem_cons_self)
    | [f], _, _, covered, _ =>
        rw [List.mem_singleton.mp (covered f List.mem_cons_self)]
    | _ :: _ :: _, length, _, _, _ => simp at length
  · rintro rfl
    refine ⟨certified, by decide, certified_runs, fun f member => member, ?_, rfl⟩
    intro f member valid
    rw [List.mem_singleton] at member
    subst member
    exact absurd valid.firing.occurrences (by decide)

/-- The certified computation's frontier at depth one is closed. -/
theorem certified_closed : Closed action frameLabel certified 1 (startAt 0) := by
  intro word member
  obtain ⟨length, run, covered⟩ := (mem_frontier action frameLabel certified 1 (startAt 0) word).mp member
  match word, length, run, covered with
  | [f], _, run, covered =>
      rw [List.mem_singleton.mp (covered f List.mem_cons_self)]
      intro g gMember valid
      rw [List.mem_singleton] at gMember
      subst gMember
      exact absurd valid.firing.occurrences (by decide)

/-- Two worlds, each the certified computation. -/
noncomputable def duplicateCollection :=
  collectWorlds action frameLabel certified 1 [startAt 0, startAt 0] observeAnswer observeAnswer_respects

/-- **Duplicate answers are kept by the branch collection.** Two worlds each certify the wire's
value; the collection is complete, counts that answer twice, and its set of answers has one
element. -/
theorem duplicate_answers_kept :
    duplicateCollection.isComplete = true ∧
      duplicateCollection.found.count (NativeWireData.encode exampleWire) = 2 ∧
      duplicateCollection.found.toFinset.card = 1 := by
  have bag : observeClass action frameLabel (startAt 0) observeAnswer observeAnswer_respects
      (Quot.mk _ certified) = {NativeWireData.encode exampleWire} := by
    rw [observeClass_mk]
    simp [observeAnswer, entailed_certified]
  have branches : ∀ root ∈ [startAt 0, startAt 0],
      Closed action frameLabel certified 1 root := by
    intro root member
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    subst member
    exact certified_closed
  have found : duplicateCollection.found =
      {NativeWireData.encode exampleWire} + {NativeWireData.encode exampleWire} := by
    unfold duplicateCollection
    rw [AnnotatedRunBranchCollection.collectWorlds_found]
    simp [AnnotatedRunBranchCollection.branchBag, certified_branches, bag]
  have complete : duplicateCollection =
      .complete ({NativeWireData.encode exampleWire} + {NativeWireData.encode exampleWire}) := by
    unfold duplicateCollection
    rw [collectWorlds_eq_complete_iff]
    refine ⟨branches, ?_⟩
    simp [AnnotatedRunBranchCollection.branchBag, certified_branches, bag]
  refine ⟨by rw [complete]; rfl, ?_, ?_⟩
  · rw [found]
    simp
  · rw [found]
    simp

/-! ### Incompatible shared equations -/

def otherWire : NativeWireData.Wire := .symbol "y"

theorem payloads_differ : payload ≠ payloadPattern otherWire := by
  intro same
  have second := payload_readback otherWire
  have first := payload_readback exampleWire
  change (readback holCanonical payload : Option (Tm Presentation.Tower.Head 0)) = _ at first
  rw [same, second] at first
  have equal := NativeWireData.encode_injective (Option.some.inj first)
  cases equal

/-- A client telling the shared result variable another wire's data. -/
def tellerFiring : Firing Pattern (Subst signature) Nat :=
  ⟨⟨[], [], [(.var 0, payloadPattern otherWire)], [], []⟩, [], ⟨[], [], []⟩⟩

def emptyConfiguration : Configuration Pattern Nat := ⟨[], ∅⟩

theorem empty_enabled (label : Nat → Pattern) (present : Finset Nat) :
    MeTTaCalculus.OccurrenceCommits.Enabled label present
      ((⟨[], [], []⟩ : Selection Nat).commit (T := Pattern)) :=
  ⟨by simp [Selection.commit], by simp [Selection.commit], by simp [Selection.commit],
    by simp [Selection.commit], fun _ member => (List.not_mem_nil member).elim⟩

/-- Every variable to the other wire's data. -/
def tellerSolution : Subst signature := fun _ => payloadPattern otherWire

theorem teller_runs : Executable action frameLabel emptyConfiguration [tellerFiring] := by
  have solved : action.Models tellerSolution
      (tellerFiring.selection.problem frameLabel tellerFiring.rule emptyConfiguration) := by
    intro equation member
    simp [Selection.problem, Selection.equations, tellerFiring, emptyConfiguration] at member
    subst member
    change tellerSolution.applyTerm (.var 0) = tellerSolution.applyTerm (payloadPattern otherWire)
    rw [payload_closed]
    rfl
  exact ⟨⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, empty_enabled _ _, ⟨_, solved⟩,
    by simp [tellerFiring]⟩, by simp [tellerFiring]⟩, ⟨_, solved⟩⟩

/-- Every solution of a store holding the certified run's equations and the teller's tell
would identify the two payloads. -/
theorem teller_contradicts {σ : Subst signature}
    (certifiedSolved : action.Models σ (follow frameLabel (startAt 0) certified).equations)
    (told : action.Solves σ (.var 0, payloadPattern otherWire)) : False := by
  have observed := certified_observes σ certifiedSolved
  change σ.applyTerm (.var 0) = σ.applyTerm payload at observed
  change σ.applyTerm (.var 0) = σ.applyTerm (payloadPattern otherWire) at told
  rw [payload_closed] at observed told
  exact payloads_differ (observed.symm.trans told)

/-- **Negative control: incompatible shared equations.** Each run runs alone; their tensor does
not, since the joint store has no solution. -/
theorem incompatible_shared_equations :
    Executable action frameLabel (startAt 0) certified ∧
      Executable action frameLabel emptyConfiguration [tellerFiring] ∧
      ¬ Executable action frameLabel (tensor (startAt 0) emptyConfiguration) (certified ++ [tellerFiring]) := by
  refine ⟨certified_runs, teller_runs, fun executes => ?_⟩
  obtain ⟨σ, solved⟩ := (tensor_defined_iff action frameLabel certified_runs teller_runs (by decide)
    (fun f member => blindTo_of_plain action frameLabel
      (by simp at member; subst member; rfl) (by simp at member; subst member; rfl))
    (fun g member => blindTo_of_plain action frameLabel
      (by simp at member; subst member; rfl) (by simp at member; subst member; rfl))).mp executes
  obtain ⟨first, _, certifiedEquations, tellerEquations⟩ :=
    (models_jointStore action frameLabel σ _ _ _ _).mp solved
  have final : action.Models σ (follow frameLabel (startAt 0) certified).equations := by
    rw [follow_equations]
    exact (action.models_append σ _ _).mpr ⟨first, certifiedEquations⟩
  exact teller_contradicts final (tellerEquations _ (by
    simp [tellerFiring, Firing.added, GuardFreeProcessOrders.added, Selection.equations]))

/-! ### A later equation cannot repair an earlier failed guard -/

/-- A guard asking whether the result variable already is the payload. -/
def guardFiring : Firing Pattern (Subst signature) Nat :=
  ⟨⟨[], [], [], [.equal (.var 0) payload], []⟩, [], ⟨[], [], []⟩⟩

/-- Where the store says nothing yet, the guard is refused: the identity solution leaves the
result variable unbound. -/
theorem guard_refused (C : Configuration Pattern Nat) (unbound : C.equations = []) :
    ¬ guardFiring.Valid action frameLabel C := by
  intro valid
  have entailed := valid.firing.checks (.equal (.var 0) payload) List.mem_cons_self
    (Subst.id signature) (by
      intro equation member
      simp [Selection.problem, Selection.equations, guardFiring, unbound] at member)
  change (Subst.id signature).applyTerm (.var 0) = (Subst.id signature).applyTerm payload at entailed
  rw [Subst.applyTerm_id, Subst.applyTerm_id] at entailed
  have readbacks := congrArg (readback (Head := Presentation.Tower.Head) (n := 0) holCanonical) entailed
  rw [readback_internal holCanonical (Nat.le_refl 0), payload_readback exampleWire] at readbacks
  cases readbacks

theorem guard_admitted_after :
    guardFiring.Valid action frameLabel (follow frameLabel (startAt 0) certified) := by
  have consistent := Executable.final_consistent action frameLabel certified_runs
  have problem : ∀ σ, action.Models σ (guardFiring.selection.problem frameLabel guardFiring.rule
      (follow frameLabel (startAt 0) certified)) ↔
      action.Models σ (follow frameLabel (startAt 0) certified).equations := by
    intro σ
    simp [Selection.problem, Selection.equations, guardFiring]
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, empty_enabled _ _, ?_, ?_⟩, by simp [guardFiring]⟩
  · obtain ⟨σ, solved⟩ := consistent
    exact ⟨σ, (problem σ).mpr solved⟩
  · intro check member σ solved
    simp only [guardFiring, List.mem_singleton] at member
    subst member
    exact certified_observes σ ((problem σ).mp solved)

/-- **Negative control: a later equation cannot repair an earlier failed guard.** The guard is
refused at its own cut; the order with the guard first does not run although the certified
equation would come later; after the certified run it is admitted. The separation hypothesis of
the frame law fails for it. -/
theorem later_equation_cannot_repair_guard :
    ¬ guardFiring.Valid action frameLabel emptyConfiguration ∧
      ¬ Executable action frameLabel (startAt 0) ([guardFiring] ++ certified) ∧
      Executable action frameLabel (startAt 0) (certified ++ [guardFiring]) ∧
      Observes action (follow frameLabel (startAt 0) (certified ++ [guardFiring])).equations
        (.var 0) payload ∧
      ¬ Separated action frameLabel (startAt 0) certified emptyConfiguration [guardFiring] := by
  refine ⟨guard_refused _ rfl, fun executes => guard_refused (startAt 0) rfl executes.1, ?_, ?_,
    fun separated => guard_refused _ rfl separated.right.1⟩
  · exact executable_append' action frameLabel _ _ _ certified_runs
      ⟨guard_admitted_after, by
        obtain ⟨σ, solved⟩ := guard_admitted_after.firing.consistent
        exact ⟨σ, solved⟩⟩
  · rw [follow_append']
    refine Observes.of_refines (fun σ solved => ?_) certified_observes
    simpa [follow, Firing.result, Selection.result, Selection.problem, Selection.equations,
      guardFiring] using solved

/-! ### A predicate query needs blindness -/

/-- The space of pending computations. -/
def pendingSpace : Subst signature → Pattern → Bool := fun _ t =>
  match t with
  | .app .evaluate _ => true
  | _ => false

/-- A client asking that no computation is pending. -/
def observerFiring : Firing Pattern (Subst signature) Nat :=
  ⟨⟨[], [], [], [], []⟩, [⟨pendingSpace, ∅⟩], ⟨[], [], []⟩⟩

theorem observer_valid_iff (C : Configuration Pattern Nat) (consistent : action.Consistent C.equations) :
    observerFiring.Valid action frameLabel C ↔
      regionOf frameLabel C.present (pendingSpace (Subst.id signature)) = ∅ := by
  have problem : ∀ σ, action.Models σ (observerFiring.selection.problem frameLabel observerFiring.rule C) ↔
      action.Models σ C.equations := by
    intro σ
    simp [Selection.problem, Selection.equations, observerFiring]
  constructor
  · intro valid
    obtain ⟨σ, solved⟩ := consistent
    exact valid.observations _ List.mem_cons_self σ ((problem σ).mpr solved)
  · intro empty
    refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, empty_enabled _ _, ?_,
      by simp [observerFiring]⟩, ?_⟩
    · obtain ⟨σ, solved⟩ := consistent
      exact ⟨σ, (problem σ).mpr solved⟩
    · intro query member σ _
      simp only [observerFiring, List.mem_singleton] at member
      subst member
      exact empty

/-- **Negative control: blindness, not order.** The observer runs alone and is not blind to the
certified space. Before the certified run, beside its pending occurrence, it is refused; after
the certified run it runs. The frame law asks for blindness, which makes the order of the two
sides irrelevant. -/
theorem query_space_needed :
    Executable action frameLabel emptyConfiguration [observerFiring] ∧
      ¬ BlindTo action frameLabel (space (startAt 0) certified) observerFiring ∧
      ¬ Executable action frameLabel (startAt 0) ([observerFiring] ++ certified) ∧
      Executable action frameLabel (startAt 0) (certified ++ [observerFiring]) := by
  have emptyConsistent : action.Consistent emptyConfiguration.equations :=
    ⟨Subst.id signature, fun _ member => (List.not_mem_nil member).elim⟩
  refine ⟨⟨(observer_valid_iff _ emptyConsistent).mpr (by decide), ?_⟩, fun blind => ?_,
    fun executes => ?_, ?_⟩
  · obtain ⟨σ, solved⟩ := emptyConsistent
    refine ⟨σ, ?_⟩
    simpa [Firing.result, Selection.result, Selection.problem, Selection.equations,
      observerFiring] using solved
  · have sees := blind.queries _ List.mem_cons_self (Subst.id signature) 0 (by decide)
    exact absurd sees (by decide)
  · have refused := (observer_valid_iff (startAt 0) ⟨Subst.id signature,
      fun _ member => (List.not_mem_nil member).elim⟩).mp executes.1
    exact absurd refused (by decide)
  · refine executable_append' action frameLabel _ _ _ certified_runs ⟨?_, ?_⟩
    · exact (observer_valid_iff _ (Executable.final_consistent action frameLabel certified_runs)).mpr
        (by decide)
    · obtain ⟨σ, solved⟩ := Executable.final_consistent action frameLabel certified_runs
      refine ⟨σ, ?_⟩
      simpa [Firing.result, Selection.result, Selection.problem, Selection.equations,
        observerFiring] using solved

/-! ### A dormant row that is stored -/

/-- The certified program at `0`, an unrelated copy at `5`, and at `9` a stored row whose
pending computation would tell the shared result variable another wire's data. -/
def rowLabel : Nat → Pattern
  | 0 => evaluate (program exampleWire) (.var 0)
  | 5 => evaluate (program exampleWire) (.var 20)
  | 9 => evaluate (program otherWire) (.var 0)
  | _ => .const .anonymous

/-- The client's configuration holds the copy and the dormant row. -/
def clientWithRow : Configuration Pattern Nat := ⟨[], {5, 9}⟩

/-- The row's firing, were it fired. -/
abbrev rowFiring : Firing Pattern (Subst signature) Nat := projectionFiringAt 31 32 33 9

theorem certified_runs_with_row : Executable action rowLabel (startAt 0) certified :=
  projection_executes rowLabel (x := 1) (y := 2) (r := 3) (o := 0) (res := 0) holPattern payload
    (by decide) (by decide) (by decide) rfl hol_closed (payload_closed _)

theorem certified_observes_with_row :
    Observes action (follow rowLabel (startAt 0) certified).equations (.var 0) payload :=
  projection_observes rowLabel (x := 1) (y := 2) (r := 3) (o := 0) (res := 0) holPattern payload
    rfl hol_closed (payload_closed _)

theorem copy_valid_with_row : (projectionFiringAt 21 22 23 5).Valid action rowLabel clientWithRow :=
  ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    consistent_of_unified (fuel := 32) (by decide +kernel),
    by simp [projectionFiringAt, projectionInstance]⟩,
    by simp [projectionFiringAt]⟩

theorem copy_runs_with_row : Executable action rowLabel clientWithRow copy :=
  ⟨copy_valid_with_row, consistent_of_unified (fuel := 32) (by decide +kernel)⟩

theorem separated_with_row :
    Separated action rowLabel (startAt 0) certified clientWithRow copy where
  left := certified_runs_with_row
  right := copy_runs_with_row
  apart := by decide
  leftBlind f member := blindTo_of_plain action rowLabel
    (by simp at member; subst member; rfl) (by simp at member; subst member; rfl)
  rightBlind g member := blindTo_of_plain action rowLabel
    (by simp at member; subst member; rfl) (by simp at member; subst member; rfl)
  joint := consistent_of_unified (fuel := 32) (by decide +kernel)

abbrev finalWithRow : Configuration Pattern Nat :=
  follow rowLabel (tensor (startAt 0) clientWithRow) (certified ++ copy)

/-- **Control: the row is stored throughout, unfired, and the valid work runs beside it with its
observation.** -/
theorem dormant_row_present :
    9 ∈ (tensor (startAt 0) clientWithRow).present ∧ 9 ∈ finalWithRow.present ∧
      Executable action rowLabel (tensor (startAt 0) clientWithRow) (certified ++ copy) ∧
      Observes action finalWithRow.equations (.var 0) payload := by
  obtain ⟨executes, _, observed⟩ :=
    observes_tensor action rowLabel separated_with_row certified_observes_with_row
  exact ⟨by decide, by decide +kernel, executes, observed⟩

/-- **Negative control: conjoining the stored row's condition with the valid work leaves no
solution.** -/
theorem row_poisons :
    ¬ action.Consistent (finalWithRow.equations ++ rowFiring.added rowLabel) := by
  rintro ⟨σ, solved⟩
  obtain ⟨final, added⟩ := (action.models_append σ _ _).mp solved
  have resultIsPayload := dormant_row_present.2.2.2 σ final
  have first := added (evaluate (secondP (pairP (.var 31) (.var 32))) (.var 33), rowLabel 9) (by
    simp [rowFiring, Firing.added, GuardFreeProcessOrders.added, Selection.equations,
      projectionFiringAt, projectionInstance])
  have second := added (.var 33, .var 32) (by
    simp [rowFiring, Firing.added, GuardFreeProcessOrders.added, Selection.equations,
      projectionFiringAt, projectionInstance])
  change σ.applyTerm (evaluate (secondP (pairP (.var 31) (.var 32))) (.var 33)) =
    σ.applyTerm (evaluate (program otherWire) (.var 0)) at first
  change σ.applyTerm (.var 33) = σ.applyTerm (.var 32) at second
  change σ.applyTerm (.var 0) = σ.applyTerm payload at resultIsPayload
  simp only [program, applyTerm_evaluate, applyTerm_secondP, applyTerm_pairP, hol_closed,
    payload_closed] at first
  obtain ⟨inner, results⟩ := evaluate_injective first
  obtain ⟨_, payloads⟩ := pairP_injective (secondP_injective inner)
  rw [payload_closed] at resultIsPayload
  exact payloads_differ (resultIsPayload.symm.trans (results.symm.trans (second.trans payloads)))

/-- **Negative control: firing the stored row at the final cut is refused.** -/
theorem row_refused : ¬ rowFiring.Valid action rowLabel finalWithRow := by
  intro valid
  obtain ⟨σ, solved⟩ := valid.firing.consistent
  exact row_poisons ⟨σ, by simpa [Firing.problem_eq'] using solved⟩

#print axioms tensor_refines
#print axioms observes_tensor
#print axioms observes_tensor_right
#print axioms FrameControls.separated
#print axioms FrameControls.unrelated_client
#print axioms FrameControls.observeAnswer_respects
#print axioms FrameControls.entailed_certified
#print axioms FrameControls.certified_branches
#print axioms FrameControls.certified_closed
#print axioms FrameControls.duplicate_answers_kept
#print axioms FrameControls.incompatible_shared_equations
#print axioms FrameControls.later_equation_cannot_repair_guard
#print axioms FrameControls.query_space_needed
#print axioms FrameControls.dormant_row_present
#print axioms FrameControls.row_poisons
#print axioms FrameControls.row_refused

end FrameControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed
