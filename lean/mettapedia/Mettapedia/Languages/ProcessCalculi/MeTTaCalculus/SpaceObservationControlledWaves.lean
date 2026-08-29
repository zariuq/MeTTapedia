import Mettapedia.GSLT.Core.ResourceAwareControl
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions

/-!
# Observation-controlled waves over located MeTTa spaces

This module connects the protocol-neutral located-space semantics to the
generic observation/resource wave boundary.

A located request contributes an exact linear demand only when its mode is
`consume`; a persistent `observe` contributes zero linear demand.  For two
requests at distinct locations, successful steps from one source construct:

* both serial orders to one common target;
* an exact decomposition of the source network into the positional linear
  demands plus the common residual; and
* complete-bag and first-witness control plans over the same evidence.

The negative control uses two same-location consumes.  Their structural work
is still two, but a singleton occurrence store cannot fund their demand.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceObservationControlledWaves

open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceChannelBoundary
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions

universe uLocation uAtom

variable {Location : Type uLocation} {Atom : Type uAtom}
variable [DecidableEq Location]

/-! ## Exact request traces and accounts -/

/-- A persistent request consumes no linear resource.  A consuming request
demands exactly one located atom occurrence in the pointwise network account. -/
def requestDemand (request : Request Location Atom) : Network Location Atom :=
  match request.mode with
  | .observe => 0
  | .consume => singletonNetwork request.location request.atom

/-- Finite chronological execution of located requests. -/
inductive RequestTrace :
    Network Location Atom → List (Request Location Atom) →
      Network Location Atom → Prop where
  | nil (state : Network Location Atom) : RequestTrace state [] state
  | cons {source middle target : Network Location Atom}
      {request : Request Location Atom} {rest : List (Request Location Atom)}
      (head : request.Steps source middle)
      (tail : RequestTrace middle rest target) :
      RequestTrace source (request :: rest) target

/-- Exact final-network observation of request traces. -/
def executionSemantics :
    ExecutionSemantics (Request Location Atom) (Network Location Atom)
      (Network Location Atom) where
  run := RequestTrace
  observe := id

/-- Candidate occurrences are observed as an unordered bag. -/
def completeBagContract :
    Contract (Request Location Atom) Unit (Multiset (Request Location Atom)) where
  observer := { observe := fun requests => (requests : Multiset _) }
  demand := { completion := .completeBag }

/-- The same candidate observation with first-witness demand. -/
def firstContract :
    Contract (Request Location Atom) Unit (Multiset (Request Location Atom)) where
  observer := { observe := fun requests => (requests : Multiset _) }
  demand := { completion := .first }

/-- One successful request exposes its exact additive source equation. -/
theorem step_source_eq_demand_add_target
    (request : Request Location Atom) {source target : Network Location Atom}
    (step : request.Steps source target) :
    source = requestDemand request + target := by
  rcases request with ⟨mode, location, atom⟩
  cases step with
  | observe present =>
      simp [requestDemand]
  | consume rest atLocation =>
      funext other
      by_cases same : other = location
      · subst other
        simp [requestDemand, singletonNetwork, atLocation]
      · simp [requestDemand, singletonNetwork, same]

/-! ## Two-request construction -/

/-- A proved two-request diamond together with the exact resource residual. -/
structure PairWave
    (first second : Request Location Atom)
    (source : Network Location Atom) where
  target : Network Location Atom
  forward : RequestTrace source [first, second] target
  reverse : RequestTrace source [second, first] target
  resources : BatchSeparation (Network Location Atom) requestDemand source
    [first, second]

/-- Distinct-location request steps construct the whole pair wave. -/
noncomputable def PairWave.ofIndependent
    (first second : Request Location Atom)
    {source afterFirst afterSecond : Network Location Atom}
    (independent : first.Independent second)
    (firstStep : first.Steps source afterFirst)
    (secondStep : second.Steps source afterSecond) :
    PairWave first second source := by
  let diamond := Request.independent_commute_via_footprints
    independent firstStep secondStep
  let joined := Classical.choose diamond
  have joinedSteps := Classical.choose_spec diamond
  have secondAfterFirst := joinedSteps.1
  have firstAfterSecond := joinedSteps.2
  refine
    { target := joined
      forward := .cons firstStep (.cons secondAfterFirst (.nil joined))
      reverse := .cons secondStep (.cons firstAfterSecond (.nil joined))
      resources :=
        { frame := joined
          source_eq := ?_ } }
  calc
    source = requestDemand first + afterFirst :=
      step_source_eq_demand_add_target first firstStep
    _ = requestDemand first + (requestDemand second + joined) := by
      rw [step_source_eq_demand_add_target second secondAfterFirst]
    _ = batchDemand requestDemand [first, second] + joined := by
      simp [batchDemand, add_assoc]

private theorem perm_two_cases {Item : Type*} (first second left right : Item)
    (permutation : [left, right].Perm [first, second]) :
    (left = first ∧ right = second) ∨
      (left = second ∧ right = first) := by
  classical
  have leftMem : left ∈ [first, second] := permutation.subset (by simp)
  have rightMem : right ∈ [first, second] := permutation.subset (by simp)
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at leftMem rightMem
  by_cases leftFirst : left = first
  · subst left
    by_cases rightSecond : right = second
    · exact Or.inl ⟨rfl, rightSecond⟩
    · have rightFirst := rightMem.resolve_right rightSecond
      subst right
      have counts := permutation.count_eq second
      simp [List.count_cons, List.count_nil] at counts
      exact Or.inl ⟨rfl, counts⟩
  · have leftSecond := leftMem.resolve_left leftFirst
    subst left
    by_cases rightFirst : right = first
    · exact Or.inr ⟨rfl, rightFirst⟩
    · have rightSecond := rightMem.resolve_left rightFirst
      subst right
      have counts := permutation.count_eq first
      simp [List.count_cons, List.count_nil] at counts
      exact Or.inr ⟨rfl, counts⟩

private theorem perm_pair_eq_or_swap {Item : Type*}
    (ordering : List Item) (first second : Item)
    (permutation : ordering.Perm [first, second]) :
    ordering = [first, second] ∨ ordering = [second, first] := by
  cases ordering with
  | nil =>
      simp at permutation
  | cons left tail =>
      cases tail with
      | nil =>
          simp at permutation
      | cons right rest =>
          have restLength : rest.length = 0 := by
            simpa using permutation.length_eq
          have restEmpty : rest = [] := List.length_eq_zero_iff.mp restLength
          subst rest
          rcases perm_two_cases first second left right permutation with
            same | swapped
          · rcases same with ⟨rfl, rfl⟩
            exact Or.inl rfl
          · rcases swapped with ⟨rfl, rfl⟩
            exact Or.inr rfl

/-- A pair diamond serializes every permutation of its exact occurrence list
to the same final network. -/
theorem PairWave.serializesToTarget
    {first second : Request Location Atom} {source : Network Location Atom}
    (wave : PairWave first second source) :
    executionSemantics.SerializesTo source [first, second] wave.target := by
  constructor
  · exact wave.forward
  · intro ordering permutation
    rcases perm_pair_eq_or_swap ordering first second permutation with
      rfl | rfl
    · exact ⟨wave.target, wave.forward, rfl⟩
    · exact ⟨wave.target, wave.reverse, rfl⟩

/-- The pair under complete-bag demand inhabits the generic wave license. -/
def PairWave.toCompleteCertified
    {first second : Request Location Atom} {source : Network Location Atom}
    (wave : PairWave first second source) :
    CertifiedBatch completeBagContract executionSemantics source wave.target
      (Network Location Atom) requestDemand source [first, second] where
  nonempty := by simp
  candidateInvariant := by
    intro ordering permutation
    exact Quot.sound permutation
  executionSerializable := wave.serializesToTarget
  resources := wave.resources

/-- Identical execution evidence under first-witness demand does not grant
bulk activation. -/
def PairWave.toFirstCertified
    {first second : Request Location Atom} {source : Network Location Atom}
    (wave : PairWave first second source) :
    CertifiedBatch firstContract executionSemantics source wave.target
      (Network Location Atom) requestDemand source [first, second] where
  nonempty := by simp
  candidateInvariant := by
    intro ordering permutation
    exact Quot.sound permutation
  executionSerializable := wave.serializesToTarget
  resources := wave.resources

/-! ## Positive and negative controls -/

namespace Examples

inductive TestLocation where
  | left
  | right
deriving DecidableEq, Repr

inductive TestAtom where
  | payload
deriving DecidableEq, Repr

def source : Network TestLocation TestAtom
  | .left => {.payload}
  | .right => {.payload}

def leftRequest : Request TestLocation TestAtom :=
  ⟨.consume, .left, .payload⟩
def rightRequest : Request TestLocation TestAtom :=
  ⟨.consume, .right, .payload⟩

def afterLeft : Network TestLocation TestAtom := Function.update source .left 0
def afterRight : Network TestLocation TestAtom := Function.update source .right 0

theorem leftStep : leftRequest.Steps source afterLeft := by
  exact LocatedStep.consume 0 rfl

theorem rightStep : rightRequest.Steps source afterRight := by
  exact LocatedStep.consume 0 rfl

noncomputable def pairWave : PairWave leftRequest rightRequest source :=
  PairWave.ofIndependent leftRequest rightRequest (by
    change TestLocation.left ≠ TestLocation.right
    decide) leftStep rightStep

/-- Distinct fibers construct a legal one-wave complete-bag plan with exact
work two and span one. -/
theorem distinct_fibres_bulk :
    ((PairWave.toCompleteCertified pairWave).plan .general).activation = .bulk ∧
      (PairWave.toCompleteCertified pairWave).unitWorkSpan = ⟨2, 1⟩ := by
  constructor
  · exact (PairWave.toCompleteCertified pairWave).completeBag_dispatches_bulk rfl
  · rfl

/-- The same pair remains controlled for first-witness demand. -/
theorem distinct_fibres_first_is_controlled :
    ((PairWave.toFirstCertified pairWave).plan .general).activation =
      .controlled :=
  (PairWave.toFirstCertified pairWave).first_remains_controlled rfl

def singletonSource : Network TestLocation TestAtom :=
  singletonNetwork .left .payload

def contestedRequest : Request TestLocation TestAtom :=
  ⟨.consume, .left, .payload⟩

/-- Equal structural work does not fund two consumes from one occurrence. -/
theorem singleton_cannot_fund_two_consumes :
    ¬ Nonempty
      (BatchSeparation (Network TestLocation TestAtom) requestDemand singletonSource
        [contestedRequest, contestedRequest]) := by
  rintro ⟨separation⟩
  have atLeft := congrFun separation.source_eq TestLocation.left
  have cardinality := congrArg Multiset.card atLeft
  simp [singletonSource, singletonNetwork, contestedRequest, requestDemand,
    batchDemand] at cardinality

end Examples

/-! ## Axiom audit -/

#print axioms step_source_eq_demand_add_target
#print axioms PairWave.serializesToTarget
#print axioms Examples.distinct_fibres_bulk
#print axioms Examples.distinct_fibres_first_is_controlled
#print axioms Examples.singleton_cannot_fund_two_consumes

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceObservationControlledWaves
