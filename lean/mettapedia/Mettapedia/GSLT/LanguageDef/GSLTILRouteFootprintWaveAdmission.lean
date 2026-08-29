import Mettapedia.GSLT.Core.ResourceAwareControl
import Mettapedia.GSLT.LanguageDef.GSLTILContextualDeltaRouteBridge
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions

/-!
# Footprint-derived wave admission for retained GSLT-IL routes

Contextual route deltas say what a retained alternative would change.  A
parallel implementation needs an additional, operational statement: which
locations the route reads and writes, and why its state transformer is framed
by those locations.

This module supplies that boundary.  Read/write footprints fold over the exact
occurrence route and preserve append.  A candidate certificate proves that
the delta-derived state transformer satisfies the existing relational frame
rule.  Two retained candidates with independent effects then form a diamond,
which yields observer-relative serializability and the serializability field
of the generic certified-wave interface.

Footprints provide no resource account.  The final construction accepts an
independent `BatchSeparation` witness; without it, no certified batch is
constructed.  Likewise, this module licenses parallel evaluation of isolated
route deltas but grants neither state-commit nor external-intent authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.RouteFootprintWaveAdmission

open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers
open Mettapedia.GSLT.LanguageDef.GSLTIL.ContextualDeltaRouteBridge
open Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction

universe u

/-! ## Compositional route footprints -/

/-- Read and write locations attributed to one physical occurrence. -/
structure RouteFootprintDisplay (Occurrence Location : Type u) where
  readsAt : Occurrence → Finset Location
  writesAt : Occurrence → Finset Location

def historyReads
    {Occurrence Location : Type u} [DecidableEq Location]
    (display : RouteFootprintDisplay Occurrence Location) :
    List Occurrence → Finset Location
  | [] => ∅
  | occurrence :: rest => display.readsAt occurrence ∪ historyReads display rest

def historyWrites
    {Occurrence Location : Type u} [DecidableEq Location]
    (display : RouteFootprintDisplay Occurrence Location) :
    List Occurrence → Finset Location
  | [] => ∅
  | occurrence :: rest => display.writesAt occurrence ∪ historyWrites display rest

@[simp] theorem historyReads_append
    {Occurrence Location : Type u} [DecidableEq Location]
    (display : RouteFootprintDisplay Occurrence Location)
    (earlier later : List Occurrence) :
    historyReads display (earlier ++ later) =
      historyReads display earlier ∪ historyReads display later := by
  induction earlier with
  | nil => simp [historyReads]
  | cons occurrence rest inductionHypothesis =>
      simp only [List.cons_append, historyReads, inductionHypothesis]
      exact (Finset.union_assoc (display.readsAt occurrence)
        (historyReads display rest) (historyReads display later)).symm

@[simp] theorem historyWrites_append
    {Occurrence Location : Type u} [DecidableEq Location]
    (display : RouteFootprintDisplay Occurrence Location)
    (earlier later : List Occurrence) :
    historyWrites display (earlier ++ later) =
      historyWrites display earlier ∪ historyWrites display later := by
  induction earlier with
  | nil => simp [historyWrites]
  | cons occurrence rest inductionHypothesis =>
      simp only [List.cons_append, historyWrites, inductionHypothesis]
      exact (Finset.union_assoc (display.writesAt occurrence)
        (historyWrites display rest) (historyWrites display later)).symm

def routeReads
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence Location : Type u} [DecidableEq Location]
    {source : theory.World}
    (display : RouteFootprintDisplay Occurrence Location)
    (route : PathRetainingFiniteRoute theory Occurrence source) :
    Finset Location :=
  historyReads display route.occurrences

def routeWrites
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence Location : Type u} [DecidableEq Location]
    {source : theory.World}
    (display : RouteFootprintDisplay Occurrence Location)
    (route : PathRetainingFiniteRoute theory Occurrence source) :
    Finset Location :=
  historyWrites display route.occurrences

@[simp] theorem routeReads_append
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence Location : Type u} [DecidableEq Location]
    {source : theory.World}
    (display : RouteFootprintDisplay Occurrence Location)
    (earlier : PathRetainingFiniteRoute theory Occurrence source)
    (later : PathRetainingFiniteRoute theory Occurrence earlier.target) :
    routeReads display (earlier.append later) =
      routeReads display earlier ∪ routeReads display later :=
  historyReads_append display earlier.occurrences later.occurrences

@[simp] theorem routeWrites_append
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence Location : Type u} [DecidableEq Location]
    {source : theory.World}
    (display : RouteFootprintDisplay Occurrence Location)
    (earlier : PathRetainingFiniteRoute theory Occurrence source)
    (later : PathRetainingFiniteRoute theory Occurrence earlier.target) :
    routeWrites display (earlier.append later) =
      routeWrites display earlier ∪ routeWrites display later :=
  historyWrites_append display earlier.occurrences later.occurrences

/-! ## Delta-derived relational effect certificates -/

def candidateStep
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence Location Atom Delta Answer Intent : Type u}
    {source : theory.World}
    (algebra : DeltaAlgebra (Network Location Atom) Delta)
    (effects : RouteEffectDisplay Occurrence Delta Intent)
    (state : Network Location Atom)
    (candidate : RouteCandidate theory Occurrence Answer source) :
    Network Location Atom :=
  candidate.state algebra effects state

/-- The operational relation is definitionally the graph of the route's
delta-derived state transformer; a footprint proof cannot validate another
hidden implementation. -/
def CandidateRelation
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence Location Atom Delta Answer Intent : Type u}
    {source : theory.World}
    (algebra : DeltaAlgebra (Network Location Atom) Delta)
    (effects : RouteEffectDisplay Occurrence Delta Intent)
    (candidate : RouteCandidate theory Occurrence Answer source) :
    Network Location Atom → Network Location Atom → Prop :=
  fun state target => target = candidateStep algebra effects state candidate

/-- A checked route transformer obeys the existing read/write frame rule at
the footprints computed from its exact occurrences. -/
structure CandidateFootprintCertificate
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence Location Atom Delta Answer Intent : Type u}
    [DecidableEq Location] {source : theory.World}
    (algebra : DeltaAlgebra (Network Location Atom) Delta)
    (effects : RouteEffectDisplay Occurrence Delta Intent)
    (footprints : RouteFootprintDisplay Occurrence Location)
    (candidate : RouteCandidate theory Occurrence Answer source) : Prop where
  sound : EffectFootprinted (CandidateRelation algebra effects candidate)
    (routeReads footprints candidate.route)
    (routeWrites footprints candidate.route)

/-! ## Independent retained pairs -/

/-- Two members of one isolated family whose exact delta transformers have
checked, independent read/write effects. -/
structure IndependentPair
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence Location Atom Delta Answer Intent : Type u}
    [DecidableEq Location] {source : theory.World}
    (algebra : DeltaAlgebra (Network Location Atom) Delta)
    (effects : RouteEffectDisplay Occurrence Delta Intent)
    (footprints : RouteFootprintDisplay Occurrence Location)
    (family : RouteFamily theory Occurrence (Network Location Atom) Answer source) where
  first : RouteCandidate theory Occurrence Answer source
  second : RouteCandidate theory Occurrence Answer source
  firstMember : first ∈ family.candidates
  secondMember : second ∈ family.candidates
  firstCertified : CandidateFootprintCertificate algebra effects footprints first
  secondCertified : CandidateFootprintCertificate algebra effects footprints second
  independent : IndependentEffects
    (routeReads footprints first.route) (routeWrites footprints first.route)
    (routeReads footprints second.route) (routeWrites footprints second.route)

namespace IndependentPair

variable
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence Location Atom Delta Answer Intent : Type u}
    [DecidableEq Location] {source : theory.World}
    {algebra : DeltaAlgebra (Network Location Atom) Delta}
    {effects : RouteEffectDisplay Occurrence Delta Intent}
    {footprints : RouteFootprintDisplay Occurrence Location}
    {family : RouteFamily theory Occurrence (Network Location Atom) Answer source}

def batch (pair : IndependentPair algebra effects footprints family) :
    List (RouteCandidate theory Occurrence Answer source) :=
  [pair.first, pair.second]

def referenceTarget (pair : IndependentPair algebra effects footprints family) :
    Network Location Atom :=
  activateAll (candidateStep algebra effects) family.parent pair.batch

/-- The checked frame theorem makes the two route-derived state transformers
commute on their shared parent. -/
theorem commute (pair : IndependentPair algebra effects footprints family) :
    candidateStep algebra effects
        (candidateStep algebra effects family.parent pair.first) pair.second =
      candidateStep algebra effects
        (candidateStep algebra effects family.parent pair.second) pair.first := by
  obtain ⟨joined, secondAfterFirst, firstAfterSecond⟩ :=
    EffectFootprinted.independent_commute
      pair.firstCertified.sound pair.secondCertified.sound pair.independent
      (source := family.parent)
      (afterFirst := candidateStep algebra effects family.parent pair.first)
      (afterSecond := candidateStep algebra effects family.parent pair.second)
      rfl rfl
  exact secondAfterFirst.symm.trans firstAfterSecond

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
  | nil => simp at permutation
  | cons left tail =>
      cases tail with
      | nil => simp at permutation
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

/-- Deterministic execution of contextual route deltas, with an authored
final-state observer. -/
def executionSemantics
    {StateView : Type u}
    (observe : Network Location Atom → StateView) :
    ExecutionSemantics (RouteCandidate theory Occurrence Answer source)
      (Network Location Atom) StateView where
  run := fun initial candidates target =>
    target = activateAll (candidateStep algebra effects) initial candidates
  observe := observe

/-- Footprint independence proves serializability at every final-state
observer.  Chronology-sensitive observers are outside this final-state
interface and therefore receive no license from this theorem. -/
theorem serializesTo
    {StateView : Type u}
    (pair : IndependentPair algebra effects footprints family)
    (observe : Network Location Atom → StateView) :
    (executionSemantics (algebra := algebra) (effects := effects) observe).SerializesTo
      family.parent pair.batch pair.referenceTarget := by
  constructor
  · rfl
  · intro ordering permutation
    refine ⟨activateAll (candidateStep algebra effects) family.parent ordering,
      rfl, ?_⟩
    rcases perm_pair_eq_or_swap ordering pair.first pair.second permutation with
      rfl | rfl
    · rfl
    · exact congrArg observe pair.commute.symm

/-- Once an independent resource decomposition and a permutation-invariant
candidate observation are supplied, footprint serializability fills the
operational field of the generic certified-batch interface. -/
def toCertified
    {Guard CandidateView StateView Account : Type u} [AddMonoid Account]
    (pair : IndependentPair algebra effects footprints family)
    (contract : Contract (RouteCandidate theory Occurrence Answer source)
      Guard CandidateView)
    (observeState : Network Location Atom → StateView)
    (candidateInvariant :
      PermutationInvariantAt contract.observer.observe pair.batch)
    (demand : RouteCandidate theory Occurrence Answer source → Account)
    (accountSource : Account)
    (resources : BatchSeparation Account demand accountSource pair.batch) :
    CertifiedBatch contract
      (executionSemantics (algebra := algebra) (effects := effects) observeState)
      family.parent pair.referenceTarget Account demand accountSource pair.batch where
  nonempty := by simp [batch]
  candidateInvariant := candidateInvariant
  executionSerializable := pair.serializesTo observeState
  resources := resources

end IndependentPair

/-! ## A reusable additive-network certificate -/

/-- A network-valued delta is supported by a finite write footprint when it
is empty at every other location. -/
def SupportedBy
    {Location Atom : Type u} [DecidableEq Location]
    (delta : Network Location Atom) (writes : Finset Location) : Prop :=
  ∀ location, location ∉ writes → delta location = 0

/-- Adding a finitely supported network delta has no reads and satisfies the
read/write frame rule at its support. -/
theorem additiveNetwork_effectFootprinted
    {Location Atom : Type u} [DecidableEq Location]
    (delta : Network Location Atom) (writes : Finset Location)
    (supported : SupportedBy delta writes) :
    EffectFootprinted
      (fun source target : Network Location Atom => target = source + delta)
      ∅ writes := by
  constructor
  · intro source target step location outside
    rw [step]
    simp [supported location outside]
  · intro source target step framedSource agrees
    refine ⟨framedSource + delta, rfl, ?_, ?_⟩
    · intro location inside
      rw [step]
      have same := agrees location (by simp [inside])
      change source location + delta location =
        framedSource location + delta location
      rw [same]
    · intro location outside
      change framedSource location + delta location = framedSource location
      rw [supported location outside]
      exact add_zero _

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge.Canary

abbrev TestState := Network Bool Unit

def networkAlgebra : DeltaAlgebra TestState TestState where
  empty := 0
  compose := (· + ·)
  apply := (· + ·)
  compose_assoc := add_assoc
  empty_compose := zero_add
  compose_empty := add_zero
  apply_empty := add_zero
  apply_compose := fun state first second => (add_assoc state first second).symm

def locationOf (occurrence : Nat) : Bool := occurrence != 0

def networkDelta (occurrence : Nat) : TestState :=
  singletonNetwork (locationOf occurrence) ()

def effects : RouteEffectDisplay Nat TestState Bool where
  deltaAt := networkDelta
  intentsAt occurrence := [occurrence = 1]

def footprints : RouteFootprintDisplay Nat Bool where
  readsAt _ := ∅
  writesAt occurrence := {locationOf occurrence}

def leftCandidate : RouteCandidate collisionTheory Nat Bool () where
  branch := [false]
  answer := false
  route := falseRoute

def rightCandidate : RouteCandidate collisionTheory Nat Bool () where
  branch := [true]
  answer := true
  route := trueRoute

def family : RouteFamily collisionTheory Nat TestState Bool () where
  parent := 0
  candidates := [leftCandidate, rightCandidate]

theorem leftDelta_supported :
    SupportedBy (leftCandidate.delta networkAlgebra effects)
      (routeWrites footprints leftCandidate.route) := by
  intro location outside
  cases location <;>
    simp [leftCandidate, falseRoute, PathRetainingFiniteRoute.single,
      RouteCandidate.delta, routeDelta, historyDelta, networkAlgebra, effects,
      networkDelta, locationOf, singletonNetwork, routeWrites, historyWrites,
      footprints] at outside ⊢

theorem rightDelta_supported :
    SupportedBy (rightCandidate.delta networkAlgebra effects)
      (routeWrites footprints rightCandidate.route) := by
  intro location outside
  cases location <;>
    simp [rightCandidate, trueRoute, PathRetainingFiniteRoute.single,
      RouteCandidate.delta, routeDelta, historyDelta, networkAlgebra, effects,
      networkDelta, locationOf, singletonNetwork, routeWrites, historyWrites,
      footprints] at outside ⊢

def leftCertificate : CandidateFootprintCertificate
    networkAlgebra effects footprints leftCandidate where
  sound := by
    change EffectFootprinted
      (fun source target : TestState =>
        target = source + leftCandidate.delta networkAlgebra effects)
      ∅ (routeWrites footprints leftCandidate.route)
    exact additiveNetwork_effectFootprinted
      (leftCandidate.delta networkAlgebra effects)
      (routeWrites footprints leftCandidate.route)
      leftDelta_supported

def rightCertificate : CandidateFootprintCertificate
    networkAlgebra effects footprints rightCandidate where
  sound := by
    change EffectFootprinted
      (fun source target : TestState =>
        target = source + rightCandidate.delta networkAlgebra effects)
      ∅ (routeWrites footprints rightCandidate.route)
    exact additiveNetwork_effectFootprinted
      (rightCandidate.delta networkAlgebra effects)
      (routeWrites footprints rightCandidate.route)
      rightDelta_supported

def independentPair : IndependentPair networkAlgebra effects footprints family where
  first := leftCandidate
  second := rightCandidate
  firstMember := by simp [family]
  secondMember := by simp [family]
  firstCertified := leftCertificate
  secondCertified := rightCertificate
  independent := by
    simp [IndependentEffects, routeReads, routeWrites, historyReads,
      historyWrites, footprints, leftCandidate, rightCandidate, falseRoute,
      trueRoute, PathRetainingFiniteRoute.single, locationOf]

def completeContract : Contract
    (RouteCandidate collisionTheory Nat Bool ()) Unit
    (Multiset (List Bool)) where
  observer :=
    { observe := fun candidates => (candidates.map (·.branch) : Multiset _) }
  demand := { completion := .completeBag }

def unitDemand (_ : RouteCandidate collisionTheory Nat Bool ()) : Nat := 1

def resources : BatchSeparation Nat unitDemand 2 independentPair.batch where
  frame := 0
  source_eq := by decide

def certified : CertifiedBatch completeContract
    (IndependentPair.executionSemantics
      (algebra := networkAlgebra) (effects := effects) id)
    family.parent independentPair.referenceTarget Nat unitDemand 2
    independentPair.batch :=
  independentPair.toCertified completeContract id (by
    intro ordering permutation
    exact Quot.sound (permutation.map fun candidate => candidate.branch))
    unitDemand 2 resources

/-- Positive control: exact route occurrence identity determines two disjoint
write footprints, which—together with a separate account decomposition—earns
bulk activation under complete-bag demand. -/
theorem disjoint_retained_routes_earn_bulk :
    (certified.plan .general).activation = .bulk ∧
      (independentPair.referenceTarget false).card = 1 ∧
      (independentPair.referenceTarget true).card = 1 := by
  constructor
  · exact certified.completeBag_dispatches_bulk rfl
  · decide

/-- Negative control: reusing one route's nonempty write footprint for both
positions fails the independence premise. Footprint soundness alone therefore
does not mint a parallel-wave certificate. -/
theorem same_route_write_is_not_independent :
    ¬ IndependentEffects
      (routeReads footprints leftCandidate.route)
      (routeWrites footprints leftCandidate.route)
      (routeReads footprints leftCandidate.route)
      (routeWrites footprints leftCandidate.route) := by
  simp [IndependentEffects, routeReads, routeWrites, historyReads,
    historyWrites, footprints, leftCandidate, falseRoute,
    PathRetainingFiniteRoute.single, locationOf]

end Canary

#print axioms historyReads_append
#print axioms historyWrites_append
#print axioms routeReads_append
#print axioms routeWrites_append
#print axioms IndependentPair.commute
#print axioms IndependentPair.serializesTo
#print axioms additiveNetwork_effectFootprinted
#print axioms Canary.disjoint_retained_routes_earn_bulk
#print axioms Canary.same_route_write_is_not_independent

end Mettapedia.GSLT.LanguageDef.GSLTIL.RouteFootprintWaveAdmission
