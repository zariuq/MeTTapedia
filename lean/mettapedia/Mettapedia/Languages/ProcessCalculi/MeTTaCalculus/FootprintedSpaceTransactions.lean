import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction

/-!
# Footprint certificates for space transactions

This module isolates the frame rule needed to parallelize interactions over a
located occurrence network.  A footprint certificate says two things:

* a transition leaves every location outside its finite footprint unchanged;
* the same transition can be replayed in any surrounding network that agrees
  on the footprint.

Two certified relations with disjoint footprints form a diamond.  This is a
permission to execute the two transitions as one parallel wave when the
requested observer forgets their chronology; it is not a scheduler and does
not make same-location competition parallel.

The certificate is deliberately relational.  Primitive located requests have
one automatically, while a richer guarded transaction may provide one after
its guard, consume, and emission footprint has been checked.
-/

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction

universe u v w x

variable {Location : Type u} {Atom : Type v}

/-- Two networks agree on every location in a finite footprint. -/
def AgreesOn [DecidableEq Location] (footprint : Finset Location)
    (left right : Network Location Atom) : Prop :=
  ∀ location, location ∈ footprint → left location = right location

/-- A transition preserves every location outside its finite footprint. -/
def PreservesOutside [DecidableEq Location] (footprint : Finset Location)
    (source target : Network Location Atom) : Prop :=
  ∀ location, location ∉ footprint → target location = source location

/-- A relational transition owns exactly the locations named by `footprint`.

`frame` is the load-bearing field: if the surrounding network changes away
from the footprint, the transition can be replayed with the same local result
and the new surroundings preserved. -/
structure Footprinted [DecidableEq Location]
    (relation : Network Location Atom → Network Location Atom → Prop)
    (footprint : Finset Location) : Prop where
  preserves : ∀ {source target}, relation source target →
    PreservesOutside footprint source target
  frame : ∀ {source target}, relation source target →
    ∀ framedSource, AgreesOn footprint source framedSource →
      ∃ framedTarget,
        relation framedSource framedTarget ∧
        AgreesOn footprint target framedTarget ∧
        PreservesOutside footprint framedSource framedTarget

namespace Footprinted

variable [DecidableEq Location]

private theorem agreesOn_of_preserves_disjoint
    {firstFootprint secondFootprint : Finset Location}
    {source target : Network Location Atom}
    (disjoint : Disjoint firstFootprint secondFootprint)
    (preserves : PreservesOutside firstFootprint source target) :
    AgreesOn secondFootprint source target := by
  intro location inSecond
  have notFirst : location ∉ firstFootprint := by
    intro inFirst
    exact (Finset.disjoint_left.mp disjoint) inFirst inSecond
  exact (preserves location notFirst).symm

/-- **Disjoint-frame diamond.** Two footprint-certified transitions starting
from the same network commute whenever their finite footprints are disjoint.
The theorem is exact at the final-network observer; a chronology-sensitive
observer still distinguishes the two paths. -/
theorem disjoint_commute
    {firstRelation secondRelation :
      Network Location Atom → Network Location Atom → Prop}
    {firstFootprint secondFootprint : Finset Location}
    (firstCertified : Footprinted firstRelation firstFootprint)
    (secondCertified : Footprinted secondRelation secondFootprint)
    (disjoint : Disjoint firstFootprint secondFootprint)
    {source afterFirst afterSecond : Network Location Atom}
    (firstStep : firstRelation source afterFirst)
    (secondStep : secondRelation source afterSecond) :
    ∃ joined,
      secondRelation afterFirst joined ∧
      firstRelation afterSecond joined := by
  have firstPreserves := firstCertified.preserves firstStep
  have secondPreserves := secondCertified.preserves secondStep
  have sourceAfterFirstAgree :
      AgreesOn secondFootprint source afterFirst :=
    agreesOn_of_preserves_disjoint disjoint firstPreserves
  have sourceAfterSecondAgree :
      AgreesOn firstFootprint source afterSecond :=
    agreesOn_of_preserves_disjoint disjoint.symm secondPreserves
  obtain ⟨joinedForward, secondAfterFirst, secondLocal, secondFrame⟩ :=
    secondCertified.frame secondStep afterFirst sourceAfterFirstAgree
  obtain ⟨joinedReverse, firstAfterSecond, firstLocal, firstFrame⟩ :=
    firstCertified.frame firstStep afterSecond sourceAfterSecondAgree
  have joinedEqual : joinedForward = joinedReverse := by
    funext location
    by_cases inSecond : location ∈ secondFootprint
    · have notFirst : location ∉ firstFootprint := by
        intro inFirst
        exact (Finset.disjoint_left.mp disjoint) inFirst inSecond
      calc
        joinedForward location = afterSecond location :=
          (secondLocal location inSecond).symm
        _ = joinedReverse location := (firstFrame location notFirst).symm
    · have forwardAt : joinedForward location = afterFirst location :=
        secondFrame location inSecond
      by_cases inFirst : location ∈ firstFootprint
      · calc
          joinedForward location = afterFirst location := forwardAt
          _ = joinedReverse location := firstLocal location inFirst
      · calc
          joinedForward location = afterFirst location := forwardAt
          _ = source location := firstPreserves location inFirst
          _ = afterSecond location :=
            (secondPreserves location inSecond).symm
          _ = joinedReverse location := (firstFrame location inFirst).symm
  refine ⟨joinedForward, secondAfterFirst, ?_⟩
  simpa [joinedEqual] using firstAfterSecond

end Footprinted

/-! ## Separate read and write footprints

One aggregate footprint is intentionally conservative.  The following
refinement permits several transitions to share read-only locations while
still refusing every write/read or write/write race.
-/

/-- A transition may inspect `reads`, may modify `writes`, and is insensitive
to the rest of the network.  The replay premise includes both sets because a
write can depend on the old value it replaces. -/
structure EffectFootprinted [DecidableEq Location]
    (relation : Network Location Atom → Network Location Atom → Prop)
    (reads writes : Finset Location) : Prop where
  preserves : ∀ {source target}, relation source target →
    PreservesOutside writes source target
  frame : ∀ {source target}, relation source target →
    ∀ framedSource, AgreesOn (reads ∪ writes) source framedSource →
      ∃ framedTarget,
        relation framedSource framedTarget ∧
        AgreesOn writes target framedTarget ∧
        PreservesOutside writes framedSource framedTarget

/-- Effect independence permits shared reads but no write/read or write/write
collision in either direction. -/
def IndependentEffects [DecidableEq Location]
    (firstReads firstWrites secondReads secondWrites : Finset Location) : Prop :=
  Disjoint firstWrites (secondReads ∪ secondWrites) ∧
  Disjoint secondWrites (firstReads ∪ firstWrites)

namespace EffectFootprinted

variable [DecidableEq Location]

private theorem agreesOn_of_preserves_disjoint
    {writes dependencies : Finset Location}
    {source target : Network Location Atom}
    (disjoint : Disjoint writes dependencies)
    (preserves : PreservesOutside writes source target) :
    AgreesOn dependencies source target := by
  intro location inDependencies
  have notWritten : location ∉ writes := by
    intro written
    exact (Finset.disjoint_left.mp disjoint) written inDependencies
  exact (preserves location notWritten).symm

/-- **Read/write diamond.** Shared reads are permitted.  Every possible write
must be disjoint from the other transition's complete dependency footprint. -/
theorem independent_commute
    {firstRelation secondRelation :
      Network Location Atom → Network Location Atom → Prop}
    {firstReads firstWrites secondReads secondWrites : Finset Location}
    (firstCertified :
      EffectFootprinted firstRelation firstReads firstWrites)
    (secondCertified :
      EffectFootprinted secondRelation secondReads secondWrites)
    (independent :
      IndependentEffects firstReads firstWrites secondReads secondWrites)
    {source afterFirst afterSecond : Network Location Atom}
    (firstStep : firstRelation source afterFirst)
    (secondStep : secondRelation source afterSecond) :
    ∃ joined,
      secondRelation afterFirst joined ∧
      firstRelation afterSecond joined := by
  have firstPreserves := firstCertified.preserves firstStep
  have secondPreserves := secondCertified.preserves secondStep
  have sourceAfterFirstAgree :
      AgreesOn (secondReads ∪ secondWrites) source afterFirst :=
    agreesOn_of_preserves_disjoint independent.1 firstPreserves
  have sourceAfterSecondAgree :
      AgreesOn (firstReads ∪ firstWrites) source afterSecond :=
    agreesOn_of_preserves_disjoint independent.2 secondPreserves
  obtain ⟨joinedForward, secondAfterFirst, secondLocal, secondFrame⟩ :=
    secondCertified.frame secondStep afterFirst sourceAfterFirstAgree
  obtain ⟨joinedReverse, firstAfterSecond, firstLocal, firstFrame⟩ :=
    firstCertified.frame firstStep afterSecond sourceAfterSecondAgree
  have joinedEqual : joinedForward = joinedReverse := by
    funext location
    by_cases inSecondWrite : location ∈ secondWrites
    · have notFirstWrite : location ∉ firstWrites := by
        intro inFirstWrite
        apply (Finset.disjoint_left.mp independent.1) inFirstWrite
        exact Finset.mem_union_right secondReads inSecondWrite
      calc
        joinedForward location = afterSecond location :=
          (secondLocal location inSecondWrite).symm
        _ = joinedReverse location :=
          (firstFrame location notFirstWrite).symm
    · have forwardAt : joinedForward location = afterFirst location :=
        secondFrame location inSecondWrite
      by_cases inFirstWrite : location ∈ firstWrites
      · calc
          joinedForward location = afterFirst location := forwardAt
          _ = joinedReverse location := firstLocal location inFirstWrite
      · calc
          joinedForward location = afterFirst location := forwardAt
          _ = source location := firstPreserves location inFirstWrite
          _ = afterSecond location :=
            (secondPreserves location inSecondWrite).symm
          _ = joinedReverse location :=
            (firstFrame location inFirstWrite).symm
  refine ⟨joinedForward, secondAfterFirst, ?_⟩
  simpa [joinedEqual] using firstAfterSecond

end EffectFootprinted

/-! ## Primitive located requests discharge the interface -/

namespace Request

variable [DecidableEq Location]

/-- A request always reads its selected location. -/
def readFootprint (request : Request Location Atom) : Finset Location :=
  {request.location}

/-- Persistent observation writes nothing; linear consumption writes its
selected location. -/
def writeFootprint (request : Request Location Atom) : Finset Location :=
  match request.mode with
  | .observe => ∅
  | .consume => {request.location}

/-- A primitive located interaction owns exactly its selected location. -/
theorem locatedStep_footprinted
    (mode : AccessMode) (requestLocation : Location) (requestAtom : Atom) :
    Footprinted
      (LocatedStep mode requestLocation requestAtom)
      {requestLocation} := by
  constructor
  · intro source target step location outside
    have different : location ≠ requestLocation := by
      simpa using outside
    exact LocatedStep.preserves_other_location different step
  · intro source target step framedSource agrees
    cases mode with
    | observe =>
      cases step with
      | observe present =>
        have localEqual : source requestLocation = framedSource requestLocation :=
          agrees requestLocation (by simp)
        have framedPresent : requestAtom ∈ framedSource requestLocation := by
          simpa [← localEqual] using present
        refine ⟨framedSource, LocatedStep.observe framedPresent, ?_, ?_⟩
        · intro location inside
          simpa using agrees location inside
        · intro location outside
          rfl
    | consume =>
      cases step with
      | consume rest atLocation =>
        have localEqual : source requestLocation = framedSource requestLocation :=
          agrees requestLocation (by simp)
        have framedAt :
            framedSource requestLocation = requestAtom ::ₘ rest := by
          simpa [← localEqual] using atLocation
        let framedTarget := Function.update framedSource requestLocation rest
        refine ⟨framedTarget, LocatedStep.consume rest framedAt, ?_, ?_⟩
        · intro location inside
          have equalLocation : location = requestLocation := by
            simpa using inside
          subst equalLocation
          simp [framedTarget]
        · intro location outside
          have different : location ≠ requestLocation := by
            simpa using outside
          simp [framedTarget, different]

/-- A primitive located request owns exactly its selected location. -/
theorem footprinted (request : Request Location Atom) :
    Footprinted request.Steps {request.location} := by
  rcases request with ⟨mode, requestLocation, requestAtom⟩
  exact locatedStep_footprinted mode requestLocation requestAtom

/-- Primitive requests also discharge the more permissive read/write
interface.  In particular, two observations may share one location. -/
theorem effectFootprinted (request : Request Location Atom) :
    EffectFootprinted request.Steps
      (readFootprint request) (writeFootprint request) := by
  rcases request with ⟨mode, requestLocation, requestAtom⟩
  cases mode with
  | observe =>
      constructor
      · intro source target step location outside
        cases step
        rfl
      · intro source target step framedSource agrees
        cases step with
        | observe present =>
          have localEqual : source requestLocation = framedSource requestLocation :=
            agrees requestLocation (by simp [readFootprint, writeFootprint])
          have framedPresent : requestAtom ∈ framedSource requestLocation := by
            simpa [← localEqual] using present
          refine ⟨framedSource, LocatedStep.observe framedPresent, ?_, ?_⟩
          · intro location inside
            simp [writeFootprint] at inside
          · intro location outside
            rfl
  | consume =>
      constructor
      · intro source target step location outside
        have different : location ≠ requestLocation := by
          simpa [writeFootprint] using outside
        exact LocatedStep.preserves_other_location different step
      · intro source target step framedSource agrees
        cases step with
        | consume rest atLocation =>
          have localEqual : source requestLocation = framedSource requestLocation :=
            agrees requestLocation (by simp [readFootprint, writeFootprint])
          have framedAt :
              framedSource requestLocation = requestAtom ::ₘ rest := by
            simpa [← localEqual] using atLocation
          let framedTarget := Function.update framedSource requestLocation rest
          refine ⟨framedTarget, LocatedStep.consume rest framedAt, ?_, ?_⟩
          · intro location inside
            have equalLocation : location = requestLocation := by
              simpa [writeFootprint] using inside
            subst equalLocation
            simp [framedTarget]
          · intro location outside
            have different : location ≠ requestLocation := by
              simpa [writeFootprint] using outside
            simp [framedTarget, different]

/-- The generic footprint theorem recovers the primitive request diamond. -/
theorem independent_commute_via_footprints
    {first second : Request Location Atom}
    {source afterFirst afterSecond : Network Location Atom}
    (independent : first.Independent second)
    (firstStep : first.Steps source afterFirst)
    (secondStep : second.Steps source afterSecond) :
    ∃ joined,
      second.Steps afterFirst joined ∧ first.Steps afterSecond joined := by
  apply Footprinted.disjoint_commute (footprinted first) (footprinted second)
  · simpa [Request.Independent, Finset.disjoint_singleton_left] using independent
  · exact firstStep
  · exact secondStep

/-- Positive control: read/read sharing at one location is effect-independent. -/
theorem observations_share_location
    (location : Location) (firstAtom secondAtom : Atom) :
    IndependentEffects
      (readFootprint (⟨.observe, location, firstAtom⟩ : Request Location Atom))
      (writeFootprint (⟨.observe, location, firstAtom⟩ : Request Location Atom))
      (readFootprint (⟨.observe, location, secondAtom⟩ : Request Location Atom))
      (writeFootprint
        (⟨.observe, location, secondAtom⟩ : Request Location Atom)) := by
  simp [IndependentEffects, readFootprint, writeFootprint]

/-- Negative control: two consumes of one location are not effect-independent,
even though a finer occurrence-indexed model may later separate distinct
resident occurrences. -/
theorem consumes_same_location_not_independent
    (location : Location) (firstAtom secondAtom : Atom) :
    ¬ IndependentEffects
      (readFootprint (⟨.consume, location, firstAtom⟩ : Request Location Atom))
      (writeFootprint (⟨.consume, location, firstAtom⟩ : Request Location Atom))
      (readFootprint (⟨.consume, location, secondAtom⟩ : Request Location Atom))
      (writeFootprint
        (⟨.consume, location, secondAtom⟩ : Request Location Atom)) := by
  simp [IndependentEffects, readFootprint, writeFootprint]

end Request

/-! ## Guarded transactions use the same proof boundary -/

namespace GuardedTransaction

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction.GuardedTransaction

variable [DecidableEq Location]
variable {Pattern : Type w} {Environment : Type x}

/-- A checked finite footprint for one guarded command.  A compiler may
construct this certificate from the locations read, consumed, and emitted by
the command.  The semantic theorem depends only on the certificate, so richer
matchers and continuations do not require another parallelism semantics. -/
structure FootprintCertificate
    (selects : Selection Location Atom Pattern Environment)
    (command : Command Location Atom Pattern Environment) where
  footprint : Finset Location
  sound : Footprinted (Fires selects command) footprint

/-- Guarded commands with disjoint checked footprints form an exact network
diamond.  This is the reusable parallel-wave obligation for authored command
languages. -/
theorem disjoint_commute
    {selects : Selection Location Atom Pattern Environment}
    {first second : Command Location Atom Pattern Environment}
    (firstCertified : FootprintCertificate selects first)
    (secondCertified : FootprintCertificate selects second)
    (disjoint : Disjoint firstCertified.footprint secondCertified.footprint)
    {source afterFirst afterSecond : Network Location Atom}
    (firstStep : Fires selects first source afterFirst)
    (secondStep : Fires selects second source afterSecond) :
    ∃ joined,
      Fires selects second afterFirst joined ∧
      Fires selects first afterSecond joined :=
  Footprinted.disjoint_commute firstCertified.sound secondCertified.sound
    disjoint firstStep secondStep

end GuardedTransaction

/-! ## Negative control -/

/-- A location footprint is not disjoint from itself.  In particular, the
generic wave theorem cannot turn two competing consumes of one occurrence
into independent work. -/
theorem singleton_footprint_not_self_disjoint [DecidableEq Location]
    (location : Location) :
    ¬ Disjoint ({location} : Finset Location) {location} := by
  simp

#print axioms Footprinted.disjoint_commute
#print axioms EffectFootprinted.independent_commute
#print axioms Request.footprinted
#print axioms Request.effectFootprinted
#print axioms Request.independent_commute_via_footprints
#print axioms Request.observations_share_location
#print axioms Request.consumes_same_location_not_independent
#print axioms GuardedTransaction.disjoint_commute
#print axioms singleton_footprint_not_self_disjoint

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
