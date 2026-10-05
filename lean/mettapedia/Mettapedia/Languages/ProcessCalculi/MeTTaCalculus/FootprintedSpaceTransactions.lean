import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
import Mettapedia.GSLT.Logic.SeparationAlgebra
import Mathlib.Data.Fintype.EquivFin

/-!
# Footprint certificates for located transitions

This module isolates the frame rule needed to parallelize interactions over a
located state: a value at every location.  A network of occurrence stores is
the case of a bag at every location; a single bag read by the multiplicity of
each atom is the case of a number at every atom.  A footprint certificate says
two things:

* a transition leaves every location outside its finite footprint unchanged;
* the same transition can be replayed in any surrounding state that agrees on
  the footprint.

Two certified relations with disjoint footprints form a diamond.  The diamond
licenses reordering the two transitions under the observer that sees only the
final state; a chronology-sensitive observer still tells the two orders apart.
It is not a scheduler, does not make same-location competition parallel, and
says nothing about a representation: allocation, indexes, intern tables,
counters and queues owe their own synchronization or ownership argument.

The certificate is deliberately relational.  Primitive located requests have
one automatically, while a richer guarded transaction may provide one after
its guard, consume, and emission footprint has been checked.

## Local rules

A rule instance is *local* (`LocalRule`) when it declares everything it depends
on and everything it changes: the resources it consumes and produces, which
vanish outside its written locations, and a guard — every other condition on
its firing, such as a side condition of matching, a lookup modulo equations, a
freshness or allocation check, or the answer of an external service — that
sees nothing outside its read and written locations.  The values at a location
form a separation algebra, and the instance fires on a state that is its
consumed part beside a separate frame.  Every such instance has a read/write
certificate (`LocalRule.effectFootprinted`), hence a footprint certificate, and
independent instances form a diamond (`LocalRule.commute`).

Positive: removing and adding one atom of a space are local rules, and they are
exactly the located consume step and the addition of a one-atom delta
(`SpaceRules.removeAtom_fires_iff`, `SpaceRules.addAtom_fires_iff`).

Negative: a guard that asks for the *absence* of an atom elsewhere reads that
location.  Without declaring the read there is no certificate
(`SpaceRules.addUnless_needs_its_read`), and with two instances whose written
locations and matches are disjoint the diamond fails
(`SpaceRules.absence_guard_breaks_diamond`).  A test that the whole bag is empty
reads every location, and over an infinite alphabet it has no finite footprint
at all (`emptinessTest_not_effectFootprinted`).

## A bag read by kinds

A bag is determined by the multiplicity of each atom because its former is
associative and commutative.  So a rule that replaces a sub-bag in any
surrounding bag is exactly the restriction to bags of a local rule on
multiplicities, which writes the kinds it consumes or produces
(`bagRule_iff_fires`, `exists_marking_of_fires`); two such rules on disjoint kinds
commute (`bagRule_commute`).  The kind footprint is conservative: two rules
consuming different copies of one atom overlap here although they commute.
Without commutativity the reading fails: a rule replacing a contiguous block of
a sequence is not determined by multiplicities at all
(`listRule_not_read_by_kinds`).
-/

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction

universe u v w x y

variable {Location : Type u} {Atom : Type v} {Value : Type y}

/-- Two networks agree on every location in a finite footprint. -/
def AgreesOn [DecidableEq Location] (footprint : Finset Location)
    (left right : Location → Value) : Prop :=
  ∀ location, location ∈ footprint → left location = right location

/-- A transition preserves every location outside its finite footprint. -/
def PreservesOutside [DecidableEq Location] (footprint : Finset Location)
    (source target : Location → Value) : Prop :=
  ∀ location, location ∉ footprint → target location = source location

/-- A relational transition owns exactly the locations named by `footprint`.

`frame` is the load-bearing field: if the surrounding network changes away
from the footprint, the transition can be replayed with the same local result
and the new surroundings preserved. -/
structure Footprinted [DecidableEq Location]
    (relation : (Location → Value) → (Location → Value) → Prop)
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
    {source target : Location → Value}
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
      (Location → Value) → (Location → Value) → Prop}
    {firstFootprint secondFootprint : Finset Location}
    (firstCertified : Footprinted firstRelation firstFootprint)
    (secondCertified : Footprinted secondRelation secondFootprint)
    (disjoint : Disjoint firstFootprint secondFootprint)
    {source afterFirst afterSecond : Location → Value}
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
    (relation : (Location → Value) → (Location → Value) → Prop)
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
    {source target : Location → Value}
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
      (Location → Value) → (Location → Value) → Prop}
    {firstReads firstWrites secondReads secondWrites : Finset Location}
    (firstCertified :
      EffectFootprinted firstRelation firstReads firstWrites)
    (secondCertified :
      EffectFootprinted secondRelation secondReads secondWrites)
    (independent :
      IndependentEffects firstReads firstWrites secondReads secondWrites)
    {source afterFirst afterSecond : Location → Value}
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

/-- A read/write certificate is a footprint certificate at the union of the
read and written locations. -/
theorem EffectFootprinted.footprinted [DecidableEq Location]
    {relation : (Location → Value) → (Location → Value) → Prop}
    {reads writes : Finset Location}
    (certified : EffectFootprinted relation reads writes) :
    Footprinted relation (reads ∪ writes) := by
  constructor
  · intro source target step location outside
    exact certified.preserves step location (fun written => outside (Finset.mem_union_right _ written))
  · intro source target step framedSource agrees
    obtain ⟨framedTarget, framedStep, writtenAgree, framedPreserves⟩ :=
      certified.frame step framedSource agrees
    refine ⟨framedTarget, framedStep, ?_, ?_⟩
    · intro location inside
      by_cases written : location ∈ writes
      · exact writtenAgree location written
      · calc
          target location = source location := certified.preserves step location written
          _ = framedSource location := agrees location inside
          _ = framedTarget location := (framedPreserves location written).symm
    · intro location outside
      exact framedPreserves location (fun written => outside (Finset.mem_union_right _ written))

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

/-! ## Local rules -/

open Mettapedia.GSLT.SeparationAlgebra

/-- **An instance of a local rule** over located states whose values form a
separation algebra.  It declares everything it depends on and everything it
changes.  The match is the choice of `consumed`; name substitution and every
other computation of the result are already done in `produced`; anything the
firing changes — including an allocator, a counter or an index kept in the
state — is part of `consumed` and `produced`, which vanish outside `writes`.
Every other condition on firing — a side condition of matching, a lookup modulo
equations, a freshness or absence check, the answer of an external service — is
`guard`, which sees nothing outside `reads ∪ writes`.  A condition that cannot
be put in this form (one that reads the whole state, say) makes the rule
non-local, and then it has no instance of this structure. -/
structure LocalRule (Location : Type u) (Value : Type y) [DecidableEq Location]
    [Zero Value] [Add Value] [SepAlgebra Value] where
  /-- The resources the instance removes. -/
  consumed : Location → Value
  /-- The resources the instance adds. -/
  produced : Location → Value
  /-- Every other condition on firing. -/
  guard : (Location → Value) → Prop
  /-- The locations the guard may read besides the written ones. -/
  reads : Finset Location
  /-- The locations the instance may change. -/
  writes : Finset Location
  consumed_outside : ∀ location, location ∉ writes → consumed location = 0
  produced_outside : ∀ location, location ∉ writes → produced location = 0
  guard_local : ∀ {source framed : Location → Value},
    AgreesOn (reads ∪ writes) source framed → guard source → guard framed

namespace LocalRule

variable [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]

/-- The instance fires when its guard holds and the source is its consumed
part beside a separate frame; the target is its produced part beside the same
frame. -/
def Fires (rule : LocalRule Location Value) (source target : Location → Value) : Prop :=
  rule.guard source ∧ ∃ frame : Location → Value,
    rule.consumed ## frame ∧ rule.produced ## frame ∧
      source = rule.consumed + frame ∧ target = rule.produced + frame

/-- **Every instance of a local rule has a read/write certificate.**  The frame
of a replay keeps the old frame on the written locations and takes the new
surroundings everywhere else. -/
theorem effectFootprinted (rule : LocalRule Location Value) :
    EffectFootprinted rule.Fires rule.reads rule.writes := by
  constructor
  · rintro source target ⟨-, frame, -, -, rfl, rfl⟩ location outside
    show rule.produced location + frame location = rule.consumed location + frame location
    rw [rule.produced_outside location outside, rule.consumed_outside location outside]
  · rintro source target ⟨guarded, frame, consumedSeparate, producedSeparate, rfl, rfl⟩
      framedSource agrees
    classical
    let framedFrame : Location → Value := fun location =>
      if location ∈ rule.writes then frame location else framedSource location
    have framedAt : ∀ location, location ∈ rule.writes →
        framedFrame location = frame location :=
      fun location written => if_pos written
    have outsideAt : ∀ location, location ∉ rule.writes →
        framedFrame location = framedSource location :=
      fun location written => if_neg written
    have separateFrom : ∀ part : Location → Value,
        (∀ location, location ∉ rule.writes → part location = 0) → part ## frame →
          part ## framedFrame := by
      intro part vanishes separate
      refine separate_pi_iff.mpr fun location => ?_
      by_cases written : location ∈ rule.writes
      · rw [framedAt location written]; exact separate location
      · rw [vanishes location written]; exact SepAlgebra.zero_separate _
    have decomposition : framedSource = rule.consumed + framedFrame := by
      funext location
      show framedSource location = rule.consumed location + framedFrame location
      by_cases written : location ∈ rule.writes
      · rw [framedAt location written]
        exact (agrees location (Finset.mem_union_right _ written)).symm
      · rw [outsideAt location written, rule.consumed_outside location written,
          SepAlgebra.zero_add]
    refine ⟨rule.produced + framedFrame,
      ⟨rule.guard_local agrees guarded, framedFrame,
        separateFrom _ rule.consumed_outside consumedSeparate,
        separateFrom _ rule.produced_outside producedSeparate, decomposition, rfl⟩, ?_, ?_⟩
    · intro location written
      show rule.produced location + frame location =
        rule.produced location + framedFrame location
      rw [framedAt location written]
    · intro location outside
      show rule.produced location + framedFrame location = framedSource location
      rw [outsideAt location outside, rule.produced_outside location outside,
        SepAlgebra.zero_add]

/-- Hence a footprint certificate at the read and written locations. -/
theorem footprinted (rule : LocalRule Location Value) :
    Footprinted rule.Fires (rule.reads ∪ rule.writes) :=
  rule.effectFootprinted.footprinted

/-- **Independent local instances form a diamond** at the final-state
observer. -/
theorem commute (first second : LocalRule Location Value)
    (independent : IndependentEffects first.reads first.writes second.reads second.writes)
    {source afterFirst afterSecond : Location → Value}
    (firstFires : first.Fires source afterFirst)
    (secondFires : second.Fires source afterSecond) :
    ∃ joined, second.Fires afterFirst joined ∧ first.Fires afterSecond joined :=
  EffectFootprinted.independent_commute first.effectFootprinted second.effectFootprinted
    independent firstFires secondFires

/-- A local rule with no condition beyond its match: it reads nothing besides
the locations it writes. -/
def unguarded (consumed produced : Location → Value) (writes : Finset Location)
    (consumedOutside : ∀ location, location ∉ writes → consumed location = 0)
    (producedOutside : ∀ location, location ∉ writes → produced location = 0) :
    LocalRule Location Value where
  consumed := consumed
  produced := produced
  guard _ := True
  reads := ∅
  writes := writes
  consumed_outside := consumedOutside
  produced_outside := producedOutside
  guard_local _ holds := holds

end LocalRule

/-! ## Space rules -/

namespace SpaceRules

variable [DecidableEq Location]

/-- Remove one occurrence of `atom` from the space at `location`. -/
def removeAtom (location : Location) (atom : Atom) : LocalRule Location (Multiset Atom) :=
  LocalRule.unguarded (Pi.single location {atom}) 0 {location}
    (fun other outside => by
      have different : other ≠ location := by simpa using outside
      simp [different])
    (fun _ _ => rfl)

/-- Add one occurrence of `atom` to the space at `location`. -/
def addAtom (location : Location) (atom : Atom) : LocalRule Location (Multiset Atom) :=
  LocalRule.unguarded 0 (Pi.single location {atom}) {location}
    (fun _ _ => rfl)
    (fun other outside => by
      have different : other ≠ location := by simpa using outside
      simp [different])

/-- **Removing an atom is the located consume step.** -/
theorem removeAtom_fires_iff (location : Location) (atom : Atom)
    (source target : Network Location Atom) :
    (removeAtom location atom).Fires source target ↔
      LocatedStep .consume location atom source target := by
  rw [LocatedStep.consume_iff]
  constructor
  · rintro ⟨-, frame, -, -, rfl, rfl⟩
    refine ⟨frame location, by simp [removeAtom, LocalRule.unguarded], ?_⟩
    funext other
    by_cases same : other = location
    · subst same; simp [removeAtom, LocalRule.unguarded]
    · simp [removeAtom, LocalRule.unguarded, same]
  · rintro ⟨rest, atLocation, rfl⟩
    refine ⟨trivial, Function.update source location rest, fun _ => trivial,
      fun _ => trivial, ?_, ?_⟩
    · funext other
      by_cases same : other = location
      · subst same
        simp [removeAtom, LocalRule.unguarded, atLocation, Multiset.singleton_add]
      · simp [removeAtom, LocalRule.unguarded, same]
    · funext other
      simp [removeAtom, LocalRule.unguarded]

/-- **Adding an atom is the addition of a one-atom delta.** -/
theorem addAtom_fires_iff (location : Location) (atom : Atom)
    (source target : Network Location Atom) :
    (addAtom location atom).Fires source target ↔
      target = source + Pi.single location {atom} := by
  constructor
  · rintro ⟨-, frame, -, -, rfl, rfl⟩
    simp [addAtom, LocalRule.unguarded, add_comm]
  · rintro rfl
    exact ⟨trivial, source, fun _ => trivial, fun _ => trivial,
      by simp [addAtom, LocalRule.unguarded], by simp [addAtom, LocalRule.unguarded, add_comm]⟩

/-- Positive control: adding at one space and removing at another are
independent, so they commute. -/
theorem addAtom_removeAtom_independent {location location' : Location}
    (different : location ≠ location') (atom atom' : Atom) :
    IndependentEffects (addAtom location atom).reads (addAtom location atom).writes
      (removeAtom location' atom').reads (removeAtom location' atom').writes := by
  simp [IndependentEffects, addAtom, removeAtom, LocalRule.unguarded, different,
    Ne.symm different]

/-- Add `atom` at `location` unless `absent` occurs at `watched`.  The guard
reads `watched`, and declares it. -/
def addUnless (location watched : Location) (atom absent : Atom) :
    LocalRule Location (Multiset Atom) where
  consumed := 0
  produced := Pi.single location {atom}
  guard state := absent ∉ state watched
  reads := {watched}
  writes := {location}
  consumed_outside _ _ := rfl
  produced_outside other outside := by
    have different : other ≠ location := by simpa using outside
    simp [different]
  guard_local agrees holds := by
    rwa [← agrees _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))]

/-- **The read of an absence guard is load-bearing.**  Certified with the
written location only, the rule has no certificate: a surrounding change at the
watched location disables it. -/
theorem addUnless_needs_its_read {location watched : Location}
    (different : watched ≠ location) (atom absent : Atom) :
    ¬ EffectFootprinted (addUnless location watched atom absent).Fires ∅ {location} := by
  intro certified
  have fires : (addUnless location watched atom absent).Fires 0 (Pi.single location {atom}) :=
    ⟨by simp [addUnless], 0, fun _ => trivial, fun _ => trivial, by simp [addUnless],
      by simp [addUnless]⟩
  obtain ⟨_, ⟨guarded, -⟩, -, -⟩ :=
    certified.frame fires (Pi.single watched {absent}) (by
      intro other inside
      have same : other = location := by simpa using inside
      subst same
      simp [Ne.symm different])
  simp [addUnless] at guarded

/-- **An absence guard breaks the diamond** even when the written locations and
the matches of the two instances are disjoint: adding `absent` at the watched
location disables the guarded addition. -/
theorem absence_guard_breaks_diamond {location watched : Location}
    (different : watched ≠ location) (atom absent : Atom) :
    Disjoint (addUnless location watched atom absent).writes (addAtom watched absent).writes ∧
      (addUnless location watched atom absent).Fires 0 (Pi.single location {atom}) ∧
      (addAtom watched absent).Fires 0 (Pi.single watched {absent}) ∧
      ¬ ∃ joined,
        (addAtom watched absent).Fires (Pi.single location {atom}) joined ∧
          (addUnless location watched atom absent).Fires (Pi.single watched {absent}) joined := by
  refine ⟨?_, ⟨by simp [addUnless], 0, fun _ => trivial, fun _ => trivial,
      by simp [addUnless], by simp [addUnless]⟩, (addAtom_fires_iff _ _ _ _).mpr (by simp), ?_⟩
  · simpa [addUnless, addAtom, LocalRule.unguarded] using different.symm
  · rintro ⟨joined, -, guarded, -⟩
    simp [addUnless] at guarded

/-- And the certificates see it: the two instances are not independent. -/
theorem absence_guard_not_independent {location watched : Location} (atom absent : Atom) :
    ¬ IndependentEffects (addUnless location watched atom absent).reads
      (addUnless location watched atom absent).writes
      (addAtom watched absent).reads (addAtom watched absent).writes := by
  simp [IndependentEffects, addUnless, addAtom, LocalRule.unguarded]

end SpaceRules

/-! ## A whole-bag test is not local -/

/-- Add one `atom` to a bag, read by multiplicities, when the bag is empty. -/
def EmptinessTest [DecidableEq Atom] (atom : Atom) (source target : Atom → ℕ) : Prop :=
  source = 0 ∧ target = Pi.single atom 1

/-- **A test of the whole bag has no finite footprint** over an infinite
alphabet: whatever finite sets it is said to read and write, a copy of an atom
outside them disables it. -/
theorem emptinessTest_not_effectFootprinted [DecidableEq Atom] [Infinite Atom]
    (atom : Atom) (reads writes : Finset Atom) :
    ¬ EffectFootprinted (EmptinessTest atom) reads writes := by
  intro certified
  obtain ⟨outside, notMem⟩ := Infinite.exists_notMem_finset (reads ∪ writes)
  obtain ⟨_, ⟨empty, -⟩, -, -⟩ :=
    certified.frame (source := 0) ⟨rfl, rfl⟩ (Pi.single outside 1) (by
      intro other inside
      have different : other ≠ outside := fun same => notMem (same ▸ inside)
      simp [different])
  have := congrFun empty outside
  simp at this

/-! ## A bag read by kinds -/

section Marking

variable [DecidableEq Atom]

/-- The multiplicity of every atom: a bag as a located state. -/
def marking (bag : Multiset Atom) : Atom → ℕ := fun atom => bag.count atom

theorem marking_add (first second : Multiset Atom) :
    marking (first + second) = marking first + marking second :=
  funext fun atom => Multiset.count_add atom first second

/-- A bag is determined by its multiplicities. -/
theorem marking_injective : Function.Injective (marking (Atom := Atom)) :=
  fun _ _ same => Multiset.ext.mpr fun atom => congrFun same atom

/-- **A local bag rule**: replace the sub-bag `consumed` by `produced` in any
surrounding bag. -/
def BagRule (consumed produced source target : Multiset Atom) : Prop :=
  ∃ frame, source = consumed + frame ∧ target = produced + frame

/-- The same rule on multiplicities: it writes the kinds it consumes or
produces and reads nothing else. -/
def markingRule (consumed produced : Multiset Atom) : LocalRule Atom ℕ :=
  LocalRule.unguarded (marking consumed) (marking produced)
    (consumed.toFinset ∪ produced.toFinset)
    (fun _ outside => Multiset.count_eq_zero.mpr fun member =>
      outside (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr member)))
    (fun _ outside => Multiset.count_eq_zero.mpr fun member =>
      outside (Finset.mem_union_right _ (Multiset.mem_toFinset.mpr member)))

/-- A decomposition of a bag's multiplicities with the consumed part in front
contains the consumed bag, and the rest is the multiplicities of the
difference. -/
theorem frame_of_marking {consumed source : Multiset Atom} {frame : Atom → ℕ}
    (decomposition : marking source = marking consumed + frame) :
    consumed ≤ source ∧ frame = marking (source - consumed) := by
  have pointwise : ∀ atom, source.count atom = consumed.count atom + frame atom :=
    fun atom => congrFun decomposition atom
  refine ⟨Multiset.le_iff_count.mpr fun atom => by rw [pointwise atom]; omega, ?_⟩
  funext atom
  show frame atom = (source - consumed).count atom
  rw [Multiset.count_sub, pointwise atom]
  omega

/-- A contained bag is split off with the difference as its frame. -/
theorem bag_of_frame {consumed source : Multiset Atom} (contained : consumed ≤ source) :
    source = consumed + (source - consumed) := by
  apply marking_injective
  funext atom
  show source.count atom = (consumed + (source - consumed)).count atom
  rw [Multiset.count_add, Multiset.count_sub]
  have := Multiset.le_iff_count.mp contained atom
  omega

/-- **The locality theorem for bags.**  A local bag rule is exactly the
restriction to bags of the local rule on multiplicities.  This is where
commutativity is spent: a bag is its multiplicities. -/
theorem bagRule_iff_fires (consumed produced source target : Multiset Atom) :
    BagRule consumed produced source target ↔
      (markingRule consumed produced).Fires (marking source) (marking target) := by
  constructor
  · rintro ⟨frame, rfl, rfl⟩
    exact ⟨trivial, marking frame, fun _ => trivial, fun _ => trivial,
      marking_add _ _, marking_add _ _⟩
  · rintro ⟨-, frame, -, -, sourceDecomposition, targetDecomposition⟩
    obtain ⟨contained, rfl⟩ := frame_of_marking sourceDecomposition
    refine ⟨source - consumed, bag_of_frame contained, marking_injective ?_⟩
    rw [marking_add]
    exact targetDecomposition

/-- And the rule on multiplicities never leaves the bags: from a bag it reaches
only bags. -/
theorem exists_marking_of_fires {consumed produced source : Multiset Atom}
    {target : Atom → ℕ}
    (fires : (markingRule consumed produced).Fires (marking source) target) :
    ∃ bag, target = marking bag := by
  obtain ⟨-, frame, -, -, sourceDecomposition, rfl⟩ := fires
  obtain ⟨-, rfl⟩ := frame_of_marking sourceDecomposition
  exact ⟨produced + (source - consumed), (marking_add _ _).symm⟩

/-- **Two local bag rules on disjoint kinds commute.** -/
theorem bagRule_commute {firstConsumed firstProduced secondConsumed secondProduced
      source afterFirst afterSecond : Multiset Atom}
    (disjoint : Disjoint (firstConsumed.toFinset ∪ firstProduced.toFinset)
      (secondConsumed.toFinset ∪ secondProduced.toFinset))
    (firstStep : BagRule firstConsumed firstProduced source afterFirst)
    (secondStep : BagRule secondConsumed secondProduced source afterSecond) :
    ∃ joined, BagRule secondConsumed secondProduced afterFirst joined ∧
      BagRule firstConsumed firstProduced afterSecond joined := by
  obtain ⟨joined, secondFires, firstFires⟩ :=
    LocalRule.commute (markingRule firstConsumed firstProduced)
      (markingRule secondConsumed secondProduced)
      (by
        show Disjoint (firstConsumed.toFinset ∪ firstProduced.toFinset)
            (∅ ∪ (secondConsumed.toFinset ∪ secondProduced.toFinset)) ∧
          Disjoint (secondConsumed.toFinset ∪ secondProduced.toFinset)
            (∅ ∪ (firstConsumed.toFinset ∪ firstProduced.toFinset))
        rw [Finset.empty_union, Finset.empty_union]
        exact ⟨disjoint, disjoint.symm⟩)
      ((bagRule_iff_fires _ _ _ _).mp firstStep) ((bagRule_iff_fires _ _ _ _).mp secondStep)
  obtain ⟨bag, rfl⟩ := exists_marking_of_fires secondFires
  exact ⟨bag, (bagRule_iff_fires _ _ _ _).mpr secondFires,
    (bagRule_iff_fires _ _ _ _).mpr firstFires⟩

/-- A positional rule: replace a contiguous block of a sequence in any
surrounding sequence. -/
def ListRule (consumed produced source target : List Atom) : Prop :=
  ∃ before after, source = before ++ consumed ++ after ∧ target = before ++ produced ++ after

/-- **Without commutativity there is no reading by kinds.**  The block `[a, b]`
can be removed from `[a, b]` and not from `[b, a]`, which have the same
multiplicities, so no relation on multiplicities restricts to the positional
rule. -/
theorem listRule_not_read_by_kinds {first second : Atom} (different : first ≠ second) :
    ¬ ∃ located : (Atom → ℕ) → (Atom → ℕ) → Prop,
      ∀ source target, ListRule [first, second] [] source target ↔
        located (fun atom => source.count atom) (fun atom => target.count atom) := by
  rintro ⟨located, restricts⟩
  have removable : ListRule [first, second] [] [first, second] [] :=
    ⟨[], [], rfl, rfl⟩
  have sameKinds : (fun atom => [second, first].count atom) =
      (fun atom => [first, second].count atom) :=
    funext fun atom => (List.Perm.swap first second []).count_eq atom
  have swapped : ListRule [first, second] [] [second, first] [] := by
    rw [restricts, sameKinds]
    exact (restricts _ _).mp removable
  obtain ⟨before, after, decomposition, -⟩ := swapped
  have lengths := congrArg List.length decomposition
  simp only [List.length_cons, List.length_nil, List.length_append] at lengths
  have beforeEmpty : before = [] := List.eq_nil_of_length_eq_zero (by omega)
  have afterEmpty : after = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst beforeEmpty afterEmpty
  simp only [List.nil_append, List.append_nil, List.cons.injEq] at decomposition
  exact different decomposition.2.1

end Marking

#print axioms Footprinted.disjoint_commute
#print axioms EffectFootprinted.independent_commute
#print axioms Request.footprinted
#print axioms Request.effectFootprinted
#print axioms Request.independent_commute_via_footprints
#print axioms Request.observations_share_location
#print axioms Request.consumes_same_location_not_independent
#print axioms GuardedTransaction.disjoint_commute
#print axioms singleton_footprint_not_self_disjoint
#print axioms EffectFootprinted.footprinted
#print axioms LocalRule.effectFootprinted
#print axioms LocalRule.commute
#print axioms SpaceRules.removeAtom_fires_iff
#print axioms SpaceRules.addAtom_fires_iff
#print axioms SpaceRules.addUnless_needs_its_read
#print axioms SpaceRules.absence_guard_breaks_diamond
#print axioms emptinessTest_not_effectFootprinted
#print axioms bagRule_iff_fires
#print axioms exists_marking_of_fires
#print axioms bagRule_commute
#print axioms listRule_not_read_by_kinds

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
