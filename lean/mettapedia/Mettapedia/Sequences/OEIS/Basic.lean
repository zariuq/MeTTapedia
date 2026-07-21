/-
# OEIS integer-sequence specifications and pinned provenance

The mathematical specification is deliberately independent of any synthesized
program or evaluator.  A source record identifies the exact OEIS snapshot entry
from which a formalization was prepared; it does not by itself assert that the
formalization faithfully translates the human entry.
-/

namespace Mettapedia.Sequences.OEIS

/-- An integer-valued OEIS sequence with an explicit mathematical offset and domain. -/
structure SequenceSpec where
  offset : Int
  Domain : Int → Prop
  value : Int → Int

/-- Convert a zero-based enumeration position into the sequence's mathematical index. -/
def SequenceSpec.index (spec : SequenceSpec) (position : Nat) : Int :=
  spec.offset + Int.ofNat position

/-- The immutable source coordinates for one formalized OEIS entry. -/
structure EntrySource where
  oeisId : String
  snapshotRevision : String
  entrySha256 : String
  offset : Int

/-- A formalization coupled to its source coordinates and checked offset agreement. -/
structure Formalization where
  source : EntrySource
  spec : SequenceSpec
  offsetMatches : spec.offset = source.offset

/-- A held-out term request generated from a formal sequence specification. -/
structure Probe (spec : SequenceSpec) where
  position : Nat
  indexInDomain : spec.Domain (spec.index position)

/-- The probe's expected value comes only from the formal specification. -/
def Probe.expected {spec : SequenceSpec} (probe : Probe spec) : Int :=
  spec.value (spec.index probe.position)

end Mettapedia.Sequences.OEIS
