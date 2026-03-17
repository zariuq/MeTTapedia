import Mettapedia.Logic.WorldModelBase
import Mettapedia.Logic.PLNWorldModelGeneric

/-!
# WorldModel Hierarchy Bridges

Explicit constructions witnessing that each specialized world model
gives rise to the more general ones above it:

    AdditiveWorldModel → MonoidalWorldModel → WorldModel

These are `def`s, not `instance`s, to avoid typeclass diamonds.
-/

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelGeneric

/-- Every `AdditiveWorldModel` gives a `WorldModel`. -/
def worldModelOfAdditive
    (State Query Ev : Type*)
    [EvidenceType State] [AddCommMonoid Ev]
    [AdditiveWorldModel State Query Ev] :
    WorldModel State Query Ev where
  revise := (· + ·)
  empty := 0
  extract := AdditiveWorldModel.extract

/-- Every `AdditiveWorldModel` gives a `MonoidalWorldModel`. -/
def monoidalWorldModelOfAdditive
    (State Query Ev : Type*)
    [EvidenceType State] [AddCommMonoid Ev]
    [AdditiveWorldModel State Query Ev] :
    MonoidalWorldModel State Query Ev where
  revise := (· + ·)
  empty := 0
  extract := AdditiveWorldModel.extract
  revise_assoc := add_assoc
  revise_empty_left := zero_add
  revise_empty_right := add_zero

/-- Every `BinaryWorldModel` gives an `AdditiveWorldModel` at `Ev = BinaryEvidence`. -/
noncomputable def additiveWorldModelOfBinary
    (State Query : Type*)
    [EvidenceType State]
    [BinaryWorldModel State Query] :
    AdditiveWorldModel State Query BinaryEvidence where
  extract := BinaryWorldModel.evidence
  extract_add := BinaryWorldModel.evidence_add

/-- Every `BinaryWorldModel` gives a `WorldModel` (composite bridge). -/
noncomputable def worldModelOfBinary
    (State Query : Type*)
    [EvidenceType State]
    [BinaryWorldModel State Query] :
    WorldModel State Query BinaryEvidence where
  revise := (· + ·)
  empty := 0
  extract := BinaryWorldModel.evidence
