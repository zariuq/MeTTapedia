import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeReadoutSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.AdditiveFoldSource
import Mettapedia.GSLT.Dynamics.RegionPortfolio

/-!
# Source-derived histogram regions for final mode observations

The source boundary is the independently interpreted captured fold and its
PeTTa let/readout continuation. The optimized result is a histogram readout.
The input list must be natural-valued and sorted before this route is admitted;
sorting an unqualified source input here would change the source program.

The scalar callback and readout are inferred from typed bodies, not their
function names. Source pages and accumulator-prefix observers receive no such
candidate. Preparation of raw values retains an exact reconstruction proof;
failure returns no candidate rather than a source answer.

Histogram storage and arithmetic here are mathematical. Native counters,
layout and preparation costs need additional refinement evidence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeAggregationPortfolio

open Mettapedia.GSLT.Dynamics ObservationQualified
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.ModeAggregation
open SpaceSemantics ModeFoldSource MeTTaIL.WireKit

structure Code where
  head : String
  names : Names
  readout : Atom

structure Certified (program : Program) (code : Code) where
  callback : ModeFoldSource.Certified program code.head
  names : callback.names = code.names
  readout : ModeReadoutSource.Certified program callback.names code.readout

def infer (program : Program) (code : Code) : Option (Certified program code) := do
  let callback ← ModeFoldSource.infer program code.head
  if names : callback.names = code.names then
    let readout ← ModeReadoutSource.infer program callback.names code.readout
    return ⟨callback, names, readout⟩
  else none

abbrev Input := Effects.State × List Nat

def sourceMeaning (program : Program) (code : Code) (input : Input) : Set Atom :=
  {answer | ModeReadoutSource.Completes program code.head code.names code.readout input.1 input.2 answer}

def boundary (program : Program) (code : Code) : Boundary Input (Set Atom) (Set Atom) where
  source := sourceMeaning program code
  summarize := id
  future := {Question := Set Atom → Bool, Answer _ := Bool, read question answers := question answers}
  sufficient _ _ same question := congrArg question same

theorem sourceMeaning_histogram {program : Program} {code : Code} (certificate : Certified program code)
    (input : Input) (sorted : input.2.Pairwise (· ≤ ·)) :
    sourceMeaning program code input = {labelAtom (sparseReadout (sparseHistogram input.2))} := by
  ext answer
  change ModeReadoutSource.Completes program code.head code.names code.readout input.1 input.2 answer ↔ _
  rw [← certificate.names, ModeReadoutSource.sorted_source_is_histogram certificate.callback certificate.readout _ _ sorted]
  rfl

noncomputable def region {program : Program} {code : Code} (certificate : Certified program code) :
    CertifiedRegion (boundary program code) Nat where
  regime := 0
  Artifact := Atom
  attempt input := if input.2.Pairwise (· ≤ ·) then
    .committed (labelAtom (sparseReadout (sparseHistogram input.2))) else .declined input
  decode answer := {answer}
  restores input restored declined := by
    dsimp only at declined
    split at declined
    · cases declined
    · exact (PartialRegionPlan.Attempt.declined.inj declined).symm
  exact input result accepted := by
    split at accepted
    next sorted =>
      cases accepted
      exact (sourceMeaning_histogram certificate input sorted).symm
    next => cases accepted

inductive Observer | finalValue | accumulatorPrefixes | sourcePages
  deriving DecidableEq

noncomputable def classify (observer : Observer) (program : Program) (code : Code) :
    Option (CertifiedRegion (boundary program code) Nat) :=
  match observer with
  | .finalValue => (infer program code).map region
  | .accumulatorPrefixes | .sourcePages => none

theorem stronger_observers_decline (program : Program) (code : Code) :
    classify .accumulatorPrefixes program code = none ∧ classify .sourcePages program code = none := ⟨rfl, rfl⟩

theorem unsorted_entrance_is_retained {program : Program} {code : Code} (certificate : Certified program code)
    (input : Input) (unsorted : ¬ input.2.Pairwise (· ≤ ·)) :
    (region certificate).attempt input = .declined input := by simp [region, unsorted]

structure Prepared (program : Program) (code : Code) (atoms : List Atom) where
  certificate : Certified program code
  values : List Nat
  reconstruction : atoms = values.map number
  sorted : values.Pairwise (· ≤ ·)

def prepare (observer : Observer) (program : Program) (code : Code) (atoms : List Atom) :
    Option (Prepared program code atoms) := do
  match observer with
  | .accumulatorPrefixes | .sourcePages => none
  | .finalValue =>
      let certificate ← infer program code
      match decoded : AdditiveFoldSource.naturals atoms with
      | none => none
      | some values =>
          if sorted : values.Pairwise (· ≤ ·) then
            return ⟨certificate, values, AdditiveFoldSource.naturals_exact atoms values decoded, sorted⟩
          else none

theorem prepared_source_exact {program : Program} {code : Code} {atoms : List Atom}
    (prepared : Prepared program code atoms) (world : Effects.State) :
    sourceMeaning program code (world, prepared.values) =
      {labelAtom (sparseReadout (sparseHistogram prepared.values))} :=
  sourceMeaning_histogram prepared.certificate _ prepared.sorted

/-- The original untyped input is returned on refusal. This is a dispatch
decision, not an empty result, a source fault or a replay of operand effects. -/
inductive Entry (program : Program) (code : Code) (atoms : List Atom) where
  | reference (original : List Atom)
  | admitted (prepared : Prepared program code atoms)

def enter (observer : Observer) (program : Program) (code : Code) (atoms : List Atom) : Entry program code atoms :=
  match prepare observer program code atoms with
  | none => .reference atoms
  | some prepared => .admitted prepared

theorem refusal_keeps_actual_inputs (observer : Observer) (program : Program) (code : Code) (atoms : List Atom)
    (refused : prepare observer program code atoms = none) :
    enter observer program code atoms = .reference atoms := by simp [enter, refused]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeAggregationPortfolio
