import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Stable contraction of ordered occurrence families

A mutable MeTTa space is observed as an ordered family of occurrences.  A
bulk removal therefore acts on occurrence positions, not merely on distinct
values: equal rows may be retained or removed independently, and every
retained row keeps its relative order.

This module separates that semantic contraction from its coordinate
realization.  `contract` is the independent list semantics.  `compile` emits
the same target together with a partial source-to-target coordinate map.
The coordinate theorem licenses an implementation that transports derived
indexes through the map instead of rebuilding them from the target rows.

The final cost statement is intentionally representation-relative.  For an
explicit target array, exactness fixes the number of target-row writes.  It
does not claim a lower bound for persistent, compressed, or symbolic
realizations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.StableOccurrenceContraction

universe uRow uTarget

/-- Stable ordered contraction.  A missing mask suffix retains nothing; the
runtime admission law separately requires equal source and mask lengths. -/
def contract {Row : Type uRow} : List Bool → List Row → List Row
  | true :: mask, row :: rows => row :: contract mask rows
  | false :: mask, _ :: rows => contract mask rows
  | _, _ => []

/-- An executable contraction result.  `sourceToTarget[i] = some j` says that
source occurrence `i` survives at target occurrence `j`; `none` receipts a
removed source occurrence. -/
structure Result (Row : Type uRow) where
  rows : List Row
  sourceToTarget : List (Option Nat)
deriving DecidableEq, Repr

private def shiftCoordinate : Option Nat → Option Nat :=
  Option.map Nat.succ

/-- Compile a stable contraction and its coordinate transport in one pass. -/
def compile {Row : Type uRow} : List Bool → List Row → Result Row
  | true :: mask, row :: rows =>
      let tail := compile mask rows
      { rows := row :: tail.rows
        sourceToTarget := some 0 :: tail.sourceToTarget.map shiftCoordinate }
  | false :: mask, _ :: rows =>
      let tail := compile mask rows
      { rows := tail.rows
        sourceToTarget := none :: tail.sourceToTarget }
  | _, _ => { rows := [], sourceToTarget := [] }

/-- The coordinate compiler is independently adequate for the ordered-list
semantics. -/
theorem compile_rows_exact {Row : Type uRow}
    (mask : List Bool) (rows : List Row) :
    (compile mask rows).rows = contract mask rows := by
  induction mask generalizing rows with
  | nil => simp [compile, contract]
  | cons keep mask inductionHypothesis =>
      cases rows with
      | nil => simp [compile, contract]
      | cons row rows =>
          cases keep <;> simp [compile, contract, inductionHypothesis]

/-- Stable contraction is natural in the row payload: changing every payload
before contraction is the same as changing every retained payload afterward.
This is the commuting square used by payload-independent indexes. -/
theorem contract_map {Row : Type uRow} {Target : Type uTarget}
    (transform : Row → Target) (mask : List Bool) (rows : List Row) :
    contract mask (rows.map transform) =
      (contract mask rows).map transform := by
  induction mask generalizing rows with
  | nil => simp [contract]
  | cons keep mask inductionHypothesis =>
      cases rows with
      | nil => simp [contract]
      | cons row rows =>
          cases keep <;> simp [contract, inductionHypothesis]

/-- Every emitted source-to-target coordinate points to the same occurrence
payload in the independent source and target observations. -/
theorem sourceToTarget_sound {Row : Type uRow}
    (mask : List Bool) (rows : List Row) (sourceIndex targetIndex : Nat)
    (mapped :
      (compile mask rows).sourceToTarget[sourceIndex]? =
        some (some targetIndex)) :
    rows[sourceIndex]? = (compile mask rows).rows[targetIndex]? := by
  induction mask generalizing rows sourceIndex targetIndex with
  | nil => simp [compile] at mapped
  | cons keep mask inductionHypothesis =>
      cases rows with
      | nil => simp [compile] at mapped
      | cons row rows =>
          cases keep with
          | false =>
              cases sourceIndex with
              | zero => simp [compile] at mapped
              | succ sourceIndex =>
                  simp only [compile] at mapped ⊢
                  exact inductionHypothesis rows sourceIndex targetIndex mapped
          | true =>
              cases sourceIndex with
              | zero =>
                  simp [compile] at mapped
                  subst targetIndex
                  simp [compile]
              | succ sourceIndex =>
                  simp only [compile] at mapped
                  cases coordinate :
                      (compile mask rows).sourceToTarget[sourceIndex]? with
                  | none => simp [coordinate] at mapped
                  | some coordinateValue =>
                      cases coordinateValue with
                      | none => simp [coordinate, shiftCoordinate] at mapped
                      | some tailTargetIndex =>
                          simp [coordinate, shiftCoordinate] at mapped
                          subst targetIndex
                          simp only [compile]
                          exact inductionHypothesis rows sourceIndex
                            tailTargetIndex coordinate

/-- The compiled coordinate table covers exactly the common source/mask
prefix.  Equal lengths therefore give one receipt per source occurrence. -/
theorem sourceToTarget_length {Row : Type uRow}
    (mask : List Bool) (rows : List Row) :
    (compile mask rows).sourceToTarget.length =
      min mask.length rows.length := by
  induction mask generalizing rows with
  | nil => simp [compile]
  | cons keep mask inductionHypothesis =>
      cases rows with
      | nil => simp [compile]
      | cons row rows =>
          cases keep <;>
            simp [compile, inductionHypothesis, Nat.succ_min_succ]

/-- A coordinate transport is stable exactly when removed source occurrences
may be skipped and each retained source occurrence receives the next target
coordinate.  The retained coordinates are therefore monotone, gap-free, and
begin at zero. -/
inductive IsStableCoordinateTransport : Nat → List (Option Nat) → Prop where
  | nil : IsStableCoordinateTransport 0 []
  | removed {targetLength coordinates} :
      IsStableCoordinateTransport targetLength coordinates →
      IsStableCoordinateTransport targetLength (none :: coordinates)
  | retained {targetLength coordinates} :
      IsStableCoordinateTransport targetLength coordinates →
      IsStableCoordinateTransport (Nat.succ targetLength)
        (some 0 :: coordinates.map shiftCoordinate)

/-- The complete admission certificate carried by a compiled coordinate
transport: one coordinate receipt exists for every source occurrence in the
common source/mask prefix, and the surviving receipts enumerate the target
coordinates stably. -/
structure TransportCertificate
    (sourceLength targetLength : Nat)
    (coordinates : List (Option Nat)) : Prop where
  coversSource : coordinates.length = sourceLength
  stable : IsStableCoordinateTransport targetLength coordinates

/-- The one-pass compiler emits a stable, gap-free coordinate transport. -/
theorem compile_sourceToTarget_stable {Row : Type uRow}
    (mask : List Bool) (rows : List Row) :
    IsStableCoordinateTransport
      (compile mask rows).rows.length
      (compile mask rows).sourceToTarget := by
  induction mask generalizing rows with
  | nil => exact IsStableCoordinateTransport.nil
  | cons keep mask inductionHypothesis =>
      cases rows with
      | nil => simpa [compile] using IsStableCoordinateTransport.nil
      | cons row rows =>
          cases keep with
          | false =>
              exact IsStableCoordinateTransport.removed
                (inductionHypothesis rows)
          | true =>
              exact IsStableCoordinateTransport.retained
                (inductionHypothesis rows)

/-- Equal source/mask lengths specialize the compiler to a certificate over
the whole source family; unequal inputs still receive an honest certificate
for their common prefix. -/
theorem compile_transport_certificate {Row : Type uRow}
    (mask : List Bool) (rows : List Row) :
    TransportCertificate
      (min mask.length rows.length)
      (compile mask rows).rows.length
      (compile mask rows).sourceToTarget where
  coversSource := sourceToTarget_length mask rows
  stable := compile_sourceToTarget_stable mask rows

/-- Contraction never increases the number of observed occurrences. -/
theorem contract_length_le {Row : Type uRow}
    (mask : List Bool) (rows : List Row) :
    (contract mask rows).length ≤ rows.length := by
  induction mask generalizing rows with
  | nil => simp [contract]
  | cons keep mask inductionHypothesis =>
      cases rows with
      | nil => simp [contract]
      | cons row rows =>
          cases keep with
          | false =>
              exact Nat.le.step (inductionHypothesis rows)
          | true =>
              simpa [contract] using
                Nat.succ_le_succ (inductionHypothesis rows)

/-- One explicit-array realization of the contraction semantics. -/
structure ExplicitRealization (Row : Type uRow)
    (mask : List Bool) (source : List Row) where
  target : List Row
  exact : target = contract mask source

/-- Representation-relative lower bound: every exact explicit target stores
exactly one cell per retained occurrence.  Symbolic and persistent carriers
are deliberately outside this statement. -/
theorem explicit_target_cells_exact {Row : Type uRow}
    (mask : List Bool) (source : List Row)
    (realization : ExplicitRealization Row mask source) :
    realization.target.length = (contract mask source).length := by
  rw [realization.exact]

/-! ## Independent positive and negative controls -/

/-- Equal payloads remain distinct occurrences when only one is removed. -/
example :
    contract [true, false, true] ["same", "same", "tail"] =
      ["same", "tail"] := by
  decide

/-- Stable contraction cannot reverse the retained occurrences. -/
example :
    contract [true, false, true] ["left", "middle", "right"] ≠
      ["right", "left"] := by
  decide

/-- The coordinate map distinguishes equal occurrences by position. -/
example :
    (compile [false, true, true] ["same", "same", "tail"]).sourceToTarget =
      [none, some 0, some 1] := by
  decide

/-- The compiled example carries the stronger monotone, gap-free transport
certificate, not merely the expected concrete coordinate bytes. -/
example :
    IsStableCoordinateTransport 2 [none, some 0, some 1] := by
  exact IsStableCoordinateTransport.removed
    (IsStableCoordinateTransport.retained
      (IsStableCoordinateTransport.retained
        IsStableCoordinateTransport.nil))

/-- Reversing two retained coordinates is not a stable transport. -/
example :
    ¬ IsStableCoordinateTransport 2 [some 1, some 0] := by
  intro transport
  cases transport

#print axioms compile_rows_exact
#print axioms contract_map
#print axioms sourceToTarget_sound
#print axioms sourceToTarget_length
#print axioms compile_sourceToTarget_stable
#print axioms compile_transport_certificate
#print axioms contract_length_le
#print axioms explicit_target_cells_exact

end Mettapedia.GSLT.Dynamics.StableOccurrenceContraction
