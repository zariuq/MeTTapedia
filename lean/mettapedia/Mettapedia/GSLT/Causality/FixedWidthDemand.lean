import Mettapedia.GSLT.Causality.ResourceWaves
import Mathlib.Data.BitVec

/-!
# Deciding wave demand with fixed-width counters

A wave admits a candidate when, for every resource, the largest read demand,
the accumulated consumption and the candidate's consumption fit in the supply
(`WaveDemand.reserve_fits_iff_count`). With counters of `w` bits the sum of
the three may not be representable, so forming it first is wrong.

`fits` subtracts instead of adding: it compares each demand with what is left
after the earlier ones, so no intermediate value wraps. It decides the
unbounded inequality at every width (`fits_eq_decide`), while the check that
forms the modular sum does not (`Controls.sum_check_wraps`). When the words
encode the multiset counts, the per-resource check decides admission of the
whole reservation (`fits_iff_reserve_fits`), and an admitted update of the
consumption and read words encodes the reserved demand
(`reserve_encoded`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.FixedWidthDemand

open ResourceInteraction

variable {w : Nat}

/-- Decide `read + consumed + added ≤ available` by guarded subtraction. -/
def fits (available read consumed added : BitVec w) : Bool :=
  if read > available then false
  else if consumed > available - read then false
  else decide (added ≤ available - read - consumed)

/-- The check that forms the modular sum first. It is not a decision
procedure for the demand inequality (`Controls.sum_check_wraps`). -/
def sumFits (available read consumed added : BitVec w) : Bool :=
  decide (read + consumed + added ≤ available)

/-- Guarded subtraction decides the demand inequality over the naturals. -/
theorem fits_eq_decide (available read consumed added : BitVec w) :
    fits available read consumed added =
      decide (read.toNat + consumed.toNat + added.toNat ≤ available.toNat) := by
  unfold fits
  by_cases readTooLarge : read > available
  · have short : available.toNat < read.toNat := BitVec.lt_def.mp readTooLarge
    rw [if_pos readTooLarge]
    symm
    apply decide_eq_false
    omega
  · have readFits : read ≤ available := by
      rw [BitVec.le_def]
      have short : ¬ available.toNat < read.toNat := by
        simpa only [GT.gt, BitVec.lt_def] using readTooLarge
      omega
    have subtractRead : (available - read).toNat = available.toNat - read.toNat :=
      BitVec.toNat_sub_of_le readFits
    rw [if_neg readTooLarge]
    by_cases consumedTooLarge : consumed > available - read
    · have short : available.toNat - read.toNat < consumed.toNat := by
        rw [← subtractRead]
        exact BitVec.lt_def.mp consumedTooLarge
      rw [if_pos consumedTooLarge]
      symm
      apply decide_eq_false
      omega
    · have consumedFits : consumed ≤ available - read := by
        rw [BitVec.le_def]
        have short : ¬ (available - read).toNat < consumed.toNat := by
          simpa only [GT.gt, BitVec.lt_def] using consumedTooLarge
        omega
      have subtractConsumed : (available - read - consumed).toNat =
          available.toNat - read.toNat - consumed.toNat := by
        rw [BitVec.toNat_sub_of_le consumedFits, subtractRead]
      rw [if_neg consumedTooLarge]
      have readNatFits := BitVec.le_def.mp readFits
      have consumedNatFits := BitVec.le_def.mp consumedFits
      rw [subtractRead] at consumedNatFits
      by_cases enough : read.toNat + consumed.toNat + added.toNat ≤ available.toNat
      · have addedFits : added ≤ available - read - consumed := by
          rw [BitVec.le_def, subtractConsumed]
          omega
        simp only [addedFits, enough, decide_true]
      · have addedDoesNotFit : ¬ added ≤ available - read - consumed := by
          rw [BitVec.le_def, subtractConsumed]
          omega
        simp only [addedDoesNotFit, enough, decide_false]

/-- Readers share a resource: the retained read demand is the larger claim. -/
def readMax (previous claim : BitVec w) : BitVec w :=
  if claim > previous then claim else previous

theorem readMax_toNat (previous claim : BitVec w) :
    (readMax previous claim).toNat = max previous.toNat claim.toNat := by
  unfold readMax
  by_cases increased : claim > previous
  · rw [if_pos increased]
    have larger := BitVec.lt_def.mp increased
    omega
  · rw [if_neg increased]
    have notLarger : ¬ previous.toNat < claim.toNat := by
      simpa only [GT.gt, BitVec.lt_def] using increased
    omega

/-- An admitted check licenses the following unsigned addition: the updated
consumption does not wrap and the complete demand still fits. -/
theorem fits_add_exact (available read consumed added : BitVec w)
    (admitted : fits available read consumed added = true) :
    (consumed + added).toNat = consumed.toNat + added.toNat ∧
      read.toNat + (consumed + added).toNat ≤ available.toNat := by
  rw [fits_eq_decide] at admitted
  have enough := of_decide_eq_true admitted
  have availableBound := available.isLt
  have noWrap : consumed.toNat + added.toNat < 2 ^ w := by omega
  have exactSum : (consumed + added).toNat = consumed.toNat + added.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt noWrap]
  exact ⟨exactSum, by omega⟩

variable {R : Type*} [DecidableEq R]

/-- Words that encode a wave's demand, a candidate's footprint and the supply,
resource by resource. -/
structure Encodes (available : Multiset R) (demand : WaveDemand R) (consume read : Multiset R)
    (supply previousRead previousConsume added claimRead : R → BitVec w) : Prop where
  supply : ∀ resource, (supply resource).toNat = available.count resource
  previousRead : ∀ resource, (previousRead resource).toNat = demand.read.count resource
  previousConsume : ∀ resource,
    (previousConsume resource).toNat = demand.consume.count resource
  added : ∀ resource, (added resource).toNat = consume.count resource
  claimRead : ∀ resource, (claimRead resource).toNat = read.count resource

/-- The per-resource fixed-width check decides admission of the reservation. -/
theorem fits_iff_reserve_fits {available : Multiset R} {demand : WaveDemand R}
    {consume read : Multiset R} {supply previousRead previousConsume added claimRead : R → BitVec w}
    (encoding : Encodes available demand consume read supply previousRead previousConsume added
      claimRead) :
    (∀ resource, fits (supply resource) (readMax (previousRead resource) (claimRead resource))
        (previousConsume resource) (added resource) = true) ↔
      (demand.reserve consume read).Fits available := by
  rw [WaveDemand.reserve_fits_iff_count]
  apply forall_congr'
  intro resource
  rw [fits_eq_decide, decide_eq_true_iff, readMax_toNat, encoding.supply,
    encoding.previousRead, encoding.previousConsume, encoding.added, encoding.claimRead]

/-- After an admitted check, the updated words encode the reserved demand. -/
theorem reserve_encoded {available : Multiset R} {demand : WaveDemand R}
    {consume read : Multiset R} {supply previousRead previousConsume added claimRead : R → BitVec w}
    (encoding : Encodes available demand consume read supply previousRead previousConsume added
      claimRead)
    (admitted : ∀ resource, fits (supply resource)
      (readMax (previousRead resource) (claimRead resource))
      (previousConsume resource) (added resource) = true) (resource : R) :
    (previousConsume resource + added resource).toNat =
        (demand.reserve consume read).consume.count resource ∧
      (readMax (previousRead resource) (claimRead resource)).toNat =
        (demand.reserve consume read).read.count resource := by
  have sum := (fits_add_exact _ _ _ _ (admitted resource)).1
  constructor
  · rw [sum, encoding.previousConsume, encoding.added]
    simp [WaveDemand.reserve]
  · rw [readMax_toNat, encoding.previousRead, encoding.claimRead]
    simp [WaveDemand.reserve]

namespace Controls

/-- `fits_eq_decide`: the boundary demand is admitted and one more unit is refused. -/
theorem boundary_admitted : fits (10 : BitVec 64) 4 5 1 = true := by decide +kernel

theorem excess_refused : fits (10 : BitVec 64) 4 5 2 = false := by decide +kernel

/-- A read of the full width is admitted when nothing else is demanded. -/
theorem full_width_read_admitted :
    fits (BitVec.allOnes 64) (BitVec.allOnes 64) 0 0 = true := by decide +kernel

/-- Forming the sum first wraps to zero and wrongly admits a demand that
exceeds the supply; guarded subtraction refuses it. -/
theorem sum_check_wraps :
    sumFits (BitVec.allOnes 64) (BitVec.allOnes 64) 1 0 = true ∧
      fits (BitVec.allOnes 64) (BitVec.allOnes 64) 1 0 = false := by decide +kernel

/-- `readMax_toNat`: a later, smaller read claim keeps the earlier demand.
Overwriting the read word with the smaller claim would admit two more
consumers than the supply allows. -/
theorem smaller_claim_keeps_read :
    readMax (7 : BitVec 64) 4 = 7 ∧
      fits (10 : BitVec 64) (readMax 7 4) 2 2 = false ∧
      fits (10 : BitVec 64) 4 2 2 = true := by decide +kernel

/-- `fits_add_exact`: an admitted update does not wrap ... -/
theorem admitted_update_exact : ((5 : BitVec 64) + 1).toNat = 6 :=
  (fits_add_exact (10 : BitVec 64) 4 5 1 boundary_admitted).1

/-- ... while an unchecked update can: the admission hypothesis is needed. -/
theorem unchecked_update_wraps :
    fits (BitVec.allOnes 64) 0 (BitVec.allOnes 64) 1 = false ∧
      ((BitVec.allOnes 64 : BitVec 64) + 1).toNat ≠ (BitVec.allOnes 64 : BitVec 64).toNat + 1 := by
  decide +kernel

/-- A single resource with two units of supply. -/
def two : Multiset Unit := {(), ()}

/-- Words that encode `two` as supply, an empty prior demand and one consumer. -/
theorem encoded_one_consumer :
    Encodes (w := 2) two WaveDemand.empty {()} 0 (fun _ => 2) (fun _ => 0) (fun _ => 0)
      (fun _ => 1) (fun _ => 0) where
  supply _ := rfl
  previousRead _ := rfl
  previousConsume _ := rfl
  added _ := rfl
  claimRead _ := rfl

/-- `fits_iff_reserve_fits`, `reserve_encoded`: the encoded check admits the
consumer, and the updated consumption word encodes the reserved demand. -/
theorem encoded_consumer_admitted :
    (WaveDemand.empty.reserve ({()} : Multiset Unit) 0).Fits two ∧
      ((0 : BitVec 2) + 1).toNat = (WaveDemand.empty.reserve ({()} : Multiset Unit) 0).consume.count () := by
  have admitted : ∀ resource : Unit, fits (w := 2) 2 (readMax 0 0) 0 1 = true := by
    intro _
    decide
  exact ⟨(fits_iff_reserve_fits encoded_one_consumer).mp admitted,
    (reserve_encoded encoded_one_consumer admitted ()).1⟩

/-- Without the encoding, the check and the reservation disagree: four units
of supply cannot be written in two bits, and the truncated word refuses a
consumer that the supply admits. -/
theorem truncated_supply_disagrees :
    (WaveDemand.empty.reserve ({()} : Multiset Unit) 0).Fits {(), (), (), ()} ∧
      fits (BitVec.ofNat 2 4) (readMax 0 0) 0 1 = false := by
  constructor
  · simp [WaveDemand.Fits, WaveDemand.reserve, WaveDemand.empty]
  · decide

end Controls

end Mettapedia.GSLT.Causality.FixedWidthDemand
