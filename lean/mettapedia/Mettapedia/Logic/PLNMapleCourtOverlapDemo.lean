import Mettapedia.Logic.BinEvNat

/-!
# Maple Court Overlap Demo: Shared Hallway Vent

Two apartments' humidity sensors share a hallway vent. Naive addition
of their evidence double-counts the shared signal. The overlap
correction removes exactly the double-counted amount. When the vent
is sealed (independent), additivity recovers.

All proofs by `decide` on `BinEvNat`.

Reference: wm-pln-book_v3.tex, §3.3 (Non-Additive Perimeter),
Maple Court box: "Two apartments share a hallway humidity vent."

0 sorry.
-/

namespace Mettapedia.Logic.PLNMapleCourtOverlapDemo

open Mettapedia.Logic

/-! ## §1: Evidence from two sensors sharing a vent

Sensor A (apartment 301): reports humidity evidence ⟨3, 1⟩
  (3 high-humidity readings, 1 normal reading)
Sensor B (apartment 302): reports humidity evidence ⟨2, 2⟩
  (2 high, 2 normal)
Shared vent: contributes ⟨1, 0⟩ to BOTH sensors
  (1 high reading from the vent that both sensors pick up) -/

def sensorA : BinEvNat := ⟨3, 1⟩
def sensorB : BinEvNat := ⟨2, 2⟩
def sharedVent : BinEvNat := ⟨1, 0⟩

/-! ## §2: Naive addition double-counts -/

def naiveTotal : BinEvNat := sensorA + sensorB

theorem naive_total : naiveTotal = ⟨5, 3⟩ := by decide

/-! ## §3: Overlap correction (inclusion-exclusion)

corrected = sensorA + sensorB - sharedVent
The shared vent reading counted in both sensors is subtracted once. -/

def correctedTotal : BinEvNat := ⟨sensorA.pos + sensorB.pos - sharedVent.pos,
                                   sensorA.neg + sensorB.neg - sharedVent.neg⟩

theorem corrected_total : correctedTotal = ⟨4, 3⟩ := by decide

theorem naive_overcounts : naiveTotal ≠ correctedTotal := by decide

/-! ## §4: When the vent is sealed (independence), additivity recovers -/

def sealedVent : BinEvNat := ⟨0, 0⟩

def correctedSealed : BinEvNat := ⟨sensorA.pos + sensorB.pos - sealedVent.pos,
                                    sensorA.neg + sensorB.neg - sealedVent.neg⟩

theorem sealed_vent_recovery : correctedSealed = naiveTotal := by decide

/-! ## §5: Sensitivity — which sensor contributes more? -/

def withoutA : BinEvNat := ⟨sensorB.pos - sharedVent.pos, sensorB.neg - sharedVent.neg⟩
def withoutB : BinEvNat := ⟨sensorA.pos - sharedVent.pos, sensorA.neg - sharedVent.neg⟩

-- Sensor A's net contribution (after removing shared vent)
theorem sensorA_net : withoutB = ⟨2, 1⟩ := by decide
-- Sensor B's net contribution (after removing shared vent)
theorem sensorB_net : withoutA = ⟨1, 2⟩ := by decide

-- Sensor A contributes more positive evidence than sensor B
theorem sensorA_stronger : withoutB.pos > withoutA.pos := by decide

/-! ## §6: End-to-end summary -/

theorem end_to_end :
    -- Naive addition gives ⟨5, 3⟩
    naiveTotal = ⟨5, 3⟩ ∧
    -- Corrected gives ⟨4, 3⟩ (one less positive from shared vent)
    correctedTotal = ⟨4, 3⟩ ∧
    -- They differ
    naiveTotal ≠ correctedTotal ∧
    -- Sealing the vent recovers additivity
    correctedSealed = naiveTotal ∧
    -- Sensor A's net contribution is stronger
    withoutB.pos > withoutA.pos := by decide

end Mettapedia.Logic.PLNMapleCourtOverlapDemo
