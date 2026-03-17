import Mettapedia.OSLF.Framework.WMCalculusLanguageDef
import Mettapedia.Logic.PLNMapleCourtDemo

/-!
# Maple Court Evidence Conformance: Full Semantic Coherence

Kernel-checked verification that the Maple Court full-day profile
computes correctly through evidence arithmetic operations.

## Three-layer coherence

1. **Reflected arithmetic model** (this file, §1): `BinEvN`/`KEv3N` with
   `hplus`/`krev`/`dirToBin`/`strength` — kernel-checked via `decide`
2. **Real extractor bridge** (this file, §2): proves the reflected values
   agree with `mapleCourtEvidence` from `PLNMapleCourtDemo.lean`
3. **PeTTa runtime**: `maple_court_full_profile.metta` (20+ assertEqual, all pass)

## Negative examples (§3)

Discrimination tests proving wrong values are rejected.  A trivial
checker that returns `true` for everything would fail these.

No `native_decide`.  No `sorry`.
-/

namespace Mettapedia.Conformance.MapleCourtEvidenceConformance

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## §1: Reflected Nat Arithmetic Model

Encode evidence as Lean Nats, compute, verify by `decide`. -/

/-- Binary evidence as Nat pair. -/
structure BinEvN where
  pos : Nat
  neg : Nat
  deriving DecidableEq, BEq

/-- 3-category evidence as Nat triple. -/
structure KEv3N where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  deriving DecidableEq, BEq

/-- HPlus on BinEvN. -/
def hplus (e₁ e₂ : BinEvN) : BinEvN := ⟨e₁.pos + e₂.pos, e₁.neg + e₂.neg⟩

/-- KRevision on KEv3N. -/
def krev (k₁ k₂ : KEv3N) : KEv3N := ⟨k₁.c0 + k₂.c0, k₁.c1 + k₂.c1, k₁.c2 + k₂.c2⟩

/-- DirichletToBinary projection. -/
def dirToBin (k : KEv3N) (i : Fin 3) : BinEvN :=
  let ci := match i with | 0 => k.c0 | 1 => k.c1 | 2 => k.c2
  let total := k.c0 + k.c1 + k.c2
  ⟨ci, total - ci⟩

/-- Strength as rational pair (num, den). -/
def strength (e : BinEvN) : Nat × Nat := (e.pos, e.pos + e.neg)

/-! ### Maple Court Observations -/

def morning_roomOccupied  : BinEvN := ⟨3, 0⟩
def morning_showerRunning : BinEvN := ⟨0, 0⟩
def morning_pipeLeak      : BinEvN := ⟨0, 0⟩
def morning_laundry : KEv3N := ⟨1, 0, 0⟩
def morning_elevator : KEv3N := ⟨1, 0, 0⟩

def evening_roomOccupied  : BinEvN := ⟨1, 0⟩
def evening_showerRunning : BinEvN := ⟨1, 0⟩
def evening_pipeLeak      : BinEvN := ⟨1, 0⟩
def evening_laundry : KEv3N := ⟨0, 1, 0⟩
def evening_elevator : KEv3N := ⟨1, 0, 0⟩

/-! ### Full-Day Computed Values -/

def refl_roomOccupied  : BinEvN := hplus morning_roomOccupied evening_roomOccupied
def refl_showerRunning : BinEvN := hplus morning_showerRunning evening_showerRunning
def refl_pipeLeak      : BinEvN := hplus morning_pipeLeak evening_pipeLeak
def refl_laundry : KEv3N := krev morning_laundry evening_laundry
def refl_elevator : KEv3N := krev morning_elevator evening_elevator

/-! ### Positive conformance (kernel-checked via `decide`) -/

-- Binary HPlus
theorem roomOccupied_eq : refl_roomOccupied = ⟨4, 0⟩ := by decide
theorem showerRunning_eq : refl_showerRunning = ⟨1, 0⟩ := by decide
theorem pipeLeak_eq : refl_pipeLeak = ⟨1, 0⟩ := by decide

-- Categorical KRevision
theorem laundryRevision_eq : refl_laundry = ⟨1, 1, 0⟩ := by decide
theorem elevatorRevision_eq : refl_elevator = ⟨2, 0, 0⟩ := by decide

-- DirichletToBinary projection
theorem laundryFree_eq : dirToBin refl_laundry 0 = ⟨1, 1⟩ := by decide
theorem laundryBusy_eq : dirToBin refl_laundry 1 = ⟨1, 1⟩ := by decide
theorem laundryFull_eq : dirToBin refl_laundry 2 = ⟨0, 2⟩ := by decide
theorem elevatorNormal_eq : dirToBin refl_elevator 0 = ⟨2, 0⟩ := by decide
theorem elevatorSlow_eq : dirToBin refl_elevator 1 = ⟨0, 2⟩ := by decide
theorem elevatorFaulty_eq : dirToBin refl_elevator 2 = ⟨0, 2⟩ := by decide

-- Strength (as rational num/den)
theorem strength_roomOccupied : strength refl_roomOccupied = (4, 4) := by decide
theorem strength_showerRunning : strength refl_showerRunning = (1, 1) := by decide
theorem strength_pipeLeak : strength refl_pipeLeak = (1, 1) := by decide
theorem strength_laundryFree : strength (dirToBin refl_laundry 0) = (1, 2) := by decide
theorem strength_laundryBusy : strength (dirToBin refl_laundry 1) = (1, 2) := by decide
theorem strength_laundryFull : strength (dirToBin refl_laundry 2) = (0, 2) := by decide
theorem strength_elevatorNormal : strength (dirToBin refl_elevator 0) = (2, 2) := by decide
theorem strength_elevatorSlow : strength (dirToBin refl_elevator 1) = (0, 2) := by decide
theorem strength_elevatorFaulty : strength (dirToBin refl_elevator 2) = (0, 2) := by decide

-- Compositionality: dirToBin of revision = hplus of dirToBin
theorem compositionality_laundry_0 :
    dirToBin (krev morning_laundry evening_laundry) 0 =
    hplus (dirToBin morning_laundry 0) (dirToBin evening_laundry 0) := by decide

theorem compositionality_elevator_0 :
    dirToBin (krev morning_elevator evening_elevator) 0 =
    hplus (dirToBin morning_elevator 0) (dirToBin evening_elevator 0) := by decide

/-! ## §2: Bridge to Real Extractor

The reflected model (§1) uses its own `BinEvN`/`hplus`/`dirToBin`.
The real extractor is `mapleCourtEvidence` from `PLNMapleCourtDemo.lean`
which operates on `BinaryEvidence` (ℝ≥0∞ pairs) and `MultiEvidence`.

These bridge theorems prove both sides agree on the same concrete values.
The reflected side uses `decide`; the extractor side reuses the existing
`fullDay_*` theorems (proved by `simp + norm_num`, also kernel-checked). -/

open Mettapedia.Logic.PLNMapleCourtDemo in
/-- Bridge: reflected (4,0) = real extractor roomOccupied output. -/
theorem bridge_roomOccupied (spec aptP bldP) :
    refl_roomOccupied = ⟨4, 0⟩ ∧
    mapleCourtEvidence spec aptP bldP fullDay .roomOccupied = ⟨4, 0⟩ :=
  ⟨by decide, Mettapedia.Logic.PLNMapleCourtDemo.fullDay_roomOccupied spec aptP bldP⟩

open Mettapedia.Logic.PLNMapleCourtDemo in
/-- Bridge: reflected (1,0) = real extractor pipeLeak output. -/
theorem bridge_pipeLeak (spec aptP bldP) :
    refl_pipeLeak = ⟨1, 0⟩ ∧
    mapleCourtEvidence spec aptP bldP fullDay .pipeLeak = ⟨1, 0⟩ :=
  ⟨by decide, Mettapedia.Logic.PLNMapleCourtDemo.fullDay_pipeLeak spec aptP bldP⟩

open Mettapedia.Logic.PLNMapleCourtDemo in
/-- Bridge: reflected (1,1) = real extractor laundryFree output. -/
theorem bridge_laundryFree (spec aptP bldP) :
    dirToBin refl_laundry 0 = ⟨1, 1⟩ ∧
    mapleCourtEvidence spec aptP bldP fullDay (.laundryInState 0) = ⟨1, 1⟩ :=
  ⟨by decide, Mettapedia.Logic.PLNMapleCourtDemo.fullDay_laundryFree spec aptP bldP⟩

open Mettapedia.Logic.PLNMapleCourtDemo in
/-- Bridge: reflected (2,0) = real extractor elevatorNormal output. -/
theorem bridge_elevatorNormal (spec aptP bldP) :
    dirToBin refl_elevator 0 = ⟨2, 0⟩ ∧
    mapleCourtEvidence spec aptP bldP fullDay (.elevatorInState 0) = ⟨2, 0⟩ :=
  ⟨by decide, Mettapedia.Logic.PLNMapleCourtDemo.fullDay_elevatorNormal spec aptP bldP⟩

open Mettapedia.Logic.PLNMapleCourtDemo in
/-- Bridge: reflected (0,2) = real extractor elevatorSlow output. -/
theorem bridge_elevatorSlow (spec aptP bldP) :
    dirToBin refl_elevator 1 = ⟨0, 2⟩ ∧
    mapleCourtEvidence spec aptP bldP fullDay (.elevatorInState 1) = ⟨0, 2⟩ :=
  ⟨by decide, Mettapedia.Logic.PLNMapleCourtDemo.fullDay_elevatorSlow spec aptP bldP⟩

/-! ## §3: Negative Examples (Discrimination Tests)

Each theorem proves a plausible-but-wrong value is rejected.
These catch overfitting: a trivial checker that accepts everything
would fail these tests. -/

/-- Room occupied is NOT (3,1) — off by one from correct (4,0). -/
theorem neg_roomOccupied_not_3_1 : refl_roomOccupied ≠ ⟨3, 1⟩ := by decide

/-- Laundry free is NOT (2,0) — wrong projection (would mean 2 free, 0 other). -/
theorem neg_laundryFree_not_2_0 : dirToBin refl_laundry 0 ≠ ⟨2, 0⟩ := by decide

/-- Elevator normal is NOT (1,1) — would mean one failure observed. -/
theorem neg_elevatorNormal_not_1_1 : dirToBin refl_elevator 0 ≠ ⟨1, 1⟩ := by decide

/-- Strength of laundry free is NOT (1,1) — it's (1,2) since total=2. -/
theorem neg_strength_laundryFree_not_1_1 :
    strength (dirToBin refl_laundry 0) ≠ (1, 1) := by decide

/-- Laundry full is NOT (1,1) — no full observations, so it's (0,2). -/
theorem neg_laundryFull_not_1_1 : dirToBin refl_laundry 2 ≠ ⟨1, 1⟩ := by decide

/-- Pipe leak is NOT (0,1) — one leak was detected, not zero. -/
theorem neg_pipeLeak_not_0_1 : refl_pipeLeak ≠ ⟨0, 1⟩ := by decide

/-! ## Summary

### Theorem counts (verified by `grep -c "^theorem"`)
- 22 positive conformance (§1): 3 binary + 2 krev + 6 dirToBin + 9 strength + 2 compositionality
- 5 bridge theorems (§2): reflected model ↔ real `mapleCourtEvidence` extractor
- 6 negative examples (§3): plausible-but-wrong values rejected
- **Total: 33 theorems**

### Three-layer coherence
- **Reflected model** (§1): `BinEvN`/`KEv3N` arithmetic, kernel-checked via `decide`
- **Real extractor** (§2): `mapleCourtEvidence` from `PLNMapleCourtDemo.lean`,
  proved via `simp + norm_num` (also kernel-checked)
- **PeTTa runtime**: `maple_court_full_profile.metta`, 20+ assertions, all pass

The bridge theorems (§2) prove both sides produce the same concrete
values.  The negative examples (§3) prove the checker discriminates.

No `native_decide`.  No `sorry`. -/

end Mettapedia.Conformance.MapleCourtEvidenceConformance
