import Mettapedia.Logic.LP.Provenance
import Mettapedia.Logic.PLNProvenanceWMSupportBridge
import Mettapedia.Logic.PLNScopedTrackedWhichState
import Provenance.Semirings.Which

/-!
# End-to-End Derivation Tracking Demo

A worked example for the WM-PLN book (Ch 6): provenance flows through
the Maple Court humidity chain, and scoped forgetting exactly removes
one observation branch while preserving the other.

## Pipeline

1. Define a tiny LP signature (5 ground atoms, 3 rules)
2. Label two observations with `Which`-valued provenance seeds
3. Define the closures (what `T_P_K_LP` would produce)
4. Convert to `ScopedTrackedWhichState`
5. Prove exact-inverse forgetting and conservation
6. Bridge to `AdditiveWorldModel.extract`

## Design note

We define closures by hand rather than evaluating `T_P_K_LP` (which is
`noncomputable`).  The closures represent what the operator produces
after fixpoint iteration on the seeded KB.
-/

namespace Mettapedia.Logic.PLNDerivationTrackingDemo

open Mettapedia.Logic.LP
open Mettapedia.Logic.PLNWorldModelGeneric

/-! ## 1. Tiny function-free Maple Court signature -/

inductive MapleCourtRel
  | pipeLeak
  | showerRunning
  | wallHumidity
  | bathroomHumidity
  | moldRisk
  deriving DecidableEq, Fintype

abbrev MapleCourtConst := Unit
abbrev MapleCourtVar := Unit

def mapleCourtSig : LPSignature where
  constants := MapleCourtConst
  vars := MapleCourtVar
  relationSymbols := MapleCourtRel
  relationArity := fun _ => 1
  functionSymbols := PEmpty
  functionArity := PEmpty.elim

instance : IsEmpty mapleCourtSig.functionSymbols := inferInstance
instance : DecidableEq mapleCourtSig.constants := inferInstance
instance : DecidableEq mapleCourtSig.vars := inferInstance
instance : DecidableEq mapleCourtSig.relationSymbols := inferInstance
instance : Fintype mapleCourtSig.constants := inferInstance
instance : Fintype mapleCourtSig.vars := inferInstance

/-- Named ground atoms (all unary, applied to the single constant `()`). -/
def pipeLeak₁ : GroundAtom mapleCourtSig := GroundAtom.ofFinArgs .pipeLeak (fun _ => ())
def showerRunning₁ : GroundAtom mapleCourtSig := GroundAtom.ofFinArgs .showerRunning (fun _ => ())
def wallHumidity₁ : GroundAtom mapleCourtSig := GroundAtom.ofFinArgs .wallHumidity (fun _ => ())
def bathroomHumidity₁ : GroundAtom mapleCourtSig := GroundAtom.ofFinArgs .bathroomHumidity (fun _ => ())
def moldRisk₁ : GroundAtom mapleCourtSig := GroundAtom.ofFinArgs .moldRisk (fun _ => ())

/-- Ground atoms with distinct relation symbols are distinct. -/
theorem atoms_ne_of_rel_ne {r₁ r₂ : MapleCourtRel} (h : r₁ ≠ r₂) :
    GroundAtom.ofFinArgs r₁ (fun _ : Fin 1 => ((): mapleCourtSig.constants)) ≠
    GroundAtom.ofFinArgs r₂ (fun _ => ()) := by
  intro heq; exact h (congrArg GroundAtom.symbol heq)

/-! ## 2. Observation seeds as Which-valued KRelations -/

def oPipe : Fin 2 := 0
def oShower : Fin 2 := 1

def pipeProv : Which (Fin 2) := Which.wset {oPipe}
def showerProv : Which (Fin 2) := Which.wset {oShower}

/-- Pipe seed: only `pipeLeak₁` carries provenance `{oPipe}`. -/
def pipeSeed : KRelation mapleCourtSig (Which (Fin 2)) :=
  fun a => if a = pipeLeak₁ then pipeProv else 0

/-- Shower seed: only `showerRunning₁` carries provenance `{oShower}`. -/
def showerSeed : KRelation mapleCourtSig (Which (Fin 2)) :=
  fun a => if a = showerRunning₁ then showerProv else 0

/-! ## 3. Closures (hand-defined fixpoints)

These represent what `T_P_K_LP` would produce after iterating on the
seeded KB.  The chain PipeLeak → WallHumidity → MoldRisk propagates
the pipe provenance; ShowerRunning → BathroomHumidity propagates
the shower provenance. -/

/-- Pipe closure: PipeLeak, WallHumidity, MoldRisk all carry `{oPipe}`. -/
def pipeClosure : KRelation mapleCourtSig (Which (Fin 2)) :=
  fun a =>
    if a = pipeLeak₁ then pipeProv
    else if a = wallHumidity₁ then pipeProv
    else if a = moldRisk₁ then pipeProv
    else 0

/-- Shower closure: ShowerRunning, BathroomHumidity carry `{oShower}`. -/
def showerClosure : KRelation mapleCourtSig (Which (Fin 2)) :=
  fun a =>
    if a = showerRunning₁ then showerProv
    else if a = bathroomHumidity₁ then showerProv
    else 0

/-- Full state: union of both observation branches. -/
def fullState : KRelation mapleCourtSig (Which (Fin 2)) :=
  pipeClosure + showerClosure

/-! ## 4. Provenance flow theorems -/


-- All atom inequalities as @[simp] lemmas (both directions)
@[simp] theorem ne_pl_sr : pipeLeak₁ ≠ showerRunning₁ := atoms_ne_of_rel_ne (by decide)
@[simp] theorem ne_sr_pl : showerRunning₁ ≠ pipeLeak₁ := ne_pl_sr.symm
@[simp] theorem ne_pl_wh : pipeLeak₁ ≠ wallHumidity₁ := atoms_ne_of_rel_ne (by decide)
@[simp] theorem ne_wh_pl : wallHumidity₁ ≠ pipeLeak₁ := ne_pl_wh.symm
@[simp] theorem ne_pl_bh : pipeLeak₁ ≠ bathroomHumidity₁ := atoms_ne_of_rel_ne (by decide)
@[simp] theorem ne_bh_pl : bathroomHumidity₁ ≠ pipeLeak₁ := ne_pl_bh.symm
@[simp] theorem ne_pl_mr : pipeLeak₁ ≠ moldRisk₁ := atoms_ne_of_rel_ne (by decide)
@[simp] theorem ne_mr_pl : moldRisk₁ ≠ pipeLeak₁ := ne_pl_mr.symm
@[simp] theorem ne_sr_wh : showerRunning₁ ≠ wallHumidity₁ := atoms_ne_of_rel_ne (by decide)
@[simp] theorem ne_wh_sr : wallHumidity₁ ≠ showerRunning₁ := ne_sr_wh.symm
@[simp] theorem ne_sr_bh : showerRunning₁ ≠ bathroomHumidity₁ := atoms_ne_of_rel_ne (by decide)
@[simp] theorem ne_bh_sr : bathroomHumidity₁ ≠ showerRunning₁ := ne_sr_bh.symm
@[simp] theorem ne_sr_mr : showerRunning₁ ≠ moldRisk₁ := atoms_ne_of_rel_ne (by decide)
@[simp] theorem ne_mr_sr : moldRisk₁ ≠ showerRunning₁ := ne_sr_mr.symm
@[simp] theorem ne_wh_bh : wallHumidity₁ ≠ bathroomHumidity₁ := atoms_ne_of_rel_ne (by decide)
@[simp] theorem ne_bh_wh : bathroomHumidity₁ ≠ wallHumidity₁ := ne_wh_bh.symm
@[simp] theorem ne_wh_mr : wallHumidity₁ ≠ moldRisk₁ := atoms_ne_of_rel_ne (by decide)
@[simp] theorem ne_mr_wh : moldRisk₁ ≠ wallHumidity₁ := ne_wh_mr.symm
@[simp] theorem ne_bh_mr : bathroomHumidity₁ ≠ moldRisk₁ := atoms_ne_of_rel_ne (by decide)
@[simp] theorem ne_mr_bh : moldRisk₁ ≠ bathroomHumidity₁ := ne_bh_mr.symm

/-- Mold risk is traced to the pipe observation. -/
theorem fullState_moldRisk : fullState moldRisk₁ = pipeProv := by
  simp [fullState, pipeClosure, showerClosure, Pi.add_apply]

/-- Bathroom humidity is traced to the shower observation. -/
theorem fullState_bathroomHumidity : fullState bathroomHumidity₁ = showerProv := by
  simp [fullState, pipeClosure, showerClosure, Pi.add_apply]

/-- Shower closure has no mold risk (only pipe chain derives it). -/
theorem showerClosure_moldRisk_zero : showerClosure moldRisk₁ = 0 := by
  simp [showerClosure]

/-- Pipe closure has no bathroom humidity (only shower derives it). -/
theorem pipeClosure_bathroomHumidity_zero : pipeClosure bathroomHumidity₁ = 0 := by
  simp [pipeClosure]

/-! ## 5. WM Extraction Bridge -/

/-- WM extraction from the full state: mold risk carries pipe provenance. -/
theorem extract_fullState_moldRisk :
    AdditiveWorldModel.extract (State := KRelation mapleCourtSig (Which (Fin 2)))
      fullState moldRisk₁ = pipeProv :=
  fullState_moldRisk

/-- WM extraction: bathroom humidity carries shower provenance. -/
theorem extract_fullState_bathroomHumidity :
    AdditiveWorldModel.extract (State := KRelation mapleCourtSig (Which (Fin 2)))
      fullState bathroomHumidity₁ = showerProv :=
  fullState_bathroomHumidity

/-! ## 6. Scoped tracking and forgetting -/

def sPipe : Fin 2 := 0
def sShower : Fin 2 := 1
def scopePipe : Finset (Fin 2) := {sPipe}
def scopeShower : Finset (Fin 2) := {sShower}

def scopedPipe : ScopedTrackedWhichState mapleCourtSig 2 2 :=
  toScopedTrackedWhichState (σ := mapleCourtSig) (n := 2) (m := 2) sPipe pipeClosure

def scopedShower : ScopedTrackedWhichState mapleCourtSig 2 2 :=
  toScopedTrackedWhichState (σ := mapleCourtSig) (n := 2) (m := 2) sShower showerClosure

def scopedFull : ScopedTrackedWhichState mapleCourtSig 2 2 :=
  scopedPipe + scopedShower

/-- Shower scope is clean w.r.t. pipe scope: shower chunks carry scope 1, not 0. -/
private theorem scopeClean_shower_pipe :
    ScopeClean (σ := mapleCourtSig) (n := 2) (m := 2) scopedShower scopePipe := by
  intro q chunk hchunk
  unfold scopedShower toScopedTrackedWhichState at hchunk
  cases h : showerClosure q with
  | wbot => simp [h] at hchunk
  | wset s =>
    simp [h] at hchunk; rcases hchunk with rfl
    simp [scopePipe, sPipe, sShower]

/-- Pipe scope is clean w.r.t. shower scope: pipe chunks carry scope 0, not 1. -/
private theorem scopeClean_pipe_shower :
    ScopeClean (σ := mapleCourtSig) (n := 2) (m := 2) scopedPipe scopeShower := by
  intro q chunk hchunk
  unfold scopedPipe toScopedTrackedWhichState at hchunk
  cases h : pipeClosure q with
  | wbot => simp [h] at hchunk
  | wset s =>
    simp [h] at hchunk; rcases hchunk with rfl
    simp [scopeShower, sPipe, sShower]

/-- Forgetting the pipe scope removes the pipe branch, leaving only shower. -/
theorem forget_pipe_scope :
    forgetScopedByScope scopePipe scopedFull = scopedShower := by
  unfold scopedFull
  rw [add_comm]
  exact forgetScopedByScope_exactInverse_of_supported_of_clean
    (σ := mapleCourtSig) (n := 2) (m := 2)
    scopedShower scopedPipe
    scopeClean_shower_pipe
    (toScopedTrackedWhichState_supportedInSingleton
      (σ := mapleCourtSig) (n := 2) (m := 2) sPipe pipeClosure)

/-- Forgetting the shower scope removes the shower branch, leaving only pipe. -/
theorem forget_shower_scope :
    forgetScopedByScope scopeShower scopedFull = scopedPipe := by
  unfold scopedFull
  exact forgetScopedByScope_exactInverse_of_supported_of_clean
    (σ := mapleCourtSig) (n := 2) (m := 2)
    scopedPipe scopedShower
    scopeClean_pipe_shower
    (toScopedTrackedWhichState_supportedInSingleton
      (σ := mapleCourtSig) (n := 2) (m := 2) sShower showerClosure)

/-! ## 7. Conservation: forget-after-remember = identity -/

/-- Forgetting the pipe branch immediately after adding it back recovers
    the shower-only base state. -/
theorem forget_after_remember_pipe :
    forgetScopedByScope scopePipe (scopedShower + scopedPipe) = scopedShower := by
  rw [add_comm]; exact forget_pipe_scope

/-- Forgetting the shower branch immediately after adding it back recovers
    the pipe-only base state. -/
theorem forget_after_remember_shower :
    forgetScopedByScope scopeShower (scopedPipe + scopedShower) = scopedPipe :=
  forget_shower_scope

/-! ## Summary -/

/-- End-to-end derivation tracking: provenance flows correctly through
    the Maple Court humidity chain, and forgetting is exact.

    This is suitable as a book listing for Ch 6. -/
theorem end_to_end :
    -- Provenance flows correctly
    fullState moldRisk₁ = pipeProv ∧
    fullState bathroomHumidity₁ = showerProv ∧
    -- Shower doesn't derive mold risk
    showerClosure moldRisk₁ = 0 ∧
    -- Pipe doesn't derive bathroom humidity
    pipeClosure bathroomHumidity₁ = 0 ∧
    -- Forgetting is exact (pipe)
    forgetScopedByScope scopePipe scopedFull = scopedShower ∧
    -- Forgetting is exact (shower)
    forgetScopedByScope scopeShower scopedFull = scopedPipe :=
  ⟨fullState_moldRisk, fullState_bathroomHumidity,
   showerClosure_moldRisk_zero, pipeClosure_bathroomHumidity_zero,
   forget_pipe_scope, forget_shower_scope⟩

end Mettapedia.Logic.PLNDerivationTrackingDemo
