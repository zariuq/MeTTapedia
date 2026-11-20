import Mathlib.Tactic

/-!
# PCIe Device Power Management Invariants

Clean mathematical specification of the core invariants in `sex-pcipm` and kernel
device power management (`D0 <-> D3hot`, add-only ASPM/L1SS policy, L1.2 LTR threshold
rounding, and PME_Status W1C safety):

1. **Add-only, quirk-safe, idempotent ASPM policy** (`BitVec 8`): firmware-enabled
   states are never cleared, disallowed/quirked/unsupported states are never newly
   enabled, and a second policy pass is strictly idempotent.
2. **L1.2 LTR threshold rounding soundness**: encoding a microsecond threshold into
   `(scale, value)` (`32^scale` ns) via ceiling division never under-approximates the
   guarded exit latency.
3. **D0 ↔ D3hot snapshot conservation**: `D0 -> D3hot` captures a `D0` config snapshot;
   repeated `D3hot -> D3hot` never clobbers the saved `D0` snapshot (preserving MSI-X /
   BARs); `D3hot -> D0` restores the exact `D0` snapshot regardless of `No_Soft_Reset`.
4. **PME_Status W1C preservation** (`BitVec 32`): writing `PMCSR` clears the
   write-one-to-clear `PME_Status` bit (bit 15) so hardware wake status is never
   spuriously wiped.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.DevicePower

/-- 8-bit bitmask of PCIe link power states (`L0s, L1, ASPM L1.1/L1.2, PCI-PM L1.1/L1.2, CLKPM`). -/
abbrev StateMask := BitVec 8

/-- Add-only link power policy: keeps everything firmware enabled (`before`), and adds
only states that are simultaneously hardware-capable, allowed by policy, not forbidden
by FADT, and not blocked by device quirks. -/
def applyLinkPolicy (before capable policy quirk : StateMask) (fadtNoAspm : Bool) : StateMask :=
  if fadtNoAspm then before
  else before ||| ((capable &&& policy) &&& (~~~quirk))

/-- Theorem 1 (Add-only): Every state bit already enabled by firmware stays enabled. -/
theorem linkPolicy_preserves_firmware
    (before capable policy quirk : StateMask) (fadtNoAspm : Bool) (i : Nat)
    (hBefore : before.getLsbD i = true) :
    (applyLinkPolicy before capable policy quirk fadtNoAspm).getLsbD i = true := by
  unfold applyLinkPolicy
  cases fadtNoAspm
  · simp [hBefore]
  · exact hBefore

/-- Theorem 2 (FADT no-ASPM): When FADT forbids OS ASPM changes, the link state is
unchanged. -/
theorem linkPolicy_fadt_forbidden_unchanged
    (before capable policy quirk : StateMask) :
    applyLinkPolicy before capable policy quirk true = before := rfl

/-- Theorem 3 (Idempotence): Running the link power policy a second time changes
nothing. -/
theorem linkPolicy_idempotent
    (before capable policy quirk : StateMask) (fadtNoAspm : Bool) :
    applyLinkPolicy (applyLinkPolicy before capable policy quirk fadtNoAspm)
      capable policy quirk fadtNoAspm =
    applyLinkPolicy before capable policy quirk fadtNoAspm := by
  unfold applyLinkPolicy
  cases fadtNoAspm
  · ext i hi
    simp
  · rfl

/-- Theorem 4 (No forbidden or quirked additions): Any newly added state bit (not in
`before`) must be supported by `capable`, permitted by `policy`, not blocked by `quirk`,
and FADT must permit OS ASPM. -/
theorem linkPolicy_new_bits_safe
    (before capable policy quirk : StateMask) (fadtNoAspm : Bool) (i : Nat) (hi : i < 8)
    (hNotBefore : before.getLsbD i = false)
    (hAfter : (applyLinkPolicy before capable policy quirk fadtNoAspm).getLsbD i = true) :
    fadtNoAspm = false ∧ capable.getLsbD i = true ∧
      policy.getLsbD i = true ∧ quirk.getLsbD i = false := by
  cases fadtNoAspm
  · simp only [applyLinkPolicy, Bool.false_eq_true, ↓reduceIte,
      BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      hNotBefore, Bool.false_or, hi, decide_true, Bool.true_and] at hAfter
    cases hc : capable.getLsbD i <;> cases hp : policy.getLsbD i <;>
      cases hq : quirk.getLsbD i <;> simp_all
  · simp [applyLinkPolicy, hNotBefore] at hAfter

/-- Scale multiplier in nanoseconds for PCIe LTR_L1.2_THRESHOLD scale `s ∈ {0..5}`:
`32^s = 2^(5*s)` ns. -/
def ltrScaleNs (scale : Nat) : Nat := 32 ^ scale

/-- Round-up quotient `ceil(ns / unit)` for `unit > 0`. -/
def ceilDiv (ns unit : Nat) : Nat := (ns + unit - 1) / unit

/-- Encoded threshold nanoseconds for `(scale, value)`. -/
def ltrThresholdNs (scale value : Nat) : Nat := value * ltrScaleNs scale

/-- Theorem 5 (L1.2 Threshold Rounding Soundness): For any scale `s` and target time
`targetNs`, rounding up via `ceilDiv` produces a threshold at least `targetNs`, so
hardware never enters L1.2 with a threshold shorter than the guarded exit latency. -/
theorem ltr_ceil_never_underestimates (scale targetNs : Nat) :
    targetNs ≤ ltrThresholdNs scale (ceilDiv targetNs (ltrScaleNs scale)) := by
  unfold ltrThresholdNs ceilDiv ltrScaleNs
  have hPos : 0 < 32 ^ scale := by positivity
  have hDiv := Nat.div_add_mod (targetNs + 32 ^ scale - 1) (32 ^ scale)
  have hMod : (targetNs + 32 ^ scale - 1) % (32 ^ scale) < 32 ^ scale :=
    Nat.mod_lt _ hPos
  have hMul : ((targetNs + 32 ^ scale - 1) / 32 ^ scale) * 32 ^ scale =
      32 ^ scale * ((targetNs + 32 ^ scale - 1) / 32 ^ scale) := Nat.mul_comm _ _
  omega

/-- Simplified PCIe power state (`D0` active, `D3hot` low-power). -/
inductive DState where
  | d0
  | d3hot
  deriving DecidableEq, Repr

/-- Abstract hardware + saved-snapshot model for one leased PCIe function. -/
structure FunctionPm (Cfg : Type) where
  state : DState
  liveCfg : Cfg
  resetCfg : Cfg
  noSoftReset : Bool
  saved : Option Cfg
  deriving DecidableEq, Repr

/-- Hardware + driver transition matching `sex_pcipm::pm::set_state`:
- `D0 -> D3hot` saves `liveCfg` into `saved`, and if `!noSoftReset` hardware loses live config.
- `D3hot -> D3hot` is a no-op that preserves `saved` (never overwrites snapshot with `resetCfg`).
- `D3hot -> D0` restores `saved` when `!noSoftReset`. -/
def transitionPm {Cfg : Type} (f : FunctionPm Cfg) (target : DState) : FunctionPm Cfg :=
  if f.state = target then f
  else match f.state, target with
  | .d0, .d3hot =>
      { f with
        state := .d3hot
        liveCfg := if f.noSoftReset then f.liveCfg else f.resetCfg
        saved := some f.liveCfg }
  | .d3hot, .d0 =>
      let restored := if f.noSoftReset then f.liveCfg else f.saved.getD f.liveCfg
      { f with state := .d0, liveCfg := restored }
  | _, _ => f

/-- Theorem 6 (Repeated D3hot preserves original D0 snapshot): Transitioning an already
`D3hot` function to `D3hot` again does not clobber the saved `D0` configuration/MSI-X
snapshot. -/
theorem repeated_d3hot_preserves_snapshot {Cfg : Type} (f : FunctionPm Cfg)
    (hD0 : f.state = .d0) :
    let f1 := transitionPm f .d3hot
    let f2 := transitionPm f1 .d3hot
    f2.saved = some f.liveCfg ∧ f2 = f1 := by
  dsimp only
  have h1 : transitionPm f .d3hot =
      { f with
        state := .d3hot
        liveCfg := if f.noSoftReset then f.liveCfg else f.resetCfg
        saved := some f.liveCfg } := by
    simp [transitionPm, hD0]
  rw [h1]
  simp [transitionPm]

/-- Theorem 7 (D0 -> D3hot -> D0 round-trip exact restoration): Starting in `D0`,
moving to `D3hot` (even repeatedly) and returning to `D0` always restores the exact
original `D0` configuration, whether `No_Soft_Reset` is set or clear. -/
theorem d0_d3hot_d0_roundtrip_restores_cfg {Cfg : Type} (f : FunctionPm Cfg)
    (hD0 : f.state = .d0) :
    let fDown := transitionPm (transitionPm f .d3hot) .d3hot
    let fUp := transitionPm fDown .d0
    fUp.state = .d0 ∧ fUp.liveCfg = f.liveCfg := by
  dsimp only
  have hDown : transitionPm (transitionPm f .d3hot) .d3hot =
      { f with
        state := .d3hot
        liveCfg := if f.noSoftReset then f.liveCfg else f.resetCfg
        saved := some f.liveCfg } := by
    simp [transitionPm, hD0]
  rw [hDown]
  cases f.noSoftReset <;> simp [transitionPm]

/-- PMCSR 32-bit write value: clears bits 1:0 (power state) and bit 15 (`PME_Status`, W1C)
before OR-ing the target state `toState &&& 3`. -/
def pmcsrWriteValue (csr toState : BitVec 32) : BitVec 32 :=
  (csr &&& ~~~(3#32 ||| (1#32 <<< 15))) ||| (toState &&& 3#32)

/-- Theorem 8 (PME_Status W1C safety): `pmcsrWriteValue` never sets bit 15 (`PME_Status`),
so D-state transitions never spuriously clear a latched hardware wake event. -/
theorem pmcsr_write_never_sets_pme_status (csr toState : BitVec 32) :
    (pmcsrWriteValue csr toState).getLsbD 15 = false := by
  unfold pmcsrWriteValue
  simp

#print axioms linkPolicy_preserves_firmware
#print axioms linkPolicy_fadt_forbidden_unchanged
#print axioms linkPolicy_idempotent
#print axioms linkPolicy_new_bits_safe
#print axioms ltr_ceil_never_underestimates
#print axioms repeated_d3hot_preserves_snapshot
#print axioms d0_d3hot_d0_roundtrip_restores_cfg
#print axioms pmcsr_write_never_sets_pme_status

end Mettapedia.Machines.Kernel.DevicePower
