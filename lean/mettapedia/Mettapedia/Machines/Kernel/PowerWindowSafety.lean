/-
  PowerWindowSafety.lean — Machine-checked invariants for SexOS SYS_POWER (syscall 84),
  firmware-window hardware isolation, laptop battery/thermal safety policies, and
  ring-3 AML work-budget termination.
-/
namespace Mettapedia.Machines.Kernel.PowerWindowSafety

/-! ### 1. Firmware Window Reserved I/O Port Isolation -/

def rangesOverlap (a b lo hi : Nat) : Bool :=
  decide (a < hi ∧ b > lo)

def portReserved (port width : Nat) : Bool :=
  let w := if width > 0 then width else 1
  let b := port + w
  rangesOverlap port b 0x20 0x22 ||
  rangesOverlap port b 0xA0 0xA2 ||
  rangesOverlap port b 0x40 0x44 ||
  rangesOverlap port b 0xCF8 0xD00 ||
  rangesOverlap port b 0x60 0x61 ||
  rangesOverlap port b 0x64 0x65 ||
  rangesOverlap port b 0x3F8 0x400

theorem port_reserved_blocks_pci_config (port width p : Nat)
    (hw : width > 0) (hp1 : port ≤ p) (hp2 : p < port + width)
    (hlo : 0xCF8 ≤ p) (hhi : p < 0xD00) :
    portReserved port width = true := by
  unfold portReserved rangesOverlap
  simp [hw]
  have h1 : port < 0xD00 := by omega
  have h2 : port + width > 0xCF8 := by omega
  simp [h1, h2]

theorem port_reserved_blocks_serial_com1 (port width p : Nat)
    (hw : width > 0) (hp1 : port ≤ p) (hp2 : p < port + width)
    (hlo : 0x3F8 ≤ p) (hhi : p < 0x400) :
    portReserved port width = true := by
  unfold portReserved rangesOverlap
  simp [hw]
  have h1 : port < 0x400 := by omega
  have h2 : port + width > 0x3F8 := by omega
  simp [h1, h2]

theorem port_reserved_allows_ec_ports :
    portReserved 0x62 1 = false ∧ portReserved 0x66 1 = false := by
  decide

/-! ### 2. Firmware Window PCI BAR / Expansion ROM Write Protection -/

def pciWriteReserved (offset width : Nat) : Bool :=
  let w := if width > 0 then width else 1
  let b := offset + w
  rangesOverlap offset b 0x10 0x28 || rangesOverlap offset b 0x30 0x34

theorem pci_write_blocks_any_bar_byte (offset width byteOff : Nat)
    (hw : width > 0) (h1 : offset ≤ byteOff) (h2 : byteOff < offset + width)
    (hbar1 : 0x10 ≤ byteOff) (hbar2 : byteOff < 0x28) :
    pciWriteReserved offset width = true := by
  unfold pciWriteReserved rangesOverlap
  simp [hw]
  left
  omega

theorem pci_write_blocks_expansion_rom (offset width byteOff : Nat)
    (hw : width > 0) (h1 : offset ≤ byteOff) (h2 : byteOff < offset + width)
    (hrom1 : 0x30 ≤ byteOff) (hrom2 : byteOff < 0x34) :
    pciWriteReserved offset width = true := by
  unfold pciWriteReserved rangesOverlap
  simp [hw]
  right
  omega

/-! ### 3. Battery & Thermal Critical Shutdown Safety Policies -/

structure BatteryReading where
  percent : Nat
  charging : Bool
  discharging : Bool
  critical : Bool

def mustShutDownBattery (r : BatteryReading) (hasAc onAc : Bool) : Bool :=
  !(hasAc && onAc) && !r.charging && r.discharging && (r.critical || decide (r.percent ≤ 2))

theorem battery_never_shuts_down_on_ac (r : BatteryReading) :
    mustShutDownBattery r true true = false := by
  simp [mustShutDownBattery]

theorem battery_never_shuts_down_while_charging (r : BatteryReading) (hasAc onAc : Bool)
    (hchg : r.charging = true) :
    mustShutDownBattery r hasAc onAc = false := by
  simp [mustShutDownBattery, hchg]

def thermalPlausible (dk : Nat) : Bool :=
  decide (2232 ≤ dk ∧ dk ≤ 4732)

def thermalCritical (temp crt : Option Nat) : Bool :=
  match temp, crt with
  | some t, some c => thermalPlausible t && thermalPlausible c && decide (t ≥ c)
  | _, _ => false

theorem thermal_placeholder_never_trips (crt : Option Nat) :
    thermalCritical (some 0xFFFFFFFF) crt = false := by
  cases crt <;> simp [thermalCritical, thermalPlausible]

/-! ### 4. Ring-3 AML Work-Budget Strict Termination -/

def spendBudget (budget cost : Nat) : Option Nat :=
  if budget < cost then none else some (budget - cost)

theorem aml_spend_positive_strictly_decreases (budget cost next : Nat)
    (hcost : cost > 0) (hstep : spendBudget budget cost = some next) :
    next < budget := by
  unfold spendBudget at hstep
  split at hstep
  · cases hstep
  · injection hstep with hnext
    omega

#print axioms port_reserved_blocks_pci_config
#print axioms port_reserved_blocks_serial_com1
#print axioms port_reserved_allows_ec_ports
#print axioms pci_write_blocks_any_bar_byte
#print axioms pci_write_blocks_expansion_rom
#print axioms battery_never_shuts_down_on_ac
#print axioms battery_never_shuts_down_while_charging
#print axioms thermal_placeholder_never_trips
#print axioms aml_spend_positive_strictly_decreases

end Mettapedia.Machines.Kernel.PowerWindowSafety
