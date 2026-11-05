import Mathlib.Tactic

/-!
# Per-domain x86 floating-point context custody

The processor owns one live floating-point image while each inactive domain
owns one saved image.  A switch saves the departing image before restoring the
arriving image.  The native `FXSAVE64`/`FXRSTOR64` instructions, interrupt
entry assembly and compiler ABI remain separate conformance boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.FpuContext

/-- The architecturally relevant part of one x86-64 `FXSAVE64` image. -/
structure Image where
  xmm : Fin 16 → UInt64 × UInt64
  mxcsr : UInt32
  x87Control : UInt16

/-- Saved domain images plus the processor's currently live image. -/
structure State (Domain : Type) where
  saved : Domain → Image
  cpuOwner : Option Domain
  cpu : Image

variable {Domain : Type}

/-- Record the live processor image as the departing domain's saved image. -/
def save [DecidableEq Domain] (state : State Domain) (owner : Domain) : State Domain :=
  { state with saved := Function.update state.saved owner state.cpu }

/-- Load an inactive domain's saved image and make that domain the live owner. -/
def restore (state : State Domain) (next : Domain) : State Domain :=
  { state with cpuOwner := some next, cpu := state.saved next }

/-- A domain changes only the live processor image while it is running. -/
def execute (state : State Domain) (image : Image) : State Domain :=
  { state with cpu := image }

/-- The eager switch used by the current single-core scheduler. -/
def switch [DecidableEq Domain]
    (state : State Domain) (departing arriving : Domain) : State Domain :=
  restore (save state departing) arriving

theorem save_records_exact [DecidableEq Domain] (state : State Domain) (owner : Domain) :
    (save state owner).saved owner = state.cpu := by
  simp [save]

theorem save_preserves_other [DecidableEq Domain] (state : State Domain)
    {owner other : Domain} (different : other ≠ owner) :
    (save state owner).saved other = state.saved other := by
  simp [save, different]

theorem save_preserves_live [DecidableEq Domain] (state : State Domain) (owner : Domain) :
    (save state owner).cpu = state.cpu ∧
      (save state owner).cpuOwner = state.cpuOwner := by
  exact ⟨rfl, rfl⟩

theorem restore_loads_exact (state : State Domain) (next : Domain) :
    (restore state next).cpu = state.saved next := by
  rfl

theorem restore_names_owner (state : State Domain) (next : Domain) :
    (restore state next).cpuOwner = some next := by
  rfl

theorem restore_preserves_saved (state : State Domain) (next other : Domain) :
    (restore state next).saved other = state.saved other := by
  rfl

theorem switch_records_departing [DecidableEq Domain] (state : State Domain)
    (departing arriving : Domain) :
    (switch state departing arriving).saved departing = state.cpu := by
  simp [switch, restore, save]

theorem switch_loads_arriving [DecidableEq Domain] (state : State Domain)
    {departing arriving : Domain} (different : arriving ≠ departing) :
    (switch state departing arriving).cpu = state.saved arriving := by
  simp [switch, restore, save, different]

theorem switch_names_arriving [DecidableEq Domain] (state : State Domain)
    (departing arriving : Domain) :
    (switch state departing arriving).cpuOwner = some arriving := by
  rfl

theorem switch_preserves_third [DecidableEq Domain] (state : State Domain)
    {departing other : Domain} (different : other ≠ departing) (arriving : Domain) :
    (switch state departing arriving).saved other = state.saved other := by
  simp [switch, restore, save, different]

theorem same_domain_switch_preserves_live [DecidableEq Domain] (state : State Domain)
    (domain : Domain) :
    (switch state domain domain).cpu = state.cpu := by
  simp [switch, restore, save]

/-- After another domain runs, switching back restores the first image exactly. -/
theorem roundTrip_restores_exact [DecidableEq Domain] (state : State Domain)
    {first second : Domain} (different : first ≠ second) (secondImage : Image) :
    (switch (execute (switch state first second) secondImage) second first).cpu = state.cpu := by
  simp [switch, execute, restore, save, different]

/-- The intervening domain's changed image is retained for its next turn. -/
theorem roundTrip_records_intervening [DecidableEq Domain] (state : State Domain)
    {first second : Domain} (secondImage : Image) :
    (switch (execute (switch state first second) secondImage) second first).saved second =
      secondImage := by
  simp [switch, execute, restore, save]

/-- A third domain's saved image is framed across a complete round trip. -/
theorem roundTrip_preserves_third [DecidableEq Domain] (state : State Domain)
    {first second third : Domain} (thirdFirst : third ≠ first)
    (thirdSecond : third ≠ second) (secondImage : Image) :
    (switch (execute (switch state first second) secondImage) second first).saved third =
      state.saved third := by
  simp [switch, execute, restore, save, thirdFirst, thirdSecond]

end Mettapedia.Machines.Kernel.FpuContext
