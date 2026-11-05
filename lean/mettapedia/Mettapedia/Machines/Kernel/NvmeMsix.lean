import Mathlib.Tactic

/-!
# Kernel-owned NVMe MSI-X routing

An independent finite model of the capability/table checks used before the
current kernel enables vector 34.  The PCI configuration and BAR readback are
native evidence; this model captures the admitted planning law.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.NvmeMsix

structure Capability where
  offset : Nat
  id : Nat
  entries : Nat
  tableBir : Nat
  tableOffset : Nat
  pbaBir : Nat
  pbaOffset : Nat
  retainedConfig : Nat
  deriving DecidableEq, Repr

structure Plan where
  capabilityOffset : Nat
  tableOffset : Nat
  pbaOffset : Nat
  entries : Nat
  vector : Nat
  destination : Nat
  retainedConfig : Nat
  maskedFirst : Bool
  enabledLast : Bool
  deriving DecidableEq, Repr

def makePlan (capability : Capability) (barLength vector destination : Nat) : Option Plan :=
  if capability.offset < 0x40 ∨ capability.offset % 4 ≠ 0 ∨ capability.id ≠ 0x11 then none
  else if capability.entries = 0 ∨ vector < 32 ∨ vector = 0xff then none
  else if capability.tableBir ≠ 0 ∨ capability.pbaBir ≠ 0 then none
  else if capability.tableOffset + 16 > barLength ∨ capability.pbaOffset + 8 > barLength then none
  else some (Plan.mk capability.offset capability.tableOffset capability.pbaOffset
    capability.entries vector destination capability.retainedConfig true true)

theorem accepted_preserves_capability {capability : Capability} {barLength vector destination : Nat}
    {plan : Plan} (accepted : makePlan capability barLength vector destination = some plan) :
    plan.capabilityOffset = capability.offset ∧ plan.entries = capability.entries ∧
      plan.retainedConfig = capability.retainedConfig := by
  unfold makePlan at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  simp only [Option.some.injEq] at accepted
  subst plan
  simp

theorem accepted_is_staged {capability : Capability} {barLength vector destination : Nat}
    {plan : Plan} (accepted : makePlan capability barLength vector destination = some plan) :
    plan.maskedFirst = true ∧ plan.enabledLast = true := by
  unfold makePlan at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  simp only [Option.some.injEq] at accepted
  subst plan
  simp

def qemuCapability : Capability :=
  Capability.mk 0x40 0x11 65 0 0x2000 0 0x3000 0x00408011

def qemuPlan : Plan :=
  Plan.mk 0x40 0x2000 0x3000 65 0x22 0 0x00408011 true true

theorem qemu_fixture_accepted : makePlan qemuCapability 0x4000 0x22 0 = some qemuPlan := by
  rfl

theorem wrong_bar_refused :
    makePlan { qemuCapability with tableBir := 1 } 0x4000 0x22 0 = none := by
  rfl

theorem out_of_bounds_refused :
    makePlan { qemuCapability with tableOffset := 0x4000 } 0x4000 0x22 0 = none := by
  rfl

#print axioms accepted_preserves_capability
#print axioms accepted_is_staged
#print axioms qemu_fixture_accepted

end Mettapedia.Machines.Kernel.NvmeMsix
