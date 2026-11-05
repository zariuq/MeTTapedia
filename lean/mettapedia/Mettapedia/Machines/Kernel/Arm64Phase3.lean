import Mathlib.Tactic

/-!
# AArch64 Phase-3 mapping and fault laws

An independent model of the finite mapping roles and four-fault EL0 smoke
sequence used by the Cesta SexOS image.  The native page-table construction
has a separate compiler/ELF qualification boundary; this file states the
role-level protection and warden laws.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.Arm64Phase3

inductive MapRole where
  | kernelText | kernelData | uart | userCode | userCode2 | userData | userStack
  | hhdmDevice | hhdmDram
  deriving DecidableEq, Repr

structure MapContract where
  role : MapRole
  va : Nat
  pa : Nat
  bytes : Nat
  el0 : Bool
  write : Bool
  execute : Bool
  device : Bool
  deriving DecidableEq, Repr

def page : Nat := 0x1000
def block2M : Nat := 0x200000
def block1G : Nat := 0x40000000
def kernelBase : Nat := 0x40080000
def uartBase : Nat := 0x09000000
def userCode : Nat := 0x00400000
def userCode2 : Nat := 0x00430000
def userData : Nat := 0x00410000
def userStack : Nat := 0x00420000
def hhdm : Nat := 0xffff800000000000
def userUnmapped : Nat := 0x50000000

def AlignedSpan (contract : MapContract) (alignment : Nat) : Prop :=
  contract.bytes ≠ 0 ∧ contract.va % alignment = 0 ∧
    contract.pa % alignment = 0 ∧ contract.bytes % alignment = 0

def Valid (contract : MapContract) : Prop :=
  match contract.role with
  | .kernelText =>
      AlignedSpan contract page ∧ contract.va = contract.pa ∧ contract.va ≥ kernelBase ∧
        contract.el0 = false ∧ contract.write = false ∧ contract.execute = true ∧
        contract.device = false
  | .kernelData =>
      AlignedSpan contract page ∧ contract.va = contract.pa ∧ contract.va ≥ kernelBase ∧
        contract.el0 = false ∧ contract.write = true ∧ contract.execute = false ∧
        contract.device = false
  | .uart =>
      AlignedSpan contract block2M ∧ contract.va = uartBase ∧ contract.pa = uartBase ∧
        contract.bytes = block2M ∧ contract.el0 = false ∧ contract.write = true ∧
        contract.execute = false ∧ contract.device = true
  | .userCode =>
      AlignedSpan contract page ∧ contract.va = userCode ∧ contract.bytes = page ∧
        contract.el0 = true ∧ contract.write = false ∧ contract.execute = true ∧
        contract.device = false
  | .userCode2 =>
      AlignedSpan contract page ∧ contract.va = userCode2 ∧ contract.bytes = page ∧
        contract.el0 = true ∧ contract.write = false ∧ contract.execute = true ∧
        contract.device = false
  | .userData =>
      AlignedSpan contract page ∧ contract.va = userData ∧ contract.bytes = page ∧
        contract.el0 = true ∧ contract.write = true ∧ contract.execute = false ∧
        contract.device = false
  | .userStack =>
      AlignedSpan contract page ∧ contract.va = userStack ∧ contract.bytes = page ∧
        contract.el0 = true ∧ contract.write = true ∧ contract.execute = false ∧
        contract.device = false
  | .hhdmDevice =>
      AlignedSpan contract block1G ∧ contract.va = hhdm ∧ contract.pa = 0 ∧
        contract.bytes = block1G ∧ contract.el0 = false ∧ contract.write = true ∧
        contract.execute = false ∧ contract.device = true
  | .hhdmDram =>
      AlignedSpan contract block1G ∧ contract.va = hhdm + block1G ∧
        contract.pa = block1G ∧ contract.bytes = block1G ∧ contract.el0 = false ∧
        contract.write = true ∧ contract.execute = false ∧ contract.device = false

theorem valid_never_writable_executable {contract : MapContract}
    (valid : Valid contract) :
    ¬ (contract.write = true ∧ contract.execute = true) := by
  cases contract.role <;> simp [Valid] at valid <;> aesop

theorem valid_kernel_text_private {contract : MapContract}
    (role : contract.role = .kernelText) (valid : Valid contract) :
    contract.el0 = false ∧ contract.write = false ∧ contract.execute = true := by
  unfold Valid at valid
  rw [role] at valid
  simp at valid
  aesop

theorem valid_hhdm_private {contract : MapContract}
    (valid : Valid contract)
    (role : contract.role = .hhdmDevice ∨ contract.role = .hhdmDram) :
    contract.el0 = false ∧ contract.write = true ∧ contract.execute = false := by
  rcases role with role | role
  · unfold Valid at valid
    rw [role] at valid
    simp at valid
    aesop
  · unfold Valid at valid
    rw [role] at valid
    simp at valid
    aesop

inductive FaultAction where
  | skip | halt | complete | redirect
  deriving DecidableEq, Repr

structure FaultObservation where
  tag : Nat
  ec : Nat
  far : Nat
  deriving DecidableEq, Repr

def faultAction (observation : FaultObservation) : FaultAction :=
  match observation.tag with
  | 1 | 2 => if observation.ec = 0x24 ∧ observation.far = kernelBase then .skip else .halt
  | 3 => if observation.ec = 0x20 ∧ observation.far = userData then .redirect else .halt
  | 4 => if observation.ec = 0x24 ∧ observation.far = userUnmapped then .complete else .halt
  | _ => .halt

def expectedFaults : List FaultObservation :=
  [{ tag := 1, ec := 0x24, far := kernelBase },
   { tag := 2, ec := 0x24, far := kernelBase },
   { tag := 3, ec := 0x20, far := userData },
   { tag := 4, ec := 0x24, far := userUnmapped }]

theorem expected_fault_actions :
    expectedFaults.map faultAction = [.skip, .skip, .redirect, .complete] := by
  rfl

theorem wrong_read_shape_halts :
    faultAction { tag := 1, ec := 0x20, far := kernelBase } = .halt := by
  rfl

theorem wrong_execute_address_halts :
    faultAction { tag := 3, ec := 0x20, far := userData + page } = .halt := by
  norm_num [faultAction, userData, page]

theorem unknown_tag_halts (tag : Nat) (unknown : tag ≠ 1 ∧ tag ≠ 2 ∧ tag ≠ 3 ∧ tag ≠ 4) :
    faultAction { tag := tag, ec := 0x24, far := kernelBase } = .halt := by
  rcases unknown with ⟨one, two, three, four⟩
  rcases tag with _ | _ | _ | _ | _ | tag <;> simp_all [faultAction]

#print axioms valid_never_writable_executable
#print axioms valid_kernel_text_private
#print axioms valid_hhdm_private
#print axioms expected_fault_actions
#print axioms unknown_tag_halts

end Mettapedia.Machines.Kernel.Arm64Phase3
