import Mettapedia.Machines.TIsa.ImportedP1
import Mettapedia.Machines.TIsa.P1Memory

/-!
# Memory accesses through declared entry pointers

Check the region, access mode, base register and extent of each explicit load
and store. The address theorem uses the executable memory semantics under a
valid concrete region layout. Frame loads use `P1Memory.frame_access`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.P1EntryMemory

open P1Source

structure Access where
  region : Region
  pointer : Reg
  width : Width
  displacement : BitVec 32
  write : Bool

def accesses : Stmt → List Access
  | .instruction (.load _ width region _ pointer displacement) =>
      [⟨region, pointer, width, displacement, false⟩]
  | .instruction (.store width region pointer displacement _) =>
      [⟨region, pointer, width, displacement, true⟩]
  | .seq left right | .branch _ left right => accesses left ++ accesses right
  | .counted _ _ _ body | .early _ _ _ _ body => accesses body
  | _ => []

theorem mem_accesses_of_atPath {statement fragment : Stmt} {path : List Nat} {access : Access}
    (located : statement.atPath path = some fragment) (member : access ∈ accesses fragment) :
    access ∈ accesses statement := by
  induction path generalizing statement with
  | nil =>
      simp [Stmt.atPath] at located
      simpa [located] using member
  | cons child path ih =>
      rcases child with _ | (_ | (_ | child)) <;>
        cases statement <;> simp [Stmt.atPath] at located
      all_goals simp [accesses, List.mem_append, ih located]

def destinations : Stmt → List Reg
  | .instruction instruction => instruction.destination?.toList
  | .seq left right | .branch _ left right => destinations left ++ destinations right
  | .counted index _ _ body | .early index _ _ _ body => index :: destinations body
  | _ => []

def Access.check (access : Access) (program : Program) : Bool :=
  let hasPointer := program.entry.any fun entry =>
    entry.register == access.pointer && entry.ty == .pointer && entry.region == access.region
  match program.regions[access.region.val]? with
  | none => false
  | some decl => hasPointer && decide
      ((if access.write then decl.mode = .readWrite else decl.mode ≠ .absent) ∧
       0 ≤ access.displacement.toInt ∧
       access.displacement.toInt + access.width.bytes ≤ decl.minimum.toNat)

theorem Access.checked (access : Access) (program : Program) (decl : RegionDecl)
    (region : program.regions[access.region.val]? = some decl)
    (accepted : access.check program = true) :
    (∃ entry ∈ program.entry, entry.register = access.pointer ∧
        entry.ty = .pointer ∧ entry.region = access.region) ∧
    (if access.write then decl.mode = .readWrite else decl.mode ≠ .absent) ∧
    0 ≤ access.displacement.toInt ∧
    access.displacement.toInt + access.width.bytes ≤ decl.minimum.toNat := by
  simpa [Access.check, region, List.any_eq_true, and_assoc] using accepted

theorem Access.address_at_base (access : Access) (program : Program) (decl : RegionDecl)
    (region : program.regions[access.region.val]? = some decl)
    (accepted : access.check program = true) (base length : Word)
    (minimum : decl.minimum.toNat ≤ length.toNat) (fits : base.toNat + length.toNat < 2 ^ 64) :
    Memory.access? base length base access.displacement.toInt access.width.bytes =
      some (base.toNat + access.displacement.toInt.toNat) := by
  obtain ⟨_, _, lower, upper⟩ := access.checked program decl region accepted
  apply (P1Memory.access?_iff_inside base length base access.displacement access.width.bytes
    (base.toNat + access.displacement.toInt.toNat) fits le_rfl (by omega)).mpr
  exact ⟨by omega, by omega, by omega⟩

noncomputable def sub1 : P1Capture.Program :=
  ImportedP1.programs[11]'(by rw [ImportedP1.exact_count.2]; decide)

theorem sub1_name : sub1.name = "mm_sub1_leaf" := by kernel_reflexivity

theorem sub1_accesses_checked :
    (accesses sub1.source.body).all (fun access => access.check sub1.source) = true := by
  kernel_reflexivity

theorem sub1_entry_pointers_unassigned :
    sub1.source.entry.all (fun entry =>
      entry.ty != .pointer || !(destinations sub1.source.body).contains entry.register) = true := by
  kernel_reflexivity

theorem sub1_access_count : (accesses sub1.source.body).length = 22 := by kernel_reflexivity

theorem sub1_access_at_base (access : Access) (member : access ∈ accesses sub1.source.body)
    (decl : RegionDecl) (region : sub1.source.regions[access.region.val]? = some decl)
    (base length : Word) (minimum : decl.minimum.toNat ≤ length.toNat)
    (fits : base.toNat + length.toNat < 2 ^ 64) :
    Memory.access? base length base access.displacement.toInt access.width.bytes =
      some (base.toNat + access.displacement.toInt.toNat) :=
  access.address_at_base sub1.source decl region
    (List.all_eq_true.mp sub1_accesses_checked access member) base length minimum fits

theorem sub1_access_at_path (path : List Nat) (fragment : Stmt) (access : Access)
    (located : sub1.source.body.atPath path = some fragment)
    (member : access ∈ accesses fragment)
    (decl : RegionDecl) (region : sub1.source.regions[access.region.val]? = some decl)
    (base length : Word) (minimum : decl.minimum.toNat ≤ length.toNat)
    (fits : base.toNat + length.toNat < 2 ^ 64) :
    Memory.access? base length base access.displacement.toInt access.width.bytes =
      some (base.toNat + access.displacement.toInt.toNat) :=
  sub1_access_at_base access (mem_accesses_of_atPath located member) decl region base length minimum fits

theorem sub1_out_of_bounds_rejected :
    (Access.mk 4 5 .word64 (32#32) true).check sub1.source = false := by kernel_reflexivity

theorem sub1_wrong_pointer_rejected :
    (Access.mk 4 1 .word64 (0#32) true).check sub1.source = false := by kernel_reflexivity

end Mettapedia.Machines.TIsa.P1EntryMemory
