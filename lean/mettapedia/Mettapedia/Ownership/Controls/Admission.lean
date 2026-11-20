import Mettapedia.Ownership.Admission
import Mettapedia.Ownership.Controls.Interface

/-!
# Controls: admission

Examples admitted and refused.
-/

set_option autoImplicit false

namespace Mettapedia.Ownership

open Mettapedia.Machines.CMemory.Borrowing
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.PermissionFlow

namespace Controls

def scalarSignature : Signature := ⟨[], false, .value, [], []⟩
def scalar (name : String) (body : Plan Action) : Function :=
  ⟨name, scalarSignature, [], [], .value, body⟩

def nullableOwnedRecordSignature : Signature :=
  ⟨[], false, .owned 1 true, [], [(0, .owned 1 true)]⟩
def nullableOwnedRecord (body : Plan Action) : Function :=
  ⟨"nullable-record", nullableOwnedRecordSignature, [], [], .owned 1 true, body⟩
def nullableOwnedRecordCallables : List Callable :=
  [⟨"nullable-record", nullableOwnedRecordSignature⟩]

theorem null_outer_record_omits_nested_fields :
    admitFunction nullableOwnedRecordCallables
      (nullableOwnedRecord (.step .nullResult .ret)) = true := by decide

theorem nonnull_outer_record_requires_nested_fields :
    admitFunction nullableOwnedRecordCallables
      (nullableOwnedRecord (.step (.root 1 8 .exclusive .heap 1)
        (.step (.give 1 1) .ret))) = false := by decide
def scalarCallables (name : String) : List Callable := [⟨name, scalarSignature⟩]

def globalWriteBody : Plan Action :=
  .step (.root 1 4 .exclusive .input 0)
    (.step (.access 1 ⟨1, 0, 4⟩ true) (.step (.endLoan 1) .ret))

theorem ambient_global_write_refused :
    admitFunction (scalarCallables "ambient")
      { scalar "ambient" globalWriteBody with ambient := [(1, 4)] } = false := by decide

def globalSignature : Signature := ⟨[.borrowed 4 true], false, .value, [], []⟩

theorem explicit_global_write_admitted :
    admitFunction [⟨"explicit", globalSignature⟩]
      ⟨"explicit", globalSignature, [1], [], .value, globalWriteBody⟩ = true := by decide

def loopBody : Plan Action :=
  .step (.root 1 8 .exclusive .local 0)
    (.step (.borrow 2 1 ⟨1, 0, 4⟩ .exclusive)
      (.step (.access 2 ⟨1, 0, 4⟩ true)
        (.step (.endLoan 2) (.step (.endLoan 1) .continueLoop))))

theorem repeated_lexical_borrow_admitted :
    admitFunction (scalarCallables "loop") (scalar "loop" (.loop loopBody .ret)) = true := by decide

theorem leaking_loop_borrow_refused :
    admitFunction (scalarCallables "loop") (scalar "loop"
      (.loop (.step (.root 1 8 .exclusive .local 0) .continueLoop) .ret)) = false := by decide

theorem unhandled_foreign_call_refused : admitFunction (scalarCallables "call")
    (scalar "call" (.step (.invoke "unknown" []) .ret)) = false := by decide

theorem false_borrowed_result_refused : admitFunction (scalarCallables "escape")
    ⟨"escape", scalarSignature, [], [], .borrowed ⟨2, 0, 4⟩ false false,
      .step (.root 1 4 .exclusive .local 0)
        (.step (.result 1 ⟨1, 0, 4⟩ false) .ret)⟩ = false := by decide

def borrowedResultSignature (nullable : Bool) : Signature :=
  ⟨[.borrowed 4 false], false, .borrowed 0 0 4 false nullable, [], []⟩
def borrowedResult (nullable : Bool) : Function :=
  ⟨"borrowed-result", borrowedResultSignature nullable, [1], [],
    .borrowed ⟨1, 0, 4⟩ false nullable,
    .step (.root 1 4 .shared .input 0)
      (.step .nullResult (.step (.endLoan 1) .ret))⟩

theorem nullable_borrowed_null_result_admitted :
    admitFunction [⟨"borrowed-result", borrowedResultSignature true⟩]
      (borrowedResult true) = true := by decide

theorem nonnullable_borrowed_null_result_refused :
    admitFunction [⟨"borrowed-result", borrowedResultSignature false⟩]
      (borrowedResult false) = false := by decide

/-- A whole buffer lent for writing gets fresh storage, as a rehash does: its old
storage is released, a fresh allocation replaces it, and the buffer stays the
caller's. -/
def growSignature (writing : Bool) : Signature := ⟨[.viewed writing], false, .value, [], []⟩
def grower (writing : Bool) (body : Plan Action) : Function :=
  ⟨"grow", growSignature writing, [1], [], .value, body⟩
def freeSignature : Signature := ⟨[.released 1], false, .value, [], []⟩
def reallocSignature : Signature := ⟨[.resized 1, .value], false, .owned 1 true, [], []⟩
def growCallables (writing : Bool) : List Callable :=
  [⟨"grow", growSignature writing⟩, ⟨"free", freeSignature⟩, ⟨"realloc", reallocSignature⟩]

def growBody (mode : Mode) (family : Nat) : Plan Action :=
  .step (.root 1 1 mode .input 0)
    (.step (.vacate 1 1) (.step (.invoke "free" [.released 1])
      (.step (.root 2 8 .exclusive .heap 1)
        (.step (.replace 1 2 family) (.step (.endLoan 1) .ret)))))

theorem replace_storage_admitted :
    admitFunction (growCallables true) (grower true (growBody .exclusive 1)) = true := by decide

/-- A buffer lent only for reading cannot have its storage replaced. -/
theorem replace_read_only_refused :
    admitFunction (growCallables false) (grower false (growBody .shared 1)) = false := by decide

/-- The family named must be the fresh allocation's. -/
theorem replace_other_family_refused :
    admitFunction (growCallables true) (grower true (growBody .exclusive 2)) = false := by decide

/-- No pointer into the old storage may be live when it is replaced. -/
theorem replace_under_live_borrow_refused :
    admitFunction (growCallables true) (grower true
      (.step (.root 1 1 .exclusive .input 0) (.step (.borrow 3 1 ⟨1, 0, 1⟩ .shared)
        (.step (.root 4 8 .exclusive .heap 1)
          (.step (.replace 1 4 1) (.step (.endLoan 3) (.step (.endLoan 1) .ret))))))) = false := by decide

/-- Only an input's storage is replaced; a local allocation is not an input. -/
theorem replace_local_refused :
    admitFunction (scalarCallables "local") (scalar "local"
      (.step (.root 1 8 .exclusive .local 0) (.step (.root 2 8 .exclusive .heap 1)
        (.step (.replace 1 2 1) (.step (.endLoan 1) .ret))))) = false := by decide

/-- A fresh allocation never replaced, released or given leaks, and is refused. -/
theorem replace_never_done_refused :
    admitFunction (growCallables true) (grower true
      (.step (.root 1 1 .exclusive .input 0)
        (.step (.root 2 8 .exclusive .heap 1) (.step (.endLoan 1) .ret)))) = false := by decide

/-- Released storage is not read before fresh storage is stored back. -/
theorem released_storage_read_refused :
    admitFunction (growCallables true) (grower true
      (.step (.root 1 1 .exclusive .input 0)
        (.step (.vacate 1 1) (.step (.invoke "free" [.released 1])
          (.step (.access 1 ⟨1, 0, 1⟩ false) .ret))))) = false := by decide

/-- Released storage is not lent to a call before it is replaced. -/
theorem released_storage_lent_refused :
    admitFunction (growCallables true) (grower true
      (.step (.root 1 1 .exclusive .input 0)
        (.step (.vacate 1 1) (.step (.invoke "free" [.released 1])
          (.step (.invoke "grow" [.loan 1]) .ret))))) = false := by decide

/-- A function never returns while an input's storage is released. -/
theorem released_storage_never_refilled_refused :
    admitFunction (growCallables true) (grower true
      (.step (.root 1 1 .exclusive .input 0)
        (.step (.vacate 1 1) (.step (.invoke "free" [.released 1])
          (.step (.endLoan 1) .ret))))) = false := by decide

/-- Released storage must reach the call that releases it. -/
theorem released_storage_never_taken_refused :
    admitFunction (growCallables true) (grower true
      (.step (.root 1 1 .exclusive .input 0)
        (.step (.vacate 1 1) (.step (.root 2 8 .exclusive .heap 1)
          (.step (.replace 1 2 1) (.step (.endLoan 1) .ret)))))) = false := by decide

/-- A reallocation either moved the storage, which the fresh result then
replaces, or returned null, which moved nothing: the old storage is restored
and the null owner ends without a release. -/
def reallocBody (onNull : Plan Action) : Plan Action :=
  .step (.root 1 1 .exclusive .input 0)
    (.step (.vacate 1 1) (.step (.invoke "realloc" [.released 1, .value])
      (.step (.root 2 8 .exclusive .heap 1)
        (.branch onNull
          (.step (.replace 1 2 1) (.step (.endLoan 1) .ret)) .done))))

def restoredOnNull : Plan Action :=
  .step (.restore 1) (.step (.access 1 ⟨1, 0, 1⟩ false)
    (.step (.endLoan 2) (.step (.nullOwner 2 1) (.step (.endLoan 1) .ret))))

theorem reallocation_admitted :
    admitFunction (growCallables true) (grower true (reallocBody restoredOnNull)) = true := by decide

/-- Without the restore the null path still reaches released storage. -/
theorem reallocation_null_unrestored_refused :
    admitFunction (growCallables true) (grower true (reallocBody
      (.step (.access 1 ⟨1, 0, 1⟩ false)
        (.step (.endLoan 2) (.step (.nullOwner 2 1) (.step (.endLoan 1) .ret)))))) = false := by decide

/-- A null owner still needs its end: releasing it as storage would leave a
transfer no call takes. -/
theorem reallocation_null_released_refused :
    admitFunction (growCallables true) (grower true (reallocBody
      (.step (.restore 1)
        (.step (.endLoan 2) (.step (.release 2 1) (.step (.endLoan 1) .ret)))))) = false := by decide

/-- Storage released to `free` never comes back. -/
theorem freed_storage_restore_refused :
    admitFunction (growCallables true) (grower true
      (.step (.root 1 1 .exclusive .input 0)
        (.step (.vacate 1 1) (.step (.invoke "free" [.released 1])
          (.step (.restore 1) (.step (.endLoan 1) .ret)))))) = false := by decide

/-- A reallocation contract names its fresh result's family. -/
theorem reallocation_without_owned_result_invalid :
    signatureValid ⟨[.resized 1, .value], false, .value, [], []⟩ = false := by decide

end Controls

end Mettapedia.Ownership
