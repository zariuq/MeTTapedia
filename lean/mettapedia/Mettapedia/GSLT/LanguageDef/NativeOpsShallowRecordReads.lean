import Mettapedia.GSLT.LanguageDef.NativeOpsMemory

/-! Record reads cannot descend through atomic fields. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.ShallowRecordReads

def atomic : SourceValue → Bool
  | .record _ _ => false
  | _ => true

theorem atomic_path_not_record (value : SourceValue) (valid : atomic value = true)
    (path : List Nat) (name : String) (fields : List SourceValue) :
    sourceReadPath path value ≠ some (.record name fields) := by
  cases value <;> cases path <;> simp_all [atomic, sourceReadPath]

theorem record_path_is_root (name : String) (fields : List SourceValue)
    (shallow : ∀ value ∈ fields, atomic value = true) (path : List Nat)
    (observedName : String) (observedFields : List SourceValue)
    (read : sourceReadPath path (.record name fields) = some (.record observedName observedFields)) :
    path = [] := by
  cases path with
  | nil => rfl
  | cons index rest =>
    cases selected : fields[index]? with
    | none => simp [sourceReadPath, selected] at read
    | some value =>
      have member : value ∈ fields := List.mem_of_getElem? selected
      exact False.elim (atomic_path_not_record value (shallow value member) rest observedName observedFields
        (by simpa only [sourceReadPath, selected, Option.bind_some] using read))

theorem read_store_other (memory : SourceMemory) (storage element : Nat)
    (value : SourceValue) (address : Address)
    (different : ¬ (address.storage = storage ∧ address.element = element)) :
    sourceRead (sourceStoreCell memory storage element value) address = sourceRead memory address := by
  simp only [sourceRead, sourceStoreCell, different, if_false]

end Mettapedia.GSLT.LanguageDef.NativeOps.ShallowRecordReads
