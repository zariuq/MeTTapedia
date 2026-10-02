import Mettapedia.GSLT.LanguageDef.NativeOpsZero

/-!
# A heap discipline for array bases

This optional invariant concerns array descriptors only. Ordinary references
may address record fields, as required by native scalar output parameters.
It grants neither pointer liveness nor ownership.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.ArrayBaseDiscipline

mutual
  def value : SourceValue → Bool
    | .record _ children => fields children
    | .array _ none _ => true
    | .array _ (some address) _ => address.fields.isEmpty
    | _ => true

  def fields : List SourceValue → Bool
    | [] => true
    | first :: rest => value first && fields rest
end

theorem fields_get {values : List SourceValue} (valid : fields values = true)
    {index : Nat} {selected : SourceValue} (read : values[index]? = some selected) :
    value selected = true := by
  induction values generalizing index with
  | nil => simp at read
  | cons first rest ih =>
      have parts : value first = true ∧ fields rest = true := by
        simpa only [fields, Bool.and_eq_true] using valid
      cases index with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at read
                cases read
                exact parts.1
      | succ index => exact ih parts.2 read

theorem fields_set {values : List SourceValue} (valid : fields values = true)
    (index : Nat) {replacement : SourceValue} (validReplacement : value replacement = true) :
    fields (values.set index replacement) = true := by
  induction values generalizing index with
  | nil => rfl
  | cons first rest ih =>
      have parts : value first = true ∧ fields rest = true := by
        simpa only [fields, Bool.and_eq_true] using valid
      cases index with
      | zero => simpa only [List.set_cons_zero, fields, Bool.and_eq_true] using
          And.intro validReplacement parts.2
      | succ index =>
          simpa only [List.set_cons_succ, fields, Bool.and_eq_true] using And.intro parts.1 (ih parts.2 index)

theorem read_path (path : List Nat) {before observed : SourceValue}
    (valid : value before = true) (read : sourceReadPath path before = some observed) :
    value observed = true := by
  induction path generalizing before with
  | nil => cases read; exact valid
  | cons index rest ih =>
      cases before with
      | record name children =>
          cases selected : children[index]? with
          | none => simp [sourceReadPath, selected] at read
          | some child =>
              exact ih (fields_get valid selected)
                (by simpa only [sourceReadPath, selected, Option.bind_some] using read)
      | _ => contradiction

theorem write_path (path : List Nat) {before replacement after : SourceValue}
    (valid : value before = true) (validReplacement : value replacement = true)
    (written : sourceWritePath path replacement before = some after) : value after = true := by
  induction path generalizing before after with
  | nil => cases written; exact validReplacement
  | cons index rest ih =>
      cases before with
      | record name children =>
          cases selected : children[index]? with
          | none => simp [sourceWritePath, selected] at written
          | some child =>
              cases changed : sourceWritePath rest replacement child with
              | none => simp [sourceWritePath, selected, changed] at written
              | some updated =>
                  have childValid := ih (fields_get valid selected) changed
                  have same : SourceValue.record name (children.set index updated) = after := by
                    simpa only [sourceWritePath, selected, changed, bind, Option.bind, Option.some.injEq] using written
                  cases same
                  exact fields_set valid index childValid
      | _ => contradiction

def Memory (memory : SourceMemory) : Prop :=
  ∀ storage element contents, memory.cells storage element = some contents → value contents = true

theorem read {memory : SourceMemory} (valid : Memory memory)
    {address : Address} {observed : SourceValue} (read : sourceRead memory address = some observed) :
    value observed = true := by
  cases stored : memory.cells address.storage address.element with
  | none => simp [sourceRead, stored] at read
  | some contents =>
      exact read_path address.fields (valid _ _ _ stored)
        (by simpa only [sourceRead, stored, Option.bind_some] using read)

theorem store {memory : SourceMemory} (valid : Memory memory) (storage element : Nat)
    (replacement : SourceValue) (validReplacement : value replacement = true) :
    Memory (sourceStoreCell memory storage element replacement) := by
  intro candidate index observed stored
  by_cases same : candidate = storage ∧ index = element
  · rcases same with ⟨rfl, rfl⟩
    have equals : replacement = observed := by
      simpa only [sourceStoreCell, and_self, if_true, Option.some.injEq] using stored
    cases equals
    exact validReplacement
  · exact valid candidate index observed
      (by simpa only [sourceStoreCell, same, if_false] using stored)

theorem write {memory after : SourceMemory} (valid : Memory memory)
    (address : Address) (replacement : SourceValue) (validReplacement : value replacement = true)
    (written : sourceWrite memory address replacement = some after) : Memory after := by
  cases stored : memory.cells address.storage address.element with
  | none => simp [sourceWrite, stored] at written
  | some before =>
      cases changed : sourceWritePath address.fields replacement before with
      | none => simp [sourceWrite, stored, changed] at written
      | some updated =>
          have same : sourceStoreCell memory address.storage address.element updated = after := by
            simpa only [sourceWrite, stored, changed, bind, Option.bind, Option.some.injEq] using written
          cases same
          exact store valid address.storage address.element updated
            (write_path address.fields (valid _ _ _ stored) validReplacement changed)

theorem release {memory : SourceMemory} (valid : Memory memory) (storage : Nat) :
    Memory (sourceRelease memory storage) := by
  intro candidate index observed stored
  by_cases same : candidate = storage
  · simp [sourceRelease, same] at stored
  · exact valid candidate index observed (by simpa only [sourceRelease, same, if_false] using stored)

theorem zero {interface : Interface} {type : NativeType} {contents : SourceValue}
    (initialized : SourceZero interface type contents) : value contents = true := by
  refine SourceZero.rec (motive_1 := fun _ contents _ => value contents = true)
    (motive_2 := fun _ contents _ => fields contents = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ initialized
  · rfl
  · rfl
  · rfl
  · rfl
  · intro element; rfl
  · intro element; rfl
  · intro name declaration contents found initializedFields valid
    exact valid
  · rfl
  · intro field first rest others initializedHead initializedTail validHead validTail
    simpa only [fields, Bool.and_eq_true] using And.intro validHead validTail

theorem array_base {type : NativeType} {address : Address} {length : NativeWord64.Word}
    (valid : value (.array type (some address) length) = true) : address.fields = [] :=
  List.isEmpty_iff.mp valid

theorem interior_scalar_reference_allowed : value (.reference (some ⟨5, 0, [6]⟩)) = true := rfl

theorem nested_interior_array_rejected :
    value (.record "Container" [.array .word (some ⟨5, 0, [6]⟩) 1]) = false := rfl

theorem nested_root_array_accepted :
    value (.record "Container" [.array .word (some ⟨5, 0, []⟩) 1]) = true := rfl

end Mettapedia.GSLT.LanguageDef.NativeOps.ArrayBaseDiscipline
