import Mettapedia.GSLT.LanguageDef.NativeOpsCScalarRead

/-!
# Retained local pointer-array stores and conditional continuations

The statement fragment reads the named array, unsigned counter and pointer
operand, then invokes the shared post-increment store. Array and counter
bindings are distinct, and the pointer RHS cannot name the incremented counter.
These local checks do not establish physical pointer separation or C layout.

Conditional execution selects the actual supplied continuation. Dropping or
adding a store changes the execution; there is no successful-template repair.
Nullable identity representation commutes with the independent slot primitive.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.LocalStore

open ScalarRead PostIndex

variable {Ptr : Type} [DecidableEq Ptr]

structure Site where
  array : Name
  counter : Name
  value : Name
  deriving DecidableEq, Repr

def Site.statement (site : Site) : CStatement :=
  .assign (.index (.identifier site.array) (.postIncrement (.identifier site.counter)))
    (.identifier site.value)

def site? : CStatement → Option Site
  | .assign (.index (.identifier array) (.postIncrement (.identifier counter)))
      (.identifier value) =>
      if array ≠ counter ∧ value ≠ counter then some ⟨array, counter, value⟩ else none
  | _ => none

theorem authored_site_is_retained (site : Site)
    (arraySeparated : site.array ≠ site.counter) (rhsSeparated : site.value ≠ site.counter) :
    site? site.statement = some site := by
  cases site
  simp_all [site?, Site.statement]

def nullable (array : Array32 Ptr) : Array32 (Option Ptr) :=
  ⟨array.slots.map some, array.count⟩

omit [DecidableEq Ptr] in
theorem nullable_store (array : Array32 Ptr) (value : Ptr) :
    store (nullable array) (some value) = (store array value).map nullable := by
  by_cases room : array.count.toNat < array.slots.length
  · simp [store, nullable, room]
  · simp [store, nullable, room]

def writeBindings (environment : Environment Ptr) (site : Site)
    (array : Array32 (Option Ptr)) : Environment Ptr :=
  Function.update (Function.update environment site.array (some (.identities array.slots)))
    site.counter (some (.unsigned array.count))

def execute (environment : Environment Ptr) : CStatement → Option (Environment Ptr)
  | .empty => some environment
  | statement => do
      let site ← site? statement
      let .identities slots ← environment site.array | none
      let .unsigned counter ← environment site.counter | none
      let .identity value ← environment site.value | none
      let written ← store (⟨slots, counter⟩ : Array32 (Option Ptr)) value
      some (writeBindings environment site written)

def sequence (environment : Environment Ptr) : List CStatement → Option (Environment Ptr)
  | [] => some environment
  | statement :: rest => (execute environment statement).bind fun updated => sequence updated rest

def branch (fields : FieldReader Ptr) (environment : Environment Ptr) :
    CStatement → Option (Environment Ptr)
  | .branch condition whenTrue whenFalse => do
      let value ← expression environment fields condition
      let selected ← truth? value
      sequence environment (if selected then whenTrue else whenFalse)
  | _ => none

omit [DecidableEq Ptr] in
theorem execute_resolved_site (environment : Environment Ptr) (site : Site)
    (array : Array32 Ptr) (value : Ptr)
    (arraySeparated : site.array ≠ site.counter) (rhsSeparated : site.value ≠ site.counter)
    (arrayRead : environment site.array = some (.identities (array.slots.map some)))
    (counterRead : environment site.counter = some (.unsigned array.count))
    (valueRead : environment site.value = some (.identity (some value))) :
    execute environment site.statement = (store array value).map
      (fun written => writeBindings environment site (nullable written)) := by
  change (do
    let parsed ← site? site.statement
    let .identities slots ← environment parsed.array | none
    let .unsigned counter ← environment parsed.counter | none
    let .identity value ← environment parsed.value | none
    let written ← store (⟨slots, counter⟩ : Array32 (Option Ptr)) value
    some (writeBindings environment parsed written)) = _
  rw [authored_site_is_retained site arraySeparated rhsSeparated]
  dsimp only [bind, Option.bind]
  rw [arrayRead]
  dsimp only [bind, Option.bind]
  rw [counterRead]
  dsimp only [bind, Option.bind]
  rw [valueRead]
  change (store (nullable array) (some value)).bind _ = _
  rw [nullable_store]
  cases store array value <;> rfl

omit [DecidableEq Ptr] in
theorem sequence_single (environment : Environment Ptr) (statement : CStatement) :
    sequence environment [statement] = execute environment statement := by
  change (execute environment statement).bind some = execute environment statement
  cases execute environment statement <;> rfl

theorem branch_selects_actual_continuation (fields : FieldReader Ptr)
    (environment : Environment Ptr) (condition : CExpr) (yes no : List CStatement)
    (selected : Bool)
    (read : (expression environment fields condition).bind truth? = some selected) :
    branch fields environment (.branch condition yes no) =
      sequence environment (if selected then yes else no) := by
  change (expression environment fields condition).bind (fun value =>
    (truth? value).bind (fun choice => sequence environment (if choice then yes else no))) = _
  rw [← Option.bind_assoc]
  rw [read]
  rfl

namespace Controls

def site : Site := ⟨"pending".toList, "added".toList, "dependency".toList⟩

def environment : Environment Nat := fun name =>
  if name = "pending".toList then some (.identities [some 1, some 99, some 88])
  else if name = "added".toList then some (.unsigned 1)
  else if name = "dependency".toList then some (.identity (some 2)) else none

def observation (environment : Environment Nat) : Option (List (Option Nat) × UInt32) := do
  let .identities slots ← environment "pending".toList | none
  let .unsigned count ← environment "added".toList | none
  some (slots.take count.toNat, count)

theorem actual_old_index_and_increment_observed :
    (execute environment site.statement).bind observation = some ([some 1, some 2], 2) :=
  by decide +kernel

theorem omitted_continuation_does_not_invent_append :
    (sequence environment []).bind observation = some ([some 1], 1) := by decide +kernel

theorem retained_empty_statement_preserves_environment :
    execute environment .empty = some environment ∧
      (sequence environment [.empty, site.statement]).bind observation =
        some ([some 1, some 2], 2) := by
  constructor
  · rfl
  · decide +kernel

theorem extra_store_adds_extra_occurrence :
    (sequence environment [site.statement, site.statement]).bind observation =
      some ([some 1, some 2, some 2], 3) := by decide +kernel

theorem selected_empty_branch_needs_no_store_room :
    (branch (fun _ _ => none) environment (.branch (.bool false) [site.statement] [])).bind
      observation = some ([some 1], 1) := by decide +kernel

theorem missing_array_binding_has_no_execution :
    execute (Function.update environment "pending".toList none) site.statement = none := rfl

theorem full_array_has_no_execution :
    execute (Function.update environment "added".toList (some (.unsigned 3))) site.statement =
      none := rfl

theorem rhs_counter_alias_is_not_admitted :
    site? (⟨"pending".toList, "added".toList, "added".toList⟩ : Site).statement = none :=
  by decide +kernel

theorem array_counter_alias_is_not_admitted :
    site? (⟨"added".toList, "added".toList, "dependency".toList⟩ : Site).statement = none :=
  by decide +kernel

end Controls

#print axioms authored_site_is_retained
#print axioms nullable_store
#print axioms execute_resolved_site
#print axioms sequence_single
#print axioms branch_selects_actual_continuation
#print axioms Controls.actual_old_index_and_increment_observed
#print axioms Controls.omitted_continuation_does_not_invent_append
#print axioms Controls.retained_empty_statement_preserves_environment
#print axioms Controls.extra_store_adds_extra_occurrence
#print axioms Controls.selected_empty_branch_needs_no_store_room
#print axioms Controls.missing_array_binding_has_no_execution
#print axioms Controls.full_array_has_no_execution
#print axioms Controls.rhs_counter_alias_is_not_admitted
#print axioms Controls.array_counter_alias_is_not_admitted

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.LocalStore
