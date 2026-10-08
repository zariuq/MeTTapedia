import Mettapedia.Machines.CMemory.Values
import Mettapedia.GSLT.LanguageDef.NativeOpsCScalarRead

/-!
# Retained scalar expressions with physical block reads

The immutable-local profile resolves identifiers to scalar values. The
current-name profile loads named cells at each reached identifier read, while
declared uninitialized locals shield outer locations. Pointer-array indexing is a typed load
from the actual stored pointer. Field descriptors specify a cell offset and
scalar type, not a field-value oracle. Comparisons and Boolean conversions of
pointers use the shared pointer-equality primitive, whose safety requires live
pointer values. Logical selection keeps the supplied unselected expression
unevaluated. Unsupported syntax or scalar types reach undefined.

Unsigned arithmetic uses the existing UInt32/UInt64 scalar operations and their
declared unsigned widening. Signed decimals and unary minus use the common
scalar profile, which rejects signed overflow. Native byte layout, other C promotions and
synchronization remain separate boundaries. This module does not define a second memory or ownership model.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.ReadExpressions

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic

inductive FieldKind where
  | pointer
  | signedWord
  | word
  | word64
  | boolean
  | embedded
  deriving DecidableEq, Repr

structure Field where
  offset : Nat
  kind : FieldKind
  deriving DecidableEq, Repr


/-- The descriptor selects the same stored scalar type, without value-based
narrowing or repair. -/
def valueKind : CVal → FieldKind
  | .bool _ => .boolean
  | .i32 _ => .signedWord
  | .u32 _ => .word
  | .u64 _ => .word64
  | .ptr _ => .pointer

abbrev Layout := Name → Option Field
abbrev Environment := Name → Option CVal

def resolved {α : Type} : Option α → CProg CVal α
  | some value => pure value
  | none => CProg.undefined

def scalar (value : CVal) : ScalarRead.Value Ptr := match value with
  | .bool value => .boolean value
  | .i32 value => .signed value
  | .u32 value => .unsigned value
  | .u64 value => .unsigned64 value
  | .ptr value => .identity value

def cell? : ScalarRead.Value Ptr → Option CVal
  | .boolean value => some (.bool value)
  | .signed value => some (.i32 value)
  | .unsigned value => some (.u32 value)
  | .unsigned64 value => some (.u64 value)
  | .identity value => some (.ptr value)
  | .identities _ => none
  | .wordRecord _ => none

/-- Pointer truth is a validity-checked comparison, not a test that bypasses
the lifetime contract of the memory primitives. -/
def truth : CVal → CProg CVal Bool
  | .bool value => pure value
  | .i32 value => pure (value != 0)
  | .u32 value => pure (value != 0)
  | .u64 value => pure (value != 0)
  | .ptr value => do
      let isNull ← CProg.ptrEq value none
      pure (!isNull)

def pointer : CVal → CProg CVal (Option Ptr)
  | .ptr value => pure value
  | _ => CProg.undefined

def word : CVal → CProg CVal UInt32
  | .u32 value => pure value
  | _ => CProg.undefined

def signedWord : CVal → CProg CVal Int32
  | .i32 value => pure value
  | _ => CProg.undefined

def field (layout : Layout) (owner : CVal) (name : Name) : CProg CVal CVal := do
  let owner ← pointer owner
  match owner, layout name with
  | some address, some descriptor =>
      match descriptor.kind with
      | .embedded => CProg.undefined
      | .signedWord => do
          let value ← CProg.loadI32 (address + descriptor.offset)
          pure (.i32 value)
      | .pointer => do
          let value ← CProg.loadPtr (address + descriptor.offset)
          pure (.ptr value)
      | .word => do
          let value ← CProg.loadU32 (address + descriptor.offset)
          pure (.u32 value)
      | .word64 => do
          let value ← CProg.loadU64 (address + descriptor.offset)
          pure (.u64 value)
      | .boolean => do
          let value ← CProg.loadBool (address + descriptor.offset)
          pure (.bool value)
  | _, _ => CProg.undefined

def indexed (array index : CVal) : CProg CVal CVal := do
  let array ← pointer array
  let index ← word index
  match array with
  | some address => CProg.loadPtr (address + index.toNat) >>= fun value => pure (.ptr value)
  | none => CProg.undefined

/-- An explicitly typed array reading retains its unsigned index width and
uses the existing scalar-cell reader at the selected logical offset. Native
element size, bounds, alignment and lifetime remain representation obligations. -/
def indexedScalar (kind : FieldKind) (array index : CVal) : CProg CVal CVal := do
  let array ← pointer array
  let offset ← match index with
    | .u32 value => pure value.toNat
    | .u64 value => pure value.toNat
    | _ => CProg.undefined
  field (fun _ => some ⟨offset, kind⟩) (.ptr array) []

def equal (left right : CVal) : CProg CVal Bool := match left, right with
  | .ptr left, .ptr right => CProg.ptrEq left right
  | _, _ => resolved (ScalarRead.equal? (scalar left) (scalar right))

/-- Numeric unary minus reuses the shared scalar laws; it never treats a
pointer's address as an integer or accepts signed overflow. -/
def negate (value : CVal) : CProg CVal CVal :=
  resolved ((ScalarRead.numericNegation? (scalar value)).bind cell?)

def binary (operator : BinaryOperator) (left right : CVal) : CProg CVal CVal :=
  match operator with
  | .eq => equal left right >>= fun value => pure (.bool value)
  | .ne => equal left right >>= fun value => pure (.bool (!value))
  | .lt =>
      match left, right with
      | .i32 _, _ | _, .i32 _ =>
          resolved ((ScalarRead.numericBinary .lt (scalar left) (scalar right)).bind cell?)
      | .u64 _, _ | _, .u64 _ =>
          resolved ((ScalarRead.numericBinary .lt (scalar left) (scalar right)).bind cell?)
      | _, _ => do
          let left ← word left
          let right ← word right
          pure (.bool (decide (left < right)))
  | other =>
      match left, right with
      | .i32 _, _ | _, .i32 _ =>
          resolved ((ScalarRead.numericBinary other (scalar left) (scalar right)).bind cell?)
      | .u64 _, _ | _, .u64 _ =>
          resolved ((ScalarRead.numericBinary other (scalar left) (scalar right)).bind cell?)
      | _, _ => do
          let left ← word left
          let right ← word right
          resolved ((ScalarRead.unsignedBinary other left right).bind cell?)

/-- A named call service is parameterized by its declared result type. -/
abbrev CallService (α : Type) := Name → List CVal → CProg CVal α

/-- Named calls receive the evaluated arguments in source order. The service
must separately justify its catalogue, conversions, state effects and return
value; it is not authorized merely because a C identifier was recognized.
This order defines the admitted interpreter profile. Applying it to C with
effectful operands needs an evaluation-order or commutation argument. -/
abbrev Calls := CallService CVal

def noCalls : Calls := fun _ _ => CProg.undefined

/-- Embedded-field addresses do not read an aggregate as a scalar cell.
The offset is admitted by the layout; validity and ownership remain obligations
of the program's physical execution contract. -/
def fieldAddress (layout : Layout) (owner : CVal) (name : Name) : CProg CVal Ptr := do
  let owner ← pointer owner
  match owner, layout name with
  | some owner, some descriptor => pure (owner + descriptor.offset)
  | _, _ => CProg.undefined

/- The recursive operands and field/index names come from the supplied AST.
No successful preparation or scan template is substituted for them. -/
/-- Resolution occurs at each source identifier read and may perform a typed
load. It is distinct from calling a source function or caching a value. -/
abbrev NameReads := Name → CProg CVal CVal
abbrev Locations := Name → Option (Ptr × FieldKind)

/-- A named stored scalar reuses the physical field reader at its supplied
location. Embedded objects remain addressable through separate object operations. -/
def located (locations : Locations) : NameReads := fun name =>
  match locations name with
  | some (address, kind) => field (fun _ => some ⟨0, kind⟩) (.ptr (some address)) name
  | none => CProg.undefined

/-- Declared but uninitialized locals shield same-spelled stored names.
Only names outside that local inventory use the supplied current locations. -/
def localOrLocated (environment : Environment) (declared : Name → Bool)
    (locations : Locations) : NameReads := fun name =>
  match environment name with
  | some value => pure value
  | none => if declared name then CProg.undefined else located locations name

/-- Address and size operations are separate from rvalue reads. The place
lookup establishes local object identities. Pointer operands are evaluated
by the common reader, while sizeof uses only retained type information. Empty providers retain the established scalar-only profile. -/
structure ObjectReads where
  place : Option (Name → Option Ptr) := none
  size : CExpr → Option CVal := fun _ => none
  fields : Option (CExpr → Bool → Layout) := none
  /-- The static array operand determines its effective element type.
  Absent metadata retains the original pointer-array/UInt32 profile. -/
  indexKind : Option (CExpr → Option FieldKind) := none

/-- A static object profile selects descriptors using the actual owner syntax
and the dot/arrow distinction. The default preserves the existing single-layout
profile. Descriptor selection does not evaluate the owner or inspect a value. -/
def ObjectReads.fieldLayout (objects : ObjectReads) (fallback : Layout)
    (owner : CExpr) (throughPointer : Bool) : Layout :=
  match objects.fields with
  | none => fallback
  | some fields => fields owner throughPointer

mutual
 def expressionWithNames (names : NameReads) (calls : Calls) (layout : Layout)
     (operand : CExpr) (objects : ObjectReads := {}) : CProg CVal CVal := match operand with
  | .identifier name => names name
  | .decimal value => resolved ((ScalarRead.signedDecimal? value).bind cell?)
  | .unsignedInteger value =>
      resolved (if value < 2 ^ 32 then some (.u32 (UInt32.ofNat value)) else none)
  | .word value => pure (.u64 (UInt64.ofNat value.toNat))
  | .bool value => pure (.bool value)
  | .null => pure (.ptr none)
  | .call name arguments => do
      let values ← argumentsWithNames names calls layout arguments objects
      calls name values
  | .unary .address (.field record name true) => do
      let owner ← expressionWithNames names calls layout record objects
      let address ← fieldAddress (objects.fieldLayout layout record true) owner name
      pure (.ptr (some address))
  | .unary .address operand => match objects.place with
      | none => CProg.undefined
      | some _ => do
          let address ← placeWithNames names calls layout operand objects
          pure (.ptr (some address))
  | .sizeOfExpr operand => resolved (objects.size (.sizeOfExpr operand))
  | .sizeOf type => resolved (objects.size (.sizeOf type))
  | .unary .negate operand => do
      let value ← expressionWithNames names calls layout operand objects
      negate value
  | .unary .not operand => do
      let value ← expressionWithNames names calls layout operand objects
      let selected ← truth value
      pure (.bool (!selected))
  | .field record name true => do
      let owner ← expressionWithNames names calls layout record objects
      field (objects.fieldLayout layout record true) owner name
  | .field record name false => match objects.place with
      | none => CProg.undefined
      | some _ => do
          let owner ← placeWithNames names calls layout record objects
          field (objects.fieldLayout layout record false) (.ptr (some owner)) name
  | .index array index => do
      let address ← expressionWithNames names calls layout array objects
      let position ← expressionWithNames names calls layout index objects
      match objects.indexKind with
      | none => indexed address position
      | some kinds => match kinds array with
          | some kind => indexedScalar kind address position
          | none => CProg.undefined
  | .binary .and left right => do
      let first ← expressionWithNames names calls layout left objects
      let selected ← truth first
      if selected then do
        let second ← expressionWithNames names calls layout right objects
        let selectedSecond ← truth second
        pure (.bool selectedSecond)
      else pure (.bool false)
  | .binary .or left right => do
      let first ← expressionWithNames names calls layout left objects
      let selected ← truth first
      if selected then pure (.bool true) else do
        let second ← expressionWithNames names calls layout right objects
        let selectedSecond ← truth second
        pure (.bool selectedSecond)
  | .binary operator left right => do
      let first ← expressionWithNames names calls layout left objects
      let second ← expressionWithNames names calls layout right objects
      binary operator first second
  | .conditional condition yes no => do
      let value ← expressionWithNames names calls layout condition objects
      let selected ← truth value
      if selected then expressionWithNames names calls layout yes objects else expressionWithNames names calls layout no objects
  | _ => CProg.undefined
 termination_by structural operand

 def argumentsWithNames (names : NameReads) (calls : Calls) (layout : Layout)
     (arguments : List CExpr) (objects : ObjectReads := {}) : CProg CVal (List CVal) := match arguments with
  | [] => pure []
  | argument :: rest => do
      let first ← expressionWithNames names calls layout argument objects
      let others ← argumentsWithNames names calls layout rest objects
      pure (first :: others)
 termination_by structural arguments

 /-- A place is resolved without reading an aggregate value. Pointer operands
 still use the same scalar reader; recursive source operands are structurally
 smaller. The descriptor's offset remains a logical cell offset. -/
 def placeWithNames (names : NameReads) (calls : Calls) (layout : Layout)
     (operand : CExpr) (objects : ObjectReads := {}) : CProg CVal Ptr := match operand with
  | .identifier name => resolved (objects.place.bind (fun places => places name))
  | .unary .dereference operand => do
      let value ← expressionWithNames names calls layout operand objects
      let address ← pointer value
      resolved address
  | .field record name true => do
      let owner ← expressionWithNames names calls layout record objects
      fieldAddress (objects.fieldLayout layout record true) owner name
  | .field record name false => do
      let owner ← placeWithNames names calls layout record objects
      let descriptor ← resolved ((objects.fieldLayout layout record false) name)
      pure (owner + descriptor.offset)
  | _ => CProg.undefined
 termination_by structural operand
end



theorem default_owner_field_layout_is_unchanged (fallback : Layout)
    (owner : CExpr) (throughPointer : Bool) :
    ({} : ObjectReads).fieldLayout fallback owner throughPointer = fallback := rfl

/-- Owner-specific addressing uses the selected record descriptor, even when
the fallback layout gives the same spelling a different offset. -/
theorem addressed_field_uses_owner_descriptor (names : NameReads) (calls : Calls)
    (fallback selected : Layout) (owner : CExpr) (name : Name) (address : Ptr)
    (offset : Nat) (kind : FieldKind) (objects : ObjectReads)
    (typed : objects.fieldLayout fallback owner true = selected)
    (readOwner : expressionWithNames names calls fallback owner objects =
      pure (.ptr (some address)))
    (descriptor : selected name = some ⟨offset, kind⟩) :
    expressionWithNames names calls fallback (.unary .address (.field owner name true)) objects =
      pure (.ptr (some (address + offset))) := by
  rw [expressionWithNames.eq_def]
  dsimp only
  rw [readOwner]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  simp only [typed, fieldAddress, pointer, descriptor, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

/-- Dot addressing obtains the object's place and then its owner-specific
descriptor; it does not read the aggregate as a scalar. -/
theorem dot_place_uses_owner_descriptor (names : NameReads) (calls : Calls)
    (fallback selected : Layout) (owner : CExpr) (name : Name) (address : Ptr)
    (offset : Nat) (kind : FieldKind) (objects : ObjectReads)
    (typed : objects.fieldLayout fallback owner false = selected)
    (ownerPlace : placeWithNames names calls fallback owner objects = pure address)
    (descriptor : selected name = some ⟨offset, kind⟩) :
    placeWithNames names calls fallback (.field owner name false) objects =
      pure (address + offset) := by
  rw [placeWithNames.eq_def]
  dsimp only
  rw [ownerPlace]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rw [typed, descriptor]
  rfl


/-- sizeof consults its retained type provider without evaluating the operand,
reading a name or calling a source function. -/
theorem size_retains_unevaluated_operand (names : NameReads) (calls : Calls)
    (layout : Layout) (objects : ObjectReads) (operand : CExpr) (value : CVal)
    (sized : objects.size (.sizeOfExpr operand) = some value) :
    expressionWithNames names calls layout (.sizeOfExpr operand) objects = pure value := by
  simp only [expressionWithNames.eq_def, sized, resolved]

/-- Unsupported sizeof has no invented default size. -/
theorem default_size_is_not_invented (names : NameReads) (calls : Calls)
    (layout : Layout) (operand : CExpr) :
    expressionWithNames names calls layout (.sizeOfExpr operand) = CProg.undefined := rfl

/-- Addressing a supplied local object does not perform an rvalue read. -/
theorem supplied_object_address_skips_rvalue (names : NameReads) (calls : Calls)
    (layout : Layout) (name : Name) (address : Ptr) :
    expressionWithNames names calls layout (.unary .address (.identifier name))
      { place := some (fun _ => some address) } = pure (.ptr (some address)) := rfl

/-- An object provider does not force an unchosen operand. -/
theorem object_profile_false_and_skips_operand (names : NameReads) (calls : Calls)
    (layout : Layout) (objects : ObjectReads) (operand : CExpr) :
    expressionWithNames names calls layout (.binary .and (.bool false) operand) objects =
      pure (.bool false) := rfl

/-- Immutable local values retain their original public interpreter profile. -/
def expressionWith (calls : Calls) (layout : Layout) (environment : Environment)
    (operand : CExpr) : CProg CVal CVal :=
  expressionWithNames (fun name => resolved (environment name)) calls layout operand

def argumentsWith (calls : Calls) (layout : Layout) (environment : Environment)
    (arguments : List CExpr) : CProg CVal (List CVal) :=
  argumentsWithNames (fun name => resolved (environment name)) calls layout arguments

/-- The existing expression equation remains the API of the immutable-local profile. -/
theorem expressionWith_equation (calls : Calls) (layout : Layout) (environment : Environment)
    (operand : CExpr) : expressionWith calls layout environment operand = (match operand with
  | .identifier name => resolved (environment name)
  | .decimal value => resolved ((ScalarRead.signedDecimal? value).bind cell?)
  | .unsignedInteger value =>
      resolved (if value < 2 ^ 32 then some (.u32 (UInt32.ofNat value)) else none)
  | .word value => pure (.u64 (UInt64.ofNat value.toNat))
  | .bool value => pure (.bool value)
  | .null => pure (.ptr none)
  | .call name arguments => do
      let values ← argumentsWith calls layout environment arguments
      calls name values
  | .unary .address (.field record name true) => do
      let owner ← expressionWith calls layout environment record
      let address ← fieldAddress layout owner name
      pure (.ptr (some address))
  | .unary .negate operand => do
      let value ← expressionWith calls layout environment operand
      negate value
  | .unary .not operand => do
      let value ← expressionWith calls layout environment operand
      let selected ← truth value
      pure (.bool (!selected))
  | .field record name true => do
      let owner ← expressionWith calls layout environment record
      field layout owner name
  | .index array index => do
      let address ← expressionWith calls layout environment array
      let position ← expressionWith calls layout environment index
      indexed address position
  | .binary .and left right => do
      let first ← expressionWith calls layout environment left
      let selected ← truth first
      if selected then do
        let second ← expressionWith calls layout environment right
        let selectedSecond ← truth second
        pure (.bool selectedSecond)
      else pure (.bool false)
  | .binary .or left right => do
      let first ← expressionWith calls layout environment left
      let selected ← truth first
      if selected then pure (.bool true) else do
        let second ← expressionWith calls layout environment right
        let selectedSecond ← truth second
        pure (.bool selectedSecond)
  | .binary operator left right => do
      let first ← expressionWith calls layout environment left
      let second ← expressionWith calls layout environment right
      binary operator first second
  | .conditional condition yes no => do
      let value ← expressionWith calls layout environment condition
      let selected ← truth value
      if selected then expressionWith calls layout environment yes else expressionWith calls layout environment no
  | _ => CProg.undefined) := by
  cases operand <;> try rfl
  case unary operator operand =>
    cases operator <;> try rfl
    case address =>
      cases operand <;> try rfl
      case field record name throughPointer => cases throughPointer <;> rfl
  case binary operator left right => cases operator <;> rfl
  case field record name throughPointer => cases throughPointer <;> rfl

theorem argumentsWith_equation (calls : Calls) (layout : Layout) (environment : Environment)
    (arguments : List CExpr) : argumentsWith calls layout environment arguments = (match arguments with
  | [] => pure []
  | argument :: rest => do
      let first ← expressionWith calls layout environment argument
      let others ← argumentsWith calls layout environment rest
      pure (first :: others)) := by
  cases arguments <;> rfl

theorem arguments_with_mapM (calls : Calls) (layout : Layout)
    (environment : Environment) (arguments : List CExpr) :
    argumentsWith calls layout environment arguments =
      arguments.mapM (expressionWith calls layout environment) := by
  induction arguments with
  | nil => rfl
  | cons argument rest ih =>
      rw [argumentsWith_equation, List.mapM_cons]
      dsimp only
      rw [ih]

/-- The default profile admits no foreign calls. Its public argument types
remain those of the original physical expression reader. -/
def expression (layout : Layout) (environment : Environment) (operand : CExpr) : CProg CVal CVal :=
  expressionWith noCalls layout environment operand

/-- Scalar field stores check the actual value tag against the admitted field
before writing. Embedded aggregates are addressable but not scalar-writable. -/
def storeField (layout : Layout) (owner : CVal) (name : Name) (value : CVal) :
    CProg CVal Unit := do
  let descriptor ← resolved (layout name)
  if descriptor.kind = valueKind value then do
    let address ← fieldAddress layout owner name
    CProg.store address value
  else CProg.undefined


theorem cell_scalar (value : CVal) : cell? (scalar value) = some value := by
  cases value <;> rfl

theorem undefined_bind {α β : Type} (next : α → CProg CVal β) :
    (CProg.undefined >>= next) = CProg.undefined := by
  simp only [CProg.undefined, Prog.bind_eq, Prog.call_bind]
  congr 1
  funext impossible
  cases impossible

theorem field_address_retains_offset (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (kind : FieldKind) (selected : layout name = some ⟨offset, kind⟩) :
    fieldAddress layout (.ptr (some owner)) name = pure (owner + offset) := by
  simp only [fieldAddress, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, selected]

theorem field_store_retains_actual_value (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (value : CVal) (selected : layout name = some ⟨offset, valueKind value⟩) :
    storeField layout (.ptr (some owner)) name value = CProg.store (owner + offset) value := by
  simp only [storeField, selected, resolved, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, if_true]
  rw [field_address_retains_offset layout owner name offset (valueKind value) selected]
  rfl

theorem call_retains_ordered_arguments (calls : Calls) (layout : Layout)
    (environment : Environment) (name : Name) (arguments : List CExpr) :
    expressionWith calls layout environment (.call name arguments) =
      (argumentsWith calls layout environment arguments >>= calls name) := by
  rw [expressionWith_equation]

theorem embedded_field_is_not_a_scalar_read (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (selected : layout name = some ⟨offset, .embedded⟩) :
    field layout (.ptr (some owner)) name = CProg.undefined := by
  simp only [field, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, selected]

theorem embedded_field_is_not_a_scalar_store (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (value : CVal) (selected : layout name = some ⟨offset, .embedded⟩) :
    storeField layout (.ptr (some owner)) name value = CProg.undefined := by
  cases value <;>
    simp only [storeField, selected, resolved, valueKind, Prog.pure_eq, Prog.bind_eq,
      Prog.ret_bind, reduceCtorEq, if_false]

theorem pointer_equality_is_primitive (left right : Option Ptr) :
    equal (.ptr left) (.ptr right) = CProg.ptrEq left right := rfl

theorem pointer_truth_is_primitive (value : Option Ptr) :
    truth (.ptr value) = (CProg.ptrEq value none >>= fun isNull => pure (!isNull)) := rfl

theorem pointer_field_uses_actual_offset (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (selected : layout name = some ⟨offset, .pointer⟩) :
    field layout (.ptr (some owner)) name =
      (CProg.loadPtr (owner + offset) >>= fun value => pure (.ptr value)) := by
  simp only [field, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, selected]

theorem word_field_uses_actual_offset (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (selected : layout name = some ⟨offset, .word⟩) :
    field layout (.ptr (some owner)) name =
      (CProg.loadU32 (owner + offset) >>= fun value => pure (.u32 value)) := by
  simp only [field, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, selected]

theorem signed_field_uses_actual_offset (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (selected : layout name = some ⟨offset, .signedWord⟩) :
    field layout (.ptr (some owner)) name =
      (CProg.loadI32 (owner + offset) >>= fun value => pure (.i32 value)) := by
  simp only [field, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, selected]

theorem word64_field_uses_actual_offset (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (selected : layout name = some ⟨offset, .word64⟩) :
    field layout (.ptr (some owner)) name =
      (CProg.loadU64 (owner + offset) >>= fun value => pure (.u64 value)) := by
  simp only [field, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, selected]

/-- Boolean fields retain the typed heap load at their actual descriptor
rather than accepting an arbitrary scalar as a truth value. -/
theorem boolean_field_uses_actual_offset (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (selected : layout name = some ⟨offset, .boolean⟩) :
    field layout (.ptr (some owner)) name =
      (CProg.loadBool (owner + offset) >>= fun value => pure (.bool value)) := by
  simp only [field, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, selected]

/-- A nullable owner does not acquire storage by selecting a field descriptor. -/
theorem null_owner_field_is_undefined (layout : Layout) (name : Name) :
    field layout (.ptr none) name = CProg.undefined := by
  simp only [field, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]

theorem index_uses_actual_pointer_and_word (array : Ptr) (index : UInt32) :
    indexed (.ptr (some array)) (.u32 index) =
      (CProg.loadPtr (array + index.toNat) >>= fun value => pure (.ptr value)) := rfl

theorem false_and_skips_arbitrary_operand (layout : Layout) (environment : Environment)
    (operand : CExpr) :
    expression layout environment (.binary .and (.bool false) operand) =
      pure (.bool false) := rfl

theorem true_or_skips_arbitrary_operand (layout : Layout) (environment : Environment)
    (operand : CExpr) :
    expression layout environment (.binary .or (.bool true) operand) =
      pure (.bool true) := rfl

theorem conditional_false_retains_selected_operand (layout : Layout)
    (environment : Environment) (yes no : CExpr) :
    expression layout environment (.conditional (.bool false) yes no) =
      expression layout environment no := rfl

theorem conditional_true_retains_selected_operand (layout : Layout)
    (environment : Environment) (yes no : CExpr) :
    expression layout environment (.conditional (.bool true) yes no) =
      expression layout environment yes := rfl

section Preservation

open Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

/-- Field stores use the existing physical footprint and frame rule; the
descriptor supplies the actual offset and matching scalar kind. -/
theorem field_store_rule (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (value : CVal)
    (selected : layout name = some ⟨offset, valueKind value⟩) :
    CTriple (L := L) (PointsToAny (owner + offset))
      (storeField layout (.ptr (some owner)) name value)
      (fun _ => PointsTo (owner + offset) value) := by
  rw [field_store_retains_actual_value layout owner name offset value selected]
  exact store_spec (owner + offset) value

/-- Every completed execution retains the same physical heap. This property
does not assert safety, progress, or that the returned observation is current. -/
def ReadOnly {α : Type} (program : CProg CVal α) : Prop :=
  ∀ (σ : Heap L) value σ', program.Runs act σ value σ' → σ' = σ

theorem pure_readOnly {α : Type} (value : α) :
    ReadOnly (L := L) (pure value : CProg CVal α) := by
  intro σ result σ' runs
  exact runs.2.symm

theorem undefined_readOnly {α : Type} :
    ReadOnly (L := L) (CProg.undefined : CProg CVal α) := by
  rintro σ value σ' ⟨_, _, impossible, _⟩
  exact False.elim impossible

theorem bind_readOnly {α β : Type} (first : CProg CVal α)
    (next : α → CProg CVal β) (firstReadOnly : ReadOnly (L := L) first)
    (nextReadOnly : ∀ value, ReadOnly (L := L) (next value)) :
    ReadOnly (L := L) (first >>= next) := by
  intro σ result σ' runs
  obtain ⟨value, between, firstRuns, nextRuns⟩ := (Prog.runs_bind _ _ _ _ _ _).mp runs
  exact (nextReadOnly value between result σ' nextRuns).trans
    (firstReadOnly σ value between firstRuns)

theorem load_readOnly (address : Ptr) :
    ReadOnly (L := L) (CProg.load (V := CVal) address) := by
  rintro σ value σ' ⟨loaded, between, ⟨_, same⟩, _, resultSame⟩
  exact resultSame.symm.trans same

theorem pointer_comparison_readOnly (left right : Option Ptr) :
    ReadOnly (L := L) (CProg.ptrEq (V := CVal) left right) := by
  rintro σ value σ' ⟨loaded, between, ⟨_, same⟩, _, resultSame⟩
  exact resultSame.symm.trans same

theorem load_pointer_readOnly (address : Ptr) :
    ReadOnly (L := L) (CProg.loadPtr address) := by
  apply bind_readOnly _ _ (load_readOnly address)
  intro value
  cases value <;> first | exact pure_readOnly _ | exact undefined_readOnly

theorem load_word_readOnly (address : Ptr) :
    ReadOnly (L := L) (CProg.loadU32 address) := by
  apply bind_readOnly _ _ (load_readOnly address)
  intro value
  cases value <;> first | exact pure_readOnly _ | exact undefined_readOnly

theorem load_signed_readOnly (address : Ptr) :
    ReadOnly (L := L) (CProg.loadI32 address) := by
  apply bind_readOnly _ _ (load_readOnly address)
  intro value
  cases value <;> first | exact pure_readOnly _ | exact undefined_readOnly

theorem load_word64_readOnly (address : Ptr) :
    ReadOnly (L := L) (CProg.loadU64 address) := by
  apply bind_readOnly _ _ (load_readOnly address)
  intro value
  cases value <;> first | exact pure_readOnly _ | exact undefined_readOnly


/-- One shared field-read rule covers each admitted scalar. The precondition
names an actual readable cell at the descriptor offset, not a field oracle. -/
theorem field_read_rule (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (value : CVal) {P : Heap L → Prop}
    (selected : layout name = some ⟨offset, valueKind value⟩)
    (reads : ∀ σ, P σ →
      CellPermission.read ((σ (owner + offset).block).2 (owner + offset).offset) =
        some (some value)) :
    CTriple P (field layout (.ptr (some owner)) name)
      (fun result σ => result = value ∧ P σ) := by
  cases value <;> simp only [valueKind] at selected
  all_goals
    simp only [field, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, selected]
    first
      | refine triple_bind _ (loadBool_rule reads) ?_
      | refine triple_bind _ (loadI32_rule reads) ?_
      | refine triple_bind _ (loadU32_rule reads) ?_
      | refine triple_bind _ (loadU64_rule reads) ?_
      | refine triple_bind _ (loadPtr_rule reads) ?_
    intro actual
    apply triple_pure
    intro same
    subst actual
    exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)

/-- A source identifier is resolved once; its retained field AST is then read
through the same physical cell contract. -/
theorem expression_field_read_rule (layout : Layout) (environment : Environment)
    (localName fieldName : Name) (owner : Ptr) (offset : Nat) (value : CVal)
    {P : Heap L → Prop}
    (localRead : environment localName = some (.ptr (some owner)))
    (selected : layout fieldName = some ⟨offset, valueKind value⟩)
    (reads : ∀ σ, P σ →
      CellPermission.read ((σ (owner + offset).block).2 (owner + offset).offset) =
        some (some value)) :
    CTriple P (expression layout environment
      (.field (.identifier localName) fieldName true))
      (fun result σ => result = value ∧ P σ) := by
  simp only [expression, expressionWith_equation, localRead, resolved, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  exact field_read_rule layout owner fieldName offset value selected reads

/-- A wide cell behind a narrow descriptor cannot become a successful read by
truncating its value. -/
theorem narrow_descriptor_of_wide_cell_is_unsafe (layout : Layout)
    (owner : Ptr) (name : Name) (offset : Nat) (value : UInt64) (σ : Heap L)
    (selected : layout name = some ⟨offset, .word⟩)
    (holds : CellPermission.read
      ((σ (owner + offset).block).2 (owner + offset).offset) = some (some (.u64 value))) :
    ¬ (field layout (.ptr (some owner)) name).Safe act σ := by
  rw [word_field_uses_actual_offset layout owner name offset selected]
  intro safe
  exact CMemory.Controls.loadU32_of_u64_undefined (owner + offset) value σ holds
    ((Prog.safe_bind _ _ _ _).mp safe).1

theorem unsigned_descriptor_of_signed_cell_is_unsafe (layout : Layout)
    (owner : Ptr) (name : Name) (offset : Nat) (value : Int32) (σ : Heap L)
    (selected : layout name = some ⟨offset, .word⟩)
    (holds : CellPermission.read
      ((σ (owner + offset).block).2 (owner + offset).offset) = some (some (.i32 value))) :
    ¬ (field layout (.ptr (some owner)) name).Safe act σ := by
  rw [word_field_uses_actual_offset layout owner name offset selected]
  intro safe
  exact CMemory.Controls.loadU32_of_i32_undefined (owner + offset) value σ holds
    ((Prog.safe_bind _ _ _ _).mp safe).1

theorem signed_descriptor_of_unsigned_cell_is_unsafe (layout : Layout)
    (owner : Ptr) (name : Name) (offset : Nat) (value : UInt32) (σ : Heap L)
    (selected : layout name = some ⟨offset, .signedWord⟩)
    (holds : CellPermission.read
      ((σ (owner + offset).block).2 (owner + offset).offset) = some (some (.u32 value))) :
    ¬ (field layout (.ptr (some owner)) name).Safe act σ := by
  rw [signed_field_uses_actual_offset layout owner name offset selected]
  intro safe
  exact CMemory.Controls.loadI32_of_u32_undefined (owner + offset) value σ holds
    ((Prog.safe_bind _ _ _ _).mp safe).1

/-- A retained predicate is lifted through a read-only program's actual
executions. In particular this preserves well-formedness, without postulating
it anew after every typed load. -/
theorem triple_preserves_predicate {α : Type} {P R : Heap L → Prop}
    {Q : α → Heap L → Prop} {program : CProg CVal α}
    (readOnly : ReadOnly (L := L) program) (spec : CTriple P program Q) :
    CTriple (fun σ => R σ ∧ P σ) program (fun result σ => R σ ∧ Q result σ) := by
  intro σ holds
  refine ⟨(spec σ holds.2).1, ?_⟩
  intro result σ' runs
  exact ⟨(readOnly σ result σ' runs).symm ▸ holds.1, (spec σ holds.2).2 result σ' runs⟩

end Preservation

universe u

def operands (layout : Layout) (environment : Environment)
    (terms : List CExpr) : CProg CVal (List CVal) :=
  terms.mapM (expression layout environment)

def environmentView (environment : Environment) : ScalarRead.Environment Ptr :=
  fun name => (environment name).map scalar

section Physical

open Mettapedia.GSLT.SeparationAlgebra

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

/-- The readout comes from permission-bearing cells. A descriptor cannot
reinterpret a different stored scalar type. -/
def fieldView (layout : Layout) (heap : Heap L) : ScalarRead.FieldReader Ptr :=
  fun owner name => do
    let descriptor ← layout name
    let stored ← CellPermission.read
      ((heap (owner + descriptor.offset).block).2 (owner + descriptor.offset).offset)
    let value ← stored
    if valueKind value = descriptor.kind then some (scalar value) else none

theorem field_view_of_read (layout : Layout) (heap : Heap L) (owner : Ptr)
    (name : Name) (offset : Nat) (value : CVal)
    (selected : layout name = some ⟨offset, valueKind value⟩)
    (reads : CellPermission.read
      ((heap (owner + offset).block).2 (owner + offset).offset) = some (some value)) :
    fieldView layout heap owner name = some (scalar value) := by
  simp only [fieldView, selected, bind, Option.bind, reads, if_true]

/-- Sequencing actual operand readers retains their order and the common
heap predicate. This is a rule about the supplied programs, not an oracle
for their results. -/
theorem operands_read_rule (layout : Layout) (environment : Environment)
    {P : Heap L → Prop} {terms : List CExpr} {values : List CVal}
    (reads : List.Forall₂ (fun term value =>
      CTriple P (expression layout environment term)
        (fun result heap => result = value ∧ P heap)) terms values) :
    CTriple P (operands layout environment terms)
      (fun result heap => result = values ∧ P heap) := by
  induction reads with
  | nil =>
      exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)
  | @cons term value terms values first rest ih =>
      simp only [operands, List.mapM_cons]
      refine triple_bind _ first fun actual => ?_
      apply triple_pure
      intro same
      subst actual
      refine triple_bind _ ih fun actualTail => ?_
      apply triple_pure
      intro same
      subst actualTail
      exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)

theorem field_view_rejects_wrong_cell_type (layout : Layout) (heap : Heap L)
    (owner : Ptr) (name : Name) (offset : Nat) (value : CVal) (kind : FieldKind)
    (selected : layout name = some ⟨offset, kind⟩)
    (reads : CellPermission.read
      ((heap (owner + offset).block).2 (owner + offset).offset) = some (some value))
    (different : valueKind value ≠ kind) :
    fieldView layout heap owner name = none := by
  simp only [fieldView, selected, bind, Option.bind, reads, if_neg different]

theorem missing_layout_is_not_a_field_value (layout : Layout) (heap : Heap L)
    (owner : Ptr) (name : Name) (missing : layout name = none) :
    fieldView layout heap owner name = none := by
  simp only [fieldView, missing, bind, Option.bind]

end Physical


namespace Controls

def emptyLayout : Layout := fun _ => none
def emptyEnvironment : Environment := fun _ => none

theorem missing_local_is_undefined :
    expression emptyLayout emptyEnvironment (.identifier "missing".toList) =
      CProg.undefined := rfl

theorem unsupported_call_is_not_executed :
    expression emptyLayout emptyEnvironment (.call "sideEffect".toList []) =
      CProg.undefined := rfl

theorem null_array_is_not_empty_success (index : UInt32) :
    indexed (.ptr none) (.u32 index) = CProg.undefined := rfl

theorem wrong_index_type_is_not_repaired (array : Ptr) :
    indexed (.ptr (some array)) (.bool false) = CProg.undefined := by
  simp only [indexed, pointer, word, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  exact undefined_bind _

theorem unknown_field_is_not_guessed (owner : Ptr) :
    field emptyLayout (.ptr (some owner)) "missing".toList = CProg.undefined := rfl

theorem oversized_unsigned_constant_is_not_narrowed :
    expression emptyLayout emptyEnvironment (.unsignedInteger (2 ^ 32)) =
      CProg.undefined := rfl

theorem wide_scalar_is_not_narrowed (value : UInt64) :
    cell? (.unsigned64 value) = some (.u64 value) := rfl

theorem inline_record_is_not_a_physical_cell (fields : List (Name × UInt64)) :
    cell? (.wordRecord fields) = none := rfl

theorem supported_cell_retains_its_width (value : UInt32) :
    cell? (.unsigned value) = some (.u32 value) := rfl

theorem wide_index_is_not_narrowed (array : Ptr) (index : UInt64) :
    indexed (.ptr (some array)) (.u64 index) = CProg.undefined := by
  simp only [indexed, pointer, word, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  exact undefined_bind _

theorem wide_nonzero_truth_is_retained :
    truth (.u64 4294967296) = pure true := rfl

theorem full_word_literal_is_retained :
    expression emptyLayout emptyEnvironment (.word 18446744073709551615) =
      pure (.u64 18446744073709551615) := rfl

theorem mixed_unsigned_addition_retains_wide_result :
    expression emptyLayout emptyEnvironment
      (.binary .add (.word 4294967296) (.unsignedInteger 1)) =
      pure (.u64 4294967297) := rfl

theorem narrow_unsigned_addition_still_wraps :
    expression emptyLayout emptyEnvironment
      (.binary .add (.unsignedInteger 4294967295) (.unsignedInteger 1)) =
      pure (.u32 0) := rfl

theorem mixed_unsigned_order_retains_high_bits :
    expression emptyLayout emptyEnvironment
      (.binary .lt (.word 4294967296) (.unsignedInteger 1)) =
      pure (.bool false) := rfl

theorem unary_minus_reads_signed_decimal :
    expression emptyLayout emptyEnvironment (.unary .negate (.decimal 1)) =
      pure (.i32 (-1)) := rfl

theorem unary_minus_does_not_wrap_signed_minimum :
    expression emptyLayout (fun _ => some (.i32 (-2147483648)))
      (.unary .negate (.identifier ['x'])) = CProg.undefined := rfl

theorem oversized_signed_decimal_is_not_narrowed :
    expression emptyLayout emptyEnvironment (.decimal (2 ^ 31)) = CProg.undefined := rfl

theorem unary_minus_does_not_reinterpret_pointer :
    expression emptyLayout (fun _ => some (.ptr (some ⟨1, 0⟩)))
      (.unary .negate (.identifier ['x'])) = CProg.undefined := rfl

end Controls

namespace NamedReadControls

def emptyEnvironment : Environment := fun _ => none
def emptyLayout : Layout := fun _ => none

theorem resolved_local_shields_arbitrary_reads (environment : Environment)
    (declared : Name → Bool) (locations : Locations) (name : Name) (value : CVal)
    (present : environment name = some value) :
    expressionWithNames (localOrLocated environment declared locations) noCalls emptyLayout
      (.identifier name) = pure value := by
  simp only [expressionWithNames.eq_def, localOrLocated, present]

theorem uninitialized_local_does_not_read_global (name : Name) (locations : Locations) :
    expressionWithNames (localOrLocated emptyEnvironment (fun _ => true) locations)
      noCalls emptyLayout (.identifier name) = CProg.undefined := rfl

theorem pointer_name_is_a_current_load (name : Name) (address : Ptr) :
    expressionWithNames (localOrLocated emptyEnvironment (fun _ => false)
      (fun _ => some (address, .pointer))) noCalls emptyLayout (.identifier name) =
      (CProg.loadPtr address >>= fun value => pure (.ptr value)) := by
  have zero : address + 0 = address := by cases address; rfl
  simp [expressionWithNames.eq_def, localOrLocated, emptyEnvironment,
    located, field, pointer, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, zero]

theorem preceding_store_does_not_freeze_name (name : Name) (address : Ptr) (value : Option Ptr) :
    (CProg.store address (.ptr value) >>= fun _ =>
      expressionWithNames (localOrLocated emptyEnvironment (fun _ => false)
        (fun _ => some (address, .pointer))) noCalls emptyLayout (.identifier name)) =
      (CProg.store address (.ptr value) >>= fun _ =>
        CProg.loadPtr address >>= fun value => pure (.ptr value)) := by
  rw [pointer_name_is_a_current_load]

theorem false_branch_does_not_resolve_sibling (names : NameReads) (name : Name) :
    expressionWithNames names noCalls emptyLayout
      (.conditional (.bool false) (.identifier name) (.bool true)) = pure (.bool true) := rfl

theorem missing_location_is_not_a_source_function_call (name : Name) (calls : Calls) :
    expressionWithNames (localOrLocated emptyEnvironment (fun _ => false) (fun _ => none))
      calls emptyLayout (.identifier name) = CProg.undefined := rfl

section PhysicalReadout

open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

/-- The live typed cell supplies the current pointer value and retains its
permission. This is a physical read contract, not a cached-value readout. -/
theorem pointer_name_reads_owned_cell (name : Name) (address : Ptr) (value : Option Ptr) :
    CTriple (L := L) (PointsTo address (.ptr value))
      (expressionWithNames (localOrLocated emptyEnvironment (fun _ => false)
        (fun _ => some (address, .pointer))) noCalls emptyLayout (.identifier name))
      (fun result heap => result = .ptr value ∧ PointsTo address (.ptr value) heap) := by
  rw [pointer_name_is_a_current_load]
  simp only [Prog.bind_eq, Prog.pure_eq]
  apply triple_bind _ (loadPtr_rule (L := L) (P := PointsTo address (.ptr value))
    (p := address) (q := value) ?_)
  · intro actual
    apply triple_pure
    intro same
    subst actual
    exact triple_pre _ (fun _ held => ⟨rfl, held⟩)
      (triple_ret _ (CVal.ptr value)
        (fun result heap => result = CVal.ptr value ∧ PointsTo address (CVal.ptr value) heap))
  · intro heap held
    apply read_of_pointsTo (F := emp)
    simpa only [sepConj_emp] using held

/-- Storing before a source name read changes its returned value while
preserving the same owned cell. No read is moved across that store. -/
theorem pointer_name_observes_preceding_store (name : Name) (address : Ptr) (value : Option Ptr) :
    CTriple (L := L) (PointsToAny address)
      (CProg.store address (.ptr value) >>= fun _ =>
        expressionWithNames (localOrLocated emptyEnvironment (fun _ => false)
          (fun _ => some (address, .pointer))) noCalls emptyLayout (.identifier name))
      (fun result heap => result = .ptr value ∧ PointsTo address (.ptr value) heap) := by
  simp only [Prog.bind_eq]
  apply triple_bind _ (store_spec (L := L) address (.ptr value))
  intro ignored
  exact pointer_name_reads_owned_cell name address value

/-- A snapshot of an earlier value has a different operation tree from a
current read, even when both eventually happen to print equal values. -/
theorem snapshot_is_not_current_name_read (name : Name) (address : Ptr) (value : Option Ptr) :
    expressionWithNames (localOrLocated emptyEnvironment (fun _ => false)
      (fun _ => some (address, .pointer))) noCalls emptyLayout (.identifier name) ≠
      pure (.ptr value) := by
  rw [pointer_name_is_a_current_load]
  intro equality
  cases equality

end PhysicalReadout

end NamedReadControls

/-- A static descriptor selects the typed load after both authored operands
have been evaluated in their original order. It supplies no value oracle. -/
theorem described_index_keeps_operands (names : NameReads) (calls : Calls) (layout : Layout)
    (objects : ObjectReads) (array index : CExpr) (kinds : CExpr → Option FieldKind)
    (kind : FieldKind) (provided : objects.indexKind = some kinds)
    (described : kinds array = some kind) :
    expressionWithNames names calls layout (.index array index) objects =
      (expressionWithNames names calls layout array objects >>= fun address =>
        expressionWithNames names calls layout index objects >>= fun position =>
          indexedScalar kind address position) := by
  rw [expressionWithNames.eq_def]
  simp only [provided, described]

/-- Missing static element information is not guessed from the returned
array value. Earlier operand effects remain part of the source reading. -/
theorem missing_index_descriptor_is_not_guessed (names : NameReads) (calls : Calls)
    (layout : Layout) (objects : ObjectReads) (array index : CExpr)
    (kinds : CExpr → Option FieldKind) (provided : objects.indexKind = some kinds)
    (missing : kinds array = none) :
    expressionWithNames names calls layout (.index array index) objects =
      (expressionWithNames names calls layout array objects >>= fun _ =>
        expressionWithNames names calls layout index objects >>= fun _ => CProg.undefined) := by
  rw [expressionWithNames.eq_def]
  simp only [provided, missing]

/-! ## Explicit scalar-array controls -/

theorem indexed_word64_keeps_full_index (array : Ptr) (index : UInt64) :
    indexedScalar .word64 (.ptr (some array)) (.u64 index) =
      (CProg.loadU64 (array + index.toNat) >>= fun value => pure (.u64 value)) := rfl

theorem indexed_word64_keeps_narrow_index (array : Ptr) (index : UInt32) :
    indexedScalar .word64 (.ptr (some array)) (.u32 index) =
      (CProg.loadU64 (array + index.toNat) >>= fun value => pure (.u64 value)) := rfl

theorem indexed_pointer_keeps_full_index (array : Ptr) (index : UInt64) :
    indexedScalar .pointer (.ptr (some array)) (.u64 index) =
      (CProg.loadPtr (array + index.toNat) >>= fun value => pure (.ptr value)) := rfl

theorem indexed_signed_index_is_not_guessed (array : Ptr) (index : Int32) (kind : FieldKind) :
    indexedScalar kind (.ptr (some array)) (.i32 index) = CProg.undefined := by
  simp only [indexedScalar, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  exact undefined_bind _

theorem indexed_null_array_is_not_loaded (index : UInt64) (kind : FieldKind) :
    indexedScalar kind (.ptr none) (.u64 index) = CProg.undefined := rfl

theorem indexed_embedded_value_is_not_a_scalar (array : Ptr) (index : UInt64) :
    indexedScalar .embedded (.ptr (some array)) (.u64 index) = CProg.undefined := rfl

end Mettapedia.Machines.CMemory.ReadExpressions
