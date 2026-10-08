import Mettapedia.GSLT.LanguageDef.ModuleFormat.Value

/-!
# The public `module/1` envelope

The structural decoder follows `mettail-elab/src/module.rs` at commit
`8c1bb3b0ef3890406e375c2c5387dc9a3cdf0439`. Export specifications are retained
whole. Language admission, execution, cryptographic trust and host resource
admission are separate from this envelope's name/reference/schema checks.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

structure Dependency where
  reference : ModuleRef
  commitment : List UInt8
  deriving Repr, DecidableEq

structure Export where
  name : String
  spec : Value
  deriving Repr, DecidableEq

structure RawModule where
  name : String
  dependencies : List Dependency
  exports : List Export
  deriving Repr, DecidableEq

/-- Envelope collection limits are explicit policy, separate from the schema. -/
structure Limits where
  dependencies : Nat
  exports : Nat
  deriving Repr, DecidableEq

/-- Collection admission in the pinned upstream envelope decoder. -/
def upstreamLimits : Limits := ⟨256, 1024⟩

def Dependency.Valid (dependency : Dependency) : Prop :=
  dependency.reference.valid ∧ dependency.commitment.length = 32

instance (dependency : Dependency) : Decidable dependency.Valid :=
  by
  unfold Dependency.Valid
  infer_instance

/-- The specification remains opaque at envelope admission. -/
def Export.Valid (entry : Export) : Prop := identifier entry.name = true

instance (entry : Export) : Decidable entry.Valid :=
  by
  unfold Export.Valid
  infer_instance

/-- An independent schema specification, rather than acceptance defined by
running the decoder. Dependencies use parsed references for duplicate checks. -/
def RawModule.Valid (limits : Limits) (module : RawModule) : Prop :=
  identifier module.name = true ∧
    module.dependencies.length ≤ limits.dependencies ∧
    (∀ dependency ∈ module.dependencies, dependency.Valid) ∧
    (module.dependencies.map Dependency.reference).Nodup ∧
    module.exports ≠ [] ∧
    module.exports.length ≤ limits.exports ∧
    (∀ entry ∈ module.exports, entry.Valid) ∧
    (module.exports.map Export.name).Nodup

instance (limits : Limits) (module : RawModule) : Decidable (module.Valid limits) :=
  by
  unfold RawModule.Valid
  infer_instance

abbrev Module (limits : Limits) := { module : RawModule // module.Valid limits }

def encodeDependency (dependency : Dependency) : Value := .record [
  ("commitment", .bytes dependency.commitment),
  ("uri", .string dependency.reference.external)]

def encodeExport (entry : Export) : Value := .record [
  ("name", .string entry.name), ("spec", entry.spec)]

/-- Sorted record keys agree with the upstream BTreeMap projection; dependency
and export vectors retain their authored order. -/
def encodeRaw (module : RawModule) : Value := .record [
  ("dependencies", .list (module.dependencies.map encodeDependency)),
  ("exports", .list (module.exports.map encodeExport)),
  ("mettail", .string "module/1"),
  ("name", .string module.name)]

def decodeDependency? (value : Value) : Option Dependency := do
  let fields ← value.record? ["commitment", "uri"]
  let uri ← Value.field? fields "uri" >>= Value.string?
  let reference ← ModuleRef.parse? uri
  let commitment ← Value.field? fields "commitment" >>= Value.bytes?
  pure ⟨reference, commitment⟩

def decodeExport? (value : Value) : Option Export := do
  let fields ← value.record? ["name", "spec"]
  let name ← Value.field? fields "name" >>= Value.string?
  let spec ← Value.field? fields "spec"
  pure ⟨name, spec⟩

/-- Decode the structural envelope before checking its declaration invariants. -/
def decodeRaw? (value : Value) : Option RawModule := do
  let fields ← value.record? ["dependencies", "exports", "mettail", "name"]
  let schema ← Value.field? fields "mettail" >>= Value.string?
  if schema ≠ "module/1" then none else do
    let name ← Value.field? fields "name" >>= Value.string?
    let dependencyValues ← Value.field? fields "dependencies" >>= Value.list?
    let dependencies ← dependencyValues.mapM decodeDependency?
    let exportValues ← Value.field? fields "exports" >>= Value.list?
    let exports ← exportValues.mapM decodeExport?
    pure ⟨name, dependencies, exports⟩

def decode? (limits : Limits) (value : Value) : Option (Module limits) := do
  let module ← decodeRaw? value
  if accepted : module.Valid limits then some ⟨module, accepted⟩ else none

@[simp] theorem decode_encodeExport (entry : Export) :
    decodeExport? (encodeExport entry) = some entry := by
  cases entry
  simp [decodeExport?, encodeExport, Value.record?, Value.field?, Value.string?]

@[simp] theorem decode_encodeDependency (dependency : Dependency)
    (accepted : dependency.reference.valid) :
    decodeDependency? (encodeDependency dependency) = some dependency := by
  cases dependency with
  | mk reference commitment =>
      simp [decodeDependency?, encodeDependency, Value.record?, Value.field?, Value.string?, Value.bytes?,
        ModuleRef.parse_external reference accepted]

theorem mapM_encode_decode {α : Type} (encode : α → Value)
    (decode : Value → Option α) (values : List α)
    (roundtrip : ∀ value ∈ values, decode (encode value) = some value) :
    (values.map encode).mapM decode = some values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [List.map_cons, List.mapM_cons]
      rw [roundtrip value (by simp), ih (fun item member => roundtrip item (by simp [member]))]
      rfl

theorem decode_encodeRaw (module : RawModule)
    (references : ∀ dependency ∈ module.dependencies, dependency.reference.valid) :
    decodeRaw? (encodeRaw module) = some module := by
  have dependencies := mapM_encode_decode encodeDependency decodeDependency?
    module.dependencies (fun dependency member =>
      decode_encodeDependency dependency (references dependency member))
  have exports := mapM_encode_decode encodeExport decodeExport? module.exports
    (fun entry _ => decode_encodeExport entry)
  cases module
  simp [decodeRaw?, encodeRaw, Value.record?, Value.field?, Value.string?, Value.list?, dependencies, exports]

/-- Exact quotation for every independently admitted module, including all
opaque export payloads and dependency commitments. -/
@[simp] theorem decode_encode (limits : Limits) (module : Module limits) :
    decode? limits (encodeRaw module.val) = some module := by
  have references : ∀ dependency ∈ module.val.dependencies,
      dependency.reference.valid := fun dependency member =>
    (module.property.2.2.1 dependency member).1
  simp [decode?, decode_encodeRaw module.val references, module.property]

/-- Successful decoding entails the separate structural decoder and every
schema constraint. It does not imply language or execution admission. -/
theorem decode_some_iff (limits : Limits) (value : Value) (module : Module limits) :
    decode? limits value = some module ↔ decodeRaw? value = some module.val := by
  unfold decode?
  cases raw : decodeRaw? value with
  | none => simp
  | some parsed =>
      by_cases accepted : parsed.Valid limits
      · simp [accepted]
        constructor
        · intro equality
          exact congrArg Subtype.val equality
        · intro equality
          exact Subtype.ext equality
      · simp [accepted]
        intro equality
        subst parsed
        exact accepted module.property

theorem encodeRaw_injective_on_admitted (limits : Limits) :
    Function.Injective (fun module : Module limits => encodeRaw module.val) := by
  intro first second equal
  have decoded := congrArg (decode? limits) equal
  simpa using decoded

end Mettapedia.GSLT.LanguageDef.ModuleFormat
