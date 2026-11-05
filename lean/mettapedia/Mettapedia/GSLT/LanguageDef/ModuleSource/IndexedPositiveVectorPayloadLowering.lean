import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedPositiveVectorLowering
import Mettapedia.TypeTheory.IndexedPositiveVectorPayload

/-!
# Payload-parametric erasure of the admitted Vector source grammar

All resolved source constructors are interpreted over the chosen payload
carrier. Native constructor code has no binder names; those names remain
ordered metadata beside the code. The structural observations below inspect
the native code independently of the source erasure.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedPositiveVectorLowering

open Mettapedia.TypeTheory
open IndexedPolynomial.Description
open IndexedPositiveContainer

universe u

def Code.eraseWithPayload (Payload : Type u) :
    {context : List DataSort} → {names : List String} → Code context names →
      IndexedPositiveContainer.Code (VectorPayload.interface Payload)
        (VectorPayload.registry Payload) 0 context
  | _, _, .result => .result ()
  | _, _, .data _ sort _ rest => .data sort (rest.eraseWithPayload Payload)
  | _, _, .recursive _ rest => .recursive () (rest.eraseWithPayload Payload)
  | _, _, .vector _ length rest =>
      .nested "Vector" (VectorPayload.entry Payload)
        (by simp [VectorPayload.registry]) length () (rest.eraseWithPayload Payload)

inductive FieldKind where
  | data (sort : DataSort)
  | recursive
  | nested (name : String)
  deriving DecidableEq

def Code.fieldOrder : {context : List DataSort} → {names : List String} →
    Code context names → List FieldKind
  | _, _, .result => []
  | _, _, .data _ sort _ rest => .data sort :: rest.fieldOrder
  | _, _, .recursive _ rest => .recursive :: rest.fieldOrder
  | _, _, .vector _ _ rest => .nested "Vector" :: rest.fieldOrder

def Code.binderNames : {context : List DataSort} → {names : List String} →
    Code context names → List String
  | _, _, .result => []
  | _, _, .data name _ _ rest => name :: rest.binderNames
  | _, _, .recursive name rest => name :: rest.binderNames
  | _, _, .vector name _ rest => name :: rest.binderNames

def nativeFieldOrder {Payload : Type u} {parameters : Nat} :
    {context : List DataSort} →
    IndexedPositiveContainer.Code (VectorPayload.interface Payload)
      (VectorPayload.registry Payload) parameters context → List FieldKind
  | _, .result _ => []
  | _, .data sort rest => .data sort :: nativeFieldOrder rest
  | _, .recursive _ rest => .recursive :: nativeFieldOrder rest
  | _, .nested name _ _ _ _ rest => .nested name :: nativeFieldOrder rest

theorem Code.eraseWithPayload_fieldOrder (Payload : Type u) :
    {context : List DataSort} → {names : List String} → (code : Code context names) →
    nativeFieldOrder (code.eraseWithPayload Payload) = code.fieldOrder
  | _, _, .result => rfl
  | _, _, .data _ sort _ rest => by
      change FieldKind.data sort :: _ = FieldKind.data sort :: _
      exact congrArg (List.cons (FieldKind.data sort)) (eraseWithPayload_fieldOrder Payload rest)
  | _, _, .recursive _ rest => by
      change FieldKind.recursive :: _ = FieldKind.recursive :: _
      exact congrArg (List.cons FieldKind.recursive) (eraseWithPayload_fieldOrder Payload rest)
  | _, _, .vector _ _ rest => by
      change FieldKind.nested "Vector" :: _ = FieldKind.nested "Vector" :: _
      exact congrArg (List.cons (FieldKind.nested "Vector")) (eraseWithPayload_fieldOrder Payload rest)

/-- A typed spine retains the original length expression, including every
earlier-data binder crossed by that expression. -/
inductive Spine : List DataSort → Type where
  | result {context} : Spine context
  | data {context} (sort : DataSort) : Spine (sort :: context) → Spine context
  | recursive {context} : Spine context → Spine context
  | vector {context} (length : LengthExpr context) : Spine context → Spine context

def Code.spine : {context : List DataSort} → {names : List String} →
    Code context names → Spine context
  | _, _, .result => .result
  | _, _, .data _ sort _ rest => .data sort rest.spine
  | _, _, .recursive _ rest => .recursive rest.spine
  | _, _, .vector _ length rest => .vector length rest.spine

/-- Structural interpretation, rather than a predicate defined by equality
with the erasure function. -/
inductive RealizesSpine (Payload : Type u) :
    {context : List DataSort} → Spine context →
    IndexedPositiveContainer.Code (VectorPayload.interface Payload)
      (VectorPayload.registry Payload) 0 context → Prop where
  | result {context} : RealizesSpine Payload (.result : Spine context) (.result ())
  | data {context sort spine native} : RealizesSpine Payload spine native →
      RealizesSpine Payload (.data sort spine : Spine context) (.data sort native)
  | recursive {context spine native} : RealizesSpine Payload spine native →
      RealizesSpine Payload (.recursive spine : Spine context) (.recursive () native)
  | vector {context length spine native} : RealizesSpine Payload spine native →
      RealizesSpine Payload (.vector length spine : Spine context)
        (.nested "Vector" (VectorPayload.entry Payload)
          (by simp [VectorPayload.registry]) length () native)

theorem Code.eraseWithPayload_spine (Payload : Type u) :
    {context : List DataSort} → {names : List String} → (code : Code context names) →
      RealizesSpine Payload code.spine (code.eraseWithPayload Payload)
  | _, _, .result => .result
  | _, _, .data _ _ _ rest => .data (eraseWithPayload_spine Payload rest)
  | _, _, .recursive _ rest => .recursive (eraseWithPayload_spine Payload rest)
  | _, _, .vector _ _ rest => .vector (eraseWithPayload_spine Payload rest)

theorem RealizesSpine.unique {Payload : Type u} {context : List DataSort}
    {first second : Spine context}
    {native : IndexedPositiveContainer.Code (VectorPayload.interface Payload)
      (VectorPayload.registry Payload) 0 context}
    (firstProof : RealizesSpine Payload first native)
    (secondProof : RealizesSpine Payload second native) : first = second := by
  induction firstProof with
  | result => cases secondProof; rfl
  | data prior ih => cases secondProof with | data other => exact congrArg _ (ih other)
  | recursive prior ih => cases secondProof with | recursive other => exact congrArg _ (ih other)
  | vector prior ih => cases secondProof with | vector other => exact congrArg _ (ih other)

theorem Code.binder_count : {context : List DataSort} → {names : List String} →
    (code : Code context names) → code.binderNames.length = code.fieldOrder.length
  | _, _, .result => rfl
  | _, _, .data _ _ _ rest => congrArg Nat.succ rest.binder_count
  | _, _, .recursive _ rest => congrArg Nat.succ rest.binder_count
  | _, _, .vector _ _ rest => congrArg Nat.succ rest.binder_count

structure PayloadConstructor (Payload : Type u) where
  name : String
  binders : List String
  body : IndexedPositiveContainer.Code (VectorPayload.interface Payload)
    (VectorPayload.registry Payload) 0 []

def ResolvedConstructor.withPayload (Payload : Type u) (source : ResolvedConstructor) :
    PayloadConstructor Payload :=
  ⟨source.name, source.body.binderNames, source.body.eraseWithPayload Payload⟩

def ResolvedFamily.withPayload (Payload : Type u) (source : ResolvedFamily) :
    List (PayloadConstructor Payload) := source.constructors.map (·.withPayload Payload)

def ResolvedFamily.codesWithPayload (Payload : Type u) (source : ResolvedFamily) :
    List (IndexedPositiveContainer.Code (VectorPayload.interface Payload)
      (VectorPayload.registry Payload) 0 []) :=
  source.constructors.map fun constructor => constructor.body.eraseWithPayload Payload

theorem ResolvedConstructor.payload_name (Payload : Type u) (source : ResolvedConstructor) :
    (source.withPayload Payload).name = source.name := rfl

theorem ResolvedConstructor.payload_binders (Payload : Type u) (source : ResolvedConstructor) :
    (source.withPayload Payload).binders = source.body.binderNames := rfl

theorem ResolvedConstructor.payload_structure (Payload : Type u) (source : ResolvedConstructor) :
    RealizesSpine Payload source.body.spine (source.withPayload Payload).body :=
  source.body.eraseWithPayload_spine Payload

theorem ResolvedConstructor.payload_binder_count (Payload : Type u) (source : ResolvedConstructor) :
    (source.withPayload Payload).binders.length =
      (nativeFieldOrder (source.withPayload Payload).body).length := by
  rw [source.payload_binders Payload]
  change source.body.binderNames.length = (nativeFieldOrder (source.body.eraseWithPayload Payload)).length
  rw [source.body.eraseWithPayload_fieldOrder Payload]
  exact source.body.binder_count

theorem ResolvedFamily.payload_names (Payload : Type u) (source : ResolvedFamily) :
    (source.withPayload Payload).map (·.name) = source.constructors.map (·.name) := by
  simp only [withPayload, List.map_map]
  rfl

theorem ResolvedFamily.payload_names_unique (Payload : Type u) (source : ResolvedFamily) :
    ((source.withPayload Payload).map (·.name)).Nodup := by
  rw [source.payload_names Payload]
  exact source.uniqueNames

@[simp] theorem ResolvedFamily.payload_inventory_length (Payload : Type u)
    (source : ResolvedFamily) :
    (source.codesWithPayload Payload).length = source.constructors.length := List.length_map ..

set_option backward.isDefEq.respectTransparency false in
theorem ResolvedFamily.payload_inventory_get (Payload : Type u) (source : ResolvedFamily)
    (occurrence : Fin source.constructors.length) :
    (source.codesWithPayload Payload).get
        ⟨occurrence.val, by rw [source.payload_inventory_length Payload]; exact occurrence.isLt⟩ =
      (source.constructors.get occurrence).body.eraseWithPayload Payload := by
  simpa only [codesWithPayload, List.get_eq_getElem] using
    (List.getElem_map (fun constructor : ResolvedConstructor =>
      constructor.body.eraseWithPayload Payload) (l := source.constructors)
      (i := occurrence.val) (h := by simpa only [List.length_map] using occurrence.isLt))

#print axioms Code.eraseWithPayload_fieldOrder
#print axioms Code.eraseWithPayload_spine
#print axioms ResolvedFamily.payload_names_unique
#print axioms ResolvedFamily.payload_inventory_get

end Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedPositiveVectorLowering
