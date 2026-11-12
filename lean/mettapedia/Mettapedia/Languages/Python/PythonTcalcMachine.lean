import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

/-!
# Existing-cell heap/frame operations and Python candidate modules

This is a finite existing-cell operation model, accompanied by separately
authored candidate modules. It follows the heap/frame/value-stack decomposition
also used by `Broyojo/python-formalization`, but does not import or refine that
project's bytecode evaluator. Its `PyState` has no instruction position,
continuation, exception or callback state. No native `tcalc` or CeTTa execution
correspondence is asserted here.

The three carriers are:

1. **Layer 1 (`Heap`)**: Maps `ObjRef` addresses to mutable `PyObj` instances containing
   indexed attribute tables (`AttrTable`) and dictionary tables (`DictTable`).
2. **Layer 2 (`Frame`)**: Maps `LocalVar` identifiers to `PyVal` values (primitives or `ObjRef`
   heap references), separating variable rebinding (`x = ...`) from heap object mutation
   (`x.attr = ...`, `x[k] = ...`).
3. **Layer 3 (`ValueStack`)**: Thread-local evaluation stack for expression intermediates.

`Frame.update`, `AttrTable.update` and `DictTable.update` replace existing
entries only; they do not allocate missing bindings or keys. Failed lookups
leave this calibration state unchanged. Thus these operations are not the
general Python assignment, attribute, or dictionary protocols. The source
bridge must establish the existing-cell profile and uniqueness invariants,
or extend the actual operations before claiming that broader coverage.

For the operations defined here we prove:
- **Positive alias preservation (`alias_mutation_visible_through_both_refs`)**: When two local
  variables `x` and `y` in `Frame` alias the same `ObjRef` in `Heap`, mutating an attribute or
  dictionary slot through `x` updates the value observed through `y`.
- **Negative control (`unaliased_mutation_preserves_other_ref`)**: When `x` and `y` reference
  distinct `ObjRef` addresses (`r₁ ≠ r₂`), mutating `r₁` through `x` leaves the object observed
  through `y` strictly invariant.
- **Disjoint footprint commutation (`disjoint_footprint_steps_commute`)**: Two `PyStep`
  transitions whose read/write heap and frame footprints are disjoint (`Footprint.Disjoint`)
  commute to the exact same post-state (`s₁₂ = s₂₁`), witnessing the diamond property for
  commuting existing heap/frame writes in this model. This is not a theorem
  about arbitrary `PyOp` pairs or the transform runtime.

Both authored Gold GSLT modules (`Python/Syntax.module` and `Python/Semantics.module`) are
loaded, elaborated, and round-trip verified at compile time. Their rewrite
execution is not thereby connected to `PyState.stepOp`; in particular the
authored continuation machine is distinct from this finite operation model.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.Python.PythonTcalcMachine

open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

/-! ## 1. Gold GSLT Module Elaboration and Round-Trip Verification -/

#module_file "../../../../../metta/gslt/module/gold/SourceLexical.module"
#module_file "../../../../../metta/gslt/module/gold/Python/Syntax.module"
#module_file "../../../../../metta/gslt/module/gold/Python/Semantics.module"

#guard SourceLexical.language.isOk
#guard PythonSyntaxGSLT.language.isOk
#guard PythonSemanticsGSLT.language.isOk

#module_roundtrip PythonSyntaxGSLT
#module_roundtrip PythonSemanticsGSLT

/-! ## 2. Core Identifiers, Values, and Indexed Object Tables -/

/-- Heap object reference address. -/
structure ObjRef where
  addr : Nat
  deriving Repr, DecidableEq, BEq

/-- Constructive boolean equality on `Nat` with transparent kernel reduction. -/
def Nat.eqBool : Nat → Nat → Bool
  | 0, 0 => true
  | 0, _ + 1 => false
  | _ + 1, 0 => false
  | a + 1, b + 1 => eqBool a b

theorem Nat.eq_of_eqBool : ∀ {a b : Nat}, Nat.eqBool a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => by cases h
  | _ + 1, 0, h => by cases h
  | _ + 1, _ + 1, h => congrArg Nat.succ (Nat.eq_of_eqBool h)

/-- Constructive boolean equality on `ObjRef`. -/
def ObjRef.eqBool (a b : ObjRef) : Bool :=
  Nat.eqBool a.addr b.addr

theorem ObjRef.eq_of_eqBool : ∀ {a b : ObjRef}, ObjRef.eqBool a b = true → a = b
  | ⟨_⟩, ⟨_⟩, h => congrArg ObjRef.mk (Nat.eq_of_eqBool h)

/-- Local variable identifier in a stack frame. -/
abbrev LocalVar := Nat

/-- Object attribute identifier. -/
abbrev AttrName := Nat

/-- Dictionary key (indexed by integer key id). -/
abbrev DictKey := Nat

/-- Python runtime values: primitives or heap object references (`ObjRef`). -/
inductive PyVal where
  | none
  | bool (flag : Bool)
  | int (val : Int)
  | ref (target : ObjRef)
  deriving Repr, DecidableEq, BEq

/-- Single entry in an object's attribute table. -/
structure AttrEntry where
  attr : AttrName
  val : PyVal
  deriving Repr, DecidableEq, BEq

/-- Indexed attribute table for a heap object. -/
abbrev AttrTable := List AttrEntry

/-- Single entry in an object's dictionary / subscript table. -/
structure DictEntry where
  key : DictKey
  val : PyVal
  deriving Repr, DecidableEq, BEq

/-- Indexed dictionary table for a heap object. -/
abbrev DictTable := List DictEntry

/-- A mutable Python heap object (`PyObj`) carrying both attribute and dictionary tables. -/
structure PyObj where
  classTag : Nat
  attrs : AttrTable
  dict : DictTable
  deriving Repr, DecidableEq, BEq

/-- Lookup an attribute in an `AttrTable`. -/
def AttrTable.lookup : AttrTable → AttrName → Option PyVal
  | [], _ => .none
  | entry :: rest, a => cond (Nat.eqBool entry.attr a) (some entry.val) (lookup rest a)

/-- Update an existing attribute slot in-place across an `AttrTable`. -/
def AttrTable.update : AttrTable → AttrName → PyVal → AttrTable
  | [], _, _ => []
  | entry :: rest, a, v =>
      cond (Nat.eqBool entry.attr a) { entry with val := v } entry :: update rest a v

/-- Lookup a key in a `DictTable`. -/
def DictTable.lookup : DictTable → DictKey → Option PyVal
  | [], _ => .none
  | entry :: rest, k => cond (Nat.eqBool entry.key k) (some entry.val) (lookup rest k)

/-- Update an existing dictionary key in-place across a `DictTable`. -/
def DictTable.update : DictTable → DictKey → PyVal → DictTable
  | [], _, _ => []
  | entry :: rest, k, v =>
      cond (Nat.eqBool entry.key k) { entry with val := v } entry :: update rest k v

/-- Read an attribute from a `PyObj`. -/
def PyObj.getAttr (obj : PyObj) (a : AttrName) : Option PyVal :=
  AttrTable.lookup obj.attrs a

/-- Mutate an attribute on a `PyObj`. -/
def PyObj.setAttr (obj : PyObj) (a : AttrName) (v : PyVal) : PyObj :=
  { obj with attrs := AttrTable.update obj.attrs a v }

/-- Read a dictionary key from a `PyObj`. -/
def PyObj.getDict (obj : PyObj) (k : DictKey) : Option PyVal :=
  DictTable.lookup obj.dict k

/-- Mutate a dictionary key on a `PyObj`. -/
def PyObj.setDict (obj : PyObj) (k : DictKey) (v : PyVal) : PyObj :=
  { obj with dict := DictTable.update obj.dict k v }

theorem AttrTable.lookup_update_self : ∀ (table : AttrTable) (a : AttrName) (v : PyVal),
    (AttrTable.lookup table a).isSome = true →
    AttrTable.lookup (AttrTable.update table a v) a = some v
  | [], _, _, hPresent => by cases hPresent
  | entry :: rest, a, v, hPresent =>
      match hEq : Nat.eqBool entry.attr a with
      | false => by
          unfold AttrTable.update AttrTable.lookup
          rw [hEq]
          dsimp only [cond]
          rw [hEq]
          dsimp only [cond]
          have hRest : (AttrTable.lookup rest a).isSome = true := by
            unfold AttrTable.lookup at hPresent
            rw [hEq] at hPresent
            exact hPresent
          exact AttrTable.lookup_update_self rest a v hRest
      | true => by
          unfold AttrTable.update AttrTable.lookup
          rw [hEq]
          dsimp only [cond]
          rw [hEq]

theorem AttrTable.lookup_update_ne : ∀ (table : AttrTable) (a₁ a₂ : AttrName) (v : PyVal),
    Nat.eqBool a₁ a₂ = false →
    AttrTable.lookup (AttrTable.update table a₁ v) a₂ = AttrTable.lookup table a₂
  | [], _, _, _, _ => rfl
  | entry :: rest, a₁, a₂, v, hNe =>
      match hEq₁ : Nat.eqBool entry.attr a₁ with
      | false => by
          unfold AttrTable.update AttrTable.lookup
          rw [hEq₁]
          dsimp only [cond]
          cases Nat.eqBool entry.attr a₂
          · exact AttrTable.lookup_update_ne rest a₁ a₂ v hNe
          · rfl
      | true => by
          unfold AttrTable.update AttrTable.lookup
          rw [hEq₁]
          dsimp only [cond]
          have hEq₂ : Nat.eqBool entry.attr a₂ = false := by
            have h1 : entry.attr = a₁ := Nat.eq_of_eqBool hEq₁
            rw [h1]
            exact hNe
          rw [hEq₂]
          exact AttrTable.lookup_update_ne rest a₁ a₂ v hNe

theorem DictTable.lookup_update_self : ∀ (table : DictTable) (k : DictKey) (v : PyVal),
    (DictTable.lookup table k).isSome = true →
    DictTable.lookup (DictTable.update table k v) k = some v
  | [], _, _, hPresent => by cases hPresent
  | entry :: rest, k, v, hPresent =>
      match hEq : Nat.eqBool entry.key k with
      | false => by
          unfold DictTable.update DictTable.lookup
          rw [hEq]
          dsimp only [cond]
          rw [hEq]
          dsimp only [cond]
          have hRest : (DictTable.lookup rest k).isSome = true := by
            unfold DictTable.lookup at hPresent
            rw [hEq] at hPresent
            exact hPresent
          exact DictTable.lookup_update_self rest k v hRest
      | true => by
          unfold DictTable.update DictTable.lookup
          rw [hEq]
          dsimp only [cond]
          rw [hEq]

/-! ## 3. Three-Layer State Architecture (`Heap`, `Frame`, `ValueStack`) -/

/-- A single heap cell binding an `ObjRef` to a `PyObj`. -/
structure HeapCell where
  ref : ObjRef
  obj : PyObj
  deriving Repr, DecidableEq, BEq

/-- Layer 1 (`Heap`): maps `ObjRef` addresses to mutable `PyObj` instances. -/
abbrev Heap := List HeapCell

/-- A single frame slot binding a `LocalVar` to a `PyVal`. -/
structure FrameCell where
  varName : LocalVar
  val : PyVal
  deriving Repr, DecidableEq, BEq

/-- Layer 2 (`Frame`): maps `LocalVar` names to `PyVal` values. -/
abbrev Frame := List FrameCell

/-- Layer 3 (`ValueStack`): operand stack of `PyVal` intermediates. -/
abbrev ValueStack := List PyVal

/-- Composite 3-layer Python machine state on `tcalc`. -/
structure PyState where
  heap : Heap
  frame : Frame
  stack : ValueStack
  deriving Repr, DecidableEq, BEq

/-- Lookup an `ObjRef` in `Heap`. -/
def Heap.lookup : Heap → ObjRef → Option PyObj
  | [], _ => .none
  | cell :: rest, r => cond (ObjRef.eqBool cell.ref r) (some cell.obj) (lookup rest r)

/-- Update a `PyObj` at `ObjRef` in-place in `Heap`. -/
def Heap.update : Heap → ObjRef → PyObj → Heap
  | [], _, _ => []
  | cell :: rest, r, o =>
      cond (ObjRef.eqBool cell.ref r) { cell with obj := o } cell :: update rest r o

/-- Modify a `PyObj` at `ObjRef` in-place in `Heap` via a transformer `f`. -/
def Heap.modify : Heap → ObjRef → (PyObj → PyObj) → Heap
  | [], _, _ => []
  | cell :: rest, r, f =>
      cond (ObjRef.eqBool cell.ref r) { cell with obj := f cell.obj } cell :: modify rest r f

/-- Lookup a `LocalVar` in `Frame`. -/
def Frame.lookup : Frame → LocalVar → Option PyVal
  | [], _ => .none
  | cell :: rest, x => cond (Nat.eqBool cell.varName x) (some cell.val) (lookup rest x)

/-- Update a `LocalVar` binding in-place in `Frame`. -/
def Frame.update : Frame → LocalVar → PyVal → Frame
  | [], _, _ => []
  | cell :: rest, x, v =>
      cond (Nat.eqBool cell.varName x) { cell with val := v } cell :: update rest x v

/-- Resolve an attribute `a` through a local variable `x` in `PyState`
    (Layer 2 `Frame` lookup followed by Layer 1 `Heap` dereference). -/
def PyState.observeAttrViaVar (s : PyState) (x : LocalVar) (a : AttrName) : Option PyVal :=
  match Frame.lookup s.frame x with
  | some (.ref r) =>
      match Heap.lookup s.heap r with
      | some obj => obj.getAttr a
      | .none => .none
  | _ => .none

/-- Resolve a dictionary key `k` through a local variable `x` in `PyState`. -/
def PyState.observeDictViaVar (s : PyState) (x : LocalVar) (k : DictKey) : Option PyVal :=
  match Frame.lookup s.frame x with
  | some (.ref r) =>
      match Heap.lookup s.heap r with
      | some obj => obj.getDict k
      | .none => .none
  | _ => .none

/-- Relational equi-join over two heap-resident dictionaries at `leftRef` and `rightRef` on `key`. -/
def PyState.evalRelJoin (s : PyState) (leftRef rightRef : ObjRef) (key : DictKey) :
    Option (PyVal × PyVal) :=
  match Heap.lookup s.heap leftRef, Heap.lookup s.heap rightRef with
  | some leftObj, some rightObj =>
      match leftObj.getDict key, rightObj.getDict key with
      | some lv, some rv => some (lv, rv)
      | _, _ => .none
  | _, _ => .none

/-! ## 4. Fundamental Heap and Frame Lookup/Update Lemmas -/

theorem Heap.lookup_update_self : ∀ (h : Heap) (r : ObjRef) (o : PyObj),
    (Heap.lookup h r).isSome = true →
    Heap.lookup (Heap.update h r o) r = some o
  | [], _, _, hPresent => by cases hPresent
  | cell :: rest, r, o, hPresent => by
      unfold Heap.update Heap.lookup
      match hEq : ObjRef.eqBool cell.ref r with
      | false =>
          dsimp only [cond]
          rw [hEq]
          dsimp only [cond]
          have hRest : (Heap.lookup rest r).isSome = true := by
            unfold Heap.lookup at hPresent
            rw [hEq] at hPresent
            exact hPresent
          exact Heap.lookup_update_self rest r o hRest
      | true =>
          dsimp only [cond]
          rw [hEq]

theorem Heap.lookup_update_ne : ∀ (h : Heap) (r₁ r₂ : ObjRef) (o : PyObj),
    ObjRef.eqBool r₁ r₂ = false →
    Heap.lookup (Heap.update h r₁ o) r₂ = Heap.lookup h r₂
  | [], _, _, _, _ => rfl
  | cell :: rest, r₁, r₂, o, hNe => by
      unfold Heap.update Heap.lookup
      match hEq₁ : ObjRef.eqBool cell.ref r₁ with
      | false =>
          dsimp only [cond]
          match ObjRef.eqBool cell.ref r₂ with
          | false => exact Heap.lookup_update_ne rest r₁ r₂ o hNe
          | true => rfl
      | true =>
          dsimp only [cond]
          have hEq₂ : ObjRef.eqBool cell.ref r₂ = false := by
            have h1 : cell.ref = r₁ := ObjRef.eq_of_eqBool hEq₁
            rw [h1]
            exact hNe
          rw [hEq₂]
          exact Heap.lookup_update_ne rest r₁ r₂ o hNe

theorem Heap.lookup_modify_self : ∀ (h : Heap) (r : ObjRef) (f : PyObj → PyObj),
    Heap.lookup (Heap.modify h r f) r = (Heap.lookup h r).map f
  | [], _, _ => rfl
  | cell :: rest, r, f => by
      unfold Heap.modify Heap.lookup
      match hEq : ObjRef.eqBool cell.ref r with
      | false =>
          dsimp only [cond]
          rw [hEq]
          exact Heap.lookup_modify_self rest r f
      | true =>
          dsimp only [cond]
          rw [hEq]
          rfl

theorem Heap.lookup_modify_ne : ∀ (h : Heap) (r₁ r₂ : ObjRef) (f : PyObj → PyObj),
    ObjRef.eqBool r₁ r₂ = false →
    Heap.lookup (Heap.modify h r₁ f) r₂ = Heap.lookup h r₂
  | [], _, _, _, _ => rfl
  | cell :: rest, r₁, r₂, f, hNe => by
      unfold Heap.modify Heap.lookup
      match hEq₁ : ObjRef.eqBool cell.ref r₁ with
      | false =>
          dsimp only [cond]
          match ObjRef.eqBool cell.ref r₂ with
          | false => exact Heap.lookup_modify_ne rest r₁ r₂ f hNe
          | true => rfl
      | true =>
          dsimp only [cond]
          have hEq₂ : ObjRef.eqBool cell.ref r₂ = false := by
            have h1 : cell.ref = r₁ := ObjRef.eq_of_eqBool hEq₁
            rw [h1]
            exact hNe
          rw [hEq₂]
          exact Heap.lookup_modify_ne rest r₁ r₂ f hNe

theorem Heap.update_comm : ∀ (h : Heap) (r₁ r₂ : ObjRef) (o₁ o₂ : PyObj),
    ObjRef.eqBool r₁ r₂ = false →
    Heap.update (Heap.update h r₁ o₁) r₂ o₂ = Heap.update (Heap.update h r₂ o₂) r₁ o₁
  | [], _, _, _, _, _ => rfl
  | cell :: rest, r₁, r₂, o₁, o₂, hNe => by
      dsimp only [Heap.update]
      rw [Heap.update_comm rest r₁ r₂ o₁ o₂ hNe]
      apply congrArg (List.cons · (Heap.update (Heap.update rest r₂ o₂) r₁ o₁))
      match hEq₁ : ObjRef.eqBool cell.ref r₁ with
      | false =>
          dsimp only [cond]
          match hEq₂ : ObjRef.eqBool cell.ref r₂ with
          | false =>
              dsimp only [cond]
              rw [hEq₁]
          | true =>
              dsimp only [cond]
              rw [hEq₁]
      | true =>
          dsimp only [cond]
          have hEq₂ : ObjRef.eqBool cell.ref r₂ = false := by
            have h1 : cell.ref = r₁ := ObjRef.eq_of_eqBool hEq₁
            rw [h1]
            exact hNe
          rw [hEq₂]
          dsimp only [cond]
          rw [hEq₁]

theorem Frame.lookup_update_self : ∀ (f : Frame) (x : LocalVar) (v : PyVal),
    (Frame.lookup f x).isSome = true →
    Frame.lookup (Frame.update f x v) x = some v
  | [], _, _, hPresent => by cases hPresent
  | cell :: rest, x, v, hPresent => by
      unfold Frame.update Frame.lookup
      match hEq : Nat.eqBool cell.varName x with
      | false =>
          dsimp only [cond]
          rw [hEq]
          dsimp only [cond]
          have hRest : (Frame.lookup rest x).isSome = true := by
            unfold Frame.lookup at hPresent
            rw [hEq] at hPresent
            exact hPresent
          exact Frame.lookup_update_self rest x v hRest
      | true =>
          dsimp only [cond]
          rw [hEq]

theorem Frame.lookup_update_ne : ∀ (f : Frame) (x₁ x₂ : LocalVar) (v : PyVal),
    Nat.eqBool x₁ x₂ = false →
    Frame.lookup (Frame.update f x₁ v) x₂ = Frame.lookup f x₂
  | [], _, _, _, _ => rfl
  | cell :: rest, x₁, x₂, v, hNe => by
      unfold Frame.update Frame.lookup
      match hEq₁ : Nat.eqBool cell.varName x₁ with
      | false =>
          dsimp only [cond]
          match Nat.eqBool cell.varName x₂ with
          | false => exact Frame.lookup_update_ne rest x₁ x₂ v hNe
          | true => rfl
      | true =>
          dsimp only [cond]
          have hEq₂ : Nat.eqBool cell.varName x₂ = false := by
            have h1 : cell.varName = x₁ := Nat.eq_of_eqBool hEq₁
            rw [h1]
            exact hNe
          rw [hEq₂]
          exact Frame.lookup_update_ne rest x₁ x₂ v hNe

theorem Frame.update_comm : ∀ (f : Frame) (x₁ x₂ : LocalVar) (v₁ v₂ : PyVal),
    Nat.eqBool x₁ x₂ = false →
    Frame.update (Frame.update f x₁ v₁) x₂ v₂ = Frame.update (Frame.update f x₂ v₂) x₁ v₁
  | [], _, _, _, _, _ => rfl
  | cell :: rest, x₁, x₂, v₁, v₂, hNe => by
      dsimp only [Frame.update]
      rw [Frame.update_comm rest x₁ x₂ v₁ v₂ hNe]
      apply congrArg (List.cons · (Frame.update (Frame.update rest x₂ v₂) x₁ v₁))
      match hEq₁ : Nat.eqBool cell.varName x₁ with
      | false =>
          dsimp only [cond]
          match hEq₂ : Nat.eqBool cell.varName x₂ with
          | false =>
              dsimp only [cond]
              rw [hEq₁]
          | true =>
              dsimp only [cond]
              rw [hEq₁]
      | true =>
          dsimp only [cond]
          have hEq₂ : Nat.eqBool cell.varName x₂ = false := by
            have h1 : cell.varName = x₁ := Nat.eq_of_eqBool hEq₁
            rw [h1]
            exact hNe
          rw [hEq₂]
          dsimp only [cond]
          rw [hEq₁]

/-! ## 5. Operational Steps (`PyStep`) and Alias Preservation Theorems -/

/-- Atomic operational transitions on `PyState`. -/
inductive PyOp where
  /-- Bind or rebind a local variable `x = v` in `Frame`. -/
  | bindVar (x : LocalVar) (v : PyVal)
  /-- Copy a reference `y = x` in `Frame` (creating an alias when `x` holds `.ref r`). -/
  | aliasVar (dst src : LocalVar)
  /-- Mutate an attribute `x.a = v` on the heap object referenced by `x`. -/
  | mutateAttrViaVar (x : LocalVar) (a : AttrName) (v : PyVal)
  /-- Mutate a dictionary entry `x[k] = v` on the heap object referenced by `x`. -/
  | mutateDictViaVar (x : LocalVar) (k : DictKey) (v : PyVal)
  /-- Direct transition writing `obj` at heap address `r` and `val` at frame slot `x`. -/
  | writeHeapAndFrame (r : ObjRef) (obj : PyObj) (x : LocalVar) (val : PyVal)
  /-- Push a value onto the evaluation stack. -/
  | pushVal (v : PyVal)
  deriving Repr, DecidableEq, BEq

/-- Deterministic step function executing a `PyOp` on `PyState`. -/
def PyState.stepOp (s : PyState) : PyOp → PyState
  | .bindVar x v =>
      { s with frame := Frame.update s.frame x v }
  | .aliasVar dst src =>
      match Frame.lookup s.frame src with
      | some v => { s with frame := Frame.update s.frame dst v }
      | .none => s
  | .mutateAttrViaVar x a v =>
      match Frame.lookup s.frame x with
      | some (.ref r) =>
          { s with heap := Heap.modify s.heap r (fun obj => obj.setAttr a v) }
      | _ => s
  | .mutateDictViaVar x k v =>
      match Frame.lookup s.frame x with
      | some (.ref r) =>
          { s with heap := Heap.modify s.heap r (fun obj => obj.setDict k v) }
      | _ => s
  | .writeHeapAndFrame r obj x val =>
      { s with
        heap := Heap.update s.heap r obj
        frame := Frame.update s.frame x val }
  | .pushVal v =>
      { s with stack := v :: s.stack }

/-- Relational small-step transition judgment `PyStep s op s'`. -/
inductive PyStep : PyState → PyOp → PyState → Prop where
  | step (s : PyState) (op : PyOp) : PyStep s op (s.stepOp op)

/-- **Positive Alias-Preservation Theorem (`alias_mutation_visible_through_both_refs`)**:
    When `x` and `y` in `Frame` alias the same `ObjRef` `r` in `Heap`, mutating attribute `a`
    to `newVal` through `x` updates the value observed through both `x` and `y` to `some newVal`. -/
theorem alias_mutation_visible_through_both_refs
    (s : PyState) (x y : LocalVar) (r : ObjRef) (obj : PyObj) (a : AttrName) (newVal : PyVal)
    (hx : Frame.lookup s.frame x = some (.ref r))
    (hy : Frame.lookup s.frame y = some (.ref r))
    (hHeap : Heap.lookup s.heap r = some obj)
    (hAttr : (AttrTable.lookup obj.attrs a).isSome = true) :
    let s' := s.stepOp (.mutateAttrViaVar x a newVal)
    s'.observeAttrViaVar x a = some newVal ∧
    s'.observeAttrViaVar y a = some newVal := by
  intro s'
  have hStep : s' = { s with heap := Heap.modify s.heap r (fun o => o.setAttr a newVal) } := by
    dsimp only [s', PyState.stepOp]
    rw [hx]
  have hLookupAfter :
      Heap.lookup (Heap.modify s.heap r (fun o => o.setAttr a newVal)) r =
      some (obj.setAttr a newVal) := by
    rw [Heap.lookup_modify_self, hHeap]
    rfl
  have hGetAttr : (obj.setAttr a newVal).getAttr a = some newVal := by
    unfold PyObj.setAttr PyObj.getAttr
    exact AttrTable.lookup_update_self obj.attrs a newVal hAttr
  constructor
  · rw [hStep]
    dsimp only [PyState.observeAttrViaVar]
    rw [hx]
    dsimp only
    rw [hLookupAfter]
    exact hGetAttr
  · rw [hStep]
    dsimp only [PyState.observeAttrViaVar]
    rw [hy]
    dsimp only
    rw [hLookupAfter]
    exact hGetAttr

/-- **Negative Control (`unaliased_mutation_preserves_other_ref`)**:
    When `x` and `y` in `Frame` point to distinct heap addresses `r₁` and `r₂` (`ObjRef.eqBool r₁ r₂ = false`),
    mutating attribute `a` through `x` leaves any attribute `b` observed through `y` unchanged. -/
theorem unaliased_mutation_preserves_other_ref
    (s : PyState) (x y : LocalVar) (r₁ r₂ : ObjRef) (a b : AttrName) (newVal : PyVal)
    (hx : Frame.lookup s.frame x = some (.ref r₁))
    (hy : Frame.lookup s.frame y = some (.ref r₂))
    (hDisjointRef : ObjRef.eqBool r₁ r₂ = false) :
    let s' := s.stepOp (.mutateAttrViaVar x a newVal)
    s'.observeAttrViaVar y b = s.observeAttrViaVar y b := by
  intro s'
  have hStep : s' = { s with heap := Heap.modify s.heap r₁ (fun o => o.setAttr a newVal) } := by
    dsimp only [s', PyState.stepOp]
    rw [hx]
  have hHeapR2 :
      Heap.lookup (Heap.modify s.heap r₁ (fun o => o.setAttr a newVal)) r₂ =
      Heap.lookup s.heap r₂ :=
    Heap.lookup_modify_ne s.heap r₁ r₂ (fun o => o.setAttr a newVal) hDisjointRef
  rw [hStep]
  dsimp only [PyState.observeAttrViaVar]
  rw [hy]
  dsimp only
  rw [hHeapR2]

/-! ## 6. Explicit Read/Write Footprints and Parallel Step Commutation (`tcalc` Diamond) -/

/-- Explicit read/write footprint of a `tcalc` transition over `Heap` (`ObjRef`) and
    `Frame` (`LocalVar`). -/
structure Footprint where
  readHeap : List ObjRef
  writeHeap : List ObjRef
  readFrame : List LocalVar
  writeFrame : List LocalVar
  deriving Repr, DecidableEq, BEq

/-- Membership exclusion check (`x ∉ ys` in boolean form). -/
def List.notMemBy {α : Type} (eqFn : α → α → Bool) (x : α) : List α → Bool
  | [] => true
  | y :: ys => !(eqFn x y) && notMemBy eqFn x ys

/-- List disjointness predicate (`∀ x ∈ xs, x ∉ ys` in boolean form). -/
def List.disjointBy {α : Type} (eqFn : α → α → Bool) : List α → List α → Bool
  | [], _ => true
  | x :: xs, ys => List.notMemBy eqFn x ys && disjointBy eqFn xs ys

/-- Two footprints are disjoint when neither transition writes to a heap object or frame slot
    that the other transition reads or writes. -/
def Footprint.Disjoint (fp₁ fp₂ : Footprint) : Prop :=
  List.disjointBy ObjRef.eqBool fp₁.writeHeap fp₂.writeHeap = true ∧
  List.disjointBy ObjRef.eqBool fp₁.writeHeap fp₂.readHeap = true ∧
  List.disjointBy ObjRef.eqBool fp₂.writeHeap fp₁.readHeap = true ∧
  List.disjointBy Nat.eqBool fp₁.writeFrame fp₂.writeFrame = true ∧
  List.disjointBy Nat.eqBool fp₁.writeFrame fp₂.readFrame = true ∧
  List.disjointBy Nat.eqBool fp₂.writeFrame fp₁.readFrame = true

/-- Footprint of an atomic heap+frame transition `.writeHeapAndFrame r obj x val`. -/
def writeTransitionFootprint (r : ObjRef) (x : LocalVar) : Footprint :=
  { readHeap := []
    writeHeap := [r]
    readFrame := []
    writeFrame := [x] }

theorem singleton_disjointBy_eq_false {α : Type} (eqFn : α → α → Bool) (a b : α)
    (h : List.disjointBy eqFn [a] [b] = true) :
    eqFn a b = false := by
  change ((!(eqFn a b) && true) && true) = true at h
  match hab : eqFn a b with
  | false => rfl
  | true =>
      rw [hab] at h
      cases h

/-- **Parallel Footprint Commutation Theorem (`disjoint_footprint_steps_commute`)**:
    If two `PyStep` transitions `op₁ = .writeHeapAndFrame r₁ obj₁ x₁ val₁` and
    `op₂ = .writeHeapAndFrame r₂ obj₂ x₂ val₂` have disjoint footprints
    (`Footprint.Disjoint (writeTransitionFootprint r₁ x₁) (writeTransitionFootprint r₂ x₂)`),
    then executing `op₁` followed by `op₂` yields the exact same `PyState` as executing
    `op₂` followed by `op₁` (the `tcalc` parallel diamond property). -/
theorem disjoint_footprint_steps_commute
    (s s₁ s₂ s₁₂ s₂₁ : PyState)
    (r₁ r₂ : ObjRef) (obj₁ obj₂ : PyObj)
    (x₁ x₂ : LocalVar) (val₁ val₂ : PyVal)
    (hDisjoint : Footprint.Disjoint (writeTransitionFootprint r₁ x₁) (writeTransitionFootprint r₂ x₂))
    (hStep₁ : PyStep s (.writeHeapAndFrame r₁ obj₁ x₁ val₁) s₁)
    (hStep₁₂ : PyStep s₁ (.writeHeapAndFrame r₂ obj₂ x₂ val₂) s₁₂)
    (hStep₂ : PyStep s (.writeHeapAndFrame r₂ obj₂ x₂ val₂) s₂)
    (hStep₂₁ : PyStep s₂ (.writeHeapAndFrame r₁ obj₁ x₁ val₁) s₂₁) :
    s₁₂ = s₂₁ := by
  cases hStep₁
  cases hStep₁₂
  cases hStep₂
  cases hStep₂₁
  rcases hDisjoint with ⟨hHeapDisj, _, _, hFrameDisj, _, _⟩
  have hNeHeap : ObjRef.eqBool r₁ r₂ = false :=
    singleton_disjointBy_eq_false ObjRef.eqBool r₁ r₂ hHeapDisj
  have hNeFrame : Nat.eqBool x₁ x₂ = false :=
    singleton_disjointBy_eq_false Nat.eqBool x₁ x₂ hFrameDisj
  dsimp only [PyState.stepOp]
  rw [Heap.update_comm s.heap r₁ r₂ obj₁ obj₂ hNeHeap]
  rw [Frame.update_comm s.frame x₁ x₂ val₁ val₂ hNeFrame]

/-! ## 7. Concrete Executable Examples and Negative/Positive `#guard` Controls -/

/-- Sample object address `0` and `1`. -/
def ref0 : ObjRef := ⟨0⟩
def ref1 : ObjRef := ⟨1⟩

/-- Sample initial state where `x` (`varName = 0`) and `y` (`varName = 1`) alias `ref0`,
    while `z` (`varName = 2`) points to `ref1`. -/
def sampleInitialState : PyState :=
  { heap :=
      [ { ref := ref0
          obj := { classTag := 1
                   attrs := [{ attr := 10, val := .int 42 }]
                   dict := [{ key := 100, val := .int 7 }] } }
      , { ref := ref1
          obj := { classTag := 1
                   attrs := [{ attr := 10, val := .int 99 }]
                   dict := [{ key := 100, val := .int 7 }] } } ]
    frame :=
      [ { varName := 0, val := .ref ref0 }
      , { varName := 1, val := .ref ref0 }
      , { varName := 2, val := .ref ref1 } ]
    stack := [] }

-- Positive control: mutating attribute 10 via `x` (0) updates observation via aliased `y` (1)
#guard (sampleInitialState.stepOp (.mutateAttrViaVar 0 10 (.int 500))).observeAttrViaVar 1 10 ==
  some (.int 500)

-- Negative control: mutating attribute 10 via `x` (0) preserves unaliased `z` (2) at 99
#guard (sampleInitialState.stepOp (.mutateAttrViaVar 0 10 (.int 500))).observeAttrViaVar 2 10 ==
  some (.int 99)

-- Relational join control: joining `ref0` and `ref1` on key 100 returns `(7, 7)`
#guard sampleInitialState.evalRelJoin ref0 ref1 100 == some (.int 7, .int 7)

-- Parallel commutation control: disjoint updates on (ref0, var 0) and (ref1, var 2) commute
#guard
  let op1 := PyOp.writeHeapAndFrame ref0 { classTag := 1, attrs := [], dict := [] } 0 (.int 11)
  let op2 := PyOp.writeHeapAndFrame ref1 { classTag := 2, attrs := [], dict := [] } 2 (.int 22)
  (sampleInitialState.stepOp op1).stepOp op2 == (sampleInitialState.stepOp op2).stepOp op1

-- Negative commutation control: conflicting writes to the same variable (var 0) do NOT commute
#guard
  let opConflict1 := PyOp.bindVar 0 (.int 11)
  let opConflict2 := PyOp.bindVar 0 (.int 22)
  (sampleInitialState.stepOp opConflict1).stepOp opConflict2 !=
    (sampleInitialState.stepOp opConflict2).stepOp opConflict1

end Mettapedia.Languages.Python.PythonTcalcMachine
