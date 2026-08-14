/-!
# Signature-indexed abstract binding trees

This module isolates the representation used by a generic physical ABT
engine.  Constructor children carry the binder depth declared for their
field; shifting, substitution, unused-binder removal, and scope checking read
only those depths.  Object languages supply the structural head type and its
field-depth signature separately.

The carrier is intentionally parameterized by structural heads.  Binding
indices are the only distinguished leaves, so object-language constants,
names, and indices of other sorts can remain ordinary head data.
-/

namespace Mettapedia.GSLT.LanguageDef.SignatureIndexedABT

set_option autoImplicit false

mutual

/-- One abstract binding tree over an arbitrary structural head type. -/
inductive Term (Head : Type) where
  | idx (value : Nat)
  | node (head : Head) (fields : Fields Head)

/-- Constructor fields decorated by their declared binder depths. -/
inductive Fields (Head : Type) where
  | nil
  | cons (depth : Nat) (term : Term Head) (rest : Fields Head)

end

namespace Term

mutual

/-- Shift every free index at or above `cutoff`. -/
def lift {Head : Type} (cutoff amount : Nat) : Term Head → Term Head
  | .idx index =>
      if index < cutoff then .idx index else .idx (index + amount)
  | .node head fields => .node head (Fields.lift cutoff amount fields)

/-- Shift each field under the binders declared for that field. -/
def Fields.lift {Head : Type} (cutoff amount : Nat) :
    Fields Head → Fields Head
  | .nil => .nil
  | .cons depth term rest =>
      .cons depth (lift (cutoff + depth) amount term)
        (Fields.lift cutoff amount rest)

end

mutual

/-- Binder-eliminating substitution at one de Bruijn depth. -/
def instantiateAt {Head : Type} (depth : Nat) (replacement : Term Head) :
    Term Head → Term Head
  | .idx index =>
      if index < depth then .idx index
      else if index = depth then lift 0 depth replacement
      else .idx (index - 1)
  | .node head fields =>
      .node head (Fields.instantiateAt depth replacement fields)

/-- Substitute beneath each field's declared binders. -/
def Fields.instantiateAt {Head : Type} (depth : Nat)
    (replacement : Term Head) : Fields Head → Fields Head
  | .nil => .nil
  | .cons fieldDepth term rest =>
      .cons fieldDepth
        (instantiateAt (depth + fieldDepth) replacement term)
        (Fields.instantiateAt depth replacement rest)

end

def instantiate {Head : Type} (replacement body : Term Head) : Term Head :=
  instantiateAt 0 replacement body

mutual

/-- Remove one unused binder, failing exactly when it occurs. -/
def dropAt? {Head : Type} (cutoff : Nat) : Term Head → Option (Term Head)
  | .idx index =>
      if index < cutoff then some (.idx index)
      else if index = cutoff then none
      else some (.idx (index - 1))
  | .node head fields =>
      return .node head (← Fields.dropAt? cutoff fields)

/-- Remove one binder beneath each field's declared binders. -/
def Fields.dropAt? {Head : Type} (cutoff : Nat) :
    Fields Head → Option (Fields Head)
  | .nil => some .nil
  | .cons fieldDepth term rest => do
      let droppedTerm ← dropAt? (cutoff + fieldDepth) term
      let droppedRest ← Fields.dropAt? cutoff rest
      some (.cons fieldDepth droppedTerm droppedRest)

end

mutual

/-- Check that every binding index is supported at the current depth. -/
def supportedAt {Head : Type} (depth : Nat) : Term Head → Bool
  | .idx index => decide (index < depth)
  | .node _ fields => Fields.supportedAt depth fields

/-- Scope checking beneath signature-declared field depths. -/
def Fields.supportedAt {Head : Type} (depth : Nat) : Fields Head → Bool
  | .nil => true
  | .cons fieldDepth term rest =>
      supportedAt (depth + fieldDepth) term &&
        Fields.supportedAt depth rest

end

mutual

/-- Verify that every node uses exactly the field depths declared by its
structural signature, recursively. -/
def conforms {Head : Type} (signature : Head → List Nat) :
    Term Head → Bool
  | .idx _ => true
  | .node head fields => Fields.conforms signature (signature head) fields

def Fields.conforms {Head : Type} (signature : Head → List Nat) :
    List Nat → Fields Head → Bool
  | [], .nil => true
  | expectedDepth :: expected, .cons actualDepth term rest =>
      decide (actualDepth = expectedDepth) && conforms signature term &&
        Fields.conforms signature expected rest
  | _, _ => false

end

@[simp] theorem conforms_idx {Head : Type} (signature : Head → List Nat)
    (index : Nat) :
    conforms signature (.idx index) = true :=
  rfl

mutual

/-- Shifting changes indices but preserves the signature shape. -/
theorem conforms_lift {Head : Type} (signature : Head → List Nat)
    (cutoff amount : Nat) (term : Term Head) :
    conforms signature (lift cutoff amount term) =
      conforms signature term := by
  cases term with
  | idx index =>
      by_cases below : index < cutoff <;>
        simp [lift, conforms, below]
  | node head fields =>
      simp [lift, conforms,
        Fields.conforms_lift signature (signature head) cutoff amount fields]

theorem Fields.conforms_lift {Head : Type} (signature : Head → List Nat)
    (expected : List Nat) (cutoff amount : Nat) (fields : Fields Head) :
    Fields.conforms signature expected (Fields.lift cutoff amount fields) =
      Fields.conforms signature expected fields := by
  cases fields with
  | nil => cases expected <;> rfl
  | cons depth term rest =>
      cases expected with
      | nil => rfl
      | cons expectedDepth expected =>
          simp [Fields.lift, Fields.conforms,
            conforms_lift signature (cutoff + depth) amount term,
            Fields.conforms_lift signature expected cutoff amount rest]

end

end Term

end Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
