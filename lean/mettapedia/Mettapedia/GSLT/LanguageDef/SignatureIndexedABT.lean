import Lean.Elab.Tactic.Omega

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

mutual

/-- A well-scoped tree remains supported in a larger ambient context. -/
theorem supportedAt_mono {Head : Type} (lower upper : Nat)
    (within : lower ≤ upper) (term : Term Head)
    (supported : supportedAt lower term = true) :
    supportedAt upper term = true := by
  cases term with
  | idx index =>
      simp only [supportedAt, decide_eq_true_eq] at supported ⊢
      exact Nat.lt_of_lt_of_le supported within
  | node head fields =>
      exact Fields.supportedAt_mono lower upper within fields supported

theorem Fields.supportedAt_mono {Head : Type} (lower upper : Nat)
    (within : lower ≤ upper) (fields : Fields Head)
    (supported : Fields.supportedAt lower fields = true) :
    Fields.supportedAt upper fields = true := by
  cases fields with
  | nil => rfl
  | cons depth term rest =>
      simp only [Fields.supportedAt, Bool.and_eq_true] at supported ⊢
      exact ⟨supportedAt_mono (lower + depth) (upper + depth)
          (Nat.add_le_add_right within depth) term supported.1,
        Fields.supportedAt_mono lower upper within rest supported.2⟩

end

mutual

/-- Shifting above the complete support cannot alter a tree. In particular,
closed replacements need no physical index shift under a binder. -/
theorem lift_of_supported {Head : Type} (cutoff amount : Nat)
    (term : Term Head) (supported : supportedAt cutoff term = true) :
    lift cutoff amount term = term := by
  cases term with
  | idx index =>
      simp only [supportedAt, decide_eq_true_eq] at supported
      simp [lift, supported]
  | node head fields =>
      simp only [lift, Fields.lift_of_supported cutoff amount fields supported]

theorem Fields.lift_of_supported {Head : Type} (cutoff amount : Nat)
    (fields : Fields Head) (supported : Fields.supportedAt cutoff fields = true) :
    Fields.lift cutoff amount fields = fields := by
  cases fields with
  | nil => rfl
  | cons depth term rest =>
      simp only [Fields.supportedAt, Bool.and_eq_true] at supported
      simp only [Fields.lift,
        lift_of_supported (cutoff + depth) amount term supported.1,
        Fields.lift_of_supported cutoff amount rest supported.2]

end

mutual

/-- Opening the outermost ambient parameter with closed syntax removes
exactly that parameter. Field-local binders remain in scope. -/
theorem supportedAt_instantiate_outermost {Head : Type} (depth : Nat)
    (replacement term : Term Head)
    (closed : supportedAt 0 replacement = true)
    (supported : supportedAt (depth + 1) term = true) :
    supportedAt depth (instantiateAt depth replacement term) = true := by
  cases term with
  | idx index =>
      simp only [supportedAt, decide_eq_true_eq] at supported
      by_cases below : index < depth
      · simp [instantiateAt, below, supportedAt]
      · have equal : index = depth := by omega
        simp only [instantiateAt, if_neg below, if_pos equal]
        rw [lift_of_supported 0 depth replacement closed]
        exact supportedAt_mono 0 depth (Nat.zero_le depth) replacement closed
  | node head fields =>
      exact Fields.supportedAt_instantiate_outermost depth replacement fields closed supported

theorem Fields.supportedAt_instantiate_outermost {Head : Type} (depth : Nat)
    (replacement : Term Head) (fields : Fields Head)
    (closed : supportedAt 0 replacement = true)
    (supported : Fields.supportedAt (depth + 1) fields = true) :
    Fields.supportedAt depth (Fields.instantiateAt depth replacement fields) = true := by
  cases fields with
  | nil => rfl
  | cons fieldDepth term rest =>
      simp only [Fields.supportedAt, Bool.and_eq_true] at supported
      simp only [Fields.instantiateAt, Fields.supportedAt, Bool.and_eq_true]
      exact ⟨supportedAt_instantiate_outermost (depth + fieldDepth) replacement term
          closed (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using supported.1),
        Fields.supportedAt_instantiate_outermost depth replacement rest closed supported.2⟩

end

mutual

/-- Instantiation preserves a structural signature when its replacement
conforms to the same signature. -/
theorem conforms_instantiateAt {Head : Type} (signature : Head → List Nat)
    (depth : Nat) (replacement term : Term Head)
    (valid : conforms signature replacement = true) :
    conforms signature (instantiateAt depth replacement term) = conforms signature term := by
  cases term with
  | idx index =>
      simp only [instantiateAt]
      split
      · rfl
      · split
        · simpa [conforms] using (conforms_lift signature 0 depth replacement).trans valid
        · rfl
  | node head fields =>
      exact Fields.conforms_instantiateAt signature (signature head) depth replacement fields valid

theorem Fields.conforms_instantiateAt {Head : Type} (signature : Head → List Nat)
    (expected : List Nat) (depth : Nat) (replacement : Term Head)
    (fields : Fields Head) (valid : conforms signature replacement = true) :
    Fields.conforms signature expected (Fields.instantiateAt depth replacement fields) =
      Fields.conforms signature expected fields := by
  cases fields with
  | nil => cases expected <;> rfl
  | cons fieldDepth term rest =>
      cases expected with
      | nil => rfl
      | cons expectedDepth expected =>
          simp only [Fields.instantiateAt, Fields.conforms,
            conforms_instantiateAt signature (depth + fieldDepth) replacement term valid,
            Fields.conforms_instantiateAt signature expected depth replacement rest valid]

end

end Term

end Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
