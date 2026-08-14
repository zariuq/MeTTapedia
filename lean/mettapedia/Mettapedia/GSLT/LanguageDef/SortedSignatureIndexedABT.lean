/-!
# Sorted signature-indexed abstract binding trees

This carrier generalizes the one-axis signature-indexed ABT to independent
de Bruijn sorts.  Every variable leaf names its sort, and every constructor
field records the list of variable sorts bound on entry.  Lift,
substitution, unused-binder removal, and support checking act on one selected
sort while leaving every other axis unchanged.

Binder lists are retained as physical signature data rather than collapsed
to a total depth.  This lets decoding and conformance reject a field that
binds the right number of variables of the wrong sort.
-/

namespace Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT

set_option autoImplicit false

mutual

/-- One ABT whose locally bound indices are partitioned by `VarSort`. -/
inductive Term (VarSort : Type) (Head : Type) where
  | idx (sort : VarSort) (value : Nat)
  | node (head : Head) (fields : Fields VarSort Head)

/-- Constructor fields decorated by the sorts bound on field entry. -/
inductive Fields (VarSort : Type) (Head : Type) where
  | nil
  | cons (binders : List VarSort) (term : Term VarSort Head)
      (rest : Fields VarSort Head)

end

deriving instance DecidableEq for Term, Fields

namespace Term

/-- Number of binders of one sort introduced by a field. -/
def binderCount {VarSort : Type} [DecidableEq VarSort]
    (sort : VarSort) (binders : List VarSort) : Nat :=
  binders.count sort

@[simp] theorem binderCount_nil {VarSort : Type} [DecidableEq VarSort]
    (sort : VarSort) :
    binderCount sort [] = 0 := by
  simp [binderCount]

@[simp] theorem binderCount_cons {VarSort : Type} [DecidableEq VarSort]
    (target binder : VarSort) (binders : List VarSort) :
    binderCount target (binder :: binders) =
      (if binder = target then 1 else 0) + binderCount target binders := by
  by_cases same : binder = target <;>
    simp [binderCount, same, Nat.add_comm]

mutual

/-- Shift one selected variable sort at or above `cutoff`. -/
def lift {VarSort Head : Type} [DecidableEq VarSort]
    (target : VarSort) (cutoff amount : Nat) : Term VarSort Head →
    Term VarSort Head
  | .idx sort index =>
      if sort = target then
        if index < cutoff then .idx sort index else .idx sort (index + amount)
      else .idx sort index
  | .node head fields =>
      .node head (Fields.lift target cutoff amount fields)

/-- Enter each field under exactly its binders of the selected sort. -/
def Fields.lift {VarSort Head : Type} [DecidableEq VarSort]
    (target : VarSort) (cutoff amount : Nat) : Fields VarSort Head →
    Fields VarSort Head
  | .nil => .nil
  | .cons binders term rest =>
      .cons binders
        (lift target (cutoff + binderCount target binders) amount term)
        (Fields.lift target cutoff amount rest)

end

mutual

/-- Binder-eliminating substitution on one selected variable sort. -/
def instantiateAt {VarSort Head : Type} [DecidableEq VarSort]
    (target : VarSort) (depth : Nat) (replacement : Term VarSort Head) :
    Term VarSort Head → Term VarSort Head
  | .idx sort index =>
      if sort = target then
        if index < depth then .idx sort index
        else if index = depth then lift target 0 depth replacement
        else .idx sort (index - 1)
      else .idx sort index
  | .node head fields =>
      .node head (Fields.instantiateAt target depth replacement fields)

/-- Substitute beneath the selected-sort binders of every field. -/
def Fields.instantiateAt {VarSort Head : Type} [DecidableEq VarSort]
    (target : VarSort) (depth : Nat) (replacement : Term VarSort Head) :
    Fields VarSort Head → Fields VarSort Head
  | .nil => .nil
  | .cons binders term rest =>
      .cons binders
        (instantiateAt target (depth + binderCount target binders)
          replacement term)
        (Fields.instantiateAt target depth replacement rest)

end

def instantiate {VarSort Head : Type} [DecidableEq VarSort]
    (target : VarSort) (replacement body : Term VarSort Head) :
    Term VarSort Head :=
  instantiateAt target 0 replacement body

mutual

/-- Remove one unused binder on a selected axis, failing if it occurs. -/
def dropAt? {VarSort Head : Type} [DecidableEq VarSort]
    (target : VarSort) (cutoff : Nat) : Term VarSort Head →
    Option (Term VarSort Head)
  | .idx sort index =>
      if sort = target then
        if index < cutoff then some (.idx sort index)
        else if index = cutoff then none
        else some (.idx sort (index - 1))
      else some (.idx sort index)
  | .node head fields =>
      return .node head (← Fields.dropAt? target cutoff fields)

/-- Remove a binder beneath the selected-sort binders of every field. -/
def Fields.dropAt? {VarSort Head : Type} [DecidableEq VarSort]
    (target : VarSort) (cutoff : Nat) : Fields VarSort Head →
    Option (Fields VarSort Head)
  | .nil => some .nil
  | .cons binders term rest => do
      let droppedTerm ←
        dropAt? target (cutoff + binderCount target binders) term
      let droppedRest ← Fields.dropAt? target cutoff rest
      some (.cons binders droppedTerm droppedRest)

end

mutual

/-- Removing an unused binder and then lifting by one reconstructs the exact
original sorted ABT.  This is the constructive direction needed by eta
certificates: a successful partial drop yields a replayable shift witness. -/
theorem lift_of_dropAt?_eq_some
    {VarSort Head : Type} [DecidableEq VarSort]
    (target : VarSort) (cutoff : Nat)
    {term dropped : Term VarSort Head}
    (hypothesis : dropAt? target cutoff term = some dropped) :
    lift target cutoff 1 dropped = term := by
  cases term with
  | idx sort index =>
      by_cases same : sort = target
      · subst same
        by_cases below : index < cutoff
        · simp [dropAt?, below] at hypothesis
          subst dropped
          simp [lift, below]
        · by_cases equal : index = cutoff
          · simp [dropAt?, equal] at hypothesis
          · have above : cutoff < index := Nat.lt_of_le_of_ne
                (Nat.le_of_not_gt below) (Ne.symm equal)
            have shiftedAbove : ¬ index - 1 < cutoff := by omega
            have restores : index - 1 + 1 = index := by omega
            simp [dropAt?, below, equal] at hypothesis
            subst dropped
            simp [lift, shiftedAbove, restores]
      · simp [dropAt?, same] at hypothesis
        subst dropped
        simp [lift, same]
  | node head fields =>
      simp only [dropAt?] at hypothesis
      cases fieldsResult : Fields.dropAt? target cutoff fields with
      | none => simp [fieldsResult] at hypothesis
      | some droppedFields =>
          simp [fieldsResult] at hypothesis
          subst dropped
          simp [lift, Fields.lift_of_dropAt?_eq_some target cutoff
            fieldsResult]

/-- Fieldwise companion to `lift_of_dropAt?_eq_some`. -/
theorem Fields.lift_of_dropAt?_eq_some
    {VarSort Head : Type} [DecidableEq VarSort]
    (target : VarSort) (cutoff : Nat)
    {fields dropped : Fields VarSort Head}
    (hypothesis : Fields.dropAt? target cutoff fields = some dropped) :
    Fields.lift target cutoff 1 dropped = fields := by
  cases fields with
  | nil =>
      simp [Fields.dropAt?] at hypothesis
      subst dropped
      rfl
  | cons binders term rest =>
      simp only [Fields.dropAt?] at hypothesis
      cases termResult :
          dropAt? target (cutoff + binderCount target binders) term with
      | none => simp [termResult] at hypothesis
      | some droppedTerm =>
          cases restResult : Fields.dropAt? target cutoff rest with
          | none => simp [termResult, restResult] at hypothesis
          | some droppedRest =>
              simp [termResult, restResult] at hypothesis
              subst dropped
              simp [Fields.lift,
                lift_of_dropAt?_eq_some target
                  (cutoff + binderCount target binders) termResult,
                Fields.lift_of_dropAt?_eq_some target cutoff restResult]

end

/-- Extend a per-sort support depth by one field's binder list. -/
def enter {VarSort : Type} [DecidableEq VarSort]
    (depth : VarSort → Nat) (binders : List VarSort) : VarSort → Nat :=
  fun sort => depth sort + binderCount sort binders

@[simp] theorem enter_nil {VarSort : Type} [DecidableEq VarSort]
    (depth : VarSort → Nat) :
    enter depth [] = depth := by
  funext sort
  simp [enter]

mutual

/-- Check every index against the support depth for its own sort. -/
def supportedAt {VarSort Head : Type} [DecidableEq VarSort]
    (depth : VarSort → Nat) : Term VarSort Head → Bool
  | .idx sort index => decide (index < depth sort)
  | .node _ fields => Fields.supportedAt depth fields

/-- Scope checking beneath every sort introduced by a field. -/
def Fields.supportedAt {VarSort Head : Type} [DecidableEq VarSort]
    (depth : VarSort → Nat) : Fields VarSort Head → Bool
  | .nil => true
  | .cons binders term rest =>
      supportedAt (enter depth binders) term &&
        Fields.supportedAt depth rest

end

mutual

/-- Verify the exact sorted field signature recursively. -/
def conforms {VarSort Head : Type} [DecidableEq VarSort]
    (signature : Head → List (List VarSort)) : Term VarSort Head → Bool
  | .idx _ _ => true
  | .node head fields => Fields.conforms signature (signature head) fields

def Fields.conforms {VarSort Head : Type} [DecidableEq VarSort]
    (signature : Head → List (List VarSort)) :
    List (List VarSort) → Fields VarSort Head → Bool
  | [], .nil => true
  | expectedBinders :: expected, .cons actualBinders term rest =>
      decide (actualBinders = expectedBinders) && conforms signature term &&
        Fields.conforms signature expected rest
  | _, _ => false

end

@[simp] theorem conforms_idx {VarSort Head : Type} [DecidableEq VarSort]
    (signature : Head → List (List VarSort)) (sort : VarSort) (index : Nat) :
    conforms signature (.idx sort index) = true :=
  rfl

mutual

/-- Axis-selective shifting preserves the exact sorted signature. -/
theorem conforms_lift {VarSort Head : Type} [DecidableEq VarSort]
    (signature : Head → List (List VarSort))
    (target : VarSort) (cutoff amount : Nat) (term : Term VarSort Head) :
    conforms signature (lift target cutoff amount term) =
      conforms signature term := by
  cases term with
  | idx sort index =>
      by_cases same : sort = target <;>
        by_cases below : index < cutoff <;>
          simp [lift, conforms, same, below]
  | node head fields =>
      simp [lift, conforms,
        Fields.conforms_lift signature (signature head)
          target cutoff amount fields]

theorem Fields.conforms_lift {VarSort Head : Type} [DecidableEq VarSort]
    (signature : Head → List (List VarSort)) (expected : List (List VarSort))
    (target : VarSort) (cutoff amount : Nat) (fields : Fields VarSort Head) :
    Fields.conforms signature expected
        (Fields.lift target cutoff amount fields) =
      Fields.conforms signature expected fields := by
  cases fields with
  | nil => cases expected <;> rfl
  | cons binders term rest =>
      cases expected with
      | nil => rfl
      | cons expectedBinders expected =>
          simp [Fields.lift, Fields.conforms,
            conforms_lift signature target
              (cutoff + binderCount target binders) amount term,
            Fields.conforms_lift signature expected target cutoff amount rest]

end


end Term

end Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT
