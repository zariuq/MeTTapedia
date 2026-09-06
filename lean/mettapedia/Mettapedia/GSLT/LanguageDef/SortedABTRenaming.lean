import Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT

/-!
# Simultaneous renaming for sorted abstract binding trees

Every variable sort has its own renaming. Entering a field lifts that family
along all of the field's binders, leaving the new bound variables fixed.
Weakening likewise shifts every sort mentioned by the binder list. These
operations support replacements that may themselves contain variables of
several sorts; the existing selected-axis operations remain unchanged.

The laws concern the existing raw sorted ABT carrier. Scope preservation has
an explicit coordinate-wise premise, and signature preservation retains the
complete authored binder lists. No object-language typing, evaluation, or
substitution of computations for mathematical terms is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT
namespace Term

variable {VarSort Head : Type}

abbrev Renaming (VarSort : Type) := VarSort → Nat → Nat

/-- Extend a variable renaming beneath a fixed number of same-sort binders. -/
def liftIndex (count : Nat) (ρ : Nat → Nat) (index : Nat) : Nat :=
  if index < count then index else count + ρ (index - count)

@[simp] theorem liftIndex_below (count : Nat) (ρ : Nat → Nat) {index : Nat}
    (below : index < count) : liftIndex count ρ index = index := by
  simp [liftIndex, below]

@[simp] theorem liftIndex_add (count : Nat) (ρ : Nat → Nat) (index : Nat) :
    liftIndex count ρ (count + index) = count + ρ index := by
  have above : ¬ count + index < count := by omega
  simp [liftIndex, above]

@[simp] theorem liftIndex_id (count index : Nat) :
    liftIndex count id index = index := by
  by_cases below : index < count
  · exact liftIndex_below count id below
  · simp only [liftIndex, below, ↓reduceIte, id_eq]
    omega

theorem liftIndex_comp (count : Nat) (ρ ξ : Nat → Nat) (index : Nat) :
    liftIndex count ρ (liftIndex count ξ index) =
      liftIndex count (fun value => ρ (ξ value)) index := by
  by_cases below : index < count
  · simp [liftIndex, below]
  · simp only [liftIndex, below, ↓reduceIte]
    have shifted : ¬ count + ξ (index - count) < count := by omega
    simp [shifted]

theorem liftIndex_sum (first second : Nat) (ρ : Nat → Nat) (index : Nat) :
    liftIndex (first + second) ρ index =
      liftIndex first (liftIndex second ρ) index := by
  by_cases belowFirst : index < first
  · have belowAll : index < first + second := by omega
    simp [liftIndex, belowFirst, belowAll]
  · by_cases belowAll : index < first + second
    · have belowSecond : index - first < second := by omega
      simp only [liftIndex, belowFirst, belowAll, belowSecond, ↓reduceIte]
      omega
    · have aboveSecond : ¬ index - first < second := by omega
      simp [liftIndex, belowFirst, belowAll, aboveSecond, Nat.sub_sub, Nat.add_assoc]

variable [DecidableEq VarSort]

/-- Lift every variable axis beneath exactly the field's authored binders. -/
def liftRenaming (binders : List VarSort) (ρ : Renaming VarSort) : Renaming VarSort :=
  fun sort => liftIndex (binderCount sort binders) (ρ sort)

/-- Shift free variables on every axis bound by the given field. -/
def weakenRenaming (binders : List VarSort) : Renaming VarSort :=
  fun sort index => binderCount sort binders + index

@[simp] theorem liftRenaming_id (binders : List VarSort) :
    liftRenaming binders (fun _ index => index) = (fun _ index => index) := by
  funext sort index
  exact liftIndex_id _ _

theorem liftRenaming_comp (binders : List VarSort) (ρ ξ : Renaming VarSort) :
    (fun sort index => liftRenaming binders ρ sort (liftRenaming binders ξ sort index)) =
      liftRenaming binders (fun sort index => ρ sort (ξ sort index)) := by
  funext sort index
  exact liftIndex_comp _ _ _ _

@[simp] theorem liftRenaming_below (binders : List VarSort) (ρ : Renaming VarSort)
    (sort : VarSort) {index : Nat} (below : index < binderCount sort binders) :
    liftRenaming binders ρ sort index = index :=
  liftIndex_below _ _ below

@[simp] theorem liftRenaming_weaken (binders : List VarSort) (ρ : Renaming VarSort)
    (sort : VarSort) (index : Nat) :
    liftRenaming binders ρ sort (weakenRenaming binders sort index) =
      weakenRenaming binders sort (ρ sort index) :=
  liftIndex_add _ _ _

theorem liftRenaming_append (first second : List VarSort) (ρ : Renaming VarSort) :
    liftRenaming (first ++ second) ρ = liftRenaming first (liftRenaming second ρ) := by
  funext sort index
  simp only [liftRenaming, binderCount, List.count_append]
  exact liftIndex_sum _ _ _ _

@[simp] theorem liftRenaming_nil (ρ : Renaming VarSort) : liftRenaming [] ρ = ρ := by
  funext sort index
  simp [liftRenaming, liftIndex]

@[simp] theorem weakenRenaming_nil :
    weakenRenaming ([] : List VarSort) = (fun _ index => index) := by
  funext sort index
  simp [weakenRenaming]

theorem weakenRenaming_append (first second : List VarSort) :
    weakenRenaming (first ++ second) =
      (fun sort index => weakenRenaming first sort (weakenRenaming second sort index)) := by
  funext sort index
  simp [weakenRenaming, binderCount, List.count_append, Nat.add_assoc]

mutual

def parallelRename (ρ : Renaming VarSort) : Term VarSort Head → Term VarSort Head
  | .idx sort index => .idx sort (ρ sort index)
  | .node head fields => .node head (Fields.parallelRename ρ fields)

def Fields.parallelRename (ρ : Renaming VarSort) : Fields VarSort Head → Fields VarSort Head
  | .nil => .nil
  | .cons binders term rest =>
      .cons binders (parallelRename (liftRenaming binders ρ) term) (Fields.parallelRename ρ rest)

end

theorem parallelRename_ext {ρ ξ : Renaming VarSort} (equal : ∀ sort index, ρ sort index = ξ sort index)
    (term : Term VarSort Head) : parallelRename ρ term = parallelRename ξ term := by
  rw [funext (fun sort => funext (equal sort))]

theorem Fields.parallelRename_ext {ρ ξ : Renaming VarSort}
    (equal : ∀ sort index, ρ sort index = ξ sort index) (fields : Fields VarSort Head) :
    Fields.parallelRename ρ fields = Fields.parallelRename ξ fields := by
  rw [funext (fun sort => funext (equal sort))]

mutual

@[simp] theorem parallelRename_id (term : Term VarSort Head) :
    parallelRename (fun _ index => index) term = term := by
  cases term with
  | idx sort index => rfl
  | node head fields => simp [parallelRename, Fields.parallelRename_id fields]

@[simp] theorem Fields.parallelRename_id (fields : Fields VarSort Head) :
    Fields.parallelRename (fun _ index => index) fields = fields := by
  cases fields with
  | nil => rfl
  | cons binders term rest =>
      simp [Fields.parallelRename, parallelRename_id term, Fields.parallelRename_id rest]

end

mutual

theorem parallelRename_comp (ρ ξ : Renaming VarSort) (term : Term VarSort Head) :
    parallelRename ρ (parallelRename ξ term) =
      parallelRename (fun sort index => ρ sort (ξ sort index)) term := by
  cases term with
  | idx sort index => rfl
  | node head fields => simp [parallelRename, Fields.parallelRename_comp ρ ξ fields]

theorem Fields.parallelRename_comp (ρ ξ : Renaming VarSort) (fields : Fields VarSort Head) :
    Fields.parallelRename ρ (Fields.parallelRename ξ fields) =
      Fields.parallelRename (fun sort index => ρ sort (ξ sort index)) fields := by
  cases fields with
  | nil => rfl
  | cons binders term rest =>
      simp [Fields.parallelRename,
        parallelRename_comp (liftRenaming binders ρ) (liftRenaming binders ξ) term,
        liftRenaming_comp, Fields.parallelRename_comp ρ ξ rest]

end

/-- Renaming a weakened replacement fixes newly bound variables on every sort. -/
theorem parallelRename_weaken (binders : List VarSort) (ρ : Renaming VarSort)
    (term : Term VarSort Head) :
    parallelRename (liftRenaming binders ρ) (parallelRename (weakenRenaming binders) term) =
      parallelRename (weakenRenaming binders) (parallelRename ρ term) := by
  rw [parallelRename_comp, parallelRename_comp]
  apply parallelRename_ext
  exact liftRenaming_weaken binders ρ

theorem parallelRename_weaken_append (first second : List VarSort) (term : Term VarSort Head) :
    parallelRename (weakenRenaming (first ++ second)) term =
      parallelRename (weakenRenaming first) (parallelRename (weakenRenaming second) term) := by
  rw [parallelRename_comp, weakenRenaming_append]

/-- Coordinate-wise scope compatibility lifts beneath all field binders. -/
theorem liftRenaming_supported {source target : VarSort → Nat} {ρ : Renaming VarSort}
    (bounded : ∀ sort index, index < source sort → ρ sort index < target sort)
    (binders : List VarSort) (sort : VarSort) (index : Nat)
    (inside : index < enter source binders sort) :
    liftRenaming binders ρ sort index < enter target binders sort := by
  by_cases below : index < binderCount sort binders
  · rw [liftRenaming_below binders ρ sort below]
    simp only [enter]
    omega
  · have original : index - binderCount sort binders < source sort := by
      simp only [enter] at inside
      omega
    have renamed := bounded sort (index - binderCount sort binders) original
    simp only [liftRenaming, liftIndex, below, ↓reduceIte, enter]
    omega

mutual

theorem supportedAt_parallelRename {source target : VarSort → Nat} {ρ : Renaming VarSort}
    (bounded : ∀ sort index, index < source sort → ρ sort index < target sort)
    (term : Term VarSort Head) (supported : supportedAt source term = true) :
    supportedAt target (parallelRename ρ term) = true := by
  cases term with
  | idx sort index =>
      simp only [parallelRename, supportedAt, decide_eq_true_eq] at supported ⊢
      exact bounded sort index supported
  | node head fields =>
      exact Fields.supportedAt_parallelRename bounded fields supported

theorem Fields.supportedAt_parallelRename {source target : VarSort → Nat} {ρ : Renaming VarSort}
    (bounded : ∀ sort index, index < source sort → ρ sort index < target sort)
    (fields : Fields VarSort Head) (supported : Fields.supportedAt source fields = true) :
    Fields.supportedAt target (Fields.parallelRename ρ fields) = true := by
  cases fields with
  | nil => rfl
  | cons binders term rest =>
      simp only [Fields.supportedAt, Bool.and_eq_true] at supported
      simp only [Fields.parallelRename, Fields.supportedAt, Bool.and_eq_true]
      exact ⟨supportedAt_parallelRename (liftRenaming_supported bounded binders) term supported.1,
        Fields.supportedAt_parallelRename bounded rest supported.2⟩

end

mutual

@[simp] theorem conforms_parallelRename (signature : Head → List (List VarSort))
    (ρ : Renaming VarSort) (term : Term VarSort Head) :
    conforms signature (parallelRename ρ term) = conforms signature term := by
  cases term with
  | idx sort index => rfl
  | node head fields =>
      exact Fields.conforms_parallelRename signature (signature head) ρ fields

@[simp] theorem Fields.conforms_parallelRename (signature : Head → List (List VarSort))
    (expected : List (List VarSort)) (ρ : Renaming VarSort) (fields : Fields VarSort Head) :
    Fields.conforms signature expected (Fields.parallelRename ρ fields) =
      Fields.conforms signature expected fields := by
  cases fields with
  | nil => cases expected <;> rfl
  | cons binders term rest =>
      cases expected with
      | nil => rfl
      | cons expectedBinders expected =>
          simp only [Fields.parallelRename, Fields.conforms,
            conforms_parallelRename signature (liftRenaming binders ρ) term,
            Fields.conforms_parallelRename signature expected ρ rest]

end

section Controls

private inductive Axis where
  | value
  | need
  deriving DecidableEq

private def mixedReplacement : Term Axis Unit :=
  .node () (.cons [] (.idx .value 0) (.cons [] (.idx .need 0) .nil))

/-- A replacement's outer need reference is weakened even when its value
variables stay at the same depth. -/
theorem need_binder_weakens_mixed_replacement :
    parallelRename (weakenRenaming [Axis.need]) mixedReplacement =
      .node () (.cons [] (.idx .value 0) (.cons [] (.idx .need 1) .nil)) := by
  decide

/-- Shifting only the value axis would retain a captured need reference. -/
theorem need_binder_not_value_only_shift :
    parallelRename (weakenRenaming [Axis.need]) mixedReplacement ≠
      lift Axis.value 0 0 mixedReplacement := by
  decide

end Controls

#print axioms parallelRename_id
#print axioms parallelRename_comp
#print axioms parallelRename_weaken
#print axioms supportedAt_parallelRename
#print axioms conforms_parallelRename
#print axioms need_binder_weakens_mixed_replacement
#print axioms need_binder_not_value_only_shift

end Term
end Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT
