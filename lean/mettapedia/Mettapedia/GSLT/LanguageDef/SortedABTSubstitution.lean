import Mettapedia.GSLT.LanguageDef.SortedABTRenaming

/-!
# Simultaneous substitution across sorted binding scopes

A replacement can contain free variables of several sorts. Entering a field
therefore weakens that replacement along every sort bound by the field, even
when the variable being replaced belongs to a different sort. The source
carrier and exact binder-list signatures are the existing sorted ABTs.

These are structural binding laws. Support and signature conformance do not
establish a typing judgment, operational adequacy, or a first-class CBPV source
calculus. In particular, ordinary suspension and memoized Need references are
not identified by substitution.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT
namespace Term

abbrev Substitution (VarSort Head : Type) := VarSort → Nat → Term VarSort Head

variable {VarSort Head : Type} [DecidableEq VarSort]

/-- Lift a simultaneous replacement under the complete field binder list.
Newly bound variables stay variables; every free axis of an inserted term is
weakened, not only the axis of the variable being replaced. -/
def liftSubstitution (binders : List VarSort) (σ : Substitution VarSort Head) :
    Substitution VarSort Head :=
  fun sort index =>
    if index < binderCount sort binders then .idx sort index
    else parallelRename (weakenRenaming binders)
      (σ sort (index - binderCount sort binders))

mutual

def parallelSubstitute (σ : Substitution VarSort Head) :
    Term VarSort Head → Term VarSort Head
  | .idx sort index => σ sort index
  | .node head fields => .node head (Fields.parallelSubstitute σ fields)

def Fields.parallelSubstitute (σ : Substitution VarSort Head) :
    Fields VarSort Head → Fields VarSort Head
  | .nil => .nil
  | .cons binders term rest =>
      .cons binders (parallelSubstitute (liftSubstitution binders σ) term)
        (Fields.parallelSubstitute σ rest)

end

@[simp] theorem liftSubstitution_ids (binders : List VarSort) :
    liftSubstitution binders (Term.idx : Substitution VarSort Head) = Term.idx := by
  funext sort index
  by_cases bound : index < binderCount sort binders
  · simp [liftSubstitution, bound]
  · simp [liftSubstitution, bound, parallelRename, weakenRenaming,
      Nat.add_sub_of_le (Nat.le_of_not_gt bound)]

mutual

@[simp] theorem parallelSubstitute_ids (term : Term VarSort Head) :
    parallelSubstitute Term.idx term = term := by
  cases term with
  | idx sort index => rfl
  | node head fields =>
      simp only [parallelSubstitute, Fields.parallelSubstitute_ids fields]

@[simp] theorem Fields.parallelSubstitute_ids (fields : Fields VarSort Head) :
    Fields.parallelSubstitute Term.idx fields = fields := by
  cases fields with
  | nil => rfl
  | cons binders term rest =>
      simp only [Fields.parallelSubstitute, liftSubstitution_ids,
        parallelSubstitute_ids term, Fields.parallelSubstitute_ids rest]

end

theorem liftSubstitution_renaming (binders : List VarSort) (ρ : Renaming VarSort) :
    liftSubstitution binders (fun sort index => (Term.idx sort (ρ sort index) :
      Term VarSort Head)) =
        fun sort index => Term.idx sort (liftRenaming binders ρ sort index) := by
  funext sort index
  by_cases bound : index < binderCount sort binders <;>
    simp [liftSubstitution, liftRenaming, liftIndex, parallelRename, weakenRenaming, bound]

mutual

theorem parallelSubstitute_renaming (ρ : Renaming VarSort) (term : Term VarSort Head) :
    parallelSubstitute (fun sort index => .idx sort (ρ sort index)) term =
      parallelRename ρ term := by
  cases term with
  | idx sort index => rfl
  | node head fields =>
      simp only [parallelSubstitute, parallelRename,
        Fields.parallelSubstitute_renaming ρ fields]

theorem Fields.parallelSubstitute_renaming (ρ : Renaming VarSort)
    (fields : Fields VarSort Head) :
    Fields.parallelSubstitute (fun sort index => .idx sort (ρ sort index)) fields =
      Fields.parallelRename ρ fields := by
  cases fields with
  | nil => rfl
  | cons binders term rest =>
      simp only [Fields.parallelSubstitute, Fields.parallelRename,
        liftSubstitution_renaming, parallelSubstitute_renaming,
        Fields.parallelSubstitute_renaming ρ rest]

end

theorem liftSubstitution_rename (binders : List VarSort)
    (ρ : Renaming VarSort) (σ : Substitution VarSort Head) :
    (fun sort index => parallelRename (liftRenaming binders ρ)
      (liftSubstitution binders σ sort index)) =
        liftSubstitution binders (fun sort index => parallelRename ρ (σ sort index)) := by
  funext sort index
  by_cases bound : index < binderCount sort binders
  · simp [liftSubstitution, bound, parallelRename, liftRenaming, liftIndex]
  · simp only [liftSubstitution, bound, ↓reduceIte]
    exact parallelRename_weaken binders ρ (σ sort (index - binderCount sort binders))

mutual

theorem parallelRename_substitute (ρ : Renaming VarSort)
    (σ : Substitution VarSort Head) (term : Term VarSort Head) :
    parallelRename ρ (parallelSubstitute σ term) =
      parallelSubstitute (fun sort index => parallelRename ρ (σ sort index)) term := by
  cases term with
  | idx sort index => rfl
  | node head fields =>
      simp only [parallelRename, parallelSubstitute,
        Fields.parallelRename_substitute ρ σ fields]

theorem Fields.parallelRename_substitute (ρ : Renaming VarSort)
    (σ : Substitution VarSort Head) (fields : Fields VarSort Head) :
    Fields.parallelRename ρ (Fields.parallelSubstitute σ fields) =
      Fields.parallelSubstitute (fun sort index => parallelRename ρ (σ sort index)) fields := by
  cases fields with
  | nil => rfl
  | cons binders term rest =>
      simp only [Fields.parallelRename, Fields.parallelSubstitute,
        parallelRename_substitute, liftSubstitution_rename,
        Fields.parallelRename_substitute ρ σ rest]

end

theorem liftSubstitution_afterRenaming (binders : List VarSort)
    (σ : Substitution VarSort Head) (ρ : Renaming VarSort) :
    (fun sort index => liftSubstitution binders σ sort (liftRenaming binders ρ sort index)) =
      liftSubstitution binders (fun sort index => σ sort (ρ sort index)) := by
  funext sort index
  by_cases bound : index < binderCount sort binders
  · simp [liftSubstitution, liftRenaming, liftIndex, bound]
  · have above : ¬ binderCount sort binders +
        ρ sort (index - binderCount sort binders) < binderCount sort binders := by omega
    simp [liftSubstitution, liftRenaming, liftIndex, bound, above]

mutual

theorem parallelSubstitute_rename (σ : Substitution VarSort Head)
    (ρ : Renaming VarSort) (term : Term VarSort Head) :
    parallelSubstitute σ (parallelRename ρ term) =
      parallelSubstitute (fun sort index => σ sort (ρ sort index)) term := by
  cases term with
  | idx sort index => rfl
  | node head fields =>
      simp only [parallelSubstitute, parallelRename,
        Fields.parallelSubstitute_rename σ ρ fields]

theorem Fields.parallelSubstitute_rename (σ : Substitution VarSort Head)
    (ρ : Renaming VarSort) (fields : Fields VarSort Head) :
    Fields.parallelSubstitute σ (Fields.parallelRename ρ fields) =
      Fields.parallelSubstitute (fun sort index => σ sort (ρ sort index)) fields := by
  cases fields with
  | nil => rfl
  | cons binders term rest =>
      simp only [Fields.parallelSubstitute, Fields.parallelRename,
        parallelSubstitute_rename, liftSubstitution_afterRenaming,
        Fields.parallelSubstitute_rename σ ρ rest]

end

theorem liftSubstitution_weaken (binders : List VarSort)
    (σ : Substitution VarSort Head) (term : Term VarSort Head) :
    parallelSubstitute (liftSubstitution binders σ)
        (parallelRename (weakenRenaming binders) term) =
      parallelRename (weakenRenaming binders) (parallelSubstitute σ term) := by
  rw [parallelSubstitute_rename, parallelRename_substitute]
  congr 1
  funext sort index
  have above : ¬ binderCount sort binders + index < binderCount sort binders := by omega
  simp [liftSubstitution, weakenRenaming, above]

theorem liftSubstitution_comp (binders : List VarSort)
    (τ σ : Substitution VarSort Head) :
    (fun sort index => parallelSubstitute (liftSubstitution binders τ)
      (liftSubstitution binders σ sort index)) =
      liftSubstitution binders (fun sort index => parallelSubstitute τ (σ sort index)) := by
  funext sort index
  by_cases bound : index < binderCount sort binders
  · simp [liftSubstitution, bound, parallelSubstitute]
  · simp only [liftSubstitution, bound, ↓reduceIte]
    exact liftSubstitution_weaken binders τ (σ sort (index - binderCount sort binders))

mutual

@[simp] theorem parallelSubstitute_comp (τ σ : Substitution VarSort Head)
    (term : Term VarSort Head) :
    parallelSubstitute τ (parallelSubstitute σ term) =
      parallelSubstitute (fun sort index => parallelSubstitute τ (σ sort index)) term := by
  cases term with
  | idx sort index => rfl
  | node head fields =>
      simp only [parallelSubstitute, Fields.parallelSubstitute_comp τ σ fields]

@[simp] theorem Fields.parallelSubstitute_comp (τ σ : Substitution VarSort Head)
    (fields : Fields VarSort Head) :
    Fields.parallelSubstitute τ (Fields.parallelSubstitute σ fields) =
      Fields.parallelSubstitute (fun sort index => parallelSubstitute τ (σ sort index)) fields := by
  cases fields with
  | nil => rfl
  | cons binders term rest =>
      simp only [Fields.parallelSubstitute, parallelSubstitute_comp,
        liftSubstitution_comp, Fields.parallelSubstitute_comp τ σ rest]

end

/-- Replacement environments are qualified independently of the source term.
Only indices actually available in the source context require a replacement. -/
def SubstitutionSupported (source target : VarSort → Nat)
    (σ : Substitution VarSort Head) : Prop :=
  ∀ sort index, index < source sort → supportedAt target (σ sort index) = true

theorem liftSubstitution_supported {source target : VarSort → Nat}
    {σ : Substitution VarSort Head} (supported : SubstitutionSupported source target σ)
    (binders : List VarSort) :
    SubstitutionSupported (enter source binders) (enter target binders)
      (liftSubstitution binders σ) := by
  intro sort index available
  by_cases bound : index < binderCount sort binders
  · simp only [liftSubstitution, bound, ↓reduceIte, supportedAt, decide_eq_true_eq]
    simp only [enter]
    omega
  · simp only [liftSubstitution, bound, ↓reduceIte]
    apply supportedAt_parallelRename (source := target)
    · intro other prior priorBound
      simp only [weakenRenaming, enter]
      omega
    · apply supported
      simp only [enter] at available
      omega

mutual

theorem supportedAt_parallelSubstitute {source target : VarSort → Nat}
    {σ : Substitution VarSort Head} (replacements : SubstitutionSupported source target σ)
    (term : Term VarSort Head) (supported : supportedAt source term = true) :
    supportedAt target (parallelSubstitute σ term) = true := by
  cases term with
  | idx sort index =>
      apply replacements
      simpa only [supportedAt, decide_eq_true_eq] using supported
  | node head fields =>
      exact Fields.supportedAt_parallelSubstitute replacements fields supported

theorem Fields.supportedAt_parallelSubstitute {source target : VarSort → Nat}
    {σ : Substitution VarSort Head} (replacements : SubstitutionSupported source target σ)
    (fields : Fields VarSort Head) (supported : Fields.supportedAt source fields = true) :
    Fields.supportedAt target (Fields.parallelSubstitute σ fields) = true := by
  cases fields with
  | nil => rfl
  | cons binders term rest =>
      simp only [Fields.supportedAt, Bool.and_eq_true] at supported
      simp only [Fields.parallelSubstitute, Fields.supportedAt, Bool.and_eq_true]
      exact ⟨supportedAt_parallelSubstitute
          (liftSubstitution_supported replacements binders) term supported.1,
        Fields.supportedAt_parallelSubstitute replacements rest supported.2⟩

end

theorem liftSubstitution_conforms (signature : Head → List (List VarSort))
    {σ : Substitution VarSort Head}
    (replacements : ∀ sort index, conforms signature (σ sort index) = true)
    (binders : List VarSort) (sort : VarSort) (index : Nat) :
    conforms signature (liftSubstitution binders σ sort index) = true := by
  by_cases bound : index < binderCount sort binders
  · simp [liftSubstitution, bound]
  · simp only [liftSubstitution, bound, ↓reduceIte, conforms_parallelRename]
    exact replacements sort (index - binderCount sort binders)

mutual

theorem conforms_parallelSubstitute (signature : Head → List (List VarSort))
    {σ : Substitution VarSort Head}
    (replacements : ∀ sort index, conforms signature (σ sort index) = true)
    (term : Term VarSort Head) :
    conforms signature (parallelSubstitute σ term) = conforms signature term := by
  cases term with
  | idx sort index => exact replacements sort index
  | node head fields =>
      exact Fields.conforms_parallelSubstitute signature replacements (signature head) fields

theorem Fields.conforms_parallelSubstitute (signature : Head → List (List VarSort))
    {σ : Substitution VarSort Head}
    (replacements : ∀ sort index, conforms signature (σ sort index) = true)
    (expected : List (List VarSort)) (fields : Fields VarSort Head) :
    Fields.conforms signature expected (Fields.parallelSubstitute σ fields) =
      Fields.conforms signature expected fields := by
  cases fields with
  | nil => cases expected <;> rfl
  | cons binders term rest =>
      cases expected with
      | nil => rfl
      | cons expectedBinders expected =>
          simp only [Fields.parallelSubstitute, Fields.conforms,
            conforms_parallelSubstitute signature
              (liftSubstitution_conforms signature replacements binders) term,
            Fields.conforms_parallelSubstitute signature replacements expected rest]

end

/-- Open the newest variable of one sort. The replacement itself may use any
sort, so field entry still uses all-sort lifting. -/
def topSubstitution (target : VarSort) (replacement : Term VarSort Head) :
    Substitution VarSort Head :=
  fun sort index =>
    if sort = target then
      if index = 0 then replacement else .idx sort (index - 1)
    else .idx sort index

def substituteTop (target : VarSort) (replacement body : Term VarSort Head) :
    Term VarSort Head := parallelSubstitute (topSubstitution target replacement) body

theorem topSubstitution_weaken (target : VarSort) (replacement : Term VarSort Head) :
    (fun sort index => topSubstitution target replacement sort
      (weakenRenaming [target] sort index)) = Term.idx := by
  funext sort index
  by_cases same : sort = target
  · subst sort
    simp [topSubstitution, weakenRenaming, binderCount]
  · have different : target ≠ sort := Ne.symm same
    simp [topSubstitution, weakenRenaming, binderCount, same, different]

@[simp] theorem substituteTop_weaken (target : VarSort)
    (replacement term : Term VarSort Head) :
    substituteTop target replacement (parallelRename (weakenRenaming [target]) term) = term := by
  simp only [substituteTop, parallelSubstitute_rename, topSubstitution_weaken,
    parallelSubstitute_ids]

theorem parallelSubstitute_top (σ : Substitution VarSort Head) (target : VarSort)
    (replacement body : Term VarSort Head) :
    parallelSubstitute σ (substituteTop target replacement body) =
      substituteTop target (parallelSubstitute σ replacement)
        (parallelSubstitute (liftSubstitution [target] σ) body) := by
  simp only [substituteTop, parallelSubstitute_comp]
  congr 1
  funext sort index
  by_cases same : sort = target
  · subst sort
    cases index with
    | zero => simp [topSubstitution, liftSubstitution, binderCount, parallelSubstitute]
    | succ index =>
        simp only [topSubstitution, ↓reduceIte, Nat.succ_ne_zero,
          Nat.succ_sub_one, parallelSubstitute]
        simpa [liftSubstitution, binderCount, substituteTop] using
          (substituteTop_weaken target (parallelSubstitute σ replacement) (σ target index)).symm
  · have different : target ≠ sort := Ne.symm same
    simp only [topSubstitution, same, ↓reduceIte, parallelSubstitute]
    simpa [liftSubstitution, binderCount, same, different, substituteTop] using
      (substituteTop_weaken target (parallelSubstitute σ replacement) (σ sort index)).symm

theorem topSubstitution_supported {depth : VarSort → Nat} (target : VarSort)
    {replacement : Term VarSort Head} (supported : supportedAt depth replacement = true) :
    SubstitutionSupported (enter depth [target]) depth (topSubstitution target replacement) := by
  intro sort index available
  by_cases same : sort = target
  · subst sort
    by_cases zero : index = 0
    · simp [topSubstitution, zero, supported]
    · simp only [topSubstitution, ↓reduceIte, zero, supportedAt, decide_eq_true_eq]
      simp [enter, binderCount] at available
      omega
  · have different : target ≠ sort := Ne.symm same
    simp only [topSubstitution, same, ↓reduceIte, supportedAt, decide_eq_true_eq]
    simpa [enter, binderCount, same, different] using available

theorem supportedAt_substituteTop {depth : VarSort → Nat} (target : VarSort)
    {replacement body : Term VarSort Head}
    (replacementSupported : supportedAt depth replacement = true)
    (bodySupported : supportedAt (enter depth [target]) body = true) :
    supportedAt depth (substituteTop target replacement body) = true :=
  supportedAt_parallelSubstitute (topSubstitution_supported target replacementSupported)
    body bodySupported

#print axioms parallelSubstitute_ids
#print axioms parallelSubstitute_renaming
#print axioms parallelRename_substitute
#print axioms parallelSubstitute_rename
#print axioms parallelSubstitute_comp
#print axioms supportedAt_parallelSubstitute
#print axioms conforms_parallelSubstitute
#print axioms substituteTop_weaken
#print axioms parallelSubstitute_top
#print axioms supportedAt_substituteTop

end Term
end Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT
