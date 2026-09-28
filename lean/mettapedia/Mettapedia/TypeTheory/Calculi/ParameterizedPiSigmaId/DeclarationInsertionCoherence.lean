import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation

/-!
# Coherence of one fresh declaration insertion

Installing one fresh declaration after a prior signature and inserting it
into that signature have the same selected types and root computation steps.
This comparison is about the actual declaration machinery, independently of
the language that supplies the typed entry.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration

variable {Head : Type}

/-- Inserting a name not owned by the prior signature retains every old entry
and every separately licensed root step. -/
theorem Signature.extends_insert_of_absent (prior : Signature Head)
    (name : DeclName) (entry : Entry Head)
    (absent : prior.entries name = none) :
    prior.Extends (prior.insert name entry) where
  entries := by
    intro candidate selectedEntry selected
    by_cases same : candidate = name
    · subst candidate
      rw [absent] at selected
      cases selected
    · simpa [Signature.insert, same] using selected
  computation := by
    intro n left right step
    simpa [Signature.insert] using step

/-- Freshness in the installed rules implies absence from both the base's
type table and the prior signature inventory. -/
private theorem fresh_absent (base : Rules Head) (prior : Signature Head)
    (name : DeclName)
    (fresh : (extendRules base prior).constantType name = none) :
    prior.entries name = none := by
  unfold extendRules combinedType at fresh
  cases baseType : base.constantType name with
  | some type => simp [baseType] at fresh
  | none =>
      cases priorEntry : prior.entries name with
      | none => rfl
      | some entry => simp [baseType, Signature.typeOf?, priorEntry] at fresh

private theorem singleton_value_iff (name candidate : DeclName) (entry : Entry Head)
    (value : Tm Head 0) :
    (Signature.ofList [(name, entry)]).valueOf? candidate = some value ↔
      candidate = name ∧ entry.value? = some value := by
  by_cases same : candidate = name
  · subst candidate
    simp [Signature.ofList, Signature.valueOf?, Signature.insert]
  · simp [Signature.ofList, Signature.valueOf?, Signature.insert, Signature.empty, same]

private theorem insert_value_of_prior (prior : Signature Head)
    (name : DeclName) (entry : Entry Head)
    (absent : prior.entries name = none) {candidate : DeclName} {value : Tm Head 0}
    (known : prior.valueOf? candidate = some value) :
    (prior.insert name entry).valueOf? candidate = some value :=
  (Signature.extends_insert_of_absent prior name entry absent).valueOf known

/-- Sequential and inserted signatures license precisely the same root
computation steps when the new name is fresh. Both directions matter: the
semantic signature cannot silently add a reduction the checker did not admit. -/
theorem rootStep_sequential_iff_insert
    (base : Rules Head) (prior : Signature Head)
    (name : DeclName) (entry : Entry Head)
    (fresh : (extendRules base prior).constantType name = none)
    {n : Nat} {left right : Tm Head n} :
    RootStep (extendRules base prior) (Signature.ofList [(name, entry)]) n left right ↔
      RootStep base (prior.insert name entry) n left right := by
  have absent := fresh_absent base prior name fresh
  constructor
  · intro step
    cases step with
    | inherited old =>
        cases old with
        | inherited core => exact .inherited core
        | delta selected => exact .delta (insert_value_of_prior prior name entry absent selected)
        | declared licensed => exact .declared licensed
    | @delta selectedName value selected =>
        obtain ⟨same, valueSame⟩ :=
          (singleton_value_iff name selectedName entry value).mp selected
        subst selectedName
        exact .delta (by simpa [Signature.valueOf?, Signature.insert] using valueSame)
    | declared impossible =>
        rw [Signature.computation_ofList] at impossible
        exact impossible.elim
  · intro step
    cases step with
    | inherited core => exact .inherited (.inherited core)
    | @delta selectedName value selected =>
        by_cases same : selectedName = name
        · subst selectedName
          have valueSame : entry.value? = some value := by
            simpa [Signature.valueOf?, Signature.insert] using selected
          exact .delta ((singleton_value_iff name name entry value).mpr ⟨rfl, valueSame⟩)
        · have priorSelected : prior.valueOf? selectedName = some value := by
            simpa [Signature.valueOf?, Signature.insert, same] using selected
          exact .inherited (.delta priorSelected)
    | declared licensed => exact .inherited (.declared licensed)

/-- The sequential checker and inserted-signature presentation select the
same type for every global name, including names already owned by `base`. -/
theorem constantType_sequential_eq_insert
    (base : Rules Head) (prior : Signature Head)
    (name : DeclName) (entry : Entry Head)
    (fresh : (extendRules base prior).constantType name = none)
    (candidate : DeclName) :
    (extendRules (extendRules base prior) (Signature.ofList [(name, entry)])).constantType
        candidate =
      (extendRules base (prior.insert name entry)).constantType candidate := by
  by_cases same : candidate = name
  · subst candidate
    simp [extendRules, combinedType, Signature.typeOf?, Signature.ofList,
      Signature.insert, Signature.empty, fresh_absent base prior name fresh]
    unfold extendRules combinedType at fresh
    cases baseType : base.constantType name with
    | some type => simp [baseType] at fresh
    | none => simp [baseType] at fresh ⊢
  · simp [extendRules, combinedType, Signature.typeOf?, Signature.ofList,
      Signature.insert, Signature.empty, same]
    cases base.constantType candidate with
    | some _ => rfl
    | none => cases prior.entries candidate <;> rfl

/-- Root-computation structures are equal when their step predicates agree.
The renaming and substitution fields are proofs and hence proof-irrelevant. -/
theorem rootComputation_ext_step {first second : RootComputation Head}
    (same : ∀ {n : Nat} (left right : Tm Head n),
      first.step left right ↔ second.step left right) : first = second := by
  cases first with
  | mk firstStep firstRename firstSubstitute =>
      cases second with
      | mk secondStep secondRename secondSubstitute =>
          have stepEqual : @firstStep = @secondStep := by
            funext n left right
            exact propext (same left right)
          cases stepEqual
          rfl

/-- The two installation routes have exactly the same computation structure,
not merely examples of matching δ-steps. -/
theorem rootComputation_sequential_eq_insert
    (base : Rules Head) (prior : Signature Head)
    (name : DeclName) (entry : Entry Head)
    (fresh : (extendRules base prior).constantType name = none) :
    (extendRules (extendRules base prior) (Signature.ofList [(name, entry)])).computation =
      (extendRules base (prior.insert name entry)).computation := by
  apply rootComputation_ext_step
  intro n left right
  exact rootStep_sequential_iff_insert base prior name entry fresh

/-- A fresh sequential admission and an inserted signature are the *same*
rules package. Thus typing, conversion, and computation can be transported by
equality rather than maintained as parallel authorities. -/
theorem extendRules_sequential_eq_insert
    (base : Rules Head) (prior : Signature Head)
    (name : DeclName) (entry : Entry Head)
    (fresh : (extendRules base prior).constantType name = none) :
    extendRules (extendRules base prior) (Signature.ofList [(name, entry)]) =
      extendRules base (prior.insert name entry) := by
  have selected :
      (extendRules (extendRules base prior) (Signature.ofList [(name, entry)])).constantType =
      (extendRules base (prior.insert name entry)).constantType := by
    funext candidate
    exact constantType_sequential_eq_insert base prior name entry fresh candidate
  have reduction := rootComputation_sequential_eq_insert base prior name entry fresh
  exact congrArg₂
    (fun constantType computation =>
      ({ base with constantType := constantType, computation := computation } : Rules Head))
    selected reduction

/-- Freshness is necessary. If an earlier declaration owns the name,
sequential installation retains its selected type while insertion replaces
it. The distinction is observable whenever the two entries have different
types and the base rules do not own the name. -/
theorem nonfresh_insertion_changes_type
    (base : Rules Head) (name : DeclName) (first second : Entry Head)
    (baseAbsent : base.constantType name = none)
    (different : first.type ≠ second.type) :
    (extendRules
        (extendRules base (Signature.ofList [(name, first)]))
        (Signature.ofList [(name, second)])).constantType name ≠
      (extendRules base
        ((Signature.ofList [(name, first)]).insert name second)).constantType name := by
  intro equal
  have selectedFirst :
      (extendRules
        (extendRules base (Signature.ofList [(name, first)]))
        (Signature.ofList [(name, second)])).constantType name = some first.type := by
    simp [extendRules, combinedType, Signature.ofList, Signature.insert,
      Signature.empty, Signature.typeOf?, baseAbsent]
  have selectedSecond :
      (extendRules base
        ((Signature.ofList [(name, first)]).insert name second)).constantType name =
          some second.type := by
    simp [extendRules, combinedType, Signature.ofList, Signature.insert,
      Signature.empty, Signature.typeOf?, baseAbsent]
  rw [selectedFirst, selectedSecond] at equal
  exact different (Option.some.inj equal)

#print axioms Signature.extends_insert_of_absent
#print axioms rootStep_sequential_iff_insert
#print axioms constantType_sequential_eq_insert
#print axioms rootComputation_ext_step
#print axioms extendRules_sequential_eq_insert
#print axioms nonfresh_insertion_changes_type

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration
