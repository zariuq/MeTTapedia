import Mettapedia.Languages.Maude.Semantics
import Mettapedia.Languages.Maude.DecidableEquality
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Nodup

/-! Typed fold presentations of one declared ACU operation. The certificate
names the actual operator and its complete identity term. Folding retains
multiplicity; permutation is licensed by commutativity. These results use
the source equation relation and do not replace a module's E-normalization,
coherence certificate or native matcher correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude

structure ACUOperation (theory : Theory) (context : VariableContext) where
  declaration : Operator
  declared : declaration ∈ theory.signature.operators
  arguments : declaration.arguments = [declaration.result, declaration.result]
  associative : declaration.attributes.associative = true
  commutative : declaration.attributes.commutative = true
  unit : Term
  identity : declaration.attributes.identity = some unit
  unit_sorted : HasSort theory.signature context unit declaration.result

namespace ACUOperation

variable {theory : Theory} {context : VariableContext}

def merge (operation : ACUOperation theory context) (left right : Term) : Term :=
  .app operation.declaration.id [left, right]

def fold (operation : ACUOperation theory context) : List Term → Term
  | [] => operation.unit
  | first :: rest => operation.merge first (operation.fold rest)

def Sorted (operation : ACUOperation theory context) (terms : List Term) : Prop :=
  ∀ term ∈ terms, HasSort theory.signature context term operation.declaration.result

theorem merge_sorted (operation : ACUOperation theory context) {left right : Term}
    (first : HasSort theory.signature context left operation.declaration.result)
    (second : HasSort theory.signature context right operation.declaration.result) :
    HasSort theory.signature context (operation.merge left right) operation.declaration.result := by
  apply HasSort.app operation.declared
  rw [operation.arguments]
  exact .cons first (.cons second .nil)

theorem fold_sorted (operation : ACUOperation theory context) (terms : List Term)
    (sorted : operation.Sorted terms) :
    HasSort theory.signature context (operation.fold terms) operation.declaration.result := by
  induction terms with
  | nil => exact operation.unit_sorted
  | cons first rest ih =>
      exact operation.merge_sorted (sorted first (by simp)) (ih (fun term member => sorted term (by simp [member])))

theorem assoc (operation : ACUOperation theory context) {first second third : Term}
    (firstSorted : HasSort theory.signature context first operation.declaration.result)
    (secondSorted : HasSort theory.signature context second operation.declaration.result)
    (thirdSorted : HasSort theory.signature context third operation.declaration.result) :
    Equivalent theory context operation.declaration.result
      (operation.merge (operation.merge first second) third)
      (operation.merge first (operation.merge second third)) := by
  exact .algebra ⟨.associative operation.declared operation.associative,
    operation.merge_sorted (operation.merge_sorted firstSorted secondSorted) thirdSorted,
    operation.merge_sorted firstSorted (operation.merge_sorted secondSorted thirdSorted)⟩

theorem comm (operation : ACUOperation theory context) {first second : Term}
    (firstSorted : HasSort theory.signature context first operation.declaration.result)
    (secondSorted : HasSort theory.signature context second operation.declaration.result) :
    Equivalent theory context operation.declaration.result
      (operation.merge first second) (operation.merge second first) :=
  .algebra ⟨.commutative operation.declared operation.commutative,
    operation.merge_sorted firstSorted secondSorted, operation.merge_sorted secondSorted firstSorted⟩

theorem left_unit (operation : ACUOperation theory context) {term : Term}
    (sorted : HasSort theory.signature context term operation.declaration.result) :
    Equivalent theory context operation.declaration.result (operation.merge operation.unit term) term :=
  .algebra ⟨.leftUnit operation.declared operation.identity,
    operation.merge_sorted operation.unit_sorted sorted, sorted⟩

theorem right_unit (operation : ACUOperation theory context) {term : Term}
    (sorted : HasSort theory.signature context term operation.declaration.result) :
    Equivalent theory context operation.declaration.result (operation.merge term operation.unit) term :=
  .algebra ⟨.rightUnit operation.declared operation.identity,
    operation.merge_sorted sorted operation.unit_sorted, sorted⟩

theorem merge_left (operation : ACUOperation theory context) {first second right : Term}
    (same : Equivalent theory context operation.declaration.result first second)
    (rightSorted : HasSort theory.signature context right operation.declaration.result) :
    Equivalent theory context operation.declaration.result
      (operation.merge first right) (operation.merge second right) := by
  let frame : ArgumentContext theory.signature context operation.declaration.result operation.declaration.result := {
    declaration := operation.declaration
    declared := operation.declared
    beforeSorts := []
    afterSorts := [operation.declaration.result]
    before := []
    after := [right]
    argumentSorts := operation.arguments
    resultSort := rfl
    beforeTyped := .nil
    afterTyped := .cons rightSorted .nil }
  exact Equivalent.argument frame same

theorem merge_right (operation : ACUOperation theory context) {left first second : Term}
    (leftSorted : HasSort theory.signature context left operation.declaration.result)
    (same : Equivalent theory context operation.declaration.result first second) :
    Equivalent theory context operation.declaration.result
      (operation.merge left first) (operation.merge left second) := by
  let frame : ArgumentContext theory.signature context operation.declaration.result operation.declaration.result := {
    declaration := operation.declaration
    declared := operation.declared
    beforeSorts := [operation.declaration.result]
    afterSorts := []
    before := [left]
    after := []
    argumentSorts := operation.arguments
    resultSort := rfl
    beforeTyped := .cons leftSorted .nil
    afterTyped := .nil }
  exact Equivalent.argument frame same

theorem fold_append (operation : ACUOperation theory context) (left right : List Term)
    (leftSorted : operation.Sorted left) (rightSorted : operation.Sorted right) :
    Equivalent theory context operation.declaration.result
      (operation.fold (left ++ right)) (operation.merge (operation.fold left) (operation.fold right)) := by
  induction left with
  | nil => exact .symm (operation.left_unit (operation.fold_sorted right rightSorted))
  | cons first rest ih =>
      have firstSorted := leftSorted first (by simp)
      have restSorted : operation.Sorted rest := fun term member => leftSorted term (by simp [member])
      exact .trans (operation.merge_right firstSorted (ih restSorted))
        (.symm (operation.assoc firstSorted (operation.fold_sorted rest restSorted)
          (operation.fold_sorted right rightSorted)))

theorem fold_perm (operation : ACUOperation theory context) {left right : List Term}
    (permutation : left.Perm right) (sorted : operation.Sorted left) :
    Equivalent theory context operation.declaration.result (operation.fold left) (operation.fold right) := by
  induction permutation with
  | nil => exact .refl operation.unit_sorted
  | cons first permutation ih =>
      exact operation.merge_right (sorted first (by simp))
        (ih (fun term member => sorted term (by simp [member])))
  | swap first second rest =>
      have firstSorted := sorted first (by simp)
      have secondSorted := sorted second (by simp)
      have restSorted : operation.Sorted rest := fun term member => sorted term (by simp [member])
      have tailSorted := operation.fold_sorted rest restSorted
      exact .trans (.symm (operation.assoc secondSorted firstSorted tailSorted))
        (.trans (operation.merge_left (operation.comm secondSorted firstSorted) tailSorted)
          (operation.assoc firstSorted secondSorted tailSorted))
  | trans first second firstIH secondIH =>
      exact .trans (firstIH sorted) (secondIH (fun term member => sorted term (first.mem_iff.mpr member)))

theorem operator_unique (operation : ACUOperation theory context)
    (checked : theory.signature.check = true) {other : Operator}
    (member : other ∈ theory.signature.operators) (same : other.id = operation.declaration.id) :
    other = operation.declaration := by
  have unique : (theory.signature.operators.map Operator.id).Nodup := by
    simp only [Signature.check, Bool.and_eq_true, decide_eq_true_eq] at checked
    exact checked.1.2
  exact List.inj_on_of_nodup_map unique member operation.declared same

theorem merge_arguments_sorted (operation : ACUOperation theory context)
    (checked : theory.signature.check = true) {left right : Term}
    (typed : HasSort theory.signature context (operation.merge left right) operation.declaration.result) :
    HasSort theory.signature context left operation.declaration.result ∧
      HasSort theory.signature context right operation.declaration.result := by
  obtain ⟨other, member, same, _, arguments⟩ := HasSort.operator_arguments typed rfl
  have equality := operation.operator_unique checked member same
  subst other
  rw [operation.arguments] at arguments
  cases arguments with
  | cons first rest =>
      cases rest with
      | cons second _ => exact ⟨first, second⟩

/-- Only the chosen operator and its exact declared identity are flattened.
Other constructors remain atoms, even when they have their own algebra laws. -/
def flatten (operation : ACUOperation theory context) (term : Term) : List Term :=
  if term = operation.unit then [] else
    match term with
    | .app id [left, right] =>
        if id = operation.declaration.id then operation.flatten left ++ operation.flatten right else [term]
    | _ => [term]
termination_by sizeOf term

theorem flatten_sound (operation : ACUOperation theory context)
    (checked : theory.signature.check = true) (term : Term)
    (typed : HasSort theory.signature context term operation.declaration.result) :
    operation.Sorted (operation.flatten term) ∧
      Equivalent theory context operation.declaration.result term (operation.fold (operation.flatten term)) := by
  have singleton (value : Term)
      (valueSorted : HasSort theory.signature context value operation.declaration.result) :
      operation.Sorted [value] ∧
        Equivalent theory context operation.declaration.result value (operation.fold [value]) := by
    exact ⟨fun item member => by simpa only [List.mem_singleton.mp member] using valueSorted,
      .symm (operation.right_unit valueSorted)⟩
  by_cases unit : term = operation.unit
  · have empty : operation.flatten term = [] := by rw [flatten.eq_def, if_pos unit]
    rw [empty, unit]
    refine ⟨?_, .refl operation.unit_sorted⟩
    intro value member
    cases member
  · cases term with
    | var name => simpa only [flatten, if_neg unit] using singleton (.var name) typed
    | app id arguments =>
        cases arguments with
        | nil => simpa only [flatten, if_neg unit] using singleton (.app id []) typed
        | cons left rest =>
          cases rest with
          | nil => simpa only [flatten, if_neg unit] using singleton (.app id [left]) typed
          | cons right tail =>
            cases tail with
            | cons third rest =>
                simpa only [flatten, if_neg unit] using singleton (.app id (left :: right :: third :: rest)) typed
            | nil =>
                by_cases selected : id = operation.declaration.id
                · subst id
                  obtain ⟨leftTyped, rightTyped⟩ := operation.merge_arguments_sorted checked typed
                  obtain ⟨leftSorted, leftSound⟩ := operation.flatten_sound checked left leftTyped
                  obtain ⟨rightSorted, rightSound⟩ := operation.flatten_sound checked right rightTyped
                  simp only [flatten, if_neg unit]
                  refine ⟨?_, .trans (operation.merge_left leftSound rightTyped)
                    (.trans (operation.merge_right (operation.fold_sorted _ leftSorted) rightSound)
                      (.symm (operation.fold_append _ _ leftSorted rightSorted)))⟩
                  intro value member
                  rcases List.mem_append.mp member with first | second
                  · exact leftSorted value first
                  · exact rightSorted value second
                · simpa only [flatten, if_neg unit, if_neg selected] using singleton (.app id [left, right]) typed
termination_by sizeOf term

theorem flatten_sorted (operation : ACUOperation theory context)
    (checked : theory.signature.check = true) {term : Term}
    (typed : HasSort theory.signature context term operation.declaration.result) :
    operation.Sorted (operation.flatten term) := (operation.flatten_sound checked term typed).1

theorem equivalent_fold_flatten (operation : ACUOperation theory context)
    (checked : theory.signature.check = true) {term : Term}
    (typed : HasSort theory.signature context term operation.declaration.result) :
    Equivalent theory context operation.declaration.result term (operation.fold (operation.flatten term)) :=
  (operation.flatten_sound checked term typed).2

theorem equivalent_of_flatten_perm (operation : ACUOperation theory context)
    (checked : theory.signature.check = true) {source target : Term}
    (sourceTyped : HasSort theory.signature context source operation.declaration.result)
    (targetTyped : HasSort theory.signature context target operation.declaration.result)
    (permutation : (operation.flatten source).Perm (operation.flatten target)) :
    Equivalent theory context operation.declaration.result source target :=
  .trans (operation.equivalent_fold_flatten checked sourceTyped)
    (.trans (operation.fold_perm permutation (operation.flatten_sorted checked sourceTyped))
      (.symm (operation.equivalent_fold_flatten checked targetTyped)))

theorem rawStep_with_residual (operation : ACUOperation theory context)
    {source target : Term} (step : RawStep theory context operation.declaration.result source target)
    (residual : List Term) (sorted : operation.Sorted residual) :
    RawStep theory context operation.declaration.result
      (operation.merge source (operation.fold residual))
      (operation.merge target (operation.fold residual)) := by
  let frame : ArgumentContext theory.signature context operation.declaration.result operation.declaration.result := {
    declaration := operation.declaration
    declared := operation.declared
    beforeSorts := []
    afterSorts := [operation.declaration.result]
    before := []
    after := [operation.fold residual]
    argumentSorts := operation.arguments
    resultSort := rfl
    beforeTyped := .nil
    afterTyped := .cons (operation.fold_sorted residual sorted) .nil }
  exact RawStep.argument frame step

/-- A selected multiset redex rewrites beside its unchanged residual.
This is a source step modulo A/E, not a new evaluator or admission rule. -/
theorem step_of_subbag (operation : ACUOperation theory context)
    (checked : theory.signature.check = true) {source left right : Term}
    (typed : HasSort theory.signature context source operation.declaration.result)
    (selected residual : List Term)
    (partition : (operation.flatten source).Perm (selected ++ residual))
    (redex : Equivalent theory context operation.declaration.result (operation.fold selected) left)
    (firing : RawStep theory context operation.declaration.result left right) :
    Step theory context operation.declaration.result source
      (operation.fold (operation.flatten right ++ residual)) := by
  have sourceSorted := operation.flatten_sorted checked typed
  have selectedSorted : operation.Sorted selected := fun term member =>
    sourceSorted term (partition.mem_iff.mpr (List.mem_append_left residual member))
  have residualSorted : operation.Sorted residual := fun term member =>
    sourceSorted term (partition.mem_iff.mpr (List.mem_append_right selected member))
  have rightSorted := firing.sorted.2
  have rightFlattened := operation.flatten_sound checked right rightSorted
  refine ⟨operation.merge left (operation.fold residual), operation.merge right (operation.fold residual),
    ?_, operation.rawStep_with_residual firing residual residualSorted, ?_⟩
  · exact .trans (operation.equivalent_fold_flatten checked typed)
      (.trans (operation.fold_perm partition sourceSorted)
        (.trans (operation.fold_append selected residual selectedSorted residualSorted)
          (operation.merge_left redex (operation.fold_sorted residual residualSorted))))
  · exact .trans (operation.merge_left rightFlattened.2 (operation.fold_sorted residual residualSorted))
      (.symm (operation.fold_append _ residual rightFlattened.1 residualSorted))

#print axioms fold_append
#print axioms fold_perm
#print axioms flatten_sound
#print axioms equivalent_of_flatten_perm
#print axioms step_of_subbag

end ACUOperation
end Mettapedia.Languages.Maude
