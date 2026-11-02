import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Support-preserving tensor selection and finite decision trees

Cells are optional scalar payloads: absence is not numerical zero or a false
condition. Lists describe logical coordinate order after equal-shape admission.
The two traversal passes count and write only selected support. Their laws are
about these algorithms, not a verification of C storage, IEEE arithmetic or
the binary transport. Payloads are arbitrary; no arithmetic law is assumed.

The tree interpreter follows one decision path per coordinate. Compilation
instead constructs both child arrays and combines them with checked selection.
The correspondence applies to already admitted, fault-free payloads. Strict
fault combination below deliberately does not license lazy code elimination.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.TensorSelection

variable {α ε : Type*}

def selectCell : Option Bool → Option α → Option α → Option α
  | none, _, _ => none
  | some true, left, _ => left
  | some false, _, right => right

def selectCells : List (Option Bool) → List (Option α) → List (Option α) →
    Option (List (Option α))
  | [], [], [] => some []
  | condition :: conditions, left :: lefts, right :: rights =>
      (selectCells conditions lefts rights).map (selectCell condition left right :: ·)
  | _, _, _ => none

theorem selectCells_length (conditions : List (Option Bool))
    (lefts rights result : List (Option α)) (found : selectCells conditions lefts rights = some result) :
    result.length = conditions.length ∧ lefts.length = conditions.length ∧ rights.length = conditions.length := by
  induction conditions generalizing lefts rights result with
  | nil =>
      cases lefts <;> cases rights <;> simp_all [selectCells]
  | cons condition conditions ih =>
      cases lefts with
      | nil => simp [selectCells] at found
      | cons left lefts =>
          cases rights with
          | nil => simp [selectCells] at found
          | cons right rights =>
              cases tail : selectCells conditions lefts rights with
              | none => simp [selectCells, tail] at found
              | some values =>
                  simp [selectCells, tail] at found
                  subst result
                  simpa using ih lefts rights values tail

theorem mismatched_lengths_refused (conditions : List (Option Bool))
    (lefts rights : List (Option α))
    (mismatch : lefts.length ≠ conditions.length ∨ rights.length ≠ conditions.length) :
    selectCells conditions lefts rights = none := by
  cases found : selectCells conditions lefts rights with
  | none => rfl
  | some result =>
      obtain ⟨_, left, right⟩ := selectCells_length conditions lefts rights result found
      rcases mismatch with mismatch | mismatch
      · exact False.elim (mismatch left)
      · exact False.elim (mismatch right)

theorem selectCells_get (conditions : List (Option Bool)) (lefts rights result : List (Option α))
    (found : selectCells conditions lefts rights = some result) (position : Nat) :
    result[position]? = (conditions[position]?).bind (fun condition =>
      (lefts[position]?).bind (fun left =>
        (rights[position]?).map (fun right => selectCell condition left right))) := by
  induction conditions generalizing lefts rights result position with
  | nil =>
      cases lefts <;> cases rights <;> simp_all [selectCells]
  | cons condition conditions ih =>
      cases lefts with
      | nil => simp [selectCells] at found
      | cons left lefts =>
          cases rights with
          | nil => simp [selectCells] at found
          | cons right rights =>
              cases tail : selectCells conditions lefts rights with
              | none => simp [selectCells, tail] at found
              | some values =>
                  simp [selectCells, tail] at found
                  subst result
                  cases position with
                  | zero => simp
                  | succ position => simpa using ih lefts rights values tail position

theorem selectCells_ofFn (n : Nat) (condition : Fin n → Option Bool)
    (left right : Fin n → Option α) :
    selectCells (List.ofFn condition) (List.ofFn left) (List.ofFn right) =
      some (List.ofFn (fun index => selectCell (condition index) (left index) (right index))) := by
  induction n with
  | zero => simp [selectCells]
  | succ n ih => simp [List.ofFn_succ, selectCells, ih]

def packedSupport (start : Nat) : List (Option α) → List (Nat × α)
  | [] => []
  | none :: rest => packedSupport (start + 1) rest
  | some value :: rest => (start, value) :: packedSupport (start + 1) rest

def countSelected : List (Option Bool) → List (Option α) → List (Option α) → Option Nat
  | [], [], [] => some 0
  | condition :: conditions, left :: lefts, right :: rights =>
      (countSelected conditions lefts rights).map
        (fun later => if (selectCell condition left right).isSome then later + 1 else later)
  | _, _, _ => none

def writeSelected (start : Nat) : List (Option Bool) → List (Option α) →
    List (Option α) → Option (List (Nat × α))
  | [], [], [] => some []
  | condition :: conditions, left :: lefts, right :: rights =>
      match selectCell condition left right with
      | none => writeSelected (start + 1) conditions lefts rights
      | some value =>
          (writeSelected (start + 1) conditions lefts rights).map ((start, value) :: ·)
  | _, _, _ => none

theorem writeSelected_agrees (conditions : List (Option Bool)) (lefts rights : List (Option α))
    (start : Nat) : writeSelected start conditions lefts rights =
      (selectCells conditions lefts rights).map (packedSupport start) := by
  induction conditions generalizing lefts rights start with
  | nil => cases lefts <;> cases rights <;> rfl
  | cons condition conditions ih =>
      cases lefts with
      | nil => cases rights <;> rfl
      | cons left lefts =>
          cases rights with
          | nil => rfl
          | cons right rights =>
              simp only [writeSelected, selectCells, ih]
              cases selected : selectCell condition left right <;>
                cases tail : selectCells conditions lefts rights <;> simp [packedSupport]

theorem countSelected_agrees (conditions : List (Option Bool)) (lefts rights : List (Option α))
    (start : Nat) : countSelected conditions lefts rights =
      (writeSelected start conditions lefts rights).map List.length := by
  rw [writeSelected_agrees]
  induction conditions generalizing lefts rights start with
  | nil => cases lefts <;> cases rights <;> rfl
  | cons condition conditions ih =>
      cases lefts with
      | nil => cases rights <;> rfl
      | cons left lefts =>
          cases rights with
          | nil => rfl
          | cons right rights =>
              rw [countSelected, selectCells, ih lefts rights (start + 1)]
              cases selected : selectCell condition left right <;>
                cases tail : selectCells conditions lefts rights <;> simp [packedSupport]

theorem countSelected_exact_allocation (conditions : List (Option Bool)) (lefts rights : List (Option α))
    (start : Nat) (records : List (Nat × α)) (written : writeSelected start conditions lefts rights = some records) :
    countSelected conditions lefts rights = some records.length := by
  rw [countSelected_agrees conditions lefts rights start, written]
  rfl

theorem packedSupport_length_le (start : Nat) (values : List (Option α)) :
    (packedSupport start values).length ≤ values.length := by
  induction values generalizing start with
  | nil => simp [packedSupport]
  | cons value rest ih =>
      cases value <;> simp only [packedSupport, List.length_cons]
      · exact (ih (start + 1)).trans (Nat.le_succ _)
      · exact Nat.succ_le_succ (ih (start + 1))

theorem selected_storage_le_condition_coordinates (conditions : List (Option Bool))
    (lefts rights : List (Option α)) (start count : Nat) (counted : countSelected conditions lefts rights = some count) :
    count ≤ conditions.length := by
  rw [countSelected_agrees conditions lefts rights start, writeSelected_agrees] at counted
  cases found : selectCells conditions lefts rights with
  | none => simp [found] at counted
  | some result =>
      simp [found] at counted
      subst count
      rw [← (selectCells_length conditions lefts rights result found).1]
      exact packedSupport_length_le start result

inductive DecisionTree (n : Nat) (α : Type*)
  | leaf : (Fin n → Option α) → DecisionTree n α
  | branch : (Fin n → Option Bool) → DecisionTree n α → DecisionTree n α → DecisionTree n α

namespace DecisionTree

variable {n : Nat}

def evaluate : DecisionTree n α → Fin n → Option α
  | .leaf values, index => values index
  | .branch condition left right, index =>
      match condition index with
      | none => none
      | some true => evaluate left index
      | some false => evaluate right index

def compile : DecisionTree n α → Option (List (Option α))
  | .leaf values => some (List.ofFn values)
  | .branch condition left right => do
      let before ← compile left
      let after ← compile right
      selectCells (List.ofFn condition) before after

theorem compile_reconstructs (tree : DecisionTree n α) :
    compile tree = some (List.ofFn (evaluate tree)) := by
  induction tree with
  | leaf values => rfl
  | branch condition left right ihLeft ihRight =>
      simp only [compile, ihLeft, ihRight]
      change selectCells (List.ofFn condition) (List.ofFn (evaluate left)) (List.ofFn (evaluate right)) = _
      rw [selectCells_ofFn]
      have pointwise : (fun index => selectCell (condition index) (evaluate left index) (evaluate right index)) =
          evaluate (.branch condition left right) := by
        funext index
        cases observed : condition index with
        | none => simp [evaluate, selectCell, observed]
        | some flag => cases flag <;> simp [evaluate, selectCell, observed]
      rw [pointwise]

theorem compiled_length (tree : DecisionTree n α) (values : List (Option α))
    (found : compile tree = some values) : values.length = n := by
  rw [compile_reconstructs] at found
  cases found
  exact List.length_ofFn

theorem compiled_selected_storage (tree : DecisionTree n α) (start : Nat) :
    (compile tree).map (packedSupport start) = some (packedSupport start (List.ofFn (evaluate tree))) := by
  rw [compile_reconstructs]
  rfl

end DecisionTree

def selectStrict (condition : Except ε (Option Bool)) (left right : Except ε (Option α)) : Except ε (Option α) :=
  match condition, left, right with
  | .error error, _, _ => .error error
  | .ok _, .error error, _ => .error error
  | .ok _, .ok _, .error error => .error error
  | .ok flag, .ok before, .ok after => .ok (selectCell flag before after)

theorem unselected_fault_is_not_eliminated (error : ε) (value : α) :
    selectStrict (.ok (some true)) (.ok (some value)) (.error error) = .error error := rfl

theorem missing_condition_is_not_false (left right : α) :
    selectCell none (some left) (some right) = none := rfl

theorem missing_unselected_branch_does_not_erase (value : α) :
    selectCell (some true) (some value) none = some value := rfl

theorem selected_absence_does_not_fall_through (other : α) :
    selectCell (some true) none (some other) = none := rfl

end Mettapedia.Algorithms.Compression.TensorSelection
