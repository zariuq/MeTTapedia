import Mathlib.Data.List.Pairwise
import Mathlib.Order.Defs.LinearOrder
import Lean.Elab.Tactic.Omega

/-!
# First-binding two/three-tree index for declaration names

This auxiliary name map keeps payloads independent of grammar syntax and of any
source-certificate representation. Equal keys retain the existing payload.
Insertion propagates a child split upward, preserving in-order bindings.
The source's structured-text comparison must separately be related to the
lawful key order used here; no source or native correspondence is assumed.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfNameIndex

universe uK uV

inductive Tree (Key : Type uK) (Value : Type uV) where
  | empty
  | two (left : Tree Key Value) (key : Key) (value : Value) (right : Tree Key Value)
  | three (left : Tree Key Value) (first : Key) (firstValue : Value)
      (middle : Tree Key Value) (second : Key) (secondValue : Value) (right : Tree Key Value)
  deriving Repr

inductive InsertResult (Key : Type uK) (Value : Type uV) where
  | done (tree : Tree Key Value)
  | split (left : Tree Key Value) (key : Key) (value : Value) (right : Tree Key Value)
  deriving Repr

variable {Key : Type uK} {Value : Type uV}

def bindings : Tree Key Value → List (Key × Value)
  | .empty => []
  | .two left key value right => bindings left ++ (key, value) :: bindings right
  | .three left first firstValue middle second secondValue right =>
      bindings left ++ (first, firstValue) ::
        (bindings middle ++ (second, secondValue) :: bindings right)

def resultBindings : InsertResult Key Value → List (Key × Value)
  | .done tree => bindings tree
  | .split left key value right => bindings left ++ (key, value) :: bindings right

def finish : InsertResult Key Value → Tree Key Value
  | .done tree => tree
  | .split left key value right => .two left key value right

def twoLeft (child : InsertResult Key Value) (key : Key) (value : Value)
    (right : Tree Key Value) : InsertResult Key Value :=
  match child with
  | .done left => .done (.two left key value right)
  | .split left first firstValue middle =>
      .done (.three left first firstValue middle key value right)

def twoRight (left : Tree Key Value) (key : Key) (value : Value)
    (child : InsertResult Key Value) : InsertResult Key Value :=
  match child with
  | .done right => .done (.two left key value right)
  | .split middle second secondValue right =>
      .done (.three left key value middle second secondValue right)

def threeLeft (child : InsertResult Key Value) (first : Key) (firstValue : Value)
    (middle : Tree Key Value) (second : Key) (secondValue : Value)
    (right : Tree Key Value) : InsertResult Key Value :=
  match child with
  | .done left => .done (.three left first firstValue middle second secondValue right)
  | .split a key value b =>
      .split (.two a key value b) first firstValue (.two middle second secondValue right)

def threeMiddle (left : Tree Key Value) (first : Key) (firstValue : Value)
    (child : InsertResult Key Value) (second : Key) (secondValue : Value)
    (right : Tree Key Value) : InsertResult Key Value :=
  match child with
  | .done middle => .done (.three left first firstValue middle second secondValue right)
  | .split a key value b =>
      .split (.two left first firstValue a) key value (.two b second secondValue right)

def threeRight (left : Tree Key Value) (first : Key) (firstValue : Value)
    (middle : Tree Key Value) (second : Key) (secondValue : Value)
    (child : InsertResult Key Value) : InsertResult Key Value :=
  match child with
  | .done right => .done (.three left first firstValue middle second secondValue right)
  | .split a key value b =>
      .split (.two left first firstValue middle) second secondValue (.two a key value b)

variable [LinearOrder Key]

def lookup (key : Key) : Tree Key Value → Option Value
  | .empty => none
  | .two left stored value right =>
      if key = stored then some value
      else if key < stored then lookup key left else lookup key right
  | .three left first firstValue middle second secondValue right =>
      if key = first then some firstValue
      else if key < first then lookup key left
      else if key = second then some secondValue
      else if key < second then lookup key middle else lookup key right

def insertWalk (key : Key) (value : Value) : Tree Key Value → InsertResult Key Value
  | .empty => .split .empty key value .empty
  | .two left stored oldValue right =>
      if key = stored then .done (.two left stored oldValue right)
      else if key < stored then twoLeft (insertWalk key value left) stored oldValue right
      else twoRight left stored oldValue (insertWalk key value right)
  | .three left first firstValue middle second secondValue right =>
      if key = first then .done (.three left first firstValue middle second secondValue right)
      else if key < first then
        threeLeft (insertWalk key value left) first firstValue middle second secondValue right
      else if key = second then .done (.three left first firstValue middle second secondValue right)
      else if key < second then
        threeMiddle left first firstValue (insertWalk key value middle) second secondValue right
      else threeRight left first firstValue middle second secondValue (insertWalk key value right)

def insertFirst (key : Key) (value : Value) (tree : Tree Key Value) : Tree Key Value :=
  finish (insertWalk key value tree)

omit [LinearOrder Key] in
@[simp] theorem bindings_finish (result : InsertResult Key Value) :
    bindings (finish result) = resultBindings result := by cases result <;> rfl

omit [LinearOrder Key] in
@[simp] theorem bindings_twoLeft (child : InsertResult Key Value) (key : Key) (value : Value)
    (right : Tree Key Value) :
    resultBindings (twoLeft child key value right) =
      resultBindings child ++ (key, value) :: bindings right := by
  cases child <;> simp [twoLeft, resultBindings, bindings, List.append_assoc]

omit [LinearOrder Key] in
@[simp] theorem bindings_twoRight (left : Tree Key Value) (key : Key) (value : Value)
    (child : InsertResult Key Value) :
    resultBindings (twoRight left key value child) =
      bindings left ++ (key, value) :: resultBindings child := by
  cases child <;> simp [twoRight, resultBindings, bindings]

omit [LinearOrder Key] in
@[simp] theorem bindings_threeLeft (child : InsertResult Key Value) (first : Key) (firstValue : Value)
    (middle : Tree Key Value) (second : Key) (secondValue : Value) (right : Tree Key Value) :
    resultBindings (threeLeft child first firstValue middle second secondValue right) =
      resultBindings child ++ (first, firstValue) ::
        (bindings middle ++ (second, secondValue) :: bindings right) := by
  cases child <;> simp [threeLeft, resultBindings, bindings, List.append_assoc]

omit [LinearOrder Key] in
@[simp] theorem bindings_threeMiddle (left : Tree Key Value) (first : Key) (firstValue : Value)
    (child : InsertResult Key Value) (second : Key) (secondValue : Value) (right : Tree Key Value) :
    resultBindings (threeMiddle left first firstValue child second secondValue right) =
      bindings left ++ (first, firstValue) ::
        (resultBindings child ++ (second, secondValue) :: bindings right) := by
  cases child <;> simp [threeMiddle, resultBindings, bindings, List.append_assoc]

omit [LinearOrder Key] in
@[simp] theorem bindings_threeRight (left : Tree Key Value) (first : Key) (firstValue : Value)
    (middle : Tree Key Value) (second : Key) (secondValue : Value)
    (child : InsertResult Key Value) :
    resultBindings (threeRight left first firstValue middle second secondValue child) =
      bindings left ++ (first, firstValue) ::
        (bindings middle ++ (second, secondValue) :: resultBindings child) := by
  cases child <;> simp [threeRight, resultBindings, bindings, List.append_assoc]

/-- Every leaf is at the indexed depth; key ordering is a separate invariant. -/
inductive Balanced : Tree Key Value → Nat → Prop where
  | empty : Balanced .empty 0
  | two {left right : Tree Key Value} (key : Key) (value : Value) {height : Nat}
      (leftBalanced : Balanced left height) (rightBalanced : Balanced right height) :
      Balanced (.two left key value right) (height + 1)
  | three {left middle right : Tree Key Value}
      (first : Key) (firstValue : Value) (second : Key) (secondValue : Value) {height : Nat}
      (leftBalanced : Balanced left height) (middleBalanced : Balanced middle height)
      (rightBalanced : Balanced right height) :
      Balanced (.three left first firstValue middle second secondValue right) (height + 1)

def ResultBalanced (height : Nat) : InsertResult Key Value → Prop
  | .done tree => Balanced tree height
  | .split left _ _ right => Balanced left height ∧ Balanced right height

omit [LinearOrder Key] in
theorem twoLeft_balanced {child : InsertResult Key Value} {right : Tree Key Value}
    (key : Key) (value : Value) {height : Nat}
    (childBalanced : ResultBalanced height child) (rightBalanced : Balanced right height) :
    ResultBalanced (height + 1) (twoLeft child key value right) := by
  cases child with
  | done left => exact .two key value childBalanced rightBalanced
  | split left first firstValue middle =>
      exact .three first firstValue key value childBalanced.1 childBalanced.2 rightBalanced

omit [LinearOrder Key] in
theorem twoRight_balanced {left : Tree Key Value} {child : InsertResult Key Value}
    (key : Key) (value : Value) {height : Nat}
    (leftBalanced : Balanced left height) (childBalanced : ResultBalanced height child) :
    ResultBalanced (height + 1) (twoRight left key value child) := by
  cases child with
  | done right => exact .two key value leftBalanced childBalanced
  | split middle second secondValue right =>
      exact .three key value second secondValue leftBalanced childBalanced.1 childBalanced.2

omit [LinearOrder Key] in
theorem threeLeft_balanced {child : InsertResult Key Value} {middle right : Tree Key Value}
    (first : Key) (firstValue : Value) (second : Key) (secondValue : Value) {height : Nat}
    (childBalanced : ResultBalanced height child) (middleBalanced : Balanced middle height)
    (rightBalanced : Balanced right height) :
    ResultBalanced (height + 1) (threeLeft child first firstValue middle second secondValue right) := by
  cases child with
  | done left => exact .three first firstValue second secondValue childBalanced middleBalanced rightBalanced
  | split a key value b =>
      exact ⟨.two key value childBalanced.1 childBalanced.2,
        .two second secondValue middleBalanced rightBalanced⟩

omit [LinearOrder Key] in
theorem threeMiddle_balanced {left right : Tree Key Value} {child : InsertResult Key Value}
    (first : Key) (firstValue : Value) (second : Key) (secondValue : Value) {height : Nat}
    (leftBalanced : Balanced left height) (childBalanced : ResultBalanced height child)
    (rightBalanced : Balanced right height) :
    ResultBalanced (height + 1) (threeMiddle left first firstValue child second secondValue right) := by
  cases child with
  | done middle => exact .three first firstValue second secondValue leftBalanced childBalanced rightBalanced
  | split a key value b =>
      exact ⟨.two first firstValue leftBalanced childBalanced.1,
        .two second secondValue childBalanced.2 rightBalanced⟩

omit [LinearOrder Key] in
theorem threeRight_balanced {left middle : Tree Key Value} {child : InsertResult Key Value}
    (first : Key) (firstValue : Value) (second : Key) (secondValue : Value) {height : Nat}
    (leftBalanced : Balanced left height) (middleBalanced : Balanced middle height)
    (childBalanced : ResultBalanced height child) :
    ResultBalanced (height + 1) (threeRight left first firstValue middle second secondValue child) := by
  cases child with
  | done right => exact .three first firstValue second secondValue leftBalanced middleBalanced childBalanced
  | split a key value b =>
      exact ⟨.two first firstValue leftBalanced middleBalanced,
        .two key value childBalanced.1 childBalanced.2⟩

theorem insertWalk_balanced (key : Key) (value : Value) {tree : Tree Key Value} {height : Nat}
    (balanced : Balanced tree height) : ResultBalanced height (insertWalk key value tree) := by
  induction balanced with
  | empty => exact ⟨.empty, .empty⟩
  | two stored oldValue leftBalanced rightBalanced leftIH rightIH =>
      simp only [insertWalk]
      split_ifs with equal less
      · exact .two stored oldValue leftBalanced rightBalanced
      · exact twoLeft_balanced stored oldValue leftIH rightBalanced
      · exact twoRight_balanced stored oldValue leftBalanced rightIH
  | three first firstValue second secondValue leftBalanced middleBalanced rightBalanced leftIH middleIH rightIH =>
      simp only [insertWalk]
      split_ifs with firstEqual firstLess secondEqual secondLess
      · exact .three first firstValue second secondValue leftBalanced middleBalanced rightBalanced
      · exact threeLeft_balanced first firstValue second secondValue leftIH middleBalanced rightBalanced
      · exact .three first firstValue second secondValue leftBalanced middleBalanced rightBalanced
      · exact threeMiddle_balanced first firstValue second secondValue leftBalanced middleIH rightBalanced
      · exact threeRight_balanced first firstValue second secondValue leftBalanced middleBalanced rightIH

theorem insertFirst_balanced (key : Key) (value : Value) {tree : Tree Key Value} {height : Nat}
    (balanced : Balanced tree height) :
    Balanced (insertFirst key value tree) height ∨
      Balanced (insertFirst key value tree) (height + 1) := by
  have result := insertWalk_balanced key value balanced
  cases inserted : insertWalk key value tree with
  | done after => exact Or.inl (by simpa [insertFirst, inserted, finish, ResultBalanced] using result)
  | split left stored oldValue right =>
      rw [inserted] at result
      exact Or.inr (by
        simpa [insertFirst, inserted, finish] using Balanced.two stored oldValue result.1 result.2)

omit [LinearOrder Key] in
/-- Equal leaf depth gives the structural logarithmic-height bound. This does
not count the work of comparing variable-length name keys. -/
theorem balanced_min_bindings {tree : Tree Key Value} {height : Nat}
    (balanced : Balanced tree height) : 2 ^ height ≤ (bindings tree).length + 1 := by
  induction balanced with
  | empty => simp [bindings]
  | two key value left right leftIH rightIH =>
      simp only [bindings, List.length_append, List.length_cons, Nat.pow_succ]
      omega
  | three first firstValue second secondValue left middle right leftIH middleIH rightIH =>
      simp only [bindings, List.length_append, List.length_cons, Nat.pow_succ]
      omega

/-- A key already found by the search is never overwritten or rebalanced.
This operational first-binding property does not require a sortedness premise. -/
theorem insertWalk_preserves_found (key : Key) (newValue : Value) (tree : Tree Key Value)
    {oldValue : Value} (found : lookup key tree = some oldValue) :
    insertWalk key newValue tree = .done tree := by
  induction tree with
  | empty => simp [lookup] at found
  | two left stored value right leftIH rightIH =>
      by_cases equal : key = stored
      · simp [insertWalk, equal]
      · by_cases less : key < stored
        · have child : lookup key left = some oldValue := by simpa [lookup, equal, less] using found
          simp [insertWalk, equal, less, leftIH child, twoLeft]
        · have child : lookup key right = some oldValue := by simpa [lookup, equal, less] using found
          simp [insertWalk, equal, less, rightIH child, twoRight]
  | three left first firstValue middle second secondValue right leftIH middleIH rightIH =>
      by_cases firstEqual : key = first
      · simp [insertWalk, firstEqual]
      · by_cases firstLess : key < first
        · have child : lookup key left = some oldValue := by
            simpa [lookup, firstEqual, firstLess] using found
          simp [insertWalk, firstEqual, firstLess, leftIH child, threeLeft]
        · by_cases secondEqual : key = second
          · simp only [insertWalk, if_neg firstEqual, if_neg firstLess, if_pos secondEqual]
          · by_cases secondLess : key < second
            · have child : lookup key middle = some oldValue := by
                simpa [lookup, firstEqual, firstLess, secondEqual, secondLess] using found
              simp [insertWalk, firstEqual, firstLess, secondEqual, secondLess,
                middleIH child, threeMiddle]
            · have child : lookup key right = some oldValue := by
                simpa [lookup, firstEqual, firstLess, secondEqual, secondLess] using found
              simp [insertWalk, firstEqual, firstLess, secondEqual, secondLess,
                rightIH child, threeRight]

theorem duplicate_insertion_preserves_tree (key : Key) (newValue : Value) (tree : Tree Key Value)
    {oldValue : Value} (found : lookup key tree = some oldValue) :
    insertFirst key newValue tree = tree := by
  simp [insertFirst, insertWalk_preserves_found key newValue tree found, finish]

end Mettapedia.GSLT.Parsing.PlainBnfNameIndex
