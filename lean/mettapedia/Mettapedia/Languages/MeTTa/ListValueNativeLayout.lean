import Mettapedia.Logic.Unification.ListSpliceTerms

/-!
# Sealed list tags and public sequence views

CeTTa stores expressions, lists and open list patterns in expression storage.
A list has one extra physical field, its sealed list tag. An open pattern has
the rest tag, a nonempty prefix and a final tail field. The public sequence
view skips the proper-list tag and refuses open patterns.

This adapter models the root layout only: payload terms stand for already
decoded child atoms. It proves the boundary needed by sequence primitives;
it does not model arena ownership, pointer layout, garbage collection or an
evaluation machine. The negative raw-field example captures why an ordinary
expression prepend is not a list-aware `cons-atom` implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ListValueNativeLayout

open Mettapedia.Logic.Unification.ListSplice

variable {Leaf Var : Type}

/-- These are private native tags, not source symbols such as `List`. -/
inductive Tag where
  | list
  | rest
  deriving DecidableEq, Repr

/-- One root storage field. A public payload cannot be an internal tag. -/
inductive Field (Leaf Var : Type) where
  | tag : Tag → Field Leaf Var
  | payload : Term Leaf Var → Field Leaf Var
  deriving Repr

inductive Root (Leaf Var : Type) where
  | atom : Leaf → Root Leaf Var
  | var : Var → Root Leaf Var
  | expression : List (Field Leaf Var) → Root Leaf Var
  deriving Repr

/-- Physical root fields, before requiring the open-spine invariant. -/
def rawLayout : Term Leaf Var → Root Leaf Var
  | .atom a => .atom a
  | .var v => .var v
  | .expr xs => .expression (xs.map .payload)
  | .list xs => .expression (.tag .list :: xs.map .payload)
  | .rest xs tail => .expression (.tag .rest :: (xs.map .payload ++ [.payload tail]))

/-- Every public builder first establishes the splice normal form. -/
def layout (term : Term Leaf Var) : Root Leaf Var := rawLayout (normalize term)

def fields : Root Leaf Var → Option (List (Field Leaf Var))
  | .expression xs => some xs
  | _ => none

def readFields : List (Field Leaf Var) → Option (List (Term Leaf Var))
  | [] => some []
  | .tag _ :: _ => none
  | .payload x :: xs => (readFields xs).map (x :: ·)

@[simp] theorem readFields_map (xs : List (Term Leaf Var)) :
    readFields (xs.map .payload) = some xs := by
  induction xs <;> simp [readFields, *]

def splitLast {α : Type} : List α → Option (List α × α)
  | [] => none
  | [x] => some ([], x)
  | x :: y :: ys => (splitLast (y :: ys)).map fun p => (x :: p.1, p.2)

@[simp] theorem splitLast_append_singleton {α : Type} (xs : List α) (x : α) :
    splitLast (xs ++ [x]) = some (xs, x) := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      cases ys with
      | nil => rfl
      | cons z zs =>
          simpa only [List.cons_append, splitLast, Option.map_some] using
            congrArg (Option.map (fun p : List α × α => (y :: p.1, p.2))) ih

/-- Decode the recognized native roots. Rest layouts without a prefix are
rejected: the actual rest tag requires at least a head and a tail field. -/
def readRoot : Root Leaf Var → Option (Term Leaf Var)
  | .atom a => some (.atom a)
  | .var v => some (.var v)
  | .expression (.tag .list :: xs) => (readFields xs).map .list
  | .expression (.tag .rest :: xs) => do
      let values ← readFields xs
      let (front, tail) ← splitLast values
      if front.isEmpty then none else some (.rest front tail)
  | .expression xs => (readFields xs).map .expr

/-- The native rest discriminator assumes a nonempty prefix. Other public
root forms need no such guard. -/
def ValidRoot : Term Leaf Var → Prop
  | .rest xs _ => xs ≠ []
  | _ => True

theorem validRoot_splice (xs : List (Term Leaf Var)) (tail : Term Leaf Var)
    (valid : ValidRoot tail) : ValidRoot (splice xs tail) := by
  cases xs with
  | nil => exact valid
  | cons x xs => cases tail <;> simp [splice, ValidRoot]

theorem validRoot_normalize (term : Term Leaf Var) : ValidRoot (normalize term) := by
  match term with
  | .atom _ => simp [normalize, ValidRoot]
  | .var _ => simp [normalize, ValidRoot]
  | .expr _ => simp [normalize, ValidRoot]
  | .list _ => simp [normalize, ValidRoot]
  | .rest xs tail =>
      rw [normalize]
      exact validRoot_splice (xs.map normalize) (normalize tail)
        (validRoot_normalize tail)
termination_by sizeOf term

theorem readRoot_rawLayout (term : Term Leaf Var) (valid : ValidRoot term) :
    readRoot (rawLayout term) = some term := by
  cases term with
  | atom a => rfl
  | var v => rfl
  | expr xs => cases xs <;> simp [readRoot, rawLayout, readFields]
  | list xs => simp [readRoot, rawLayout]
  | rest xs tail =>
      cases xs with
      | nil => exact False.elim (valid rfl)
      | cons x xs =>
          have readAppend : readFields ((x :: xs).map .payload ++ [.payload tail]) =
              some ((x :: xs) ++ [tail]) := by
            simpa only [List.map_append, List.map_cons, List.map_nil] using
              readFields_map ((x :: xs) ++ [tail])
          simp only [rawLayout, readRoot]
          rw [readAppend]
          have last : splitLast (x :: (xs ++ [tail])) = some (x :: xs, tail) :=
            splitLast_append_singleton (x :: xs) tail
          simp [last]

/-- The root representation recovers the semantic normal form; empty rest
prefixes disappear rather than becoming a malformed tagged expression. -/
theorem readRoot_layout (term : Term Leaf Var) :
    readRoot (layout term) = some (normalize term) :=
  readRoot_rawLayout (normalize term) (validRoot_normalize term)

theorem rawLayout_injective {left right : Term Leaf Var}
    (validLeft : ValidRoot left) (validRight : ValidRoot right)
    (equal : rawLayout left = rawLayout right) : left = right := by
  have decoded := congrArg readRoot equal
  rw [readRoot_rawLayout left validLeft, readRoot_rawLayout right validRight] at decoded
  exact Option.some.inj decoded

theorem layout_eq_iff (left right : Term Leaf Var) :
    layout left = layout right ↔ normalize left = normalize right := by
  constructor
  · intro same
    exact rawLayout_injective (validRoot_normalize left) (validRoot_normalize right) same
  · intro same
    exact congrArg rawLayout same

/-- This is a genuine constructor boundary, not reservation of a source word. -/
theorem tag_ne_payload (tag : Tag) (value : Term Leaf Var) :
    (Field.tag tag : Field Leaf Var) ≠ .payload value := by
  intro equal
  cases equal

theorem list_layout_ne_expr (xs ys : List (Term Leaf Var)) :
    rawLayout (.list xs) ≠ rawLayout (.expr ys) := by
  intro same
  have impossible := rawLayout_injective (by trivial) (by trivial) same
  cases impossible

inductive SequenceKind where
  | expression
  | list
  deriving DecidableEq, Repr

def sequenceView : Term Leaf Var → Option (SequenceKind × List (Term Leaf Var))
  | .expr xs => some (.expression, xs)
  | .list xs => some (.list, xs)
  | _ => none

/-- The native root-field algorithm: skip a proper-list tag, reject a
recognized rest pattern, and otherwise expose expression fields. Malformed
tagged roots are intentionally not silently repaired by this view. -/
def physicalSequenceView : Root Leaf Var →
    Option (SequenceKind × List (Field Leaf Var))
  | .expression (.tag .list :: xs) => some (.list, xs)
  | .expression (.tag .rest :: _ :: _ :: _) => none
  | .expression xs => some (.expression, xs)
  | _ => none

/-- The physical and public sequence views agree for builder-admitted roots.
This is the precise obligation behind using the shared native sequence view
instead of unconditionally exposing `expr.elems`. -/
theorem physicalSequenceView_rawLayout (term : Term Leaf Var) (valid : ValidRoot term) :
    physicalSequenceView (rawLayout term) =
      (sequenceView term).map (fun p => (p.1, p.2.map Field.payload)) := by
  cases term with
  | atom a => rfl
  | var v => rfl
  | expr xs => cases xs <;> rfl
  | list xs => rfl
  | rest xs tail =>
      cases xs with
      | nil => exact False.elim (valid rfl)
      | cons x xs => cases xs <;> rfl

theorem physicalSequenceView_layout (term : Term Leaf Var) :
    physicalSequenceView (layout term) =
      (sequenceView (normalize term)).map (fun p => (p.1, p.2.map Field.payload)) :=
  physicalSequenceView_rawLayout (normalize term) (validRoot_normalize term)

def rebuild (kind : SequenceKind) (xs : List (Term Leaf Var)) : Term Leaf Var :=
  match kind with
  | .expression => .expr xs
  | .list => .list xs

@[simp] theorem sequenceView_rebuild (kind : SequenceKind) (xs : List (Term Leaf Var)) :
    sequenceView (rebuild kind xs) = some (kind, xs) := by cases kind <;> rfl

def publicCons (head tail : Term Leaf Var) : Option (Term Leaf Var) := do
  let (kind, xs) ← sequenceView tail
  return rebuild kind (head :: xs)

def publicDecons (value : Term Leaf Var) : Option (Term Leaf Var × Term Leaf Var) := do
  let (kind, xs) ← sequenceView value
  match xs with
  | [] => none
  | x :: tail => return (x, rebuild kind tail)

@[simp] theorem publicCons_rebuild (head : Term Leaf Var) (kind : SequenceKind)
    (xs : List (Term Leaf Var)) :
    publicCons head (rebuild kind xs) = some (rebuild kind (head :: xs)) := by
  simp [publicCons]

@[simp] theorem publicDecons_rebuild_cons (kind : SequenceKind) (head : Term Leaf Var)
    (xs : List (Term Leaf Var)) :
    publicDecons (rebuild kind (head :: xs)) = some (head, rebuild kind xs) := by
  simp [publicDecons]

theorem decons_cons (head tail : Term Leaf Var) (result : Term Leaf Var)
    (built : publicCons head tail = some result) :
    publicDecons result = some (head, tail) := by
  cases tail <;> simp [publicCons, sequenceView, rebuild] at built
  all_goals subst result; rfl

theorem cons_decons (value head tail : Term Leaf Var)
    (split : publicDecons value = some (head, tail)) : publicCons head tail = some value := by
  cases value <;> simp [publicDecons, sequenceView] at split
  all_goals
    split at split
    · cases split
    · simp only [Option.some.injEq, Prod.mk.injEq] at split
      rcases split with ⟨rfl, rfl⟩
      rfl

theorem sequenceView_open (xs : List (Term Leaf Var)) (tail : Term Leaf Var) :
    sequenceView (.rest xs tail) = none := rfl

/-- Empty lists have one physical tag field but no public element. -/
theorem empty_list_fields_not_elements :
    fields (rawLayout (.list [] : Term Leaf Var)) = some [.tag .list] ∧
      publicDecons (.list [] : Term Leaf Var) = none := by
  exact ⟨rfl, rfl⟩

theorem physical_list_length (xs : List (Term Leaf Var)) :
    (.tag .list :: xs.map Field.payload : List (Field Leaf Var)).length - 1 =
      xs.length := by simp

/-- A public list view returns payload fields only, never the sealed tag. -/
theorem public_fields_have_no_tag (xs : List (Term Leaf Var)) (tag : Tag) :
    (Field.tag tag : Field Leaf Var) ∉ xs.map .payload := by
  simp

/-- An unsafe expression prepend works directly on physical fields. It is
included only as a counterexample to using `expr.elems` as public list data. -/
def rawFieldCons (head : Term Leaf Var) (root : Root Leaf Var) : Option (Root Leaf Var) :=
  (fields root).map fun xs => .expression (.payload head :: xs)

theorem rawFieldCons_list (head : Term Leaf Var) (xs : List (Term Leaf Var)) :
    rawFieldCons head (rawLayout (.list xs)) =
      some (.expression (.payload head :: .tag .list :: xs.map .payload)) := rfl

/-- The exposed tag is in a payload position, so this layout has no public
term decoding. This is the shape of the equation-body tag-leak regression. -/
theorem rawFieldCons_list_rejected (head : Term Leaf Var) (xs : List (Term Leaf Var)) :
    (rawFieldCons head (rawLayout (.list xs))).bind readRoot = none := by
  simp [rawFieldCons, fields, rawLayout, readRoot, readFields]

theorem rawFieldCons_ne_publicCons (head : Term Leaf Var) (xs : List (Term Leaf Var)) :
    rawFieldCons head (rawLayout (.list xs)) ≠
      (publicCons head (.list xs)).map rawLayout := by
  simp [rawFieldCons, fields, rawLayout, publicCons, sequenceView, rebuild]

end Mettapedia.Languages.MeTTa.ListValueNativeLayout
