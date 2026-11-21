import Mettapedia.Machines.Specialization.PathJoin

/-!
# Ordered semijoin reduction on a join tree

Each child is joined to its parent on a separator key. A backward pass
retains only rows whose child buckets are all nonempty. Forward enumeration
keeps the occurrence order of each bucket and uses the ordered product of
the child witnesses. Branches may have different separators and arbitrary
arity. The running-intersection law licenses interpreting these edge
constraints as all the equalities of a conjunctive query.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Specialization.OrderedJoinTree

open PathJoin (Tables)

variable {Key Row Label : Type}

mutual

inductive Tree (Key Row Label : Type) where
  | node (label : Label) (children : Forest Key Row Label)

inductive Forest (Key Row Label : Type) where
  | nil
  | cons (parentKey : Row → Key) (child : Tree Key Row Label) (later : Forest Key Row Label)

end

def Tree.label : Tree Key Row Label → Label
  | .node label _ => label

def Forest.arity : Forest Key Row Label → Nat
  | .nil => 0
  | .cons _ _ later => later.arity + 1

def present {A : Type} (items : List A) : Bool := !items.isEmpty

theorem present_iff {A : Type} (items : List A) : present items = true ↔ ∃ item, item ∈ items := by
  cases items with
  | nil => simp [present]
  | cons first rest => exact ⟨fun _ => ⟨first, List.mem_cons_self⟩, fun _ => rfl⟩

theorem absent_iff {A : Type} (items : List A) : present items = false ↔ items = [] := by
  cases items <;> simp [present]

def combine (left right : List (List Row)) : List (List Row) :=
  left.flatMap fun first => right.map (first ++ ·)

theorem present_combine (left right : List (List Row)) :
    present (combine left right) = (present left && present right) := by
  apply Bool.eq_iff_iff.mpr
  simp only [present_iff, Bool.and_eq_true, combine]
  constructor
  · rintro ⟨joined, member⟩
    obtain ⟨first, inLeft, found⟩ := List.mem_flatMap.mp member
    obtain ⟨last, inRight, _⟩ := List.mem_map.mp found
    exact ⟨⟨first, inLeft⟩, ⟨last, inRight⟩⟩
  · rintro ⟨⟨first, inLeft⟩, ⟨last, inRight⟩⟩
    exact ⟨first ++ last, List.mem_flatMap.mpr ⟨first, inLeft, List.mem_map.mpr ⟨last, inRight, rfl⟩⟩⟩

theorem combine_length (left right : List (List Row)) :
    (combine left right).length = left.length * right.length := by
  induction left with
  | nil => simp [combine]
  | cons first later ih =>
    simp only [combine, List.flatMap_cons, List.length_append, List.length_map, List.length_cons,
      Nat.add_mul, Nat.one_mul] at ih ⊢
    rw [ih, Nat.add_comm]

variable (read : Label → Key → List Row)

mutual

def enumerate : Tree Key Row Label → Key → List (List Row)
  | .node label children, key =>
    (read label key).flatMap fun row => (enumerateForest children row).map (row :: ·)

def enumerateForest : Forest Key Row Label → Row → List (List Row)
  | .nil, _ => [[]]
  | .cons key child later, selected =>
    combine (enumerate child (key selected)) (enumerateForest later selected)

end

def supports : Forest Key Row Label → Row → Bool
  | .nil, _ => true
  | .cons key child later, row => present (read child.label (key row)) && supports later row

mutual

def Trimmed : Tree Key Row Label → Prop
  | .node label children =>
    TrimmedForest children ∧ ∀ key row, row ∈ read label key → supports read children row = true

def TrimmedForest : Forest Key Row Label → Prop
  | .nil => ∀ row, supports read .nil row = true
  | .cons _ child later => Trimmed child ∧ TrimmedForest later

end

mutual

theorem enumerate_live : ∀ (tree : Tree Key Row Label), Trimmed read tree →
    ∀ key, present (enumerate read tree key) = present (read tree.label key)
  | .node label children, trimmed, key => by
    obtain ⟨descendants, ready⟩ := trimmed
    apply Bool.eq_iff_iff.mpr
    simp only [present_iff, enumerate, Tree.label]
    constructor
    · rintro ⟨answer, found⟩
      obtain ⟨row, selected, _⟩ := List.mem_flatMap.mp found
      exact ⟨row, selected⟩
    · rintro ⟨row, selected⟩
      have live := (enumerateForest_live children descendants row).trans (ready key row selected)
      obtain ⟨suffix, member⟩ := (present_iff _).mp live
      exact ⟨row :: suffix, List.mem_flatMap.mpr ⟨row, selected, List.mem_map.mpr ⟨suffix, member, rfl⟩⟩⟩

theorem enumerateForest_live : ∀ (forest : Forest Key Row Label), TrimmedForest read forest →
    ∀ row, present (enumerateForest read forest row) = supports read forest row
  | .nil, _, _ => rfl
  | .cons key child later, ⟨first, rest⟩, row => by
    simp only [enumerateForest, supports, present_combine, enumerate_live child first,
      enumerateForest_live later rest]

end

abbrev Relation (Key Row : Type) := (Row → Key) × List Row

def referenceBucket [DecidableEq Key] (label : Relation Key Row) (key : Key) : List Row :=
  label.2.filter fun row => decide (label.1 row = key)

variable (tables : Tables Key Row)

mutual

def prepare : Tree Key Row (Relation Key Row) → Tree Key Row tables.State × Nat
  | .node (keyOf, rows) children =>
    let ready := prepareForest children
    let kept := PathJoin.buildWhere tables keyOf (supports tables.read ready.1) rows
    (.node kept.1 ready.1, ready.2 + kept.2 + rows.length * children.arity)

def prepareForest : Forest Key Row (Relation Key Row) → Forest Key Row tables.State × Nat
  | .nil => (.nil, 0)
  | .cons key child later =>
    let prepared := prepare child
    let rest := prepareForest later
    (.cons key prepared.1 rest.1, prepared.2 + rest.2 + 1)

end

mutual

theorem prepare_exact [DecidableEq Key] : ∀ (tree : Tree Key Row (Relation Key Row)),
    Trimmed tables.read (prepare tables tree).1 ∧
      ∀ key, enumerate tables.read (prepare tables tree).1 key = enumerate referenceBucket tree key
  | .node (keyOf, rows) children => by
    obtain ⟨trimmed, exactChildren⟩ := prepareForest_exact children
    let prepared := (prepareForest tables children).1
    let keep := supports tables.read prepared
    let built := PathJoin.buildWhere tables keyOf keep rows
    change ∀ row, enumerateForest tables.read prepared row = enumerateForest referenceBucket children row
      at exactChildren
    have buckets (key : Key) : tables.read built.1 key = (referenceBucket (keyOf, rows) key).filter keep := by
      rw [PathJoin.buildWhere_exact]
      simp only [referenceBucket, List.filter_filter, Bool.and_comm]
    constructor
    · change TrimmedForest tables.read prepared ∧
        ∀ key row, row ∈ tables.read built.1 key → keep row = true
      refine ⟨trimmed, ?_⟩
      intro key row member
      rw [buckets] at member
      exact (List.mem_filter.mp member).2
    · intro key
      change (tables.read built.1 key).flatMap (fun row =>
        (enumerateForest tables.read prepared row).map (row :: ·)) = _
      rw [buckets, PathJoin.filter_omits_empty]
      · simp only [enumerate, exactChildren]
      · intro row dead
        have live := enumerateForest_live tables.read prepared trimmed row
        change present (enumerateForest tables.read prepared row) = keep row at live
        rw [dead] at live
        rw [(absent_iff _).mp live, List.map_nil]

theorem prepareForest_exact [DecidableEq Key] : ∀ (forest : Forest Key Row (Relation Key Row)),
    TrimmedForest tables.read (prepareForest tables forest).1 ∧
      ∀ row, enumerateForest tables.read (prepareForest tables forest).1 row =
        enumerateForest referenceBucket forest row
  | .nil => ⟨fun _ => rfl, fun _ => rfl⟩
  | .cons key child later => by
    obtain ⟨trimmed, answers⟩ := prepare_exact child
    obtain ⟨restTrimmed, restAnswers⟩ := prepareForest_exact later
    refine ⟨⟨trimmed, restTrimmed⟩, ?_⟩
    intro row
    change combine (enumerate tables.read (prepare tables child).1 (key row))
      (enumerateForest tables.read (prepareForest tables later).1 row) = _
    rw [answers, restAnswers]
    rfl

end

mutual

def inputAllowance : Tree Key Row (Relation Key Row) → Nat
  | .node (_, rows) children => inputForestAllowance children + (2 + children.arity) * rows.length + 1

def inputForestAllowance : Forest Key Row (Relation Key Row) → Nat
  | .nil => 0
  | .cons _ child later => inputAllowance child + inputForestAllowance later + 1

end

mutual

theorem prepare_work : ∀ tree : Tree Key Row (Relation Key Row),
    (prepare tables tree).2 ≤ inputAllowance tree
  | .node (keyOf, rows) children => by
    have childWork := prepareForest_work children
    have retained := PathJoin.buildWhere_work tables keyOf (supports tables.read (prepareForest tables children).1) rows
    simp only [prepare, inputAllowance, Nat.add_mul, Nat.mul_comm rows.length children.arity]
    omega

theorem prepareForest_work : ∀ forest : Forest Key Row (Relation Key Row),
    (prepareForest tables forest).2 ≤ inputForestAllowance forest
  | .nil => Nat.le_refl _
  | .cons key child later => by
    simp only [prepareForest, inputForestAllowance]
    exact Nat.add_le_add_right (Nat.add_le_add (prepare_work child) (prepareForest_work later)) _

end

end Mettapedia.Machines.Specialization.OrderedJoinTree
