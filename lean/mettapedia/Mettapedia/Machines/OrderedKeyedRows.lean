import Mettapedia.Machines.KeyedImprovement

/-!
# Occurrence-exact functional rows and keyed improvement

A key fibre is an ordered list, not a set. Representation requires exactly
zero or one occurrence at each key, so equal duplicate rows are excluded.
The row worker keeps untouched rows in order and appends a new or improved
row. Its projection agrees with keyed improvement, including the changed
flag. The projection alone cannot recover enumeration order.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.KeyedImprovement.OrderedRows

variable {Key Value : Type} [DecidableEq Key] [LinearOrder Value]

def fibre (rows : List (Key × Value)) (key : Key) : List Value :=
  rows.filterMap (fun entry => if entry.1 = key then some entry.2 else none)

def Represents (rows : List (Key × Value)) (store : Store Key Value) : Prop :=
  ∀ key, fibre rows key = (store key).toList

def lookup (rows : List (Key × Value)) (key : Key) : Option Value := (fibre rows key).head?

omit [LinearOrder Value] in
theorem fibre_cons (entry : Key × Value) (rows : List (Key × Value)) (key : Key) :
    fibre (entry :: rows) key = if entry.1 = key then entry.2 :: fibre rows key else fibre rows key := by
  by_cases same : entry.1 = key <;> simp [fibre, same]

omit [LinearOrder Value] in
theorem mem_fibre (rows : List (Key × Value)) (key : Key) (value : Value) :
    value ∈ fibre rows key ↔ (key, value) ∈ rows := by
  induction rows with
  | nil => simp [fibre]
  | cons entry rows ih =>
      rcases entry with ⟨other, held⟩
      by_cases same : other = key <;> simp_all [fibre_cons, Prod.mk.injEq, eq_comm]

omit [LinearOrder Value] in
theorem Represents.lookup_eq {rows : List (Key × Value)} {store : Store Key Value}
    (represented : Represents rows store) : lookup rows = store := by
  funext key
  simp only [lookup, represented key]
  cases store key <;> rfl

omit [LinearOrder Value] in
theorem Represents.member {rows : List (Key × Value)} {store : Store Key Value}
    (represented : Represents rows store) (key : Key) (value : Value) :
    (key, value) ∈ rows ↔ store key = some value := by
  rw [← mem_fibre, represented key]
  cases store key <;> simp [eq_comm]

omit [LinearOrder Value] in
theorem Represents.at_most_one {rows : List (Key × Value)} {store : Store Key Value}
    (represented : Represents rows store) (key : Key) : (fibre rows key).length ≤ 1 := by
  rw [represented key]
  cases store key <;> simp

def replace (rows : List (Key × Value)) (key : Key) (candidate : Value) : List (Key × Value) :=
  rows.filter (fun entry => entry.1 != key) ++ [(key, candidate)]

omit [LinearOrder Value] in
theorem fibre_filtered (rows : List (Key × Value)) (key other : Key) :
    fibre (rows.filter (fun entry => entry.1 != key)) other = if other = key then [] else fibre rows other := by
  induction rows with
  | nil => simp [fibre]
  | cons entry rows ih =>
      by_cases removed : entry.1 = key
      · by_cases same : other = key <;> simp_all [fibre_cons]
        exact Ne.symm same
      · by_cases same : other = key
        · subst other; simp [removed, fibre_cons, ih]
        · by_cases selected : entry.1 = other <;> simp [removed, same, selected, fibre_cons, ih]

omit [LinearOrder Value] in
theorem fibre_replace (rows : List (Key × Value)) (key other : Key) (candidate : Value) :
    fibre (replace rows key candidate) other = if other = key then [candidate] else fibre rows other := by
  have append (first second : List (Key × Value)) : fibre (first ++ second) other = fibre first other ++ fibre second other := by
    simp [fibre]
  rw [replace, append, fibre_filtered]
  by_cases same : other = key <;> simp [same, Ne.symm, fibre]

omit [LinearOrder Value] in
theorem Represents.replace {rows : List (Key × Value)} {store : Store Key Value}
    (represented : Represents rows store) (key : Key) (candidate : Value) :
    Represents (replace rows key candidate) (Function.update store key (some candidate)) := by
  intro other
  rw [fibre_replace]
  by_cases same : other = key <;> simp [same, represented other]

omit [LinearOrder Value] in
theorem Represents.absent_filter {rows : List (Key × Value)} {store : Store Key Value}
    (represented : Represents rows store) (key : Key) (missing : store key = none) :
    rows.filter (fun entry => entry.1 != key) = rows := by
  apply List.filter_eq_self.mpr
  intro entry member
  have absent : entry.1 ≠ key := by
    intro same
    have found := (represented.member entry.1 entry.2).mp (by simpa using member)
    simp [same, missing] at found
  simpa using absent

theorem Represents.exact_removal {rows : List (Key × Value)} {store : Store Key Value}
    (represented : Represents rows store) (key : Key) (previous : Value) (held : store key = some previous) :
    rows.filter (· != (key, previous)) = rows.filter (fun entry => entry.1 != key) := by
  apply List.filter_congr
  intro entry member
  by_cases same : entry.1 = key
  · have found := (represented.member entry.1 entry.2).mp (by simpa using member)
    rw [same, held] at found
    have value := Option.some.inj found
    have pair : entry = (key, previous) := Prod.ext same value.symm
    subst entry
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne, ne_eq]
  · have pair : entry ≠ (key, previous) := fun equal => same (congrArg Prod.fst equal)
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne]
    simp [same, pair]

def publish (rows : List (Key × Value)) (key : Key) (candidate : Value)
    (observed : Option Value) : List (Key × Value) × Bool :=
  match observed with
  | none => (rows ++ [(key, candidate)], true)
  | some previous => if candidate < previous then
      (rows.filter (· != (key, previous)) ++ [(key, candidate)], true)
    else (rows, false)

theorem publish_refines {rows : List (Key × Value)} {store : Store Key Value}
    (represented : Represents rows store) (key : Key) (candidate : Value) :
    Represents (publish rows key candidate (store key)).1 (improve store key candidate).1 ∧
      (publish rows key candidate (store key)).2 = (improve store key candidate).2 := by
  cases held : store key with
  | none =>
      constructor
      · simpa only [publish, improve, held, replace, represented.absent_filter key held] using represented.replace key candidate
      · simp [publish, improve, held]
  | some previous =>
      by_cases better : candidate < previous
      · constructor
        · simpa only [publish, improve, held, if_pos better, represented.exact_removal key previous held, replace]
            using represented.replace key candidate
        · simp [publish, improve, held, better]
      · constructor
        · simpa only [publish, improve, held, if_neg better] using represented
        · simp [publish, improve, held, better]

namespace Controls

theorem duplicate_equal_rows_are_not_functional (store : Store Nat Nat) :
    ¬ Represents [(0, 10), (0, 10)] store := by
  intro represented
  have bound := represented.at_most_one 0
  change 2 ≤ 1 at bound
  omega

theorem empty_represents_absence : Represents ([] : List (Nat × Nat)) (fun _ => none) := by
  intro key; rfl

theorem replacement_keeps_other_order :
    publish [(0, 10), (2, 8), (1, 5)] 0 7 (some 10) = ([(2, 8), (1, 5), (0, 7)], true) := by decide

theorem order_is_not_recovered_from_lookup :
    lookup [(0, 10), (1, 5)] = lookup [(1, 5), (0, 10)] ∧
      ([(0, 10), (1, 5)] : List (Nat × Nat)) ≠ [(1, 5), (0, 10)] := by
  constructor
  · funext key
    by_cases zero : key = 0 <;> by_cases one : key = 1 <;>
      simp_all [lookup, fibre, eq_comm]
  · decide

end Controls
end Mettapedia.Machines.KeyedImprovement.OrderedRows
