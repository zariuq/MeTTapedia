import Mathlib.Logic.Function.Basic
import Mathlib.Data.Multiset.Bind

/-!
# Ordered semijoin reduction for paths

A backward pass retains a row exactly when its destination can complete
the suffix. Its buckets retain stored occurrences in order. The forward
pass then visits only prefixes of actual answers. Pricing table calls
separately gives a linear bound in the input and the delivered answer
spines, even when the unpruned intermediate product would be large.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Specialization.PathJoin

variable {Key Row : Type}

/-- A representation of ordered buckets with constant-size operations at
the table interface. Each theorem prices calls to the interface. -/
structure Tables (Key Row : Type) where
  State : Type
  empty : State
  read : State → Key → List Row
  prepend : State → Key → Row → State
  empty_exact : ∀ key, read empty key = []
  read_same : ∀ table key row, read (prepend table key row) key = row :: read table key
  read_other : ∀ table key other row, other ≠ key → read (prepend table key row) other = read table other

structure EdgeKeys (Key Row : Type) where
  source : Row → Key
  target : Row → Key

def functional [DecidableEq Key] : Tables Key Row where
  State := Key → List Row
  empty := fun _ => []
  read := fun table key => table key
  prepend := fun table key row => Function.update table key (row :: table key)
  empty_exact := by intro; rfl
  read_same := by intros; simp
  read_other := by intros; apply Function.update_of_ne; assumption

variable (keys : EdgeKeys Key Row) (tables : Tables Key Row)

def select [DecidableEq Key] (keep : Key → Bool) (key : Key) (row : Row) : Bool :=
  decide (keys.source row = key) && keep (keys.target row)

/-- One tested row and at most one bucket insertion per input occurrence.
The right fold retains the input order without reversing the observer. -/
def buildWhere (keyOf : Row → Key) (keep : Row → Bool) : List Row → tables.State × Nat
  | [] => (tables.empty, 1)
  | row :: rest =>
    let later := buildWhere keyOf keep rest
    if keep row then
      (tables.prepend later.1 (keyOf row) row, later.2 + 2)
    else (later.1, later.2 + 1)

theorem buildWhere_exact [DecidableEq Key] (keyOf : Row → Key) (keep : Row → Bool)
    (rows : List Row) (key : Key) :
    tables.read (buildWhere tables keyOf keep rows).1 key =
      rows.filter (fun row => decide (keyOf row = key) && keep row) := by
  induction rows with
  | nil => exact tables.empty_exact key
  | cons row rest ih =>
    by_cases retained : keep row = true
    · by_cases same : keyOf row = key
      · simp [buildWhere, retained, same, tables.read_same, ih]
      · have other : key ≠ keyOf row := Ne.symm same
        simp [buildWhere, retained, same, tables.read_other _ _ _ _ other, ih]
    · have discarded : keep row = false := Bool.eq_false_iff.mpr retained
      simp [buildWhere, discarded, ih]

theorem buildWhere_work (keyOf : Row → Key) (keep : Row → Bool) (rows : List Row) :
    (buildWhere tables keyOf keep rows).2 ≤ 2 * rows.length + 1 := by
  induction rows with
  | nil => exact Nat.le_refl _
  | cons row rest ih =>
    simp only [buildWhere, List.length_cons]
    split <;> omega

def build (keep : Key → Bool) (rows : List Row) : tables.State × Nat :=
  buildWhere tables keys.source (fun row => keep (keys.target row)) rows

theorem build_exact [DecidableEq Key] (keep : Key → Bool) (rows : List Row) (key : Key) :
    tables.read (build keys tables keep rows).1 key = rows.filter (select keys keep key) :=
  buildWhere_exact tables keys.source (fun row => keep (keys.target row)) rows key

theorem build_work (keep : Key → Bool) (rows : List Row) :
    (build keys tables keep rows).2 ≤ 2 * rows.length + 1 :=
  buildWhere_work tables keys.source (fun row => keep (keys.target row)) rows

def viable (finish : Key → Bool) : List tables.State → Key → Bool
  | [], key => finish key
  | first :: _, key => !(tables.read first key).isEmpty

def addLayer (finish : Key → Bool) (rows : List Row) (later : List tables.State × Nat) :
    List tables.State × Nat :=
  let first := build keys tables (viable tables finish later.1) rows
  (first.1 :: later.1, first.2 + later.2 + 1)

def prepareFrom (finish : Key → Bool) (later : List tables.State × Nat) (layers : List (List Row)) :
    List tables.State × Nat :=
  layers.foldr (addLayer keys tables finish) later

def prepare (finish : Key → Bool) (layers : List (List Row)) : List tables.State × Nat :=
  prepareFrom keys tables finish ([], 1) layers

theorem prepareFrom_bound (finish : Key → Bool) (later : List tables.State × Nat)
    (layers : List (List Row)) :
    (prepareFrom keys tables finish later layers).2 ≤
      2 * ((layers.map List.length).sum + layers.length) + later.2 := by
  induction layers with
  | nil => simp [prepareFrom]
  | cons rows rest ih =>
    have localWork := build_work keys tables
      (viable tables finish (prepareFrom keys tables finish later rest).1) rows
    change (addLayer keys tables finish rows (prepareFrom keys tables finish later rest)).2 ≤ _
    simp only [addLayer, List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem prepare_bound (finish : Key → Bool) (layers : List (List Row)) :
    (prepare keys tables finish layers).2 ≤ 2 * ((layers.map List.length).sum + layers.length) + 1 :=
  prepareFrom_bound keys tables finish ([], 1) layers

theorem prepare_depth (finish : Key → Bool) (layers : List (List Row)) :
    (prepare keys tables finish layers).1.length = layers.length := by
  induction layers with
  | nil => rfl
  | cons rows rest ih =>
    change Nat.succ (prepare keys tables finish rest).1.length = Nat.succ rest.length
    rw [ih]

/-- Ordered reference traversal, parametrized by the buckets for each
layer. A row occurrence is prepended to each suffix answer it enables. -/
def paths (finish : Key → Bool) : List (Key → List Row) → Key → List (List Row)
  | [], key => if finish key then [[]] else []
  | first :: rest, key =>
    (first key).flatMap fun row => (paths finish rest (keys.target row)).map (List.cons row)

def reference [DecidableEq Key] (finish : Key → Bool) (layers : List (List Row)) (start : Key) :
    List (List Row) :=
  paths keys finish (layers.map fun rows key => rows.filter (fun row => decide (keys.source row = key))) start

def execute (finish : Key → Bool) (indexes : List tables.State) (start : Key) : List (List Row) :=
  paths keys finish (indexes.map tables.read) start

inductive Trimmed (finish : Key → Bool) : List tables.State → Prop
  | empty : Trimmed finish []
  | cons {first : tables.State} {rest : List tables.State} (suffix : Trimmed finish rest)
      (continues : ∀ key row, row ∈ tables.read first key →
        (execute keys tables finish rest (keys.target row)).isEmpty = false) :
      Trimmed finish (first :: rest)

theorem viable_exact (finish : Key → Bool) {indexes : List tables.State}
    (trimmed : Trimmed keys tables finish indexes) (start : Key) :
    viable tables finish indexes start = !(execute keys tables finish indexes start).isEmpty := by
  cases trimmed with
  | empty => cases done : finish start <;> simp [viable, execute, paths, done]
  | @cons first rest trimmed productive =>
    cases seen : tables.read first start with
    | nil => simp [viable, execute, paths, seen]
    | cons row pending =>
      have output := productive start row (by simp [seen])
      change (paths keys finish (rest.map tables.read) (keys.target row)).isEmpty = false at output
      have nonempty : paths keys finish (rest.map tables.read) (keys.target row) ≠ [] := by
        intro empty
        rw [empty] at output
        cases output
      simp [viable, execute, paths, seen, nonempty]

theorem filter_omits_empty {A B : Type} (test : A → Bool) (emit : A → List B)
    (complete : ∀ row, test row = false → emit row = []) (rows : List A) :
    (rows.filter test).flatMap emit = rows.flatMap emit := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    cases checks : test row
    · simp [checks, complete row checks, ih]
    · simp [checks, ih]

theorem prepare_correct [DecidableEq Key] (finish : Key → Bool) (layers : List (List Row)) :
    let indexes := (prepare keys tables finish layers).1
    Trimmed keys tables finish indexes ∧
      ∀ start, execute keys tables finish indexes start = reference keys finish layers start := by
  induction layers with
  | nil => exact ⟨.empty, fun _ => rfl⟩
  | cons rows rest ih =>
    let suffix := (prepare keys tables finish rest).1
    let keep := viable tables finish suffix
    let first := (build keys tables keep rows).1
    have viableSuffix : Trimmed keys tables finish suffix := ih.1
    have viableRead (key : Key) : keep key = !(execute keys tables finish suffix key).isEmpty :=
      viable_exact keys tables finish viableSuffix key
    have exactSuffix (key : Key) : execute keys tables finish suffix key = reference keys finish rest key := ih.2 key
    have grouped (key : Key) :
        tables.read first key = (rows.filter (fun row => decide (keys.source row = key))).filter
          (fun row => keep (keys.target row)) := by
      rw [build_exact, List.filter_filter]
      apply congrArg (fun test => rows.filter test)
      funext row
      exact Bool.and_comm _ _
    refine ⟨.cons viableSuffix ?_, ?_⟩
    · intro key row member
      have kept := (List.mem_filter.mp (grouped key ▸ member)).2
      rw [viableRead] at kept
      change (execute keys tables finish suffix (keys.target row)).isEmpty = false
      simpa using kept
    · intro start
      change (tables.read first start).flatMap (fun row =>
        (execute keys tables finish suffix (keys.target row)).map (List.cons row)) = _
      rw [grouped, filter_omits_empty]
      · simp only [exactSuffix, reference, List.map_cons, paths]
      · intro row unavailable
        rw [viableRead] at unavailable
        have empty : (execute keys tables finish suffix (keys.target row)).isEmpty = true := by
          simpa using unavailable
        simp only [List.isEmpty_iff.mp empty, List.map_nil]

/-- Unit list costs include visiting a row and grafting its emitted
spines. One table read per visited prefix selects the next bucket. -/
def delivery (finish : Key → Bool) : List tables.State → Key → Nat
  | [], _ => 1
  | first :: rest, key =>
    1 + ((tables.read first key).map fun row =>
      let next := keys.target row
      1 + delivery finish rest next + 2 * (execute keys tables finish rest next).length).sum

theorem sum_bounded (rows : List Row) (cost size : Row → Nat) (rate : Nat)
    (bound : ∀ row ∈ rows, cost row ≤ rate * size row) :
    (rows.map cost).sum ≤ rate * (rows.map size).sum := by
  induction rows with
  | nil => simp
  | cons row rest ih =>
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    exact Nat.add_le_add (bound row List.mem_cons_self)
      (ih (fun other member => bound other (List.mem_cons_of_mem _ member)))

theorem delivery_bound (finish : Key → Bool) {indexes : List tables.State}
    (trimmed : Trimmed keys tables finish indexes) (start : Key) :
    delivery keys tables finish indexes start ≤
      1 + 4 * indexes.length * (execute keys tables finish indexes start).length := by
  induction trimmed generalizing start with
  | empty => simp [delivery]
  | @cons first rest trimmed productive ih =>
    have payOne : ∀ row ∈ tables.read first start,
        1 + delivery keys tables finish rest (keys.target row) +
            2 * (execute keys tables finish rest (keys.target row)).length ≤
          4 * (rest.length + 1) * (execute keys tables finish rest (keys.target row)).length := by
      intro row visible
      have grows := ih (keys.target row)
      have hasReply : 1 ≤ (execute keys tables finish rest (keys.target row)).length := by
        cases seen : execute keys tables finish rest (keys.target row) with
        | nil => simpa [seen] using productive start row visible
        | cons => simp
      rw [Nat.mul_add, Nat.mul_one, Nat.add_mul]
      omega
    have visits := sum_bounded _ _ _ _ payOne
    simp only [delivery, execute, List.map_cons, paths, List.length_cons, List.length_flatMap,
      List.length_map]
    simp only [execute] at visits
    exact Nat.add_le_add_left visits _

theorem path_input_and_output_bound [DecidableEq Key] (finish : Key → Bool)
    (layers : List (List Row)) (start : Key) :
    let built := prepare keys tables finish layers
    built.2 + delivery keys tables finish built.1 start ≤
      2 * ((layers.map List.length).sum + layers.length) + 2 +
        4 * layers.length * (reference keys finish layers start).length := by
  have pre := prepare_bound keys tables finish layers
  obtain ⟨good, exactAnswers⟩ := prepare_correct keys tables finish layers
  have out := delivery_bound keys tables finish good start
  rw [prepare_depth keys tables finish, exactAnswers] at out
  omega

theorem reference_cons [DecidableEq Key] (finish : Key → Bool) (rows : List Row)
    (layers : List (List Row)) (start : Key) :
    reference keys finish (rows :: layers) start =
      (rows.filter (fun row => decide (keys.source row = start))).flatMap fun row =>
        (reference keys finish layers (keys.target row)).map (List.cons row) := rfl

/-- Replacing one layer by the inserted occurrences computes its exact
bag delta. All unaffected layers may be used with their current contents.
Repeated values are still new occurrences and contribute separately. -/
theorem append_delta [DecidableEq Key] (finish : Key → Bool) (leading suffix : List (List Row))
    (old added : List Row) (start : Key) :
    (reference keys finish (leading ++ (old ++ added) :: suffix) start : Multiset (List Row)) =
      (reference keys finish (leading ++ old :: suffix) start : Multiset (List Row)) +
      (reference keys finish (leading ++ added :: suffix) start : Multiset (List Row)) := by
  induction leading generalizing start with
  | nil =>
    simp only [List.nil_append, reference_cons, List.filter_append, List.flatMap_append, Multiset.coe_add]
  | cons rows leading ih =>
    simp only [List.cons_append, reference_cons, ← Multiset.coe_bind]
    rw [← Multiset.bind_add]
    apply Multiset.bind_congr
    intro row _
    simp only [← Multiset.map_coe, ih, Multiset.map_add]

theorem prepareFrom_same_tables (finish : Key → Bool) (layers : List (List Row))
    (later : List tables.State) (first second : Nat) :
    (prepareFrom keys tables finish (later, first) layers).1 =
      (prepareFrom keys tables finish (later, second) layers).1 := by
  induction layers with
  | nil => rfl
  | cons rows rest ih =>
    change (addLayer keys tables finish rows (prepareFrom keys tables finish (later, first) rest)).1 =
      (addLayer keys tables finish rows (prepareFrom keys tables finish (later, second) rest)).1
    simp only [addLayer, ih]

theorem prepare_reuse_suffix (finish : Key → Bool) (leading suffix : List (List Row)) :
    (prepareFrom keys tables finish ((prepare keys tables finish suffix).1, 0) leading).1 =
      (prepare keys tables finish (leading ++ suffix)).1 := by
  have reuse := prepareFrom_same_tables keys tables finish leading
    (prepare keys tables finish suffix).1 0 (prepare keys tables finish suffix).2
  rw [reuse]
  simp only [prepare, prepareFrom, List.foldr_append]

/-- Compute a one-layer insertion delta using the retained suffix. The
cost involves scans only of the inserted rows and earlier layers. The
remaining work follows paths contributing to this delta. -/
theorem append_delta_reusing_suffix [DecidableEq Key] (finish : Key → Bool)
    (leading suffix : List (List Row)) (old added : List Row) (start : Key) :
    let affected := leading ++ [added]
    let built := prepareFrom keys tables finish ((prepare keys tables finish suffix).1, 0) affected
    let delta := execute keys tables finish built.1 start
    (reference keys finish (leading ++ (old ++ added) :: suffix) start : Multiset (List Row)) =
        (reference keys finish (leading ++ old :: suffix) start : Multiset (List Row)) + delta ∧
      built.2 + delivery keys tables finish built.1 start ≤
        2 * ((affected.map List.length).sum + affected.length) + 1 +
          4 * (leading.length + 1 + suffix.length) * delta.length := by
  let affected := leading ++ [added]
  let built := prepareFrom keys tables finish ((prepare keys tables finish suffix).1, 0) affected
  have same : built.1 = (prepare keys tables finish (leading ++ added :: suffix)).1 := by
    simpa only [affected, List.append_assoc, List.singleton_append] using
      prepare_reuse_suffix keys tables finish affected suffix
  have correct := prepare_correct keys tables finish (leading ++ added :: suffix)
  have result : execute keys tables finish built.1 start =
      reference keys finish (leading ++ added :: suffix) start := by rw [same, correct.2]
  have current : Trimmed keys tables finish built.1 := by rw [same]; exact correct.1
  have bound := prepareFrom_bound keys tables finish ((prepare keys tables finish suffix).1, 0) affected
  have out := delivery_bound keys tables finish current start
  have depth : built.1.length = leading.length + 1 + suffix.length := by
    rw [same, prepare_depth, List.length_append, List.length_cons]
    omega
  rw [depth] at out
  constructor
  · rw [result]
    exact append_delta keys finish leading suffix old added start
  · change built.2 + delivery keys tables finish built.1 start ≤
      2 * ((affected.map List.length).sum + affected.length) + 1 +
        4 * (leading.length + 1 + suffix.length) * (execute keys tables finish built.1 start).length
    change built.2 ≤ 2 * ((affected.map List.length).sum + affected.length) + 0 at bound
    omega

namespace Controls

private def edges : EdgeKeys Nat (Nat × Nat) := ⟨Prod.fst, Prod.snd⟩

private def layers : List (List (Nat × Nat)) :=
  [[(0, 1), (0, 2), (0, 1)], [(1, 3), (1, 4), (2, 5)], [(4, 7), (5, 9), (6, 7)]]

private def finish (key : Nat) : Bool := key == 7

theorem ordered_semijoin_preserves_both_occurrences :
    execute edges functional finish (prepare edges functional finish layers).1 0 =
      [[(0, 1), (1, 4), (4, 7)], [(0, 1), (1, 4), (4, 7)]] := by decide +kernel

theorem a_prefix_without_an_accepted_suffix_is_removed :
    viable functional finish (prepare edges functional finish [[(0, 2)], [(2, 5)], [(5, 9)]]).1 0 = false :=
  by decide +kernel

theorem a_middle_layer_insert_keeps_duplicate_witnesses :
    let delta := reference edges finish [[(0, 1), (0, 1)], [(1, 4)], [(4, 7)]] 0
    delta.length = 2 ∧ delta.head? = delta.getLast? := by decide +kernel

end Controls

end Mettapedia.Machines.Specialization.PathJoin
