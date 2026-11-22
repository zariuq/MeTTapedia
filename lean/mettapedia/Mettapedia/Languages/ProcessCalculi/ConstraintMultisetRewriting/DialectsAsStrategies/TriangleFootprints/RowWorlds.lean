import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep.FramedMachines
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PredicateQueryAdmission

/-!
# Worlds of rows: one occurrence per row, each move reading its region completely

`HEOnTheStep.FramedMachines` placed a framed machine's world on the step as one occurrence, so
every move that kept the world read all of it. Here the world is a list of **rows**, and each row
is its own occurrence, labelled with the row and its position (`rowEncode`). A move declares a
**footprint**: the region of rows it depends on (`Footprint`). It is placed on the step as one
firing (`RowStep`) that

* takes the control and the frames it pops, and makes the new control and the frames it pushes;
* **reads** the rows of its region, every one of them (`footRule`);
* makes the **complete observation** of its region (`observation`): the predicate query of
  `PredicateQueryAdmission` saying that the region holds exactly the occurrences it read. So the
  footprint of a complete query is the matched rows plus the absence of any other row there.

A move whose region is empty reads nothing, and its observation cannot be spoiled.

## Results

* `row_store_to_machine`: for a **world-local** machine (`WorldLocal`: a move depends on the world
  only through the rows of its region), every firing from a store representing a configuration is
  a step of the machine, and the result represents the target.
* `row_machine_to_store`: for a local, read-only machine, every step is one firing.
* `row_bisimulation`: representation is a strong bisimulation between the step under these rules
  and the machine. Every configuration is represented (`row_exists_represents`); the outcomes
  (answer bag and rows) agree (`row_outcomes_eq`), and so do the stuck configurations
  (`row_stuck_iff`).
* `row_reads_exact`: what a firing reads is exactly the rows of its region in the world, with their
  positions. The read word is the footprint, and the observation records that it is complete.
* `row_firing_region`: the region a firing reads is the footprint of a move from the store's own
  control, or the empty region of publication.

## Controls

* `Controls.peeker_missed`: a machine that looks at a row outside its declared footprint is not
  world-local, and from a store whose world lacks that row the step fires a move the machine cannot
  make. The bisimulation needs world-locality.
* `Controls.peeker_exact_local`, `Controls.peeker_reads_only_its_row`: declared with its true
  region (the rows `true`), the same machine is world-local, and its firing from the world
  `[false, true]` reads the row `(true, 1)` and not the row `(false, 0)`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

open MeTTaCalculus.OccurrenceCommits (Enabled fire labels labels_fire labels_mono regionOf
  mem_regionOf PredicateQuery)
open FragmentsOfTheStep.TransitionMaps
open HEOnTheStep

/-! ## Rows and regions -/

section Rows

variable {X : Type}

/-- The rows of a world inside a region, each with its position. -/
def regionRows (ρ : X → Bool) (rows : List X) : List (X × ℕ) :=
  rows.zipIdx.filter fun p => ρ p.1

theorem zipIdx_pairwise : ∀ (rows : List X) (k : ℕ),
    (rows.zipIdx k).Pairwise fun p q => p.2 < q.2
  | [], _ => List.Pairwise.nil
  | x :: rows, k => by
      rw [List.zipIdx_cons]
      refine List.Pairwise.cons (fun q member => ?_) (zipIdx_pairwise rows (k + 1))
      have := List.le_snd_of_mem_zipIdx member
      omega

theorem regionRows_pairwise (ρ : X → Bool) (rows : List X) :
    (regionRows ρ rows).Pairwise fun p q => p.2 < q.2 :=
  (zipIdx_pairwise rows 0).filter _

theorem nodup_of_sorted {L : List (X × ℕ)} (sorted : L.Pairwise fun p q => p.2 < q.2) :
    L.Nodup :=
  sorted.imp fun {_ _} lt same => by subst same; exact Nat.lt_irrefl _ lt

/-- The empty region holds no row. -/
theorem regionRows_none (rows : List X) : regionRows (fun _ => false) rows = [] := by
  simp [regionRows]

/-- The full region holds every row. -/
theorem regionRows_all (rows : List X) : regionRows (fun _ => true) rows = rows.zipIdx := by
  simp [regionRows]

/-- Two lists of rows with the same positioned rows are the same. -/
theorem eq_of_zipIdx_eq {rows rows' : List X} (same : rows.zipIdx = rows'.zipIdx) :
    rows = rows' := by
  have mapped := congrArg (List.map Prod.fst) same
  rwa [List.zipIdx_map_fst, List.zipIdx_map_fst] at mapped

variable {C F A : Type}

/-- The cells of the step for a world of rows: a row cell holds the row with its position. -/
abbrev RowCell (X C F A : Type) := Cell (X × ℕ) C F A

/-- One cell per row, labelled with the row and its position. -/
def rowCells (rows : List X) : List (RowCell X C F A) := rows.zipIdx.map Cell.world

/-- A region of rows as a region of cells: the control, frames and answers lie outside it. -/
def cellRegion (ρ : X → Bool) : RowCell X C F A → Bool
  | .world p => ρ p.1
  | .control _ _ => false
  | .frame _ _ => false
  | .answer _ => false

/-- The position a cell holds, when it is a row. -/
def cellIndex : RowCell X C F A → ℕ
  | .world p => p.2
  | .control _ _ => 0
  | .frame _ _ => 0
  | .answer _ => 0

theorem world_injective : Function.Injective (Cell.world : X × ℕ → RowCell X C F A) :=
  fun _ _ same => Cell.world.inj same

theorem rowCells_nodup (rows : List X) : (rowCells rows : List (RowCell X C F A)).Nodup :=
  List.Nodup.map world_injective (nodup_of_sorted (zipIdx_pairwise rows 0))

theorem filter_rowCells (ρ : X → Bool) (rows : List X) :
    (rowCells rows : List (RowCell X C F A)).filter (cellRegion ρ) =
      (regionRows ρ rows).map Cell.world := by
  unfold rowCells regionRows
  rw [List.filter_map]
  rfl

theorem filterMap_answer_world (l : List (X × ℕ)) :
    (l.map Cell.world : List (RowCell X C F A)).filterMap Cell.answer? = [] := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      simp only [List.map_cons, List.filterMap_cons, Cell.answer?]
      exact ih

theorem filterMap_world_world (l : List (X × ℕ)) :
    (l.map Cell.world : List (RowCell X C F A)).filterMap Cell.world? = l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      simp only [List.map_cons, List.filterMap_cons, Cell.world?]
      exact congrArg (p :: ·) ih

theorem filter_popCells (ρ : X → Bool) (s : List F) (b : ℕ) :
    (popCells s b : List (RowCell X C F A)).filter (cellRegion ρ) = [] := by
  induction s with
  | nil => rfl
  | cons f s ih =>
      simp only [popCells, List.filter_cons, cellRegion]
      exact ih

theorem filter_answers (ρ : X → Bool) (e : List A) :
    (e.map Cell.answer : List (RowCell X C F A)).filter (cellRegion ρ) = [] := by
  induction e with
  | nil => rfl
  | cons a e ih =>
      simp only [List.map_cons, List.filter_cons, cellRegion]
      exact ih

end Rows

/-! ## The encoding -/

section Encoding

variable {W X C F A : Type}

/-- **The store of a configuration**: one cell per row of its world, its control with the stack's
depth, one cell per frame, one per published answer. -/
def rowEncode (view : W → List X) (x : Config W C F A) : Multiset (RowCell X C F A) :=
  ((rowCells (view x.world) : List (RowCell X C F A)) : Multiset (RowCell X C F A)) +
    (Cell.control x.control x.stack.length ::ₘ
      (((popCells x.stack 0 : List (RowCell X C F A)) : Multiset (RowCell X C F A)) +
        ((x.emitted.map Cell.answer : List (RowCell X C F A)) : Multiset (RowCell X C F A))))

/-- The cells of a configuration, as a list. -/
def rowEncodeList (view : W → List X) (x : Config W C F A) : List (RowCell X C F A) :=
  rowCells (view x.world) ++
    (Cell.control x.control x.stack.length :: (popCells x.stack 0 ++ x.emitted.map Cell.answer))

theorem rowEncode_eq_coe (view : W → List X) (x : Config W C F A) :
    rowEncode view x = (rowEncodeList view x : Multiset (RowCell X C F A)) := by
  simp only [rowEncode, rowEncodeList, Multiset.coe_add, Multiset.cons_coe]

/-- The rows held by a bag of cells, with their positions. -/
def rowsOf (m : Multiset (RowCell X C F A)) : Multiset (X × ℕ) := m.filterMap Cell.world?

theorem answersOf_rowEncode (view : W → List X) (x : Config W C F A) :
    answersOf (rowEncode view x) = (x.emitted : Multiset A) := by
  rw [rowEncode_eq_coe]
  unfold answersOf
  rw [Multiset.filterMap_coe]
  congr 1
  simp only [rowEncodeList, rowCells, List.filterMap_append, List.filterMap_cons, Cell.answer?,
    filterMap_answer_world, answers_popCells, answers_map, List.nil_append]

theorem rowsOf_rowEncode (view : W → List X) (x : Config W C F A) :
    rowsOf (rowEncode view x) = ((view x.world).zipIdx : Multiset (X × ℕ)) := by
  rw [rowEncode_eq_coe]
  unfold rowsOf
  rw [Multiset.filterMap_coe]
  congr 1
  simp only [rowEncodeList, rowCells, List.filterMap_append, List.filterMap_cons, Cell.world?,
    filterMap_world_world, worlds_popCells, worlds_map, List.append_nil]

/-- **The split of a configuration's store** at a move: the control and the popped frames, and the
rest, which holds the rows, the base frames and the answers. -/
theorem rowEncode_split (view : W → List X) (w : W) (c : C) (pop base : List F) (e : List A) :
    rowEncode view (⟨w, c, pop ++ base, e⟩ : Config W C F A) =
      ((Cell.control c (pop.length + base.length) :: popCells pop base.length :
          List (RowCell X C F A)) : Multiset (RowCell X C F A)) +
        (((rowCells (view w) : List (RowCell X C F A)) : Multiset (RowCell X C F A)) +
          (((popCells base 0 : List (RowCell X C F A)) : Multiset (RowCell X C F A)) +
            ((e.map Cell.answer : List (RowCell X C F A)) : Multiset (RowCell X C F A)))) := by
  unfold rowEncode
  simp only [popCells_append, Nat.add_zero, List.length_append, ← Multiset.coe_add,
    ← Multiset.cons_coe, ← Multiset.singleton_add]
  abel

theorem rowEncode_publish (view : W → List X) (w : W) (c : C) (e : List A) :
    rowEncode view (⟨w, c, [], e⟩ : Config W C F A) =
      (([Cell.control c 0] : List (RowCell X C F A)) : Multiset (RowCell X C F A)) +
        (((rowCells (view w) : List (RowCell X C F A)) : Multiset (RowCell X C F A)) +
          ((e.map Cell.answer : List (RowCell X C F A)) : Multiset (RowCell X C F A))) := by
  unfold rowEncode
  simp only [popCells, List.length_nil, Multiset.coe_nil, zero_add, ← Multiset.cons_coe,
    ← Multiset.singleton_add]
  abel

theorem rowEncode_published (view : W → List X) (w : W) (c : C) (a : A) (e : List A) :
    rowEncode view (⟨w, c, [], e ++ [a]⟩ : Config W C F A) =
      (([Cell.control c 0, Cell.answer a] : List (RowCell X C F A)) : Multiset (RowCell X C F A)) +
        (((rowCells (view w) : List (RowCell X C F A)) : Multiset (RowCell X C F A)) +
          ((e.map Cell.answer : List (RowCell X C F A)) : Multiset (RowCell X C F A))) := by
  unfold rowEncode
  simp only [popCells, List.length_nil, Multiset.coe_nil, zero_add, List.map_append,
    List.map_cons, List.map_nil, ← Multiset.coe_add, ← Multiset.cons_coe,
    ← Multiset.singleton_add, add_zero]
  abel

theorem control_mem_rowEncode {view : W → List X} {x : Config W C F A} {c : C} {n : ℕ}
    (member : Cell.control c n ∈ rowEncode view x) : c = x.control ∧ n = x.stack.length := by
  unfold rowEncode rowCells at member
  simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_coe, List.mem_map] at member
  rcases member with ⟨p, _, same⟩ | same | inFrames | ⟨a, _, same⟩
  · cases same
  · injection same with c n
    exact ⟨c, n⟩
  · have := popCells_frames x.stack 0 _ inFrames
    simp [Cell.isFrame] at this
  · cases same

theorem frames_rowEncode (view : W → List X) (x : Config W C F A) :
    (rowEncode view x).filter (fun cell => cell.isFrame = true) =
      ((popCells x.stack 0 : List (RowCell X C F A)) : Multiset (RowCell X C F A)) := by
  rw [rowEncode_eq_coe, Multiset.filter_coe]
  congr 1
  have rows : ∀ l : List (X × ℕ),
      (l.map Cell.world : List (RowCell X C F A)).filter (fun cell => decide (cell.isFrame = true))
        = [] := by
    intro l
    induction l with
    | nil => rfl
    | cons p l ih =>
        simp only [List.map_cons, List.filter_cons, Cell.isFrame]
        exact ih
  have frames : (popCells x.stack 0 : List (RowCell X C F A)).filter
      (fun cell => decide (cell.isFrame = true)) = popCells x.stack 0 :=
    List.filter_eq_self.mpr fun cell member => by
      simp [popCells_frames x.stack 0 cell member]
  have answers : ∀ e : List A, (e.map Cell.answer : List (RowCell X C F A)).filter
      (fun cell => decide (cell.isFrame = true)) = [] := by
    intro e
    induction e with
    | nil => rfl
    | cons a e ih =>
        simp only [List.map_cons, List.filter_cons, Cell.isFrame]
        exact ih
  rw [rowEncodeList, List.filter_append, List.filter_cons_of_neg (by simp [Cell.isFrame]),
    List.filter_append, rowCells, rows, frames, answers]
  simp

theorem region_rowEncode (view : W → List X) (x : Config W C F A) (ρ : X → Bool) :
    (rowEncode view x).filter (fun cell => cellRegion ρ cell = true) =
      (((regionRows ρ (view x.world)).map Cell.world : List (RowCell X C F A)) :
        Multiset (RowCell X C F A)) := by
  rw [rowEncode_eq_coe, Multiset.filter_coe]
  congr 1
  have same : (fun cell : RowCell X C F A => decide (cellRegion ρ cell = true)) = cellRegion ρ := by
    funext cell
    simp
  rw [same]
  simp only [rowEncodeList, List.filter_append, List.filter_cons, cellRegion, filter_rowCells,
    filter_popCells, filter_answers]
  simp

/-- **A row label is held by at most one occurrence** of a represented store. -/
theorem count_row_le_one (view : W → List X) (x : Config W C F A) (p : X × ℕ) :
    (rowEncode view x).count (Cell.world p) ≤ 1 := by
  have rest : (Cell.control x.control x.stack.length ::ₘ
      (((popCells x.stack 0 : List (RowCell X C F A)) : Multiset (RowCell X C F A)) +
        ((x.emitted.map Cell.answer : List (RowCell X C F A)) : Multiset (RowCell X C F A)))).count
          (Cell.world p) = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro member
    simp only [Multiset.mem_cons, Multiset.mem_add, Multiset.mem_coe] at member
    rcases member with same | inFrames | inAnswers
    · cases same
    · have := popCells_frames x.stack 0 _ inFrames
      simp [Cell.isFrame] at this
    · obtain ⟨a, _, same⟩ := List.mem_map.mp inAnswers
      cases same
  unfold rowEncode
  rw [Multiset.count_add, rest, add_zero, Multiset.coe_count]
  exact List.nodup_iff_count_le_one.mp (rowCells_nodup _) _

end Encoding

/-! ## Distinct occurrences, sorted rows -/

section Occurrences

variable {X C F A : Type}

/-- Two occurrences of a store with one label are one occurrence, when the label is held once. -/
theorem eq_of_label_eq {T : Type} [DecidableEq T] {store : Finset (T × ℕ)} {o o' : T × ℕ}
    (present : o ∈ store) (present' : o' ∈ store) (same : o.1 = o'.1)
    (single : (labels Prod.fst store).count o.1 ≤ 1) : o = o' := by
  by_contra different
  have two : ({o, o'} : Finset (T × ℕ)) ⊆ store.filter fun q => o.1 = q.1 := by
    intro q member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨present, rfl⟩
    · exact Finset.mem_filter.mpr ⟨present', same⟩
  have card := Finset.card_le_card two
  rw [Finset.card_pair different] at card
  have counted : (labels Prod.fst store).count o.1 = (store.filter fun q => o.1 = q.1).card := by
    unfold labels
    rw [Multiset.count_map]
    rfl
  omega

/-- Two lists of positioned rows, each in increasing position, that carry one bag of cells are
one list. -/
theorem eq_of_coe_map_world {L L' : List (X × ℕ)}
    (sorted : L.Pairwise fun p q => p.2 < q.2) (sorted' : L'.Pairwise fun p q => p.2 < q.2)
    (same : ((L.map Cell.world : List (RowCell X C F A)) : Multiset (RowCell X C F A)) =
      ((L'.map Cell.world : List (RowCell X C F A)) : Multiset (RowCell X C F A))) :
    L = L' := by
  have perm := Multiset.coe_eq_coe.mp same
  have mapped : (L.map Cell.world : List (RowCell X C F A)) = L'.map Cell.world :=
    List.Perm.eq_of_pairwise (le := fun a b => cellIndex a < cellIndex b)
      (fun _ _ _ _ ab ba => absurd (Nat.lt_trans ab ba) (Nat.lt_irrefl _))
      (List.pairwise_map.mpr sorted) (List.pairwise_map.mpr sorted') perm
  exact List.map_injective_iff.mpr world_injective mapped

/-- **Facts of one ground firing**: its selection carries the rule's reads and takes, its knowledge
keeps identical sides, and the labels move by its takes and makes. -/
theorem firing_facts {T : Type} [DecidableEq T] {before : Configuration T (T × ℕ)}
    {rule : RuleInstance T} {sel : Selection (T × ℕ)}
    (valid : sel.Valid (groundAction T) Prod.fst rule before) :
    sel.read.map Prod.fst = rule.read ∧ sel.taken.map Prod.fst = rule.take ∧
      Trivial (sel.problem Prod.fst rule before) ∧
      labels Prod.fst (sel.result Prod.fst rule before).present =
        labels Prod.fst before.present - (rule.take : Multiset T) + (rule.produce : Multiset T) := by
  obtain ⟨⟨⟩, solved⟩ := valid.consistent
  obtain ⟨_, takesMatch, readsMatch, _⟩ := Selection.models_problem (groundAction T) valid solved
  have mapTake : sel.taken.map Prod.fst = rule.take := matched_map takesMatch
  have mapRead : sel.read.map Prod.fst = rule.read := matched_map readsMatch
  refine ⟨mapRead, mapTake, fun e member => solved e member, ?_⟩
  change labels Prod.fst (fire before.present (sel.commit (T := T))) = _
  rw [labels_fire valid.occurrences]
  change labels Prod.fst before.present - labels Prod.fst sel.taken.toFinset +
    labels Prod.fst sel.made.toFinset = _
  rw [labels_toFinset valid.take_distinct, labels_toFinset valid.output_distinct, mapTake,
    valid.outputs]

end Occurrences

/-! ## Footprints and the rules -/

section Rules

variable {W X C F A : Type}

/-- **A footprint**: for each move (control and popped frames before, control and pushed frames
after), the region of rows it depends on. -/
abbrev Footprint (C F X : Type) := C → List F → C → List F → X → Bool

/-- **World-locality**: a move depends on the world only through the rows of its region, with their
positions. -/
def WorldLocal (M : FramedMachine W C F A) (view : W → List X) (foot : Footprint C F X) : Prop :=
  ∀ {w w₀ : W} {c c' : C} {pop push : List F},
    regionRows (foot c pop c' push) (view w) = regionRows (foot c pop c' push) (view w₀) →
    M.Framed w c pop w c' push → M.Framed w₀ c pop w₀ c' push

/-- A read-only machine: no transition changes the world. -/
def ReadOnly (M : FramedMachine W C F A) : Prop :=
  ∀ {w w' : W} {c c' : C} {s s' : List F}, M.transition w (c, s) w' (c', s') → w' = w

/-- A move that reads the positioned rows `R`: take the control and the popped frames, read the
rows, make the new control and the pushed frames. -/
def footRule (R : List (X × ℕ)) (c : C) (pop : List F) (c' : C) (push : List F) (b : ℕ) :
    RuleInstance (RowCell X C F A) :=
  ⟨.control c (pop.length + b) :: popCells pop b, R.map Cell.world, [], [],
    .control c' (push.length + b) :: popCells push b⟩

/-- **The rules of a machine with a footprint**: each framed read-only move over every base depth,
reading the rows of its region in a world where it is a move, with that region; and publication,
with the empty region. -/
inductive FootRules (M : FramedMachine W C F A) (view : W → List X) (foot : Footprint C F X) :
    RuleInstance (RowCell X C F A) → (X → Bool) → Prop
  | reading {w : W} {c c' : C} {pop push : List F} (b : ℕ) :
      M.Framed w c pop w c' push →
      FootRules M view foot (footRule (regionRows (foot c pop c' push) (view w)) c pop c' push b)
        (foot c pop c' push)
  | publish {c c' : C} {a : A} :
      M.publish c = some (a, c') → FootRules M view foot (publishRule c a c') (fun _ => false)

/-- **The complete observation** of a firing with region `ρ`: the region holds exactly the
occurrences it read. -/
def observation (ρ : X → Bool) (sel : Selection (RowCell X C F A × ℕ)) :
    PredicateQueryAdmission.Query (RowCell X C F A) Unit (RowCell X C F A × ℕ) :=
  PredicateQueryAdmission.Query.fixed ⟨cellRegion ρ, sel.read.toFinset⟩

/-- **The step under a machine's footprinted rules**: one rule instance, admitted by the occurrence
step together with the complete observation of its region (`PredicateQueryAdmission.Valid`). -/
def RowStep (M : FramedMachine W C F A) (view : W → List X) (foot : Footprint C F X)
    (before after : Store (X × ℕ) C F A) : Prop :=
  ∃ rule ρ, FootRules M view foot rule ρ ∧
    ∃ sel : Selection (RowCell X C F A × ℕ),
      PredicateQueryAdmission.Valid (groundAction (RowCell X C F A)) Prod.fst rule
        [observation ρ sel] before sel ∧
      after = sel.result Prod.fst rule before

/-- A firing is a step of `PredicateQueryAdmission`, with its observation. -/
theorem RowStep.predicateStep {M : FramedMachine W C F A} {view : W → List X}
    {foot : Footprint C F X} {before after : Store (X × ℕ) C F A}
    (step : RowStep M view foot before after) :
    ∃ rule ρ seen, FootRules M view foot rule ρ ∧
      PredicateQueryAdmission.Step (groundAction (RowCell X C F A)) Prod.fst rule
        [PredicateQueryAdmission.Query.fixed ⟨cellRegion ρ, seen⟩] before after := by
  obtain ⟨rule, ρ, member, sel, valid, rfl⟩ := step
  exact ⟨rule, ρ, sel.read.toFinset, member, sel, valid, rfl⟩

/-- **Representation**: knowledge has identical sides, and the store's labels are the
configuration's cells. -/
def RowRepresents (view : W → List X) (S : Store (X × ℕ) C F A) (x : Config W C F A) : Prop :=
  Trivial S.equations ∧ labels Prod.fst S.present = rowEncode view x

/-- **Every configuration is represented**, by distinct occurrences of its cells and no
knowledge. -/
theorem row_exists_represents (view : W → List X) (x : Config W C F A) :
    ∃ S : Store (X × ℕ) C F A, RowRepresents view S x := by
  obtain ⟨os, distinct, _, mapped⟩ := fresh_outputs (rowEncodeList view x) ∅
  refine ⟨⟨[], os.toFinset⟩, fun e member => by simp at member, ?_⟩
  change labels Prod.fst os.toFinset = rowEncode view x
  rw [labels_toFinset distinct, mapped, rowEncode_eq_coe]

end Rules

/-! ## The observation of a represented store -/

section Observation

variable {W X C F A : Type}

/-- **Reading the region's rows makes the observation hold**: in a represented store, the
occurrences of the region are exactly the occurrences of its rows. -/
theorem observation_holds {view : W → List X} {S : Store (X × ℕ) C F A} {x : Config W C F A}
    (represented : RowRepresents view S x) {ρ : X → Bool} {sel : Selection (RowCell X C F A × ℕ)}
    (inStore : ∀ o ∈ sel.read, o ∈ S.present)
    (mapped : sel.read.map Prod.fst = (regionRows ρ (view x.world)).map Cell.world) :
    (⟨cellRegion ρ, sel.read.toFinset⟩ :
      PredicateQuery (RowCell X C F A × ℕ) (RowCell X C F A)).Holds Prod.fst S.present := by
  unfold PredicateQuery.Holds
  ext o
  rw [mem_regionOf, List.mem_toFinset]
  constructor
  · rintro ⟨present, inRegion⟩
    have label : o.1 ∈ labels Prod.fst S.present := Multiset.mem_map_of_mem _ present
    rw [represented.2] at label
    have filtered : o.1 ∈ (rowEncode view x).filter (fun cell => cellRegion ρ cell = true) :=
      Multiset.mem_filter.mpr ⟨label, inRegion⟩
    rw [region_rowEncode, Multiset.mem_coe] at filtered
    obtain ⟨p, _, hp⟩ := List.mem_map.mp filtered
    rw [← mapped] at filtered
    obtain ⟨o', read, same⟩ := List.mem_map.mp filtered
    have single : (labels Prod.fst S.present).count o.1 ≤ 1 := by
      rw [represented.2, ← hp]
      exact count_row_le_one view x p
    rw [eq_of_label_eq present (inStore o' read) same.symm single]
    exact read
  · intro read
    refine ⟨inStore o read, ?_⟩
    have inRows : o.1 ∈ (regionRows ρ (view x.world)).map Cell.world := by
      rw [← mapped]
      exact List.mem_map.mpr ⟨o, read, rfl⟩
    obtain ⟨p, member, hp⟩ := List.mem_map.mp inRows
    rw [← hp]
    unfold regionRows at member
    exact (List.mem_filter.mp member).2

/-- **The observation forces the region's rows**: when the observation of a firing that reads the
sorted rows `R` holds in a represented store, `R` is the region's rows of the world. -/
theorem observed_regionRows {view : W → List X} {S : Store (X × ℕ) C F A} {x : Config W C F A}
    (represented : RowRepresents view S x) {ρ : X → Bool} {R : List (X × ℕ)}
    (sorted : R.Pairwise fun p q => p.2 < q.2) {sel : Selection (RowCell X C F A × ℕ)}
    (mapped : sel.read.map Prod.fst = R.map Cell.world)
    (holds : (⟨cellRegion ρ, sel.read.toFinset⟩ :
      PredicateQuery (RowCell X C F A × ℕ) (RowCell X C F A)).Holds Prod.fst S.present) :
    R = regionRows ρ (view x.world) := by
  have distinct : sel.read.Nodup := by
    have : (sel.read.map Prod.fst).Nodup := by
      rw [mapped]
      exact List.Nodup.map world_injective (nodup_of_sorted sorted)
    exact List.Nodup.of_map _ this
  have region : regionOf Prod.fst S.present (cellRegion ρ) = sel.read.toFinset := holds
  have bag := congrArg (labels Prod.fst) region
  rw [labels_toFinset distinct, mapped] at bag
  have left : labels Prod.fst (regionOf Prod.fst S.present (cellRegion ρ)) =
      (labels Prod.fst S.present).filter (fun cell => cellRegion ρ cell = true) := by
    unfold labels regionOf
    rw [Finset.filter_val, Multiset.filter_map]
    rfl
  rw [left, represented.2, region_rowEncode] at bag
  exact (eq_of_coe_map_world (regionRows_pairwise ρ _) sorted bag).symm

end Observation

/-! ## The bisimulation -/

section Bisimulation

variable {W X C F A : Type} {M : FramedMachine W C F A} {view : W → List X}
  {foot : Footprint C F X}

/-- The reads of a firing lie in the store. -/
theorem reads_present {T : Type} [DecidableEq T] {before : Configuration T (T × ℕ)}
    {rule : RuleInstance T} {sel : Selection (T × ℕ)}
    (valid : sel.Valid (groundAction T) Prod.fst rule before) :
    ∀ o ∈ sel.read, o ∈ before.present := fun _ read =>
  valid.occurrences.kept_subset (show _ ∈ sel.read.toFinset from List.mem_toFinset.mpr read)

/-- **Every firing is a step of a world-local machine.** -/
theorem row_store_to_machine (worldLocal : WorldLocal M view foot) {S S' : Store (X × ℕ) C F A}
    {x : Config W C F A} (represented : RowRepresents view S x)
    (step : RowStep M view foot S S') : ∃ x', M.Step x x' ∧ RowRepresents view S' x' := by
  obtain ⟨rule, ρ, member, sel, valid, rfl⟩ := step
  obtain ⟨mapRead, mapTake, knowledge', moved⟩ := firing_facts valid.firing
  have takes : (rule.take : Multiset (RowCell X C F A)) ≤ labels Prod.fst S.present := by
    rw [← mapTake, ← labels_toFinset valid.firing.take_distinct]
    exact labels_mono valid.firing.occurrences.taken_subset
  have holds : (⟨cellRegion ρ, sel.read.toFinset⟩ :
      PredicateQuery (RowCell X C F A × ℕ) (RowCell X C F A)).Holds Prod.fst S.present :=
    (PredicateQueryAdmission.Query.fixed_ask_iff valid.firing.consistent).mp
      (valid.observations _ (List.mem_singleton_self _))
  have cells := represented.2
  rw [cells] at takes moved
  obtain ⟨w, c, s, e⟩ := x
  cases member with
  | @reading w₀ c₀ c₁ pop push b framed =>
      have rowsSame := observed_regionRows represented (regionRows_pairwise _ _) mapRead holds
      have framed' := worldLocal rowsSame framed
      have controlIn : Cell.control c₀ (pop.length + b) ∈
          rowEncode view (⟨w, c, s, e⟩ : Config W C F A) :=
        Multiset.mem_of_le takes (by simp [footRule])
      obtain ⟨hc, depth⟩ := control_mem_rowEncode controlIn
      have frames : ((popCells pop b : List (RowCell X C F A)) : Multiset (RowCell X C F A)) ≤
          ((popCells s 0 : List (RowCell X C F A)) : Multiset (RowCell X C F A)) := by
        have filtered :=
          Multiset.filter_le_filter (fun cell : RowCell X C F A => cell.isFrame = true) takes
        rw [frames_rowEncode] at filtered
        have notControl :
            ¬ ((Cell.control c₀ (pop.length + b) : RowCell X C F A).isFrame = true) := by
          simp [Cell.isFrame]
        have popFrames :
            ((popCells pop b : List (RowCell X C F A)) : Multiset (RowCell X C F A)).filter
              (fun cell => cell.isFrame = true) =
                ((popCells pop b : List (RowCell X C F A)) : Multiset (RowCell X C F A)) :=
          Multiset.filter_eq_self.mpr fun cell inPop =>
            popCells_frames pop b cell (Multiset.mem_coe.mp inPop)
        simp only [footRule, ← Multiset.cons_coe] at filtered
        rw [Multiset.filter_cons_of_neg (p := fun cell : RowCell X C F A => cell.isFrame = true) _
          notControl, popFrames] at filtered
        exact filtered
      obtain ⟨base, hs, hb⟩ := stack_of_popCells_le pop s b depth.symm frames
      subst hc hs hb
      refine ⟨⟨w, c₁, push ++ base, e⟩, FramedMachine.Step.internal (framed' base), knowledge', ?_⟩
      change labels Prod.fst (sel.result Prod.fst _ S).present = _
      rw [moved, rowEncode_split, rowEncode_split]
      simp only [footRule]
      rw [add_tsub_cancel_left]
      exact add_comm _ _
  | @publish c₀ c₁ a emitted =>
      have controlIn : Cell.control c₀ 0 ∈ rowEncode view (⟨w, c, s, e⟩ : Config W C F A) :=
        Multiset.mem_of_le takes (by simp [publishRule])
      obtain ⟨hc, depth⟩ := control_mem_rowEncode controlIn
      have empty : s = [] := List.length_eq_zero_iff.mp depth.symm
      subst hc empty
      refine ⟨⟨w, c₁, [], e ++ [a]⟩, FramedMachine.Step.publish emitted, knowledge', ?_⟩
      change labels Prod.fst (sel.result Prod.fst _ S).present = _
      rw [moved, rowEncode_publish, rowEncode_published]
      simp only [publishRule]
      rw [add_tsub_cancel_left]
      exact add_comm _ _

/-- **Every step of a local read-only machine is one firing.** -/
theorem row_machine_to_store (loc : M.Local) (readOnly : ReadOnly M) {S : Store (X × ℕ) C F A}
    {x x' : Config W C F A} (represented : RowRepresents view S x) (step : M.Step x x') :
    ∃ S', RowStep M view foot S S' ∧ RowRepresents view S' x' := by
  obtain ⟨knowledge, cells⟩ := represented
  cases step with
  | @internal w w' c c' s s' e transition =>
      have same : w' = w := readOnly transition
      subst w'
      obtain ⟨pop, push, base, rfl, rfl, framed⟩ := loc transition
      have readsLe : (((regionRows (foot c pop c' push) (view w)).map Cell.world :
          List (RowCell X C F A)) : Multiset (RowCell X C F A)) ≤
            ((rowCells (view w) : List (RowCell X C F A)) : Multiset (RowCell X C F A)) :=
        Multiset.coe_le.mpr ((List.filter_sublist).map Cell.world).subperm
      obtain ⟨S', fires, knowledge', moved⟩ :=
        fire_of_le S (footRule (regionRows (foot c pop c' push) (view w)) c pop c' push
          base.length) rfl rfl knowledge (by
            rw [cells, rowEncode_split]
            simp only [footRule]
            rw [← Multiset.coe_add, add_comm]
            exact add_le_add le_rfl (readsLe.trans (Multiset.le_add_right _ _)))
      obtain ⟨sel, valid, rfl⟩ := fires
      obtain ⟨mapRead, _, _, _⟩ := firing_facts valid
      have holds := observation_holds (ρ := foot c pop c' push) ⟨knowledge, cells⟩
        (reads_present valid) mapRead
      refine ⟨_, ⟨_, _, .reading base.length framed, sel, ⟨valid, ?_⟩, rfl⟩, knowledge', ?_⟩
      · intro query member
        rw [List.mem_singleton] at member
        subst member
        exact (PredicateQueryAdmission.Query.fixed_ask_iff valid.consistent).mpr holds
      · rw [moved, cells, rowEncode_split, rowEncode_split]
        simp only [footRule]
        rw [add_tsub_cancel_left]
        exact add_comm _ _
  | @publish w c c' a e emitted =>
      obtain ⟨S', fires, knowledge', moved⟩ :=
        fire_of_le S (publishRule c a c') rfl rfl knowledge (by
          rw [cells, rowEncode_publish]
          simp only [publishRule, List.nil_append]
          exact Multiset.le_add_right _ _)
      obtain ⟨sel, valid, rfl⟩ := fires
      obtain ⟨mapRead, _, _, _⟩ := firing_facts valid
      have mapped : sel.read.map Prod.fst =
          (regionRows (fun _ : X => false) (view w)).map Cell.world := by
        rw [mapRead, regionRows_none]
        rfl
      have holds := observation_holds (ρ := fun _ : X => false) ⟨knowledge, cells⟩
        (reads_present valid) mapped
      refine ⟨_, ⟨_, _, .publish emitted, sel, ⟨valid, ?_⟩, rfl⟩, knowledge', ?_⟩
      · intro query member
        rw [List.mem_singleton] at member
        subst member
        exact (PredicateQueryAdmission.Query.fixed_ask_iff valid.consistent).mpr holds
      · rw [moved, cells, rowEncode_publish, rowEncode_published]
        simp only [publishRule]
        rw [add_tsub_cancel_left]
        exact add_comm _ _

/-- **A local, read-only, world-local machine is strongly bisimilar to the step under its
footprinted rules**, through representation. -/
theorem row_bisimulation (loc : M.Local) (readOnly : ReadOnly M)
    (worldLocal : WorldLocal M view foot) :
    IsBisimulation (RowStep M view foot) M.Step (RowRepresents view) :=
  ⟨fun represented step => row_store_to_machine worldLocal represented step,
    fun represented step => row_machine_to_store loc readOnly represented step⟩

/-- **What a firing reads is its region's rows**, with their positions, and nothing else. -/
theorem row_reads_exact {S : Store (X × ℕ) C F A} {x : Config W C F A}
    (represented : RowRepresents view S x) {rule : RuleInstance (RowCell X C F A)} {ρ : X → Bool}
    (member : FootRules M view foot rule ρ) {sel : Selection (RowCell X C F A × ℕ)}
    (valid : PredicateQueryAdmission.Valid (groundAction (RowCell X C F A)) Prod.fst rule
      [observation ρ sel] S sel) :
    rule.read = (regionRows ρ (view x.world)).map Cell.world := by
  obtain ⟨mapRead, _, _, _⟩ := firing_facts valid.firing
  have holds : (⟨cellRegion ρ, sel.read.toFinset⟩ :
      PredicateQuery (RowCell X C F A × ℕ) (RowCell X C F A)).Holds Prod.fst S.present :=
    (PredicateQueryAdmission.Query.fixed_ask_iff valid.firing.consistent).mp
      (valid.observations _ (List.mem_singleton_self _))
  cases member with
  | reading b framed =>
      have rowsSame := observed_regionRows represented (regionRows_pairwise _ _) mapRead holds
      simp only [footRule]
      rw [rowsSame]
  | publish emitted =>
      simp only [publishRule, regionRows_none, List.map_nil]

/-- **Which region a firing reads**: the footprint of a move from the store's own control, or the
empty region of publication; and it reads exactly that region's rows. -/
theorem row_firing_region {S S' : Store (X × ℕ) C F A} {x : Config W C F A}
    (represented : RowRepresents view S x) (step : RowStep M view foot S S') :
    ∃ (rule : RuleInstance (RowCell X C F A)) (ρ : X → Bool), FootRules M view foot rule ρ ∧
      rule.read = (regionRows ρ (view x.world)).map Cell.world ∧
      ((∃ pop c' push, ρ = foot x.control pop c' push) ∨ ρ = fun _ => false) := by
  obtain ⟨rule, ρ, member, sel, valid, rfl⟩ := step
  refine ⟨rule, ρ, member, row_reads_exact represented member valid, ?_⟩
  obtain ⟨_, mapTake, _, _⟩ := firing_facts valid.firing
  have takes : (rule.take : Multiset (RowCell X C F A)) ≤ labels Prod.fst S.present := by
    rw [← mapTake, ← labels_toFinset valid.firing.take_distinct]
    exact labels_mono valid.firing.occurrences.taken_subset
  rw [represented.2] at takes
  cases member with
  | @reading w₀ c₀ c₁ pop push b framed =>
      have controlIn : Cell.control c₀ (pop.length + b) ∈ rowEncode view x :=
        Multiset.mem_of_le takes (by simp [footRule])
      obtain ⟨hc, _⟩ := control_mem_rowEncode controlIn
      exact Or.inl ⟨pop, c₁, push, by rw [hc]⟩
  | publish emitted => exact Or.inr rfl

theorem row_store_path_to_machine (worldLocal : WorldLocal M view foot)
    {S S' : Store (X × ℕ) C F A} {x : Config W C F A} (represented : RowRepresents view S x)
    (path : Relation.ReflTransGen (RowStep M view foot) S S') :
    ∃ x', Relation.ReflTransGen M.Step x x' ∧ RowRepresents view S' x' := by
  induction path with
  | refl => exact ⟨x, .refl, represented⟩
  | tail _ step ih =>
      obtain ⟨y, path, here⟩ := ih
      obtain ⟨y', step', there⟩ := row_store_to_machine worldLocal here step
      exact ⟨y', path.tail step', there⟩

theorem row_machine_path_to_store (loc : M.Local) (readOnly : ReadOnly M)
    {S : Store (X × ℕ) C F A} {x x' : Config W C F A} (represented : RowRepresents view S x)
    (path : Relation.ReflTransGen M.Step x x') :
    ∃ S', Relation.ReflTransGen (RowStep M view foot) S S' ∧ RowRepresents view S' x' := by
  induction path with
  | refl => exact ⟨S, .refl, represented⟩
  | tail _ step ih =>
      obtain ⟨T, path, here⟩ := ih
      obtain ⟨T', step', there⟩ := row_machine_to_store loc readOnly here step
      exact ⟨T', path.tail step', there⟩

/-- **Stuck on one side, stuck on the other.** -/
theorem row_stuck_iff (loc : M.Local) (readOnly : ReadOnly M)
    (worldLocal : WorldLocal M view foot) {S : Store (X × ℕ) C F A} {x : Config W C F A}
    (represented : RowRepresents view S x) :
    (∀ S', ¬ RowStep M view foot S S') ↔ ∀ x', ¬ M.Step x x' := by
  constructor
  · intro stuck x' step
    obtain ⟨S', fires, _⟩ := row_machine_to_store (foot := foot) loc readOnly represented step
    exact stuck S' fires
  · intro stuck S' fires
    obtain ⟨x', step, _⟩ := row_store_to_machine worldLocal represented fires
    exact stuck x' step

/-- The possible outcomes on the step: the answer bag and the positioned rows of every reached
store. -/
def rowStoreOutcomes (M : FramedMachine W C F A) (view : W → List X) (foot : Footprint C F X)
    (S : Store (X × ℕ) C F A) : Set (Multiset A × Multiset (X × ℕ)) :=
  {o | ∃ S', Relation.ReflTransGen (RowStep M view foot) S S' ∧
    o = (answersOf (labels Prod.fst S'.present), rowsOf (labels Prod.fst S'.present))}

/-- The machine's possible outcomes: the published answers as a bag, and the positioned rows of the
world reached. -/
def rowMachineOutcomes (M : FramedMachine W C F A) (view : W → List X) (x : Config W C F A) :
    Set (Multiset A × Multiset (X × ℕ)) :=
  {o | ∃ x', Relation.ReflTransGen M.Step x x' ∧
    o = ((x'.emitted : Multiset A), ((view x'.world).zipIdx : Multiset (X × ℕ)))}

/-- **The observations agree**: the answer bag and the rows reached. -/
theorem row_outcomes_eq (loc : M.Local) (readOnly : ReadOnly M)
    (worldLocal : WorldLocal M view foot) {S : Store (X × ℕ) C F A} {x : Config W C F A}
    (represented : RowRepresents view S x) :
    rowStoreOutcomes M view foot S = rowMachineOutcomes M view x := by
  ext o
  constructor
  · rintro ⟨S', path, rfl⟩
    obtain ⟨x', path', here⟩ := row_store_path_to_machine worldLocal represented path
    exact ⟨x', path', by rw [here.2, answersOf_rowEncode, rowsOf_rowEncode]⟩
  · rintro ⟨x', path, rfl⟩
    obtain ⟨S', path', here⟩ := row_machine_path_to_store (foot := foot) loc readOnly represented path
    exact ⟨S', path', by rw [here.2, answersOf_rowEncode, rowsOf_rowEncode]⟩

end Bisimulation

/-! ## Controls -/

namespace Controls

/-- A machine that moves from `false` to `true` when its world holds a row `true`. -/
def peeker : FramedMachine (List Bool) Bool Unit Unit where
  transition w cs w' cs' := w' = w ∧ cs.1 = false ∧ cs'.1 = true ∧ cs'.2 = cs.2 ∧ true ∈ w
  publish _ := none

/-- The peeker declared as reading nothing. -/
def blind : Footprint Bool Unit Bool := fun _ _ _ _ _ => false

/-- The peeker declared with its true region: the rows `true`. -/
def exact : Footprint Bool Unit Bool := fun _ _ _ _ row => row

theorem peeker_local : peeker.Local := by
  intro w w' c c' s s' transition
  obtain ⟨hw, hc, hc', hs, holds⟩ := transition
  exact ⟨[], [], s, rfl, by simpa using hs, fun _ => ⟨hw, hc, hc', rfl, holds⟩⟩

theorem peeker_readOnly : ReadOnly peeker := fun transition => transition.1

/-- **Negative control: a footprint that leaves out what the move looks at.** The peeker declared
blind is not world-local; from a store representing the world `[]`, where the machine is stuck,
the step fires. -/
theorem peeker_missed :
    ¬ WorldLocal peeker id blind ∧
      (∀ x', ¬ peeker.Step ⟨[], false, [], []⟩ x') ∧
      ∀ S : Store (Bool × ℕ) Bool Unit Unit, RowRepresents id S ⟨[], false, [], []⟩ →
        ∃ S', RowStep peeker id blind S S' := by
  refine ⟨fun worldLocal => ?_, ?_, ?_⟩
  · have framed : peeker.Framed [true] false [] [true] true [] :=
      fun _ => ⟨rfl, rfl, rfl, rfl, by simp⟩
    have moved := worldLocal (w := [true]) (w₀ := []) (by simp [regionRows, blind]) framed []
    exact absurd moved.2.2.2.2 (by simp)
  · intro x' step
    cases step with
    | internal transition => exact absurd transition.2.2.2.2 (by simp)
    | publish emitted => cases emitted
  · intro S represented
    have framed : peeker.Framed [true] false [] [true] true [] :=
      fun _ => ⟨rfl, rfl, rfl, rfl, by simp⟩
    obtain ⟨knowledge, cells⟩ := represented
    obtain ⟨S', fires, _, _⟩ :=
      fire_of_le S (footRule (regionRows (blind false [] true []) (id [true])) false [] true [] 0)
        rfl rfl knowledge (by
          rw [cells]
          simp [footRule, regionRows, blind, rowEncode, popCells])
    obtain ⟨sel, valid, rfl⟩ := fires
    obtain ⟨mapRead, _, _, _⟩ := firing_facts valid
    have mapped : sel.read.map Prod.fst =
        (regionRows (blind false [] true []) (id ([] : List Bool))).map Cell.world := by
      rw [mapRead]
      simp [footRule, regionRows, blind]
    have holds := observation_holds (ρ := blind false [] true []) ⟨knowledge, cells⟩
      (reads_present valid) mapped
    refine ⟨_, _, _, .reading 0 framed, sel, ⟨valid, ?_⟩, rfl⟩
    intro query member
    rw [List.mem_singleton] at member
    subst member
    exact (PredicateQueryAdmission.Query.fixed_ask_iff valid.consistent).mpr holds

/-- **Positive control: with its true region the peeker is world-local**: two worlds with the same
rows `true` at the same positions agree on whether a row `true` is there. -/
theorem peeker_exact_local : WorldLocal peeker id exact := by
  intro w w₀ c c' pop push same framed base
  obtain ⟨_, hc, hc', hs, holds⟩ := framed base
  refine ⟨rfl, hc, hc', hs, ?_⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp holds
  have inRows : (true, i) ∈ regionRows (exact c pop c' push) (id w) :=
    List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr hi, rfl⟩
  rw [same] at inRows
  exact List.mem_iff_getElem?.mpr ⟨i, List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp inRows).1⟩

/-- **Positive control: the firing reads only its region's row.** From the world `[false, true]`,
every firing of the peeker with its true region reads the row `(true, 1)` and not `(false, 0)`. -/
theorem peeker_reads_only_its_row {S : Store (Bool × ℕ) Bool Unit Unit}
    (represented : RowRepresents id S ⟨[false, true], false, [], []⟩)
    {rule : RuleInstance (RowCell Bool Bool Unit Unit)} {ρ : Bool → Bool}
    (member : FootRules peeker id exact rule ρ) {sel : Selection (RowCell Bool Bool Unit Unit × ℕ)}
    (valid : PredicateQueryAdmission.Valid (groundAction (RowCell Bool Bool Unit Unit)) Prod.fst rule
      [observation ρ sel] S sel) (moving : ρ = fun row => row) :
    rule.read = [Cell.world (true, 1)] := by
  rw [row_reads_exact represented member valid, moving]
  rfl

end Controls

#print axioms regionRows_pairwise
#print axioms count_row_le_one
#print axioms eq_of_label_eq
#print axioms eq_of_coe_map_world
#print axioms observation_holds
#print axioms observed_regionRows
#print axioms row_exists_represents
#print axioms row_store_to_machine
#print axioms row_machine_to_store
#print axioms row_bisimulation
#print axioms row_reads_exact
#print axioms row_firing_region
#print axioms row_stuck_iff
#print axioms row_outcomes_eq
#print axioms RowStep.predicateStep
#print axioms Controls.peeker_missed
#print axioms Controls.peeker_exact_local
#print axioms Controls.peeker_reads_only_its_row

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
