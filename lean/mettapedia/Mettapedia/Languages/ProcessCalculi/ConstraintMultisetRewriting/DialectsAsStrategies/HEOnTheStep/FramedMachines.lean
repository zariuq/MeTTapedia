import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.TransitionMaps
import Mettapedia.Machines.ProgressObservation

/-!
# Framed machines on the step: one transition, one firing

A **framed machine** has a world, a control (the pending work), a stack of first-order
continuation frames, and the answers it has published. A transition (`FramedMachine.transition`)
relates world, control and stack before and after; publication (`FramedMachine.publish`) emits the
next answer of a control when the stack is empty.

The machine is placed on the step's store (`encode`): one occurrence holds the world, one the control
together with the depth of the stack, one each frame at its depth from the bottom, one each
published answer. A transition is one firing of a rule of `Rules`:

* it takes the control and the frames it pops, and makes the new control and the frames it pushes;
* it **reads** the world when it keeps it, and **takes** the world and makes the new one when it
  changes it;
* publication takes the control at depth zero and makes the next control and the answer.

Frames below the popped ones are not touched, so a firing's footprint is what the transition uses.
That is honest exactly when transitions are **local** (`FramedMachine.Local`): every transition
pops some frames and pushes some frames, and the same move is a transition over every other base of
the stack (`FramedMachine.Framed`).

## Results

* `store_to_machine`: every firing of the rules, from a store representing a configuration, is a
  transition from it, and the result represents the target. Locality is not needed here.
* `machine_to_store`: for a local machine, every transition is one firing.
* `bisimulation`: for a local machine, representation is a **strong bisimulation** between the step
  restricted to the rules and the machine. Every configuration is represented
  (`exists_represents`).
* Readouts (`answersOf`, `worldsOf`): the bag of published answers and the world, read off the
  store's labels (`answersOf_encode`, `worldsOf_encode`); the outcomes reachable on both sides agree
  (`outcomes_eq`), and so do the stuck configurations (`stuck_iff`).
* No added divergence: no firing is administrative, so every infinite execution of the step under
  these rules observes machine moves arbitrarily far along it (`nonZeno`, through
  `Machines.ProgressObservation`); and infinite executions correspond in both directions
  (`machine_divergence_lifts`, `store_divergence_projects`, `divergence_iff`).

## Controls

* `Controls.bottomReader_missed`: a machine whose transition reads the bottom of the stack without
  popping it is not local; it steps while the step under its rules never fires. The bisimulation
  needs locality.
* `Controls.counter_local`, `Controls.counter_fires`: a machine that pushes and pops frames is
  local, so it is bisimilar, and its first move is a firing.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep

open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire labels labels_fire labels_mono)
open FragmentsOfTheStep.TransitionMaps

/-! ## Ground terms over any labels -/

/-- Ground terms over a label type: the identity is the only solution and equal means identical. -/
def groundAction (T : Type) : SubstitutionAction T Unit where
  E := Eq
  equivalence := ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩
  apply := fun _ t => t
  identity := ()
  compose := fun _ _ => ()
  apply_identity := fun _ => rfl
  apply_compose := fun _ _ _ => rfl
  preserves := fun _ _ _ same => same

section Ground

variable {T : Type} [DecidableEq T]

/-- Knowledge whose equations have identical sides. -/
def Trivial (eqs : EquationStore T) : Prop := ∀ e ∈ eqs, e.1 = e.2

/-- Labels of a store, split at one present occurrence. -/
theorem labels_split (store : Finset (T × ℕ)) {o : T × ℕ} (present : o ∈ store) :
    labels Prod.fst store = o.1 ::ₘ labels Prod.fst (store.erase o) := by
  unfold labels
  rw [Finset.erase_val, ← Multiset.map_cons, Multiset.cons_erase present]

/-- **Distinct occurrences for a bag of labels**: a list of labels below the store's labels is
carried by distinct present occurrences. -/
theorem select_occurrences :
    ∀ (ls : List T) (store : Finset (T × ℕ)), (ls : Multiset T) ≤ labels Prod.fst store →
      ∃ os : List (T × ℕ), os.Nodup ∧ (∀ o ∈ os, o ∈ store) ∧ os.map Prod.fst = ls
  | [], _, _ => ⟨[], List.nodup_nil, by simp, rfl⟩
  | l :: ls, store, le => by
      have mem : l ∈ labels Prod.fst store := Multiset.mem_of_le le (by simp)
      obtain ⟨o, present, same⟩ : ∃ o ∈ store, o.1 = l := by
        unfold labels at mem
        obtain ⟨o, member, same⟩ := Multiset.mem_map.mp mem
        exact ⟨o, member, same⟩
      subst same
      have rest : (ls : Multiset T) ≤ labels Prod.fst (store.erase o) := by
        rw [labels_split store present, ← Multiset.cons_coe] at le
        exact (Multiset.cons_le_cons_iff _).mp le
      obtain ⟨os, distinct, inside, mapped⟩ := select_occurrences ls (store.erase o) rest
      refine ⟨o :: os, List.nodup_cons.mpr ⟨fun member => ?_, distinct⟩, ?_, by simp [mapped]⟩
      · exact (Finset.mem_erase.mp (inside o member)).1 rfl
      · intro p member
        rcases List.mem_cons.mp member with rfl | later
        · exact present
        · exact (Finset.mem_erase.mp (inside p later)).2

/-- Labels of distinct occurrences are the labels of the list. -/
theorem labels_toFinset {os : List (T × ℕ)} (distinct : os.Nodup) :
    labels Prod.fst os.toFinset = ((os.map Prod.fst : List T) : Multiset T) := by
  unfold labels
  rw [List.toFinset_val, distinct.dedup, Multiset.map_coe]

omit [DecidableEq T] in
/-- A fresh occurrence for every label beside every store. -/
theorem exists_fresh (used : Finset (T × ℕ)) (value : T) :
    ∃ o : T × ℕ, o ∉ used ∧ o.1 = value := by
  obtain ⟨n, unused⟩ := Infinite.exists_notMem_finset (used.image Prod.snd)
  exact ⟨(value, n), fun member => unused (Finset.mem_image.mpr ⟨_, member, rfl⟩), rfl⟩

/-- Distinct fresh occurrences carrying any list of labels. -/
theorem fresh_outputs : ∀ (values : List T) (world : Finset (T × ℕ)), ∃ made : List (T × ℕ),
    made.Nodup ∧ Disjoint made.toFinset world ∧ made.map Prod.fst = values
  | [], _ => ⟨[], by simp, by simp, rfl⟩
  | value :: values, world => by
      obtain ⟨o, fresh, atValue⟩ := exists_fresh world value
      obtain ⟨made, distinct, away, outputs⟩ := fresh_outputs values (insert o world)
      have absent : o ∉ made := fun member =>
        Finset.disjoint_left.mp away (by simpa using member) (by simp)
      refine ⟨o :: made, List.nodup_cons.mpr ⟨absent, distinct⟩, ?_, ?_⟩
      · apply Finset.disjoint_left.mpr
        intro item inMade inWorld
        rcases List.mem_cons.mp (by simpa using inMade) with rfl | member
        · exact fresh inWorld
        · exact Finset.disjoint_left.mp away (by simpa using member) (by simp [inWorld])
      · simp [outputs, atValue]

omit [DecidableEq T] in
/-- Equations between labels and their own occurrences have identical sides. -/
theorem trivial_equations : ∀ (os : List (T × ℕ)),
    Trivial (Selection.equations Prod.fst (os.map Prod.fst) os)
  | [] => fun e member => by simp [Selection.equations] at member
  | o :: rest => fun e member => by
      simp only [Selection.equations, List.map_cons, List.zipWith_cons_cons, List.mem_cons] at member
      rcases member with rfl | later
      · rfl
      · exact trivial_equations rest e later

omit [DecidableEq T] in
theorem matched_map {patterns : List T} {os : List (T × ℕ)}
    (matched : List.Forall₂ (fun p (o : T × ℕ) => (groundAction T).E ((groundAction T).apply () p)
      ((groundAction T).apply () o.1)) patterns os) : os.map Prod.fst = patterns := by
  induction matched with
  | nil => rfl
  | @cons p o ps os' head _ ih =>
      have same : p = o.1 := head
      rw [List.map_cons, ih, same]

/-- **Firing a rule over ground labels.** A rule without checks and tells, whose reads and takes lie
in the store's labels, fires; the labels move by the rule's takes and makes, and knowledge keeps
identical sides. -/
theorem fire_of_le (C : Configuration T (T × ℕ)) (rule : RuleInstance T)
    (noChecks : rule.checks = []) (noTells : rule.tell = []) (trivial : Trivial C.equations)
    (enough : ((rule.read ++ rule.take : List T) : Multiset T) ≤ labels Prod.fst C.present) :
    ∃ C', ConstraintMultisetRewriting.Step (groundAction T) Prod.fst rule C C' ∧
      Trivial C'.equations ∧
      labels Prod.fst C'.present =
        labels Prod.fst C.present - (rule.take : Multiset T) + (rule.produce : Multiset T) := by
  obtain ⟨os, distinct, inside, mapped⟩ := select_occurrences _ _ enough
  obtain ⟨reads, takes, rfl, mapRead, mapTake⟩ : ∃ reads takes : List (T × ℕ),
      os = reads ++ takes ∧ reads.map Prod.fst = rule.read ∧ takes.map Prod.fst = rule.take :=
    ⟨os.take rule.read.length, os.drop rule.read.length, (List.take_append_drop _ _).symm,
      by rw [List.map_take, mapped, List.take_left' rfl],
      by rw [List.map_drop, mapped, List.drop_left' rfl]⟩
  obtain ⟨made, madeDistinct, madeFresh, madeLabels⟩ := fresh_outputs rule.produce C.present
  have takesNodup : takes.Nodup := (List.nodup_append.mp distinct).2.1
  let sel : Selection (T × ℕ) := ⟨takes, reads, made⟩
  have enabled : Enabled Prod.fst C.present (sel.commit (T := T)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro o member
      exact inside o (List.mem_append_right _ (List.mem_toFinset.mp member))
    · intro o member
      exact inside o (List.mem_append_left _ (List.mem_toFinset.mp member))
    · rw [Finset.disjoint_left]
      intro o inTakes inReads
      exact List.disjoint_of_nodup_append distinct (List.mem_toFinset.mp inReads)
        (List.mem_toFinset.mp inTakes)
    · exact madeFresh
    · intro read member
      simp [Selection.commit] at member
  have problemTrivial : Trivial (sel.problem Prod.fst rule C) := by
    intro e member
    simp only [Selection.problem, noTells, List.append_nil, List.mem_append] at member
    rcases member with (old | taken) | read
    · exact trivial e old
    · rw [← mapTake] at taken
      exact trivial_equations takes e taken
    · rw [← mapRead] at read
      exact trivial_equations reads e read
  have valid : sel.Valid (groundAction T) Prod.fst rule C := by
    refine ⟨takesNodup, madeDistinct, ?_, ?_, madeLabels, enabled, ⟨(), problemTrivial⟩, ?_⟩
    · rw [← mapTake, List.length_map]
    · rw [← mapRead, List.length_map]
    · intro check member
      rw [noChecks] at member
      cases member
  refine ⟨sel.result Prod.fst rule C, ⟨sel, valid, rfl⟩, problemTrivial, ?_⟩
  change labels Prod.fst (fire C.present (sel.commit (T := T))) = _
  rw [labels_fire enabled]
  change labels Prod.fst C.present - labels Prod.fst takes.toFinset +
    labels Prod.fst made.toFinset = _
  rw [labels_toFinset takesNodup, labels_toFinset madeDistinct, mapTake, madeLabels]

/-- **Reading a ground firing.** A firing's takes lie in the store's labels, so do its reads, the
labels move by its takes and makes, and knowledge keeps identical sides. -/
theorem read_firing {C C' : Configuration T (T × ℕ)} {rule : RuleInstance T}
    (step : ConstraintMultisetRewriting.Step (groundAction T) Prod.fst rule C C') :
    (rule.take : Multiset T) ≤ labels Prod.fst C.present ∧
      (∀ l ∈ rule.read, l ∈ labels Prod.fst C.present) ∧
      Trivial C'.equations ∧
      labels Prod.fst C'.present =
        labels Prod.fst C.present - (rule.take : Multiset T) + (rule.produce : Multiset T) := by
  obtain ⟨sel, valid, rfl⟩ := step
  obtain ⟨⟨⟩, solved⟩ := valid.consistent
  obtain ⟨_, takesMatch, readsMatch, _⟩ := Selection.models_problem (groundAction T) valid solved
  have mapTake : sel.taken.map Prod.fst = rule.take := matched_map takesMatch
  have mapRead : sel.read.map Prod.fst = rule.read := matched_map readsMatch
  refine ⟨?_, ?_, fun e member => solved e member, ?_⟩
  · rw [← mapTake, ← labels_toFinset valid.take_distinct]
    exact labels_mono valid.occurrences.taken_subset
  · intro l member
    rw [← mapRead] at member
    obtain ⟨o, inRead, rfl⟩ := List.mem_map.mp member
    have present : o ∈ C.present :=
      valid.occurrences.kept_subset (show o ∈ sel.read.toFinset from List.mem_toFinset.mpr inRead)
    exact Multiset.mem_map.mpr ⟨o, present, rfl⟩
  · change labels Prod.fst (fire C.present (sel.commit (T := T))) = _
    rw [labels_fire valid.occurrences]
    change labels Prod.fst C.present - labels Prod.fst sel.taken.toFinset +
      labels Prod.fst sel.made.toFinset = _
    rw [labels_toFinset valid.take_distinct, labels_toFinset valid.output_distinct, mapTake,
      valid.outputs]

end Ground

/-! ## Framed machines -/

/-- **A framed machine**: a transition on world, control and stack, and publication of answers at
the empty stack. -/
structure FramedMachine (W C F A : Type) where
  transition : W → C × List F → W → C × List F → Prop
  publish : C → Option (A × C)

/-- A configuration: the world, the control, the stack (top first), and the published answers. -/
structure Config (W C F A : Type) where
  world : W
  control : C
  stack : List F
  emitted : List A

namespace FramedMachine

variable {W C F A : Type} (M : FramedMachine W C F A)

/-- The machine's steps: a transition, or a publication at the empty stack. -/
inductive Step : Config W C F A → Config W C F A → Prop
  | internal {w w' : W} {c c' : C} {s s' : List F} {e : List A} :
      M.transition w (c, s) w' (c', s') → Step ⟨w, c, s, e⟩ ⟨w', c', s', e⟩
  | publish {w : W} {c c' : C} {a : A} {e : List A} :
      M.publish c = some (a, c') → Step ⟨w, c, [], e⟩ ⟨w, c', [], e ++ [a]⟩

/-- A move that pops `pop` and pushes `push`, and is a transition over every base of the stack. -/
def Framed (w : W) (c : C) (pop : List F) (w' : W) (c' : C) (push : List F) : Prop :=
  ∀ base, M.transition w (c, pop ++ base) w' (c', push ++ base)

/-- **Locality**: every transition pops some frames, pushes some, and is framed. -/
def Local : Prop :=
  ∀ {w w' : W} {c c' : C} {s s' : List F}, M.transition w (c, s) w' (c', s') →
    ∃ pop push base, s = pop ++ base ∧ s' = push ++ base ∧ M.Framed w c pop w' c' push

end FramedMachine

/-! ## The machine's occurrences -/

/-- What one occurrence holds: the world, the control with the stack's depth, one frame at its depth
from the bottom, or one published answer. -/
inductive Cell (W C F A : Type) where
  | world (w : W)
  | control (c : C) (depth : ℕ)
  | frame (depth : ℕ) (f : F)
  | answer (a : A)

namespace Cell

variable {W C F A : Type}

def isFrame : Cell W C F A → Bool
  | world _ => false
  | control _ _ => false
  | frame _ _ => true
  | answer _ => false

def answer? : Cell W C F A → Option A
  | world _ => none
  | control _ _ => none
  | frame _ _ => none
  | answer a => some a

def world? : Cell W C F A → Option W
  | world w => some w
  | control _ _ => none
  | frame _ _ => none
  | answer _ => none

end Cell

instance (W C F A : Type) : DecidableEq (Cell W C F A) := Classical.decEq _

section Encoding

variable {W C F A : Type}

/-- The frames of a stack over a base of `b` frames, each at its depth from the bottom. -/
def popCells : List F → ℕ → List (Cell W C F A)
  | [], _ => []
  | f :: s, b => .frame (s.length + b) f :: popCells s b

theorem popCells_append : ∀ (p q : List F) (b : ℕ),
    (popCells (p ++ q) b : List (Cell W C F A)) = popCells p (q.length + b) ++ popCells q b
  | [], _, _ => rfl
  | f :: p, q, b => by
      simp only [List.cons_append, popCells, List.length_append, popCells_append p q b]
      congr 2
      omega

theorem depth_lt : ∀ {s : List F} {b d : ℕ} {f : F},
    (Cell.frame d f : Cell W C F A) ∈ (popCells s b : List (Cell W C F A)) → d < s.length + b
  | [], _, _, _, member => by simp [popCells] at member
  | g :: s, b, d, f, member => by
      simp only [popCells, List.mem_cons] at member
      rcases member with same | deeper
      · injection same with depth _
        simp only [List.length_cons]
        omega
      · have := depth_lt deeper
        simp only [List.length_cons]
        omega

theorem popCells_frames (s : List F) (b : ℕ) :
    ∀ cell ∈ (popCells s b : List (Cell W C F A)), cell.isFrame = true := by
  induction s with
  | nil => simp [popCells]
  | cons f s ih =>
      intro cell member
      simp only [popCells, List.mem_cons] at member
      rcases member with rfl | later
      · rfl
      · exact ih cell later

theorem answers_popCells (s : List F) (b : ℕ) :
    (popCells s b : List (Cell W C F A)).filterMap Cell.answer? = [] := by
  induction s with
  | nil => rfl
  | cons f s ih =>
      simp only [popCells, List.filterMap_cons, Cell.answer?]
      exact ih

theorem worlds_popCells (s : List F) (b : ℕ) :
    (popCells s b : List (Cell W C F A)).filterMap Cell.world? = [] := by
  induction s with
  | nil => rfl
  | cons f s ih =>
      simp only [popCells, List.filterMap_cons, Cell.world?]
      exact ih

theorem answers_map (e : List A) :
    (e.map (Cell.answer (W := W) (C := C) (F := F))).filterMap Cell.answer? = e := by
  induction e with
  | nil => rfl
  | cons a e ih =>
      simp only [List.map_cons, List.filterMap_cons, Cell.answer?]
      exact congrArg (a :: ·) ih

theorem worlds_map (e : List A) :
    (e.map (Cell.answer (W := W) (C := C) (F := F))).filterMap Cell.world? = [] := by
  induction e with
  | nil => rfl
  | cons a e ih =>
      simp only [List.map_cons, List.filterMap_cons, Cell.world?]
      exact ih

/-- **The store of a configuration**, as the bag of its occurrences' labels. -/
def encode (x : Config W C F A) : Multiset (Cell W C F A) :=
  Cell.world x.world ::ₘ Cell.control x.control x.stack.length ::ₘ
    (((popCells x.stack 0 : List (Cell W C F A)) : Multiset (Cell W C F A)) +
      ((x.emitted.map Cell.answer : List (Cell W C F A)) : Multiset (Cell W C F A)))

/-- The cells of a configuration, as a list. -/
def encodeList (x : Config W C F A) : List (Cell W C F A) :=
  Cell.world x.world :: Cell.control x.control x.stack.length ::
    (popCells x.stack 0 ++ x.emitted.map Cell.answer)

theorem encode_eq_coe (x : Config W C F A) : encode x = (encodeList x : Multiset (Cell W C F A)) := by
  unfold encode encodeList
  rw [Multiset.coe_add]
  rfl

theorem frames_encode (x : Config W C F A) :
    (encode x).filter (fun cell => cell.isFrame = true) =
      ((popCells x.stack 0 : List (Cell W C F A)) : Multiset (Cell W C F A)) := by
  have frames : ((popCells x.stack 0 : List (Cell W C F A)) : Multiset (Cell W C F A)).filter
      (fun cell => cell.isFrame = true) =
        ((popCells x.stack 0 : List (Cell W C F A)) : Multiset (Cell W C F A)) :=
    Multiset.filter_eq_self.mpr fun cell member =>
      popCells_frames x.stack 0 cell (Multiset.mem_coe.mp member)
  have answers : (((x.emitted.map Cell.answer : List (Cell W C F A)) : Multiset (Cell W C F A))).filter
      (fun cell => cell.isFrame = true) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro cell member
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp member)
    simp [Cell.isFrame]
  have notWorld : ¬ ((Cell.world x.world : Cell W C F A).isFrame = true) := by simp [Cell.isFrame]
  have notControl : ¬ ((Cell.control x.control x.stack.length : Cell W C F A).isFrame = true) := by
    simp [Cell.isFrame]
  unfold encode
  rw [Multiset.filter_cons_of_neg (p := fun cell : Cell W C F A => cell.isFrame = true) _ notWorld,
    Multiset.filter_cons_of_neg (p := fun cell : Cell W C F A => cell.isFrame = true) _ notControl,
    Multiset.filter_add, frames, answers, add_zero]

theorem control_mem_encode {x : Config W C F A} {c : C} {n : ℕ}
    (member : Cell.control c n ∈ encode x) : c = x.control ∧ n = x.stack.length := by
  unfold encode at member
  simp only [Multiset.mem_cons, Multiset.mem_add, Multiset.mem_coe] at member
  rcases member with same | same | inFrames | inAnswers
  · cases same
  · injection same with c n
    exact ⟨c, n⟩
  · have := popCells_frames x.stack 0 _ inFrames
    simp [Cell.isFrame] at this
  · obtain ⟨a, _, same⟩ := List.mem_map.mp inAnswers
    cases same

theorem world_mem_encode {x : Config W C F A} {w : W}
    (member : Cell.world w ∈ encode x) : w = x.world := by
  unfold encode at member
  simp only [Multiset.mem_cons, Multiset.mem_add, Multiset.mem_coe] at member
  rcases member with same | same | inFrames | inAnswers
  · injection same with same
  · cases same
  · have := popCells_frames x.stack 0 _ inFrames
    simp [Cell.isFrame] at this
  · obtain ⟨a, _, same⟩ := List.mem_map.mp inAnswers
    cases same

/-- Frames found on top of a stack of the right depth are its top. -/
theorem stack_of_popCells_le : ∀ (pop s : List F) (b : ℕ), s.length = pop.length + b →
    ((popCells pop b : List (Cell W C F A)) : Multiset (Cell W C F A)) ≤
      ((popCells s 0 : List (Cell W C F A)) : Multiset (Cell W C F A)) →
    ∃ base, s = pop ++ base ∧ base.length = b
  | [], s, b, len, _ => ⟨s, rfl, by simpa using len⟩
  | f :: pop, [], b, len, _ => by
      simp only [List.length_nil, List.length_cons] at len
      omega
  | f :: pop, g :: s, b, len, le => by
      simp only [List.length_cons] at len
      have len' : s.length = pop.length + b := by omega
      have mem : (Cell.frame (pop.length + b) f : Cell W C F A) ∈
          ((popCells (g :: s) 0 : List (Cell W C F A)) : Multiset (Cell W C F A)) :=
        Multiset.mem_of_le le (by simp [popCells])
      have fg : f = g := by
        simp only [popCells, Multiset.mem_coe, List.mem_cons] at mem
        rcases mem with same | deeper
        · injection same
        · have := depth_lt deeper
          omega
      subst fg
      have rest : ((popCells pop b : List (Cell W C F A)) : Multiset (Cell W C F A)) ≤
          ((popCells s 0 : List (Cell W C F A)) : Multiset (Cell W C F A)) := by
        simp only [popCells, ← Multiset.cons_coe] at le
        rw [show s.length + 0 = pop.length + b by omega] at le
        exact (Multiset.cons_le_cons_iff _).mp le
      obtain ⟨base, rfl, baseLen⟩ := stack_of_popCells_le pop s b len' rest
      exact ⟨base, rfl, baseLen⟩

/-- **The split of a configuration's store** at a move: the control and the popped frames, and the
rest, which holds the world, the base frames and the answers. -/
theorem encode_split (w : W) (c : C) (pop base : List F) (e : List A) :
    encode (⟨w, c, pop ++ base, e⟩ : Config W C F A) =
      ((Cell.control c (pop.length + base.length) :: popCells pop base.length :
          List (Cell W C F A)) : Multiset (Cell W C F A)) +
        (Cell.world w ::ₘ (((popCells base 0 : List (Cell W C F A)) : Multiset (Cell W C F A)) +
          ((e.map Cell.answer : List (Cell W C F A)) : Multiset (Cell W C F A)))) := by
  unfold encode
  simp only [popCells_append, Nat.add_zero, List.length_append, ← Multiset.coe_add,
    ← Multiset.cons_coe, ← Multiset.singleton_add]
  abel

/-- The same split with the world among the taken cells. -/
theorem encode_split_world (w : W) (c : C) (pop base : List F) (e : List A) :
    encode (⟨w, c, pop ++ base, e⟩ : Config W C F A) =
      ((Cell.world w :: Cell.control c (pop.length + base.length) :: popCells pop base.length :
          List (Cell W C F A)) : Multiset (Cell W C F A)) +
        (((popCells base 0 : List (Cell W C F A)) : Multiset (Cell W C F A)) +
          ((e.map Cell.answer : List (Cell W C F A)) : Multiset (Cell W C F A))) := by
  unfold encode
  simp only [popCells_append, Nat.add_zero, List.length_append, ← Multiset.coe_add,
    ← Multiset.cons_coe, ← Multiset.singleton_add]
  abel

theorem encode_publish (w : W) (c : C) (e : List A) :
    encode (⟨w, c, [], e⟩ : Config W C F A) =
      (([Cell.control c 0] : List (Cell W C F A)) : Multiset (Cell W C F A)) +
        (Cell.world w ::ₘ ((e.map Cell.answer : List (Cell W C F A)) : Multiset (Cell W C F A))) := by
  unfold encode
  simp only [popCells, List.length_nil, Multiset.coe_nil, zero_add, ← Multiset.cons_coe,
    ← Multiset.singleton_add]
  abel

theorem encode_published (w : W) (c : C) (a : A) (e : List A) :
    encode (⟨w, c, [], e ++ [a]⟩ : Config W C F A) =
      (([Cell.control c 0, Cell.answer a] : List (Cell W C F A)) : Multiset (Cell W C F A)) +
        (Cell.world w ::ₘ ((e.map Cell.answer : List (Cell W C F A)) : Multiset (Cell W C F A))) := by
  unfold encode
  simp only [popCells, List.length_nil, Multiset.coe_nil, zero_add, List.map_append, List.map_cons,
    List.map_nil, ← Multiset.coe_add, ← Multiset.cons_coe, ← Multiset.singleton_add, add_zero]
  abel

end Encoding

/-! ## The rules -/

section Rules

variable {W C F A : Type}

/-- A move that keeps the world: take the control and the popped frames, read the world, make the
new control and the pushed frames. -/
def readingRule (w : W) (c : C) (pop : List F) (c' : C) (push : List F) (b : ℕ) :
    RuleInstance (Cell W C F A) :=
  ⟨.control c (pop.length + b) :: popCells pop b, [.world w], [], [],
    .control c' (push.length + b) :: popCells push b⟩

/-- A move that changes the world: also take the world and make the new one. -/
def writingRule (w : W) (c : C) (pop : List F) (w' : W) (c' : C) (push : List F) (b : ℕ) :
    RuleInstance (Cell W C F A) :=
  ⟨.world w :: .control c (pop.length + b) :: popCells pop b, [], [], [],
    .world w' :: .control c' (push.length + b) :: popCells push b⟩

/-- Publication: take the control at depth zero, make the next control and the answer. -/
def publishRule (c : C) (a : A) (c' : C) : RuleInstance (Cell W C F A) :=
  ⟨[.control c 0], [], [], [], [.control c' 0, .answer a]⟩

/-- **The rules of a framed machine**: its framed moves over every base depth, and publication. -/
inductive Rules (M : FramedMachine W C F A) : RuleInstance (Cell W C F A) → Prop
  | reading {w : W} {c c' : C} {pop push : List F} (b : ℕ) :
      M.Framed w c pop w c' push → Rules M (readingRule w c pop c' push b)
  | writing {w w' : W} {c c' : C} {pop push : List F} (b : ℕ) :
      w' ≠ w → M.Framed w c pop w' c' push → Rules M (writingRule w c pop w' c' push b)
  | publish {c c' : C} {a : A} : M.publish c = some (a, c') → Rules M (publishRule c a c')

/-- The step's stores for a framed machine: occurrences are labelled cells with copy numbers. -/
abbrev Store (W C F A : Type) := Configuration (Cell W C F A) (Cell W C F A × ℕ)

/-- **The step restricted to the machine's rules**, over ground labels. -/
def StoreStep (M : FramedMachine W C F A) (before after : Store W C F A) : Prop :=
  ∃ rule, Rules M rule ∧
    ConstraintMultisetRewriting.Step (groundAction (Cell W C F A)) Prod.fst rule before after

/-- **Representation**: knowledge has identical sides, and the store's labels are the
configuration's cells. -/
def Represents (S : Store W C F A) (x : Config W C F A) : Prop :=
  Trivial S.equations ∧ labels Prod.fst S.present = encode x

/-- **Every configuration is represented**, by distinct occurrences of its cells and no
knowledge. -/
theorem exists_represents (x : Config W C F A) : ∃ S : Store W C F A, Represents S x := by
  obtain ⟨os, distinct, _, mapped⟩ := fresh_outputs (encodeList x) ∅
  refine ⟨⟨[], os.toFinset⟩, fun e member => by simp at member, ?_⟩
  change labels Prod.fst os.toFinset = encode x
  rw [labels_toFinset distinct, mapped, encode_eq_coe]

end Rules

/-! ## The bisimulation -/

section Bisimulation

variable {W C F A : Type} {M : FramedMachine W C F A}

/-- **Every firing is a transition.** A firing of the machine's rules from a store representing a
configuration is a step of the machine to a configuration the result represents. -/
theorem store_to_machine {S S' : Store W C F A} {x : Config W C F A}
    (represented : Represents S x) (step : StoreStep M S S') :
    ∃ x', M.Step x x' ∧ Represents S' x' := by
  obtain ⟨knowledge, cells⟩ := represented
  obtain ⟨rule, member, fires⟩ := step
  obtain ⟨takes, reads, knowledge', moved⟩ := read_firing fires
  rw [cells] at takes reads moved
  obtain ⟨w, c, s, e⟩ := x
  cases member with
  | @reading w₀ c₀ c₁ pop push b framed =>
      have worldIn : Cell.world w₀ ∈ encode (⟨w, c, s, e⟩ : Config W C F A) :=
        reads _ (by simp [readingRule])
      have controlIn : Cell.control c₀ (pop.length + b) ∈ encode (⟨w, c, s, e⟩ : Config W C F A) :=
        Multiset.mem_of_le takes (by simp [readingRule])
      have hw : w₀ = w := world_mem_encode worldIn
      obtain ⟨hc, depth⟩ := control_mem_encode controlIn
      have frames : ((popCells pop b : List (Cell W C F A)) : Multiset (Cell W C F A)) ≤
          ((popCells s 0 : List (Cell W C F A)) : Multiset (Cell W C F A)) := by
        have filtered :=
          Multiset.filter_le_filter (fun cell : Cell W C F A => cell.isFrame = true) takes
        rw [frames_encode] at filtered
        have notControl : ¬ ((Cell.control c₀ (pop.length + b) : Cell W C F A).isFrame = true) := by
          simp [Cell.isFrame]
        have popFrames : ((popCells pop b : List (Cell W C F A)) : Multiset (Cell W C F A)).filter
            (fun cell => cell.isFrame = true) =
              ((popCells pop b : List (Cell W C F A)) : Multiset (Cell W C F A)) :=
          Multiset.filter_eq_self.mpr fun cell inPop =>
            popCells_frames pop b cell (Multiset.mem_coe.mp inPop)
        simp only [readingRule, ← Multiset.cons_coe] at filtered
        rw [Multiset.filter_cons_of_neg (p := fun cell : Cell W C F A => cell.isFrame = true) _
          notControl, popFrames] at filtered
        exact filtered
      obtain ⟨base, hs, hb⟩ := stack_of_popCells_le pop s b depth.symm frames
      subst hw hc hs hb
      refine ⟨⟨w₀, c₁, push ++ base, e⟩, FramedMachine.Step.internal (framed base), knowledge', ?_⟩
      rw [moved, encode_split, encode_split]
      simp only [readingRule]
      rw [add_tsub_cancel_left]
      exact add_comm _ _
  | @writing w₀ w₁ c₀ c₁ pop push b changed framed =>
      have worldIn : Cell.world w₀ ∈ encode (⟨w, c, s, e⟩ : Config W C F A) :=
        Multiset.mem_of_le takes (by simp [writingRule])
      have controlIn : Cell.control c₀ (pop.length + b) ∈ encode (⟨w, c, s, e⟩ : Config W C F A) :=
        Multiset.mem_of_le takes (by simp [writingRule])
      have hw : w₀ = w := world_mem_encode worldIn
      obtain ⟨hc, depth⟩ := control_mem_encode controlIn
      have frames : ((popCells pop b : List (Cell W C F A)) : Multiset (Cell W C F A)) ≤
          ((popCells s 0 : List (Cell W C F A)) : Multiset (Cell W C F A)) := by
        have filtered :=
          Multiset.filter_le_filter (fun cell : Cell W C F A => cell.isFrame = true) takes
        rw [frames_encode] at filtered
        have notWorld : ¬ ((Cell.world w₀ : Cell W C F A).isFrame = true) := by simp [Cell.isFrame]
        have notControl : ¬ ((Cell.control c₀ (pop.length + b) : Cell W C F A).isFrame = true) := by
          simp [Cell.isFrame]
        have popFrames : ((popCells pop b : List (Cell W C F A)) : Multiset (Cell W C F A)).filter
            (fun cell => cell.isFrame = true) =
              ((popCells pop b : List (Cell W C F A)) : Multiset (Cell W C F A)) :=
          Multiset.filter_eq_self.mpr fun cell inPop =>
            popCells_frames pop b cell (Multiset.mem_coe.mp inPop)
        simp only [writingRule, ← Multiset.cons_coe] at filtered
        rw [Multiset.filter_cons_of_neg (p := fun cell : Cell W C F A => cell.isFrame = true) _
          notWorld, Multiset.filter_cons_of_neg (p := fun cell : Cell W C F A => cell.isFrame = true) _
          notControl, popFrames] at filtered
        exact filtered
      obtain ⟨base, hs, hb⟩ := stack_of_popCells_le pop s b depth.symm frames
      subst hw hc hs hb
      refine ⟨⟨w₁, c₁, push ++ base, e⟩, FramedMachine.Step.internal (framed base), knowledge', ?_⟩
      rw [moved, encode_split_world, encode_split_world]
      simp only [writingRule]
      rw [add_tsub_cancel_left]
      exact add_comm _ _
  | @publish c₀ c₁ a emitted =>
      have controlIn : Cell.control c₀ 0 ∈ encode (⟨w, c, s, e⟩ : Config W C F A) :=
        Multiset.mem_of_le takes (by simp [publishRule])
      obtain ⟨hc, depth⟩ := control_mem_encode controlIn
      have empty : s = [] := List.length_eq_zero_iff.mp depth.symm
      subst hc empty
      refine ⟨⟨w, c₁, [], e ++ [a]⟩, FramedMachine.Step.publish emitted, knowledge', ?_⟩
      rw [moved, encode_publish, encode_published]
      simp only [publishRule]
      rw [add_tsub_cancel_left]
      exact add_comm _ _

/-- **Every transition of a local machine is one firing.** -/
theorem machine_to_store (loc : M.Local) {S : Store W C F A} {x x' : Config W C F A}
    (represented : Represents S x) (step : M.Step x x') :
    ∃ S', StoreStep M S S' ∧ Represents S' x' := by
  obtain ⟨knowledge, cells⟩ := represented
  cases step with
  | @internal w w' c c' s s' e transition =>
      obtain ⟨pop, push, base, rfl, rfl, framed⟩ := loc transition
      by_cases same : w' = w
      · subst same
        obtain ⟨S', fires, knowledge', moved⟩ :=
          fire_of_le S (readingRule w' c pop c' push base.length) rfl rfl knowledge (by
            rw [cells, encode_split]
            simp only [readingRule, List.singleton_append, ← Multiset.cons_coe]
            rw [Multiset.add_cons]
            exact (Multiset.cons_le_cons_iff _).mpr (Multiset.le_add_right _ _))
        refine ⟨S', ⟨_, .reading base.length framed, fires⟩, knowledge', ?_⟩
        rw [moved, cells, encode_split, encode_split]
        simp only [readingRule]
        rw [add_tsub_cancel_left]
        exact add_comm _ _
      · obtain ⟨S', fires, knowledge', moved⟩ :=
          fire_of_le S (writingRule w c pop w' c' push base.length) rfl rfl knowledge (by
            rw [cells, encode_split_world]
            simp only [writingRule, List.nil_append]
            exact Multiset.le_add_right _ _)
        refine ⟨S', ⟨_, .writing base.length same framed, fires⟩, knowledge', ?_⟩
        rw [moved, cells, encode_split_world, encode_split_world]
        simp only [writingRule]
        rw [add_tsub_cancel_left]
        exact add_comm _ _
  | @publish w c c' a e emitted =>
      obtain ⟨S', fires, knowledge', moved⟩ :=
        fire_of_le S (publishRule c a c') rfl rfl knowledge (by
          rw [cells, encode_publish]
          simp only [publishRule, List.nil_append]
          exact Multiset.le_add_right _ _)
      refine ⟨S', ⟨_, .publish emitted, fires⟩, knowledge', ?_⟩
      rw [moved, cells, encode_publish, encode_published]
      simp only [publishRule]
      rw [add_tsub_cancel_left]
      exact add_comm _ _

/-- **A local framed machine is strongly bisimilar to the step restricted to its rules**, through
representation. -/
theorem bisimulation (loc : M.Local) : IsBisimulation (StoreStep M) M.Step Represents :=
  ⟨fun represented step => store_to_machine represented step,
    fun represented step => machine_to_store loc represented step⟩

theorem store_path_to_machine {S S' : Store W C F A} {x : Config W C F A}
    (represented : Represents S x) (path : Relation.ReflTransGen (StoreStep M) S S') :
    ∃ x', Relation.ReflTransGen M.Step x x' ∧ Represents S' x' := by
  induction path with
  | refl => exact ⟨x, .refl, represented⟩
  | tail _ step ih =>
      obtain ⟨y, path, here⟩ := ih
      obtain ⟨y', step', there⟩ := store_to_machine here step
      exact ⟨y', path.tail step', there⟩

theorem machine_path_to_store (loc : M.Local) {S : Store W C F A} {x x' : Config W C F A}
    (represented : Represents S x) (path : Relation.ReflTransGen M.Step x x') :
    ∃ S', Relation.ReflTransGen (StoreStep M) S S' ∧ Represents S' x' := by
  induction path with
  | refl => exact ⟨S, .refl, represented⟩
  | tail _ step ih =>
      obtain ⟨T, path, here⟩ := ih
      obtain ⟨T', step', there⟩ := machine_to_store loc here step
      exact ⟨T', path.tail step', there⟩

/-- **Stuck on one side, stuck on the other.** -/
theorem stuck_iff (loc : M.Local) {S : Store W C F A} {x : Config W C F A}
    (represented : Represents S x) : (∀ S', ¬ StoreStep M S S') ↔ ∀ x', ¬ M.Step x x' := by
  constructor
  · intro stuck x' step
    obtain ⟨S', fires, _⟩ := machine_to_store loc represented step
    exact stuck S' fires
  · intro stuck S' fires
    obtain ⟨x', step, _⟩ := store_to_machine represented fires
    exact stuck x' step

end Bisimulation

/-! ## Readouts -/

section Readouts

variable {W C F A : Type}

/-- The answers held by a bag of cells. -/
def answersOf (m : Multiset (Cell W C F A)) : Multiset A := m.filterMap Cell.answer?

/-- The worlds held by a bag of cells. -/
def worldsOf (m : Multiset (Cell W C F A)) : Multiset W := m.filterMap Cell.world?

/-- **The answer bag of a represented store is the bag of the published answers.** -/
theorem answersOf_encode (x : Config W C F A) : answersOf (encode x) = (x.emitted : Multiset A) := by
  rw [encode_eq_coe]
  unfold answersOf
  rw [Multiset.filterMap_coe]
  congr 1
  simp only [encodeList, List.filterMap_cons, Cell.answer?, List.filterMap_append, answers_popCells,
    answers_map, List.nil_append]

/-- **The world of a represented store is the configuration's world.** -/
theorem worldsOf_encode (x : Config W C F A) : worldsOf (encode x) = {x.world} := by
  rw [encode_eq_coe]
  unfold worldsOf
  rw [Multiset.filterMap_coe]
  have list : (encodeList x).filterMap Cell.world? = [x.world] := by
    simp only [encodeList, List.filterMap_cons, Cell.world?, List.filterMap_append, worlds_popCells,
      worlds_map, List.nil_append]
  rw [list]
  rfl

variable (M : FramedMachine W C F A)

/-- The possible outcomes on the step: answer bag and worlds of every reached store. -/
def storeOutcomes (S : Store W C F A) : Set (Multiset A × Multiset W) :=
  {o | ∃ S', Relation.ReflTransGen (StoreStep M) S S' ∧
    o = (answersOf (labels Prod.fst S'.present), worldsOf (labels Prod.fst S'.present))}

/-- The machine's possible outcomes: the published answers as a bag, and the world reached. -/
def machineOutcomes (x : Config W C F A) : Set (Multiset A × Multiset W) :=
  {o | ∃ x', Relation.ReflTransGen M.Step x x' ∧ o = ((x'.emitted : Multiset A), {x'.world})}

variable {M}

/-- **The observations agree**: from a represented configuration, the step under the rules and the
machine have the same possible outcomes (answer bag, world reached). -/
theorem outcomes_eq (loc : M.Local) {S : Store W C F A} {x : Config W C F A}
    (represented : Represents S x) : storeOutcomes M S = machineOutcomes M x := by
  ext o
  constructor
  · rintro ⟨S', path, rfl⟩
    obtain ⟨x', path', here⟩ := store_path_to_machine represented path
    exact ⟨x', path', by rw [here.2, answersOf_encode, worldsOf_encode]⟩
  · rintro ⟨x', path, rfl⟩
    obtain ⟨S', path', here⟩ := machine_path_to_store loc represented path
    exact ⟨S', path', by rw [here.2, answersOf_encode, worldsOf_encode]⟩

end Readouts

/-! ## No added divergence -/

section Divergence

variable {W C F A : Type}

/-- The step's stores under a machine's rules, with firings as events. -/
def Fired (_M : FramedMachine W C F A) : Type := Store W C F A

/-- A firing of a rule of the machine. -/
def Firing (M : FramedMachine W C F A) (before after : Store W C F A) : Type :=
  {rule // Rules M rule ∧
    ConstraintMultisetRewriting.Step (groundAction (Cell W C F A)) Prod.fst rule before after}

instance (M : FramedMachine W C F A) : Quiver (Fired M) := ⟨Firing M⟩

/-- Every firing is observed: it is one machine move. -/
def fired (M : FramedMachine W C F A) :
    Mettapedia.Machines.ProgressObservation.Observation (Fired M) (RuleInstance (Cell W C F A)) :=
  fun {before after} event => some (Subtype.val (event : Firing M before after))

/-- **No administrative firings**: every infinite execution of the step under a machine's rules
observes machine moves arbitrarily far along it (window 9's productivity, through its potential
criterion: nothing is erased). This holds by construction of the observation: every firing of a
framed machine is labelled with its rule, so no firing is silent. It is a sanity property of the
encoding, not a dynamic result about HE. -/
theorem nonZeno (M : FramedMachine W C F A) :
    Mettapedia.Machines.ProgressObservation.NonZeno (fired M) :=
  Mettapedia.Machines.ProgressObservation.nonZeno_of_rank (fired M) (fun _ => 0)
    (fun event erased => by simp [fired] at erased)

variable {M : FramedMachine W C F A}

/-- **Machine divergence lifts**: an infinite run of a local machine is one infinite run of the
step, configuration by configuration. -/
theorem machine_divergence_lifts (loc : M.Local) {xs : ℕ → Config W C F A}
    (steps : ∀ n, M.Step (xs n) (xs (n + 1))) {S : Store W C F A} (represented : Represents S (xs 0)) :
    ∃ Ss : ℕ → Store W C F A, Ss 0 = S ∧
      ∀ n, StoreStep M (Ss n) (Ss (n + 1)) ∧ Represents (Ss n) (xs n) := by
  let lift : (n : ℕ) → {T : Store W C F A // Represents T (xs n)} := fun n =>
    Nat.rec (motive := fun n => {T : Store W C F A // Represents T (xs n)}) ⟨S, represented⟩
      (fun n previous => ⟨Classical.choose (machine_to_store loc previous.2 (steps n)),
        (Classical.choose_spec (machine_to_store loc previous.2 (steps n))).2⟩) n
  refine ⟨fun n => (lift n).1, rfl, fun n => ⟨?_, (lift n).2⟩⟩
  exact (Classical.choose_spec (machine_to_store loc (lift n).2 (steps n))).1

/-- **Store divergence projects**: an infinite run of the step under the rules is an infinite run of
the machine. -/
theorem store_divergence_projects {Ss : ℕ → Store W C F A}
    (steps : ∀ n, StoreStep M (Ss n) (Ss (n + 1))) {x : Config W C F A}
    (represented : Represents (Ss 0) x) :
    ∃ xs : ℕ → Config W C F A, xs 0 = x ∧
      ∀ n, M.Step (xs n) (xs (n + 1)) ∧ Represents (Ss n) (xs n) := by
  let project : (n : ℕ) → {y : Config W C F A // Represents (Ss n) y} := fun n =>
    Nat.rec (motive := fun n => {y : Config W C F A // Represents (Ss n) y}) ⟨x, represented⟩
      (fun n previous => ⟨Classical.choose (store_to_machine previous.2 (steps n)),
        (Classical.choose_spec (store_to_machine previous.2 (steps n))).2⟩) n
  refine ⟨fun n => (project n).1, rfl, fun n => ⟨?_, (project n).2⟩⟩
  exact (Classical.choose_spec (store_to_machine (project n).2 (steps n))).1

/-- **No added and no lost divergence**: from a represented configuration, the step under the rules
runs forever exactly when the machine can. -/
theorem divergence_iff (loc : M.Local) {S : Store W C F A} {x : Config W C F A}
    (represented : Represents S x) :
    (∃ Ss : ℕ → Store W C F A, Ss 0 = S ∧ ∀ n, StoreStep M (Ss n) (Ss (n + 1))) ↔
      ∃ xs : ℕ → Config W C F A, xs 0 = x ∧ ∀ n, M.Step (xs n) (xs (n + 1)) := by
  constructor
  · rintro ⟨Ss, rfl, steps⟩
    obtain ⟨xs, start, run⟩ := store_divergence_projects steps represented
    exact ⟨xs, start, fun n => (run n).1⟩
  · rintro ⟨xs, rfl, steps⟩
    obtain ⟨Ss, start, run⟩ := machine_divergence_lifts loc steps represented
    exact ⟨Ss, start, fun n => (run n).1⟩

end Divergence

/-! ## Controls -/

namespace Controls

/-- A transition that reads the bottom of the stack without popping it. -/
def bottomReader : FramedMachine Unit Bool Bool Unit where
  transition _ cs _ cs' := cs.1 = false ∧ cs'.1 = true ∧ cs'.2 = cs.2 ∧ cs.2.getLast? = some true
  publish _ := none

theorem bottomReader_transition :
    bottomReader.transition () (false, [true]) () (true, [true]) := ⟨rfl, rfl, rfl, rfl⟩

theorem bottomReader_not_framed {w w' : Unit} {c c' : Bool} {pop push : List Bool} :
    ¬ bottomReader.Framed w c pop w' c' push := by
  intro framed
  obtain ⟨_, _, _, last⟩ := framed [false]
  simp at last

/-- The rules of the bottom reader are empty: none of its moves is framed. -/
theorem bottomReader_rules_empty (rule : RuleInstance (Cell Unit Bool Bool Unit)) :
    ¬ Rules bottomReader rule := by
  intro member
  cases member with
  | reading _ framed => exact bottomReader_not_framed framed
  | writing _ _ framed => exact bottomReader_not_framed framed
  | publish emitted => simp [bottomReader] at emitted

/-- **Negative control: without locality the step misses the machine.** The bottom reader is not
local; it moves from `(false, [true])`, while the step under its rules never fires. -/
theorem bottomReader_missed :
    ¬ bottomReader.Local ∧
      bottomReader.Step ⟨(), false, [true], []⟩ ⟨(), true, [true], []⟩ ∧
      ∀ S S' : Store Unit Bool Bool Unit, ¬ StoreStep bottomReader S S' := by
  refine ⟨fun loc => ?_, .internal bottomReader_transition, ?_⟩
  · obtain ⟨_, _, _, _, _, framed⟩ := loc bottomReader_transition
    exact bottomReader_not_framed framed
  · rintro S S' ⟨rule, member, _⟩
    exact bottomReader_rules_empty rule member

/-- A counter: count down pushing a frame, then pop the frames at zero. -/
def counter : FramedMachine Unit ℕ Unit ℕ where
  transition _ cs _ cs' :=
    (∃ n, cs.1 = n + 1 ∧ cs'.1 = n ∧ cs'.2 = () :: cs.2) ∨
      (cs.1 = 0 ∧ cs'.1 = 0 ∧ cs.2 = () :: cs'.2)
  publish _ := none

/-- **Positive control: the counter is local.** -/
theorem counter_local : counter.Local := by
  intro w w' c c' s s' transition
  rcases transition with ⟨n, hc, hc', hs'⟩ | ⟨hc, hc', hs⟩
  · exact ⟨[], [()], s, rfl, hs', fun _ => Or.inl ⟨n, hc, hc', rfl⟩⟩
  · exact ⟨[()], [], s', hs, rfl, fun _ => Or.inr ⟨hc, hc', rfl⟩⟩

/-- **Positive control: the counter's first move is a firing**, from every store representing its
start, and such stores exist. -/
theorem counter_fires :
    (∃ S : Store Unit ℕ Unit ℕ, Represents S ⟨(), 1, [], []⟩) ∧
      ∀ S : Store Unit ℕ Unit ℕ, Represents S ⟨(), 1, [], []⟩ →
        ∃ S', StoreStep counter S S' ∧ Represents S' ⟨(), 0, [()], []⟩ :=
  ⟨exists_represents _, fun _ represented =>
    machine_to_store counter_local represented (.internal (Or.inl ⟨0, rfl, rfl, rfl⟩))⟩

end Controls

#print axioms fire_of_le
#print axioms read_firing
#print axioms exists_represents
#print axioms store_to_machine
#print axioms machine_to_store
#print axioms bisimulation
#print axioms stuck_iff
#print axioms answersOf_encode
#print axioms worldsOf_encode
#print axioms outcomes_eq
#print axioms nonZeno
#print axioms machine_divergence_lifts
#print axioms store_divergence_projects
#print axioms divergence_iff
#print axioms Controls.bottomReader_missed
#print axioms Controls.counter_local
#print axioms Controls.counter_fires

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep
