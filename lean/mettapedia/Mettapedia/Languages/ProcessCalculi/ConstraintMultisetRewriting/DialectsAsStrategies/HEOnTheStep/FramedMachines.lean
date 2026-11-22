import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedSubstitution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.TransitionMaps
import Mettapedia.Machines.ProgressObservation
import Mettapedia.GSLT.Core.RouteTrace

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

Frames below the selected footprint are untouched. For a **local** machine
(`FramedMachine.Local`), every transition has a pop/push witness that works
over every base of the stack (`FramedMachine.Framed`). The raw rule family
can also pop and re-make extra frames; this is invisible to label readback.
When physical identity matters, `internal_beneath` uses the local witness
to protect the attached base and `CustodyFiring` records actual occurrence
selection and issuance.

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
* An actual firing path gives a stronger publication observer:
  `firing_path_reads_answers` and `answerTrace_fires` preserve exact counts
  and ordered answer words, starting with the given publication history.
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

theorem taken_labels {before : Configuration T (T × ℕ)} {rule : RuleInstance T}
    {selected : Selection (T × ℕ)} (valid : selected.Valid (groundAction T) Prod.fst rule before) :
    selected.taken.map Prod.fst = rule.take := by
  obtain ⟨⟨⟩, solved⟩ := valid.consistent
  exact matched_map (Selection.models_problem (groundAction T) valid solved).2.1

/-- Choose the actual selected occurrences of a ground firing. The
made identities can avoid the whole issuance history, not just the
currently present store. -/
theorem fire_of_le_allocated (C : Configuration T (T × ℕ)) (rule : RuleInstance T)
    (issued : Finset (T × ℕ)) (covered : C.present ⊆ issued)
    (noChecks : rule.checks = []) (noTells : rule.tell = []) (trivial : Trivial C.equations)
    (enough : ((rule.read ++ rule.take : List T) : Multiset T) ≤ labels Prod.fst C.present) :
    ∃ picked : Selection (T × ℕ),
      picked.Valid (groundAction T) Prod.fst rule C ∧ Disjoint picked.made.toFinset issued ∧
      Trivial (picked.result Prod.fst rule C).equations ∧
      labels Prod.fst (picked.result Prod.fst rule C).present =
        labels Prod.fst C.present - (rule.take : Multiset T) + (rule.produce : Multiset T) := by
  obtain ⟨os, distinct, inside, mapped⟩ := select_occurrences _ _ enough
  obtain ⟨reads, takes, rfl, mapRead, mapTake⟩ : ∃ reads takes : List (T × ℕ),
      os = reads ++ takes ∧ reads.map Prod.fst = rule.read ∧ takes.map Prod.fst = rule.take :=
    ⟨os.take rule.read.length, os.drop rule.read.length, (List.take_append_drop _ _).symm,
      by rw [List.map_take, mapped, List.take_left' rfl],
      by rw [List.map_drop, mapped, List.drop_left' rfl]⟩
  obtain ⟨made, madeDistinct, unused, madeLabels⟩ := fresh_outputs rule.produce issued
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
    · exact unused.mono_right covered
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
  refine ⟨sel, valid, unused, problemTrivial, ?_⟩
  change labels Prod.fst (fire C.present (sel.commit (T := T))) = _
  rw [labels_fire enabled]
  change labels Prod.fst C.present - labels Prod.fst takes.toFinset +
    labels Prod.fst made.toFinset = _
  rw [labels_toFinset takesNodup, labels_toFinset madeDistinct, mapTake, madeLabels]

/-- **Firing a rule over ground labels.** A rule without checks and tells,
whose reads and takes lie in the store's labels, fires; labels move by
the rule's takes and makes, and knowledge keeps identical sides. -/
theorem fire_of_le (C : Configuration T (T × ℕ)) (rule : RuleInstance T)
    (noChecks : rule.checks = []) (noTells : rule.tell = []) (trivial : Trivial C.equations)
    (enough : ((rule.read ++ rule.take : List T) : Multiset T) ≤ labels Prod.fst C.present) :
    ∃ C', ConstraintMultisetRewriting.Step (groundAction T) Prod.fst rule C C' ∧
      Trivial C'.equations ∧
      labels Prod.fst C'.present =
        labels Prod.fst C.present - (rule.take : Multiset T) + (rule.produce : Multiset T) := by
  obtain ⟨picked, valid, _, known, labels'⟩ :=
    fire_of_le_allocated C rule C.present (fun _ member => member) noChecks noTells trivial enough
  exact ⟨_, ⟨picked, valid, rfl⟩, known, labels'⟩

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

@[simp] theorem popCells_length (stack : List F) (base : ℕ) :
    (popCells stack base : List (Cell W C F A)).length = stack.length := by
  induction stack with
  | nil => rfl
  | cons frame rest ih => simp only [popCells, List.length_cons, ih]

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

theorem popCells_nodup (s : List F) (b : ℕ) : (popCells s b : List (Cell W C F A)).Nodup := by
  induction s with
  | nil => exact List.nodup_nil
  | cons f rest ih =>
    apply List.nodup_cons.mpr
    refine ⟨fun member => ?_, ih⟩
    have smaller : rest.length + b < rest.length + b := depth_lt member
    exact (Nat.lt_irrefl _ smaller)

theorem popCells_depth_ge {s : List F} {base depth : ℕ} {frame : F}
    (member : (Cell.frame depth frame : Cell W C F A) ∈ (popCells s base : List (Cell W C F A))) :
    base ≤ depth := by
  induction s with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | later
    · injection same with atDepth _
      omega
    · exact ih later

/-- Depths recover the order of a stack even though stored cells form a bag. -/
theorem popCells_bag_injective (base : ℕ) :
    Function.Injective (fun stack : List F =>
      ((popCells stack base : List (Cell W C F A)) : Multiset (Cell W C F A))) := by
  intro first
  induction first with
  | nil =>
      intro second same
      have count := congrArg Multiset.card same
      have empty : second.length = 0 := by
        simpa only [Multiset.coe_card, popCells_length, List.length_nil] using count.symm
      exact (List.length_eq_zero_iff.mp empty).symm
  | cons frame rest ih =>
      intro second same
      have count := congrArg Multiset.card same
      have lengths : (frame :: rest).length = second.length := by
        simpa only [Multiset.coe_card, popCells_length] using count
      cases second with
      | nil => simp at lengths
      | cons other tail =>
          change ((popCells (frame :: rest) base : List (Cell W C F A)) : Multiset (Cell W C F A)) =
            ((popCells (other :: tail) base : List (Cell W C F A)) : Multiset (Cell W C F A)) at same
          have tails : rest.length = tail.length := Nat.succ.inj lengths
          have present : (Cell.frame (rest.length + base) frame : Cell W C F A) ∈ popCells (other :: tail) base := by
            apply Multiset.mem_coe.mp
            rw [← same]
            exact Multiset.mem_coe.mpr (List.mem_cons_self ..)
          rcases List.mem_cons.mp present with head | deeper
          · have frames : frame = other := (Cell.frame.inj head).2
            subst other
            have equalRest :
                ((popCells rest base : List (Cell W C F A)) : Multiset (Cell W C F A)) =
                  ((popCells tail base : List (Cell W C F A)) : Multiset (Cell W C F A)) := by
              simpa only [popCells, ← Multiset.cons_coe, tails, Multiset.cons_inj_right] using same
            exact congrArg (frame :: ·) (ih equalRest)
          · have impossible := depth_lt deeper
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

/-- Although the store uses a bag of cell labels, a frame at its given
depth has exactly one physical occurrence in a represented stack. -/
theorem same_frame_occurrence {S : Store W C F A} {x : Config W C F A}
    (represented : Represents S x) {left right : Cell W C F A × ℕ} {depth : ℕ} {frame : F}
    (leftLive : left ∈ S.present) (rightLive : right ∈ S.present)
    (leftLabel : left.1 = .frame depth frame) (rightLabel : right.1 = .frame depth frame) :
    left = right := by
  by_contra apart
  have rightStill : right ∈ S.present.erase left := Finset.mem_erase.mpr ⟨Ne.symm apart, rightLive⟩
  have all : ((labels Prod.fst S.present).filter (fun cell => cell.isFrame = true)).Nodup := by
    rw [represented.2, frames_encode]
    exact popCells_nodup x.stack 0
  rw [labels_split S.present leftLive, labels_split _ rightStill, leftLabel, rightLabel] at all
  rw [Multiset.filter_cons_of_pos _ (by rfl), Multiset.filter_cons_of_pos _ (by rfl)] at all
  exact (Multiset.nodup_cons.mp all).1 (by simp)

/-- The active control, like an individual stack slot, is single-copy. -/
theorem same_control_occurrence {S : Store W C F A} {x : Config W C F A}
    (represented : Represents S x) {left right : Cell W C F A × ℕ} {c : C} {depth : ℕ}
    (leftLive : left ∈ S.present) (rightLive : right ∈ S.present)
    (leftLabel : left.1 = .control c depth) (rightLabel : right.1 = .control c depth) :
    left = right := by
  classical
  by_contra apart
  have rightStill : right ∈ S.present.erase left := Finset.mem_erase.mpr ⟨Ne.symm apart, rightLive⟩
  let control : Cell W C F A := .control c depth
  have noFrame : control ∉ popCells x.stack 0 := by
    intro member
    have isFrame := popCells_frames x.stack 0 control member
    simp [control, Cell.isFrame] at isFrame
  have noAnswer : control ∉ x.emitted.map Cell.answer := by
    intro member
    obtain ⟨_, _, equal⟩ := List.mem_map.mp member
    simp [control] at equal
  have bound : (encode x).count control ≤ 1 := by
    have frames : ((popCells x.stack 0 : List (Cell W C F A)) : Multiset _).count control = 0 :=
      Multiset.count_eq_zero_of_notMem (fun member => noFrame (Multiset.mem_coe.mp member))
    have answers : ((x.emitted.map (Cell.answer : A → Cell W C F A) : List _) : Multiset _).count control = 0 :=
      Multiset.count_eq_zero_of_notMem (fun member => noAnswer (Multiset.mem_coe.mp member))
    rw [encode, Multiset.count_cons_of_ne (by simp [control]), Multiset.count_cons, Multiset.count_add,
      frames, answers]
    split <;> decide
  change left.1 = control at leftLabel
  change right.1 = control at rightLabel
  rw [← represented.2, labels_split S.present leftLive, labels_split _ rightStill,
    leftLabel, rightLabel, Multiset.count_cons_self, Multiset.count_cons_self] at bound
  omega

/-- Lift a specified, unpadded footprint for a world-preserving move,
with its concrete occurrence choices and non-reused output IDs. -/
theorem reading_allocated {S : Store W C F A} (history : Finset (Cell W C F A × ℕ)) (covered : S.present ⊆ history)
    {w : W} {c c' : C} {pop push base : List F} {emitted : List A}
    (represented : Represents S ⟨w, c, pop ++ base, emitted⟩) :
    let rule := readingRule w c pop c' push base.length (A := A)
    ∃ selection : Selection (Cell W C F A × ℕ),
      selection.Valid (groundAction (Cell W C F A)) Prod.fst rule S ∧
      Disjoint selection.made.toFinset history ∧
      Represents (selection.result Prod.fst rule S) ⟨w, c', push ++ base, emitted⟩ := by
  dsimp only
  obtain ⟨knowledge, labels₀⟩ := represented
  obtain ⟨selection, valid, fresh, known, moved⟩ :=
    fire_of_le_allocated S (readingRule w c pop c' push base.length) history covered rfl rfl knowledge (by
      rw [labels₀, encode_split]
      simp only [readingRule, List.singleton_append, ← Multiset.cons_coe]
      rw [Multiset.add_cons]
      exact (Multiset.cons_le_cons_iff _).mpr (Multiset.le_add_right _ _))
  refine ⟨selection, valid, fresh, known, ?_⟩
  rw [moved, labels₀, encode_split, encode_split]
  simp only [readingRule]
  rw [add_tsub_cancel_left]
  exact add_comm _ _

/-- The same allocation boundary for a transition that changes the
shared world, with the actually selected world occurrence included. -/
theorem writing_allocated {S : Store W C F A} (history : Finset (Cell W C F A × ℕ)) (covered : S.present ⊆ history)
    {w w' : W} {c c' : C} {pop push base : List F} {emitted : List A}
    (represented : Represents S ⟨w, c, pop ++ base, emitted⟩) :
    let rule := writingRule w c pop w' c' push base.length (A := A)
    ∃ selection : Selection (Cell W C F A × ℕ),
      selection.Valid (groundAction (Cell W C F A)) Prod.fst rule S ∧
      Disjoint selection.made.toFinset history ∧
      Represents (selection.result Prod.fst rule S) ⟨w', c', push ++ base, emitted⟩ := by
  dsimp only
  obtain ⟨knowledge, labels₀⟩ := represented
  obtain ⟨selection, valid, fresh, known, moved⟩ :=
    fire_of_le_allocated S (writingRule w c pop w' c' push base.length) history covered rfl rfl knowledge (by
      rw [labels₀, encode_split_world]
      simp only [writingRule, List.nil_append]
      exact Multiset.le_add_right _ _)
  refine ⟨selection, valid, fresh, known, ?_⟩
  rw [moved, labels₀, encode_split_world, encode_split_world]
  simp only [writingRule]
  rw [add_tsub_cancel_left]
  exact add_comm _ _

open LocatedSubstitution.Authority (Ledger Mark) in
/-- An existing framed-machine firing with its ordered occurrence choices
and the authority marks to install on its actual outputs. Individual
profiles determine the marks; the physical update is shared. -/
structure CustodyFiring (M : FramedMachine W C F A) (S : Store W C F A)
    {Phase : Type} (ledger : Ledger (Cell W C F A × ℕ) Phase) where
  rule : RuleInstance (Cell W C F A)
  member : Rules M rule
  selected : Selection (Cell W C F A × ℕ)
  valid : selected.Valid (groundAction (Cell W C F A)) Prod.fst rule S
  unused : ledger.Fresh selected
  marks : Vector (Mark (Cell W C F A × ℕ) Phase) selected.made.length

namespace CustodyFiring

open LocatedSubstitution.Authority (Ledger Mark)
variable {M : FramedMachine W C F A} {S : Store W C F A}
  {Phase : Type} {ledger : Ledger (Cell W C F A × ℕ) Phase}

def result (firing : CustodyFiring M S ledger) : Store W C F A :=
  firing.selected.result Prod.fst firing.rule S

def after (firing : CustodyFiring M S ledger) : Ledger (Cell W C F A × ℕ) Phase :=
  ledger.advance S.present firing.selected firing.marks

theorem raw_step (firing : CustodyFiring M S ledger) : StoreStep M S firing.result :=
  ⟨firing.rule, firing.member, firing.selected, firing.valid, rfl⟩

theorem covered (firing : CustodyFiring M S ledger) (old : ledger.Covers S.present) :
    firing.after.Covers firing.result.present :=
  Ledger.covers_advance firing.marks old

theorem retained (firing : CustodyFiring M S ledger) {o : Cell W C F A × ℕ}
    (old : o ∈ S.present) (keep : o ∉ firing.selected.taken) :
    o ∈ firing.result.present ∧ firing.after.mark o = ledger.mark o := by
  have live : o ∈ fire S.present (firing.selected.commit (T := Unit)) :=
    mem_fire.mpr (.inl ⟨old, by simpa only [Selection.commit, List.mem_toFinset] using keep⟩)
  have notMade : o ∉ firing.selected.made := fun made =>
    Finset.disjoint_left.mp firing.valid.occurrences.fresh (List.mem_toFinset.mpr made) old
  exact ⟨live, Ledger.mark_retained _ _ live notMade⟩

theorem retired (firing : CustodyFiring M S ledger) {o : Cell W C F A × ℕ}
    (taken : o ∈ firing.selected.taken) : o ∉ firing.result.present := by
  intro present
  have chosen : o ∈ firing.selected.taken.toFinset := List.mem_toFinset.mpr taken
  rcases mem_fire.mp present with ⟨_, remained⟩ | made
  · exact remained chosen
  · exact Finset.disjoint_left.mp firing.valid.occurrences.fresh made
      (firing.valid.occurrences.taken_subset chosen)

theorem installed (firing : CustodyFiring M S ledger)
    {o : Cell W C F A × ℕ} {mark : Mark (Cell W C F A × ℕ) Phase}
    (chosen : (o, mark) ∈ firing.selected.made.zip firing.marks.toList) :
    firing.after.mark o = some mark :=
  Ledger.mark_installed _ _ _ firing.valid.output_distinct chosen

theorem retained_below (firing : CustodyFiring M S ledger) (base : ℕ)
    (consumesAbove : ∀ depth frame, Cell.frame depth frame ∈ firing.rule.take → base ≤ depth)
    {occ : Cell W C F A × ℕ} {depth : ℕ} {frame : F}
    (present : occ ∈ S.present) (atFrame : occ.1 = .frame depth frame) (below : depth < base) :
    occ ∈ firing.result.present ∧ firing.after.mark occ = ledger.mark occ := by
  apply firing.retained present
  intro taken
  have labelTaken := List.mem_map_of_mem (f := Prod.fst) taken
  rw [taken_labels firing.valid, atFrame] at labelTaken
  exact (Nat.not_le_of_gt below) (consumesAbove _ _ labelTaken)

end CustodyFiring

open LocatedSubstitution.Authority (Ledger Mark) in
abbrev CustodyStore (W C F A Phase : Type) :=
  Store W C F A × Ledger (Cell W C F A × ℕ) Phase

/-- The physical slots strictly below a cut keep both identity and mark. -/
def RetainsLowerFrames {Phase : Type} (cut : ℕ) (before after : CustodyStore W C F A Phase) : Prop :=
  ∀ {occ : Cell W C F A × ℕ} {depth : ℕ} {frame : F}, occ ∈ before.1.present →
    occ.1 = .frame depth frame → depth < cut →
    occ ∈ after.1.present ∧ after.2.mark occ = before.2.mark occ

namespace RetainsLowerFrames

variable {Phase : Type} {cut upper : ℕ} {before middle after : CustodyStore W C F A Phase}

theorem refl (cut : ℕ) (store : CustodyStore W C F A Phase) : RetainsLowerFrames cut store store :=
  fun live _ _ => ⟨live, rfl⟩

theorem trans (first : RetainsLowerFrames cut before middle) (later : RetainsLowerFrames cut middle after) :
    RetainsLowerFrames cut before after := by
  intro occ depth frame live slot below
  obtain ⟨seen, same⟩ := first live slot below
  obtain ⟨still, mark⟩ := later seen slot below
  exact ⟨still, mark.trans same⟩

theorem mono (kept : RetainsLowerFrames upper before after) (within : cut ≤ upper) :
    RetainsLowerFrames cut before after :=
  fun live slot below => kept live slot (below.trans_le within)

end RetainsLowerFrames

open LocatedSubstitution.Authority (Ledger) in
theorem CustodyFiring.keeps_lower_frames {M : FramedMachine W C F A} {Phase : Type}
    {S : Store W C F A} {ledger : Ledger (Cell W C F A × ℕ) Phase}
    (firing : CustodyFiring M S ledger) (cut : ℕ)
    (above : ∀ depth frame, Cell.frame depth frame ∈ firing.rule.take → cut ≤ depth) :
    RetainsLowerFrames cut (S, ledger) (firing.result, firing.after) :=
  fun live slot below => firing.retained_below cut above live slot below

/-- A recorded authority update over an actual framed firing. Profile
proofs constrain which marks are passed to this common update. -/
def CustodyStep (M : FramedMachine W C F A) {Phase : Type}
    (before after : CustodyStore W C F A Phase) : Prop :=
  ∃ firing : CustodyFiring M before.1 before.2, after = (firing.result, firing.after)

theorem CustodyStep.raw {M : FramedMachine W C F A} {Phase : Type}
    {before after : CustodyStore W C F A Phase} (move : CustodyStep M before after) :
    StoreStep M before.1 after.1 := by
  obtain ⟨firing, rfl⟩ := move
  exact firing.raw_step

theorem CustodyStep.raw_path {M : FramedMachine W C F A} {Phase : Type}
    {before after : CustodyStore W C F A Phase}
    (path : Relation.ReflTransGen (CustodyStep M) before after) :
    Relation.ReflTransGen (StoreStep M) before.1 after.1 := by
  induction path with
  | refl => exact .refl
  | tail _ move ih => exact ih.tail move.raw

open LocatedSubstitution.Authority (Ledger) in
/-- An issued identity can only survive unchanged or disappear.
Retirement is irreversible even if a later output has the same label. -/
theorem custody_path_issued {M : FramedMachine W C F A} {Phase : Type}
    {before after : CustodyStore W C F A Phase}
    (path : Relation.ReflTransGen (CustodyStep M) before after) :
    before.2.issued ⊆ after.2.issued ∧
    ∀ o ∈ before.2.issued, o ∈ after.1.present →
      o ∈ before.1.present ∧ after.2.mark o = before.2.mark o := by
  induction path with
  | refl => exact ⟨fun _ member => member, fun _ _ live => ⟨live, rfl⟩⟩
  | tail _ move ih =>
    obtain ⟨firing, rfl⟩ := move
    refine ⟨ih.1.trans (Ledger.issued_mono _ _ _ _), fun o issued live => ?_⟩
    have notMade (made : o ∈ firing.selected.made) : False :=
      Ledger.fresh_not_issued firing.unused made (ih.1 issued)
    rcases mem_fire.mp live with ⟨old, _⟩ | made
    · obtain ⟨initial, same⟩ := ih.2 o issued old
      exact ⟨initial, (Ledger.mark_retained _ _ live notMade).trans same⟩
    · exact (notMade (List.mem_toFinset.mp made)).elim

theorem custody_path_no_reissue {M : FramedMachine W C F A} {Phase : Type}
    {before after : CustodyStore W C F A Phase}
    (path : Relation.ReflTransGen (CustodyStep M) before after) :
    before.2.issued ⊆ after.2.issued ∧
    ∀ o ∈ before.2.issued, o ∉ before.1.present → o ∉ after.1.present :=
  let history := custody_path_issued path
  ⟨history.1, fun o issued gone live => gone (history.2 o issued live).1⟩

/-- Endpoint retention is also retention at every intermediate cut of
the recorded path. A lower frame cannot disappear and be restored under
its old key during the body. -/
theorem RetainsLowerFrames.at_prefix {M : FramedMachine W C F A} {Phase : Type} {cut : ℕ}
    {before middle after : CustodyStore W C F A Phase}
    (covered : before.2.Covers before.1.present) (kept : RetainsLowerFrames cut before after)
    (initial : Relation.ReflTransGen (CustodyStep M) before middle)
    (remaining : Relation.ReflTransGen (CustodyStep M) middle after) :
    RetainsLowerFrames cut before middle := by
  intro occ depth frame live slot below
  have issued := covered.1 live
  have beforeEnd := custody_path_issued initial
  have atMiddle := (custody_path_issued remaining).2 occ (beforeEnd.1 issued) (kept live slot below).1
  exact ⟨atMiddle.1, (beforeEnd.2 occ issued atMiddle.1).2⟩

section ProtectedFrames

open LocatedSubstitution.Authority (Ledger Mark)

variable {M : FramedMachine W C F A} {Phase : Type}
  {S : Store W C F A} {ledger : Ledger (Cell W C F A × ℕ) Phase}

/-- A move with no stack operations replaces exactly its active control
while leaving all stack slots alone. The supplied next mark is installed
on the actual replacement control, even when the world changes. -/
theorem advance_control {w w' : W} {c c' : C} {stack : List F} {emitted : List A}
    (move : M.Framed w c [] w' c' []) (represented : Represents S ⟨w, c, stack, emitted⟩)
    (covered : ledger.Covers S.present) {old : Cell W C F A × ℕ}
    {mark : Mark (Cell W C F A × ℕ) Phase}
    (marked : ledger.mark old = some mark) (active : old.1 = .control c stack.length)
    (nextMark : Mark (Cell W C F A × ℕ) Phase) :
    ∃ (firing : CustodyFiring M S ledger) (next : Cell W C F A × ℕ),
      old ∈ firing.selected.taken ∧ next.1 = .control c' stack.length ∧
      firing.after.mark next = some nextMark ∧
      Represents firing.result ⟨w', c', stack, emitted⟩ ∧
      RetainsLowerFrames stack.length (S, ledger) (firing.result, firing.after) := by
  have present : old ∈ S.present := (covered.2 _).mpr (by rw [marked]; rfl)
  by_cases equal : w' = w
  · subst w'
    obtain ⟨selected, valid, unused, reaches⟩ :=
      reading_allocated (c' := c') (pop := []) (push := []) (base := stack)
        ledger.issued covered.1 represented
    rcases selected with ⟨taken, read, made⟩
    have oneTaken : taken.length = 1 := valid.take_length.symm
    have oneMade : made.length = 1 := by
      simpa [readingRule, popCells] using congrArg List.length valid.outputs
    obtain ⟨chosen, rfl⟩ := List.length_eq_one_iff.mp oneTaken
    obtain ⟨next, rfl⟩ := List.length_eq_one_iff.mp oneMade
    have atChosen : chosen.1 = .control c stack.length := by
      simpa [readingRule, popCells] using taken_labels valid
    have chosenLive := valid.occurrences.taken_subset (by simp [Selection.commit] : chosen ∈
      ((Selection.mk [chosen] read [next]).commit (T := Unit)).taken)
    have same := same_control_occurrence represented chosenLive present atChosen active
    subst chosen
    let firing : CustodyFiring M S ledger :=
      ⟨_, .reading stack.length move, ⟨[old], read, [next]⟩, valid, unused, #v[nextMark]⟩
    refine ⟨firing, next, List.mem_cons_self, by simpa [readingRule, popCells] using valid.outputs,
      firing.installed List.mem_cons_self, reaches, firing.keeps_lower_frames _ ?_⟩
    intro depth frame member
    simp [firing, readingRule, popCells] at member
  · obtain ⟨selected, valid, unused, reaches⟩ :=
      writing_allocated (w' := w') (c' := c') (pop := []) (push := []) (base := stack)
        ledger.issued covered.1 represented
    rcases selected with ⟨taken, read, made⟩
    have twoTaken : taken.length = 2 := valid.take_length.symm
    have twoMade : made.length = 2 := by
      simpa [writingRule, popCells] using congrArg List.length valid.outputs
    obtain ⟨currentWorld, chosen, rfl⟩ := List.length_eq_two.mp twoTaken
    obtain ⟨nextWorld, next, rfl⟩ := List.length_eq_two.mp twoMade
    have labelsTaken : [currentWorld.1, chosen.1] = [.world w, .control c stack.length] := by
      simpa [writingRule, popCells] using taken_labels valid
    have chosenLive := valid.occurrences.taken_subset (by simp [Selection.commit] : chosen ∈
      ((Selection.mk [currentWorld, chosen] read [nextWorld, next]).commit (T := Unit)).taken)
    have same := same_control_occurrence represented chosenLive present
      (List.cons.inj (List.cons.inj labelsTaken).2).1 active
    subst chosen
    let firing : CustodyFiring M S ledger :=
      ⟨_, .writing stack.length equal move, ⟨[currentWorld, old], read, [nextWorld, next]⟩,
        valid, unused, #v[.cell none, nextMark]⟩
    have labelsMade : [nextWorld.1, next.1] = [.world w', .control c' stack.length] := by
      simpa [writingRule, popCells] using valid.outputs
    refine ⟨firing, next, List.mem_cons_of_mem _ List.mem_cons_self,
      (List.cons.inj (List.cons.inj labelsMade).2).1,
      firing.installed (List.mem_cons_of_mem _ List.mem_cons_self), reaches,
      firing.keeps_lower_frames _ ?_⟩
    intro depth frame member
    simp [firing, writingRule, popCells] at member

/-- Execute an internal body with a lower stack attached. The chosen
footprint is the body's own pop/push witness. It cannot consume an
attached frame, even through a shared-world write. -/
theorem internal_beneath (locality : M.Local)
    {w w' : W} {c c' : C} {inner inner' : List F} {outer : List F} {emitted : List A}
    (move : M.transition w (c, inner) w' (c', inner'))
    (represented : Represents S ⟨w, c, inner ++ outer, emitted⟩)
    (covered : ledger.Covers S.present) :
    ∃ firing : CustodyFiring M S ledger,
      Represents firing.result ⟨w', c', inner' ++ outer, emitted⟩ ∧
      RetainsLowerFrames outer.length (S, ledger) (firing.result, firing.after) := by
  obtain ⟨pop, push, base, rfl, rfl, framed⟩ := locality move
  have atBody : Represents S ⟨w, c, pop ++ (base ++ outer), emitted⟩ := by
    simpa only [List.append_assoc] using represented
  by_cases equal : w' = w
  · subst w'
    obtain ⟨selected, valid, unused, reached⟩ :=
      reading_allocated (c' := c') (push := push) ledger.issued covered.1 atBody
    let firing : CustodyFiring M S ledger :=
      ⟨_, .reading (base ++ outer).length framed, selected, valid, unused,
        Vector.replicate selected.made.length (.cell none)⟩
    refine ⟨firing, by simpa only [firing, CustodyFiring.result, List.append_assoc] using reached,
      RetainsLowerFrames.mono (firing.keeps_lower_frames (base ++ outer).length ?_)
        (by simp [List.length_append])⟩
    intro index value member
    change Cell.frame index value ∈ (readingRule w c pop c' push (base ++ outer).length (A := A)).take at member
    simp only [readingRule, List.mem_cons] at member
    rcases member with impossible | frameTaken
    · cases impossible
    · exact popCells_depth_ge frameTaken
  · obtain ⟨selected, valid, unused, reached⟩ :=
      writing_allocated (w' := w') (c' := c') (push := push) ledger.issued covered.1 atBody
    let firing : CustodyFiring M S ledger :=
      ⟨_, .writing (base ++ outer).length equal framed, selected, valid, unused,
        Vector.replicate selected.made.length (.cell none)⟩
    refine ⟨firing, by simpa only [firing, CustodyFiring.result, List.append_assoc] using reached,
      RetainsLowerFrames.mono (firing.keeps_lower_frames (base ++ outer).length ?_)
        (by simp [List.length_append])⟩
    intro index value member
    change Cell.frame index value ∈ (writingRule w c pop w' c' push (base ++ outer).length (A := A)).take at member
    simp only [writingRule, List.mem_cons] at member
    rcases member with impossible | impossible | frameTaken
    · cases impossible
    · cases impossible
    · exact popCells_depth_ge frameTaken

/-- A whole actual body path under an attached scope keeps every lower
frame and its authority. The body need not reconstruct the attached scope. -/
theorem internal_path_beneath (locality : M.Local)
    {source target : W × (C × List F)} {outer : List F} {emitted : List A}
    (path : Relation.ReflTransGen (fun s t : W × (C × List F) => M.transition s.1 s.2 t.1 t.2) source target)
    (represented : Represents S ⟨source.1, source.2.1, source.2.2 ++ outer, emitted⟩)
    (covered : ledger.Covers S.present) :
    ∃ after : CustodyStore W C F A Phase,
      Relation.ReflTransGen (CustodyStep M) (S, ledger) after ∧
      Represents after.1 ⟨target.1, target.2.1, target.2.2 ++ outer, emitted⟩ ∧
      after.2.Covers after.1.present ∧ RetainsLowerFrames outer.length (S, ledger) after := by
  induction path with
  | refl => exact ⟨(S, ledger), .refl, represented, covered, RetainsLowerFrames.refl _ _⟩
  | tail _ move ih =>
    obtain ⟨middle, paid, middleRep, middleCover, retains⟩ := ih
    obtain ⟨firing, reaches, keeps⟩ := internal_beneath locality move middleRep middleCover
    exact ⟨(firing.result, firing.after), paid.tail ⟨firing, rfl⟩, reaches, firing.covered middleCover,
      RetainsLowerFrames.trans retains keeps⟩

end ProtectedFrames

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

/-- Encoding preserves world, control and stack exactly. Only the separately
published answer list is intentionally observed as a bag. -/
theorem encode_eq_iff (first second : Config W C F A) :
    encode first = encode second ↔
      first.world = second.world ∧ first.control = second.control ∧
        first.stack = second.stack ∧ (first.emitted : Multiset A) = second.emitted := by
  constructor
  · intro same
    have worlds := congrArg worldsOf same
    have world : first.world = second.world := by
      simpa only [worldsOf_encode, Multiset.singleton_inj] using worlds
    have control : first.control = second.control := by
      apply (control_mem_encode (x := second) (c := first.control) (n := first.stack.length) ?_).1
      rw [← same]
      exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self ..)
    have frames := congrArg (Multiset.filter (fun cell => cell.isFrame = true)) same
    have stack : first.stack = second.stack :=
      popCells_bag_injective 0 (by simpa only [frames_encode] using frames)
    have emitted := congrArg answersOf same
    exact ⟨world, control, stack, by simpa only [answersOf_encode] using emitted⟩
  · rintro ⟨world, control, stack, emitted⟩
    simp only [encode, world, control, stack, ← Multiset.map_coe, emitted]

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

/-! ## Firing paths, publication order and progress -/

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
observes machine moves arbitrarily far along it (productivity of observations in the sense of
`Mettapedia.Machines.ProgressObservation`, through its potential criterion: nothing is erased). This holds by construction of the observation: every firing of a
framed machine is labelled with its rule, so no firing is silent. It is a sanity property of the
encoding, not a dynamic result about HE. -/
theorem nonZeno (M : FramedMachine W C F A) :
    Mettapedia.Machines.ProgressObservation.NonZeno (fired M) :=
  Mettapedia.Machines.ProgressObservation.nonZeno_of_rank (fired M) (fun _ => 0)
    (fun event erased => by simp [fired] at erased)

variable {M : FramedMachine W C F A}

/-- The answer packet of a fired rule, rather than an ordering chosen
from its endpoint store. Only a publication rule makes an answer cell. -/
def rulePublication (rule : RuleInstance (Cell W C F A)) : Option A :=
  (rule.produce.filterMap Cell.answer?).head?

theorem Rules.publication_footprint {rule : RuleInstance (Cell W C F A)} (member : Rules M rule) :
    rule.take.filterMap Cell.answer? = [] ∧
      rule.produce.filterMap Cell.answer? = (rulePublication rule).toList := by
  cases member <;>
    simp only [rulePublication, readingRule, writingRule, publishRule, List.filterMap_cons,
      Cell.answer?, answers_popCells] <;> simp

open Mettapedia.Machines.ProgressObservation (Observation observePath)

/-- Reading one publication does not treat an internal world effect
or a frame replacement as publishing an answer. -/
def publication (M : FramedMachine W C F A) : Observation (Fired M) A :=
  fun {before after} event => rulePublication (event : Firing M before after).val

/-- Every observed packet is backed by the actual answer-cell change.
The equation counts repeated occurrences, not only distinct values. -/
theorem firing_answer_delta {S S' : Fired M} (event : S ⟶ S') :
    answersOf (labels Prod.fst S'.present) =
      answersOf (labels Prod.fst S.present) + ((publication M event).toList : Multiset A) := by
  let firing : Firing M S S' := event
  obtain ⟨enough, _, _, moved⟩ := read_firing firing.property.2
  obtain ⟨take, make⟩ := firing.property.1.publication_footprint
  have restored := congrArg answersOf (tsub_add_cancel_of_le enough)
  have unchanged : answersOf (labels Prod.fst S.present - (firing.val.take : Multiset (Cell W C F A))) =
      answersOf (labels Prod.fst S.present) := by
    simpa only [answersOf, Multiset.filterMap_add, Multiset.filterMap_coe,
      take, Multiset.coe_nil, add_zero] using restored
  rw [moved, answersOf, Multiset.filterMap_add, Multiset.filterMap_coe, make]
  change answersOf (labels Prod.fst S.present - (firing.val.take : Multiset (Cell W C F A))) +
    ((publication M event).toList : Multiset A) = _
  rw [unchanged]

private theorem packet_injective {first second : Option A}
    (same : (first.toList : Multiset A) = (second.toList : Multiset A)) : first = second := by
  have ordered := Multiset.coe_eq_coe.mp same
  cases first <;> cases second <;> simp_all

/-- Keeping the sequence of store cuts suffices for this observer:
two legal firings with the same endpoints publish the same packet,
even if their rules or selected occurrences differ. -/
theorem firing_publication_unique {S S' : Fired M} (first second : S ⟶ S') :
    publication M first = publication M second :=
  packet_injective (add_left_cancel ((firing_answer_delta first).symm.trans (firing_answer_delta second)))

/-- Forgetting an ordered word to a bag recovers exactly the
accumulated answer-cell change of the physical path. -/
theorem firing_path_answer_delta {S S' : Fired M} (path : Quiver.Path S S') :
    answersOf (labels Prod.fst S'.present) =
      answersOf (labels Prod.fst S.present) + (observePath (publication M) path : Multiset A) := by
  induction path with
  | nil => simp
  | cons _ event ih =>
    rw [firing_answer_delta event, ih, Mettapedia.Machines.ProgressObservation.observePath_cons,
      ← Multiset.coe_add, add_assoc]

/-- One machine step either keeps the publication list or appends one
answer. It never reorders already published answers. -/
theorem FramedMachine.Step.emitted_packet {x y : Config W C F A} (move : M.Step x y) :
    ∃ next : Option A, y.emitted = x.emitted ++ next.toList := by
  cases move with
  | internal _ => exact ⟨none, by simp⟩
  | publish _ => exact ⟨some _, rfl⟩

/-- The raw lockstep maps preserve the actual answer event in either
direction. The one-result footprint lets the bag delta identify one
list packet without postulating any order on payloads. -/
theorem firing_emits_exact {S S' : Fired M} {x y : Config W C F A}
    (before : Represents S x) (after : Represents S' y) (move : M.Step x y) (event : S ⟶ S') :
    y.emitted = x.emitted ++ (publication M event).toList := by
  have delta := firing_answer_delta event
  rw [before.2, after.2, answersOf_encode, answersOf_encode] at delta
  obtain ⟨packet, emitted⟩ := move.emitted_packet
  have sameBag : (packet.toList : Multiset A) = ((publication M event).toList : Multiset A) := by
    apply add_left_cancel (a := (x.emitted : Multiset A))
    simpa only [emitted, Multiset.coe_add] using delta
  rw [emitted, packet_injective sameBag]

open Mettapedia.GSLT.Ultrainfinite.Route (ObservedTrace)

/-- An observer of the two cuts of a real machine move. The execution
and the decision to erase an observation remain separate. -/
abbrev FramedMachine.CutTrace {Event : Type} (M : FramedMachine W C F A)
    (read : Config W C F A → Config W C F A → List Event) :=
  ObservedTrace (Step := fun x y => PLift (M.Step x y)) (fun {x y} _ => read x y)

theorem FramedMachine.path_has_cutTrace {Event : Type} (read : Config W C F A → Config W C F A → List Event)
    {x y : Config W C F A} (path : Relation.ReflTransGen M.Step x y) : ∃ n word, M.CutTrace read n x y word := by
  induction path with
  | refl => exact ⟨0, [], .refl _⟩
  | tail _ edge ih =>
    obtain ⟨n, word, trace⟩ := ih
    exact ⟨_, _, ObservedTrace.comp _ trace (.cons ⟨edge⟩ (.refl _))⟩

theorem FramedMachine.cutTrace_path {Event : Type} {read : Config W C F A → Config W C F A → List Event}
    {n : ℕ} {x y : Config W C F A} {word : List Event} (trace : M.CutTrace read n x y word) :
    Relation.ReflTransGen M.Step x y := by
  induction trace with
  | refl => exact .refl
  | cons edge _ ih => exact Relation.ReflTransGen.head edge.down ih

/-- Pass an observer through the existing lockstep representation.
Only equality at a single related firing is required; each finite
prefix retains its exact length. -/
theorem firing_path_reads_cuts {Event : Type}
    (read : Config W C F A → Config W C F A → List Event) (observe : Observation (Fired M) Event)
    (agrees : ∀ {S S' : Fired M} {x y : Config W C F A}, Represents S x → Represents S' y →
      M.Step x y → ∀ edge : S ⟶ S', read x y = (observe edge).toList)
    {S S' : Fired M} {x : Config W C F A}
    (represented : Represents S x) (path : Quiver.Path S S') :
    ∃ y, M.CutTrace read path.length x y (observePath observe path) ∧ Represents S' y := by
  induction path with
  | nil => exact ⟨x, .refl _, represented⟩
  | @cons middle final paid event ih =>
    let firing : Firing M middle final := event
    obtain ⟨y, seen, here⟩ := ih
    obtain ⟨z, move, there⟩ := store_to_machine here ⟨firing.val, firing.property⟩
    have single : M.CutTrace read 1 y z (read y z ++ []) := .cons ⟨move⟩ (.refl _)
    rw [agrees here there move event, List.append_nil] at single
    exact ⟨z, ObservedTrace.comp _ seen single, there⟩

theorem cut_trace_fires {Event : Type}
    (read : Config W C F A → Config W C F A → List Event) (observe : Observation (Fired M) Event)
    (agrees : ∀ {S S' : Fired M} {x y : Config W C F A}, Represents S x → Represents S' y →
      M.Step x y → ∀ edge : S ⟶ S', read x y = (observe edge).toList)
    (locality : M.Local) {S : Fired M} {x y : Config W C F A} (represented : Represents S x)
    {n : ℕ} {word : List Event} (trace : M.CutTrace read n x y word) :
    ∃ (final : Fired M) (path : Quiver.Path S final),
      Represents final y ∧ path.length = n ∧ observePath observe path = word := by
  induction trace generalizing S with
  | refl => exact ⟨S, .nil, represented, rfl, rfl⟩
  | cons edge _ ih =>
    obtain ⟨middle, ⟨rule, member, selected⟩, current⟩ := machine_to_store locality represented edge.down
    let next : S ⟶ (show Fired M from middle) := ⟨rule, member, selected⟩
    obtain ⟨final, rest, reached, count, seen⟩ := ih current
    have first := agrees represented current edge.down next
    let one : Quiver.Path S (show Fired M from middle) := Quiver.Path.cons .nil next
    refine ⟨final, one.comp rest, reached, ?_, ?_⟩
    · have oneLength : one.length = 1 := rfl
      rw [Quiver.Path.length_comp, oneLength, count, Nat.add_comm 1]
    · have oneWord : observePath observe one = (observe next).toList := rfl
      rw [Mettapedia.Machines.ProgressObservation.observePath_comp, oneWord, seen, first]

/-- An actual machine edge observes only the suffix it has just
published, not publication history already present at its source. -/
def FramedMachine.answerSuffix (M : FramedMachine W C F A)
    {x y : Config W C F A} (_ : PLift (M.Step x y)) : List A :=
  y.emitted.drop x.emitted.length

abbrev FramedMachine.AnswerTrace (M : FramedMachine W C F A) :=
  ObservedTrace (Step := fun x y => PLift (M.Step x y)) (@M.answerSuffix)

theorem FramedMachine.answerTrace_emitted {n : ℕ} {x y : Config W C F A} {word : List A}
    (path : M.AnswerTrace n x y word) : y.emitted = x.emitted ++ word := by
  induction path with
  | refl => simp
  | cons edge _ ih =>
    obtain ⟨packet, appended⟩ := edge.down.emitted_packet
    simp only [FramedMachine.answerSuffix, appended, List.drop_left, ih, List.append_assoc]

theorem FramedMachine.answerTrace_path {n : ℕ} {x y : Config W C F A} {word : List A}
    (trace : M.AnswerTrace n x y word) : Relation.ReflTransGen M.Step x y :=
  FramedMachine.cutTrace_path trace

theorem FramedMachine.path_has_answerTrace {x y : Config W C F A}
    (path : Relation.ReflTransGen M.Step x y) : ∃ n word, M.AnswerTrace n x y word :=
  M.path_has_cutTrace (fun x y => y.emitted.drop x.emitted.length) path

private theorem answer_cut_agrees {S S' : Fired M} {x y : Config W C F A}
    (before : Represents S x) (after : Represents S' y) (move : M.Step x y) (event : S ⟶ S') :
    y.emitted.drop x.emitted.length = (publication M event).toList := by
  rw [firing_emits_exact before after move event, List.drop_left]

/-- Read an independently given physical firing path back one move at a
time, with its exact step count and ordered word of new publications. -/
theorem firing_path_reads_answers {S S' : Fired M} {x : Config W C F A}
    (represented : Represents S x) (path : Quiver.Path S S') :
    ∃ y, M.AnswerTrace path.length x y (observePath (publication M) path) ∧ Represents S' y :=
  firing_path_reads_cuts (fun x y => y.emitted.drop x.emitted.length)
    (publication M) answer_cut_agrees represented path

/-- Any observed source trace lifts to actual physical firings with no
event added, dropped or reordered, including silent steps in the count. -/
theorem answerTrace_fires (locality : M.Local) {S : Fired M} {x y : Config W C F A}
    (represented : Represents S x) {n : ℕ} {word : List A} (trace : M.AnswerTrace n x y word) :
    ∃ (final : Fired M) (path : Quiver.Path S final),
      Represents final y ∧ path.length = n ∧ observePath (publication M) path = word :=
  cut_trace_fires (fun x y => y.emitted.drop x.emitted.length)
    (publication M) answer_cut_agrees locality represented trace

/-- A store has a readable world only when the world occurrence is
unique. A journal stored inside that world is not an answer cell. -/
def readUniqueWorld (store : Store W C F A) : Option W :=
  match (worldsOf (labels Prod.fst store.present)).toList with
  | [world] => some world
  | _ => none

theorem readUniqueWorld_represents {S : Store W C F A} {x : Config W C F A}
    (represented : Represents S x) : readUniqueWorld S = some x.world := by
  rw [readUniqueWorld, represented.2, worldsOf_encode, Multiset.toList_singleton]

/-- Publish the reached view together with any packet at this same
cut. A genuinely silent cut neither changes the selected view nor
publishes. This does not observe operations invisible to the view. -/
def reportCut {View Packet : Type} [DecidableEq View] (before after : View) (reply : Option Packet) :
    Option (View × Option Packet) :=
  if before = after ∧ reply.isNone then none else some (after, reply)

theorem reportCut_view {View Packet : Type} [DecidableEq View]
    (before after : View) (reply : Option Packet) :
    (reportCut before after reply).toList.foldl (fun _ item => item.1) before = after := by
  cases reply <;> by_cases same : before = after <;> simp [reportCut, same]

theorem reportCut_answers {View Packet : Type} [DecidableEq View]
    (before after : View) (reply : Option Packet) :
    (reportCut before after reply).toList.filterMap Prod.snd = reply.toList := by
  cases reply <;> by_cases same : before = after <;> simp [reportCut, same]

/-- Change the observed view while retaining the ordered packets. Updating
the previous view matters: a change with no packet can become silent
after projection, so merely mapping the event labels is not enough. -/
def coarsenCuts {Fine Coarse Packet : Type} [DecidableEq Coarse] (project : Fine → Coarse) :
    Fine → List (Fine × Option Packet) → List (Coarse × Option Packet)
  | _, [] => []
  | before, (after, packet) :: rest =>
      (reportCut (project before) (project after) packet).toList ++ coarsenCuts project after rest

theorem coarsenCuts_append {Fine Coarse Packet : Type} [DecidableEq Coarse] (project : Fine → Coarse)
    (before : Fine) (first second : List (Fine × Option Packet)) :
    coarsenCuts project before (first ++ second) =
      coarsenCuts project before first ++
        coarsenCuts project (first.foldl (fun _ event => event.1) before) second := by
  induction first generalizing before with
  | nil => rfl
  | cons event first ih =>
    obtain ⟨after, packet⟩ := event
    simp only [List.cons_append, coarsenCuts, List.foldl_cons, ih, List.append_assoc]

theorem coarsenCuts_reportCut_append {Fine Coarse Packet : Type} [DecidableEq Fine] [DecidableEq Coarse]
    (project : Fine → Coarse) (before after : Fine) (packet : Option Packet)
    (rest : List (Fine × Option Packet)) :
    coarsenCuts project before ((reportCut before after packet).toList ++ rest) =
      (reportCut (project before) (project after) packet).toList ++ coarsenCuts project after rest := by
  cases packet <;> by_cases same : before = after <;> simp [reportCut, same, coarsenCuts]

/-- Successive changes of view compose without replaying the execution.
Composition uses the initial view as well as the observed suffix. -/
theorem coarsenCuts_comp {Fine Coarse Small Packet : Type} [DecidableEq Coarse] [DecidableEq Small]
    (first : Fine → Coarse) (second : Coarse → Small) (before : Fine) (word : List (Fine × Option Packet)) :
    coarsenCuts second (first before) (coarsenCuts first before word) =
      coarsenCuts (second ∘ first) before word := by
  induction word generalizing before with
  | nil => rfl
  | cons event rest ih =>
    obtain ⟨after, packet⟩ := event
    simp only [coarsenCuts, coarsenCuts_reportCut_append, Function.comp_apply, ih]

theorem coarsenCuts_answers {Fine Coarse Packet : Type} [DecidableEq Coarse] (project : Fine → Coarse)
    (before : Fine) (word : List (Fine × Option Packet)) :
    (coarsenCuts project before word).filterMap Prod.snd = word.filterMap Prod.snd := by
  induction word generalizing before with
  | nil => rfl
  | cons event rest ih =>
    obtain ⟨after, packet⟩ := event
    rw [coarsenCuts, List.filterMap_append, reportCut_answers, ih]
    cases packet <;> simp

/-- Discarding world data still retains one event per packet, in order
and with multiplicity. An effect-only event does not become a packet. -/
theorem coarsenCuts_unit {Fine Packet : Type} (before : Fine) (word : List (Fine × Option Packet)) :
    coarsenCuts (fun _ => ()) before word =
      (word.filterMap Prod.snd).map (fun packet => ((), some packet)) := by
  induction word generalizing before with
  | nil => rfl
  | cons event rest ih =>
    obtain ⟨after, packet⟩ := event
    cases packet <;> simp [coarsenCuts, reportCut, ih]

def worldPublication {View : Type} [DecidableEq View] (M : FramedMachine W C F A) (view : W → View) :
    Observation (Fired M) (View × Option A) :=
  fun {S S'} event => do
    let before ← readUniqueWorld S
    let after ← readUniqueWorld S'
    reportCut (view before) (view after) (publication M event)

def FramedMachine.worldCut {View : Type} [DecidableEq View] (view : W → View)
    (x y : Config W C F A) : List (View × Option A) :=
  (reportCut (view x.world) (view y.world) (y.emitted.drop x.emitted.length).head?).toList

theorem world_cut_agrees {View : Type} [DecidableEq View] (view : W → View)
    {S S' : Fired M} {x y : Config W C F A} (before : Represents S x) (after : Represents S' y)
    (move : M.Step x y) (event : S ⟶ S') :
    FramedMachine.worldCut view x y = (worldPublication M view event).toList := by
  unfold FramedMachine.worldCut worldPublication
  rw [readUniqueWorld_represents before, readUniqueWorld_represents after, answer_cut_agrees before after move event]
  cases publication M event <;> rfl

/-- The ordered packet word and the reached world projection are
both recoverable from the joint cut observation. -/
theorem FramedMachine.worldCut_readouts {View : Type} [DecidableEq View] (view : W → View)
    {n : ℕ} {x y : Config W C F A} {word : List (View × Option A)}
    (trace : M.CutTrace (FramedMachine.worldCut view) n x y word) :
    word.foldl (fun _ item => item.1) (view x.world) = view y.world ∧
      y.emitted = x.emitted ++ word.filterMap Prod.snd := by
  induction trace with
  | refl => simp
  | @cons _ before middle _ _ edge _ ih =>
    obtain ⟨packet, appended⟩ := edge.down.emitted_packet
    have report : (middle.emitted.drop before.emitted.length).head? = packet := by
      rw [appended, List.drop_left]
      cases packet <;> rfl
    change (_ ++ _ : List (View × Option A)).foldl (fun _ item => item.1) _ = _ ∧ _
    rw [FramedMachine.worldCut, report, List.foldl_append, reportCut_view, List.filterMap_append, reportCut_answers]
    exact ⟨ih.1, ih.2.trans (by rw [appended, List.append_assoc])⟩

/-- Refine an observer on the existing trace without changing its
endpoints or its number of machine steps. Only its word is projected. -/
theorem FramedMachine.coarsen_worldCut {Fine Coarse : Type} [DecidableEq Fine] [DecidableEq Coarse]
    (view : W → Fine) (project : Fine → Coarse)
    {n : ℕ} {x y : Config W C F A} {word : List (Fine × Option A)}
    (trace : M.CutTrace (FramedMachine.worldCut view) n x y word) :
    M.CutTrace (FramedMachine.worldCut (project ∘ view)) n x y (coarsenCuts project (view x.world) word) := by
  induction trace with
  | refl => exact .refl _
  | cons edge _ ih =>
    rw [FramedMachine.worldCut, coarsenCuts_reportCut_append]
    exact .cons edge ih

/-- Identity on a word of actual cuts. Arbitrary lists may have spurious
stutters; source traces do not. -/
theorem FramedMachine.worldCut_identity {View : Type} [DecidableEq View] (view : W → View)
    {n : ℕ} {x y : Config W C F A} {word : List (View × Option A)}
    (trace : M.CutTrace (FramedMachine.worldCut view) n x y word) :
    coarsenCuts id (view x.world) word = word := by
  induction trace with
  | refl => rfl
  | @cons _ before middle _ _ edge _ ih =>
    simp only [FramedMachine.worldCut, coarsenCuts_reportCut_append, id_eq, ih]

/-- The same independently supplied physical path returns the coarser
word. The source representation supplies readable world occurrences at
each cut, including when the stored payloads are not unique answers. -/
theorem coarsen_worldPublication_path {Fine Coarse : Type} [DecidableEq Fine] [DecidableEq Coarse]
    (view : W → Fine) (project : Fine → Coarse)
    {S S' : Fired M} {x : Config W C F A} (represented : Represents S x) (path : Quiver.Path S S') :
    coarsenCuts project (view x.world) (observePath (worldPublication M view) path) =
      observePath (worldPublication M (project ∘ view)) path := by
  induction path with
  | nil => rfl
  | @cons middle final earlier event ih =>
    obtain ⟨y, trace, current⟩ := firing_path_reads_cuts
      (FramedMachine.worldCut view) (worldPublication M view) (world_cut_agrees view) represented earlier
    let firing : Firing M middle final := event
    obtain ⟨z, _, reached⟩ := store_to_machine current ⟨firing.val, firing.property⟩
    simp only [Mettapedia.Machines.ProgressObservation.observePath_cons, coarsenCuts_append, ih,
      (M.worldCut_readouts view trace).1, worldPublication, readUniqueWorld_represents current,
      readUniqueWorld_represents reached, Function.comp_apply]
    have one := coarsenCuts_reportCut_append project (view y.world) (view z.world) (publication M event) []
    simp only [coarsenCuts, List.append_nil] at one
    exact congrArg (fun tail => observePath (worldPublication M (project ∘ view)) earlier ++ tail) one

/-- Exact observation criterion for representing a completed block by
one endpoint cut. This does not license or construct a fused firing. -/
theorem FramedMachine.worldCut_endpoint_iff {View : Type} [DecidableEq View] (view : W → View)
    {n : ℕ} {x y : Config W C F A} {word : List (View × Option A)}
    (trace : M.CutTrace (FramedMachine.worldCut view) n x y word) :
    word = (reportCut (view x.world) (view y.world) (word.filterMap Prod.snd).head?).toList ↔
      word.length ≤ 1 := by
  constructor
  · intro same
    rw [same]
    cases reportCut (view x.world) (view y.world) (word.filterMap Prod.snd).head? <;> simp
  · intro short
    have reached := (M.worldCut_readouts view trace).1
    have normalized := M.worldCut_identity view trace
    cases word with
    | nil =>
      simp only [List.foldl_nil] at reached
      simp [reportCut, reached]
    | cons event rest =>
      have last : rest = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at short; omega)
      subst rest
      obtain ⟨after, packet⟩ := event
      simp only [List.foldl_cons, List.foldl_nil] at reached
      rw [← reached]
      cases packet <;> simpa [coarsenCuts] using normalized.symm

/-- The given start history and a supplied physical path determine a
unique source endpoint, even when that endpoint alone loses order. -/
theorem firing_path_endpoint_unique {S S' : Fired M} {x y z : Config W C F A}
    (path : Quiver.Path S S') (left : Represents S' y) (right : Represents S' z)
    (first : M.AnswerTrace path.length x y (observePath (publication M) path))
    (second : M.AnswerTrace path.length x z (observePath (publication M) path)) : y = z := by
  obtain ⟨world, control, stack, _⟩ := (encode_eq_iff y z).mp (left.2.symm.trans right.2)
  have emitted := (FramedMachine.answerTrace_emitted first).trans (FramedMachine.answerTrace_emitted second).symm
  cases y
  cases z
  simp_all

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

/-- Frame depths retain stack order despite the bag-valued physical store. -/
theorem stack_order_is_retained :
    encode (⟨(), (), [true, false], []⟩ : Config Unit Unit Bool Empty) ≠
      encode ⟨(), (), [false, true], []⟩ := by
  intro same
  have order := ((encode_eq_iff _ _).1 same).2.2.1
  exact (by decide : [true, false] ≠ [false, true]) order

/-- The generic publication observer is only a bag; full list injectivity
would be false. Streaming keeps its ordered answers in the world instead. -/
theorem published_order_is_not_retained :
    encode (⟨(), (), [], [true, false]⟩ : Config Unit Unit Empty Bool) =
      encode ⟨(), (), [], [false, true]⟩ := by
  apply (encode_eq_iff _ _).2
  exact ⟨rfl, rfl, rfl, by decide⟩

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
