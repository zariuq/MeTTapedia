import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionCompleteness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchOutcome

/-!
# Derivations, fairness, and the given-clause loop

## Derivations (Bachmair–Ganzinger)

A **derivation** (`Derivation`) is a sequence of ground clause sets in which every new clause follows
from the previous set and every removed clause is redundant with respect to the next set. Its
**limit** (`limit`) is the set of persistent clauses. It is **fair** (`Fair`) when every inference
from persistent clauses is redundant with respect to some set of the derivation.

* **The redundancy criterion is stable under removing redundant clauses**
  (`redundant_diff`, `redundantInference_diff`), by well-founded induction on the clause ordering.
* **Soundness of derived clauses** (`Derivation.entails`): every clause of every set follows from the
  initial set.
* **Removed clauses stay redundant** (`removed_redundant`) and the persistent clauses entail every
  clause that ever appeared (`limit_models`).
* **Fair derivations reach saturation** (`Derivation.saturated`): the limit is saturated.
* **Refutational completeness relative to fairness and saturation** (`Derivation.complete`): if the
  initial set is unsatisfiable, the empty clause appears in some set.

## The given-clause loop

The loop keeps an **active** list and a **passive** queue (`Loop`). Each step takes the head of the
passive queue as the given clause, moves it to the active list, and appends to the queue every
conclusion its generator produces from the given clause and the active clauses (`Loop.step`). A
generator is **complete** (`Generator.Complete`) when it produces the conclusion of every inference
whose premises are among the given and active clauses and include the given clause, and **sound**
when it produces only consequences.

* The loop's sets form a derivation (`Loop.derivation`).
* **First-in first-out selection is fair** (`Loop.selected`, `Loop.fair`): a clause at position `k`
  of the queue is the given clause `k` steps later, so every persistent premise is eventually active
  and every inference among persistent clauses is eventually performed.
* Hence **the loop is refutationally complete** (`Loop.complete`).

## The readout in the outcome algebra

A finite saturation run reads as a search outcome (`readout`): its answer is the empty clause, if
derived, and its status is finished only when the final set is saturated.

* **Commit** means the initial set is unsatisfiable (`readout_commit`).
* **Refuted** means it is satisfiable, by refutational completeness (`readout_refuted`); this
  "no proof exists" answer is sound only because of the completeness theorem.
* **Suspended** claims nothing; a cut-off run never reads refuted (`readout_cutOff`).

Only the outcome algebra and its verdicts are taken from the bounded-search modules; the soundness
of each reading is proved here from this calculus's own theorems, not transferred from the search
policies' results.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition

open Mettapedia.Logic.LP

variable {sig : LPSignature} [LinearOrder (GroundTerm sig)]

/-! ## The redundancy criterion -/

section Criterion

variable {N N' : Set (Clause (GroundTerm sig))}

theorem lowerSet_mono (sub : N ⊆ N') (C : Clause (GroundTerm sig)) : lowerSet N C ⊆ lowerSet N' C :=
  fun _ member => ⟨sub member.1, member.2⟩

theorem Redundant.mono (sub : N ⊆ N') {C : Clause (GroundTerm sig)} (redundant : Redundant N C) :
    Redundant N' C :=
  Entails.mono (lowerSet_mono sub C) redundant

theorem RedundantInference.mono (sub : N ⊆ N') {main concl : Clause (GroundTerm sig)}
    (redundant : RedundantInference N main concl) : RedundantInference N' main concl :=
  Entails.mono (lowerSet_mono sub main) redundant

/-- The clauses of `N` that are not redundant with respect to `N`. -/
def irredundant (N : Set (Clause (GroundTerm sig))) : Set (Clause (GroundTerm sig)) :=
  {C | C ∈ N ∧ ¬ Redundant N C}

/-- **A model of the irredundant clauses below `C` is a model of all clauses below `C`.** -/
theorem models_lower_of_irredundant [WellFoundedLT (GroundTerm sig)] (I : Congruence sig) (C : Clause (GroundTerm sig))
    (holds : ∀ D ∈ lowerSet (irredundant N) C, Models I.rel D) : ∀ D ∈ lowerSet N C, Models I.rel D := by
  intro D member
  refine clauseLT_wf.induction (C := fun D => D ∈ N → ClauseLT D C → Models I.rel D) D
    (fun D ih inN lt => ?_) member.1 member.2
  by_cases redundant : Redundant N D
  · exact redundant I fun E ⟨inE, ltE⟩ => ih E ltE inE (clauseLT_trans ltE lt)
  · exact holds D ⟨⟨inN, redundant⟩, lt⟩

/-- **Removing redundant clauses keeps redundancy.** -/
theorem redundant_diff [WellFoundedLT (GroundTerm sig)] {C : Clause (GroundTerm sig)} (redundant : Redundant N C) :
    Redundant (irredundant N) C :=
  fun I holds => redundant I (models_lower_of_irredundant I C holds)

theorem redundantInference_diff [WellFoundedLT (GroundTerm sig)] {main concl : Clause (GroundTerm sig)}
    (redundant : RedundantInference N main concl) : RedundantInference (irredundant N) main concl :=
  fun I holds => redundant I (models_lower_of_irredundant I main holds)

end Criterion

/-! ## Derivations -/

section Derivations

/-- **A derivation**: every new clause follows from the previous set, and every removed clause is
redundant with respect to the next set. -/
structure Derivation (N : ℕ → Set (Clause (GroundTerm sig))) : Prop where
  sound : ∀ i, ∀ C ∈ N (i + 1), C ∉ N i → Entails (N i) C
  removes : ∀ i, ∀ C ∈ N i, C ∉ N (i + 1) → Redundant (N (i + 1)) C

/-- The clauses of some set. -/
def union (N : ℕ → Set (Clause (GroundTerm sig))) : Set (Clause (GroundTerm sig)) := {C | ∃ i, C ∈ N i}

/-- **The limit**: the persistent clauses. -/
def limit (N : ℕ → Set (Clause (GroundTerm sig))) : Set (Clause (GroundTerm sig)) :=
  {C | ∃ i, ∀ j, i ≤ j → C ∈ N j}

/-- **Fairness**: every inference from persistent clauses is redundant with respect to some set. -/
def Fair (N : ℕ → Set (Clause (GroundTerm sig))) : Prop :=
  ∀ side main concl, Inference side main concl → (∀ D ∈ side, D ∈ limit N) → main ∈ limit N →
    ∃ i, RedundantInference (N i) main concl

variable {N : ℕ → Set (Clause (GroundTerm sig))}

theorem limit_subset_union : limit N ⊆ union N := fun _ ⟨i, persistent⟩ => ⟨i, persistent i le_rfl⟩

theorem subset_union (i : ℕ) : N i ⊆ union N := fun _ member => ⟨i, member⟩

/-- **Soundness of derived clauses**: every model of the initial set models every set. -/
theorem Derivation.models (derivation : Derivation N) (I : Congruence sig)
    (initial : ∀ C ∈ N 0, Models I.rel C) : ∀ i, ∀ C ∈ N i, Models I.rel C
  | 0 => initial
  | i + 1 => fun C member => by
      by_cases old : C ∈ N i
      · exact derivation.models I initial i C old
      · exact derivation.sound i C member old I (derivation.models I initial i)

/-- Every derived clause follows from the initial set. -/
theorem Derivation.entails (derivation : Derivation N) (i : ℕ) {C : Clause (GroundTerm sig)}
    (member : C ∈ N i) : Entails (N 0) C :=
  fun I initial => derivation.models I initial i C member

/-- Every model of a later set models the earlier ones. -/
theorem Derivation.models_back (derivation : Derivation N) (I : Congruence sig) :
    ∀ i, (∀ C ∈ N i, Models I.rel C) → ∀ C ∈ N 0, Models I.rel C
  | 0, holds => holds
  | i + 1, holds => derivation.models_back I i fun C member => by
      by_cases kept : C ∈ N (i + 1)
      · exact holds C kept
      · exact derivation.removes i C member kept I fun D lower => holds D lower.1

/-- **A clause that appears and does not persist is redundant** with respect to the union. -/
theorem removed_redundant (derivation : Derivation N) {C : Clause (GroundTerm sig)}
    (appears : C ∈ union N) (transient : C ∉ limit N) : Redundant (union N) C := by
  classical
  obtain ⟨i, member⟩ := appears
  have leaves : ∃ k, C ∉ N (i + k) := by
    by_contra stays
    push Not at stays
    exact transient ⟨i, fun j le => by simpa [Nat.add_sub_cancel' le] using stays (j - i)⟩
  let k := Nat.find leaves
  have outside : C ∉ N (i + k) := Nat.find_spec leaves
  have positive : k ≠ 0 := fun zero => outside (by rw [zero, Nat.add_zero]; exact member)
  obtain ⟨k', hk⟩ := Nat.exists_eq_succ_of_ne_zero positive
  have inside : C ∈ N (i + k') := by
    by_contra out
    exact Nat.find_min leaves (show k' < k by omega) out
  rw [hk] at outside
  have removal := derivation.removes (i + k') C inside outside
  exact removal.mono (subset_union _)

/-- The irredundant clauses of the union persist. -/
theorem irredundant_union_subset_limit (derivation : Derivation N) : irredundant (union N) ⊆ limit N := by
  intro C ⟨appears, notRedundant⟩
  by_contra transient
  exact notRedundant (removed_redundant derivation appears transient)

/-- Redundancy with respect to the union is redundancy with respect to the limit. -/
theorem Derivation.redundant_limit [WellFoundedLT (GroundTerm sig)] (derivation : Derivation N) {C : Clause (GroundTerm sig)}
    (redundant : Redundant (union N) C) : Redundant (limit N) C :=
  (redundant_diff redundant).mono (irredundant_union_subset_limit derivation)

theorem Derivation.redundantInference_limit [WellFoundedLT (GroundTerm sig)] (derivation : Derivation N) {main concl : Clause (GroundTerm sig)}
    (redundant : RedundantInference (union N) main concl) : RedundantInference (limit N) main concl :=
  (redundantInference_diff redundant).mono (irredundant_union_subset_limit derivation)

/-- **The persistent clauses entail every clause that ever appeared.** -/
theorem limit_models [WellFoundedLT (GroundTerm sig)] (derivation : Derivation N) (I : Congruence sig)
    (holds : ∀ C ∈ limit N, Models I.rel C) : ∀ C ∈ union N, Models I.rel C := by
  intro C appears
  by_cases persistent : C ∈ limit N
  · exact holds C persistent
  · exact derivation.redundant_limit (removed_redundant derivation appears persistent) I
      fun D lower => holds D lower.1

/-- **Fair derivations reach saturation.** -/
theorem Derivation.saturated [WellFoundedLT (GroundTerm sig)] (derivation : Derivation N) (fair : Fair N) : Saturated (limit N) := by
  intro side main concl inference sides mainIn
  obtain ⟨i, redundant⟩ := fair side main concl inference sides mainIn
  exact derivation.redundantInference_limit (redundant.mono (subset_union i))

/-- **Refutational completeness relative to fairness and saturation**: a fair derivation from an
unsatisfiable set derives the empty clause. -/
theorem Derivation.complete [WellFoundedLT (GroundTerm sig)] [GroundSimplification sig] (derivation : Derivation N) (fair : Fair N)
    (unsatisfiable : ¬ ∃ I : Congruence sig, ∀ C ∈ N 0, Models I.rel C) : ∃ i, (0 : Clause (GroundTerm sig)) ∈ N i := by
  by_contra never
  push Not at never
  have noEmpty : (0 : Clause (GroundTerm sig)) ∉ limit N := fun ⟨i, persistent⟩ => never i (persistent i le_rfl)
  obtain ⟨I, holds⟩ := satisfiable (derivation.saturated fair) noEmpty
  exact unsatisfiable ⟨I, fun C member => limit_models derivation I holds C ⟨0, member⟩⟩

end Derivations

/-! ## The given-clause loop -/

section Loop

/-- **A generator of conclusions** from a given clause and the active clauses. -/
abbrev Generator (sig : LPSignature) [LinearOrder (GroundTerm sig)] :=
  Clause (GroundTerm sig) → List (Clause (GroundTerm sig)) → List (Clause (GroundTerm sig))

/-- **A complete generator** produces the conclusion of every inference whose premises are among the
given and active clauses and include the given clause. -/
def Generator.Complete (generate : Generator sig) : Prop :=
  ∀ (given : Clause (GroundTerm sig)) (active : List (Clause (GroundTerm sig))) side main concl,
    Inference side main concl → (∀ D ∈ side, D = given ∨ D ∈ active) → (main = given ∨ main ∈ active) →
      (main = given ∨ given ∈ side) → concl ∈ generate given active

/-- **A sound generator** produces only consequences of the given and active clauses. -/
def Generator.Sound (generate : Generator sig) : Prop :=
  ∀ given active, ∀ concl ∈ generate given active, Entails {D | D = given ∨ D ∈ active} concl

/-- **The state of the given-clause loop**: the active clauses and the passive queue. -/
structure Loop (sig : LPSignature) [LinearOrder (GroundTerm sig)] where
  active : List (Clause (GroundTerm sig))
  passive : List (Clause (GroundTerm sig))

namespace Loop

/-- **One step**: the head of the queue is the given clause; it becomes active, and its conclusions
with the active clauses join the end of the queue. -/
def step (generate : Generator sig) (s : Loop sig) : Loop sig :=
  match s.passive with
  | [] => s
  | given :: rest => ⟨given :: s.active, rest ++ generate given s.active⟩

/-- The run of the loop. -/
def run (generate : Generator sig) (s : Loop sig) : ℕ → Loop sig
  | 0 => s
  | i + 1 => step generate (run generate s i)

/-- The clauses of a state. -/
def clauses (s : Loop sig) : Set (Clause (GroundTerm sig)) := {C | C ∈ s.active ∨ C ∈ s.passive}

variable (generate : Generator sig)

theorem active_mono (s : Loop sig) : ∀ C ∈ s.active, C ∈ (step generate s).active := by
  intro C member
  unfold step
  split
  · exact member
  · exact List.mem_cons_of_mem _ member

theorem clauses_mono (s : Loop sig) : clauses s ⊆ clauses (step generate s) := by
  intro C member
  unfold step
  split
  · exact member
  · next given rest same =>
    rcases member with active | passive
    · exact Or.inl (List.mem_cons_of_mem _ active)
    · rw [same] at passive
      rcases List.mem_cons.mp passive with rfl | inRest
      · exact Or.inl List.mem_cons_self
      · exact Or.inr (List.mem_append_left _ inRest)

theorem clauses_run_mono (s : Loop sig) {i j : ℕ} (le : i ≤ j) :
    clauses (run generate s i) ⊆ clauses (run generate s j) := by
  induction le with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (clauses_mono generate _)

/-- **The loop's sets form a derivation** for a sound generator: nothing is removed, and every new
clause follows from the previous set. -/
theorem derivation (sound : Generator.Sound generate) (s : Loop sig) :
    Derivation fun i => clauses (run generate s i) where
  sound i C member old := by
    simp only [run] at member
    revert member old
    unfold step
    split
    · exact fun member old => absurd member old
    · next given rest same =>
      intro member old
      rcases member with active | passive
      · rcases List.mem_cons.mp active with rfl | inActive
        · exact absurd (Or.inr (same ▸ List.mem_cons_self)) old
        · exact absurd (Or.inl inActive) old
      · rcases List.mem_append.mp passive with inRest | generated
        · exact absurd (Or.inr (same ▸ List.mem_cons_of_mem _ inRest)) old
        · refine (sound given _ C generated).mono fun D member => ?_
          rcases member with rfl | inActive
          · exact Or.inr (same ▸ List.mem_cons_self)
          · exact Or.inl inActive
  removes i C member gone := absurd (clauses_mono generate _ member) gone

/-- **First-in first-out**: a clause at position `k` of the queue is the given clause `k` steps later,
and is active from then on. -/
theorem selected (s : Loop sig) : ∀ (k : ℕ) {C : Clause (GroundTerm sig)}, s.passive[k]? = some C →
    C ∈ (run generate s (k + 1)).active
  | 0, C, at_head => by
      obtain ⟨given, rest, same⟩ : ∃ given rest, s.passive = given :: rest := by
        cases h : s.passive with
        | nil => rw [h] at at_head; exact absurd at_head (by simp)
        | cons given rest => exact ⟨given, rest, rfl⟩
      rw [same] at at_head
      simp only [List.getElem?_cons_zero, Option.some.injEq] at at_head
      subst at_head
      show _ ∈ (step generate s).active
      unfold step
      rw [same]
      exact List.mem_cons_self
  | k + 1, C, at_position => by
      obtain ⟨given, rest, same⟩ : ∃ given rest, s.passive = given :: rest := by
        cases h : s.passive with
        | nil => rw [h] at at_position; exact absurd at_position (by simp)
        | cons given rest => exact ⟨given, rest, rfl⟩
      have moved : (step generate s).passive[k]? = some C := by
        unfold step
        rw [same]
        rw [same] at at_position
        simp only [List.getElem?_cons_succ] at at_position
        obtain ⟨bound, -⟩ := List.getElem?_eq_some_iff.mp at_position
        rw [List.getElem?_append_left bound]
        exact at_position
      have later := selected (step generate s) k moved
      have shift : ∀ j, run generate (step generate s) j = run generate s (j + 1) := by
        intro j
        induction j with
        | zero => rfl
        | succ j ih => simp only [run, ih]
      rw [shift] at later
      exact later

theorem active_run_mono (s : Loop sig) {i j : ℕ} (le : i ≤ j) :
    ∀ C ∈ (run generate s i).active, C ∈ (run generate s j).active := by
  induction le with
  | refl => exact fun _ member => member
  | step _ ih => exact fun C member => active_mono generate _ C (ih C member)

/-- Every clause of the loop is eventually active. -/
theorem eventually_active (s : Loop sig) {i : ℕ} {C : Clause (GroundTerm sig)}
    (member : C ∈ clauses (run generate s i)) : ∃ j, C ∈ (run generate s j).active := by
  rcases member with active | passive
  · exact ⟨i, active⟩
  · obtain ⟨k, at_position⟩ := List.mem_iff_getElem?.mp passive
    have shift : ∀ j, run generate (run generate s i) j = run generate s (i + j) := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        show step generate (run generate (run generate s i) j) = run generate s ((i + j) + 1)
        rw [ih]
        rfl
    have := selected generate (run generate s i) k at_position
    rw [shift] at this
    exact ⟨_, this⟩

/-- One step either changes nothing or moves the head of the queue to the active list. -/
theorem step_cases (s : Loop sig) : step generate s = s ∨ ∃ given rest, s.passive = given :: rest ∧
    (step generate s).active = given :: s.active ∧ (step generate s).passive = rest ++ generate given s.active := by
  unfold step
  split
  · exact Or.inl rfl
  · next given rest same => exact Or.inr ⟨given, rest, same, rfl, rfl⟩

/-- **First-in first-out selection is fair** for a complete generator, from an empty active list. -/
theorem fair [GroundSimplification sig] (complete : Generator.Complete generate) (s : Loop sig) (start : s.active = []) :
    Fair fun i => clauses (run generate s i) := by
  classical
  intro side main concl inference sides mainIn
  obtain ⟨i, member⟩ := limit_subset_union mainIn
  obtain ⟨jm, mainActive⟩ := eventually_active generate s member
  let ready : ℕ → Prop := fun j =>
    main ∈ (run generate s j).active ∧ ∀ D ∈ side, D ∈ (run generate s j).active
  have exists_ready : ∃ j, ready j := by
    cases side with
    | none => exact ⟨jm, mainActive, fun D member => by cases member⟩
    | some D =>
        obtain ⟨i', member'⟩ := limit_subset_union (sides D rfl)
        obtain ⟨jd, dActive⟩ := eventually_active generate s member'
        refine ⟨max jm jd, active_run_mono generate s (le_max_left _ _) _ mainActive, fun D' member => ?_⟩
        cases member
        exact active_run_mono generate s (le_max_right _ _) _ dActive
  have readyJ : ready (Nat.find exists_ready) := Nat.find_spec exists_ready
  have positive : Nat.find exists_ready ≠ 0 := by
    intro zero
    have atZero := readyJ.1
    rw [zero] at atZero
    change main ∈ s.active at atZero
    rw [start] at atZero
    exact absurd atZero List.not_mem_nil
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero positive
  have notReady : ¬ ready j := Nat.find_min exists_ready (by omega)
  have readyNext : ready (j + 1) := by
    have h := readyJ
    rw [hj] at h
    exact h
  change main ∈ (step generate (run generate s j)).active ∧
    ∀ D ∈ side, D ∈ (step generate (run generate s j)).active at readyNext
  rcases step_cases generate (run generate s j) with same | ⟨given, rest, -, active, passive⟩
  · rw [same] at readyNext
    exact absurd readyNext notReady
  · rw [active] at readyNext
    have involved : main = given ∨ given ∈ side := by
      by_contra neither
      push Not at neither
      refine notReady ⟨?_, fun D member => ?_⟩
      · rcases List.mem_cons.mp readyNext.1 with same | inActive
        · exact absurd same neither.1
        · exact inActive
      · rcases List.mem_cons.mp (readyNext.2 D member) with same | inActive
        · exact absurd (same ▸ member) neither.2
        · exact inActive
    have produced := complete given (run generate s j).active side main concl inference
      (fun D member => List.mem_cons.mp (readyNext.2 D member))
      (List.mem_cons.mp readyNext.1) involved
    refine ⟨j + 1, RedundantInference.of_mem inference (Or.inr ?_)⟩
    change concl ∈ (step generate (run generate s j)).passive
    rw [passive]
    exact List.mem_append_right _ produced

/-- **The given-clause loop is refutationally complete**: from an unsatisfiable queue and an empty
active list, with a sound and complete generator, it derives the empty clause. -/
theorem complete [WellFoundedLT (GroundTerm sig)] [GroundSimplification sig] (sound : Generator.Sound generate) (complete : Generator.Complete generate)
    (s : Loop sig) (start : s.active = [])
    (unsatisfiable : ¬ ∃ I : Congruence sig, ∀ C ∈ s.passive, Models I.rel C) :
    ∃ i, (0 : Clause (GroundTerm sig)) ∈ clauses (run generate s i) :=
  (derivation generate sound s).complete (fair generate complete s start) fun ⟨I, holds⟩ =>
    unsatisfiable ⟨I, fun C member => holds C (Or.inr member)⟩

end Loop

end Loop

/-! ## The readout of a saturation run in the outcome algebra -/

section Readout

open Search (Outcome Status)

/-- **The readout of a saturation run**: its answer is the empty clause, if derived, and its status
is finished exactly when the run reports saturation. -/
noncomputable def readout (N : Set (Clause (GroundTerm sig))) (finished : Bool) : Outcome Unit := by
  classical
  exact ⟨if (0 : Clause (GroundTerm sig)) ∈ N then {()} else 0, if finished then .finished else .cutOff⟩

/-- A run reports saturation only when its final set is saturated. -/
def Reports (N : Set (Clause (GroundTerm sig))) (finished : Bool) : Prop := finished = true → Saturated N

variable {N : Set (Clause (GroundTerm sig))} {finished : Bool}

theorem readout_answers_ne_zero_iff : (readout N finished).answers ≠ 0 ↔ (0 : Clause (GroundTerm sig)) ∈ N := by
  classical
  unfold readout
  by_cases empty : (0 : Clause (GroundTerm sig)) ∈ N
  · simp [empty]
  · simp [empty]

/-- **Commit**: the empty clause was derived, so the final set, and with it every set the run was
derived from soundly, is unsatisfiable. -/
theorem readout_commit (commit : (readout N finished).verdict = .commit) :
    ¬ ∃ I : Congruence sig, ∀ C ∈ N, Models I.rel C := by
  rintro ⟨I, holds⟩
  have empty := readout_answers_ne_zero_iff.mp ((Outcome.verdict_eq_commit_iff _).mp commit)
  exact not_models_zero I.rel (holds 0 empty)

/-- **Refuted**: the run finished, saturated, without the empty clause; by refutational completeness
the final set is satisfiable. -/
theorem readout_refuted [WellFoundedLT (GroundTerm sig)] [GroundSimplification sig] (reports : Reports N finished) (refuted : (readout N finished).verdict = .refuted) :
    ∃ I : Congruence sig, ∀ C ∈ N, Models I.rel C := by
  classical
  have zero := (Outcome.verdict_eq_refuted_iff _).mp refuted
  have noAnswers : (readout N finished).answers = 0 := by rw [zero]; rfl
  have finishedStatus : (readout N finished).status = .finished := by rw [zero]; rfl
  have noEmpty : (0 : Clause (GroundTerm sig)) ∉ N := fun empty =>
    readout_answers_ne_zero_iff.mpr empty noAnswers
  have saturated : Saturated N := by
    apply reports
    cases finished
    · simp [readout] at finishedStatus
    · rfl
  exact satisfiable saturated noEmpty

/-- **Suspended claims nothing**: a run cut off never reads refuted. -/
theorem readout_cutOff (cut : finished = false) : (readout N finished).verdict ≠ .refuted := by
  classical
  apply Outcome.verdict_ne_refuted_of_cutOff
  simp [readout, cut]

/-- **The readout of a derivation's stage, back to its start**: a refuted readout at any stage of a
derivation makes the initial set satisfiable. -/
theorem Derivation.readout_refuted [WellFoundedLT (GroundTerm sig)] [GroundSimplification sig] {N : ℕ → Set (Clause (GroundTerm sig))} (derivation : Derivation N)
    (i : ℕ) (reports : Reports (N i) finished) (refuted : (readout (N i) finished).verdict = .refuted) :
    ∃ I : Congruence sig, ∀ C ∈ N 0, Models I.rel C := by
  obtain ⟨I, holds⟩ := Superposition.readout_refuted reports refuted
  exact ⟨I, derivation.models_back I i holds⟩

/-- A committed readout at any stage makes the initial set unsatisfiable. -/
theorem Derivation.readout_commit {N : ℕ → Set (Clause (GroundTerm sig))} (derivation : Derivation N)
    (i : ℕ) (commit : (readout (N i) finished).verdict = .commit) :
    ¬ ∃ I : Congruence sig, ∀ C ∈ N 0, Models I.rel C := by
  rintro ⟨I, holds⟩
  exact Superposition.readout_commit commit ⟨I, derivation.models I holds i⟩

end Readout

#print axioms models_lower_of_irredundant
#print axioms redundant_diff
#print axioms redundantInference_diff
#print axioms Derivation.models
#print axioms Derivation.entails
#print axioms Derivation.models_back
#print axioms removed_redundant
#print axioms Derivation.redundant_limit
#print axioms limit_models
#print axioms Derivation.saturated
#print axioms Derivation.complete
#print axioms Loop.derivation
#print axioms Loop.selected
#print axioms Loop.eventually_active
#print axioms Loop.fair
#print axioms Loop.complete
#print axioms readout_commit
#print axioms readout_refuted
#print axioms readout_cutOff
#print axioms Derivation.readout_refuted
#print axioms Derivation.readout_commit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition
