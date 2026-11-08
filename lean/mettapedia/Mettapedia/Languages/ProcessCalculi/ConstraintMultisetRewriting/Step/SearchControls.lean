import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchPolicy
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchTabling

/-!
# Controls for bounded search

The left-recursive space `leftRec`: `root` offers the answer `0` and the state `left`; `left` offers
itself first and then the answer `1`. Its tree is infinite; the answer `1` occurs at `[1, 1]`,
`[1, 0, 1]`, `[1, 0, 0, 1]`, ….

* **Depth-first on a left-recursive branch** is cut off with an answer found elsewhere, at every
  budget from two on (`dfs_within`), and never records the answer at `[1, 1]` (`dfs_loses`), which
  breadth-first records at budget five (`bfs_finds`) and iterative deepening at depth two
  (`deepen_finds`).
* **Zero budget** is cut off with no answers and reads suspended, never refuted, although answers
  exist (`zero_budget`); a finished search with no answers reads refuted (`deadEnd_refuted`).
* **Collect over a choice with a cut-off alternative** is unknown, although an answer was found
  (`collect_cut_choice`).
* **`take 1` stops early**: it is finished for its own contract while the full search is cut off at
  every budget, for every policy (`take_stops_early`, `never_finishes`).
* **Tabling**: a cut-off record kept as cut off is sound (`kept_record_sound`); the same record
  read as finished refutes a state that has answers and loses the answers at the root
  (`misread_refutes`, `misread_loses`); no finished record of `left` is sound
  (`misread_record_unsound`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search

namespace Controls

/-- The states of the left-recursive control. -/
inductive Node where
  | root
  | left
  deriving DecidableEq, Repr

/-- **The left-recursive control.** -/
def leftRec : Space Node ℕ where
  unfold
    | .root => [.inl 0, .inr .left]
    | .left => [.inr .left, .inl 1]

theorem left_state : ∀ k : ℕ, leftRec.item (.inr .left) (List.replicate k 0) = some (.inr .left)
  | 0 => rfl
  | k + 1 => by
      rw [List.replicate_succ, Space.item_inr_cons]
      exact left_state k

theorem root_left_state (k : ℕ) :
    leftRec.item (.inr .root) (1 :: List.replicate k 0) = some (.inr .left) := by
  rw [Space.item_inr_cons]
  exact left_state k

theorem answer_left : (([1], 1) : List ℕ × ℕ) ∈ leftRec.Answers (.inr .left) := rfl
theorem answer_deep : (([1, 1], 1) : List ℕ × ℕ) ∈ leftRec.Answers (.inr .root) := rfl
theorem answer_deeper : (([1, 0, 1], 1) : List ℕ × ℕ) ∈ leftRec.Answers (.inr .root) := rfl
theorem answer_shallow : (([0], 0) : List ℕ × ℕ) ∈ leftRec.Answers (.inr .root) := rfl

/-- Every budgeted run of `left` is cut off. -/
theorem run_left_cutOff (N : ℕ) : (leftRec.run N (.inr .left)).status = .cutOff :=
  (leftRec.status_run_eq_cutOff_iff N _).mpr ⟨_, _, left_state N, by simp⟩

/-- Every budgeted run of `root` is cut off. -/
theorem run_root_cutOff (N : ℕ) : (leftRec.run N (.inr .root)).status = .cutOff :=
  (leftRec.status_run_eq_cutOff_iff N _).mpr ⟨_, _, root_left_state N, by simp⟩

/-- **No policy ever finishes** the left-recursive control. -/
theorem never_finishes (P : Policy (List ℕ × (ℕ ⊕ Node))) (k : ℕ) :
    (leftRec.search P k (.inr .root)).pending ≠ [] := by
  intro finished
  have := leftRec.length_lt_of_finished P finished (root_left_state k)
  simp at this

/-! ## Depth-first loses an answer -/

theorem children_left (w : List ℕ) :
    leftRec.children w .left = [(w ++ [0], .inr .left), (w ++ [1], .inl 1)] := rfl

/-- From budget two on, depth-first has recorded the answer `0` and is in front of `left`. -/
theorem dfs_shape : ∀ k : ℕ, ∃ w rest,
    leftRec.search .dfs (k + 2) (.inr .root) = ⟨[([0], 0)], (w, .inr .left) :: rest⟩
  | 0 => ⟨[1], [], rfl⟩
  | k + 1 => by
      obtain ⟨w, rest, same⟩ := dfs_shape k
      refine ⟨w ++ [0], (w ++ [1], .inl 1) :: rest, ?_⟩
      rw [show k + 1 + 2 = (k + 2) + 1 by omega, Space.search_succ, same]
      show (⟨[([0], 0)], Policy.dfs.insert (leftRec.children w .left) rest⟩ : Config Node ℕ) = _
      rw [children_left]
      rfl

/-- **Depth-first is cut off with an answer found elsewhere**, at every budget from two on. -/
theorem dfs_within (k : ℕ) :
    leftRec.within .dfs (k + 2) (.inr .root) = ⟨{0}, .cutOff⟩ := by
  obtain ⟨w, rest, same⟩ := dfs_shape k
  rw [Space.within, same]
  rfl

theorem dfs_found_small : ∀ k < 2, (leftRec.search .dfs k (.inr .root)).found = []
  | 0, _ => rfl
  | 1, _ => rfl

/-- **Depth-first never records the answer at `[1, 1]`.** -/
theorem dfs_loses (k : ℕ) : (([1, 1], 1) : List ℕ × ℕ) ∉ (leftRec.search .dfs k (.inr .root)).found := by
  by_cases small : k < 2
  · rw [dfs_found_small k small]
    exact List.not_mem_nil
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    obtain ⟨w, rest, same⟩ := dfs_shape j
    rw [same]
    show (([1, 1], 1) : List ℕ × ℕ) ∉ [([0], 0)]
    decide

/-- **Breadth-first records it at budget five.** -/
theorem bfs_finds : (([1, 1], 1) : List ℕ × ℕ) ∈ (leftRec.search .bfs 5 (.inr .root)).found := by
  decide

/-- **Iterative deepening records it at depth two.** -/
theorem deepen_finds : (([1, 1], 1) : List ℕ × ℕ) ∈ (leftRec.deepen 2 (.inr .root)).answers :=
  leftRec.mem_deepen answer_deep (by decide)

/-! ## Incomplete is never none -/

/-- **Zero budget**: cut off with no answers, suspended and not refuted, although answers exist. -/
theorem zero_budget :
    leftRec.approx 0 (.inr .root) = Outcome.unknown ∧
      (leftRec.approx 0 (.inr .root)).verdict = .suspended ∧
      (leftRec.approx 0 (.inr .root)).verdict ≠ .refuted ∧
      (([0], 0) : List ℕ × ℕ) ∈ leftRec.Answers (.inr .root) := by
  refine ⟨leftRec.approx_zero _, ?_, ?_, answer_shallow⟩
  · rw [leftRec.approx_zero]; rfl
  · rw [leftRec.approx_zero]; decide

/-- A state with no alternatives. -/
def deadEnd : Space Unit ℕ := ⟨fun _ => []⟩

/-- **Finished with no answers is refuted**, and the refutation is sound. -/
theorem deadEnd_refuted :
    (deadEnd.approx 1 (.inr ())).verdict = .refuted ∧ ∀ w a, deadEnd.item (.inr ()) w ≠ some (.inl a) := by
  have refuted : (deadEnd.approx 1 (.inr ())).verdict = .refuted := by
    rw [deadEnd.approx_succ]
    rfl
  exact ⟨refuted, deadEnd.refuted_sound refuted⟩

/-- **Collect over a choice with a cut-off alternative is unknown**, though an answer was found. -/
theorem collect_cut_choice :
    leftRec.approx 2 (.inr .root) = Outcome.pure 0 + (leftRec.approx 1 (.inr .left) + 0) ∧
      0 ∈ (leftRec.approx 2 (.inr .root)).answers ∧
      Outcome.collect (leftRec.approx 2 (.inr .root)) = Outcome.unknown := by
  have choice : leftRec.approx 2 (.inr .root) = Outcome.pure 0 + (leftRec.approx 1 (.inr .left) + 0) := by
    rw [leftRec.approx_succ]
    show leftRec.approx 1 (.inl 0) + (leftRec.approx 1 (.inr .left) + 0) = _
    rw [leftRec.approx_inl]
  refine ⟨choice, ?_, ?_⟩
  · rw [choice]
    simp
  · have cut : (leftRec.approx 1 (.inr .left) + 0).status = .cutOff := by
      rw [add_zero]
      exact run_left_cutOff 1
    rw [choice, Outcome.collect_add_cutOff _ _ cut]

/-! ## `take` stops early -/

theorem take_two : (leftRec.take .dfs 1 2 (.inr .root)).found = [([0], 0)] := rfl

theorem take_found (k : ℕ) : (leftRec.take .dfs 1 (k + 2) (.inr .root)).found = [([0], 0)] := by
  induction k with
  | zero => exact take_two
  | succ k ih =>
      have unfold : leftRec.take .dfs 1 (k + 1 + 2) (.inr .root) =
          leftRec.stepUntil .dfs 1 (leftRec.take .dfs 1 (k + 2) (.inr .root)) :=
        Function.iterate_succ_apply' _ _ _
      rw [unfold, Space.stepUntil, if_pos (by rw [ih]; rfl), ih]

/-- **`take 1` is finished for its own contract, not for the full search**: the full search is cut
off at every budget, for every policy. -/
theorem take_stops_early (k : ℕ) :
    (leftRec.take .dfs 1 (k + 2) (.inr .root)).takeStatus 1 = .finished ∧
      (leftRec.first .dfs (k + 2) (.inr .root)) = some ([0], 0) ∧
      ∀ (P : Policy (List ℕ × (ℕ ⊕ Node))) (j : ℕ), (leftRec.search P j (.inr .root)).status = .cutOff := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Config.takeStatus, if_pos (by rw [take_found]; decide)]
  · rw [Space.first, take_found]
    rfl
  · intro P j
    apply Status.eq_cutOff_of_ne_finished
    rw [Ne, Config.status_eq_finished_iff]
    exact never_finishes P j

/-! ## Tabling -/

/-- A record of `left` from its depth-zero run, kept as cut off. -/
def kept : Node → Option (Outcome ℕ)
  | .left => some Outcome.unknown
  | .root => none

/-- The same record read as finished: refuted. -/
def misread : Node → Option (Outcome ℕ)
  | .left => some 0
  | .root => none

/-- The record is the depth-zero run of `left`. -/
theorem kept_is_run : leftRec.approx 0 (.inr .left) = Outcome.unknown := leftRec.approx_zero _

/-- **A cut-off record kept as cut off is sound.** -/
theorem kept_record_sound : leftRec.SoundMemo kept := by
  intro s o h
  cases s with
  | root => cases h
  | left =>
      cases h
      exact ⟨0, bot_le⟩

/-- **The misread record refutes a state that has answers.** -/
theorem misread_refutes :
    (leftRec.runMemo misread 1 (.inr .left)).verdict = .refuted ∧
      (([1], 1) : List ℕ × ℕ) ∈ leftRec.Answers (.inr .left) :=
  ⟨rfl, answer_left⟩

/-- **The misread record loses answers**: the tabled run of `root` claims to be finished with the
answer `0` only, while `1` is an answer. -/
theorem misread_loses :
    (leftRec.runMemo misread 1 (.inr .root)).status = .finished ∧
      1 ∉ (leftRec.runMemo misread 1 (.inr .root)).answers ∧
      (([1, 1], 1) : List ℕ × ℕ) ∈ leftRec.Answers (.inr .root) := by
  refine ⟨rfl, ?_, answer_deep⟩
  show 1 ∉ ((Outcome.pure 0 + ((0 : Outcome ℕ) + 0) : Outcome ℕ)).answers
  simp

/-- With the kept record, the tabled run of `root` stays cut off, and it is sound. -/
theorem kept_cut :
    (leftRec.runMemo kept 1 (.inr .root)).status = .cutOff ∧
      ∃ N, leftRec.runMemo kept 1 (.inr .root) ≤ leftRec.approx N (.inr .root) :=
  ⟨rfl, leftRec.runMemo_le_approx kept_record_sound 1 _⟩

/-- **No finished record of `left` is sound**: its search never finishes. -/
theorem misread_record_unsound (A : Multiset ℕ) :
    ¬ ∃ N, (⟨A, .finished⟩ : Outcome ℕ) ≤ leftRec.approx N (.inr .left) :=
  leftRec.finished_record_unsound .left A run_left_cutOff

theorem misread_not_sound : ¬ leftRec.SoundMemo misread := by
  intro sound
  obtain ⟨N, below⟩ := sound .left 0 rfl
  exact misread_record_unsound 0 ⟨N, below⟩

end Controls

#print axioms Controls.never_finishes
#print axioms Controls.dfs_shape
#print axioms Controls.dfs_within
#print axioms Controls.dfs_loses
#print axioms Controls.bfs_finds
#print axioms Controls.deepen_finds
#print axioms Controls.zero_budget
#print axioms Controls.deadEnd_refuted
#print axioms Controls.collect_cut_choice
#print axioms Controls.take_stops_early
#print axioms Controls.kept_record_sound
#print axioms Controls.misread_refutes
#print axioms Controls.misread_loses
#print axioms Controls.kept_cut
#print axioms Controls.misread_record_unsound
#print axioms Controls.misread_not_sound

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search
