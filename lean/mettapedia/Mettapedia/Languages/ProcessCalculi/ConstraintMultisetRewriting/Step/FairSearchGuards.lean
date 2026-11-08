import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FairSearch

/-!
# Search firings license a guarded firing, in one store

The certificate a lowered Pi guard checks can be made by the step's own search firings, in the same
store as the guarded firing. Occurrences are reach facts `inl e` and the answer `inr ()`.

* The **exploration** reads `inl e` and makes `inl e'` for every edge (`reachEdge`).
* The **guarded firing with certificate `I`** reads the reach facts of `I` and makes the answer
  (`answer`). It belongs to the program exactly when `I` checks (`checkInvariant`): the check is
  decided once per instance of the rule, not at every firing.

The program is monotone (`program_monotone`).

* **Soundness, under every schedule** (`answer_sound`): whenever the answer is present, the
  specification holds. No fairness, no trust in the search.
* **Completeness under weak fairness** (`answer_eventually`): on a finite-state datum that
  satisfies the specification, every weakly fair run makes the answer, and keeps it. The
  exploration saturates the datum's reachable states (`reach_saturates`), and the guarded firing
  whose certificate is that set becomes enabled.
* **Control: the closure-free license answers wrongly** (`closure_free_license_answers`): with the
  fragment check in place of the certificate check, the guarded firing for `{0}` fires at once on
  the datum `0` that reaches the bad state `1`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FairSearchGuards

open MeTTaCalculus.OccurrenceCommits (Commit Enabled fire mem_fire)
open MeTTaCalculus.OccurrenceCommits.Liveness (Run)
open FairSearch GuardFragments

universe u

variable {R : Type u} [DecidableEq R]

/-- **Expanding an edge**: read the fact that `e` is reached, make the fact that `e'` is. -/
def reachEdge (e e' : R) : Commit (R ⊕ Unit) (R ⊕ Unit) := ⟨∅, {.inl e}, {.inl e'}, []⟩

/-- **The guarded firing with certificate `I`**: read the reach facts of `I`, make the answer. -/
def answer (I : Finset R) : Commit (R ⊕ Unit) (R ⊕ Unit) :=
  ⟨∅, I.map Function.Embedding.inl, {.inr ()}, []⟩

variable (succ : R → Finset R) (p : R → Bool) (d : R)

/-- **The program**: the exploration, and the guarded firing for every certificate that checks. -/
def program : Set (Commit (R ⊕ Unit) (R ⊕ Unit)) :=
  {c | (∃ e, ∃ e' ∈ succ e, c = reachEdge e e') ∨ ∃ I, checkInvariant succ p d I = true ∧ c = answer I}

/-- The same program licensed by the closure-free check. -/
def fragmentProgram : Set (Commit (R ⊕ Unit) (R ⊕ Unit)) :=
  {c | (∃ e, ∃ e' ∈ succ e, c = reachEdge e e') ∨ ∃ I, checkFragment p d I = true ∧ c = answer I}

theorem program_monotone : ∀ c ∈ program succ p d, c.Monotone := by
  rintro c (⟨e, e', -, rfl⟩ | ⟨I, -, rfl⟩) <;> exact ⟨rfl, rfl⟩

variable {succ p d}

/-- **Soundness under every schedule**: whenever the answer is present, the specification holds. -/
theorem answer_sound (r : Run (commitSystem id (program succ p d)).withIdle)
    (start : r.state 0 = {.inl d}) :
    ∀ n, Sum.inr () ∈ r.state n → Always succ (fun e => p e = true) d
  | 0, member => by
      rw [start] at member
      simp at member
  | n + 1, member => by
      rcases state_succ r n with same | ⟨c, inProgram, -, -, next⟩
      · rw [same] at member
        exact answer_sound r start n member
      · rw [next] at member
        rcases mem_fire.mp member with ⟨old, -⟩ | made
        · exact answer_sound r start n old
        · rcases inProgram with ⟨e, e', -, rfl⟩ | ⟨I, checks, rfl⟩
          · simp [reachEdge] at made
          · exact (checkInvariant_eq_true_iff.mp checks).always

/-- **Under weak fairness the exploration makes every reachable state**, for good. -/
theorem reach_saturates (r : Run (commitSystem id (program succ p d)).withIdle)
    (start : r.state 0 = {.inl d}) (fair : ∀ c ∈ program succ p d, r.WeaklyFair (task c)) {e : R}
    (reach : Reach succ d e) : ∃ N, ∀ n ≥ N, Sum.inl e ∈ r.state n := by
  induction reach with
  | refl =>
      refine ⟨0, fun n _ => state_mono (program_monotone succ p d) r (Nat.zero_le n) ?_⟩
      rw [start]
      exact Finset.mem_singleton_self _
  | @tail b e' _ step ih =>
      obtain ⟨N, present⟩ := ih
      by_cases already : Sum.inl e' ∈ r.state N
      · exact ⟨N, fun n le => state_mono (program_monotone succ p d) r le already⟩
      · have member : reachEdge b e' ∈ program succ p d := Or.inl ⟨b, e', step, rfl⟩
        have enabled : Enabled id (r.state N) (reachEdge b e') :=
          { taken_subset := Finset.empty_subset _
            kept_subset := Finset.singleton_subset_iff.mpr (present N le_rfl)
            apart := Finset.disjoint_empty_left _
            fresh := Finset.disjoint_singleton_left.mpr already
            queries_hold := fun _ inQueries => by cases inQueries }
        obtain ⟨n, -, always⟩ :=
          made_present_eventually (program_monotone succ p d) r (fair _ member) member rfl enabled
        exact ⟨n, always⟩

/-- **Completeness under weak fairness**: on a finite-state datum that satisfies the specification,
every weakly fair run makes the answer, and keeps it. -/
theorem answer_eventually (finite : FiniteState succ d) (always : Always succ (fun e => p e = true) d)
    (r : Run (commitSystem id (program succ p d)).withIdle) (start : r.state 0 = {.inl d})
    (fair : ∀ c ∈ program succ p d, r.WeaklyFair (task c)) :
    ∃ N, ∀ n ≥ N, Sum.inr () ∈ r.state n := by
  have covers : ∀ s : Finset R, (∀ e ∈ s, Reach succ d e) →
      ∃ N, ∀ n ≥ N, ∀ e ∈ s, Sum.inl e ∈ r.state n := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨0, fun _ _ e member => absurd member (Finset.notMem_empty e)⟩
    | insert a s _ ih =>
        intro each
        obtain ⟨N, present⟩ := ih fun e member => each e (Finset.mem_insert_of_mem member)
        obtain ⟨M, here⟩ := reach_saturates r start fair (each a (Finset.mem_insert_self a s))
        refine ⟨max N M, fun n le e member => ?_⟩
        rcases Finset.mem_insert.mp member with rfl | old
        · exact here n (le_of_max_le_right le)
        · exact present n (le_of_max_le_left le) e old
  obtain ⟨N, present⟩ := covers finite.toFinset fun e member => finite.mem_toFinset.mp member
  have checks : checkInvariant succ p d finite.toFinset = true :=
    checkInvariant_eq_true_iff.mpr (invariant_reach always finite)
  have member : answer finite.toFinset ∈ program succ p d := Or.inr ⟨_, checks, rfl⟩
  by_cases already : Sum.inr () ∈ r.state N
  · exact ⟨N, fun n le => state_mono (program_monotone succ p d) r le already⟩
  · have enabled : Enabled id (r.state N) (answer finite.toFinset) :=
      { taken_subset := Finset.empty_subset _
        kept_subset := by
          intro o inKept
          obtain ⟨e, inF, rfl⟩ := Finset.mem_map.mp inKept
          exact present N le_rfl e inF
        apart := Finset.disjoint_empty_left _
        fresh := Finset.disjoint_singleton_left.mpr already
        queries_hold := fun _ inQueries => by cases inQueries }
    obtain ⟨n, -, kept⟩ :=
      made_present_eventually (program_monotone succ p d) r (fair _ member) member rfl enabled
    exact ⟨n, kept⟩

namespace Controls

open GuardFragments.Controls (escape zeroOnly closure_free_unsound)

/-- **The closure-free license answers wrongly**: the guarded firing for `{0}` fires at once on the
datum `0`, which reaches the bad state `1`. -/
theorem closure_free_license_answers :
    ∃ s, (commitSystem id (fragmentProgram escape zeroOnly 0)).Reachable {.inl 0} s ∧
      Sum.inr () ∈ s ∧ ¬ Always escape (fun e => zeroOnly e = true) 0 :=
  ⟨fire {.inl 0} (answer {0}), ⟨[answer {0}], .cons
      (⟨Or.inr ⟨{0}, by decide, rfl⟩, by decide⟩ :
        answer {0} ∈ fragmentProgram escape zeroOnly 0 ∧
          Enabled id ({.inl 0} : Finset (ℕ ⊕ Unit)) (answer {0})) (.nil _)⟩,
    by decide, closure_free_unsound.2.1⟩

end Controls

#print axioms program_monotone
#print axioms answer_sound
#print axioms reach_saturates
#print axioms answer_eventually
#print axioms Controls.closure_free_license_answers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FairSearchGuards
