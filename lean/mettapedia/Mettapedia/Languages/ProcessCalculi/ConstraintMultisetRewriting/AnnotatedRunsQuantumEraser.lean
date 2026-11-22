import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsQuantumAttention

/-!
# Erasing the records restores interference

R27's superposed alternatives make the answer rows `20` and `21`: records, so their amplitudes
`1` and `-1` read classically, `2` (`Attention.Recorded.recorded_branch_counted_as_interfering`).

Two erasers consume the records: `eraseFirst` takes `20` and `eraseSecond` takes `21`, and each
makes the row `30`. With them in the catalogue, the two causal histories `first; eraseFirst` and
`second; eraseSecond` reach one configuration class (`erased_same_end`), so nothing at the cut
records which alternative was taken, and the readout of the amplitudes `1` and `-1` is `0`
(`eraser_restores_interference`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace AmplitudeRuns

namespace QuantumEraser

open Mettapedia.Algebra.RationalComplexAmplitude (Amplitude born)
open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label Run zeros)
open AnnotatedRunBranchCollection.Controls.Superpose (root first second first_valid second_valid
  alternatives)
open AmplitudeControls (everything regionBranches_everything refused_of_absent class_bag)
open AmplitudeControls.Superposed (shifted shifted_first shifted_second)
open AnnotatedRunUnfolding (CausalClass mem_frontier Terminal)
open AnnotatedRunBranchCollection (terminalBranches mem_terminalBranches Closed)

/-- **The eraser of the first record**: takes the answer row `20` and makes the row `30`. -/
def eraseFirst : Run := ⟨⟨[.const 2], [], [], [], [.const 2]⟩, [], ⟨[20], [], [30]⟩⟩

/-- **The eraser of the second record**: takes the answer row `21` and makes the row `30`. -/
def eraseSecond : Run := ⟨⟨[.const 2], [], [], [], [.const 2]⟩, [], ⟨[21], [], [30]⟩⟩

/-- The alternatives with their erasers. -/
def erasing : List Run := [first, second, eraseFirst, eraseSecond]

theorem eraseFirst_valid : eraseFirst.Valid A label (first.result label root) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [eraseFirst]⟩,
    by simp [eraseFirst]⟩
  intro equation member
  have cases : equation = (.const 9, label 9) ∨ equation = (.const 2, label 20) := by
    simpa [Selection.problem, Selection.equations, Selection.result, Firing.result, root, first,
      eraseFirst] using member
  rcases cases with rfl | rfl <;> rfl

theorem eraseSecond_valid : eraseSecond.Valid A label (second.result label root) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [eraseSecond]⟩,
    by simp [eraseSecond]⟩
  intro equation member
  have cases : equation = (.const 9, label 9) ∨ equation = (.const 2, label 21) := by
    simpa [Selection.problem, Selection.equations, Selection.result, Firing.result, root, second,
      eraseSecond] using member
  rcases cases with rfl | rfl <;> rfl

theorem at_root {g : Run} (member : g ∈ erasing) (valid : g.Valid A label root) :
    g = first ∨ g = second := by
  simp only [erasing, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd valid (refused_of_absent (o := 20) (by simp [eraseFirst]) (by decide))
  · exact absurd valid (refused_of_absent (o := 21) (by simp [eraseSecond]) (by decide))

theorem after_first {h : Run} (member : h ∈ erasing)
    (valid : h.Valid A label (first.result label root)) : h = eraseFirst := by
  simp only [erasing, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact absurd valid (refused_of_absent (o := 9) (by simp [first]) (by decide))
  · exact absurd valid (refused_of_absent (o := 9) (by simp [second]) (by decide))
  · rfl
  · exact absurd valid (refused_of_absent (o := 21) (by simp [eraseSecond]) (by decide))

theorem after_second {h : Run} (member : h ∈ erasing)
    (valid : h.Valid A label (second.result label root)) : h = eraseSecond := by
  simp only [erasing, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact absurd valid (refused_of_absent (o := 9) (by simp [first]) (by decide))
  · exact absurd valid (refused_of_absent (o := 9) (by simp [second]) (by decide))
  · exact absurd valid (refused_of_absent (o := 20) (by simp [eraseFirst]) (by decide))
  · rfl

theorem erased_terminal_first :
    Terminal A label erasing (eraseFirst.result label (first.result label root)) := by
  intro f member
  simp only [erasing, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact refused_of_absent (o := 9) (by simp [first]) (by decide)
  · exact refused_of_absent (o := 9) (by simp [second]) (by decide)
  · exact refused_of_absent (o := 20) (by simp [eraseFirst]) (by decide)
  · exact refused_of_absent (o := 21) (by simp [eraseSecond]) (by decide)

theorem erased_terminal_second :
    Terminal A label erasing (eraseSecond.result label (second.result label root)) := by
  intro f member
  simp only [erasing, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact refused_of_absent (o := 9) (by simp [first]) (by decide)
  · exact refused_of_absent (o := 9) (by simp [second]) (by decide)
  · exact refused_of_absent (o := 20) (by simp [eraseFirst]) (by decide)
  · exact refused_of_absent (o := 21) (by simp [eraseSecond]) (by decide)

theorem erasing_closed : Closed A label erasing 2 root := by
  intro word member
  obtain ⟨length, run, covered⟩ := (mem_frontier A label erasing 2 root word).mp member
  rcases word with _ | ⟨g, _ | ⟨h, _ | ⟨k, rest⟩⟩⟩
  · simp at length
  · simp at length
  · rcases at_root (covered g (by simp)) run.1 with rfl | rfl
    · rw [after_first (covered h (by simp)) run.2.1]
      exact erased_terminal_first
    · rw [after_second (covered h (by simp)) run.2.1]
      exact erased_terminal_second
  · simp only [List.length_cons] at length
    omega

open Classical in
theorem erasing_branches :
    terminalBranches A label erasing 2 root =
      {Quot.mk _ [first, eraseFirst], Quot.mk _ [second, eraseSecond]} := by
  ext trace
  rw [mem_terminalBranches, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨word, length, run, covered, terminal, rfl⟩
    rcases word with _ | ⟨g, _ | ⟨h, _ | ⟨k, rest⟩⟩⟩
    · exact absurd first_valid (terminal first (by simp [erasing]))
    · rcases at_root (covered g (by simp)) run.1 with rfl | rfl
      · exact absurd eraseFirst_valid (terminal eraseFirst (by simp [erasing]))
      · exact absurd eraseSecond_valid (terminal eraseSecond (by simp [erasing]))
    · rcases at_root (covered g (by simp)) run.1 with rfl | rfl
      · rw [after_first (covered h (by simp)) run.2.1]
        exact Or.inl rfl
      · rw [after_second (covered h (by simp)) run.2.1]
        exact Or.inr rfl
    · simp only [List.length_cons] at length
      omega
  · rintro (rfl | rfl)
    · exact ⟨[first, eraseFirst], by simp,
        ⟨first_valid, eraseFirst_valid, eraseFirst_valid.firing.consistent⟩, by simp [erasing],
        erased_terminal_first, rfl⟩
    · exact ⟨[second, eraseSecond], by simp,
        ⟨second_valid, eraseSecond_valid, eraseSecond_valid.firing.consistent⟩,
        by simp [erasing], erased_terminal_second, rfl⟩

/-- **The erased histories are two causal histories.** -/
theorem erased_distinct :
    (Quot.mk _ [first, eraseFirst] : CausalClass A label root) ≠ Quot.mk _ [second, eraseSecond] := by
  intro same
  have bags := class_bag same
  have member : first ∈ ([second, eraseSecond] : Multiset Run) := by
    rw [← bags]
    simp
  rw [Multiset.mem_coe, List.mem_cons, List.mem_singleton] at member
  rcases member with same' | same'
  · have made := congrArg (fun f : Run => f.selection.made) same'
    simp [first, second] at made
  · have made := congrArg (fun f : Run => f.selection.made) same'
    simp [first, eraseSecond] at made

/-- **Erased, nothing records which alternative was taken**: both histories reach one
configuration class. -/
theorem erased_same_end :
    classEnd A label root (Quot.mk _ [first, eraseFirst]) =
      classEnd A label root (Quot.mk _ [second, eraseSecond]) := by
  rw [classEnd_mk, classEnd_mk]
  exact Quotient.sound (show GuardFreeProcessOrders.SameUpTo A _ _ from
    ⟨fun _ => Iff.rfl, by decide⟩)

theorem shifted_eraseFirst : shifted eraseFirst = 1 := by simp [shifted, eraseFirst]

theorem shifted_eraseSecond : shifted eraseSecond = 1 := by simp [shifted, eraseSecond]

open Classical in
theorem erased_paths :
    branchAmplitudes A label shifted erasing 2 root everything = {1, -1} := by
  unfold branchAmplitudes
  rw [regionBranches_everything, erasing_branches,
    Finset.insert_val_of_notMem (by simpa using erased_distinct), Finset.singleton_val]
  simp [classAmplitude_mk, runAmplitude, shifted_first, shifted_second, shifted_eraseFirst,
    shifted_eraseSecond]

open Classical in
/-- **Erasing the records restores interference.** Without the erasers the superposed amplitudes
`1` and `-1` read `2`; with them, the two histories reach one configuration class and read `0`. -/
theorem eraser_restores_interference :
    branchReadout A label shifted alternatives 1 root everything = 2 ∧
      branchReadout A label shifted erasing 2 root everything = 0 ∧
      incoherent (branchAmplitudes A label shifted erasing 2 root everything) = 2 := by
  refine ⟨Attention.Recorded.recorded_branch_counted_as_interfering.2.2, ?_, ?_⟩
  · have inFirst : (Quot.mk _ [first, eraseFirst] : CausalClass A label root) ∈
        regionBranches A label erasing 2 root everything := by
      rw [regionBranches_everything, erasing_branches]
      exact Finset.mem_insert_self _ _
    have shared : ∀ trace ∈ regionBranches A label erasing 2 root everything,
        classEnd A label root trace = classEnd A label root (Quot.mk _ [first, eraseFirst]) := by
      intro trace member
      rw [regionBranches_everything, erasing_branches, Finset.mem_insert, Finset.mem_singleton]
        at member
      rcases member with rfl | rfl
      · rfl
      · exact erased_same_end.symm
    rw [branchReadout_of_one_end A label shifted ⟨_, inFirst⟩ shared,
      regionalAmplitude_eq_coherent, erased_paths]
    exact opposite_phase_control.1
  · rw [erased_paths]
    exact opposite_phase_control.2.1

end QuantumEraser

end AmplitudeRuns

open AmplitudeRuns.QuantumEraser

#print axioms eraseFirst_valid
#print axioms eraseSecond_valid
#print axioms erasing_closed
#print axioms erasing_branches
#print axioms erased_distinct
#print axioms erased_same_end
#print axioms erased_paths
#print axioms eraser_restores_interference

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
