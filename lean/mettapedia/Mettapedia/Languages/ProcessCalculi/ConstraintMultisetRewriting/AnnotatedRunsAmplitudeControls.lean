import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsAmplitude
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunBranchCollectionControls

/-!
# Controls for amplitudes over causal histories

All controls run on the candidate step, over R27's unfolding.

* **Superposed alternatives interfere** (`superposed_cancel`, `superposed_reinforce`): R27's two
  alternatives competing for one token are two causal histories. With amplitudes `1` and
  `e^{iπ} = -1` their regional amplitude is `0` against an incoherent `2`, and the complete
  collection certifies the cancellation; in phase it is `2`, with Born weight `4` against `2`.
* **A third alternative's arrival flips the cancellation** (`third_alternative_flips`): with a
  third alternative of amplitude `1` in the catalogue the branches give `1` against `3`, and
  nothing cancels.
* **A diamond is one branch** (`diamond_counts_twice`): the two orders of R22's round of the taker
  and the reader are one causal history of amplitude `i`. Summed over interleavings it is `2i`,
  with Born weight `4` where it should be `1`.
* **Incomplete is not amplitude zero** (`incomplete_not_zero`): with depth budget `0` the taker is
  still enabled, so the collection is incomplete and found nothing; its partial sum is `0`, and
  it certifies no amplitude. With budget `1` the regional amplitude is `1`.
* **An incomplete collection whose paths cancel certifies nothing**
  (`partial_cancellation_not_certified`): a staged third alternative needs two firings. At depth
  budget `1` the collection is incomplete and the two paths it found, `1` and `-1`, cancel; at
  budget `2` the frontier is closed and the regional amplitude is `1`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns.AmplitudeRuns.AmplitudeControls

open Mettapedia.Algebra.RationalComplexAmplitude (Amplitude born)
open AnnotatedRunUnfolding (CausalClass frontier mem_frontier Terminal)
open AnnotatedRunBranchCollection (terminalBranches mem_terminalBranches Closed Collection)
open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label Run zeros)

/-- The region of every configuration class. -/
def everything : ConfigurationClass A Nat → Prop := fun _ => True

theorem regionBranches_everything (catalogue : List Run) (budget : ℕ)
    (root : Configuration (Term signature) Nat) :
    regionBranches A label catalogue budget root everything =
      terminalBranches A label catalogue budget root := by
  classical
  unfold regionBranches
  exact Finset.filter_true_of_mem fun _ _ => trivial

/-- Round equivalence keeps the bag of firings, so classes with different bags differ. -/
theorem class_bag {root : Configuration (Term signature) Nat} {w w' : List Run}
    (same : (Quot.mk _ w : CausalClass A label root) = Quot.mk _ w') :
    (w : Multiset Run) = (w' : Multiset Run) :=
  congrArg (Quot.lift (fun w : List Run => (w : Multiset Run))
    (fun _ _ related => Multiset.coe_eq_coe.mpr (RoundEquiv.perm A label related))) same

theorem single_class_injective {root : Configuration (Term signature) Nat} {f g : Run}
    (same : (Quot.mk _ [f] : CausalClass A label root) = Quot.mk _ [g]) : f = g :=
  Multiset.singleton_inj.mp (class_bag same)

/-- A firing that takes an absent occurrence is refused. -/
theorem refused_of_absent {f : Run} {C : Configuration (Term signature) Nat} {o : Nat}
    (taken : o ∈ f.selection.taken) (absent : o ∉ C.present) : ¬ f.Valid A label C := fun valid =>
  absent (valid.firing.occurrences.taken_subset (by simpa [Selection.commit] using taken))

/-- A firing that makes an occurrence already present is refused. -/
theorem refused_of_made_present {f : Run} {C : Configuration (Term signature) Nat} {o : Nat}
    (made : o ∈ f.selection.made) (present : o ∈ C.present) : ¬ f.Valid A label C := fun valid =>
  Finset.disjoint_left.mp valid.firing.occurrences.fresh (by simpa [Selection.commit] using made)
    present

/-! ## Superposed alternatives interfere -/

namespace Superposed

open AnnotatedRunBranchCollection.Controls.Superpose (root first second alternatives first_valid
  second_valid closed branches branches_distinct first_ne_second)

/-- The second alternative, the one that makes `21`, is shifted by `π`; every other firing has
amplitude `1`. -/
def shifted (f : Run) : Amplitude := if f.selection.made = [21] then -1 else 1

/-- Every firing has amplitude `1`. -/
def aligned (_ : Run) : Amplitude := 1

theorem shifted_first : shifted first = 1 := by simp [shifted, first]

theorem shifted_second : shifted second = -1 := by simp [shifted, second]

open Classical in
theorem paths (amp : Run → Amplitude) :
    branchAmplitudes A label amp alternatives 1 root everything = {amp first, amp second} := by
  unfold branchAmplitudes
  rw [regionBranches_everything, branches,
    Finset.insert_val_of_notMem (by simpa using branches_distinct), Finset.singleton_val]
  simp [classAmplitude_mk, runAmplitude]

/-- **Destructive interference of two superposed alternatives.** With amplitudes `1` and
`e^{iπ} = -1` the two causal histories give the regional amplitude `0` against an incoherent `2`,
and the complete collection certifies the cancellation. -/
theorem superposed_cancel :
    branchAmplitudes A label shifted alternatives 1 root everything = {1, -1} ∧
      regionalAmplitude A label shifted alternatives 1 root everything = 0 ∧
      incoherent (branchAmplitudes A label shifted alternatives 1 root everything) = 2 ∧
      amplitudeCollection A label shifted alternatives 1 root everything = .complete {1, -1} ∧
      CertifiesCancellation (amplitudeCollection A label shifted alternatives 1 root everything) ∧
      interferenceVerdict (amplitudeCollection A label shifted alternatives 1 root everything) =
        .cancels := by
  have bag : branchAmplitudes A label shifted alternatives 1 root everything = {1, -1} := by
    rw [paths, shifted_first, shifted_second]
  have certified : CertifiesCancellation
      (amplitudeCollection A label shifted alternatives 1 root everything) :=
    (certifiesCancellation_iff A label shifted).mpr ⟨closed, bag ▸ opposite_phase_control.2.2⟩
  refine ⟨bag, ?_, ?_, ?_, certified, (interferenceVerdict_cancels_iff _).mpr certified⟩
  · rw [regionalAmplitude_eq_coherent, bag]
    exact opposite_phase_control.2.2.1
  · rw [bag]
    exact opposite_phase_control.2.1
  · exact (amplitudeCollection_eq_complete_iff A label shifted alternatives 1 root everything _).mpr
      ⟨closed, bag.symm⟩

/-- **Constructive interference of the same alternatives in phase**: the regional amplitude `2`
has Born weight `4` against an incoherent `2`. -/
theorem superposed_reinforce :
    branchAmplitudes A label aligned alternatives 1 root everything = {1, 1} ∧
      born (regionalAmplitude A label aligned alternatives 1 root everything) = 4 ∧
      incoherent (branchAmplitudes A label aligned alternatives 1 root everything) = 2 ∧
      CertifiesReinforcement
        (amplitudeCollection A label aligned alternatives 1 root everything) := by
  have bag : branchAmplitudes A label aligned alternatives 1 root everything = {1, 1} := by
    rw [paths]
    rfl
  refine ⟨bag, ?_, ?_, (certifiesReinforcement_iff A label aligned).mpr
    ⟨closed, bag ▸ in_phase_control.2.2⟩⟩
  · rw [regionalAmplitude_eq_coherent, bag]
    exact in_phase_control.1
  · rw [bag]
    exact in_phase_control.2.1

/-! ### A third alternative arrives -/

/-- A third alternative takes the token and makes `22`. -/
def third : Run := ⟨⟨[.const 9], [], [], [], [.const 2]⟩, [], ⟨[9], [], [22]⟩⟩

def alternatives₃ : List Run := [first, second, third]

theorem third_valid : third.Valid A label root := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [third]⟩,
    by simp [third]⟩
  intro equation member
  have same : equation = (.const 9, label 9) := by
    simpa [Selection.problem, Selection.equations, root, third] using member
  subst same
  rfl

theorem shifted_third : shifted third = 1 := by simp [shifted, third]

theorem cases₃ {g : Run} (member : g ∈ alternatives₃) : g = first ∨ g = second ∨ g = third := by
  simpa [alternatives₃] using member

theorem takes_token₃ (f : Run) (member : f ∈ alternatives₃) : 9 ∈ f.selection.taken := by
  rcases cases₃ member with rfl | rfl | rfl <;> simp [first, second, third]

theorem token_gone₃ (g : Run) (inAlternatives : g ∈ alternatives₃) :
    ∀ f ∈ alternatives₃, ¬ f.Valid A label (g.result label root) := by
  intro f member
  apply refused_of_absent (takes_token₃ f member)
  rcases cases₃ inAlternatives with rfl | rfl | rfl <;> decide

theorem closed₃ : Closed A label alternatives₃ 1 root := by
  intro word member
  obtain ⟨length, _, covered⟩ := (mem_frontier A label alternatives₃ 1 root word).mp member
  rcases word with _ | ⟨g, _ | ⟨h, rest⟩⟩
  · simp at length
  · exact token_gone₃ g (covered g (List.mem_singleton_self g))
  · simp only [List.length_cons] at length
    omega

open Classical in
theorem branches₃ :
    terminalBranches A label alternatives₃ 1 root =
      {Quot.mk _ [first], Quot.mk _ [second], Quot.mk _ [third]} := by
  ext trace
  rw [mem_terminalBranches, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨word, length, _, covered, terminal, rfl⟩
    rcases word with _ | ⟨g, _ | ⟨h, rest⟩⟩
    · exact absurd first_valid (terminal first (by simp [alternatives₃]))
    · rcases cases₃ (covered g (List.mem_singleton_self g)) with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · simp only [List.length_cons] at length
      omega
  · rintro (rfl | rfl | rfl)
    · exact ⟨[first], by simp, ⟨first_valid, first_valid.firing.consistent⟩,
        by simp [alternatives₃], token_gone₃ first (by simp [alternatives₃]), rfl⟩
    · exact ⟨[second], by simp, ⟨second_valid, second_valid.firing.consistent⟩,
        by simp [alternatives₃], token_gone₃ second (by simp [alternatives₃]), rfl⟩
    · exact ⟨[third], by simp, ⟨third_valid, third_valid.firing.consistent⟩,
        by simp [alternatives₃], token_gone₃ third (by simp [alternatives₃]), rfl⟩

theorem first_ne_third : first ≠ third := fun same => by
  have made := congrArg (fun f : Run => f.selection.made) same
  simp [first, third] at made

theorem second_ne_third : second ≠ third := fun same => by
  have made := congrArg (fun f : Run => f.selection.made) same
  simp [second, third] at made

open Classical in
theorem paths₃ (amp : Run → Amplitude) :
    branchAmplitudes A label amp alternatives₃ 1 root everything =
      {amp first, amp second, amp third} := by
  unfold branchAmplitudes
  have notFirst : (Quot.mk _ [first] : CausalClass A label root) ∉
      ({Quot.mk _ [second], Quot.mk _ [third]} : Finset (CausalClass A label root)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun same => first_ne_second (single_class_injective same),
      fun same => first_ne_third (single_class_injective same)⟩
  have notSecond : (Quot.mk _ [second] : CausalClass A label root) ∉
      ({Quot.mk _ [third]} : Finset (CausalClass A label root)) := by
    rw [Finset.mem_singleton]
    exact fun same => second_ne_third (single_class_injective same)
  rw [regionBranches_everything, branches₃, Finset.insert_val_of_notMem notFirst,
    Finset.insert_val_of_notMem notSecond, Finset.singleton_val]
  simp [classAmplitude_mk, runAmplitude]

/-- **A third alternative's arrival flips the certified cancellation.** The two alternatives
cancel; with a third of amplitude `1` in the catalogue the branches give `1` against an incoherent
`3`, the complete collection certifies no cancellation, and the verdict is "neither". -/
theorem third_alternative_flips :
    CertifiesCancellation (amplitudeCollection A label shifted alternatives 1 root everything) ∧
      branchAmplitudes A label shifted alternatives₃ 1 root everything = {1, -1, 1} ∧
      regionalAmplitude A label shifted alternatives₃ 1 root everything = 1 ∧
      incoherent (branchAmplitudes A label shifted alternatives₃ 1 root everything) = 3 ∧
      ¬ CertifiesCancellation
        (amplitudeCollection A label shifted alternatives₃ 1 root everything) ∧
      interferenceVerdict (amplitudeCollection A label shifted alternatives₃ 1 root everything) =
        .neither := by
  have bag : branchAmplitudes A label shifted alternatives₃ 1 root everything = {1, -1, 1} := by
    rw [paths₃, shifted_first, shifted_second, shifted_third]
  have flipped := third_path_flips
  have reordered : ({1, -1, 1} : Multiset Amplitude) = 1 ::ₘ {1, -1} :=
    congrArg (Multiset.cons 1) (Multiset.cons_swap (-1 : Amplitude) 1 0)
  have complete : amplitudeCollection A label shifted alternatives₃ 1 root everything =
      .complete {1, -1, 1} :=
    (amplitudeCollection_eq_complete_iff A label shifted alternatives₃ 1 root everything _).mpr
      ⟨closed₃, bag.symm⟩
  have notCancel : ¬ Destructive {1, -1, 1} := by
    rw [reordered]
    exact flipped.2.2.2
  have notReinforce : ¬ Constructive {1, -1, 1} := by
    rw [reordered]
    unfold Constructive
    rw [flipped.2.1, flipped.2.2.1, born_one]
    norm_num
  refine ⟨superposed_cancel.2.2.2.2.1, bag, ?_, ?_, ?_, ?_⟩
  · rw [regionalAmplitude_eq_coherent, bag, reordered]
    exact flipped.2.1
  · rw [bag, reordered]
    exact flipped.2.2.1
  · rw [complete]
    exact notCancel
  · rw [complete]
    simp only [interferenceVerdict, if_neg notCancel, if_neg notReinforce]

end Superposed

/-! ## A diamond is one branch -/

namespace Diamond

open AnnotatedRuns.Controls (taker reader start)

/-- The taker has amplitude `i`; every other firing has amplitude `1`. -/
def phase (f : Run) : Amplitude := if f.selection.taken = [0] then unitI else 1

theorem phase_taker : phase taker = unitI := by simp [phase, taker]

theorem phase_reader : phase reader = 1 := by simp [phase, reader]

open Classical in
/-- **A diamond is one branch.** The two orders of R22's round of the taker and the reader are one
causal history of amplitude `i`. Summed over its branches it is `i`, with Born weight `1`; summed
over its two interleavings it is `2i`, with Born weight `4`. -/
theorem diamond_counts_twice :
    (Quot.mk _ [taker, reader] : CausalClass A label start) = Quot.mk _ [reader, taker] ∧
      runAmplitude phase [taker, reader] = unitI ∧ runAmplitude phase [reader, taker] = unitI ∧
      ∑ trace ∈ ({Quot.mk _ [taker, reader], Quot.mk _ [reader, taker]} :
          Finset (CausalClass A label start)), classAmplitude A label phase start trace = unitI ∧
      ([[taker, reader], [reader, taker]].map (runAmplitude phase)).sum = unitI + unitI ∧
      born unitI = 1 ∧ born (unitI + unitI) = 4 := by
  have same := AnnotatedRunUnfolding.Controls.independent_orders_share_causal_class
  have forward : runAmplitude phase [taker, reader] = unitI := by
    simp [runAmplitude, phase_taker, phase_reader]
  have backward : runAmplitude phase [reader, taker] = unitI := by
    simp [runAmplitude, phase_taker, phase_reader]
  refine ⟨same, forward, backward, ?_, ?_, born_unitI, ?_⟩
  · rw [same, Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.sum_singleton,
      classAmplitude_mk, backward]
  · simp [forward, backward]
  · rw [born_double, born_unitI]
    norm_num

/-! ### The diamond in the unfolding -/

open AnnotatedRuns.Controls (taker_valid reader_valid shared_variables_swap zeros)
open AnnotatedRunUnfolding (enabled completed)

/-- The catalogue of the diamond: the taker and the reader. -/
def catalogue : List Run := [taker, reader]

theorem reader_valid_start : reader.Valid A label start := shared_variables_swap.1.1

theorem taker_after_reader : taker.Valid A label (reader.result label start) :=
  shared_variables_swap.1.2.1

theorem taker_once : ¬ taker.Valid A label (taker.result label start) :=
  refused_of_absent (o := 0) (by simp [taker]) (by decide)

theorem reader_once : ¬ reader.Valid A label (reader.result label start) :=
  refused_of_made_present (o := 3) (by simp [reader]) (by decide)

theorem forward_end :
    ∀ f ∈ catalogue, ¬ f.Valid A label (reader.result label (taker.result label start)) := by
  intro f member
  simp only [catalogue, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact refused_of_absent (o := 0) (by simp [taker]) (by decide)
  · exact refused_of_made_present (o := 3) (by simp [reader]) (by decide)

theorem backward_end :
    ∀ f ∈ catalogue, ¬ f.Valid A label (taker.result label (reader.result label start)) := by
  intro f member
  simp only [catalogue, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact refused_of_absent (o := 0) (by simp [taker]) (by decide)
  · exact refused_of_made_present (o := 3) (by simp [reader]) (by decide)

open Classical in
theorem enabled_start : enabled A label catalogue start = [taker, reader] := by
  unfold enabled catalogue
  rw [List.filter_cons, List.filter_cons, List.filter_nil, if_pos (decide_eq_true taker_valid),
    if_pos (decide_eq_true reader_valid_start)]

open Classical in
theorem enabled_after_taker : enabled A label catalogue (taker.result label start) = [reader] := by
  unfold enabled catalogue
  rw [List.filter_cons, List.filter_cons, List.filter_nil,
    if_neg (fun h => taker_once (of_decide_eq_true h)), if_pos (decide_eq_true reader_valid)]

open Classical in
theorem enabled_after_reader : enabled A label catalogue (reader.result label start) = [taker] := by
  unfold enabled catalogue
  rw [List.filter_cons, List.filter_cons, List.filter_nil,
    if_pos (decide_eq_true taker_after_reader), if_neg (fun h => reader_once (of_decide_eq_true h))]

open Classical in
theorem enabled_forward_end :
    enabled A label catalogue (reader.result label (taker.result label start)) = [] := by
  unfold enabled
  exact List.filter_eq_nil_iff.mpr fun f member decided =>
    forward_end f member (of_decide_eq_true decided)

open Classical in
theorem enabled_backward_end :
    enabled A label catalogue (taker.result label (reader.result label start)) = [] := by
  unfold enabled
  exact List.filter_eq_nil_iff.mpr fun f member decided =>
    backward_end f member (of_decide_eq_true decided)

open Classical in
theorem frontier_zero {C : Configuration (Term signature) Nat}
    (consistent : A.Consistent C.equations) : frontier A label catalogue 0 C = [[]] := by
  rw [AnnotatedRunUnfolding.frontier, if_pos consistent]

open Classical in
theorem frontier_one_start : frontier A label catalogue 1 start = [[taker], [reader]] := by
  rw [AnnotatedRunUnfolding.frontier, enabled_start]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [frontier_zero taker_valid.firing.consistent,
    frontier_zero reader_valid_start.firing.consistent]
  rfl

open Classical in
theorem frontier_two_start :
    frontier A label catalogue 2 start = [[taker, reader], [reader, taker]] := by
  rw [AnnotatedRunUnfolding.frontier, enabled_start]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [AnnotatedRunUnfolding.frontier, AnnotatedRunUnfolding.frontier, enabled_after_taker,
    enabled_after_reader]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [frontier_zero reader_valid.firing.consistent,
    frontier_zero taker_after_reader.firing.consistent]
  rfl

theorem not_terminal_start : ¬ Terminal A label catalogue (follow label start ([] : List Run)) :=
  fun terminal => terminal taker (by simp [catalogue]) taker_valid

theorem not_terminal_taker : ¬ Terminal A label catalogue (follow label start [taker]) :=
  fun terminal => terminal reader (by simp [catalogue]) reader_valid

theorem not_terminal_reader : ¬ Terminal A label catalogue (follow label start [reader]) :=
  fun terminal => terminal taker (by simp [catalogue]) taker_after_reader

theorem terminal_forward : Terminal A label catalogue (follow label start [taker, reader]) :=
  forward_end

theorem terminal_backward : Terminal A label catalogue (follow label start [reader, taker]) :=
  backward_end

open Classical in
/-- **The terminal histories of the diamond within budget `2`**: its two interleavings. -/
theorem completed_diamond :
    completed A label catalogue 2 start = [[taker, reader], [reader, taker]] := by
  unfold completed
  rw [show List.range (2 + 1) = [0, 1, 2] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [frontier_zero (C := start) ⟨zeros, fun _ member => by cases member⟩, frontier_one_start,
    frontier_two_start]
  simp only [List.cons_append, List.nil_append]
  rw [List.filter_cons, List.filter_cons, List.filter_cons, List.filter_cons, List.filter_cons,
    List.filter_nil, if_neg (fun h => not_terminal_start (of_decide_eq_true h)),
    if_neg (fun h => not_terminal_taker (of_decide_eq_true h)),
    if_neg (fun h => not_terminal_reader (of_decide_eq_true h)),
    if_pos (decide_eq_true terminal_forward), if_pos (decide_eq_true terminal_backward)]

open Classical in
theorem diamond_branches :
    terminalBranches A label catalogue 2 start = {Quot.mk _ [taker, reader]} := by
  unfold terminalBranches
  rw [completed_diamond]
  simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil]
  rw [← AnnotatedRunUnfolding.Controls.independent_orders_share_causal_class]
  simp

open Classical in
theorem diamond_interleavings :
    interleavings A label catalogue 2 start everything (Quot.mk _ [taker, reader]) = 2 := by
  unfold interleavings
  have kept : ∀ w ∈ [[taker, reader], [reader, taker]],
      (fun w : List Run => decide (everything (ConfigurationClass.mk A (follow label start w)))) w =
        true := fun _ _ => decide_eq_true trivial
  rw [completed_diamond, List.filter_eq_self.mpr kept]
  simp only [List.map_cons, List.map_nil]
  rw [← AnnotatedRunUnfolding.Controls.independent_orders_share_causal_class]
  simp

open Classical in
/-- **A diamond in the unfolding.** For the catalogue of the taker and the reader at depth budget
`2`, the terminal histories are the two interleavings of one causal history, of amplitude `i`.
The regional amplitude is `i`, with Born weight `1`; the sum over interleavings is `2i`, with Born
weight `4`. -/
theorem diamond_in_unfolding :
    completed A label catalogue 2 start = [[taker, reader], [reader, taker]] ∧
      terminalBranches A label catalogue 2 start = {Quot.mk _ [taker, reader]} ∧
      regionalAmplitude A label phase catalogue 2 start everything = unitI ∧
      interleavingAmplitude A label phase catalogue 2 start everything = unitI + unitI ∧
      born (regionalAmplitude A label phase catalogue 2 start everything) = 1 ∧
      born (interleavingAmplitude A label phase catalogue 2 start everything) = 4 := by
  have regional : regionalAmplitude A label phase catalogue 2 start everything = unitI := by
    unfold regionalAmplitude
    rw [regionBranches_everything, diamond_branches, Finset.sum_singleton, classAmplitude_mk]
    simp [runAmplitude, phase_taker, phase_reader]
  have interleaved : interleavingAmplitude A label phase catalogue 2 start everything =
      unitI + unitI := by
    rw [interleavingAmplitude_eq_sum_count, regionBranches_everything, diamond_branches,
      Finset.sum_singleton, diamond_interleavings, classAmplitude_mk, two_nsmul]
    simp [runAmplitude, phase_taker, phase_reader]
  refine ⟨completed_diamond, diamond_branches, regional, interleaved, ?_, ?_⟩
  · rw [regional, born_unitI]
  · rw [interleaved, born_double, born_unitI]
    norm_num

end Diamond

/-! ## Incomplete is not amplitude zero -/

namespace Budget

open AnnotatedRuns.Controls (taker start taker_valid)

/-- After the taker, the taker is refused: it took `0`. -/
theorem taker_once : ¬ taker.Valid A label (taker.result label start) :=
  refused_of_absent (o := 0) (by simp [taker]) (by decide)

theorem open_zero : ¬ Closed A label [taker] 0 start :=
  AnnotatedRunBranchCollection.Controls.Status.open_world

theorem closed_one : Closed A label [taker] 1 start := by
  intro word member
  obtain ⟨length, _, covered⟩ := (mem_frontier A label [taker] 1 start word).mp member
  rcases word with _ | ⟨g, _ | ⟨h, rest⟩⟩
  · simp at length
  · rw [List.mem_singleton.mp (covered g (List.mem_singleton_self g))]
    intro f inCatalogue
    rw [List.mem_singleton.mp inCatalogue]
    exact taker_once
  · simp only [List.length_cons] at length
    omega

open Classical in
theorem branches_zero : terminalBranches A label [taker] 0 start = ∅ := by
  ext trace
  simp only [Finset.notMem_empty, iff_false]
  rw [mem_terminalBranches]
  rintro ⟨word, length, _, _, terminal, _⟩
  rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp length)] at terminal
  exact terminal taker (List.mem_singleton_self _) taker_valid

open Classical in
theorem branches_one : terminalBranches A label [taker] 1 start = {Quot.mk _ [taker]} := by
  ext trace
  rw [mem_terminalBranches, Finset.mem_singleton]
  constructor
  · rintro ⟨word, length, _, covered, terminal, rfl⟩
    rcases word with _ | ⟨g, _ | ⟨h, rest⟩⟩
    · exact absurd taker_valid (terminal taker (List.mem_singleton_self _))
    · rw [List.mem_singleton.mp (covered g (List.mem_singleton_self g))]
    · simp only [List.length_cons] at length
      omega
  · rintro rfl
    exact ⟨[taker], by simp, ⟨taker_valid, taker_valid.firing.consistent⟩, by simp,
      fun f inCatalogue => by rw [List.mem_singleton.mp inCatalogue]; exact taker_once, rfl⟩

/-- **Incomplete is not amplitude zero.** With depth budget `0` the taker is still enabled: the
collection is incomplete and found no path, so its partial sum is `0`; it certifies no amplitude,
and its verdict is "incomplete". With budget `1` the frontier is closed and the regional amplitude
is `1`. -/
theorem incomplete_not_zero :
    amplitudeCollection A label (fun _ => 1) [taker] 0 start everything = .incomplete 0 ∧
      coherent (0 : Multiset Amplitude) = 0 ∧
      certifiedAmplitude (amplitudeCollection A label (fun _ => 1) [taker] 0 start everything) =
        none ∧
      interferenceVerdict (amplitudeCollection A label (fun _ => 1) [taker] 0 start everything) =
        .incomplete ∧
      amplitudeCollection A label (fun _ => 1) [taker] 1 start everything = .complete {1} ∧
      certifiedAmplitude (amplitudeCollection A label (fun _ => 1) [taker] 1 start everything) =
        some 1 := by
  have empty : branchAmplitudes A label (fun _ => 1) [taker] 0 start everything = 0 := by
    unfold branchAmplitudes
    rw [regionBranches_everything, branches_zero]
    rfl
  have single : branchAmplitudes A label (fun _ => 1) [taker] 1 start everything = {1} := by
    unfold branchAmplitudes
    rw [regionBranches_everything, branches_one, Finset.singleton_val, Multiset.map_singleton,
      classAmplitude_mk]
    simp [runAmplitude]
  have incomplete : amplitudeCollection A label (fun _ => 1) [taker] 0 start everything =
      .incomplete 0 := by
    rw [amplitudeCollection_incomplete_of_open A label _ open_zero, empty]
  have complete : amplitudeCollection A label (fun _ => 1) [taker] 1 start everything =
      .complete {1} :=
    (amplitudeCollection_eq_complete_iff A label _ [taker] 1 start everything _).mpr
      ⟨closed_one, single.symm⟩
  refine ⟨incomplete, coherent_zero, by rw [incomplete]; rfl, by rw [incomplete]; rfl, complete, ?_⟩
  rw [complete]
  simp [certifiedAmplitude, coherent]

end Budget

/-! ## An incomplete collection whose paths cancel certifies nothing -/

namespace Staged

open AnnotatedRunBranchCollection.Controls.Superpose (root first second first_valid second_valid
  first_ne_second)
open Superposed (shifted shifted_first shifted_second)

/-- The staged alternative starts: it takes the token and makes `23`. -/
def prep : Run := ⟨⟨[.const 9], [], [], [], [.const 2]⟩, [], ⟨[9], [], [23]⟩⟩

/-- The staged alternative finishes: it takes `23` and makes `24`. -/
def finish : Run := ⟨⟨[.const 2], [], [], [], [.const 2]⟩, [], ⟨[23], [], [24]⟩⟩

/-- Two alternatives of one firing and one of two. -/
def staged : List Run := [first, second, prep, finish]

theorem prep_valid : prep.Valid A label root := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [prep]⟩,
    by simp [prep]⟩
  intro equation member
  have same : equation = (.const 9, label 9) := by
    simpa [Selection.problem, Selection.equations, root, prep] using member
  subst same
  rfl

theorem finish_valid : finish.Valid A label (prep.result label root) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [finish]⟩,
    by simp [finish]⟩
  intro equation member
  have cases : equation = (.const 9, label 9) ∨ equation = (.const 2, label 23) := by
    simpa [Selection.problem, Selection.equations, Selection.result, Firing.result, root, prep,
      finish] using member
  rcases cases with rfl | rfl <;> rfl

theorem shifted_prep : shifted prep = 1 := by simp [shifted, prep]

theorem shifted_finish : shifted finish = 1 := by simp [shifted, finish]

theorem staged_cases {g : Run} (member : g ∈ staged) :
    g = first ∨ g = second ∨ g = prep ∨ g = finish := by
  simpa [staged] using member

theorem staged_takes (g : Run) (member : g ∈ staged) :
    9 ∈ g.selection.taken ∨ 23 ∈ g.selection.taken := by
  rcases staged_cases member with rfl | rfl | rfl | rfl <;> simp [first, second, prep, finish]

/-- Without the token and without `23`, nothing in the catalogue is admitted. -/
theorem staged_refused {C : Configuration (Term signature) Nat} (no9 : 9 ∉ C.present)
    (no23 : 23 ∉ C.present) : ∀ g ∈ staged, ¬ g.Valid A label C := by
  intro g member
  rcases staged_takes g member with taken | taken
  · exact refused_of_absent taken no9
  · exact refused_of_absent taken no23

theorem finish_refused_root : ¬ finish.Valid A label root :=
  refused_of_absent (o := 23) (by simp [finish]) (by decide)

theorem staged_open_one : ¬ Closed A label staged 1 root := by
  intro closed
  have member : [prep] ∈ frontier A label staged 1 root :=
    (mem_frontier A label staged 1 root [prep]).mpr
      ⟨rfl, ⟨prep_valid, prep_valid.firing.consistent⟩, by simp [staged]⟩
  exact closed [prep] member finish (by simp [staged]) finish_valid

/-- After the staged alternative, nothing is admitted. -/
theorem staged_done : Terminal A label staged (follow label root [prep, finish]) :=
  staged_refused (by decide) (by decide)

theorem staged_closed_two : Closed A label staged 2 root := by
  intro word member
  obtain ⟨length, run, covered⟩ := (mem_frontier A label staged 2 root word).mp member
  rcases word with _ | ⟨g, _ | ⟨h, _ | ⟨i, rest⟩⟩⟩
  · simp at length
  · simp at length
  · obtain ⟨gValid, hValid, -⟩ := run
    rcases staged_cases (covered g (by simp)) with rfl | rfl | rfl | rfl
    · exact absurd hValid (staged_refused (by decide) (by decide) h (covered h (by simp)))
    · exact absurd hValid (staged_refused (by decide) (by decide) h (covered h (by simp)))
    · rcases staged_cases (covered h (by simp)) with rfl | rfl | rfl | rfl
      · exact absurd hValid (refused_of_absent (o := 9) (by simp [first]) (by decide))
      · exact absurd hValid (refused_of_absent (o := 9) (by simp [second]) (by decide))
      · exact absurd hValid (refused_of_absent (o := 9) (by simp [prep]) (by decide))
      · exact staged_done
    · exact absurd gValid finish_refused_root
  · simp only [List.length_cons] at length
    omega

open Classical in
theorem staged_branches_one :
    terminalBranches A label staged 1 root = {Quot.mk _ [first], Quot.mk _ [second]} := by
  ext trace
  rw [mem_terminalBranches, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨word, length, run, covered, terminal, rfl⟩
    rcases word with _ | ⟨g, _ | ⟨h, rest⟩⟩
    · exact absurd first_valid (terminal first (by simp [staged]))
    · rcases staged_cases (covered g (List.mem_singleton_self g)) with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd finish_valid (terminal finish (by simp [staged]))
      · exact absurd run.1 finish_refused_root
    · simp only [List.length_cons] at length
      omega
  · rintro (rfl | rfl)
    · exact ⟨[first], by simp, ⟨first_valid, first_valid.firing.consistent⟩, by simp [staged],
        staged_refused (by decide) (by decide), rfl⟩
    · exact ⟨[second], by simp, ⟨second_valid, second_valid.firing.consistent⟩, by simp [staged],
        staged_refused (by decide) (by decide), rfl⟩

open Classical in
theorem staged_branches_two :
    terminalBranches A label staged 2 root =
      {Quot.mk _ [first], Quot.mk _ [second], Quot.mk _ [prep, finish]} := by
  ext trace
  rw [mem_terminalBranches, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨word, length, run, covered, terminal, rfl⟩
    rcases word with _ | ⟨g, _ | ⟨h, _ | ⟨i, rest⟩⟩⟩
    · exact absurd first_valid (terminal first (by simp [staged]))
    · rcases staged_cases (covered g (List.mem_singleton_self g)) with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact absurd finish_valid (terminal finish (by simp [staged]))
      · exact absurd run.1 finish_refused_root
    · obtain ⟨gValid, hValid, -⟩ := run
      rcases staged_cases (covered g (by simp)) with rfl | rfl | rfl | rfl
      · exact absurd hValid (staged_refused (by decide) (by decide) h (covered h (by simp)))
      · exact absurd hValid (staged_refused (by decide) (by decide) h (covered h (by simp)))
      · rcases staged_cases (covered h (by simp)) with rfl | rfl | rfl | rfl
        · exact absurd hValid (refused_of_absent (o := 9) (by simp [first]) (by decide))
        · exact absurd hValid (refused_of_absent (o := 9) (by simp [second]) (by decide))
        · exact absurd hValid (refused_of_absent (o := 9) (by simp [prep]) (by decide))
        · exact Or.inr (Or.inr rfl)
      · exact absurd gValid finish_refused_root
    · simp only [List.length_cons] at length
      omega
  · rintro (rfl | rfl | rfl)
    · exact ⟨[first], by simp, ⟨first_valid, first_valid.firing.consistent⟩, by simp [staged],
        staged_refused (by decide) (by decide), rfl⟩
    · exact ⟨[second], by simp, ⟨second_valid, second_valid.firing.consistent⟩, by simp [staged],
        staged_refused (by decide) (by decide), rfl⟩
    · exact ⟨[prep, finish], by simp,
        ⟨prep_valid, finish_valid, finish_valid.firing.consistent⟩, by simp [staged], staged_done,
        rfl⟩

theorem first_ne_staged :
    (Quot.mk _ [first] : CausalClass A label root) ≠ Quot.mk _ [prep, finish] := fun same => by
  have cards := congrArg Multiset.card (class_bag same)
  simp at cards

theorem second_ne_staged :
    (Quot.mk _ [second] : CausalClass A label root) ≠ Quot.mk _ [prep, finish] := fun same => by
  have cards := congrArg Multiset.card (class_bag same)
  simp at cards

open Classical in
theorem staged_paths_one :
    branchAmplitudes A label shifted staged 1 root everything = {1, -1} := by
  unfold branchAmplitudes
  have notFirst : (Quot.mk _ [first] : CausalClass A label root) ∉
      ({Quot.mk _ [second]} : Finset (CausalClass A label root)) := by
    rw [Finset.mem_singleton]
    exact fun same => first_ne_second (single_class_injective same)
  rw [regionBranches_everything, staged_branches_one, Finset.insert_val_of_notMem notFirst,
    Finset.singleton_val]
  simp [classAmplitude_mk, runAmplitude, shifted_first, shifted_second]

open Classical in
theorem staged_paths_two :
    branchAmplitudes A label shifted staged 2 root everything = {1, -1, 1} := by
  unfold branchAmplitudes
  have notFirst : (Quot.mk _ [first] : CausalClass A label root) ∉
      ({Quot.mk _ [second], Quot.mk _ [prep, finish]} : Finset (CausalClass A label root)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun same => first_ne_second (single_class_injective same), first_ne_staged⟩
  have notSecond : (Quot.mk _ [second] : CausalClass A label root) ∉
      ({Quot.mk _ [prep, finish]} : Finset (CausalClass A label root)) := by
    rw [Finset.mem_singleton]
    exact second_ne_staged
  rw [regionBranches_everything, staged_branches_two, Finset.insert_val_of_notMem notFirst,
    Finset.insert_val_of_notMem notSecond, Finset.singleton_val]
  simp [classAmplitude_mk, runAmplitude, shifted_first, shifted_second, shifted_prep,
    shifted_finish]

/-- **An incomplete collection whose found paths cancel certifies nothing.** At depth budget `1`
the staged alternative is still running, so the collection is incomplete; the two paths it found,
`1` and `-1`, cancel, yet it certifies neither a cancellation nor an amplitude. At budget `2` the
frontier is closed and the regional amplitude is `1`. -/
theorem partial_cancellation_not_certified :
    ¬ Closed A label staged 1 root ∧
      amplitudeCollection A label shifted staged 1 root everything = .incomplete {1, -1} ∧
      Destructive {1, -1} ∧
      ¬ CertifiesCancellation (amplitudeCollection A label shifted staged 1 root everything) ∧
      certifiedAmplitude (amplitudeCollection A label shifted staged 1 root everything) = none ∧
      amplitudeCollection A label shifted staged 2 root everything = .complete {1, -1, 1} ∧
      certifiedAmplitude (amplitudeCollection A label shifted staged 2 root everything) =
        some 1 := by
  have incomplete : amplitudeCollection A label shifted staged 1 root everything =
      .incomplete {1, -1} := by
    rw [amplitudeCollection_incomplete_of_open A label _ staged_open_one, staged_paths_one]
  have complete : amplitudeCollection A label shifted staged 2 root everything =
      .complete {1, -1, 1} :=
    (amplitudeCollection_eq_complete_iff A label _ staged 2 root everything _).mpr
      ⟨staged_closed_two, staged_paths_two.symm⟩
  refine ⟨staged_open_one, incomplete, opposite_phase_control.2.2, ?_, ?_, complete, ?_⟩
  · rw [incomplete]
    exact id
  · rw [incomplete]
    rfl
  · rw [complete]
    have reordered : ({1, -1, 1} : Multiset Amplitude) = 1 ::ₘ {1, -1} :=
      congrArg (Multiset.cons 1) (Multiset.cons_swap (-1 : Amplitude) 1 0)
    simp only [certifiedAmplitude, Option.some.injEq]
    rw [reordered]
    exact third_path_flips.2.1

end Staged

#print axioms regionBranches_everything
#print axioms class_bag
#print axioms single_class_injective
#print axioms refused_of_absent
#print axioms Superposed.paths
#print axioms Superposed.superposed_cancel
#print axioms Superposed.superposed_reinforce
#print axioms Superposed.third_valid
#print axioms Superposed.closed₃
#print axioms Superposed.branches₃
#print axioms Superposed.paths₃
#print axioms Superposed.third_alternative_flips
#print axioms Diamond.diamond_counts_twice
#print axioms Diamond.completed_diamond
#print axioms Diamond.diamond_branches
#print axioms Diamond.diamond_interleavings
#print axioms Diamond.diamond_in_unfolding
#print axioms Budget.taker_once
#print axioms Budget.closed_one
#print axioms Budget.branches_zero
#print axioms Budget.branches_one
#print axioms Budget.incomplete_not_zero
#print axioms Staged.prep_valid
#print axioms Staged.finish_valid
#print axioms Staged.staged_open_one
#print axioms Staged.staged_closed_two
#print axioms Staged.staged_branches_one
#print axioms Staged.staged_branches_two
#print axioms Staged.staged_paths_one
#print axioms Staged.staged_paths_two
#print axioms Staged.partial_cancellation_not_certified

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns.AmplitudeRuns.AmplitudeControls
