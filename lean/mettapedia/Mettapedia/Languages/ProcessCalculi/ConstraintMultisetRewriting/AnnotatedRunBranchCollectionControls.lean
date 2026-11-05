import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunBranchCollection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunUnfoldingControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunBranchCollectionSources
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunCandidatesControls

/-!
# Controls for branch collection

* **Interleavings are one branch** (`one_branch_two_words`): the two orders of a round are one
  causal class, observed once, while the word-level collection over the two histories gives the
  answer twice.
* **Superposed alternatives are branches of one unfolding** (`superpose_two_branches`): two
  alternatives compete for one token; they are two distinct branches, the collection is
  complete, and their equal answers are both kept.
* **Duplicates are kept within and across worlds** (`probe_worlds_keep_duplicates`): two
  superposed worlds, each R17's probe store `(p 1) (p 1) (p 2)`, collapse completely to
  `(r 1)` four times and `(r 2)` twice.
* **Incompleteness is not emptiness** (`incomplete_not_complete_empty`): a world whose taker is
  still enabled at the depth budget gives an incomplete collection with no answers; a world with
  nothing to fire gives the complete empty collection.
* **The stratified cut** (`stratified_worlds`): two worlds constraining `$x` to `2` and to `1`,
  collected after their constraints, give `2` and `1`; collected before, a world would give
  `1 2`.
* **Two budgets** (`two_budgets`): over the unfolding driven by the sources, no classification
  budget or no depth budget leaves the collection incomplete; with both the frontier is closed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunBranchCollection.Controls

open AnnotatedRuns
open AnnotatedRunUnfolding (CausalClass collect frontier mem_frontier Terminal)
open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)

/-! ## Interleavings are one branch -/

namespace Interleavings

open AnnotatedRuns.Controls (label Run taker reader start)

/-- A constant observation. -/
def seven : Configuration (Term signature) Nat → Multiset Nat := fun _ => {7}

theorem seven_respects : RespectsClasses A seven := fun _ _ _ => rfl

open Classical in
/-- **Interleavings are one branch.** The two orders of the round of the taker and the reader are
one causal class, observed once; the word-level collection over both histories counts twice. -/
theorem one_branch_two_words :
    (Quot.mk _ [taker, reader] : CausalClass A label start) = Quot.mk _ [reader, taker] ∧
      ∑ trace ∈ ({Quot.mk _ [taker, reader], Quot.mk _ [reader, taker]} :
          Finset (CausalClass A label start)), observeClass A label start seven seven_respects trace =
        {7} ∧
      collect label start (fun _ => [7]) [[taker, reader], [reader, taker]] = [7, 7] := by
  have same := AnnotatedRunUnfolding.Controls.independent_orders_share_causal_class
  refine ⟨same, ?_, rfl⟩
  rw [same, Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.sum_singleton]
  rfl

end Interleavings

/-! ## Superposed alternatives are branches of one unfolding -/

namespace Superpose

open AnnotatedRuns.Controls (label Run zeros)

/-- The superposition token `9`, and nothing else. -/
def root : Configuration (Term signature) Nat := ⟨[], {9}⟩

/-- The first alternative takes the token and makes the answer `20`. -/
def first : Run := ⟨⟨[.const 9], [], [], [], [.const 2]⟩, [], ⟨[9], [], [20]⟩⟩

/-- The second alternative takes the token and makes the answer `21`, with an equal label. -/
def second : Run := ⟨⟨[.const 9], [], [], [], [.const 2]⟩, [], ⟨[9], [], [21]⟩⟩

def alternatives : List Run := [first, second]

theorem first_valid : first.Valid A label root := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [first]⟩,
    by simp [first]⟩
  intro equation member
  have same : equation = (.const 9, label 9) := by
    simpa [Selection.problem, Selection.equations, root, first] using member
  subst same
  rfl

theorem second_valid : second.Valid A label root := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [second]⟩,
    by simp [second]⟩
  intro equation member
  have same : equation = (.const 9, label 9) := by
    simpa [Selection.problem, Selection.equations, root, second] using member
  subst same
  rfl

theorem takes_token (f : Run) (member : f ∈ alternatives) : 9 ∈ f.selection.taken := by
  simp only [alternatives, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [first, second]

theorem token_gone_first : ∀ f ∈ alternatives, ¬ f.Valid A label (first.result label root) := by
  intro f member valid
  have present := valid.firing.occurrences.taken_subset
    (by simpa [Selection.commit] using takes_token f member)
  revert present
  decide

theorem token_gone_second : ∀ f ∈ alternatives, ¬ f.Valid A label (second.result label root) := by
  intro f member valid
  have present := valid.firing.occurrences.taken_subset
    (by simpa [Selection.commit] using takes_token f member)
  revert present
  decide

theorem one_alternative {g : Run} (covered : ∀ f ∈ [g], f ∈ alternatives) : g = first ∨ g = second := by
  simpa [alternatives] using covered g (List.mem_singleton_self g)

theorem closed : Closed A label alternatives 1 root := by
  intro word member
  obtain ⟨length, _, covered⟩ := (mem_frontier A label alternatives 1 root word).mp member
  rcases word with _ | ⟨g, _ | ⟨h, rest⟩⟩
  · simp at length
  · rcases one_alternative covered with rfl | rfl
    · exact token_gone_first
    · exact token_gone_second
  · simp only [List.length_cons] at length
    omega

open Classical in
theorem branches :
    terminalBranches A label alternatives 1 root = {Quot.mk _ [first], Quot.mk _ [second]} := by
  ext trace
  rw [mem_terminalBranches, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨word, length, _, covered, terminal, rfl⟩
    rcases word with _ | ⟨g, _ | ⟨h, rest⟩⟩
    · exact absurd first_valid (terminal first (by simp [alternatives]))
    · rcases one_alternative covered with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · simp only [List.length_cons] at length
      omega
  · rintro (rfl | rfl)
    · exact ⟨[first], by simp, ⟨first_valid, first_valid.firing.consistent⟩, by simp [alternatives],
        token_gone_first, rfl⟩
    · exact ⟨[second], by simp, ⟨second_valid, second_valid.firing.consistent⟩,
        by simp [alternatives], token_gone_second, rfl⟩

theorem first_ne_second : first ≠ second := fun same => by
  have made := congrArg (fun f : Run => f.selection.made) same
  simp [first, second] at made

/-- The two branches are distinct classes: round equivalence keeps the bag of firings. -/
theorem branches_distinct : (Quot.mk _ [first] : CausalClass A label root) ≠ Quot.mk _ [second] := by
  intro same
  have bags := congrArg (Quot.lift (fun w : List Run => (w : Multiset Run))
    (fun _ _ related => Multiset.coe_eq_coe.mpr (RoundEquiv.perm A label related))) same
  exact first_ne_second (Multiset.singleton_inj.mp bags)

/-- The answers at the end of a branch: the labels of the occurrences from `20` on. -/
def answers (C : Configuration (Term signature) Nat) : Multiset (Term signature) :=
  (C.present.filter fun o => 20 ≤ o).val.map label

theorem answers_respects : RespectsClasses A answers := by
  intro C D same
  unfold answers
  rw [same.2]

theorem answers_first : answers (first.result label root) = {label 20} := by
  have present : (first.result label root).present = {20} := by decide
  unfold answers
  rw [present]
  rfl

theorem answers_second : answers (second.result label root) = {label 21} := by
  have present : (second.result label root).present = {21} := by decide
  unfold answers
  rw [present]
  rfl

open Classical in
/-- **Superposed alternatives are branches of one unfolding.** Two alternatives compete for the
superposition token: they are two branches, the collection is complete, and their equal answers
are both kept. -/
theorem superpose_two_branches :
    terminalBranches A label alternatives 1 root = {Quot.mk _ [first], Quot.mk _ [second]} ∧
      (Quot.mk _ [first] : CausalClass A label root) ≠ Quot.mk _ [second] ∧
      collectWorlds A label alternatives 1 [root] answers answers_respects =
        .complete ({label 20} + {label 21}) ∧
      label 20 = label 21 := by
  refine ⟨branches, branches_distinct, (collectWorlds_eq_complete_iff A label _).mpr ⟨?_, ?_⟩, rfl⟩
  · intro world member
    rw [List.mem_singleton] at member
    subst member
    exact closed
  · classical
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    unfold branchBag
    rw [branches, Finset.sum_pair branches_distinct, observeClass_mk, observeClass_mk]
    exact congrArg₂ (· + ·) answers_first.symm answers_second.symm

end Superpose

/-! ## Duplicates are kept within and across worlds -/

namespace Probe

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Subst)
open MetaMeTTaComparison (atomAction)
open MeTTaOperationsMatch (encodedAnswers)
open MeTTaOperationsMatch.Probe (label pattern template before r one two probe_answers prepared)

/-- No further firing in either world. -/
def nothing : List (Firing Atom Subst Nat) := []

theorem closed : Closed atomAction label nothing 0 before := by
  intro word _ f member
  cases member

open Classical in
theorem branches :
    terminalBranches atomAction label nothing 0 before = {Quot.mk _ []} := by
  ext trace
  rw [mem_terminalBranches, Finset.mem_singleton]
  constructor
  · rintro ⟨word, length, _, _, _, rfl⟩
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp length)]
  · rintro rfl
    exact ⟨[], le_refl _, prepared.base, by simp, (by intro f member; cases member), rfl⟩

theorem branch_bag :
    branchBag atomAction label nothing 0 before (encodedAnswers label pattern template)
        (encodedAnswers_respects label pattern template) = {r one, r one, r two} := by
  unfold branchBag
  rw [branches, Finset.sum_singleton, observeClass_mk]
  exact probe_answers

/-- **Two superposed worlds, each the probe store, collapse completely, keeping every
duplicate.** -/
theorem probe_worlds_keep_duplicates :
    collectWorlds atomAction label nothing 0 [before, before] (encodedAnswers label pattern template)
        (encodedAnswers_respects label pattern template) =
      .complete ({r one, r one, r two} + {r one, r one, r two}) ∧
      Multiset.count (r one) ({r one, r one, r two} + {r one, r one, r two}) = 4 ∧
      Multiset.count (r two) ({r one, r one, r two} + {r one, r one, r two}) = 2 := by
  refine ⟨(collectWorlds_eq_complete_iff atomAction label _).mpr ⟨?_, ?_⟩, by decide, by decide⟩
  · intro root member
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    subst member
    exact closed
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, branch_bag]

end Probe

/-! ## Incompleteness is not emptiness -/

namespace Status

open AnnotatedRuns.Controls (label Run zeros taker start taker_valid)

/-- An observation with no answers. -/
def silent : Configuration (Term signature) Nat → Multiset Nat := fun _ => 0

theorem silent_respects : RespectsClasses A silent := fun _ _ _ => rfl

theorem silent_class (root : Configuration (Term signature) Nat) (trace : CausalClass A label root) :
    observeClass A label root silent silent_respects trace = 0 := by
  induction trace using Quot.ind
  rfl

theorem silent_bag (catalogue : List Run) (root : Configuration (Term signature) Nat) :
    branchBag A label catalogue 0 root silent silent_respects = 0 :=
  Finset.sum_eq_zero fun trace _ => silent_class root trace

/-- At depth `0` the taker is still enabled at the start: the frontier is open. -/
theorem open_world : ¬ Closed A label [taker] 0 start := by
  intro closed
  have terminal := closed [] ((mem_frontier A label [taker] 0 start []).mpr
    ⟨rfl, ⟨zeros, by intro e member; cases member⟩, by simp⟩)
  exact terminal taker (List.mem_singleton_self _) taker_valid

theorem closed_world : Closed A label ([] : List Run) 0 start := by
  intro word _ f member
  cases member

/-- **Incompleteness is not emptiness.** Both collections found nothing; one is incomplete and
the other complete. -/
theorem incomplete_not_complete_empty :
    collectWorlds A label [taker] 0 [start] silent silent_respects = .incomplete 0 ∧
      collectWorlds A label ([] : List Run) 0 [start] silent silent_respects = .complete 0 ∧
      (Collection.incomplete 0 : Collection Nat) ≠ .complete 0 := by
  refine ⟨?_, ?_, Collection.incomplete_ne_complete 0 0⟩
  · rw [collectWorlds_incomplete_of_open A label (List.mem_singleton_self start) open_world]
    simp [silent_bag]
  · refine (collectWorlds_eq_complete_iff A label 0).mpr ⟨?_, ?_⟩
    · intro root member
      rw [List.mem_singleton] at member
      subst member
      exact closed_world
    · simp [silent_bag]

end Status

/-! ## The stratified cut -/

namespace Cut

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope.Roles.Collection (collectP collectFirst)

/-- R16's measured space `(p 1) (p 2)`, collected through `(p $x)`, as a bag. -/
def answers (s : Store Unit ℕ) : Multiset ℕ := collectP s

/-- Two worlds: one constrains `$x` to `2`, the other to `1`. -/
def constraints : Bool → Steps Unit ℕ
  | true => [((), 2)]
  | false => [((), 1)]

/-- **The stratified cut.** Collected after their constraints, the two worlds give `2` and `1`;
collected before its constraint, the first world would give `1 2`. -/
theorem stratified_worlds :
    collectAtCut answers constraints [true, false] = {2, 1} ∧
      collectAtCut answers constraints [false, true] = {2, 1} ∧
      ((collectFirst answers Store.empty (constraints true)).map Prod.fst).getD 0 = {1, 2} ∧
      worldAnswers answers constraints true = {2} := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end Cut

/-! ## Two budgets: the unfolding driven by the sources -/

namespace Driven

open AnnotatedRuns.Controls (label Run zeros taker start taker_valid)
open AnnotatedRunCandidates (sourceFrontier mem_sourceFrontier_succ candidates)
open AnnotatedRunCandidates.Controls (sources gated gated_calibrated takerOne takerOne_valid
  candidates_eq catalogue contents supply driven_frontier pending_gated)

theorem start_consistent : A.Consistent start.equations :=
  ⟨zeros, by intro e member; cases member⟩

theorem taker_candidate : taker ∈ candidates catalogue contents supply := by
  rw [candidates_eq]
  exact List.mem_cons_self

/-- Nothing is admitted after either alternative: the first takes `0`, the second `1`, and both
make `2`. -/
theorem nothing_after (f : Run) (hf : f ∈ candidates catalogue contents supply) :
    ∀ g ∈ candidates catalogue contents supply, ¬ g.Valid A label (f.result label start) := by
  rw [candidates_eq] at hf ⊢
  intro g hg valid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf hg
  rcases hf with rfl | rfl <;> rcases hg with rfl | rfl
  · have present : (0 : Nat) ∈ (taker.result label start).present :=
      valid.firing.occurrences.taken_subset
        (show (0 : Nat) ∈ (taker.selection.commit (T := Term signature)).taken by
          simp [Selection.commit, taker])
    revert present
    decide
  · exact Finset.disjoint_left.mp valid.firing.occurrences.fresh
      (show (2 : Nat) ∈ (takerOne.selection.commit (T := Term signature)).made by
        simp [Selection.commit, takerOne])
      (show (2 : Nat) ∈ (taker.result label start).present by decide)
  · exact Finset.disjoint_left.mp valid.firing.occurrences.fresh
      (show (2 : Nat) ∈ (taker.selection.commit (T := Term signature)).made by
        simp [Selection.commit, taker])
      (show (2 : Nat) ∈ (takerOne.result label start).present by decide)
  · have present : (1 : Nat) ∈ (takerOne.result label start).present :=
      valid.firing.occurrences.taken_subset
        (show (1 : Nat) ∈ (takerOne.selection.commit (T := Term signature)).taken by
          simp [Selection.commit, takerOne])
    revert present
    decide

/-- **Two budgets.** With no classification budget, or with no depth budget, the collection over
the unfolding driven by the sources is incomplete; with both it is complete. -/
theorem two_budgets :
    (∃ found, sourceCollect A label sources gated 0 1 start Status.silent Status.silent_respects =
      .incomplete found) ∧
      (∃ found, sourceCollect A label sources gated 1 0 start Status.silent Status.silent_respects =
        .incomplete found) ∧
      SourceClosed A label sources gated 1 1 start := by
  classical
  refine ⟨⟨_, sourceCollect_incomplete_of_not_closed A label ?_⟩,
    ⟨_, sourceCollect_incomplete_of_not_closed A label ?_⟩, ⟨driven_frontier.2.2.1, ?_⟩⟩
  · intro closed
    have status := closed.1
    rw [driven_frontier.1] at status
    cases status
  · rintro ⟨_, ends⟩
    have member : [] ∈ (sourceFrontier A label sources gated 1 0 start).1 := by
      simp only [sourceFrontier]
      rw [if_pos start_consistent]
      exact List.mem_singleton_self _
    exact AnnotatedRunCandidates.not_none_of_valid A label (gated_calibrated start) taker_candidate
      taker_valid (ends [] member)
  · intro word member
    obtain ⟨f, admitted, rest, inRest, rfl⟩ := (mem_sourceFrontier_succ A label).mp member
    have candidate : f ∈ candidates catalogue contents supply := by
      simp only [AnnotatedRunCandidates.Sources.generateAt, AnnotatedRunCandidates.generate,
        AnnotatedRunUnfolding.known, List.mem_filter] at admitted
      exact admitted.1
    have restNil : rest = [] := by
      simp only [sourceFrontier] at inRest
      split at inRest
      · exact List.mem_singleton.mp inRest
      · cases inRest
    subst restNil
    have complete : (sources.generateAt gated 1 (f.result label start)).status = .complete :=
      AnnotatedRunCandidates.status_complete_iff.mpr (pending_gated _ 1 one_ne_zero)
    exact (AnnotatedRunCandidates.none_iff_terminal A label (gated_calibrated _)).mpr
      ⟨complete, nothing_after f candidate⟩

end Driven

#print axioms Interleavings.one_branch_two_words
#print axioms Superpose.branches
#print axioms Superpose.branches_distinct
#print axioms Superpose.superpose_two_branches
#print axioms Probe.branches
#print axioms Probe.probe_worlds_keep_duplicates
#print axioms Status.incomplete_not_complete_empty
#print axioms Cut.stratified_worlds
#print axioms Driven.nothing_after
#print axioms Driven.two_budgets

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunBranchCollection.Controls
