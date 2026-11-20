import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Multiplicity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Answers.Sets

/-!
# One translation, two bags, one state counted twice

`P1` has the equation `(= (f) one)`; `P2` has it twice, at two sites. The query is `(f)`.

* **One translation** (`same_translation`): an equation's schema does not mention its site
  (`translate_duplicate`), so the rules of `P2` are the rules of `P1`. (The hosted states differ in
  their rows: `P2`'s start has one more equation row.)
* **Two bags** (`p1_answers`, `p2_answers`, `bags_differ`): the source answers `{one}` for `P1` and
  `{one, one}` for `P2`, as real MeTTa systems do.
* **The larger bag is read off one reachable state counted twice** (`one_state_twice`): a frontier of
  `P2`'s final configuration holds the same reached state twice, and its bag is `{one, one}`. The
  multiplicity is the frontier's, taken from the source's live alternatives; the step reaches one
  state.
* **One reachable state represents two different alternatives** (`two_alternatives`): the
  representation compares readings, so "the alternative of a state" is not a function; the answers
  of a frontier read states only.

The two start states differ, so this exhibit shows that the bag is not a function of the rules. That it
is not a function of the rules and the start state together is `Answers.SameStart.bags_differ`. What
the step determines by itself is the set of answers (`Answers.answers_as_sets`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Answers.Bags

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting
open Classical

/-- The trivial discipline, with its type language on the nose (so that case analysis on moves sees it). -/
abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩
abbrev N := mettaNodes

def supply : ℕ → MClosed := fun _ => csym "space"
abbrev sp : MClosed → Multiset (Row mkeys [] ()) := fun _ => 0

def fT : MData := tuple [sym "f"]
def oneT : MData := sym "one"
def oneC : MClosed := csym "one"

/-- `(= (f) one)`. -/
def eqF : SourceLanguage.Equation mkeys [] () MTy := ⟨[400], fT, .ret oneT⟩
def P1 : SourceLanguage.Program mkeys [] () MTy := ⟨[eqF], fun t => .apply t⟩
/-- The same equation twice, at two sites. -/
def P2 : SourceLanguage.Program mkeys [] () MTy := ⟨[eqF, ⟨[401], fT, .ret oneT⟩], fun t => .apply t⟩

/-- The query `(f)`. -/
def q : Comp mkeys [] () MTy := .apply fT

/-- **One translation.** -/
theorem same_translation : translate N P2 = translate N P1 :=
  translate_duplicate N P1 (List.mem_singleton_self _) [401]

abbrev X : Branch mkeys [] () MTy := ⟨[(fT, fT)], .eval (.ret oneT), [], []⟩
abbrev Y : Branch mkeys [] () MTy := ⟨[(fT, fT)], .value oneT, [], []⟩

abbrev W0 : World mkeys [] () := ⟨0, 0, sp⟩
abbrev W1 : World mkeys [] () := ⟨1, 0, sp⟩

theorem live_ff : Solvable ([(fT, fT)] : List (Constraint mkeys [] ())) :=
  ⟨Empty, noNames, closeNames [] (csym "a"), fun c member => by
    simp only [List.mem_singleton] at member
    subst member
    rfl⟩

theorem determines_one : Determines ([(fT, fT)] : List (Constraint mkeys [] ())) oneT oneC :=
  ⟨live_ff, fun _ _ _ => rfl⟩

theorem matched1 : ∃ e' ∈ P1.equations, Solvable ([] ++ [(instantiate (copyAt mkeys 0) e'.lhs, fT)]) :=
  ⟨eqF, List.mem_singleton_self _, live_ff⟩

theorem matched2 : ∃ e' ∈ P2.equations, Solvable ([] ++ [(instantiate (copyAt mkeys 0) e'.lhs, fT)]) :=
  ⟨eqF, List.mem_cons_self, live_ff⟩

def final1 : Config mkeys [] () MTy := ⟨W1, {Y}⟩
def final2 : Config mkeys [] () MTy := ⟨W1, {Y, Y}⟩

theorem p1_runs : Runs D P1 supply (Config.initial sp q) final1 := by
  refine Relation.ReflTransGen.tail (b := ⟨W1, {X}⟩) ?_ (step_one live_ff (.ret _ _ _ _ _))
  exact Relation.ReflTransGen.single (Step.of_eq (rest := 0) rfl rfl live_nil (.apply W0 [] fT [] [] matched1))

theorem p2_runs : Runs D P2 supply (Config.initial sp q) final2 := by
  refine Relation.ReflTransGen.tail (b := ⟨W1, {Y, X}⟩) ?_
    (Step.of_eq (D := D) (P := P2) (supply := supply) (b := X) (rest := {Y}) (Multiset.cons_swap _ _ _) rfl
      live_ff (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨W1, {X, X}⟩) ?_
    (Step.of_eq (D := D) (P := P2) (supply := supply) (b := X) (rest := {X}) rfl rfl live_ff (.ret _ _ _ _ _))
  exact Relation.ReflTransGen.single (Step.of_eq (rest := 0) rfl rfl live_nil (.apply W0 [] fT [] [] matched2))

/-- **`P1` answers `{one}`.** -/
theorem p1_answers : Config.answers (D := D) final1 = {{oneC}} := by
  show Config.answers (D := D) ⟨W1, {Y}⟩ = _
  rw [answers_singleton (D := D) ⟨rfl, _, rfl⟩ live_ff, answer_of_determines rfl determines_one]

/-- **`P2` answers `{one, one}`.** -/
theorem p2_answers : Config.answers (D := D) final2 = {{oneC}, {oneC}} := by
  show Config.answers (D := D) ⟨W1, Y ::ₘ {Y}⟩ = _
  rw [answers_cons_finished (D := D) ⟨rfl, _, rfl⟩ live_ff, answers_singleton (D := D) ⟨rfl, _, rfl⟩ live_ff,
    answer_of_determines rfl determines_one]
  rfl

/-- **The two bags differ.** -/
theorem bags_differ : Config.answers (D := D) final1 ≠ Config.answers (D := D) final2 := by
  rw [p1_answers, p2_answers]
  intro same
  have := congrArg Multiset.card same
  simp at this

theorem q_unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [] := by
  intro t member x inside
  simp only [q, Comp.data, List.mem_singleton] at member
  subst member
  simp [fT, tuple, tupleArgs, sym, support, supportArgs] at inside

/-- **`P2`'s bag is read off one reachable state, counted twice.** -/
theorem one_state_twice :
    ∃ s a, Relation.ReflTransGen (Fires N P2) (Hosting.start N P2 q) s ∧
      Frontier (D := D) N P2 final2
        ({(Y, s, a), (Y, s, a)} : Multiset (Branch mkeys [] () D.Ty × HostState MSig × ℕ)) ∧
      frontierAnswers (D := D) N
        ({(Y, s, a), (Y, s, a)} : Multiset (Branch mkeys [] () D.Ty × HostState MSig × ℕ)) = {{oneC}, {oneC}} := by
  have plainP : PlainProgram P2 := by
    intro e' member
    simp only [P2, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> trivial
  have rep0 := start_represents N P2 q q_unopened
  have plain0 : PlainBranch (initialBranch (Ty := MTy) q) := ⟨rfl, .inl ⟨q, rfl, trivial⟩⟩
  have moveApply : Move D P2 supply W0 (initialBranch q) W1
      ((P2.equations.map (callBranch D 0 [] fT [] [])) : Multiset (Branch mkeys [] () MTy)) :=
    .apply W0 [] fT [] [] matched2
  have childX : X ∈ ((P2.equations.map (callBranch D 0 [] fT [] [])) : Multiset (Branch mkeys [] () MTy)) :=
    Multiset.mem_coe.mpr (List.mem_map.mpr ⟨eqF, List.mem_cons_self, rfl⟩)
  obtain ⟨s1, a1, fires1, rep1, plain1⟩ := simulation N (D := D) plainP moveApply rep0 plain0 childX live_ff
  have moveRet : Move D P2 supply W1 X W1 {Y} := .ret W1 [(fT, fT)] oneT [] []
  obtain ⟨s2, a2, fires2, rep2, plain2⟩ :=
    simulation N (D := D) plainP moveRet rep1 plain1 (Multiset.mem_singleton_self _) live_ff
  have frontier : Frontier (D := D) N P2 final2 {(Y, s2, a2), (Y, s2, a2)} := by
    refine ⟨?_, ?_⟩
    · have allLive : ∀ b ∈ final2.branches, Solvable b.store := by
        intro b member
        have same : b = Y := by simpa [final2] using member
        rw [same]
        exact live_ff
      rw [Multiset.filter_eq_self.mpr allLive]
      rfl
    · intro x member
      have same : x = (Y, s2, a2) := by simpa using member
      rw [same]
      exact ⟨rep2, plain2⟩
  refine ⟨s2, a2, (Relation.ReflTransGen.single fires1).tail fires2, frontier, ?_⟩
  rw [← frontier_answers N frontier, p2_answers]

/-! ## One reachable state, two alternatives -/

/-- The same answer with an empty store. -/
abbrev Y' : Branch mkeys [] () MTy := ⟨[], .value oneT, [], []⟩

theorem models_Y' {B : Interface.Frames.Frame MSig} (σ : Assignment (fam mkeys) B.arity) : Models σ Y'.store := by
  intro c member
  cases member

theorem models_Y {B : Interface.Frames.Frame MSig} (σ : Assignment (fam mkeys) B.arity) : Models σ Y.store := by
  intro c member
  simp only [List.mem_singleton] at member
  subst member
  rfl

theorem below_Y' (n : ℕ) : BranchBelow n Y' := by
  refine ⟨?_, ?_, ?_⟩
  · intro c member
    cases member
  · intro t member
    simp only [focusData, List.mem_singleton] at member
    subst member
    exact fun _ _ _ => rfl
  · intro fr member
    cases member

theorem same_readings (B : Interface.Frames.Frame MSig) (r : Observation MSig B.arity) :
    branchReads N Y B r ↔ branchReads N Y' B r := by
  constructor
  · rintro ⟨σ, _, same⟩
    exact ⟨σ, ⟨models_Y' σ, same⟩⟩
  · rintro ⟨σ, _, same⟩
    exact ⟨σ, ⟨models_Y σ, same⟩⟩

theorem represents_both {n : ℕ} {s : HostState MSig} {a : ℕ} (rep : Represents N P1 n Y s a) :
    Represents N P1 n Y' s a :=
  ⟨rep.notRow, rep.present, fun B r => (rep.reads B r).trans (same_readings B r), rep.rows, rep.independent,
    below_Y' n, rfl⟩

/-- **A reachable state represents two different alternatives**: `Represents` is equality of readings,
so "the alternative of a state" is not a function; `frontierAnswers` reads states only. -/
theorem two_alternatives :
    ∃ s a, Relation.ReflTransGen (Fires N P1) (Hosting.start N P1 q) s ∧
      Represents N P1 1 Y s a ∧ Represents N P1 1 Y' s a ∧ Y ≠ Y' := by
  have plainP : PlainProgram P1 := by
    intro e' member
    rw [List.mem_singleton.mp member]
    trivial
  have rep0 := start_represents N P1 q q_unopened
  have plain0 : PlainBranch (initialBranch (Ty := MTy) q) := ⟨rfl, .inl ⟨q, rfl, trivial⟩⟩
  have moveApply : Move D P1 supply W0 (initialBranch q) W1
      ((P1.equations.map (callBranch D 0 [] fT [] [])) : Multiset (Branch mkeys [] () MTy)) :=
    .apply W0 [] fT [] [] matched1
  have childX : X ∈ ((P1.equations.map (callBranch D 0 [] fT [] [])) : Multiset (Branch mkeys [] () MTy)) :=
    Multiset.mem_coe.mpr (List.mem_map.mpr ⟨eqF, List.mem_singleton_self _, rfl⟩)
  obtain ⟨s1, a1, fires1, rep1, plain1⟩ := simulation N (D := D) plainP moveApply rep0 plain0 childX live_ff
  have moveRet : Move D P1 supply W1 X W1 {Y} := .ret W1 [(fT, fT)] oneT [] []
  obtain ⟨s2, a2, fires2, rep2, _⟩ :=
    simulation N (D := D) plainP moveRet rep1 plain1 (Multiset.mem_singleton_self _) live_ff
  refine ⟨s2, a2, (Relation.ReflTransGen.single fires1).tail fires2, rep2, represents_both rep2, ?_⟩
  intro same
  have := congrArg Branch.store same
  simp at this

#print axioms same_translation
#print axioms p1_runs
#print axioms p2_runs
#print axioms p1_answers
#print axioms p2_answers
#print axioms bags_differ
#print axioms one_state_twice
#print axioms two_alternatives

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Answers.Bags
