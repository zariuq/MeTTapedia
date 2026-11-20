import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.RuleClasses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ExampleChoice
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Multiplicity

/-!
# Classes of histories: what they identify, what they keep apart, and what names count

* `two_histories_one_class` (positive): the query `(ret one)` has two different complete histories
  of the step, which differ in the identity of the made row, in one class with one answer; the
  source's bag has one answer. Counting histories over-counts the bag.
* `two_classes_one_answer` (negative): the query `(choice (ret one) (ret one))` has two complete
  classes with the same answer; the source's bag has that answer twice. Classes are not identified by
  their answers.
* `duplicate_two_classes_one_rule_word`: a program with two equations that differ only in their site
  has two complete named classes with **one word of rules** and one rule set for both equations; the
  source's bag has the answer twice. A count of words of rules gives one; the names give two.
* `example_bag`: the hypotheses of `bag_of_classes` hold of the run of `ExampleChoice`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit

abbrev D := untyped.discipline
abbrev N := mettaNodes

def supply : ℕ → MClosed := fun _ => csym "space"

def one : MData := sym "one"

abbrev W0 : World mkeys [] () := ⟨0, 0, fun _ => 0⟩

/-- The program with no equations. -/
def emptyP : SourceLanguage.Program mkeys [] () MTy := ⟨[], fun t => .apply t⟩

theorem emptyP_plain : PlainProgram emptyP := by
  intro e member
  cases member

theorem one_unopened (c : Comp mkeys [] () MTy) (data : c.data ⊆ [one]) :
    ∀ t ∈ c.data, ∀ x ∈ support t, x.scopes = [] := by
  intro t member x inside
  have isOne := List.mem_singleton.mp (data member)
  subst isOne
  simp [one, sym, support, supportArgs] at inside

theorem one_determined (K : List (Constraint mkeys [] ())) (live : Solvable K) :
    Determines K one (csym "one") :=
  ⟨live, fun _ _ _ => rfl⟩

/-- The finished alternative answering `one`. -/
abbrev done (K : List (Constraint mkeys [] ())) : Branch mkeys [] () MTy := ⟨K, .value one, [], []⟩

theorem done_finished (K : List (Constraint mkeys [] ())) : Branch.Finished (D := D) (done K) := ⟨rfl, _, rfl⟩

theorem done_plain (K : List (Constraint mkeys [] ())) : PlainBranch (done K) := ⟨rfl, .inr ⟨_, rfl⟩⟩

theorem done_answer : (done []).answer (D := D) = {csym "one"} :=
  answer_of_determines rfl (one_determined [] live_nil)

/-- A state representing the finished alternative has no firing. -/
theorem done_terminal {P : SourceLanguage.Program mkeys [] () MTy} (plainP : PlainProgram P)
    {K : List (Constraint mkeys [] ())} {s : HostState MSig} {k : ℕ} (rep : Represents N P 0 (done K) s k) :
    Terminal N P s :=
  fun s' => finished_still N (D := D) (supply := supply) (w := W0) plainP rep (done_plain K) (done_finished K)
    (s' := s')

/-! ## Two histories, one class -/

def q1 : Comp mkeys [] () MTy := .ret one

theorem q1_start : Represents N emptyP 0 (initialBranch q1) (Hosting.start N emptyP q1) 0 :=
  start_represents N emptyP q1 (one_unopened q1 (by simp [q1, Comp.data]))

theorem q1_present : (Hosting.start N emptyP q1).present = {0} := rfl

theorem q1_fires (k : ℕ) (hk : k ≠ 0) :
    ∃ s, FiresNamed N emptyP .ret (Hosting.start N emptyP q1) 0 s k ∧ Represents N emptyP 0 (done []) s k := by
  have move : NamedMove (D := D) emptyP W0 (initialBranch q1) .ret W0 (done []) := .ret [] one [] []
  have plain : PlainBranch (initialBranch (Ty := MTy) q1) := ⟨rfl, .inl ⟨_, rfl, trivial⟩⟩
  obtain ⟨s, fired, rep, _⟩ := simulation_named N emptyP_plain move q1_start plain live_nil (k := k)
    (by rw [q1_present, Finset.mem_singleton]; exact hk)
  exact ⟨s, fired, rep⟩

theorem q1_source :
    ∃ C : Config mkeys [] () MTy, Runs D emptyP supply (Config.initial (fun _ => 0) q1) C ∧
      C.Quiescent (D := D) emptyP supply ∧ C.answers (D := D) = {{csym "one"}} := by
  refine ⟨⟨W0, {done []}⟩, .single (Step.single live_nil (.ret W0 [] one [] [])), Config.quiescent_single, ?_⟩
  rw [answers_singleton (done_finished []) live_nil, done_answer]

/-- **Two different complete histories of one class.** -/
theorem q1_two_histories :
    ∃ s₁ s₂ : HostState MSig, s₁ ≠ s₂ ∧ NamedFrom (D := D) N emptyP q1 [.ret] s₁ 1 ∧
      NamedFrom (D := D) N emptyP q1 [.ret] s₂ 2 ∧ Terminal N emptyP s₁ ∧ Terminal N emptyP s₂ := by
  obtain ⟨s₁, fired₁, rep₁⟩ := q1_fires 1 one_ne_zero
  obtain ⟨s₂, fired₂, rep₂⟩ := q1_fires 2 two_ne_zero
  refine ⟨s₁, s₂, ?_, Chain.single fired₁, Chain.single fired₂, done_terminal emptyP_plain rep₁,
    done_terminal emptyP_plain rep₂⟩
  intro same
  subst same
  have rows := alt_row_unique N rep₁ rep₂
  omega

/-- The histories of one class show one answer. -/
theorem q1_one_answer {s₁ s₂ : HostState MSig} {a₁ a₂ : ℕ}
    (chain₁ : NamedFrom (D := D) N emptyP q1 [.ret] s₁ a₁) (chain₂ : NamedFrom (D := D) N emptyP q1 [.ret] s₂ a₂) :
    stateAnswer N s₁ a₁ = stateAnswer N s₂ a₂ :=
  (answer_of_rule_word N (D := D) (P := emptyP) q1 (ν₁ := [.ret]) (ν₂ := [.ret]) rfl chain₁ chain₂).1

/-! ## Two classes, one answer -/

def q2 : Comp mkeys [] () MTy := .choice (.ret one) (.ret one)

theorem q2_start : Represents N emptyP 0 (initialBranch q2) (Hosting.start N emptyP q2) 0 :=
  start_represents N emptyP q2 (one_unopened q2 (by simp [q2, Comp.data]))

theorem q2_present : (Hosting.start N emptyP q2).present = {0} := rfl

/-- The alternative `(ret one)` with an empty store. -/
abbrev retOne : Branch mkeys [] () MTy := ⟨[], .eval (.ret one), [], []⟩

theorem q2_plain : PlainBranch (initialBranch (Ty := MTy) q2) := ⟨rfl, .inl ⟨_, rfl, trivial, trivial⟩⟩

theorem retOne_plain : PlainBranch retOne := ⟨rfl, .inl ⟨_, rfl, trivial⟩⟩

/-- One history of a word that takes a side of the choice and then returns. -/
theorem side_exists (side : RuleName)
    (move : NamedMove (D := D) emptyP W0 (initialBranch q2) side W0 retOne) :
    ∃ s a, NamedFrom (D := D) N emptyP q2 [side, .ret] s a := by
  have retMove : NamedMove (D := D) emptyP W0 retOne .ret W0 (done []) := .ret [] one [] []
  obtain ⟨s₁, fired₁, rep₁, _⟩ := simulation_named N emptyP_plain move q2_start q2_plain live_nil
    (k := 1) (by rw [q2_present, Finset.mem_singleton]; exact one_ne_zero)
  have fresh : (2 : ℕ) ∉ s₁.present := by
    rw [rep₁.present]
    simp [emptyP]
  obtain ⟨s₂, fired₂, _, _⟩ := simulation_named N emptyP_plain retMove rep₁ retOne_plain live_nil
    (k := 2) fresh
  exact ⟨s₂, 2, Chain.snoc (Chain.single fired₁) fired₂⟩

/-- Every history of such a word ends in a state representing the finished alternative. -/
theorem side_every (side : RuleName)
    (move : NamedMove (D := D) emptyP W0 (initialBranch q2) side W0 retOne) :
    ∀ s a, NamedFrom (D := D) N emptyP q2 [side, .ret] s a → Represents N emptyP 0 (done []) s a := by
  intro s a reached
  have reached' : NamedFrom (D := D) N emptyP q2 ([side] ++ [.ret]) s a := reached
  obtain ⟨s₁, a₁, first, fired₂⟩ := reached'.snoc_inv
  have first' : NamedFrom (D := D) N emptyP q2 ([] ++ [side]) s₁ a₁ := first
  obtain ⟨s₀, a₀, start, fired₁⟩ := first'.snoc_inv
  obtain ⟨rfl, rfl⟩ := start.nil_inv
  obtain ⟨w₁, b₁, move₁, rep₁, plain₁⟩ :=
    reflection_named N (D := D) (w := W0) emptyP_plain q2_start q2_plain fired₁
  obtain ⟨rfl, rfl⟩ := NamedMove.unique move₁ move
  have retMove : NamedMove (D := D) emptyP W0 retOne .ret W0 (done []) := .ret [] one [] []
  obtain ⟨w₂, b₂, move₂, rep₂, _⟩ := reflection_named N (D := D) (w := W0) emptyP_plain rep₁ plain₁ fired₂
  obtain ⟨rfl, rfl⟩ := NamedMove.unique move₂ retMove
  exact rep₂

theorem side_complete (side : RuleName)
    (move : NamedMove (D := D) emptyP W0 (initialBranch q2) side W0 retOne) :
    CompleteClass (D := D) N emptyP q2 [side, .ret] := by
  obtain ⟨s, a, reached⟩ := side_exists side move
  exact ⟨s, a, reached, done_terminal emptyP_plain (side_every side move s a reached)⟩

theorem side_answer (side : RuleName)
    (move : NamedMove (D := D) emptyP W0 (initialBranch q2) side W0 retOne) :
    classAnswer (D := D) N emptyP q2 [side, .ret] = {csym "one"} := by
  obtain ⟨s, a, reached⟩ := side_exists side move
  have answerOf : ∀ s a, NamedFrom (D := D) N emptyP q2 [side, .ret] s a → stateAnswer N s a = {csym "one"} := by
    intro s a reached
    rw [answer_eq N (side_every side move s a reached) (done_finished []), done_answer]
  ext g
  constructor
  · rintro ⟨s', a', reached', shown⟩
    rwa [answerOf s' a' reached'] at shown
  · intro member
    exact ⟨s, a, reached, by rw [answerOf s a reached]; exact member⟩

theorem q2_source :
    ∃ C : Config mkeys [] () MTy, Runs D emptyP supply (Config.initial (fun _ => 0) q2) C ∧
      C.Quiescent (D := D) emptyP supply ∧ C.answers (D := D) = {{csym "one"}, {csym "one"}} := by
  refine ⟨⟨W0, {done [], done []}⟩, ?_, ?_, ?_⟩
  · have s1 : SourceLanguage.Step D emptyP supply (Config.initial (fun _ => 0) q2) ⟨W0, {retOne, retOne}⟩ :=
      Step.single live_nil (.choice W0 [] (.ret one) (.ret one) [] [])
    have s2 : SourceLanguage.Step D emptyP supply ⟨W0, {retOne, retOne}⟩ ⟨W0, {done [], retOne}⟩ :=
      Step.of_eq (rest := {retOne}) rfl rfl live_nil (.ret W0 [] one [] [])
    have s3 : SourceLanguage.Step D emptyP supply ⟨W0, {done [], retOne}⟩ ⟨W0, {done [], done []}⟩ :=
      Step.of_eq (rest := {done []}) (Multiset.cons_swap _ _ _) rfl live_nil (.ret W0 [] one [] [])
    exact ((Relation.ReflTransGen.single s1).tail s2).tail s3
  · refine Config.quiescent_of_finished fun b member _ => ?_
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at member
    rcases member with rfl | rfl <;> exact done_finished []
  · show Config.answers (D := D) ⟨W0, done [] ::ₘ {done []}⟩ = _
    rw [answers_cons_finished (done_finished []) live_nil, answers_singleton (done_finished []) live_nil,
      done_answer]
    rfl

/-- **Negative control**: two complete classes with the same answer, kept apart; the source's bag
has the answer twice. -/
theorem two_classes_one_answer :
    CompleteClass (D := D) N emptyP q2 [.left, .ret] ∧ CompleteClass (D := D) N emptyP q2 [.right, .ret] ∧
      ([.left, .ret] : List RuleName) ≠ [.right, .ret] ∧
      classAnswer (D := D) N emptyP q2 [.left, .ret] = classAnswer (D := D) N emptyP q2 [.right, .ret] ∧
      ∃ C : Config mkeys [] () MTy, Runs D emptyP supply (Config.initial (fun _ => 0) q2) C ∧
        C.Quiescent (D := D) emptyP supply ∧ C.answers (D := D) = {{csym "one"}, {csym "one"}} := by
  have leftMove : NamedMove (D := D) emptyP W0 (initialBranch q2) .left W0 retOne := .left [] _ _ [] []
  have rightMove : NamedMove (D := D) emptyP W0 (initialBranch q2) .right W0 retOne := .right [] _ _ [] []
  exact ⟨side_complete _ leftMove, side_complete _ rightMove, by decide,
    by rw [side_answer _ leftMove, side_answer _ rightMove], q2_source⟩

/-! ## Duplicate equations: two named classes, one word of rules -/

def f : MData := sym "f"

/-- The equation `(= (f) one)` at a site. -/
def eqAt (site : List ℕ) : SourceLanguage.Equation mkeys [] () MTy := ⟨site, f, .ret one⟩

/-- **Two equations that differ only in their site.** -/
def dupP : SourceLanguage.Program mkeys [] () MTy := ⟨[eqAt [1], eqAt [2]], fun t => .apply t⟩

def q3 : Comp mkeys [] () MTy := .apply f

theorem dupP_plain : PlainProgram dupP := by
  intro e member
  simp only [dupP, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> trivial

theorem q3_start : Represents N dupP 0 (initialBranch q3) (Hosting.start N dupP q3) 2 :=
  start_represents N dupP q3 (by
    intro t member x inside
    simp only [q3, Comp.data, List.mem_singleton] at member
    subst member
    simp [f, sym, support, supportArgs] at inside)

theorem q3_present : (Hosting.start N dupP q3).present = insert 2 (Finset.range 2) := rfl

/-- The store after a copy of either equation matched the call. -/
def matchedStore : List (Constraint mkeys [] ()) := [] ++ [(instantiate (copyAt mkeys 0) f, f)]

theorem matchedStore_live : Solvable matchedStore := by
  obtain ⟨X, target, σ, _⟩ := live_nil
  exact ⟨X, target, σ, fun e member => by
    simp only [matchedStore, List.nil_append, List.mem_singleton] at member
    subst member
    rfl⟩

/-- The alternative a copy of an equation makes. -/
abbrev called (site : List ℕ) : Branch mkeys [] () MTy := callBranch D W0.scope [] f [] [] (eqAt site)

/-- The finished alternative after it returns. -/
abbrev calledDone : Branch mkeys [] () MTy :=
  ⟨matchedStore, .value (instantiate (copyAt mkeys 0) one), [], []⟩

theorem calledDone_finished : Branch.Finished (D := D) calledDone := ⟨rfl, _, rfl⟩

theorem calledDone_plain : PlainBranch calledDone := ⟨rfl, .inr ⟨_, rfl⟩⟩

theorem calledDone_answer : calledDone.answer (D := D) = {csym "one"} :=
  answer_of_determines rfl ⟨matchedStore_live, fun _ _ _ => rfl⟩

theorem matched : ∃ e ∈ dupP.equations, Solvable ([] ++ [(instantiate (copyAt mkeys W0.scope) e.lhs, f)]) :=
  ⟨eqAt [1], by simp [dupP], matchedStore_live⟩

theorem called_plain (site : List ℕ) : PlainBranch (called site) := ⟨rfl, .inl ⟨_, rfl, trivial⟩⟩

/-- A complete class through equation `i`. -/
theorem dup_complete (i : ℕ) (site : List ℕ) (get : dupP.equations[i]? = some (eqAt site)) :
    CompleteClass (D := D) N dupP q3 [.eqn i, .ret] := by
  have plain : PlainBranch (initialBranch (Ty := MTy) q3) := ⟨rfl, .inl ⟨_, rfl, trivial⟩⟩
  have move : NamedMove (D := D) dupP W0 (initialBranch q3) (.eqn i) W0.fresh (called site) :=
    NamedMove.eqn (D := D) (P := dupP) (w := W0) [] f [] [] i (eqAt site) get matched
  obtain ⟨s₁, fired₁, rep₁, _⟩ := simulation_named N dupP_plain move q3_start plain matchedStore_live
    (k := 3) (by rw [q3_present]; simp)
  have retMove : NamedMove (D := D) dupP W0.fresh (called site) .ret W0.fresh calledDone :=
    NamedMove.ret (D := D) (P := dupP) (w := W0.fresh) matchedStore (instantiate (copyAt mkeys 0) one) [] []
  have fresh : (4 : ℕ) ∉ s₁.present := by
    rw [rep₁.present]
    simp [dupP]
  obtain ⟨s₂, fired₂, rep₂, _⟩ := simulation_named N dupP_plain retMove rep₁ (called_plain site)
    matchedStore_live (k := 4) fresh
  exact ⟨s₂, 4, Chain.snoc (Chain.single fired₁) fired₂, fun s' =>
    finished_still N (D := D) (supply := supply) (w := W0.fresh) dupP_plain rep₂ calledDone_plain
      calledDone_finished (s' := s')⟩

theorem q3_source :
    ∃ C : Config mkeys [] () MTy, Runs D dupP supply (Config.initial (fun _ => 0) q3) C ∧
      C.Quiescent (D := D) dupP supply ∧ C.answers (D := D) = {{csym "one"}, {csym "one"}} := by
  refine ⟨⟨W0.fresh, {calledDone, calledDone}⟩, ?_, ?_, ?_⟩
  · have s1 : SourceLanguage.Step D dupP supply (Config.initial (fun _ => 0) q3)
        ⟨W0.fresh, {called [1], called [2]}⟩ :=
      Step.single live_nil (.apply W0 [] f [] [] matched)
    have s2 : SourceLanguage.Step D dupP supply ⟨W0.fresh, {called [1], called [2]}⟩
        ⟨W0.fresh, {calledDone, called [2]}⟩ :=
      Step.of_eq (rest := {called [2]}) rfl rfl matchedStore_live (.ret W0.fresh matchedStore _ [] [])
    have s3 : SourceLanguage.Step D dupP supply ⟨W0.fresh, {calledDone, called [2]}⟩
        ⟨W0.fresh, {calledDone, calledDone}⟩ :=
      Step.of_eq (rest := {calledDone}) (Multiset.cons_swap _ _ _) rfl matchedStore_live
        (.ret W0.fresh matchedStore _ [] [])
    exact ((Relation.ReflTransGen.single s1).tail s2).tail s3
  · refine Config.quiescent_of_finished fun b member _ => ?_
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at member
    rcases member with rfl | rfl <;> exact calledDone_finished
  · show Config.answers (D := D) ⟨W0.fresh, calledDone ::ₘ {calledDone}⟩ = _
    rw [answers_cons_finished calledDone_finished matchedStore_live,
      answers_singleton calledDone_finished matchedStore_live, calledDone_answer]
    rfl

/-- **Duplicate equations**: two complete named classes, distinct, whose names denote one word of
rules; the program's translation is the translation of one of the two equations; the source's bag
has the answer twice. -/
theorem duplicate_two_classes_one_rule_word :
    CompleteClass (D := D) N dupP q3 [.eqn 0, .ret] ∧ CompleteClass (D := D) N dupP q3 [.eqn 1, .ret] ∧
      ([.eqn 0, .ret] : List RuleName) ≠ [.eqn 1, .ret] ∧
      ([.eqn 0, .ret] : List RuleName).filterMap (ruleNamed N dupP) =
        ([.eqn 1, .ret] : List RuleName).filterMap (ruleNamed N dupP) ∧
      translate N dupP = translate N (⟨[eqAt [1]], fun t => .apply t⟩ : SourceLanguage.Program mkeys [] () MTy) ∧
      ∃ C : Config mkeys [] () MTy, Runs D dupP supply (Config.initial (fun _ => 0) q3) C ∧
        C.Quiescent (D := D) dupP supply ∧ C.answers (D := D) = {{csym "one"}, {csym "one"}} :=
  ⟨dup_complete 0 [1] rfl, dup_complete 1 [2] rfl, by decide, rfl,
    translate_duplicate N ⟨[eqAt [1]], fun t => .apply t⟩ (List.mem_singleton_self _) [2], q3_source⟩

/-! ## The main theorem's hypotheses hold -/

/-- **Existence**: the run of `ExampleChoice` satisfies every hypothesis of `bag_of_classes`; its bag
of answers is the answers of the finished complete classes. -/
theorem example_bag_answers :
    ∃ M : Multiset (List RuleName),
      ExampleChoice.final.answers (D := ExampleChoice.D) =
        (@Multiset.filter _ (FinishedClass (D := ExampleChoice.D) ExampleChoice.N ExampleBeta.program
          ExampleChoice.query) (fun _ => Classical.propDecidable _) M).map
          (classAnswer (D := ExampleChoice.D) ExampleChoice.N ExampleBeta.program ExampleChoice.query) := by
  obtain ⟨M, _, answers⟩ := bag_of_classes ExampleChoice.N (supply := ExampleChoice.supply) (fun _ => 0)
    ExampleChoice.query ExampleChoice.program_plain ExampleChoice.query_plain ExampleChoice.query_unopened
    ExampleChoice.runs ExampleChoice.final_quiescent
  exact ⟨M, answers⟩

/-- **Existence for the step alone**: the run of `ExampleChoice` satisfies every hypothesis of
`bag_of_rule_classes` (its program has one equation, so its schemas are distinct). -/
theorem example_rule_bag :
    ∃ M : Multiset (List (CRule MSig)),
      ExampleChoice.final.answers (D := ExampleChoice.D) =
        (@Multiset.filter _ (FinishedRuleClass (D := ExampleChoice.D) ExampleChoice.N ExampleBeta.program
          ExampleChoice.query) (fun _ => Classical.propDecidable _) M).map
          (ruleClassAnswer (D := ExampleChoice.D) ExampleChoice.N ExampleBeta.program ExampleChoice.query) := by
  obtain ⟨M, _, answers⟩ := bag_of_rule_classes ExampleChoice.N (D := ExampleChoice.D) (P := ExampleBeta.program)
    (supply := ExampleChoice.supply) (fun _ => 0)
    ExampleChoice.query ExampleChoice.program_plain ExampleChoice.query_plain ExampleChoice.query_unopened
    (List.nodup_singleton _) ExampleChoice.runs ExampleChoice.final_quiescent
  exact ⟨M, answers⟩

/-- **The duplicate program fails exactly the hypothesis of distinct schemas**: its two equations
have one schema. -/
theorem dup_schemas_not_distinct : ¬ (dupP.equations.map (schema N)).Nodup := by
  intro nodup
  exact (List.nodup_cons.mp nodup).1 (List.mem_singleton.mpr rfl)

#print axioms example_rule_bag
#print axioms dup_schemas_not_distinct
#print axioms q1_fires
#print axioms q1_two_histories
#print axioms q1_one_answer
#print axioms example_bag_answers
#print axioms side_every
#print axioms two_classes_one_answer
#print axioms dup_complete
#print axioms duplicate_two_classes_one_rule_word

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Controls
