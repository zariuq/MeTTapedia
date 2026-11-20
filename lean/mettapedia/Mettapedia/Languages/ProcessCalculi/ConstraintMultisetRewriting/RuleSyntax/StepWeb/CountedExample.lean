import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.CountedFibres

/-!
# An equation written twice: two answers through two competing origins

The source program `Hosting.Alternatives.Controls.dupP` has the equation `(= (f) one)` written at two
sites; the two equations have one schema, so the translated program is that of the equation written
once (`Hosting.Alternatives.StepAlone.same_translation_two_bags`). The query `(f)` answers `one`
twice in the source, as HE and CeTTa answer `[1, 1]`. This module derives that bag from the held
presentation of `CountedTransitions` (a bag store of rows, one match per step, guards asked after the
firing's own tells, one knowledge store; the control rules fixed beside the store and the two
equations held in it as persistent occurrences `0` and `1`).

## The closed example

* `written_twice_answers`: the finished members of the delivered multiset are exactly the two words
  of names `[eqn 0, ret]` and `[eqn 1, ret]`, whose origins `[held 0, ret]` and `[held 1, ret]` are
  the words of complete runs of the held-rule step; each answers `one` under the agreed observer
  `Hosting.Alternatives.classAnswer`, and the source's bag of answers is the multiset of these two
  answer sets, `{one, one}`.
* `written_twice_origins`, `written_twice_rule_count`: over the call there are two origins (the
  schema's origin count is `2`, the return's `1`), so the one class by rules of the call and the return
  is counted twice by `bag_by_origin_counts`.
* `written_twice_run_fibre`: over one actual run of the set presentation (the call, then the return,
  openings and row identities fixed), exactly two actual runs of the held-rule step lie: the run
  fibre of `Interface.Bridges.LiveRules.Origins.run_fibre_card` has two elements.
* `written_twice_conflict`: the two origins **compete**: both held firings take the call's row `2`,
  and after either of them the row is gone, so no later firing takes it. They are two alternatives of
  one choice, not two firings that run together.

## Quotients

* `fresh_variant_histories`, `fresh_variants_counted_once`: two complete held histories of
  `[held 0, ret]` that differ in the fresh identities of the rows their firings make end in
  different states, and are one class, counted once.
* `opening_variants`: two different admitted held firings by the occurrence `0` over the call, with
  one selection, differing only in the opening of unknowns the equation does not use, reach one held
  state: one transition, one class. The opening enters a firing only through the opened rule, and the
  two openings agree on the rule's terms (`variant_terms`).
* `rigid_origins_apart`: `[held 0, ret]` and `[held 1, ret]` have one word of rules and one answer,
  and are two classes.

## Controls

* `once_versus_twice`: the equation written once and twice have the same translated program, so the
  same transitions of the set presentation; the held states hold one occurrence and two; the bags of
  answers are `{one}` and `{one, one}`.
* `different_equations`: with `(= (f) one)` and `(= (f) two)` the two classes have different answers,
  and the bag is `{one, two}`.
* `ordered_observer_does_not_descend`: for `(choice (ret one) (ret two))`, two complete source runs
  that differ only in the order of two returns of different alternatives (the two orders close a
  square) reach one configuration with the bag `{one, two}`, while the answers delivered so far, read
  in order, differ: an observer of ordered history does not descend through that exchange.

The answers are sets of closed terms and are computed by rewriting; the finite facts (distinct
words of names, the names of the call's move, the origin counts) are checked by `decide` and `rfl`.

## What is not shown here

No pair of firings that differ in their extensions (the frames they declare) is constructed: such
frames differ in a type of names, and their difference is not provable in general. The
ordered-history control is about the source's interleaving of different alternatives; within one
alternative no two firings can be exchanged (`adjacent_not_exchangeable`). The examples are about the
first fragment (`ret`, `apply`, `choice`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Counted.Example

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting Hosting.Alternatives
open RuleOccurrences
open Hosting.Alternatives.Controls (N D supply one f eqAt dupP q3 W0 matchedStore matchedStore_live called
  calledDone calledDone_finished calledDone_plain calledDone_answer q3_source dupP_plain matched called_plain
  q3_start q3_present)
open Hosting.Alternatives.StepAlone (onceP onceP_source matchedOnce)
open Classical

/-! ## A call that returns -/

/-- The query `(f)` mentions no opened name. -/
theorem q3_unopened : ∀ t ∈ q3.data, ∀ x ∈ support t, x.scopes = [] := by
  intro t member x inside
  simp only [q3, Comp.data, List.mem_singleton] at member
  subst member
  simp [f, sym, support, supportArgs] at inside

/-- The equation `(= (f) t)` at a site. -/
abbrev retEq (site : List ℕ) (t : MData) : SourceLanguage.Equation mkeys [] () MTy := ⟨site, f, .ret t⟩

/-- The finished alternative after a call by `(= (f) t)` returns. -/
abbrev doneWith (t : MData) : Branch mkeys [] () MTy :=
  ⟨matchedStore, .value (instantiate (copyAt mkeys 0) t), [], []⟩

/-- **A call by the equation at position `i`, then its return**, as a named history of the step,
making the rows `k₁` and `k₂`. -/
theorem call_ret_named {P : SourceLanguage.Program mkeys [] () MTy} (plainP : PlainProgram P)
    (matchedP : ∃ e ∈ P.equations, Solvable ([] ++ [(instantiate (copyAt mkeys W0.scope) e.lhs, f)]))
    {i : ℕ} {site : List ℕ} {t : MData} (get : P.equations[i]? = some (retEq site t)) {k₁ k₂ : ℕ}
    (after : P.equations.length < k₁) (later : k₁ < k₂) :
    ∃ s, NamedFrom (D := D) N P q3 [.eqn i, .ret] s k₂ ∧ Represents N P W0.fresh.scope (doneWith t) s k₂ := by
  have fresh₁ : k₁ ∉ (Hosting.start N P q3).present := by
    show k₁ ∉ insert P.equations.length (Finset.range P.equations.length)
    simp only [Finset.mem_insert, Finset.mem_range]
    omega
  have rep₀ : Represents N P W0.scope (initialBranch q3) (Hosting.start N P q3) P.equations.length :=
    start_represents N P q3 q3_unopened
  have plain₀ : PlainBranch (initialBranch (Ty := MTy) q3) := ⟨rfl, .inl ⟨_, rfl, trivial⟩⟩
  have move : NamedMove (D := D) P W0 (initialBranch q3) (.eqn i) W0.fresh
      (callBranch D W0.scope [] f [] [] (retEq site t)) :=
    NamedMove.eqn (D := D) (P := P) (w := W0) [] f [] [] i (retEq site t) get matchedP
  obtain ⟨s₁, fired₁, rep₁, _⟩ := simulation_named N plainP move rep₀ plain₀ matchedStore_live (k := k₁) fresh₁
  have retMove : NamedMove (D := D) P W0.fresh (callBranch D W0.scope [] f [] [] (retEq site t)) .ret W0.fresh
      (doneWith t) :=
    NamedMove.ret (D := D) (P := P) (w := W0.fresh) matchedStore (instantiate (copyAt mkeys 0) t) [] []
  have calledPlain : PlainBranch (callBranch D W0.scope [] f [] [] (retEq site t)) := ⟨rfl, .inl ⟨_, rfl, trivial⟩⟩
  have fresh₂' : k₂ ∉ s₁.present := by
    rw [rep₁.present]
    simp only [Finset.mem_insert, Finset.mem_range]
    omega
  obtain ⟨s₂, fired₂, rep₂, _⟩ :=
    simulation_named N plainP retMove rep₁ calledPlain matchedStore_live (k := k₂) fresh₂'
  exact ⟨s₂, Chain.snoc (Chain.single fired₁) fired₂, rep₂⟩

theorem doneWith_finished (t : MData) : Branch.Finished (D := D) (doneWith t) := ⟨rfl, _, rfl⟩

theorem doneWith_plain (t : MData) : PlainBranch (doneWith t) := ⟨rfl, .inr ⟨_, rfl⟩⟩

/-- **The class of a call that returns**: complete, finished, with the answer the equation's
right side determines. -/
theorem call_ret_class {P : SourceLanguage.Program mkeys [] () MTy} (plainP : PlainProgram P)
    (matchedP : ∃ e ∈ P.equations, Solvable ([] ++ [(instantiate (copyAt mkeys W0.scope) e.lhs, f)]))
    {i : ℕ} {site : List ℕ} {t : MData} (get : P.equations[i]? = some (retEq site t)) {g : MClosed}
    (determined : Determines matchedStore (instantiate (copyAt mkeys 0) t) g) :
    CompleteClass (D := D) N P q3 [.eqn i, .ret] ∧ FinishedClass (D := D) N P q3 [.eqn i, .ret] ∧
      classAnswer (D := D) N P q3 [.eqn i, .ret] = {g} := by
  obtain ⟨s, named, rep⟩ := call_ret_named plainP matchedP get (k₁ := P.equations.length + 1)
    (k₂ := P.equations.length + 2) (by omega) (by omega)
  have shown : stateAnswer N s (P.equations.length + 2) = {g} :=
    (answer_eq N rep (doneWith_finished t)).trans (answer_of_determines rfl determined)
  refine ⟨⟨s, _, named, fun s' => finished_still N (D := D) (supply := supply) (w := W0.fresh) plainP rep
    (doneWith_plain t) (doneWith_finished t) (s' := s')⟩,
    ⟨s, _, named, (finished_iff N rep).mp ⟨doneWith_finished t, matchedStore_live⟩⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨s', a', named', inside⟩
    rw [(answer_of_rule_word N (D := D) (P := P) q3 (ν₁ := [.eqn i, .ret]) (ν₂ := [.eqn i, .ret]) rfl named'
      named).1, shown] at inside
    exact inside
  · intro inside
    exact ⟨s, _, named, by rw [shown]; exact inside⟩

/-- **The held class of a call that returns**: the origins of the call and the return. -/
abbrev callRet (i : ℕ) : List (Use (CRule MSig) ℕ) := [.held i, .ambient (retRule N)]

theorem callRet_eq (i : ℕ) : callRet i = ([.eqn i, .ret] : List RuleName).map (origin N) := rfl

theorem call_ret_held {P : SourceLanguage.Program mkeys [] () MTy} (plainP : PlainProgram P)
    (matchedP : ∃ e ∈ P.equations, Solvable ([] ++ [(instantiate (copyAt mkeys W0.scope) e.lhs, f)]))
    {i : ℕ} {site : List ℕ} {t : MData} (get : P.equations[i]? = some (retEq site t)) {g : MClosed}
    (determined : Determines matchedStore (instantiate (copyAt mkeys 0) t) g) :
    CompleteHeldClass N P q3 (callRet i) ∧ CompleteHeldRun N P q3 (callRet i) ∧
      FinishedHeldClass N P q3 (callRet i) ∧ classAnswer (D := D) N P q3 [.eqn i, .ret] = {g} := by
  obtain ⟨complete, finished, answer⟩ := call_ret_class plainP matchedP get determined
  exact ⟨(completeHeld_map_iff N (D := D) q3 plainP trivial q3_unopened _).mpr complete,
    (completeHeldRun_map_iff N (D := D) q3 plainP trivial q3_unopened _).mpr complete,
    (finishedHeld_map_iff N (D := D) q3 plainP trivial q3_unopened _).mpr finished, answer⟩

/-- **The finished classes of the delivered multiset, when there are two named ones and two
answers.** -/
theorem finished_classes_pair {P : SourceLanguage.Program mkeys [] () MTy} {M : Multiset (List RuleName)}
    (count : ∀ ν, M.count ν = if CompleteHeldRun N P q3 (ν.map (origin N)) then 1 else 0) {ν₀ ν₁ : List RuleName}
    (apart : ν₀ ≠ ν₁) (complete₀ : CompleteHeldRun N P q3 (ν₀.map (origin N)))
    (complete₁ : CompleteHeldRun N P q3 (ν₁.map (origin N)))
    (finished₀ : FinishedHeldClass N P q3 (ν₀.map (origin N)))
    (finished₁ : FinishedHeldClass N P q3 (ν₁.map (origin N)))
    (two : Multiset.card (M.filter fun ν => FinishedHeldClass N P q3 (ν.map (origin N))) ≤ 2) :
    (M.filter fun ν => FinishedHeldClass N P q3 (ν.map (origin N))) = {ν₀, ν₁} := by
  have memOf : ∀ ν, CompleteHeldRun N P q3 (ν.map (origin N)) → FinishedHeldClass N P q3 (ν.map (origin N)) →
      ν ∈ M.filter fun ν => FinishedHeldClass N P q3 (ν.map (origin N)) := by
    intro ν complete finished
    refine Multiset.mem_filter.mpr ⟨Multiset.count_pos.mp ?_, finished⟩
    rw [count ν, if_pos complete]
    exact Nat.one_pos
  have pairNodup : ({ν₀, ν₁} : Multiset (List RuleName)).Nodup :=
    Multiset.nodup_cons.mpr ⟨fun inside => apart (Multiset.mem_singleton.mp inside), Multiset.nodup_singleton _⟩
  have le : ({ν₀, ν₁} : Multiset (List RuleName)) ≤
      M.filter fun ν => FinishedHeldClass N P q3 (ν.map (origin N)) := by
    refine (Multiset.le_iff_subset pairNodup).mpr ?_
    intro ν inside
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at inside
    rcases inside with rfl | rfl
    · exact memOf _ complete₀ finished₀
    · exact memOf _ complete₁ finished₁
  exact (Multiset.eq_of_le_of_card_le le (by simpa using two)).symm

/-! ## The closed example: an equation written twice -/

/-- **The equation written twice answers `one` twice, through the two held occurrences.** In the
delivered multiset of `bag_of_held_classes` (words of names, each counted once when the word of its
origins is that of a complete run of the held-rule step), the finished members are exactly the call by
equation `0` and the call by equation `1`, each followed by the return; their origins are
`[held 0, ret]` and `[held 1, ret]`; each answers `one` under the agreed observer `classAnswer`; the
source's bag of answers is the multiset of these two answer sets. -/
theorem written_twice_answers :
    ∃ M : Multiset (List RuleName),
      (∀ ν, M.count ν = if CompleteHeldRun N dupP q3 (ν.map (origin N)) then 1 else 0) ∧
        (M.filter fun ν => FinishedHeldClass N dupP q3 (ν.map (origin N))) = {[.eqn 0, .ret], [.eqn 1, .ret]} ∧
        ([.eqn 0, .ret] : List RuleName).map (origin N) = callRet 0 ∧
        ([.eqn 1, .ret] : List RuleName).map (origin N) = callRet 1 ∧
        classAnswer (D := D) N dupP q3 [.eqn 0, .ret] = {csym "one"} ∧
        classAnswer (D := D) N dupP q3 [.eqn 1, .ret] = {csym "one"} ∧
        ∃ C : Config mkeys [] () MTy, Runs D dupP supply (Config.initial (fun _ => 0) q3) C ∧
          C.Quiescent (D := D) dupP supply ∧
          C.answers (D := D) = (M.filter fun ν => FinishedHeldClass N dupP q3 (ν.map (origin N))).map
            (classAnswer (D := D) N dupP q3) ∧
          C.answers (D := D) = {{csym "one"}, {csym "one"}} := by
  obtain ⟨C, runs, quiet, answersC⟩ := q3_source
  obtain ⟨M, count, -, answers⟩ :=
    bag_of_held_classes N (D := D) (fun _ => 0) q3 dupP_plain trivial q3_unopened runs quiet
  obtain ⟨-, complete₀, finished₀, answer₀⟩ := call_ret_held (P := dupP) dupP_plain matched (i := 0)
    (site := [1]) (t := one) rfl (g := csym "one") ⟨matchedStore_live, fun _ _ _ => rfl⟩
  obtain ⟨-, complete₁, finished₁, answer₁⟩ := call_ret_held (P := dupP) dupP_plain matched (i := 1)
    (site := [2]) (t := one) rfl (g := csym "one") ⟨matchedStore_live, fun _ _ _ => rfl⟩
  have apart : ([.eqn 0, .ret] : List RuleName) ≠ [.eqn 1, .ret] := by decide
  have two : Multiset.card (M.filter fun ν => FinishedHeldClass N dupP q3 (ν.map (origin N))) ≤ 2 := by
    have cards := congrArg Multiset.card (answers.symm.trans answersC)
    rw [Multiset.card_map] at cards
    rw [cards]
    simp
  exact ⟨M, count, finished_classes_pair count apart complete₀ complete₁ finished₀ finished₁ two, rfl, rfl,
    answer₀, answer₁, C, runs, quiet, answers, answersC⟩

/-- **Two origins over the call, one over the return.** The schema of `(= (f) one)` is held by both
occurrences; the return is the one ambient control rule. -/
theorem written_twice_origins :
    originCount N dupP (schema N (eqAt [1])) = 2 ∧ originCount N dupP (retRule N) = 1 := by
  refine ⟨?_, originCount_control N dupP ((mem_controlRules N).mpr (Or.inl rfl))⟩
  rw [originCount_schema]
  have all : ∀ i : ℕ, (i ∈ heldIds dupP ∧ heldRule N dupP i = schema N (eqAt [1])) ↔ i ∈ Finset.range 2 := by
    intro i
    constructor
    · exact fun both => both.1
    · intro small
      refine ⟨small, ?_⟩
      rcases (by have := Finset.mem_range.mp small; omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight all), Nat.card_eq_finsetCard, Finset.card_range]

/-- **The one class by rules of the call and the return has an origin fibre of two.** In the
delivered multiset of words of names, two words lie over the word of rules of the call and the
return (`origin_fibre_card`); forgetting the names, that word of rules is counted twice
(`bag_by_rule_counts`, the coarser reading). -/
theorem written_twice_rule_count :
    originWays N dupP [schema N (eqAt [1]), retRule N] = 2 ∧
      (∃ M : Multiset (List RuleName),
        (∀ ν, M.count ν = if CompleteHeldRun N dupP q3 (ν.map (origin N)) then 1 else 0) ∧
          Multiset.card (M.filter fun ν => ν.filterMap (ruleNamed N dupP) = [schema N (eqAt [1]), retRule N]) =
            2) ∧
      ∃ E : Multiset (List (CRule MSig)),
        (∀ ρ, E.count ρ = if CompleteRuleClass (D := D) N dupP q3 ρ then originWays N dupP ρ else 0) ∧
        E.count [schema N (eqAt [1]), retRule N] = 2 ∧
        ∃ C : Config mkeys [] () MTy, Runs D dupP supply (Config.initial (fun _ => 0) q3) C ∧
          C.answers (D := D) = (E.filter (FinishedRuleClass (D := D) N dupP q3)).map
            (ruleClassAnswer (D := D) N dupP q3) ∧
          C.answers (D := D) = {{csym "one"}, {csym "one"}} := by
  obtain ⟨schemaCount, retCount⟩ := written_twice_origins
  have ways : originWays N dupP [schema N (eqAt [1]), retRule N] = 2 := by
    unfold originWays
    rw [List.map_cons, List.map_cons, List.map_nil, schemaCount, retCount]
    decide
  obtain ⟨C, runs, quiet, answersC⟩ := q3_source
  obtain ⟨complete₀, -, -, -⟩ := call_ret_held (P := dupP) dupP_plain matched (i := 0) (site := [1])
    (t := one) rfl (g := csym "one") ⟨matchedStore_live, fun _ _ _ => rfl⟩
  have completeRule : CompleteRuleClass (D := D) N dupP q3 [schema N (eqAt [1]), retRule N] :=
    ((completeHeld_iff_rule N (D := D) q3 (callRet 0)).mp complete₀).1
  obtain ⟨M, count, fibres, -, -⟩ :=
    bag_by_origin_counts N (D := D) q3 (fun _ => 0) dupP_plain trivial q3_unopened runs quiet
  obtain ⟨E, countE, answers⟩ :=
    bag_by_rule_counts N (D := D) q3 (fun _ => 0) dupP_plain trivial q3_unopened runs quiet
  refine ⟨ways, ⟨M, count, ?_⟩, E, countE, ?_, C, runs, answers, answersC⟩
  · rw [fibres, if_pos completeRule, ways]
  · rw [countE, if_pos completeRule, ways]

section RunFibre

open Interface.Bridges.LiveRules.Origins (baseEvents HeldRuns projectRun)

/-- **Two held-rule runs over one run of the set presentation.** There is an actual run of the set
presentation from the start, the call by the equations' one schema and then the return, with its
openings and row identities fixed; exactly two actual runs of the held-rule step lie over it: the
run fibre of `Interface.Bridges.LiveRules.Origins.run_fibre_card` has two elements, one for each
occurrence that holds the schema. -/
theorem written_twice_run_fibre :
    ∃ exec : (baseEvents (Interface.Frames.contextual MSig) (RuleSyntax.Contextual.declarations MSig)
        (P := controlRules N) (Q := equationRules N dupP)).Execution 2 (Hosting.start N dupP q3),
      ((baseEvents (Interface.Frames.contextual MSig) (RuleSyntax.Contextual.declarations MSig)
        (P := controlRules N) (Q := equationRules N dupP)).word exec).map Prod.fst =
          [schema N (eqAt [1]), retRule N] ∧
      Nat.card {run : HeldRuns (Interface.Frames.contextual MSig) (RuleSyntax.Contextual.declarations MSig)
          (P := controlRules N) (ids := heldIds dupP) (code := heldRule N dupP) (fun _ => ())
            (Hosting.start N dupP q3) 2 //
        projectRun (Interface.Frames.contextual MSig) (RuleSyntax.Contextual.declarations MSig) (fun _ => ())
            (offers N dupP) (Hosting.start N dupP q3) 2 run =
          (RuleSyntax.step (Interface.Frames.contextual MSig) ℕ (RuleSyntax.Contextual.declarations MSig)
            (controlRules N ∪ equationRules N dupP)).toStep.countedExecutionRunEquiv
              (fun {_} firing => (firing.rule, firing.selection)) (Hosting.start N dupP q3) 2 exec} = 2 := by
  have plain₀ : PlainBranch (initialBranch (Ty := MTy) q3) := ⟨rfl, .inl ⟨_, rfl, trivial⟩⟩
  have fresh₁ : (3 : ℕ) ∉ (Hosting.start N dupP q3).present := by
    rw [q3_present]
    decide
  have move : NamedMove (D := D) dupP W0 (initialBranch q3) (.eqn 0) W0.fresh (called [1]) :=
    NamedMove.eqn (D := D) (P := dupP) (w := W0) [] f [] [] 0 (eqAt [1]) rfl matched
  obtain ⟨s₁, fired₁, rep₁, -⟩ := simulation_named N dupP_plain move q3_start plain₀ matchedStore_live fresh₁
  have retMove : NamedMove (D := D) dupP W0.fresh (called [1]) .ret W0.fresh calledDone :=
    NamedMove.ret (D := D) (P := dupP) (w := W0.fresh) matchedStore (instantiate (copyAt mkeys 0) one) [] []
  have fresh₂ : (4 : ℕ) ∉ s₁.present := by
    rw [rep₁.present]
    decide
  obtain ⟨s₂, fired₂, -, -⟩ :=
    simulation_named N dupP_plain retMove rep₁ (called_plain [1]) matchedStore_live fresh₂
  obtain ⟨r₁, named₁, g₁, rule₁, admitted₁, -, -, result₁⟩ := fired₁
  obtain ⟨r₂, named₂, g₂, rule₂, admitted₂, -, -, -⟩ := fired₂
  subst result₁
  have schemaRule : schema N (eqAt [1]) = r₁ :=
    Option.some.inj (named₁ : some (schema N (eqAt [1])) = some r₁)
  have retRule' : retRule N = r₂ := Option.some.inj (named₂ : some (retRule N) = some r₂)
  let exec : (baseEvents (Interface.Frames.contextual MSig) (RuleSyntax.Contextual.declarations MSig)
      (P := controlRules N) (Q := equationRules N dupP)).Execution 2 (Hosting.start N dupP q3) :=
    ⟨⟨g₁, admitted₁⟩, ⟨⟨g₂, admitted₂⟩, PUnit.unit⟩⟩
  have words : ((baseEvents (Interface.Frames.contextual MSig) (RuleSyntax.Contextual.declarations MSig)
      (P := controlRules N) (Q := equationRules N dupP)).word exec).map Prod.fst =
        [schema N (eqAt [1]), retRule N] := by
    show [g₁.rule, g₂.rule] = _
    rw [rule₁, rule₂, ← schemaRule, ← retRule']
  refine ⟨exec, words, ?_⟩
  rw [held_run_fibre_card, words]
  exact written_twice_rule_count.1

end RunFibre

/-- **The two origins compete for the call.** At the start, the held firing by occurrence `0` and the
held firing by occurrence `1` each take the call's row `2`; every admitted held firing there takes
that row, and in every state it reaches the row is gone, so no firing there takes it again. -/
theorem written_twice_conflict :
    (∃ s₀ s₁ : HostState MSig,
      HeldFires N dupP (.held 0) (Hosting.start N dupP q3) 2 s₀ 3 ∧
        HeldFires N dupP (.held 1) (Hosting.start N dupP q3) 2 s₁ 3) ∧
      ∀ fr : HeldFiring N dupP (Hosting.start N dupP q3),
        fr.Admits (Interface.Frames.contextual MSig) (controlRules N) →
          fr.selection.taken = [2] ∧
            ∀ s' : HostState MSig, fr.result (Interface.Frames.contextual MSig) = heldState N dupP s' →
              2 ∉ s'.present ∧ ∀ g : HeldFiring N dupP s',
                g.Admits (Interface.Frames.contextual MSig) (controlRules N) → 2 ∉ g.selection.taken := by
  have plain₀ : PlainBranch (initialBranch (Ty := MTy) q3) := ⟨rfl, .inl ⟨_, rfl, trivial⟩⟩
  have fresh : (3 : ℕ) ∉ (Hosting.start N dupP q3).present := by
    rw [q3_present]
    decide
  refine ⟨?_, ?_⟩
  · have move₀ : NamedMove (D := D) dupP W0 (initialBranch q3) (.eqn 0) W0.fresh (called [1]) :=
      NamedMove.eqn (D := D) (P := dupP) (w := W0) [] f [] [] 0 (eqAt [1]) rfl matched
    have move₁ : NamedMove (D := D) dupP W0 (initialBranch q3) (.eqn 1) W0.fresh (called [2]) :=
      NamedMove.eqn (D := D) (P := dupP) (w := W0) [] f [] [] 1 (eqAt [2]) rfl matched
    obtain ⟨s₀, fired₀, -, -⟩ := simulation_named N dupP_plain move₀ q3_start plain₀ matchedStore_live fresh
    obtain ⟨s₁, fired₁, -, -⟩ := simulation_named N dupP_plain move₁ q3_start plain₀ matchedStore_live fresh
    exact ⟨s₀, s₁, heldFires_of_firesNamed fired₀, heldFires_of_firesNamed fired₁⟩
  · intro fr admitted
    obtain ⟨baseAdmitted, endpoint⟩ := heldFiring_project admitted
    obtain ⟨a', taken, made, fresh'⟩ := hosted_takes N q3_start baseAdmitted
    have shaped₀ : StepAlone.Shaped N dupP (Hosting.start N dupP q3) 2 :=
      ⟨q3_start.notRow, q3_start.present, q3_start.rows⟩
    obtain ⟨a'', -, made', shaped'⟩ := StepAlone.shaped_fires N shaped₀ baseAdmitted
    have same : a'' = a' := by
      rw [made] at made'
      exact (List.cons.inj made').1.symm
    have callPresent : (2 : ℕ) ∈ (Hosting.start N dupP q3).present := by
      rw [q3_present]
      decide
    have moved : a' ≠ 2 := fun h => fresh' (by rw [h]; exact callPresent)
    have length : dupP.equations.length = 2 := rfl
    refine ⟨taken, fun s' reached => ?_⟩
    have result : (toProgram fr (heldFiring_member admitted)).result (Interface.Frames.contextual MSig)
        (Hosting.start N dupP q3) = s' :=
      holding_injective (endpoint.symm.trans reached)
    have gone : (2 : ℕ) ∉ s'.present := by
      rw [← result, shaped'.present, same, Finset.mem_insert, Finset.mem_range, length]
      omega
    refine ⟨gone, fun g admittedG inside => gone ?_⟩
    exact admittedG.2.1.taken_subset (List.mem_toFinset.mpr inside)

/-! ## Quotients -/

/-- A state representing the finished call has no held firing. -/
theorem doneWith_still {s : HostState MSig} {a : ℕ}
    (rep : Represents N dupP W0.fresh.scope (doneWith one) s a) : HeldTerminal N dupP s :=
  (heldTerminal_iff N s).mpr fun s' => finished_still N (D := D) (supply := supply) (w := W0.fresh)
    dupP_plain rep (doneWith_plain one) (doneWith_finished one) (s' := s')

/-- **Fresh variants**: two complete held histories of the call by occurrence `0` and the return,
making the rows `3, 4` and `5, 6`, end in different states. -/
theorem fresh_variant_histories :
    ∃ s₁ s₂ : HostState MSig, s₁ ≠ s₂ ∧
      HeldFrom N dupP q3 (callRet 0) s₁ 4 ∧ HeldFrom N dupP q3 (callRet 0) s₂ 6 ∧
      HeldTerminal N dupP s₁ ∧ HeldTerminal N dupP s₂ := by
  obtain ⟨s₁, named₁, rep₁⟩ := call_ret_named (P := dupP) dupP_plain matched (i := 0) (site := [1]) (t := one)
    rfl (k₁ := 3) (k₂ := 4) (show 2 < 3 by omega) (by omega)
  obtain ⟨s₂, named₂, rep₂⟩ := call_ret_named (P := dupP) dupP_plain matched (i := 0) (site := [1]) (t := one)
    rfl (k₁ := 5) (k₂ := 6) (show 2 < 5 by omega) (by omega)
  refine ⟨s₁, s₂, fun same => ?_, heldFrom_of_namedFrom N (D := D) q3 named₁,
    heldFrom_of_namedFrom N (D := D) q3 named₂, doneWith_still rep₁, doneWith_still rep₂⟩
  subst same
  exact absurd (alt_row_unique N rep₁ rep₂) (by decide)

/-- **Fresh variants are one class, counted once**: in the delivered multiset of words of names the
call by equation `0` and the return is counted once, though its origins have the different complete
held histories of `fresh_variant_histories`. The law that identifies them is
`Hosting.Alternatives.answer_of_rule_word`: all histories of one word show one answer. -/
theorem fresh_variants_counted_once {M : Multiset (List RuleName)}
    (count : ∀ ν, M.count ν = if CompleteHeldRun N dupP q3 (ν.map (origin N)) then 1 else 0) :
    M.count [.eqn 0, .ret] = 1 := by
  obtain ⟨-, complete₀, -, -⟩ := call_ret_held (P := dupP) dupP_plain matched (i := 0) (site := [1])
    (t := one) rfl (g := csym "one") ⟨matchedStore_live, fun _ _ _ => rfl⟩
  have complete : CompleteHeldRun N dupP q3 (([.eqn 0, .ret] : List RuleName).map (origin N)) := complete₀
  rw [count, if_pos complete]

section OpeningVariant

/-- The start of the query `(f)` in the program written twice. -/
abbrev startTwice : HostState MSig := Hosting.start N dupP q3

/-- The rule of the call: the schema of `(= (f) one)`. -/
abbrev callRule : CRule MSig := schema N (eqAt [1])

theorem callRule_mem : callRule ∈ translate N dupP :=
  schema_mem N dupP (by simp [dupP])

/-- The frame a firing of the call extends the start's frame to, declaring the rule's unknowns. -/
abbrev callFrame : Interface.Frames.Frame MSig :=
  RuleSyntax.Contextual.extend MSig startTwice.frame callRule.locals

/-- **The call's firing with a given opening**: the call's rule, extended by its own unknowns,
taking the call's row `2` and making the row `3`. -/
def callFiring (opening : Assignment callRule.locals.arity callFrame.arity) :
    RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig) (translate N dupP) startTwice.frame :=
  ⟨callRule, callRule_mem, callRule.locals, opening, ⟨[2], [], [3]⟩, []⟩

/-- The canonical opening: each unknown to its own new name. -/
abbrev canonicalCallOpening : Assignment callRule.locals.arity callFrame.arity :=
  RuleSyntax.Contextual.canonicalOpening MSig startTwice.frame callRule.locals

/-- **Another opening**: the stack to its own new name, as in the canonical opening, and every name
of the source, which the equation does not use, to the start's own name for it. -/
def variantCallOpening : Assignment callRule.locals.arity callFrame.arity
  | .inl name => generator callFrame.arity (.inl (.inl name))
  | .inr stack => generator callFrame.arity (.inr (.inr stack))

/-- **The two openings agree on every term of the rule**: the equation `(= (f) one)` uses none of the
source's names, only the stack. -/
theorem variant_terms : ∀ t ∈ callRule.terms,
    instantiateObservation variantCallOpening t = instantiateObservation canonicalCallOpening t := by
  intro t member
  simp only [callRule, schema, RuleSyntax.Rule.terms, List.mem_append, List.mem_singleton, List.map_nil,
    List.flatMap_nil, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

/-- The varied opening is fresh: the canonical opening's instantiations serve, since the two agree on
the rule's terms. -/
theorem variant_fresh :
    (callFiring variantCallOpening).Fresh (Interface.Frames.contextual MSig) startTwice := by
  intro b g h
  obtain ⟨u, weakened, opened⟩ :=
    RuleSyntax.Contextual.canonical_fresh startTwice callRule callRule_mem ⟨[2], [], [3]⟩ [] b g h
  refine ⟨u, weakened, fun t member => ?_⟩
  show instantiateObservation u (instantiateObservation variantCallOpening t) = instantiateObservation h t
  rw [variant_terms t member]
  exact opened t member

/-- **The call's firing is admitted with every fresh opening**: the proof of `fire_simple_at`, which
uses only the freshness of the opening (`simple_amalgamate`). -/
theorem callFiring_admits {opening : Assignment callRule.locals.arity callFrame.arity}
    (fresh : (callFiring opening).Fresh (Interface.Frames.contextual MSig) startTwice) :
    (callFiring opening).Admits (Interface.Frames.contextual MSig) startTwice := by
  have simpleF : Simple (callFiring opening) 2 3 _ _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have shapes : (callFiring opening).Shapes (Interface.Frames.contextual MSig) startTwice :=
    ⟨fresh, List.nodup_singleton 2, List.nodup_singleton 3, rfl, rfl, rfl, rfl⟩
  have callPresent : (2 : ℕ) ∈ startTwice.present := by
    rw [q3_present]
    decide
  have fresh₃ : (3 : ℕ) ∉ startTwice.present := by
    rw [q3_present]
    decide
  have solvable : (Interface.Frames.contextual MSig).Solvable
      ((callFiring opening).information (Interface.Frames.contextual MSig) startTwice) := by
    obtain ⟨W, target, ρ, solved⟩ := matchedStore_live
    have reads : branchReads N (called [1]) ⟨W, target⟩ (observe (encBranch N (instantiate ρ) (called [1]))) :=
      ⟨ρ, solved, rfl⟩
    obtain ⟨h, readsB, told, _⟩ := (transfer_schema N (eqAt [1]) rfl q3_start.fresh _).mpr reads
    obtain ⟨g, known, matchedRow⟩ := (q3_start.reads _ _).mpr readsB
    obtain ⟨u, solvedU, _⟩ := simple_amalgamate simpleF fresh callPresent g h known told matchedRow.symm
    exact ⟨_, u, solvedU⟩
  exact ⟨shapes, enabled_single callPresent fresh₃, solvable, entails_of_no_checks rfl rfl⟩

/-- **Two fresh-opening variants of one firing are one transition, counted once.** At the start of
the program written twice there are two different admitted held firings by the occurrence `0` over
the call, with the same selection, differing only in the opening of unknowns the equation does not
use; they reach the same held state. Their class is one word of origins, counted once in the
delivered multiset (`fresh_variants_counted_once`); the law that makes this harmless is that the
opening enters a firing only through the opened rule (`variant_terms`). -/
theorem opening_variants :
    ∃ f₁ f₂ : HeldFiring N dupP startTwice, f₁ ≠ f₂ ∧ f₁.use = .held 0 ∧ f₂.use = .held 0 ∧
      f₁.Admits (Interface.Frames.contextual MSig) (controlRules N) ∧
      f₂.Admits (Interface.Frames.contextual MSig) (controlRules N) ∧
      f₁.selection = f₂.selection ∧
      f₁.result (Interface.Frames.contextual MSig) = f₂.result (Interface.Frames.contextual MSig) := by
  have canonicalAdmits := callFiring_admits (opening := canonicalCallOpening)
    (RuleSyntax.Contextual.canonical_fresh startTwice callRule callRule_mem ⟨[2], [], [3]⟩ [])
  have variantAdmits := callFiring_admits variant_fresh
  have available : (heldState N dupP startTwice).Available (controlRules N) (.held 0) :=
    Finset.mem_range.mpr (by decide)
  obtain ⟨f₁, member₁, use₁, same₁, admitted₁, result₁⟩ := lift_admits (Interface.Frames.contextual MSig)
    (callFiring canonicalCallOpening) canonicalAdmits available (rfl : heldRule N dupP 0 = callRule)
  obtain ⟨f₂, member₂, use₂, same₂, admitted₂, result₂⟩ := lift_admits (Interface.Frames.contextual MSig)
    (callFiring variantCallOpening) variantAdmits available (rfl : heldRule N dupP 0 = callRule)
  have apart : callFiring canonicalCallOpening ≠ callFiring variantCallOpening := by
    intro same
    obtain ⟨-, -, openings, -, -⟩ := RuleSyntax.Firing.mk.inj same
    have functions : canonicalCallOpening = variantCallOpening := eq_of_heq openings
    have atName := congrFun functions (.inl (fo [] [1] 0))
    unfold canonicalCallOpening RuleSyntax.Contextual.canonicalOpening variantCallOpening generator at atName
    injection atName with _ _ operator _
    injection operator with made
    injection made with name
    cases name
  have sameResult : (callFiring canonicalCallOpening).result (Interface.Frames.contextual MSig) startTwice =
      (callFiring variantCallOpening).result (Interface.Frames.contextual MSig) startTwice := rfl
  refine ⟨f₁, f₂, fun same => apart ?_, use₁, use₂, admitted₁, admitted₂, ?_, ?_⟩
  · subst same
    exact same₁.symm.trans same₂
  · exact (congrArg (fun g : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig) (translate N dupP)
      startTwice.frame => g.selection) same₁).trans
        (congrArg (fun g : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig) (translate N dupP)
          startTwice.frame => g.selection) same₂).symm
  · rw [result₁, result₂, sameResult]

end OpeningVariant

/-- **Rigid origins are not identified.** The calls by equation `0` and by equation `1` have one word
of rules and one answer under the agreed observer, and are two words of names, with two words of
origins, each the word of a complete run of the held-rule step. -/
theorem rigid_origins_apart :
    ([.eqn 0, .ret] : List RuleName) ≠ [.eqn 1, .ret] ∧ callRet 0 ≠ callRet 1 ∧
      (callRet 0).map (heldCode N dupP) = (callRet 1).map (heldCode N dupP) ∧
      classAnswer (D := D) N dupP q3 [.eqn 0, .ret] = classAnswer (D := D) N dupP q3 [.eqn 1, .ret] ∧
      CompleteHeldRun N dupP q3 (callRet 0) ∧ CompleteHeldRun N dupP q3 (callRet 1) := by
  obtain ⟨-, complete₀, -, answer₀⟩ := call_ret_held (P := dupP) dupP_plain matched (i := 0) (site := [1])
    (t := one) rfl (g := csym "one") ⟨matchedStore_live, fun _ _ _ => rfl⟩
  obtain ⟨-, complete₁, -, answer₁⟩ := call_ret_held (P := dupP) dupP_plain matched (i := 1) (site := [2])
    (t := one) rfl (g := csym "one") ⟨matchedStore_live, fun _ _ _ => rfl⟩
  exact ⟨by decide, fun same => absurd (Use.held.inj (List.cons.inj same).1) (by decide), rfl,
    answer₀.trans answer₁.symm, complete₀, complete₁⟩

/-- The names of the call's move in the program written twice: the two positions. -/
theorem written_twice_call_names :
    (List.range dupP.equations.length).map RuleName.eqn = [.eqn 0, .eqn 1] := by
  decide

/-! ## Controls -/

theorem onceP_plain : PlainProgram onceP := by
  intro e member
  simp only [onceP, List.mem_singleton] at member
  subst member
  trivial

/-- **Once against twice.** The equation written once and written twice translate to one set of rules,
so the step of the set presentation has the same transitions; the held-rule step is one step for every
program, and the held states hold one occurrence and two; the bags of answers are `{one}` and
`{one, one}`. -/
theorem once_versus_twice :
    translate N dupP = translate N onceP ∧
      (∀ s t : HostState MSig,
        LogicOverTheStep.StepSpan.Succ (hostStep N dupP).toStep s t ↔
          LogicOverTheStep.StepSpan.Succ (hostStep N onceP).toStep s t) ∧
      heldIds dupP ≠ heldIds onceP ∧
      (∃ M : Multiset (List RuleName),
        (∀ ν, M.count ν = if CompleteHeldRun N onceP q3 (ν.map (origin N)) then 1 else 0) ∧
          (M.filter fun ν => FinishedHeldClass N onceP q3 (ν.map (origin N))) = {[.eqn 0, .ret]} ∧
          ∃ C : Config mkeys [] () MTy, Runs D onceP supply (Config.initial (fun _ => 0) q3) C ∧
            C.Quiescent (D := D) onceP supply ∧
            C.answers (D := D) = (M.filter fun ν => FinishedHeldClass N onceP q3 (ν.map (origin N))).map
              (classAnswer (D := D) N onceP q3) ∧
            C.answers (D := D) = {{csym "one"}}) ∧
      ∃ M : Multiset (List RuleName),
        (∀ ν, M.count ν = if CompleteHeldRun N dupP q3 (ν.map (origin N)) then 1 else 0) ∧
          (M.filter fun ν => FinishedHeldClass N dupP q3 (ν.map (origin N))) = {[.eqn 0, .ret], [.eqn 1, .ret]} ∧
          ∃ C : Config mkeys [] () MTy, Runs D dupP supply (Config.initial (fun _ => 0) q3) C ∧
            C.Quiescent (D := D) dupP supply ∧
            C.answers (D := D) = (M.filter fun ν => FinishedHeldClass N dupP q3 (ν.map (origin N))).map
              (classAnswer (D := D) N dupP q3) ∧
            C.answers (D := D) = {{csym "one"}, {csym "one"}} := by
  have sameRules : translate N dupP = translate N onceP := StepAlone.same_translation_two_bags.1
  refine ⟨sameRules, fun s t => ?_, ?_, ?_, ?_⟩
  · show LogicOverTheStep.StepSpan.Succ (RuleSyntax.step (Interface.Frames.contextual MSig) ℕ
        (RuleSyntax.Contextual.declarations MSig) (translate N dupP)).toStep s t ↔
      LogicOverTheStep.StepSpan.Succ (RuleSyntax.step (Interface.Frames.contextual MSig) ℕ
        (RuleSyntax.Contextual.declarations MSig) (translate N onceP)).toStep s t
    rw [sameRules]
  · intro same
    have cards := congrArg Finset.card same
    rw [Finset.card_range, Finset.card_range] at cards
    exact absurd cards (by show ¬ ((2 : ℕ) = 1); decide)
  · obtain ⟨C, runs, quiet, answersC⟩ := onceP_source
    obtain ⟨M, count, -, answers⟩ :=
      bag_of_held_classes N (D := D) (fun _ => 0) q3 onceP_plain trivial q3_unopened runs quiet
    obtain ⟨-, complete₀, finished₀, -⟩ := call_ret_held (P := onceP) onceP_plain matchedOnce (i := 0)
      (site := [1]) (t := one) rfl (g := csym "one") ⟨matchedStore_live, fun _ _ _ => rfl⟩
    have complete : CompleteHeldRun N onceP q3 (([.eqn 0, .ret] : List RuleName).map (origin N)) := complete₀
    have member : ([.eqn 0, .ret] : List RuleName) ∈
        M.filter fun ν => FinishedHeldClass N onceP q3 (ν.map (origin N)) := by
      refine Multiset.mem_filter.mpr ⟨Multiset.count_pos.mp ?_, finished₀⟩
      rw [count, if_pos complete]
      exact Nat.one_pos
    have one' : Multiset.card (M.filter fun ν => FinishedHeldClass N onceP q3 (ν.map (origin N))) ≤ 1 := by
      have cards := congrArg Multiset.card (answers.symm.trans answersC)
      rw [Multiset.card_map] at cards
      rw [cards]
      simp
    have single : (M.filter fun ν => FinishedHeldClass N onceP q3 (ν.map (origin N))) = {[.eqn 0, .ret]} := by
      have le : ({[.eqn 0, .ret]} : Multiset (List RuleName)) ≤
          M.filter fun ν => FinishedHeldClass N onceP q3 (ν.map (origin N)) :=
        Multiset.singleton_le.mpr member
      exact (Multiset.eq_of_le_of_card_le le (by simpa using one')).symm
    exact ⟨M, count, single, C, runs, quiet, answers, answersC⟩
  · obtain ⟨M, count, pair, -, -, -, -, C, runs, quiet, answers, answersC⟩ := written_twice_answers
    exact ⟨M, count, pair, C, runs, quiet, answers, answersC⟩

/-- The datum `two`. -/
def two : MData := sym "two"

/-- **Two different equations**: `(= (f) one)` and `(= (f) two)`. -/
def twoP : SourceLanguage.Program mkeys [] () MTy := ⟨[eqAt [1], retEq [2] two], fun t => .apply t⟩

theorem twoP_plain : PlainProgram twoP := by
  intro e member
  simp only [twoP, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> trivial

theorem matchedTwo : ∃ e ∈ twoP.equations, Solvable ([] ++ [(instantiate (copyAt mkeys W0.scope) e.lhs, f)]) :=
  ⟨eqAt [1], by simp [twoP], matchedStore_live⟩

/-- The alternative the second equation makes. -/
abbrev calledTwo : Branch mkeys [] () MTy := callBranch D W0.scope [] f [] [] (retEq [2] two)

theorem doneWithTwo_answer : (doneWith two).answer (D := D) = {csym "two"} :=
  answer_of_determines rfl ⟨matchedStore_live, fun _ _ _ => rfl⟩

theorem twoP_source :
    ∃ C : Config mkeys [] () MTy, Runs D twoP supply (Config.initial (fun _ => 0) q3) C ∧
      C.Quiescent (D := D) twoP supply ∧ C.answers (D := D) = {{csym "one"}, {csym "two"}} := by
  refine ⟨⟨W0.fresh, {calledDone, doneWith two}⟩, ?_, ?_, ?_⟩
  · have s1 : SourceLanguage.Step D twoP supply (Config.initial (fun _ => 0) q3)
        ⟨W0.fresh, {called [1], calledTwo}⟩ :=
      Step.single live_nil (.apply W0 [] f [] [] matchedTwo)
    have s2 : SourceLanguage.Step D twoP supply ⟨W0.fresh, {called [1], calledTwo}⟩
        ⟨W0.fresh, {calledDone, calledTwo}⟩ :=
      Step.of_eq (rest := {calledTwo}) rfl rfl matchedStore_live (.ret W0.fresh matchedStore _ [] [])
    have s3 : SourceLanguage.Step D twoP supply ⟨W0.fresh, {calledDone, calledTwo}⟩
        ⟨W0.fresh, {calledDone, doneWith two}⟩ :=
      Step.of_eq (rest := {calledDone}) (Multiset.cons_swap _ _ _) (Multiset.pair_comm _ _) matchedStore_live
        (.ret W0.fresh matchedStore _ [] [])
    exact ((Relation.ReflTransGen.single s1).tail s2).tail s3
  · refine Config.quiescent_of_finished fun b member _ => ?_
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact calledDone_finished
    · exact doneWith_finished two
  · show Config.answers (D := D) ⟨W0.fresh, calledDone ::ₘ {doneWith two}⟩ = _
    rw [answers_cons_finished calledDone_finished matchedStore_live,
      answers_singleton (doneWith_finished two) matchedStore_live, calledDone_answer, doneWithTwo_answer]
    rfl

theorem one_answer_ne_two : ({csym "one"} : Set MClosed) ≠ {csym "two"} := by
  intro same
  have inside : csym "one" ∈ ({csym "two"} : Set MClosed) := same ▸ Set.mem_singleton _
  exact (by decide : csym "one" ≠ csym "two") (Set.mem_singleton_iff.mp inside)

/-- **Two different equations give two different answers**: the two classes of names answer `one`
and `two` under the agreed observer, and the bag is `{one, two}`. -/
theorem different_equations :
    ∃ M : Multiset (List RuleName),
      (∀ ν, M.count ν = if CompleteHeldRun N twoP q3 (ν.map (origin N)) then 1 else 0) ∧
        (M.filter fun ν => FinishedHeldClass N twoP q3 (ν.map (origin N))) = {[.eqn 0, .ret], [.eqn 1, .ret]} ∧
        classAnswer (D := D) N twoP q3 [.eqn 0, .ret] = {csym "one"} ∧
        classAnswer (D := D) N twoP q3 [.eqn 1, .ret] = {csym "two"} ∧
        classAnswer (D := D) N twoP q3 [.eqn 0, .ret] ≠ classAnswer (D := D) N twoP q3 [.eqn 1, .ret] ∧
        ∃ C : Config mkeys [] () MTy, Runs D twoP supply (Config.initial (fun _ => 0) q3) C ∧
          C.Quiescent (D := D) twoP supply ∧
          C.answers (D := D) = (M.filter fun ν => FinishedHeldClass N twoP q3 (ν.map (origin N))).map
            (classAnswer (D := D) N twoP q3) ∧
          C.answers (D := D) = {{csym "one"}, {csym "two"}} := by
  obtain ⟨C, runs, quiet, answersC⟩ := twoP_source
  obtain ⟨M, count, -, answers⟩ :=
    bag_of_held_classes N (D := D) (fun _ => 0) q3 twoP_plain trivial q3_unopened runs quiet
  obtain ⟨-, complete₀, finished₀, answer₀⟩ := call_ret_held (P := twoP) twoP_plain matchedTwo (i := 0)
    (site := [1]) (t := one) rfl (g := csym "one") ⟨matchedStore_live, fun _ _ _ => rfl⟩
  obtain ⟨-, complete₁, finished₁, answer₁⟩ := call_ret_held (P := twoP) twoP_plain matchedTwo (i := 1)
    (site := [2]) (t := two) rfl (g := csym "two") ⟨matchedStore_live, fun _ _ _ => rfl⟩
  have apart : ([.eqn 0, .ret] : List RuleName) ≠ [.eqn 1, .ret] := by decide
  have cardTwo : Multiset.card (M.filter fun ν => FinishedHeldClass N twoP q3 (ν.map (origin N))) ≤ 2 := by
    have cards := congrArg Multiset.card (answers.symm.trans answersC)
    rw [Multiset.card_map] at cards
    rw [cards]
    simp
  refine ⟨M, count, finished_classes_pair count apart complete₀ complete₁ finished₀ finished₁ cardTwo, answer₀,
    answer₁, ?_, C, runs, quiet, answers, answersC⟩
  rw [answer₀, answer₁]
  exact one_answer_ne_two

/-! ## What descends, and an observer of ordered history that does not -/

section OrderedHistory

open Hosting.Alternatives.Controls (emptyP retOne done done_finished done_answer)

/-- The query `(choice (ret one) (ret two))`. -/
def qc : Comp mkeys [] () MTy := .choice (.ret one) (.ret two)

/-- The alternative `(ret two)` with an empty store. -/
abbrev retTwo : Branch mkeys [] () MTy := ⟨[], .eval (.ret two), [], []⟩

/-- The finished alternative answering `two`. -/
abbrev doneTwo : Branch mkeys [] () MTy := ⟨[], .value two, [], []⟩

theorem doneTwo_finished : Branch.Finished (D := D) doneTwo := ⟨rfl, _, rfl⟩

theorem doneTwo_answer : doneTwo.answer (D := D) = {csym "two"} :=
  answer_of_determines rfl ⟨live_nil, fun _ _ _ => rfl⟩

/-- An alternative that has not finished is not counted. -/
theorem answers_cons_waiting {w : World mkeys [] ()} {b : Branch mkeys [] () MTy}
    {rest : Multiset (Branch mkeys [] () MTy)} (waiting : ¬ Branch.Finished (D := D) b) :
    Config.answers (D := D) (⟨w, b ::ₘ rest⟩ : Config mkeys [] () MTy) =
      Config.answers (D := D) (⟨w, rest⟩ : Config mkeys [] () MTy) := by
  unfold Config.answers
  rw [Multiset.filter_cons_of_neg _ fun both => waiting both.1]

theorem ret_waiting (t : MData) : ¬ Branch.Finished (D := D) (⟨[], .eval (.ret t), [], []⟩ : Branch mkeys [] () MTy) := by
  rintro ⟨_, v, value⟩
  cases value

/-- **An observer of ordered history does not descend.** Two complete source runs of
`(choice (ret one) (ret two))` differ only in the order of the two returns, which move different
alternatives and close a square: both orders reach one configuration, whose bag of answers is
`{one, two}`. The bag is the same; the history of delivered answers, read in order, is not:
`one` is delivered first in one run and `two` in the other. -/
theorem ordered_observer_does_not_descend :
    ∃ C₁ C₂ C₂' C₃ : Config mkeys [] () MTy,
      Runs D emptyP supply (Config.initial (fun _ => 0) qc) C₁ ∧
        SourceLanguage.Step D emptyP supply C₁ C₂ ∧ SourceLanguage.Step D emptyP supply C₂ C₃ ∧
        SourceLanguage.Step D emptyP supply C₁ C₂' ∧ SourceLanguage.Step D emptyP supply C₂' C₃ ∧
        C₃.Quiescent (D := D) emptyP supply ∧
        C₃.answers (D := D) = {{csym "one"}, {csym "two"}} ∧
        C₂.answers (D := D) = {{csym "one"}} ∧ C₂'.answers (D := D) = {{csym "two"}} ∧
        [C₁.answers (D := D), C₂.answers (D := D), C₃.answers (D := D)] ≠
          [C₁.answers (D := D), C₂'.answers (D := D), C₃.answers (D := D)] := by
  have first : SourceLanguage.Step D emptyP supply (Config.initial (fun _ => 0) qc) ⟨W0, {retOne, retTwo}⟩ :=
    Step.single live_nil (.choice W0 [] (.ret one) (.ret two) [] [])
  have oneFirst : SourceLanguage.Step D emptyP supply ⟨W0, {retOne, retTwo}⟩ ⟨W0, {done [], retTwo}⟩ :=
    Step.of_eq (rest := {retTwo}) rfl rfl live_nil (.ret W0 [] one [] [])
  have twoAfter : SourceLanguage.Step D emptyP supply ⟨W0, {done [], retTwo}⟩ ⟨W0, {done [], doneTwo}⟩ :=
    Step.of_eq (rest := {done []}) (Multiset.cons_swap _ _ _) (Multiset.pair_comm _ _) live_nil
      (.ret W0 [] two [] [])
  have twoFirst : SourceLanguage.Step D emptyP supply ⟨W0, {retOne, retTwo}⟩ ⟨W0, {retOne, doneTwo}⟩ :=
    Step.of_eq (rest := {retOne}) (Multiset.cons_swap _ _ _) (Multiset.pair_comm _ _) live_nil
      (.ret W0 [] two [] [])
  have oneAfter : SourceLanguage.Step D emptyP supply ⟨W0, {retOne, doneTwo}⟩ ⟨W0, {done [], doneTwo}⟩ :=
    Step.of_eq (rest := {doneTwo}) rfl rfl live_nil (.ret W0 [] one [] [])
  have oneSoFar : Config.answers (D := D) (⟨W0, {done [], retTwo}⟩ : Config mkeys [] () MTy) =
      {{csym "one"}} := by
    show Config.answers (D := D) ⟨W0, done [] ::ₘ retTwo ::ₘ 0⟩ = _
    rw [answers_cons_finished (done_finished []) live_nil, answers_cons_waiting (ret_waiting two),
      answers_zero, done_answer]
    rfl
  have twoSoFar : Config.answers (D := D) (⟨W0, {retOne, doneTwo}⟩ : Config mkeys [] () MTy) =
      {{csym "two"}} := by
    show Config.answers (D := D) ⟨W0, retOne ::ₘ {doneTwo}⟩ = _
    rw [answers_cons_waiting (ret_waiting one), answers_singleton doneTwo_finished live_nil, doneTwo_answer]
  have both : Config.answers (D := D) (⟨W0, {done [], doneTwo}⟩ : Config mkeys [] () MTy) =
      {{csym "one"}, {csym "two"}} := by
    show Config.answers (D := D) ⟨W0, done [] ::ₘ {doneTwo}⟩ = _
    rw [answers_cons_finished (done_finished []) live_nil, answers_singleton doneTwo_finished live_nil,
      done_answer, doneTwo_answer]
    rfl
  refine ⟨_, _, _, _, .single first, oneFirst, twoAfter, twoFirst, oneAfter, ?_, both, oneSoFar, twoSoFar, ?_⟩
  · refine Config.quiescent_of_finished fun b member _ => ?_
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact done_finished []
    · exact doneTwo_finished
  · rw [oneSoFar, twoSoFar]
    intro same
    have middle := (List.cons.inj (List.cons.inj same).2).1
    exact one_answer_ne_two (Multiset.singleton_inj.mp middle)

end OrderedHistory

#print axioms ordered_observer_does_not_descend
#print axioms call_ret_class
#print axioms call_ret_held
#print axioms written_twice_answers
#print axioms written_twice_origins
#print axioms written_twice_rule_count
#print axioms written_twice_run_fibre
#print axioms written_twice_conflict
#print axioms fresh_variant_histories
#print axioms fresh_variants_counted_once
#print axioms variant_terms
#print axioms callFiring_admits
#print axioms opening_variants
#print axioms rigid_origins_apart
#print axioms written_twice_call_names
#print axioms once_versus_twice
#print axioms twoP_source
#print axioms different_equations

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Counted.Example
