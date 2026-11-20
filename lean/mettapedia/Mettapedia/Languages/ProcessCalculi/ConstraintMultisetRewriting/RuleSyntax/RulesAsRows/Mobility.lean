import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Untagged

/-!
# Codes received in rows: outside every closed fragment, inside the tags of the knowledge

**The limit of closed fragments.** A closed fragment makes only data rows and literal codes of its own
rules (`ClosedFragment.made`). The rule that takes a message and makes, as a row, the code the message
carries (`relay`) is in the fragment (`relay_fragment`) and in no closed fragment (`relay_outside`), so
no theorem stated for closed fragments covers a store that holds its code. Fired by the stored-rule
program from a store tagged by syntax (`relayFiring_admitted`), it reaches a store that no set of rules
tags by syntax (`relayed_untagged`), although at every solution the made row is the code of `second`
(`relayed_value`): under the syntactic tags, codes do not travel.

**The tags of the knowledge cover it.** The bisimulation asks the specification's store to be tagged
through its knowledge (`SemTagged`), and along runs it asks an invariant of the stored-rule program that
implies the tags (`runs_forward_of`, `runs_backward_of`).
* The store the relay reaches is tagged through its knowledge (`relayed_semTagged`).
* For the program `Relaying` (the relay and `second`), the stores tagged through their knowledge whose
  messages all carry, at every solution, the body of the code of `second` (`RelayInv`) are kept by every
  firing of the stored-rule program (`relayInv_preserved`). So every run of the stored-rule program from
  the start is a run of the interpreter, step for step, and conversely (`relay_runs_forward`,
  `relay_runs_backward`).
* Existence: the stored-rule program relays the code and then fires `second` from it (`relay_run`), and
  through the interpreter two admitted firings reach `obj done` (`interpreter_relay_run`).
* Control, the invariant's message clause: where a message's payload is an unknown of the store, the
  relay makes a code row the knowledge does not determine, and the result is not tagged through its
  knowledge (`openPayload_not_kept`).

What travels is a row whose value the knowledge makes a code; the rules that can fire are still the
rules of `Relaying`, gated by their codes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Mobility

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open Expr
open Examples (second second_mem five seen done)
open Untagged (secondBody secondBody_closed code_secondBody lst_ne_var exists_zip_right)

/-! ## The relay and the limit of closed fragments -/

/-- A message carrying a term. -/
def msg (t : Expr) : Expr := cell (sym 50) t

/-- **Install a code received in a message**: take `obj (msg x)`, make the row `code x`. -/
def relay : Rule Tm := ⟨PUnit.unit, ⟨[obj (msg (var 0))], [], [], [], [code (var 0)]⟩, []⟩

theorem relay_fragment : Fragment relay := Examples.fragment_of_check rfl

/-- **The relay is in no closed fragment**: what it makes is neither a data row nor a literal code. -/
theorem relay_outside {F : Set (Rule Tm)} (closedF : ClosedFragment F) : relay ∉ F := by
  intro inside
  rcases closedF.made relay inside (code (var 0)) (List.mem_singleton_self _) with
    ⟨t, same⟩ | ⟨r, hr, same⟩
  · exact obj_ne_code t (var 0) same.symm
  · have isClosed := ruleCode_closed (closedF.fragment r hr)
    rw [← same] at isClosed
    exact absurd isClosed (by decide)

/-- **The relaying program**: the relay and `second`. -/
def Relaying : Set (Rule Tm) := {relay, second}

theorem relay_mem : relay ∈ Relaying := Or.inl rfl

theorem second_mem_relaying : second ∈ Relaying := Or.inr rfl

theorem relaying_fragment : ∀ r ∈ Relaying, Fragment r := by
  rintro r (rfl | rfl)
  · exact relay_fragment
  · exact second_mem.1

/-! ## The relay fires and makes a row no syntax tags -/

/-- The labels of the start: a message carrying the body of `second`'s code, the relay's code, and a
seen row. -/
def startLabel (o : ℕ) : Expr :=
  if o = 0 then obj (msg secondBody) else if o = 1 then ruleCode relay else obj (seen five)

/-- **The start.** -/
def relayStart : State Tm ℕ := ⟨PUnit.unit, [], {0, 1, 2}, startLabel⟩

theorem relayStart_tagged : Tagged Relaying relayStart := by
  intro o present
  simp only [relayStart, Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl | rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨relay, relay_mem, rfl⟩
  · exact Or.inl ⟨_, rfl⟩

/-- The stored relay, taking the message, reading its code, making row `3`. -/
def relayFiring : Firing ℕ Ext (Stored Relaying) relayStart.frame :=
  storedFiring relay_mem relayStart.frame (shift 10) ⟨[0], [1], [3]⟩ []

theorem relayFiring_information :
    relayFiring.information X relayStart =
      [(obj (msg (var 10)), obj (msg secondBody)), (ruleCode relay, ruleCode relay)] :=
  rfl

theorem relayStart_bound : stateBound relayStart ≤ 10 := by decide

/-- **The stored relay fires from the start, tagged by syntax.** -/
theorem relayFiring_admitted : relayFiring.Admits X relayStart := by
  refine ⟨⟨fresh_shift relayFiring rfl relayStart_bound, by decide, by decide, rfl, rfl, rfl, rfl⟩,
    by decide, ⟨PUnit.unit, fun v => if v = 10 then secondBody else var v, ?_⟩, ?_⟩
  · rw [relayFiring_information]
    intro e inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> rfl
  · intro b σ _
    refine (holds_iff relayFiring rfl σ).mpr ?_
    intro c inside
    simp [relayFiring, storedFiring, stored, relay] at inside

/-- The store after the relay. -/
def relayed : State Tm ℕ := relayFiring.result X relayStart

theorem relayed_present : relayed.present = {1, 2, 3} := by decide

theorem relayed_label : relayed.label 3 = code (var 10) := by decide

theorem relayed_knowledge :
    relayed.knowledge = [(obj (msg (var 10)), obj (msg secondBody)), (ruleCode relay, ruleCode relay)] :=
  relayFiring_information

/-- **No set of rules tags the store the relay reaches by syntax.** -/
theorem relayed_untagged (G : Set (Rule Tm)) : ¬ Tagged G relayed := by
  intro tagged
  have present : (3 : ℕ) ∈ relayed.present := by rw [relayed_present]; decide
  rcases tagged 3 present with ⟨t, same⟩ | ⟨r, -, same⟩
  · rw [relayed_label] at same
    exact obj_ne_code t (var 10) same.symm
  · rw [relayed_label] at same
    exact lst_ne_var _ 10 (Expr.cell.inj same).2.symm

/-- **Yet at every solution the made row is the code of `second`.** -/
theorem relayed_value (σ : ℕ → Expr) (solved : action.Models σ relayed.knowledge) :
    nf (subst σ (relayed.label 3)) = ruleCode second := by
  have first : nf (subst σ (obj (msg (var 10)))) = nf (subst σ (obj (msg secondBody))) :=
    solved (obj (msg (var 10)), obj (msg secondBody)) (by rw [relayed_knowledge]; exact List.mem_cons_self)
  simp only [obj, msg, subst, nf, Expr.cell.injEq, true_and] at first
  rw [subst_of_closed σ secondBody_closed, nf_of_closed secondBody_closed] at first
  rw [relayed_label]
  show code (nf (σ 10)) = ruleCode second
  rw [first]
  rfl

/-! ## The tags through the knowledge -/

/-- The value of a coded row at a solution, for `second`. -/
theorem second_code_value (σ : ℕ → Expr) : nf (subst σ (ruleCode second)) = ruleCode second := by
  rw [subst_ruleCode second_mem.1, nf_ruleCode second_mem.1]

/-- **The store the relay reaches is tagged through its knowledge.** -/
theorem relayed_semTagged : SemTagged Relaying relayed := by
  intro o present
  rw [relayed_present] at present
  simp only [Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl | rfl
  · have label : relayed.label 1 = ruleCode relay := by decide
    exact Or.inr ⟨relay, relay_mem, fun σ _ => by rw [label]⟩
  · have label : relayed.label 2 = obj (seen five) := by decide
    exact Or.inl fun σ _ => ⟨nf (subst σ (seen five)), by rw [label]; rfl⟩
  · exact Or.inr ⟨second, second_mem_relaying, fun σ solved => by
      rw [relayed_value σ solved, second_code_value]⟩

/-- **The relay invariant**: every row is tagged through the knowledge, and every message carries, at
every solution, the body of the code of `second`. -/
def RelayInv (s : State Tm ℕ) : Prop :=
  SemTagged Relaying s ∧ ∀ o ∈ s.present, ∀ σ, action.Models σ s.knowledge →
    ∀ p, nf (subst σ (s.label o)) = obj (msg p) → code p = ruleCode second

/-- The rows of a result: a made row carries an opened made row of the rule; any other row was present
and keeps its label. -/
theorem result_rows {P : Program Tm} {s : State Tm ℕ} (f : Firing ℕ Ext P s.frame)
    (admitted : f.Admits X s) {o : ℕ} (present : o ∈ (f.result X s).present) :
    (∃ m ∈ f.rule.body.produce, (f.result X s).label o = subst f.opening m) ∨
      (o ∈ s.present ∧ (f.result X s).label o = s.label o) := by
  by_cases made : o ∈ f.selection.made
  · obtain ⟨-, -, -, -, -, madeLength, -⟩ := admitted.1
    have lengths : f.selection.made.length = (f.opened X).produce.length := by
      simp only [Firing.opened, RuleInstance.map, List.length_map]
      exact madeLength.symm
    obtain ⟨t, pair⟩ := exists_zip_right lengths made
    have label := Firing.result_label_made f admitted.1 pair
    have inProduce : t ∈ f.rule.body.produce.map (subst f.opening) := (List.of_mem_zip pair).2
    obtain ⟨m, member, rfl⟩ := List.mem_map.mp inProduce
    exact Or.inl ⟨m, member, label⟩
  · refine Or.inr ⟨?_, (Firing.result_label_other f made).trans (congrFun (row_eq f) o)⟩
    rcases mem_fire.mp present with ⟨old, -⟩ | fresh
    · exact old
    · exact absurd (by simpa [Selection.commit] using fresh) made

/-- **Every firing of the stored-rule program keeps the relay invariant.** -/
theorem relayInv_preserved (s s' : State Tm ℕ) (inv : RelayInv s) (moved : StoredSucc Relaying s s') :
    RelayInv s' := by
  obtain ⟨f, admitted, rfl⟩ := moved
  show RelayInv (f.result X s)
  obtain ⟨-, -, -, takeLength, readLength, -, -⟩ := admitted.1
  have refines : ∀ σ, action.Models σ (f.result X s).knowledge → action.Models σ s.knowledge :=
    fun σ solved => ((models_information f takeLength readLength σ).mp solved).1
  -- a made row of `f` is `obj done`, or the code the taken message carries
  have madeRows : ∀ m ∈ f.rule.body.produce, (subst f.opening m = obj done) ∨
      (∀ σ, action.Models σ (f.result X s).knowledge →
        nf (subst σ (subst f.opening m)) = ruleCode second) := by
    obtain ⟨r, hr, hf⟩ := stored_cases f
    have rule : f.rule = stored r := by rw [hf]; rfl
    have which : r = relay ∨ r = second := hr
    rcases which with rfl | rfl
    · -- the relay: the made row is the code of the message's payload
      intro m inside
      have isCode : m = code (var 0) := by
        rw [rule] at inside
        simpa [stored, relay] using inside
      refine Or.inr fun σ solved => ?_
      subst isCode
      obtain ⟨-, takes, -, -⟩ := (models_information f takeLength readLength σ).mp solved
      have takePattern : f.rule.body.take = [obj (msg (var 0))] := by rw [rule]; rfl
      rw [takePattern] at takes
      obtain ⟨om, eqTaken, matched⟩ : ∃ om, om ∈ f.selection.taken ∧
          nf (subst σ (subst f.opening (obj (msg (var 0))))) = nf (subst σ (s.label om)) := by
        cases htaken : f.selection.taken with
        | nil => rw [htaken] at takes; cases takes
        | cons om rest =>
            rw [htaken] at takes
            exact ⟨om, List.mem_cons_self, (List.forall₂_cons.mp takes).1⟩
      have omPresent : om ∈ s.present :=
        present_of_enabled admitted.2.1 om (List.mem_append_left _ eqTaken)
      have payload := inv.2 om omPresent σ (refines σ solved) (nf (subst σ (f.opening 0)))
        (by rw [← matched]; rfl)
      show code (nf (subst σ (f.opening 0))) = ruleCode second
      exact payload
    · -- `second` makes `obj done`
      intro m inside
      left
      have isDone : m = obj done := by
        rw [rule] at inside
        simpa [stored, second] using inside
      rw [isDone]
      rfl
  refine ⟨fun o present => ?_, fun o present σ solved p value => ?_⟩
  · rcases result_rows f admitted present with ⟨m, member, label⟩ | ⟨old, label⟩
    · rcases madeRows m member with isDone | coded
      · exact Or.inl fun σ _ => ⟨done, by rw [label, isDone]; rfl⟩
      · exact Or.inr ⟨second, second_mem_relaying, fun σ solved => by
          rw [label, coded σ solved, second_code_value]⟩
    · rcases inv.1 o old with data | ⟨r, hr, coded⟩
      · exact Or.inl fun σ solved => by rw [label]; exact data σ (refines σ solved)
      · exact Or.inr ⟨r, hr, fun σ solved => by rw [label]; exact coded σ (refines σ solved)⟩
  · rcases result_rows f admitted present with ⟨m, member, label⟩ | ⟨old, label⟩
    · rcases madeRows m member with isDone | coded
      · rw [label, isDone] at value
        simp [obj, msg, done, subst, nf] at value
      · rw [label, coded σ solved] at value
        exact (obj_ne_code _ _ value.symm).elim
    · rw [label] at value
      exact inv.2 o old σ (refines σ solved) p value

theorem relayInv_tags (s : State Tm ℕ) (inv : RelayInv s) : SemTagged Relaying s := inv.1

/-- **The start satisfies the relay invariant.** -/
theorem relayStart_inv : RelayInv relayStart := by
  refine ⟨relayStart_tagged.sem, fun o present σ _ p value => ?_⟩
  simp only [relayStart, Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl | rfl
  · have label : relayStart.label 0 = obj (msg secondBody) := rfl
    rw [label] at value
    simp only [obj, msg, subst, nf, Expr.cell.injEq, true_and] at value
    rw [subst_of_closed σ secondBody_closed, nf_of_closed secondBody_closed] at value
    rw [← value]
    rfl
  · have label : relayStart.label 1 = ruleCode relay := rfl
    rw [label, subst_ruleCode relay_fragment, nf_ruleCode relay_fragment] at value
    exact (obj_ne_code _ _ value.symm).elim
  · have label : relayStart.label 2 = obj (seen five) := rfl
    rw [label] at value
    simp [obj, msg, seen, five, subst, nf] at value

/-! ## Runs from the start, both ways -/

/-- **Every run of the stored-rule program from the start is a run of the interpreter, step for
step.** -/
theorem relay_runs_forward {s' : State Tm ℕ} (run : Relation.ReflTransGen (StoredSucc Relaying) relayStart s') :
    ∃ u', Relation.ReflTransGen InterpSucc relayStart u' ∧ Represents Relaying s' u' ∧ RelayInv s' :=
  runs_forward_of relaying_fragment relayInv_tags relayInv_preserved relayStart_inv
    (represents_refl relayStart_tagged) run

/-- **Every run of the interpreter from the start is a run of the stored-rule program, step for
step.** -/
theorem relay_runs_backward {u' : State Tm ℕ} (run : Relation.ReflTransGen InterpSucc relayStart u') :
    ∃ s', Relation.ReflTransGen (StoredSucc Relaying) relayStart s' ∧ Represents Relaying s' u' ∧
      RelayInv s' :=
  runs_backward_of relaying_fragment relayInv_tags relayInv_preserved relayStart_inv
    (represents_refl relayStart_tagged) run

/-! ## Existence: the relayed code is used -/

theorem relayed_bound : stateBound relayed ≤ 20 := by decide

/-- `second`, reading the relayed row as its code and taking the seen row. -/
def useFiring : Firing ℕ Ext (Stored Relaying) relayed.frame :=
  storedFiring second_mem_relaying relayed.frame (shift 20) ⟨[2], [3], [4]⟩ []

theorem useFiring_information :
    useFiring.information X relayed =
      [(obj (msg (var 10)), obj (msg secondBody)), (ruleCode relay, ruleCode relay),
        (obj (seen (var 20)), obj (seen five)), (ruleCode second, code (var 10))] := by
  decide

/-- **`second` fires from the relayed code.** -/
theorem useFiring_admitted : useFiring.Admits X relayed := by
  refine ⟨⟨fresh_shift useFiring rfl relayed_bound, by decide, by decide, rfl, rfl, rfl, rfl⟩,
    by decide, ⟨PUnit.unit, fun v => if v = 10 then secondBody else if v = 20 then five else var v, ?_⟩, ?_⟩
  · rw [useFiring_information]
    intro e inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl | rfl <;> rfl
  · intro b σ solved
    rw [useFiring_information] at solved
    refine (holds_iff useFiring rfl σ).mpr ?_
    intro c inside
    simp only [useFiring, storedFiring, stored, second, List.mem_singleton] at inside
    subst inside
    have seenRow : nf (subst σ (obj (seen (var 20)))) = nf (subst σ (obj (seen five))) :=
      solved _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    simp only [obj, seen, five, subst, nf, Expr.cell.injEq, true_and] at seenRow
    show nf (σ 20) = five
    exact seenRow

/-- The store after `second`. -/
def relayedDone : State Tm ℕ := useFiring.result X relayed

theorem relayedDone_present : relayedDone.present = {1, 3, 4} := by decide

theorem relayedDone_label : relayedDone.label 4 = obj done := rfl

/-- **The stored-rule program relays the code, then fires `second` from it.** -/
theorem relay_run : StoredSucc Relaying relayStart relayed ∧ StoredSucc Relaying relayed relayedDone :=
  ⟨⟨relayFiring, relayFiring_admitted, rfl⟩, ⟨useFiring, useFiring_admitted, rfl⟩⟩

/-- **Through the interpreter**: two admitted firings from the start, the second interpreting a code
that the first made from a message; the result holds `obj done` at every solution. -/
theorem interpreter_relay_run :
    ∃ u₁ u₂ : State Tm ℕ, InterpSucc relayStart u₁ ∧ InterpSucc u₁ u₂ ∧
      Represents Relaying relayedDone u₂ ∧ 4 ∈ u₂.present ∧
      ∀ σ, action.Models σ u₂.knowledge → nf (subst σ (u₂.label 4)) = obj done := by
  have keeps₀ := keepsTags_of_invariant relayInv_tags relayInv_preserved relayStart_inv
  obtain ⟨u₁, moved₁, rep₁⟩ := (step_bisimulation relaying_fragment (represents_refl relayStart_tagged)
    keeps₀).1 _ relay_run.1
  have inv₁ := relayInv_preserved _ _ relayStart_inv relay_run.1
  have keeps₁ := keepsTags_of_invariant relayInv_tags relayInv_preserved inv₁
  obtain ⟨u₂, moved₂, rep₂⟩ := (step_bisimulation relaying_fragment rep₁ keeps₁).1 _ relay_run.2
  refine ⟨u₁, u₂, moved₁, moved₂, rep₂, ?_, fun σ solved => ?_⟩
  · rw [rep₂.present, relayedDone_present]
    decide
  · have present : 4 ∈ relayedDone.present := by rw [relayedDone_present]; decide
    obtain ⟨σ', -, labels⟩ := rep₂.forth σ solved
    rw [labels 4 present, relayedDone_label]
    rfl

/-! ## Control: a message whose payload is unknown -/

theorem lst_ne_three (l : List Expr) : lst l ≠ sym 3 := by
  cases l <;> simp [lst, nil]

/-- A message whose payload is the store's unknown `5`, and the relay's code. -/
def openStart : State Tm ℕ :=
  ⟨PUnit.unit, [], {0, 1}, fun o => if o = 0 then obj (msg (var 5)) else ruleCode relay⟩

/-- The stored relay at the open start. -/
def openFiring : Firing ℕ Ext (Stored Relaying) openStart.frame :=
  storedFiring relay_mem openStart.frame (shift 10) ⟨[0], [1], [2]⟩ []

theorem openFiring_information :
    openFiring.information X openStart =
      [(obj (msg (var 10)), obj (msg (var 5))), (ruleCode relay, ruleCode relay)] :=
  rfl

theorem openFiring_admitted : openFiring.Admits X openStart := by
  refine ⟨⟨fresh_shift openFiring rfl (by decide), by decide, by decide, rfl, rfl, rfl, rfl⟩,
    by decide, ⟨PUnit.unit, fun v => if v = 10 then var 5 else var v, ?_⟩, ?_⟩
  · rw [openFiring_information]
    intro e inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> rfl
  · intro b σ _
    refine (holds_iff openFiring rfl σ).mpr ?_
    intro c inside
    simp [openFiring, storedFiring, stored, relay] at inside

/-- **Where a message's payload is an unknown, the relay leaves a store that is not tagged through its
knowledge**: the knowledge lets the made row be `code (sym 3)`, which is neither a data row nor the
code of any rule. The start is tagged by syntax; the hypothesis that fails is the invariant's message
clause. -/
theorem openPayload_not_kept :
    Tagged Relaying openStart ∧ openFiring.Admits X openStart ∧
      ¬ SemTagged Relaying (openFiring.result X openStart) := by
  refine ⟨?_, openFiring_admitted, fun tagged => ?_⟩
  · intro o present
    simp only [openStart, Finset.mem_insert, Finset.mem_singleton] at present
    rcases present with rfl | rfl
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨relay, relay_mem, rfl⟩
  · have present : (2 : ℕ) ∈ (openFiring.result X openStart).present := by decide
    have label : (openFiring.result X openStart).label 2 = code (var 10) := by decide
    let σ : ℕ → Expr := fun v => if v = 5 ∨ v = 10 then sym 3 else var v
    have known : action.Models σ (openFiring.result X openStart).knowledge := by
      show action.Models σ (openFiring.information X openStart)
      rw [openFiring_information]
      intro e inside
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl <;> rfl
    rcases tagged 2 present with data | ⟨r, hr, coded⟩
    · obtain ⟨t, same⟩ := data σ known
      rw [label] at same
      exact obj_ne_code _ _ same.symm
    · have value := coded.value (relaying_fragment r hr) known
      rw [label] at value
      change code (nf (σ 10)) = code (lst ((List.range 9).map fun k => lst ((partsAt r k).map quote)))
        at value
      have inner : nf (σ 10) = lst ((List.range 9).map fun k => lst ((partsAt r k).map quote)) :=
        (Expr.cell.inj value).2
      have body : nf (σ 10) = sym 3 := rfl
      rw [body] at inner
      exact lst_ne_three _ inner.symm

#print axioms relay_fragment
#print axioms relay_outside
#print axioms relayFiring_admitted
#print axioms relayed_untagged
#print axioms relayed_value
#print axioms relayed_semTagged
#print axioms relayInv_preserved
#print axioms relayStart_inv
#print axioms relay_runs_forward
#print axioms relay_runs_backward
#print axioms relay_run
#print axioms interpreter_relay_run
#print axioms openPayload_not_kept

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Mobility
