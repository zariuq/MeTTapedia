import Mettapedia.GSLT.ProofPlans.Execution

/-!
# Work plans: proof plans whose steps act

A work plan is a proof plan whose steps are actions with effects: each rule
application does something to the world as well as concluding its judgment.
The plan structure is unchanged, so every structural result about plans
survives: completion spaces, refinement by discharge, joint completion of
networks, and the plan transforms.  What does not survive is incremental
execution: resumption after a discharge reorders effects.

This module runs the plan `both(?A, ab(axA₁))` of the fixture kernel as a work
plan whose actions append to a journal (a write-only effect).

* Executing the completed plan journals `axA₁, axA₁, ab, both`; executing it
  incrementally journals `axA₁, ab, axA₁, both` (`journals_differ`).  The two
  journals are permutations of each other (`journals_permute`): with a
  write-only effect, incremental execution preserves the multiset of effects
  and loses their order.
* A receipt that records each action's position in the completed plan's order
  restores that order: sorting the incremental receipts by position gives the
  completed journal (`receipts_restore_order`).
* The same two facts hold for every plan that cites each obligation once and
  in index order. The journals are permutations (`journals_perm_of_linear`),
  and sorting receipts of plan position restores the completed journal
  (`linearReceipts_restore_order`).
* With an effect that is read back, as the counter of `Stateful`, the values
  themselves differ (`readback_not_a_permutation`, citing
  `Stateful.Controls.commutation_fails`), and no reordering of receipts
  repairs a value computed from the wrong state: such a step must be
  re-executed in plan order.

Receipts therefore have to provide: the position of each action in plan order
(to restore the order of write-only effects), the state or context each action
read (to detect values computed from the wrong state, and the recorded context
of `Contextual`), and the identity of each obligation occurrence (so that a
discharge cited twice is executed and charged per citation, as
`Cost.Controls.shared_obligation_paid_twice` requires).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProofPlans.WorkPlans

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.ProofPlans.Stateful
open Mettapedia.GSLT.ProofPlans.Fixture
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenSearchMachine
  (holeOccurrences holeOccurrencesList)

/-- **The journal executor**: every action appends its rule identifier to the
journal. -/
abbrev journalExecutor : Executor kernel (List RuleId) where
  carrier := fun _ => Unit
  act := fun ruleInstance _ _ _ _ journal => ((), journal ++ [ruleInstance.ruleId])

/-- The journal of the completed work plan, in plan order. -/
theorem completed_journal :
    (run journalExecutor (planBoth.discharge (.cons dA₁ .nil)) []).2 =
      [ruleAxA₁.id, ruleAxA₁.id, ruleAB.id, ruleBoth.id] := by
  decide

/-- The journal of incremental execution: the determined `ab(axA₁)` first,
then the discharge, then the pending step. -/
theorem incremental_journal :
    (incremental journalExecutor planBoth (.cons dA₁ .nil) []).2 =
      [ruleAxA₁.id, ruleAB.id, ruleAxA₁.id, ruleBoth.id] := by
  decide

/-- **Incremental execution reorders effects.** -/
theorem journals_differ :
    (run journalExecutor (planBoth.discharge (.cons dA₁ .nil)) []).2 ≠
      (incremental journalExecutor planBoth (.cons dA₁ .nil) []).2 := by
  decide

/-- **With a write-only effect, the multiset of effects is preserved.** -/
theorem journals_permute :
    List.Perm (run journalExecutor (planBoth.discharge (.cons dA₁ .nil)) []).2
      (incremental journalExecutor planBoth (.cons dA₁ .nil) []).2 := by
  decide

/-- A receipt: the position of the action in the completed plan's order, and
the action. -/
abbrev Receipt := ℕ × RuleId

/-- The receipts of incremental execution: `ab(axA₁)` occupies positions `1`
and `2` of the completed order, the discharge position `0`, and `both`
position `3`. -/
def incrementalReceipts : List Receipt :=
  [(1, ruleAxA₁.id), (2, ruleAB.id), (0, ruleAxA₁.id), (3, ruleBoth.id)]

/-- The receipts carry exactly the incremental journal. -/
theorem receipts_carry_journal :
    incrementalReceipts.map Prod.snd = (incremental journalExecutor planBoth (.cons dA₁ .nil) []).2 := by
  decide

/-- **Receipts with plan positions restore the completed order.** -/
theorem receipts_restore_order :
    ((incrementalReceipts.insertionSort fun first second => first.1 ≤ second.1).map Prod.snd) =
      (run journalExecutor (planBoth.discharge (.cons dA₁ .nil)) []).2 := by
  decide

/-! ## Linear plans

A plan is linear when its assumption occurrences are exactly the context
indices, once each and in index order.  For a write-only journal, incremental
execution then permutes the completed journal, and a receipt of plan position
restores that order. -/

variable {context : List Pattern}

theorem bubble3 {α : Type} (a1 b1 c1 a2 b2 c2 : List α) :
    List.Perm
      (a1 ++ (b1 ++ (c1 ++ (a2 ++ (b2 ++ c2)))))
      (a1 ++ (a2 ++ (b1 ++ (b2 ++ (c1 ++ c2))))) := by
  have s1 :
      List.Perm
        (a1 ++ (b1 ++ (c1 ++ (a2 ++ (b2 ++ c2)))))
        (a1 ++ (b1 ++ (a2 ++ (c1 ++ (b2 ++ c2))))) := by
    have asLeft :
        a1 ++ (b1 ++ (c1 ++ (a2 ++ (b2 ++ c2)))) =
          (a1 ++ b1) ++ (c1 ++ (a2 ++ (b2 ++ c2))) := by
      simp only [List.append_assoc]
    have asRight :
        (a1 ++ b1) ++ (a2 ++ (c1 ++ (b2 ++ c2))) =
          a1 ++ (b1 ++ (a2 ++ (c1 ++ (b2 ++ c2)))) := by
      simp only [List.append_assoc]
    rw [asLeft]
    exact ((List.perm_append_comm_assoc c1 a2 (b2 ++ c2)).append_left (a1 ++ b1)).trans
      (List.Perm.of_eq asRight)
  have s2 :
      List.Perm
        (a1 ++ (b1 ++ (a2 ++ (c1 ++ (b2 ++ c2)))))
        (a1 ++ (a2 ++ (b1 ++ (c1 ++ (b2 ++ c2))))) :=
    (List.perm_append_comm_assoc b1 a2 (c1 ++ (b2 ++ c2))).append_left a1
  have s3 :
      List.Perm
        (a1 ++ (a2 ++ (b1 ++ (c1 ++ (b2 ++ c2)))))
        (a1 ++ (a2 ++ (b1 ++ (b2 ++ (c1 ++ c2))))) := by
    have asLeft :
        a1 ++ (a2 ++ (b1 ++ (c1 ++ (b2 ++ c2)))) =
          (a1 ++ (a2 ++ b1)) ++ (c1 ++ (b2 ++ c2)) := by
      simp only [List.append_assoc]
    have asRight :
        (a1 ++ (a2 ++ b1)) ++ (b2 ++ (c1 ++ c2)) =
          a1 ++ (a2 ++ (b1 ++ (b2 ++ (c1 ++ c2)))) := by
      simp only [List.append_assoc]
    rw [asLeft]
    exact ((List.perm_append_comm_assoc c1 b2 c2).append_left (a1 ++ (a2 ++ b1))).trans
      (List.Perm.of_eq asRight)
  exact s1.trans (s2.trans s3)

/-- Regroup three blocks from two successive segments. -/
theorem block_perm {α : Type} (a1 b1 c1 a2 b2 c2 : List α) :
    List.Perm
      ((a1 ++ b1 ++ c1) ++ (a2 ++ b2 ++ c2))
      ((a1 ++ a2) ++ (b1 ++ b2) ++ (c1 ++ c2)) := by
  have leftEq :
      (a1 ++ b1 ++ c1) ++ (a2 ++ b2 ++ c2) =
        a1 ++ (b1 ++ (c1 ++ (a2 ++ (b2 ++ c2)))) := by
    simp only [List.append_assoc]
  have rightEq :
      (a1 ++ a2) ++ (b1 ++ b2) ++ (c1 ++ c2) =
        a1 ++ (a2 ++ (b1 ++ (b2 ++ (c1 ++ c2)))) := by
    simp only [List.append_assoc]
  rw [leftEq, rightEq]
  exact bubble3 a1 b1 c1 a2 b2 c2

def enumerateFrom (start : Nat) {α : Type} : List α → List (Nat × α)
  | [] => []
  | head :: tail => (start, head) :: enumerateFrom (start + 1) tail

theorem enumerateFrom_append (start : Nat) {α : Type} (xs ys : List α) :
    enumerateFrom start (xs ++ ys) =
      enumerateFrom start xs ++ enumerateFrom (start + xs.length) ys := by
  induction xs generalizing start with
  | nil => simp [enumerateFrom]
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append, enumerateFrom, List.length_cons, inductionHypothesis]
      refine congrArg
        (fun index =>
          (start, head) :: (enumerateFrom (start + 1) tail ++ enumerateFrom index ys))
        ?_
      omega

theorem enumerateFrom_snd (start : Nat) {α : Type} (rules : List α) :
    (enumerateFrom start rules).map Prod.snd = rules := by
  induction rules generalizing start with
  | nil => rfl
  | cons _ tail inductionHypothesis =>
      simp [enumerateFrom, inductionHypothesis]

theorem enumerateFrom_ge (start : Nat) {α : Type} (rules : List α) :
    ∀ receipt ∈ enumerateFrom start rules, start ≤ receipt.1 := by
  induction rules generalizing start with
  | nil =>
      intro _ member
      cases member
  | cons _ tail inductionHypothesis =>
      intro receipt member
      simp only [enumerateFrom, List.mem_cons] at member
      cases member with
      | inl equal =>
          subst equal
          exact Nat.le_refl _
      | inr later =>
          exact Nat.le_trans (Nat.le_succ start)
            (inductionHypothesis (start + 1) receipt later)

theorem enumerateFrom_pairwise (start : Nat) (rules : List RuleId) :
    (enumerateFrom start rules).Pairwise (fun first second => first.1 ≤ second.1) := by
  induction rules generalizing start with
  | nil => exact List.Pairwise.nil
  | cons _ tail inductionHypothesis =>
      refine List.Pairwise.cons ?_ (inductionHypothesis (start + 1))
      intro receipt member
      exact Nat.le_trans (Nat.le_succ start)
        (enumerateFrom_ge (start + 1) tail receipt member)

theorem enumerateFrom_unique (start : Nat) (rules : List RuleId) :
    ∀ first ∈ enumerateFrom start rules, ∀ second ∈ enumerateFrom start rules,
      first.1 = second.1 → first = second := by
  induction rules generalizing start with
  | nil =>
      intro _ member
      cases member
  | cons head tail inductionHypothesis =>
      intro first firstMember second secondMember samePosition
      simp only [enumerateFrom, List.mem_cons] at firstMember secondMember
      cases firstMember with
      | inl firstHead =>
          cases secondMember with
          | inl secondHead =>
              exact firstHead.trans secondHead.symm
          | inr secondLater =>
              have later := enumerateFrom_ge (start + 1) tail second secondLater
              subst firstHead
              omega
      | inr firstLater =>
          cases secondMember with
          | inl secondHead =>
              have later := enumerateFrom_ge (start + 1) tail first firstLater
              subst secondHead
              omega
          | inr secondLater =>
              exact inductionHypothesis (start + 1) first firstLater second secondLater
                samePosition

theorem orderedInsert_forall {α : Type} {r : α → α → Prop} [DecidableRel r]
    {motive : α → Prop} {item : α} {rules : List α}
    (itemHolds : motive item) (rulesHold : ∀ entry ∈ rules, motive entry) :
    ∀ entry ∈ rules.orderedInsert r item, motive entry := by
  induction rules with
  | nil =>
      simp only [List.orderedInsert, List.mem_singleton]
      intro entry equal
      subst equal
      exact itemHolds
  | cons head tail inductionHypothesis =>
      cases decision : decide (r item head) with
      | true =>
          rw [List.orderedInsert_cons_of_le r tail (of_decide_eq_true decision)]
          intro entry member
          rcases List.mem_cons.mp member with equal | later
          · subst equal
            exact itemHolds
          · exact rulesHold entry later
      | false =>
          rw [List.orderedInsert_of_not_le r tail (of_decide_eq_false decision)]
          intro entry member
          rcases List.mem_cons.mp member with equal | later
          · subst equal
            exact rulesHold entry List.mem_cons_self
          · exact inductionHypothesis
              (fun entry member => rulesHold entry (List.mem_cons_of_mem head member))
              entry later

theorem orderedInsert_pairwise {α : Type} {r : α → α → Prop} [DecidableRel r]
    (total : ∀ x y, r x y ∨ r y x)
    (step : ∀ {x y z}, r x y → r y z → r x z)
    (item : α) (rules : List α) (sorted : rules.Pairwise r) :
    (rules.orderedInsert r item).Pairwise r := by
  induction rules with
  | nil =>
      rw [List.orderedInsert]
      exact List.Pairwise.cons (fun _ member => nomatch member) List.Pairwise.nil
  | cons head tail inductionHypothesis =>
      cases sorted with
      | cons headRelated tailSorted =>
          cases decision : decide (r item head) with
          | true =>
              rw [List.orderedInsert_cons_of_le r tail (of_decide_eq_true decision)]
              refine List.Pairwise.cons ?_ (List.Pairwise.cons headRelated tailSorted)
              intro entry member
              simp only [List.mem_cons] at member
              cases member with
              | inl equal =>
                  subst equal
                  exact of_decide_eq_true decision
              | inr later =>
                  exact step (of_decide_eq_true decision) (headRelated entry later)
          | false =>
              rw [List.orderedInsert_of_not_le r tail (of_decide_eq_false decision)]
              have headItem : r head item := by
                cases total item head with
                | inl itemHead => exact absurd itemHead (of_decide_eq_false decision)
                | inr headItem => exact headItem
              refine List.Pairwise.cons ?_ (inductionHypothesis tailSorted)
              intro entry member
              exact orderedInsert_forall headItem
                (fun entry later => headRelated entry later) entry member

theorem orderedInsert_perm {α : Type} {r : α → α → Prop} [DecidableRel r] (item : α) :
    ∀ rules : List α, List.Perm (rules.orderedInsert r item) (item :: rules)
  | [] => List.Perm.of_eq (List.orderedInsert_nil r item)
  | head :: tail => by
      cases decision : decide (r item head) with
      | true =>
          rw [List.orderedInsert_cons_of_le r tail (of_decide_eq_true decision)]
      | false =>
          rw [List.orderedInsert_of_not_le r tail (of_decide_eq_false decision)]
          exact ((orderedInsert_perm item tail).cons head).trans
            (List.Perm.swap item head tail)

theorem insertionSort_perm {α : Type} {r : α → α → Prop} [DecidableRel r] :
    ∀ rules : List α, List.Perm (rules.insertionSort r) rules
  | [] => List.Perm.of_eq (List.insertionSort_nil r)
  | head :: tail => by
      rw [List.insertionSort_cons]
      exact (orderedInsert_perm (r := r) head (tail.insertionSort r)).trans
        ((insertionSort_perm tail).cons head)

theorem insertionSort_pairwise {α : Type} {r : α → α → Prop} [DecidableRel r]
    (total : ∀ x y, r x y ∨ r y x)
    (step : ∀ {x y z}, r x y → r y z → r x z) :
    ∀ rules : List α, (rules.insertionSort r).Pairwise r
  | [] => by
      rw [List.insertionSort_nil]
      exact List.Pairwise.nil
  | _ :: tail => by
      rw [List.insertionSort_cons]
      exact orderedInsert_pairwise total step _ _ (insertionSort_pairwise total step tail)

mutual

def ruleJournal {goal : Pattern} : Derivation kernelDefinition goal → List RuleId
  | .byRule ruleInstance _ children => ruleJournalList children ++ [ruleInstance.ruleId]

def ruleJournalList {goals : List Pattern} :
    DerivationList kernelDefinition goals → List RuleId
  | .nil => []
  | .cons head tail => ruleJournal head ++ ruleJournalList tail

end

mutual

theorem run_journal {goal : Pattern} :
    (derivation : Derivation kernelDefinition goal) → (state : List RuleId) →
      (run journalExecutor derivation state).2 = state ++ ruleJournal derivation
  | .byRule _ _ children, state => by
      simp only [run, ruleJournal]
      rw [runList_journal children state]
      simp [List.append_assoc]

theorem runList_journal {goals : List Pattern} :
    (derivations : DerivationList kernelDefinition goals) → (state : List RuleId) →
      (runList journalExecutor derivations state).2 =
        state ++ ruleJournalList derivations
  | .nil, state => by
      simp [runList, ruleJournalList, List.append_nil]
  | .cons head tail, state => by
      simp only [runList, ruleJournalList]
      rw [runList_journal tail (run journalExecutor head state).2,
        run_journal head state, List.append_assoc]

end

def evidenceAt {goals : List Pattern} :
    DerivationList kernelDefinition goals → (index : Fin goals.length) →
      Derivation kernelDefinition (goals.get index)
  | .nil, index => Fin.elim0 index
  | .cons head tail, index =>
      Fin.cases head (fun tailIndex => evidenceAt tail tailIndex) index

def journalsAt {goals : List Pattern}
    (evidence : DerivationList kernelDefinition goals) :
    List (Fin goals.length) → List RuleId
  | [] => []
  | index :: indices =>
      ruleJournal (evidenceAt evidence index) ++ journalsAt evidence indices

theorem journalsAt_map_succ {premise : Pattern} {premises : List Pattern}
    (head : Derivation kernelDefinition premise)
    (tail : DerivationList kernelDefinition premises)
    (indices : List (Fin premises.length)) :
    journalsAt (.cons head tail) (indices.map Fin.succ) = journalsAt tail indices := by
  induction indices with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      simp only [List.map_cons, journalsAt, inductionHypothesis, evidenceAt]
      erw [Fin.cases_succ]

theorem journals_finRange {goals : List Pattern} :
    (evidence : DerivationList kernelDefinition goals) →
      journalsAt evidence (List.finRange goals.length) = ruleJournalList evidence
  | .nil => by
      simp [journalsAt, ruleJournalList, List.finRange_zero]
  | .cons head tail => by
      erw [List.finRange_succ]
      rw [journalsAt, journalsAt_map_succ, journals_finRange tail, ruleJournalList]
      erw [evidenceAt, Fin.cases_zero]
      rfl

mutual

def holeList {goal : Pattern} :
    OpenDerivation kernelDefinition context goal → List (Fin context.length)
  | .assumption index => [index]
  | .byRule _ _ children => holeListList children

def holeListList {goals : List Pattern} :
    OpenDerivationList kernelDefinition context goals → List (Fin context.length)
  | .nil => []
  | .cons head tail => holeList head ++ holeListList tail

end

mutual

def determinedRules {goal : Pattern} :
    OpenDerivation kernelDefinition context goal → List RuleId
  | .assumption _ => []
  | .byRule ruleInstance _ children =>
      if holeListList children = [] then
        determinedRulesList children ++ [ruleInstance.ruleId]
      else
        determinedRulesList children

def determinedRulesList {goals : List Pattern} :
    OpenDerivationList kernelDefinition context goals → List RuleId
  | .nil => []
  | .cons head tail => determinedRules head ++ determinedRulesList tail

end

mutual

def residualRules {goal : Pattern} :
    OpenDerivation kernelDefinition context goal → List RuleId
  | .assumption _ => []
  | .byRule ruleInstance _ children =>
      if holeListList children = [] then
        []
      else
        residualRulesList children ++ [ruleInstance.ruleId]

def residualRulesList {goals : List Pattern} :
    OpenDerivationList kernelDefinition context goals → List RuleId
  | .nil => []
  | .cons head tail => residualRules head ++ residualRulesList tail

end

mutual

theorem holeList_spec {goal : Pattern} :
    (plan : OpenDerivation kernelDefinition context goal) →
      holeList plan = holeOccurrences plan
  | .assumption _ => rfl
  | .byRule _ _ children => by
      simp only [holeList, holeOccurrences, holeListList_spec children]

theorem holeListList_spec {goals : List Pattern} :
    (plans : OpenDerivationList kernelDefinition context goals) →
      holeListList plans = holeOccurrencesList plans
  | .nil => rfl
  | .cons head tail => by
      simp only [holeListList, holeOccurrencesList, holeList_spec head,
        holeListList_spec tail]

end

mutual

theorem residual_empty {goal : Pattern}
    (plan : OpenDerivation kernelDefinition context goal)
    (closed : holeList plan = []) : residualRules plan = [] := by
  cases plan with
  | assumption _ =>
      simp only [holeList] at closed
      cases closed
  | byRule _ _ children =>
      have childClosed : holeListList children = [] := by
        simpa [holeList] using closed
      unfold residualRules
      rw [if_pos childClosed]

theorem residualList_empty {goals : List Pattern}
    (plans : OpenDerivationList kernelDefinition context goals)
    (closed : holeListList plans = []) : residualRulesList plans = [] := by
  cases plans with
  | nil => rfl
  | cons head tail =>
      have splitEmpty : holeList head = [] ∧ holeListList tail = [] := by
        simpa [holeListList, List.append_eq_nil_iff] using closed
      simp [residualRulesList, residual_empty head splitEmpty.1,
        residualList_empty tail splitEmpty.2]

end

mutual

theorem speval_of_closed {goal : Pattern} :
    (plan : OpenDerivation kernelDefinition context goal) → (state : List RuleId) →
      holeList plan = [] →
        ∃ value,
          (speval journalExecutor plan state).1 = Residual.value value ∧
            (speval journalExecutor plan state).2 = state ++ determinedRules plan
  | .assumption _, _, closed => by
      simp only [holeList] at closed
      cases closed
  | .byRule ruleInstance _ children, state, closed => by
      have childClosed : holeListList children = [] := by
        simpa [holeList] using closed
      obtain ⟨_, valuesSome, stateEquation⟩ :=
        spevalList_of_closed children state childClosed
      refine ⟨(), ?_, ?_⟩
      · simp only [speval, valuesSome, journalExecutor]
      · simp only [speval, valuesSome, journalExecutor, stateEquation, List.append_assoc]
        unfold determinedRules
        rw [if_pos childClosed]

theorem spevalList_of_closed {goals : List Pattern} :
    (plans : OpenDerivationList kernelDefinition context goals) → (state : List RuleId) →
      holeListList plans = [] →
        ∃ values,
          (spevalList journalExecutor plans state).1.values? = some values ∧
            (spevalList journalExecutor plans state).2 =
              state ++ determinedRulesList plans
  | .nil, state, _ =>
      ⟨RealizationList.nil, rfl, by simp [spevalList, determinedRulesList, List.append_nil]⟩
  | .cons head tail, state, closed => by
      have splitEmpty : holeList head = [] ∧ holeListList tail = [] := by
        simpa [holeListList, List.append_eq_nil_iff] using closed
      obtain ⟨value, headForm, headState⟩ :=
        speval_of_closed head state splitEmpty.1
      obtain ⟨values, tailSome, tailState⟩ :=
        spevalList_of_closed tail (speval journalExecutor head state).2 splitEmpty.2
      refine ⟨RealizationList.cons value values, ?_, ?_⟩
      · simp only [spevalList, headForm, tailSome, ResidualList.values?, Option.map_some]
      · simp only [spevalList, determinedRulesList]
        rw [tailState, headState, List.append_assoc]

end

theorem values_none {goals : List Pattern} :
    (plans : OpenDerivationList kernelDefinition context goals) → (state : List RuleId) →
      holeListList plans ≠ [] →
        (spevalList journalExecutor plans state).1.values? = none
  | .nil, _, openPlans => by
      simp only [holeListList] at openPlans
      exact absurd rfl openPlans
  | .cons head tail, state, openPlans => by
      cases headHoles : holeList head with
      | nil =>
          have tailOpen : holeListList tail ≠ [] := by
            intro tailClosed
            exact openPlans (by simp [holeListList, headHoles, tailClosed])
          obtain ⟨_, headForm, _⟩ := speval_of_closed head state headHoles
          have tailNone :=
            values_none tail (speval journalExecutor head state).2 tailOpen
          simp only [spevalList, headForm, ResidualList.values?, tailNone, Option.map_none]
      | cons _ _ =>
          cases head with
          | assumption _ =>
              simp [spevalList, speval, ResidualList.values?]
          | byRule _ _ children =>
              have childOpen : holeListList children ≠ [] := by
                intro closedChildren
                simp only [holeList, closedChildren] at headHoles
                cases headHoles
              have noneChildren := values_none children state childOpen
              simp [spevalList, speval, noneChildren, ResidualList.values?]
termination_by plans => sizeOf plans

mutual

theorem speval_state {goal : Pattern}
    (plan : OpenDerivation kernelDefinition context goal) (state : List RuleId) :
    (speval journalExecutor plan state).2 = state ++ determinedRules plan := by
  cases planHoles : holeList plan with
  | nil =>
      obtain ⟨_, _, stateEquation⟩ := speval_of_closed plan state planHoles
      exact stateEquation
  | cons _ _ =>
      cases plan with
      | assumption _ =>
          simp [speval, determinedRules]
      | byRule _ _ children =>
          have childOpen : holeListList children ≠ [] := by
            intro closedChildren
            simp only [holeList, closedChildren] at planHoles
            cases planHoles
          have noneValues := values_none children state childOpen
          simp only [speval, noneValues]
          unfold determinedRules
          rw [if_neg childOpen]
          exact spevalList_state children state

theorem spevalList_state {goals : List Pattern}
    (plans : OpenDerivationList kernelDefinition context goals) (state : List RuleId) :
    (spevalList journalExecutor plans state).2 =
      state ++ determinedRulesList plans := by
  cases plans with
  | nil =>
      simp [spevalList, determinedRulesList, List.append_nil]
  | cons head tail =>
      simp only [spevalList, determinedRulesList]
      rw [spevalList_state tail (speval journalExecutor head state).2,
        speval_state head state, List.append_assoc]

end

mutual

theorem sresume_append {goal : Pattern}
    (plan : OpenDerivation kernelDefinition context goal)
    (state₀ state : List RuleId)
    (environment : RealizationList (fun _ => Unit) context) :
    (sresume journalExecutor (speval journalExecutor plan state₀).1 environment state).2 =
      state ++ residualRules plan := by
  cases plan with
  | assumption _ =>
      simp [speval, sresume, residualRules, List.append_nil]
  | byRule ruleInstance application children =>
      cases childHoles : holeListList children with
      | nil =>
          have closedPlan :
              holeList (.byRule ruleInstance application children) = [] := by
            simp [holeList, childHoles]
          obtain ⟨_, form, _⟩ :=
            speval_of_closed (.byRule ruleInstance application children) state₀ closedPlan
          simp [form, sresume, residual_empty _ closedPlan, List.append_nil]
      | cons _ _ =>
          have childOpen : holeListList children ≠ [] := by
            simp [childHoles]
          have noneValues := values_none children state₀ childOpen
          simp only [speval, noneValues, sresume, journalExecutor]
          rw [sresumeList_append children state₀ state environment]
          unfold residualRules
          rw [if_neg childOpen]
          simp [List.append_assoc]

theorem sresumeList_append {goals : List Pattern}
    (plans : OpenDerivationList kernelDefinition context goals)
    (state₀ state : List RuleId)
    (environment : RealizationList (fun _ => Unit) context) :
    (sresumeList journalExecutor (spevalList journalExecutor plans state₀).1
        environment state).2 =
      state ++ residualRulesList plans := by
  cases plans with
  | nil =>
      simp [spevalList, sresumeList, residualRulesList, List.append_nil]
  | cons head tail =>
      simp only [spevalList, sresumeList, residualRulesList]
      rw [sresume_append head state₀ state environment]
      rw [sresumeList_append tail (speval journalExecutor head state₀).2
        (state ++ residualRules head) environment, List.append_assoc]

end

mutual

def bareJournal {goal : Pattern} : OpenDerivation kernelDefinition [] goal → List RuleId
  | .assumption index => Fin.elim0 index
  | .byRule ruleInstance _ children => bareJournalList children ++ [ruleInstance.ruleId]

def bareJournalList {goals : List Pattern} :
    OpenDerivationList kernelDefinition [] goals → List RuleId
  | .nil => []
  | .cons head tail => bareJournal head ++ bareJournalList tail

end

mutual

def boundJournal {goal : Pattern}
    (plan : OpenDerivation kernelDefinition context goal)
    (environment : OpenDerivationList kernelDefinition [] context) : List RuleId :=
  match plan with
  | .assumption index => bareJournal (environment.get index)
  | .byRule ruleInstance _ children =>
      boundJournalList children environment ++ [ruleInstance.ruleId]

def boundJournalList {goals : List Pattern}
    (plans : OpenDerivationList kernelDefinition context goals)
    (environment : OpenDerivationList kernelDefinition [] context) : List RuleId :=
  match plans with
  | .nil => []
  | .cons head tail =>
      boundJournal head environment ++ boundJournalList tail environment

end

mutual

def citedJournal {goal : Pattern}
    (plan : OpenDerivation kernelDefinition context goal)
    (evidence : DerivationList kernelDefinition context) : List RuleId :=
  match plan with
  | .assumption index => ruleJournal (evidenceAt evidence index)
  | .byRule ruleInstance _ children =>
      citedJournalList children evidence ++ [ruleInstance.ruleId]

def citedJournalList {goals : List Pattern}
    (plans : OpenDerivationList kernelDefinition context goals)
    (evidence : DerivationList kernelDefinition context) : List RuleId :=
  match plans with
  | .nil => []
  | .cons head tail => citedJournal head evidence ++ citedJournalList tail evidence

end

mutual

theorem bare_close {goal : Pattern} :
    (plan : OpenDerivation kernelDefinition [] goal) →
      ruleJournal plan.close = bareJournal plan
  | .assumption index => Fin.elim0 index
  | .byRule ruleInstance _ children => by
      simp [OpenDerivation.close, ruleJournal, bareJournal, bare_close_list children]

theorem bare_close_list {goals : List Pattern} :
    (plans : OpenDerivationList kernelDefinition [] goals) →
      ruleJournalList plans.close = bareJournalList plans
  | .nil => rfl
  | .cons head tail => by
      simp [OpenDerivationList.close, ruleJournalList, bareJournalList,
        bare_close head, bare_close_list tail]

end

mutual

theorem bare_ofClosed {goal : Pattern} :
    (derivation : Derivation kernelDefinition goal) →
      bareJournal (OpenDerivation.ofClosed (context := []) derivation) =
        ruleJournal derivation
  | .byRule ruleInstance _ children => by
      simp [OpenDerivation.ofClosed, bareJournal, ruleJournal, bare_ofClosed_list children]

theorem bare_ofClosed_list {goals : List Pattern} :
    (derivations : DerivationList kernelDefinition goals) →
      bareJournalList (OpenDerivationList.ofClosed (context := []) derivations) =
        ruleJournalList derivations
  | .nil => rfl
  | .cons head tail => by
      simp [OpenDerivationList.ofClosed, bareJournalList, ruleJournalList,
        bare_ofClosed head, bare_ofClosed_list tail]

end

theorem ofClosed_evidenceAt {goals : List Pattern} :
    (evidence : DerivationList kernelDefinition goals) → (index : Fin goals.length) →
      (OpenDerivationList.ofClosed (context := []) evidence).get index =
        OpenDerivation.ofClosed (context := []) (evidenceAt evidence index)
  | .nil, index => Fin.elim0 index
  | .cons _ tail, index => by
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · simp only [OpenDerivationList.ofClosed, OpenDerivationList.get, evidenceAt]
        erw [Fin.cases_zero, Fin.cases_zero]
        rfl
      · simp only [OpenDerivationList.ofClosed, OpenDerivationList.get, evidenceAt]
        erw [Fin.cases_succ]
        exact ofClosed_evidenceAt tail tailIndex

mutual

theorem bare_bind {goal : Pattern} :
    (plan : OpenDerivation kernelDefinition context goal) →
      (environment : OpenDerivationList kernelDefinition [] context) →
        bareJournal (plan.bind environment) = boundJournal plan environment
  | .assumption _, environment => by
      simp [OpenDerivation.bind, boundJournal]
  | .byRule ruleInstance _ children, environment => by
      simp [OpenDerivation.bind, bareJournal, boundJournal,
        bare_bind_list children environment]

theorem bare_bind_list {goals : List Pattern} :
    (plans : OpenDerivationList kernelDefinition context goals) →
      (environment : OpenDerivationList kernelDefinition [] context) →
        bareJournalList (plans.bind environment) = boundJournalList plans environment
  | .nil, _ => rfl
  | .cons head tail, environment => by
      simp [OpenDerivationList.bind, bareJournalList, boundJournalList,
        bare_bind head environment, bare_bind_list tail environment]

end

mutual

theorem bound_ofClosed {goal : Pattern} :
    (plan : OpenDerivation kernelDefinition context goal) →
      (evidence : DerivationList kernelDefinition context) →
        boundJournal plan (OpenDerivationList.ofClosed (context := []) evidence) =
          citedJournal plan evidence
  | .assumption index, evidence => by
      simp [boundJournal, citedJournal, ofClosed_evidenceAt evidence index,
        bare_ofClosed (evidenceAt evidence index)]
  | .byRule ruleInstance _ children, evidence => by
      simp [boundJournal, citedJournal, bound_ofClosed_list children evidence]

theorem bound_ofClosed_list {goals : List Pattern} :
    (plans : OpenDerivationList kernelDefinition context goals) →
      (evidence : DerivationList kernelDefinition context) →
        boundJournalList plans (OpenDerivationList.ofClosed (context := []) evidence) =
          citedJournalList plans evidence
  | .nil, _ => rfl
  | .cons head tail, evidence => by
      simp [boundJournalList, citedJournalList, bound_ofClosed head evidence,
        bound_ofClosed_list tail evidence]

end

theorem discharge_journal {goal : Pattern}
    (plan : OpenDerivation kernelDefinition context goal)
    (evidence : DerivationList kernelDefinition context) :
    ruleJournal (plan.discharge evidence) = citedJournal plan evidence := by
  simp only [OpenDerivation.discharge]
  rw [bare_close, bare_bind, bound_ofClosed]

theorem incremental_journal_parts {goal : Pattern}
    (plan : OpenDerivation kernelDefinition context goal)
    (evidence : DerivationList kernelDefinition context) (state : List RuleId) :
    (incremental journalExecutor plan evidence state).2 =
      state ++ determinedRules plan ++ ruleJournalList evidence ++ residualRules plan := by
  have resumed :
      (sresume journalExecutor (speval journalExecutor plan state).1
          (runList journalExecutor evidence (speval journalExecutor plan state).2).1
          (runList journalExecutor evidence (speval journalExecutor plan state).2).2).2 =
        (runList journalExecutor evidence (speval journalExecutor plan state).2).2 ++
          residualRules plan :=
    sresume_append plan state
      (runList journalExecutor evidence (speval journalExecutor plan state).2).2
      (runList journalExecutor evidence (speval journalExecutor plan state).2).1
  have evaluated :
      (runList journalExecutor evidence (speval journalExecutor plan state).2).2 =
        (speval journalExecutor plan state).2 ++ ruleJournalList evidence :=
    runList_journal evidence (speval journalExecutor plan state).2
  calc
    (incremental journalExecutor plan evidence state).2
        = (sresume journalExecutor (speval journalExecutor plan state).1
            (runList journalExecutor evidence (speval journalExecutor plan state).2).1
            (runList journalExecutor evidence (speval journalExecutor plan state).2).2).2 := by
          simp only [incremental]
    _ = (speval journalExecutor plan state).2 ++ ruleJournalList evidence ++
          residualRules plan := by
          rw [resumed, evaluated, List.append_assoc]
    _ = state ++ determinedRules plan ++ ruleJournalList evidence ++ residualRules plan := by
          rw [speval_state plan state, List.append_assoc]

structure Positioned where
  next : Nat
  determined : List Receipt
  evidence : List Receipt
  residual : List Receipt

mutual

def positioned {goal : Pattern}
    (plan : OpenDerivation kernelDefinition context goal)
    (evidence : DerivationList kernelDefinition context) (start : Nat) : Positioned :=
  match plan with
  | .assumption index =>
      let rules := ruleJournal (evidenceAt evidence index)
      { next := start + rules.length
        determined := []
        evidence := enumerateFrom start rules
        residual := [] }
  | .byRule ruleInstance _ children =>
      let child := positionedList children evidence start
      if holeListList children = [] then
        { next := child.next + 1
          determined := child.determined ++ [(child.next, ruleInstance.ruleId)]
          evidence := child.evidence
          residual := child.residual }
      else
        { next := child.next + 1
          determined := child.determined
          evidence := child.evidence
          residual := child.residual ++ [(child.next, ruleInstance.ruleId)] }

def positionedList {goals : List Pattern}
    (plans : OpenDerivationList kernelDefinition context goals)
    (evidence : DerivationList kernelDefinition context) (start : Nat) : Positioned :=
  match plans with
  | .nil => { next := start, determined := [], evidence := [], residual := [] }
  | .cons head tail =>
      let first := positioned head evidence start
      let rest := positionedList tail evidence first.next
      { next := rest.next
        determined := first.determined ++ rest.determined
        evidence := first.evidence ++ rest.evidence
        residual := first.residual ++ rest.residual }

end

structure PositionFacts
    (build : Positioned) (start : Nat)
    (cited determined residual : List RuleId)
    (holes : List (Fin context.length))
    (evidence : DerivationList kernelDefinition context) : Prop where
  next_eq : build.next = start + cited.length
  determined_snd : build.determined.map Prod.snd = determined
  evidence_snd : build.evidence.map Prod.snd = journalsAt evidence holes
  residual_snd : build.residual.map Prod.snd = residual
  permutation : List.Perm
    (build.determined ++ build.evidence ++ build.residual)
    (enumerateFrom start cited)

mutual

theorem positioned_facts {goal : Pattern} :
    (plan : OpenDerivation kernelDefinition context goal) →
      (evidence : DerivationList kernelDefinition context) → (start : Nat) →
        PositionFacts (positioned plan evidence start) start
          (citedJournal plan evidence) (determinedRules plan) (residualRules plan)
          (holeList plan) evidence
  | .assumption index, evidence, start => by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [positioned, citedJournal]
      · simp [positioned, determinedRules]
      · simp [positioned, holeList, journalsAt, enumerateFrom_snd, List.append_nil]
      · simp [positioned, residualRules]
      · simp [positioned, citedJournal, List.nil_append, List.append_nil]
  | .byRule ruleInstance _ children, evidence, start => by
      have child := positionedList_facts children evidence start
      cases childHoles : holeListList children with
      | nil =>
          have evidNil :
              (positionedList children evidence start).evidence = [] := by
            have mapped :
                ((positionedList children evidence start).evidence).map Prod.snd = [] := by
              simpa [journalsAt, childHoles] using child.evidence_snd
            exact List.map_eq_nil_iff.mp mapped
          have residualNil :
              (positionedList children evidence start).residual = [] := by
            have mapped :
                ((positionedList children evidence start).residual).map Prod.snd = [] := by
              simpa [residualList_empty children childHoles] using child.residual_snd
            exact List.map_eq_nil_iff.mp mapped
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · unfold positioned
            rw [if_pos childHoles]
            simp only [citedJournal, child.next_eq, List.length_append, List.length_singleton]
            omega
          · unfold positioned
            unfold determinedRules
            rw [if_pos childHoles, if_pos childHoles]
            simp [List.map_append, List.map_cons, List.map_nil, child.determined_snd]
          · unfold positioned
            rw [if_pos childHoles]
            simp [holeList, evidNil, childHoles, journalsAt]
          · unfold positioned
            unfold residualRules
            rw [if_pos childHoles, if_pos childHoles]
            simp [residualNil]
          · unfold positioned
            rw [if_pos childHoles]
            simp only [citedJournal, evidNil, residualNil, List.append_nil]
            rw [child.next_eq]
            have extended := child.permutation.append
              (List.Perm.refl [(start + (citedJournalList children evidence).length,
                ruleInstance.ruleId)])
            simp only [evidNil, residualNil, List.append_nil] at extended
            have enumerated :
                enumerateFrom start (citedJournalList children evidence) ++
                    [(start + (citedJournalList children evidence).length, ruleInstance.ruleId)] =
                  enumerateFrom start
                    (citedJournalList children evidence ++ [ruleInstance.ruleId]) := by
              rw [enumerateFrom_append, enumerateFrom, enumerateFrom]
            exact extended.trans (List.Perm.of_eq enumerated)
      | cons _ _ =>
          have childOpen : holeListList children ≠ [] := by
            simp [childHoles]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · simp only [positioned]
            rw [if_neg childOpen]
            simp only [citedJournal, child.next_eq, List.length_append, List.length_singleton]
            omega
          · simp only [positioned, determinedRules]
            rw [if_neg childOpen, if_neg childOpen]
            exact child.determined_snd
          · simp only [positioned, holeList]
            rw [if_neg childOpen]
            exact child.evidence_snd
          · simp only [positioned, residualRules]
            rw [if_neg childOpen, if_neg childOpen]
            simp [List.map_append, List.map_cons, List.map_nil, child.residual_snd]
          · simp only [positioned]
            rw [if_neg childOpen]
            simp only [citedJournal]
            rw [child.next_eq]
            have extended := child.permutation.append
              (List.Perm.refl [(start + (citedJournalList children evidence).length,
                ruleInstance.ruleId)])
            rw [List.append_assoc] at extended
            have enumerated :
                enumerateFrom start (citedJournalList children evidence) ++
                    [(start + (citedJournalList children evidence).length, ruleInstance.ruleId)] =
                  enumerateFrom start
                    (citedJournalList children evidence ++ [ruleInstance.ruleId]) := by
              rw [enumerateFrom_append, enumerateFrom, enumerateFrom]
            exact extended.trans (List.Perm.of_eq enumerated)

theorem positionedList_facts {goals : List Pattern} :
    (plans : OpenDerivationList kernelDefinition context goals) →
      (evidence : DerivationList kernelDefinition context) → (start : Nat) →
        PositionFacts (positionedList plans evidence start) start
          (citedJournalList plans evidence) (determinedRulesList plans)
          (residualRulesList plans) (holeListList plans) evidence
  | .nil, _, start => by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [positionedList, citedJournalList]
      · simp [positionedList, determinedRulesList]
      · simp [positionedList, holeListList, journalsAt]
      · simp [positionedList, residualRulesList]
      · simp [positionedList, citedJournalList, enumerateFrom]
  | .cons head tail, evidence, start => by
      have headFacts := positioned_facts head evidence start
      have tailFacts := positionedList_facts tail evidence
        (positioned head evidence start).next
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [positionedList, citedJournalList, List.length_append]
        rw [tailFacts.next_eq, headFacts.next_eq]
        omega
      · simp only [positionedList, determinedRulesList, List.map_append,
          headFacts.determined_snd, tailFacts.determined_snd]
      · simp only [positionedList, holeListList, List.map_append,
          headFacts.evidence_snd, tailFacts.evidence_snd]
        -- journalsAt of a concatenation
        have holesAppend :
            journalsAt evidence (holeList head ++ holeListList tail) =
              journalsAt evidence (holeList head) ++
                journalsAt evidence (holeListList tail) := by
          induction holeList head with
          | nil => simp [journalsAt]
          | cons _ _ inductionHypothesis =>
              simp [journalsAt, inductionHypothesis, List.append_assoc]
        simp [holesAppend]
      · simp only [positionedList, residualRulesList, List.map_append,
          headFacts.residual_snd, tailFacts.residual_snd]
      · simp only [positionedList]
        have rearranged :=
          (block_perm
            (positioned head evidence start).determined
            (positioned head evidence start).evidence
            (positioned head evidence start).residual
            (positionedList tail evidence (positioned head evidence start).next).determined
            (positionedList tail evidence (positioned head evidence start).next).evidence
            (positionedList tail evidence (positioned head evidence start).next).residual).symm
        have joined := headFacts.permutation.append tailFacts.permutation
        have enumerated :
            enumerateFrom start (citedJournal head evidence) ++
                enumerateFrom (positioned head evidence start).next
                  (citedJournalList tail evidence) =
              enumerateFrom start
                (citedJournal head evidence ++ citedJournalList tail evidence) := by
          rw [headFacts.next_eq, enumerateFrom_append]
        exact rearranged.trans (joined.trans (List.Perm.of_eq enumerated))

end

/-- Receipts of a plan in incremental order: determined steps, then the
evidence in obligation order, then the residual steps.  Each position is the
index of that step in the completed journal. -/
def linearReceipts {goal : Pattern}
    (plan : OpenDerivation kernelDefinition context goal)
    (evidence : DerivationList kernelDefinition context) : List Receipt :=
  let build := positioned plan evidence 0
  build.determined ++ build.evidence ++ build.residual

/-- **Write-only journals of a linear plan are permutations.**  The plan cites
each obligation once, in index order. -/
theorem journals_perm_of_linear {goal : Pattern}
    (plan : OpenDerivation kernelDefinition context goal)
    (evidence : DerivationList kernelDefinition context)
    (linear : holeOccurrences plan = List.finRange context.length) :
    List.Perm
      (run journalExecutor (plan.discharge evidence) []).2
      (incremental journalExecutor plan evidence []).2 := by
  have facts := positioned_facts plan evidence 0
  have mapped := facts.permutation.map Prod.snd
  simp only [List.map_append, facts.determined_snd, facts.evidence_snd, facts.residual_snd,
    enumerateFrom_snd, holeList_spec plan, linear, journals_finRange] at mapped
  have completed :
      (run journalExecutor (plan.discharge evidence) []).2 = citedJournal plan evidence :=
    (run_journal (plan.discharge evidence) []).trans (discharge_journal plan evidence)
  have parts := incremental_journal_parts plan evidence []
  exact (List.Perm.of_eq completed).trans
    (mapped.symm.trans (List.Perm.of_eq parts.symm))

/-- The receipts carry the incremental journal. -/
theorem linearReceipts_carry_journal {goal : Pattern}
    (plan : OpenDerivation kernelDefinition context goal)
    (evidence : DerivationList kernelDefinition context)
    (linear : holeOccurrences plan = List.finRange context.length) :
    (linearReceipts plan evidence).map Prod.snd =
      (incremental journalExecutor plan evidence []).2 := by
  have facts := positioned_facts plan evidence 0
  have parts := incremental_journal_parts plan evidence []
  calc
    (linearReceipts plan evidence).map Prod.snd
        = determinedRules plan ++ journalsAt evidence (holeList plan) ++ residualRules plan := by
          simp only [linearReceipts, List.map_append, facts.determined_snd, facts.evidence_snd,
            facts.residual_snd]
    _ = determinedRules plan ++ ruleJournalList evidence ++ residualRules plan := by
          simp only [holeList_spec plan, linear, journals_finRange]
    _ = (incremental journalExecutor plan evidence []).2 := parts.symm

/-- **Receipts of plan position restore the completed journal.** -/
theorem linearReceipts_restore_order {goal : Pattern}
    (plan : OpenDerivation kernelDefinition context goal)
    (evidence : DerivationList kernelDefinition context)
    (_linear : holeOccurrences plan = List.finRange context.length) :
    ((linearReceipts plan evidence).insertionSort fun first second => first.1 ≤ second.1).map
        Prod.snd =
      (run journalExecutor (plan.discharge evidence) []).2 := by
  have facts := positioned_facts plan evidence 0
  have sortRelation :
      (linearReceipts plan evidence).insertionSort (fun first second => first.1 ≤ second.1) =
        enumerateFrom 0 (citedJournal plan evidence) := by
    have sortPerm :=
      insertionSort_perm (r := fun first second : Receipt => first.1 ≤ second.1)
        (linearReceipts plan evidence)
    have sorted :
        ((linearReceipts plan evidence).insertionSort
            (fun first second => first.1 ≤ second.1)).Pairwise
          (fun first second => first.1 ≤ second.1) :=
      insertionSort_pairwise (r := fun first second : Receipt => first.1 ≤ second.1)
        (fun first second => Nat.le_total first.1 second.1)
        (fun {first second third : Receipt} (forward : first.1 ≤ second.1)
            (backward : second.1 ≤ third.1) => Nat.le_trans forward backward)
        (linearReceipts plan evidence)
    have targetSorted :=
      enumerateFrom_pairwise 0 (citedJournal plan evidence)
    have sameOrder :
        List.Perm
          ((linearReceipts plan evidence).insertionSort
            (fun first second => first.1 ≤ second.1))
          (enumerateFrom 0 (citedJournal plan evidence)) := by
      simp only [linearReceipts] at sortPerm
      exact sortPerm.trans facts.permutation
    exact List.Perm.eq_of_pairwise
      (le := fun first second : Receipt => first.1 ≤ second.1)
      (fun first second firstMember secondMember forward backward => by
        have sameIndex : first.1 = second.1 := Nat.le_antisymm forward backward
        have firstTarget :
            first ∈ enumerateFrom 0 (citedJournal plan evidence) :=
          sameOrder.subset firstMember
        exact enumerateFrom_unique 0 (citedJournal plan evidence) first firstTarget
          second secondMember sameIndex)
      sorted targetSorted sameOrder
  rw [sortRelation, enumerateFrom_snd]
  exact (discharge_journal plan evidence).symm.trans
    (run_journal (plan.discharge evidence) []).symm

/-- **A read-back effect is not repaired by reordering the journal.**
`both(axA₁, ab(axA₁))` yields 1 in plan order and 10 incrementally. -/
theorem readback_not_a_permutation :
    (run Controls.tickExecutor (planBoth.discharge (.cons dA₁ .nil)) 0).1 ≠
      (incremental Controls.tickExecutor planBoth (.cons dA₁ .nil) 0).1 :=
  Controls.commutation_fails

/-- `both(?A, ab(axA₁))` cites its one obligation once, in index order. -/
theorem planBoth_is_linear : holeOccurrences planBoth = List.finRange 1 := by
  decide

/-- The general receipts of that plan are the instance receipts. -/
theorem planBoth_receipts :
    linearReceipts planBoth (.cons dA₁ .nil) = incrementalReceipts := by
  decide

end Mettapedia.GSLT.ProofPlans.WorkPlans
