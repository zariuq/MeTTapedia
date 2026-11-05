import Mettapedia.Languages.CHR.Operational
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Sort

/-! An explicit newest-first partner policy and the logical obligations of
an exhausted candidate search. Ordering preserves every candidate occurrence;
guards and propagation history decide which candidate may fire. The proofs
below connect those finite decisions to the independent refined relation.
Completeness of a concrete match producer remains a separate obligation. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.PartnerSelection

structure Candidate where
  environment : Environment
  selection : Selection
  deriving Repr, DecidableEq

def priority (candidate : Candidate) : List Nat := candidate.selection.heads.map Occurrence.id

def newerIds : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | first :: rest, second :: tail =>
      if first == second then newerIds rest tail else decide (second < first)

theorem newerIds_lex (first second : List Nat) :
    newerIds first second = true ↔ List.Lex (fun a b : Nat => b < a) first second := by
  induction first generalizing second with
  | nil => cases second <;> simp [newerIds]
  | cons first rest ih =>
      cases second with
      | nil => simp [newerIds]
      | cons second tail =>
          by_cases same : first = second
          · subst second
            simp [newerIds, List.cons_lex_cons_iff, ih]
          · have unequal : (first == second) = false := beq_eq_false_iff_ne.mpr same
            simp [newerIds, unequal, List.cons_lex_cons_iff, same]

theorem newerIds_irrefl (ids : List Nat) : newerIds ids ids = false := by
  apply Bool.eq_false_iff.mpr
  intro contrary
  exact List.lex_irrefl (r := fun a b : Nat => b < a) (fun _ => Nat.lt_irrefl _) ids
    ((newerIds_lex ids ids).mp contrary)

def preferred (first second : Candidate) : Bool :=
  priority first == priority second || newerIds (priority first) (priority second)

theorem preferred_iff (first second : Candidate) : preferred first second = true ↔
    priority first = priority second ∨ List.Lex (fun a b : Nat => b < a) (priority first) (priority second) := by
  simp only [preferred, Bool.or_eq_true, beq_iff_eq, newerIds_lex]

theorem newerIds_total (first second : List Nat) :
    first = second ∨ newerIds first second = true ∨ newerIds second first = true := by
  induction first generalizing second with
  | nil => cases second <;> simp [newerIds]
  | cons first rest ih =>
      cases second with
      | nil => simp [newerIds]
      | cons second tail =>
          by_cases same : first = second
          · subst second
            simpa [newerIds] using ih tail
          · have reverse : second ≠ first := Ne.symm same
            rcases lt_or_gt_of_ne same with less | greater
            · exact .inr (.inr (by simp [newerIds, reverse, less]))
            · exact .inr (.inl (by simp [newerIds, same, greater]))

theorem preferred_total (first second : Candidate) : preferred first second = true ∨ preferred second first = true := by
  rcases newerIds_total (priority first) (priority second) with same | earlier | later
  · exact .inl (by simp [preferred, same])
  · exact .inl (by simp [preferred, earlier])
  · exact .inr (by simp [preferred, later])

theorem preferred_trans (first second third : Candidate)
    (one : preferred first second = true) (two : preferred second third = true) :
    preferred first third = true := by
  apply (preferred_iff first third).mpr
  rcases (preferred_iff first second).mp one with same | earlier
  · simpa only [same] using (preferred_iff second third).mp two
  · rcases (preferred_iff second third).mp two with same | later
    · exact .inr (same ▸ earlier)
    · exact .inr (List.lex_trans (fun one two => Nat.lt_trans two one) earlier later)

def insert (candidate : Candidate) : List Candidate → List Candidate
  | [] => [candidate]
  | first :: rest =>
      if preferred candidate first then candidate :: first :: rest else first :: insert candidate rest

def order : List Candidate → List Candidate
  | [] => []
  | first :: rest => insert first (order rest)

theorem insert_perm (candidate : Candidate) (candidates : List Candidate) :
    (candidate :: candidates).Perm (insert candidate candidates) := by
  induction candidates with
  | nil => exact List.Perm.refl _
  | cons first rest ih =>
      unfold insert
      split
      · exact List.Perm.refl _
      · exact (List.Perm.swap first candidate rest).trans (List.Perm.cons first ih)

theorem order_perm (candidates : List Candidate) : candidates.Perm (order candidates) := by
  induction candidates with
  | nil => exact List.Perm.refl _
  | cons first rest ih => exact (List.Perm.cons first ih).trans (insert_perm first (order rest))

theorem order_member (candidate : Candidate) (candidates : List Candidate) :
    candidate ∈ order candidates ↔ candidate ∈ candidates := (order_perm candidates).mem_iff.symm

private theorem insert_eq_orderedInsert (candidate : Candidate) (candidates : List Candidate) :
    insert candidate candidates = List.orderedInsert (fun first second => preferred first second = true) candidate candidates := by
  induction candidates with
  | nil => rfl
  | cons first rest ih => simp only [insert, List.orderedInsert_cons, ih]

theorem order_eq_insertionSort (candidates : List Candidate) :
    order candidates = List.insertionSort (fun first second => preferred first second = true) candidates := by
  induction candidates with
  | nil => rfl
  | cons first rest ih => simp only [order, List.insertionSort_cons, ih, insert_eq_orderedInsert]

theorem order_sorted (candidates : List Candidate) :
    (order candidates).Pairwise (fun first second => preferred first second = true) := by
  let relation := fun first second : Candidate => preferred first second = true
  let : Std.Total relation := ⟨preferred_total⟩
  let : IsTrans Candidate relation := ⟨preferred_trans⟩
  rw [order_eq_insertionSort]
  exact List.pairwise_insertionSort relation candidates

def choose (rule : Rule) (index : Nat) (history : List Key) :
    List Candidate → Except ArithmeticFault (Option Candidate)
  | [] => .ok none
  | candidate :: rest =>
      if candidate.selection.Fresh rule index history then
        match guardsEval candidate.environment rule.guards with
        | .error reason => .error reason
        | .ok true => .ok (some candidate)
        | .ok false => choose rule index history rest
      else choose rule index history rest

theorem choose_sound (rule : Rule) (index : Nat) (history : List Key)
    (candidates : List Candidate) (chosen : Candidate)
    (accepted : choose rule index history candidates = .ok (some chosen)) :
    chosen ∈ candidates ∧ chosen.selection.Fresh rule index history ∧
      guardsEval chosen.environment rule.guards = .ok true := by
  induction candidates with
  | nil => cases accepted
  | cons first rest ih =>
      by_cases fresh : first.selection.Fresh rule index history
      · cases guarded : guardsEval first.environment rule.guards with
        | error reason => simp [choose, fresh, guarded] at accepted
        | ok answer =>
            cases answer with
            | false =>
                have remaining := ih (by simpa [choose, fresh, guarded] using accepted)
                exact ⟨List.mem_cons_of_mem first remaining.1, remaining.2⟩
            | true =>
                have same : first = chosen := by simpa [choose, fresh, guarded] using accepted
                subst chosen
                exact ⟨List.mem_cons_self, fresh, guarded⟩
      · have remaining := ih (by simpa [choose, fresh] using accepted)
        exact ⟨List.mem_cons_of_mem first remaining.1, remaining.2⟩

theorem choose_exhausted (rule : Rule) (index : Nat) (history : List Key)
    (candidates : List Candidate) (exhausted : choose rule index history candidates = .ok none) :
    ∀ candidate ∈ candidates,
      ¬ candidate.selection.Fresh rule index history ∨
        guardsEval candidate.environment rule.guards = .ok false := by
  induction candidates with
  | nil => simp
  | cons first rest ih =>
      by_cases fresh : first.selection.Fresh rule index history
      · cases guarded : guardsEval first.environment rule.guards with
        | error reason => simp [choose, fresh, guarded] at exhausted
        | ok answer =>
            cases answer with
            | true => simp [choose, fresh, guarded] at exhausted
            | false =>
                have remaining := ih (by simpa [choose, fresh, guarded] using exhausted)
                intro candidate member
                rcases List.mem_cons.mp member with rfl | later
                · exact .inr guarded
                · exact remaining candidate later
      · have remaining := ih (by simpa [choose, fresh] using exhausted)
        intro candidate member
        rcases List.mem_cons.mp member with rfl | later
        · exact .inl fresh
        · exact remaining candidate later

theorem choose_fault_sound (rule : Rule) (index : Nat) (history : List Key)
    (candidates : List Candidate) (reason : ArithmeticFault)
    (faulted : choose rule index history candidates = .error reason) :
    ∃ candidate ∈ candidates, candidate.selection.Fresh rule index history ∧
      guardsEval candidate.environment rule.guards = .error reason := by
  induction candidates with
  | nil => cases faulted
  | cons first rest ih =>
      by_cases fresh : first.selection.Fresh rule index history
      · cases guarded : guardsEval first.environment rule.guards with
        | error actual =>
            have same : actual = reason := by simpa [choose, fresh, guarded] using faulted
            subst actual
            exact ⟨first, List.mem_cons_self, fresh, guarded⟩
        | ok answer =>
            cases answer with
            | true => simp [choose, fresh, guarded] at faulted
            | false =>
                obtain ⟨candidate, member, eligible, failed⟩ := ih (by simpa [choose, fresh, guarded] using faulted)
                exact ⟨candidate, List.mem_cons_of_mem first member, eligible, failed⟩
      · obtain ⟨candidate, member, eligible, failed⟩ := ih (by simpa [choose, fresh] using faulted)
        exact ⟨candidate, List.mem_cons_of_mem first member, eligible, failed⟩

theorem chosen_refined_step (program : Program) (state : State) (rule : Rule)
    (active cursor : Nat) (tail : List Task) (occurrence : RuleOccurrence)
    (candidates : List Candidate) (chosen : Candidate)
    (tasks : state.tasks = .scan active cursor :: tail) (running : state.status = .running)
    (atCursor : (occurrences program)[cursor]? = some occurrence)
    (atRule : program.rules[occurrence.rule]? = some rule)
    (represented : ∀ candidate ∈ candidates,
      candidate.selection.Matches rule candidate.environment state.store ∧
        candidate.selection.ActiveAt active occurrence.head)
    (accepted : choose rule occurrence.rule state.history candidates = .ok (some chosen)) :
    Step program state
      (commit state rule occurrence.rule chosen.environment chosen.selection active cursor tail) := by
  obtain ⟨member, fresh, guarded⟩ := choose_sound rule occurrence.rule state.history candidates chosen accepted
  obtain ⟨matched, activeHead⟩ := represented chosen member
  exact Step.fire state active cursor tail occurrence rule chosen.environment chosen.selection
    tasks running atCursor atRule matched activeHead fresh guarded

theorem exhausted_refined_step (program : Program) (state : State) (rule : Rule)
    (active cursor : Nat) (tail : List Task) (occurrence : RuleOccurrence)
    (candidates : List Candidate)
    (tasks : state.tasks = .scan active cursor :: tail) (running : state.status = .running)
    (atCursor : (occurrences program)[cursor]? = some occurrence)
    (atRule : program.rules[occurrence.rule]? = some rule)
    (covers : ∀ (environment : Environment) (selection : Selection),
      selection.Matches rule environment state.store → selection.ActiveAt active occurrence.head →
        Candidate.mk environment selection ∈ candidates)
    (exhausted : choose rule occurrence.rule state.history candidates = .ok none) :
    Step program state {state with tasks := .scan active (cursor + 1) :: tail} := by
  apply Step.skip state active cursor tail occurrence rule tasks running atCursor atRule
  intro environment selection matched activeHead
  exact choose_exhausted rule occurrence.rule state.history candidates exhausted
    ⟨environment, selection⟩ (covers environment selection matched activeHead)

example : newerIds [2, 16] [2, 15] = true := by decide
example : newerIds [2, 15] [2, 16] = false := by decide
example : newerIds [2, 16] [2, 16] = false := by decide

#print axioms order_perm
#print axioms order_sorted
#print axioms choose_sound
#print axioms choose_exhausted
#print axioms choose_fault_sound
#print axioms chosen_refined_step
#print axioms exhausted_refined_step

end Mettapedia.Languages.CHR.PartnerSelection
