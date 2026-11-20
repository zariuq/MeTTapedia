import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Language
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleInstanceSets
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.IssuedNamesControls

/-!
# Admitted firings of a ground program, read on the bag of rows

On the ground first-order step (`NamesOnTheStep.IssuingControls.ground`: the identity is the only solution
and equal means identical), the step of a program as a set of rule instances
(`LogicOverTheStep.ProgramAdequacy.program`, which `RuleInstanceSets.instanceSet_eq` equates with the step of
the program for ground programs) is read here on the bag of labels of the present rows (`bagOf`).

A configuration's knowledge is **trivial** when each of its equations has identical sides (`Trivial`): on
ground terms this is exactly solvability (`consistent_iff_trivial`).

* `succ_bag`: every admitted firing of a rule, from a configuration with trivial knowledge, takes the rule's
  consumed rows out of the bag and puts its yielded rows in (`consumes`, `yields`: reads deduplicated, since
  reads may share an occurrence and takes may not); its guards hold; the knowledge stays trivial.
* `succ_of_bag`: conversely, for a rule of the positive fragment whose guards hold, every way of finding its
  consumed rows in the bag is the effect of an admitted firing, given fresh identities for every label
  (`ProgramAdequacy.Supply`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation

open NamesOnTheStep (Expr)
open NamesOnTheStep.IssuingControls (ground)
open LogicOverTheStep.ProgramAdequacy (program program_succ_iff Supply freshList)
open LogicOverTheStep.StepSpan (Succ)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open OneFrame (bodies)

universe uO

variable {O : Type uO} [DecidableEq O] (label : O → Expr)

/-- **The bag of rows** of a configuration: the labels of its present occurrences. -/
def bagOf (C : Configuration Expr O) : Multiset Expr := C.present.val.map label

/-- **Trivial knowledge**: every equation has identical sides. -/
def Trivial (store : EquationStore Expr) : Prop := ∀ e ∈ store, e.1 = e.2

/-- **On ground terms a knowledge is solvable exactly when it is trivial.** -/
theorem consistent_iff_trivial (store : EquationStore Expr) : ground.Consistent store ↔ Trivial store :=
  ⟨fun ⟨_, solved⟩ => solved, fun trivial => ⟨(), trivial⟩⟩

/-! ## Finite sets of occurrences, read as bags -/

theorem val_union_of_disjoint {s t : Finset O} (apart : Disjoint s t) :
    (s ∪ t).val = s.val + t.val := by
  rw [← Finset.disjUnion_eq_union s t apart]
  rfl

theorem val_eq_add_sdiff {s t : Finset O} (inside : s ⊆ t) : t.val = s.val + (t \ s).val := by
  rw [Finset.sdiff_val]
  exact (add_tsub_cancel_of_le (Finset.val_le_iff.mpr inside)).symm

theorem toFinset_val_of_nodup {l : List O} (nodup : l.Nodup) : l.toFinset.val = (l : Multiset O) := by
  rw [List.toFinset_val, List.dedup_eq_self.mpr nodup]

omit [DecidableEq O] in
theorem map_eq_of_forall₂ : ∀ {ps : List Expr} {os : List O}, List.Forall₂ (fun p o => p = label o) ps os →
    os.map label = ps
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons head tail => by rw [List.map_cons, map_eq_of_forall₂ tail, head]

omit [DecidableEq O] in
/-- The equations of patterns with rows carrying them are trivial. -/
theorem equations_trivial : ∀ (os : List O), Trivial (Selection.equations label (os.map label) os)
  | [] => fun _ member => absurd member List.not_mem_nil
  | o :: os => by
      intro e member
      simp only [Selection.equations, List.map_cons, List.zipWith_cons_cons, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact equations_trivial os e member

/-- **Distinct occurrences carrying a sub-bag of a finite set's labels.** -/
theorem exists_taken : ∀ (l : List Expr) (s : Finset O), (l : Multiset Expr) ≤ s.val.map label →
    ∃ os : List O, os.Nodup ∧ (∀ o ∈ os, o ∈ s) ∧ os.map label = l
  | [], _, _ => ⟨[], List.nodup_nil, fun _ member => absurd member List.not_mem_nil, rfl⟩
  | x :: l, s, le => by
      have inside : x ∈ s.val.map label := Multiset.mem_of_le le (Multiset.mem_coe.mpr List.mem_cons_self)
      obtain ⟨o, inS, labelled⟩ := Multiset.mem_map.mp inside
      have split : s.val.map label = label o ::ₘ (s.erase o).val.map label := by
        rw [Finset.erase_val, ← Multiset.map_cons, Multiset.cons_erase inS]
      rw [split, labelled, ← Multiset.cons_coe] at le
      obtain ⟨os, nodup, within, mapped⟩ := exists_taken l (s.erase o) ((Multiset.cons_le_cons_iff x).mp le)
      refine ⟨o :: os, List.nodup_cons.mpr ⟨fun member => Finset.notMem_erase o s (within o member), nodup⟩, ?_,
        by rw [List.map_cons, mapped, labelled]⟩
      intro p member
      rcases List.mem_cons.mp member with rfl | member
      · exact inS
      · exact Finset.mem_of_mem_erase (within p member)

omit [DecidableEq O] in
/-- **Occurrences carrying labels found in a finite set**, possibly repeated. -/
theorem exists_read : ∀ (l : List Expr) (D : Finset O), (∀ x ∈ l, x ∈ D.val.map label) →
    ∃ os : List O, (∀ o ∈ os, o ∈ D) ∧ os.map label = l
  | [], _, _ => ⟨[], fun _ member => absurd member List.not_mem_nil, rfl⟩
  | x :: l, D, each => by
      obtain ⟨o, inD, labelled⟩ := Multiset.mem_map.mp (each x List.mem_cons_self)
      obtain ⟨os, within, mapped⟩ := exists_read l D fun y member => each y (List.mem_cons_of_mem _ member)
      refine ⟨o :: os, ?_, by rw [List.map_cons, mapped, labelled]⟩
      intro p member
      rcases List.mem_cons.mp member with rfl | member
      · exact Finset.mem_val.mp inD
      · exact within p member

/-! ## What an admitted firing does to the bag -/

/-- The bag of a configuration splits into its taken rows and the rest of its rows. -/
theorem bagOf_split {C : Configuration Expr O} {taken : List O} (nodup : taken.Nodup)
    (inside : taken.toFinset ⊆ C.present) :
    bagOf label C = (taken.map label : Multiset Expr) + (C.present \ taken.toFinset).val.map label := by
  unfold bagOf
  rw [val_eq_add_sdiff inside, Multiset.map_add, toFinset_val_of_nodup nodup, Multiset.map_coe]

/-- The rest of a configuration's rows, after a commit, with the made rows. -/
theorem bagOf_result {rule : RuleInstance Expr} {sel : Selection O} {C : Configuration Expr O}
    (madeNodup : sel.made.Nodup) (fresh : Disjoint sel.made.toFinset C.present)
    (outputs : sel.made.map label = rule.produce) :
    bagOf label (sel.result label rule C) =
      (C.present \ sel.taken.toFinset).val.map label + (rule.produce : Multiset Expr) := by
  unfold bagOf
  show (fire C.present (sel.commit (T := Expr))).val.map label = _
  have apart : Disjoint (C.present \ sel.taken.toFinset) sel.made.toFinset :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset fresh.symm
  unfold fire
  show ((C.present \ sel.taken.toFinset) ∪ sel.made.toFinset).val.map label = _
  rw [val_union_of_disjoint apart, Multiset.map_add, toFinset_val_of_nodup madeNodup, Multiset.map_coe, outputs]

/-- **An admitted firing takes its consumed rows out of the bag and puts its yielded rows in.** -/
theorem bag_of_valid {rule : RuleInstance Expr} {sel : Selection O} {C : Configuration Expr O}
    (valid : sel.Valid ground label rule C) :
    ∃ rest : Multiset Expr, ((rule.take ++ rule.read.dedup : List Expr) : Multiset Expr) + rest = bagOf label C ∧
      bagOf label (sel.result label rule C) = ((rule.produce ++ rule.read.dedup : List Expr) : Multiset Expr) + rest := by
  obtain ⟨σ, solved⟩ := valid.consistent
  obtain ⟨-, takes, reads, -⟩ := Selection.models_problem ground valid solved
  have takenLabels : sel.taken.map label = rule.take := map_eq_of_forall₂ label takes
  have readLabels : sel.read.map label = rule.read := map_eq_of_forall₂ label reads
  have enabled := valid.occurrences
  have readInD : ∀ x ∈ rule.read, x ∈ (C.present \ sel.taken.toFinset).val.map label := by
    intro x member
    rw [← readLabels] at member
    obtain ⟨o, inRead, rfl⟩ := List.mem_map.mp member
    have readO : o ∈ sel.read.toFinset := List.mem_toFinset.mpr inRead
    have present : o ∈ C.present := enabled.kept_subset readO
    have notTaken : o ∉ sel.taken.toFinset := fun taken => Finset.disjoint_left.mp enabled.apart taken readO
    exact Multiset.mem_map_of_mem label (Finset.mem_val.mpr (Finset.mem_sdiff.mpr ⟨present, notTaken⟩))
  have dedupLe : ((rule.read.dedup : List Expr) : Multiset Expr) ≤
      (C.present \ sel.taken.toFinset).val.map label := by
    refine (Multiset.le_iff_subset (Multiset.coe_nodup.mpr (List.nodup_dedup _))).mpr ?_
    intro x member
    exact readInD x (List.mem_dedup.mp (Multiset.mem_coe.mp member))
  refine ⟨(C.present \ sel.taken.toFinset).val.map label - (rule.read.dedup : Multiset Expr), ?_, ?_⟩
  · rw [bagOf_split label valid.take_distinct enabled.taken_subset, takenLabels, ← Multiset.coe_add, add_assoc,
      add_tsub_cancel_of_le dedupLe]
  · rw [bagOf_result label valid.output_distinct enabled.fresh valid.outputs, ← Multiset.coe_add, add_assoc,
      add_tsub_cancel_of_le dedupLe]
    exact add_comm _ _

/-- **An admitted firing's guards hold**, and its result's knowledge stays trivial. -/
theorem guards_of_valid {rule : RuleInstance Expr} {sel : Selection O} {C : Configuration Expr O}
    (valid : sel.Valid ground label rule C) :
    (∀ e ∈ rule.tell, e.1 = e.2) ∧ (∀ c ∈ rule.checks, groundCheck c = true) ∧
      Trivial (sel.result label rule C).equations := by
  obtain ⟨σ, solved⟩ := valid.consistent
  refine ⟨fun e member => (Selection.models_problem ground valid solved).2.2.2 e member, ?_, solved⟩
  intro c member
  cases c with
  | equal left right =>
      have holds := valid.checks _ member σ solved
      simp only [groundCheck, decide_eq_true_eq]
      exact holds
  | predicate quantifier _ => rfl
  | count _ _ => rfl

/-! ## Every way of finding the consumed rows is an admitted firing -/

/-- **A rule instance whose checks are trivial equations and whose tells are trivial fires wherever its
consumed rows are found in the bag**, given fresh identities for every label. -/
theorem valid_of_bag (supply : Supply label) {rule : RuleInstance Expr} {C : Configuration Expr O}
    (knowledge : Trivial C.equations) (tells : Trivial rule.tell)
    (checks : ∀ c ∈ rule.checks, ∃ t, c = .equal t t) {rest : Multiset Expr}
    (split : ((rule.take ++ rule.read.dedup : List Expr) : Multiset Expr) + rest = bagOf label C) :
    ∃ sel : Selection O, sel.Valid ground label rule C ∧
      bagOf label (sel.result label rule C) = ((rule.produce ++ rule.read.dedup : List Expr) : Multiset Expr) + rest := by
  rw [← Multiset.coe_add, add_assoc] at split
  obtain ⟨taken, takenNodup, takenIn, takenLabels⟩ :=
    exists_taken label rule.take C.present
      (show (rule.take : Multiset Expr) ≤ C.present.val.map label from (le_add_right le_rfl).trans_eq split)
  have takenSub : taken.toFinset ⊆ C.present := fun o member => takenIn o (List.mem_toFinset.mp member)
  have restEq : ((rule.read.dedup : List Expr) : Multiset Expr) + rest =
      (C.present \ taken.toFinset).val.map label := by
    have whole := bagOf_split label (C := C) takenNodup takenSub
    rw [takenLabels, ← split] at whole
    exact add_left_cancel whole
  obtain ⟨read, readIn, readLabels⟩ := exists_read label rule.read (C.present \ taken.toFinset) (by
    intro x member
    rw [← restEq]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_coe.mpr (List.mem_dedup.mpr member))))
  obtain ⟨made, madeNodup, madeFresh, madeLabels⟩ := freshList label supply C.present rule.produce
  have freshDisjoint : Disjoint made.toFinset C.present :=
    Finset.disjoint_left.mpr fun o member present => madeFresh o (List.mem_toFinset.mp member) present
  have problemTrivial : Trivial ((⟨taken, read, made⟩ : Selection O).problem label rule C) := by
    intro e member
    simp only [Selection.problem, List.mem_append] at member
    rcases member with ((old | taking) | reading) | told
    · exact knowledge e old
    · rw [← takenLabels] at taking
      exact equations_trivial label taken e taking
    · rw [← readLabels] at reading
      exact equations_trivial label read e reading
    · exact tells e told
  have valid : (⟨taken, read, made⟩ : Selection O).Valid ground label rule C := {
    take_distinct := takenNodup
    output_distinct := madeNodup
    take_length := by rw [← takenLabels, List.length_map]
    read_length := by rw [← readLabels, List.length_map]
    outputs := madeLabels
    occurrences := ⟨takenSub, fun o member => (Finset.mem_sdiff.mp (readIn o (List.mem_toFinset.mp member))).1,
      Finset.disjoint_left.mpr fun o taking reading =>
        (Finset.mem_sdiff.mp (readIn o (List.mem_toFinset.mp reading))).2 taking,
      freshDisjoint, fun query member => by simp [Selection.commit] at member⟩
    consistent := (consistent_iff_trivial _).mpr problemTrivial
    checks := by
      intro c member σ _
      obtain ⟨t, rfl⟩ := checks c member
      rfl }
  refine ⟨⟨taken, read, made⟩, valid, ?_⟩
  rw [bagOf_result label (sel := ⟨taken, read, made⟩) madeNodup freshDisjoint madeLabels]
  show (C.present \ taken.toFinset).val.map label + _ = _
  rw [← restEq, ← Multiset.coe_add]
  exact (add_comm _ _).trans (add_assoc _ _ _).symm

/-! ## On the rules of a program -/

variable {rules : List (Rule Rows)}

/-- **Every successor of the step of a program, from trivial knowledge, replaces a rule's consumed rows by its
yielded rows**, the rule's guards hold, and the knowledge stays trivial. -/
theorem succ_bag {C C' : Configuration Expr O}
    (step : Succ (program ground label (bodies {r | r ∈ rules})) C C') :
    ∃ r ∈ rules, guardsHold r = true ∧ ∃ rest : Multiset Expr,
      ((consumes r : List Expr) : Multiset Expr) + rest = bagOf label C ∧
        bagOf label C' = ((yields r : List Expr) : Multiset Expr) + rest ∧ Trivial C'.equations := by
  obtain ⟨rule, sel, ⟨r, inRules, rfl⟩, valid, rfl⟩ := (program_succ_iff ground label _ C C').mp step
  obtain ⟨tells, checks, knowledge⟩ := guards_of_valid label valid
  obtain ⟨rest, before, after⟩ := bag_of_valid label valid
  refine ⟨r, inRules, ?_, rest, before, after, knowledge⟩
  simp only [guardsHold, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨tells, checks⟩

/-- A rule of the fragment whose guards hold has trivial equation checks. -/
theorem checks_trivial {r : Rule Rows} (positive : Positive r) (holds : guardsHold r = true) :
    ∀ c ∈ r.body.checks, ∃ t, c = .equal t t := by
  intro c member
  have equation := List.all_eq_true.mp positive.2 c member
  simp only [guardsHold, Bool.and_eq_true, List.all_eq_true] at holds
  have trivial := holds.2 c member
  cases c with
  | equal left right =>
      simp only [groundCheck, decide_eq_true_eq] at trivial
      exact ⟨left, by rw [trivial]⟩
  | predicate quantifier _ => cases equation
  | count _ _ => cases equation

/-- **For a rule of the fragment whose guards hold, every way of finding its consumed rows in the bag is an
admitted firing**, given fresh identities for every label. -/
theorem succ_of_bag (supply : Supply label) {r : Rule Rows} (member : r ∈ rules) (positive : Positive r)
    (holds : guardsHold r = true) {C : Configuration Expr O} (knowledge : Trivial C.equations)
    {rest : Multiset Expr} (split : ((consumes r : List Expr) : Multiset Expr) + rest = bagOf label C) :
    ∃ C', Succ (program ground label (bodies {r | r ∈ rules})) C C' ∧
      bagOf label C' = ((yields r : List Expr) : Multiset Expr) + rest := by
  have tells : Trivial r.body.tell := by
    simp only [guardsHold, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at holds
    exact holds.1
  obtain ⟨sel, valid, bag⟩ := valid_of_bag label supply knowledge tells (checks_trivial positive holds) split
  exact ⟨_, (program_succ_iff ground label _ C _).mpr ⟨r.body, sel, ⟨r, member, rfl⟩, valid, rfl⟩, bag⟩

#print axioms consistent_iff_trivial
#print axioms exists_taken
#print axioms bag_of_valid
#print axioms guards_of_valid
#print axioms valid_of_bag
#print axioms succ_bag
#print axioms succ_of_bag

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation
