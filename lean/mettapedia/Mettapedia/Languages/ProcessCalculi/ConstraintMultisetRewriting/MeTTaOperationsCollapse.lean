import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsMatch

/-!
# `collapse` as an observation over the valid firings at one store

`collapse` gathers the answers of a completed search. Here it is the bag of
answers of every valid single-read firing at one store
(`MeTTaOperationsMatch.encodedAnswers`). The observation adds no equation and
no occurrence. Only resolved answers escape; the bindings made by one answer
stay inside that answer.

* `answerOccurrences_antitone`, `encodedAnswers_antitone`: a stronger store
  over the same occurrences can only remove answers.
* `OrderEffect`: with a shared variable shared by the collapsed query and a later
  query, collapsing first gives the answers `1 2` and then `2`; constraining
  first gives `2` and then `2`. This is the order effect measured on Hyperon
  Experimental, PeTTa and the CeTTa PeTTa lane. The two bags differ
  (`order_matters`).
* `private_pattern_bag_invariant`: when the collapsed pattern's variables are
  private to the query, the bag does not depend on the store. The CeTTa draft's
  `prime` lane gives `((1 2) 2)` in both orders; its match pattern is private.
* `twin_preserves_validity`: a valid firing stays valid after adding an
  occurrence that copies a stored label with one symbol replaced by a symbol
  that occurs nowhere in the firing's data. Hence
  `validity_never_certifies_completeness`: the five ports of a rule instance
  cannot express that a set of reads is every answer of an open query. The
  bag is computed outside the step.
* `predicate_query_detects_twin`: the occurrence-commit layer under the
  candidate step has the missing primitive. A predicate query that selects
  the query's matches is spoiled by the same added occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsCollapse

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (fire PredicateQuery regionOf)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsMatch

variable {O : Type*} [DecidableEq O]

/-! ## The observation -/

/-- The answer occurrences are those whose single-read firing keeps the store
consistent; no freshness of the pattern is assumed. -/
theorem mem_answerOccurrences_iff_consistent {label : O → Atom} {pattern template : Atom}
    {before : Configuration Atom O} (supply : ∃ m, m ∉ before.present ∧ label m = template) (o : O) :
    o ∈ answerOccurrences label pattern template before ↔
      o ∈ before.present ∧ atomAction.Consistent (before.equations ++ [(pattern, label o)]) := by
  classical
  unfold answerOccurrences
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨present, m, valid⟩
    exact ⟨present, ((valid_iff label pattern template before o m).mp valid).2.2.2⟩
  · rintro ⟨present, consistent⟩
    obtain ⟨m, notPresent, labelled⟩ := supply
    exact ⟨present, m, (valid_iff label pattern template before o m).mpr
      ⟨present, notPresent, labelled, consistent⟩⟩

/-- A stronger store over the same occurrences admits fewer answers. -/
theorem answerOccurrences_antitone {label : O → Atom} {pattern template : Atom}
    {weaker stronger : Configuration Atom O} (samePresent : stronger.present = weaker.present)
    (refines : atomAction.Refines stronger.equations weaker.equations) :
    answerOccurrences label pattern template stronger ⊆ answerOccurrences label pattern template weaker := by
  classical
  intro o member
  unfold answerOccurrences at member ⊢
  rw [Finset.mem_filter] at member ⊢
  obtain ⟨present, m, valid⟩ := member
  obtain ⟨_, fresh, labelled, ⟨σ, solved⟩⟩ := (valid_iff label pattern template stronger o m).mp valid
  refine ⟨samePresent ▸ present, m, (valid_iff label pattern template weaker o m).mpr
    ⟨samePresent ▸ present, samePresent ▸ fresh, labelled, ⟨σ, ?_⟩⟩⟩
  obtain ⟨old, new⟩ := (atomAction.models_append σ _ _).mp solved
  exact (atomAction.models_append σ _ _).mpr ⟨refines σ old, new⟩

theorem encodedAnswers_antitone {label : O → Atom} {pattern template : Atom}
    {weaker stronger : Configuration Atom O} (samePresent : stronger.present = weaker.present)
    (refines : atomAction.Refines stronger.equations weaker.equations) :
    encodedAnswers label pattern template stronger ≤ encodedAnswers label pattern template weaker :=
  Multiset.map_le_map (Finset.val_le_iff.mpr (answerOccurrences_antitone samePresent refines))

/-- With a pattern private to the query, the bag is the reference bag of the
stored labels at every consistent store: no constraint elsewhere reaches it. -/
theorem private_pattern_bag_invariant {label : O → Atom} {pattern template : Atom}
    {first second : Configuration Atom O} (one : Prepared label pattern template first)
    (two : Prepared label pattern template second) (samePresent : first.present = second.present) :
    encodedAnswers label pattern template first = encodedAnswers label pattern template second := by
  rw [encodedAnswers_eq_reference one, encodedAnswers_eq_reference two, samePresent]

/-! ## The order effect -/

theorem atom_ne_wrap (atom : Atom) (head : String) : atom ≠ Insertion.wrap head atom := by
  intro equal
  have sizes := congrArg sizeOf equal
  simp [Insertion.wrap] at sizes
  omega

namespace OrderEffect

def one : Atom := .symbol "1"
def two : Atom := .symbol "2"
def p (value : Atom) : Atom := Insertion.wrap "p" value
def q (value : Atom) : Atom := Insertion.wrap "q" value
def x : Atom := .var "x"
def y : Atom := .var "y"

/-- `(p 1)`, `(p 2)` and `(q 2)`; output occurrences carry the templates `$x` or `$y`. -/
def label (n : Nat) : Atom :=
  if n = 0 then p one else if n = 1 then p two else if n = 2 then q two else if n = 6 then y else x

def before : Configuration Atom Nat := ⟨[], {0, 1, 2}⟩

/-- `(match &self (q $x) $x)` with the same live `x` as the collapsed query. -/
def constrain : Selection Nat := selection 2 4

def constrained : Configuration Atom Nat := constrain.result label (rule (q x) x) before

theorem one_ne_two : one ≠ two := by decide

theorem p_inj {a b : Atom} (same : p a = p b) : a = b := by
  simpa [p, Insertion.wrap] using same

theorem p_ne_q (a b : Atom) : p a ≠ q b := by
  simp [p, q, Insertion.wrap]

theorem constrain_valid : constrain.Valid atomAction label (rule (q x) x) before := by
  refine (valid_iff label (q x) x before 2 4).mpr ⟨by decide, by decide, rfl, ?_⟩
  refine ⟨Insertion.single "x" two, ?_⟩
  intro e member
  simp only [before, List.nil_append, List.mem_singleton] at member
  subst member
  change subst _ (q x) = subst _ (label 2)
  simp [q, x, label, Insertion.subst_wrap, two, subst, Insertion.single]

theorem constrained_equations : constrained.equations = [(q x, q two)] := by
  simp [constrained, constrain, Selection.result, problem_eq, before, label]

theorem constrained_present : constrained.present = {0, 1, 2, 4} := by
  simp [constrained, constrain, Selection.result, Selection.commit, selection, fire, before]

theorem supply_before : ∃ m, m ∉ before.present ∧ label m = x := ⟨5, by decide, rfl⟩

theorem supply_constrained : ∃ m, m ∉ constrained.present ∧ label m = x :=
  ⟨5, by rw [constrained_present]; decide, rfl⟩

theorem answer_p (value : Atom) : answer (p x) x (p value) = value := by
  have covered : Covered (p x) x := by
    intro v member
    simpa [p, x, Insertion.wrap, vars, vars.varsList] using member
  rw [answer_eq_of_solution covered (τ := Insertion.single "x" value) (by simp [p, x])]
  simp [x]


theorem consistent_p {value : Atom} (ground : vars value = []) :
    atomAction.Consistent ([] ++ [(p x, p value)]) := by
  refine ⟨Insertion.single "x" value, ?_⟩
  intro e member
  simp only [List.nil_append, List.mem_singleton] at member
  subst member
  change subst _ (p x) = subst _ (p value)
  rw [subst_of_vars_eq_nil _ (p value) (by simpa [p, Insertion.wrap, vars, vars.varsList] using ground)]
  simp [p, x]

theorem not_consistent_p_q (value : Atom) (store : EquationStore Atom) :
    ¬ atomAction.Consistent (store ++ [(p x, q value)]) := by
  rintro ⟨σ, solved⟩
  have equation := solved (p x, q value) (by simp)
  change subst σ (p x) = subst σ (q value) at equation
  simp only [p, q, Insertion.subst_wrap] at equation
  simp [Insertion.wrap] at equation

theorem collapse_first : answerOccurrences label (p x) x before = {0, 1} := by
  ext o
  rw [mem_answerOccurrences_iff_consistent supply_before]
  constructor
  · rintro ⟨present, consistent⟩
    simp only [before, Finset.mem_insert, Finset.mem_singleton] at present ⊢
    rcases present with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr rfl
    · exact absurd consistent (by simpa [before, label] using not_consistent_p_q two [])
  · intro member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact ⟨by decide, by simpa [before, label] using consistent_p (value := one) rfl⟩
    · exact ⟨by decide, by simpa [before, label] using consistent_p (value := two) rfl⟩

theorem pair_val : ({0, 1} : Finset Nat).val = {0, 1} := by decide

theorem collapse_first_bag : encodedAnswers label (p x) x before = {one, two} := by
  unfold encodedAnswers
  rw [collapse_first, pair_val]
  simp [label, answer_p]

/-- After the constraining firing, every solution reads its answer as `2`. -/
theorem constrained_resolves (σ : Subst) (solved : atomAction.Models σ constrained.equations) :
    subst σ x = two := by
  rw [constrained_equations] at solved
  have equation := solved (q x, q two) (by simp)
  change subst σ (q x) = subst σ (q two) at equation
  simp only [q, Insertion.subst_wrap] at equation
  simpa [Insertion.wrap, two, subst] using equation

theorem subst_x_of_p {σ : Subst} {value : Atom} (equation : subst σ (p x) = subst σ (p value))
    (ground : value = one ∨ value = two) : subst σ x = value := by
  simp only [p, Insertion.subst_wrap] at equation
  rcases ground with rfl | rfl <;> simpa [Insertion.wrap, one, two, subst] using equation

theorem constrain_first : answerOccurrences label (p x) x constrained = {1} := by
  ext o
  rw [mem_answerOccurrences_iff_consistent supply_constrained, constrained_present,
    constrained_equations]
  constructor
  · rintro ⟨present, ⟨σ, solved⟩⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at present ⊢
    have bound : subst σ x = two := by
      have equation := solved (q x, q two) (by simp)
      change subst σ (q x) = subst σ (q two) at equation
      simp only [q, Insertion.subst_wrap] at equation
      simpa [Insertion.wrap, two, subst] using equation
    rcases present with rfl | rfl | rfl | rfl
    · have equation := solved (p x, label 0) (by simp)
      change subst σ (p x) = subst σ (label 0) at equation
      have value := subst_x_of_p (value := one) (by simpa [label] using equation) (.inl rfl)
      rw [bound] at value
      exact absurd value.symm one_ne_two
    · rfl
    · have consistent : atomAction.Consistent ([(q x, q two)] ++ [(p x, label 2)]) := ⟨σ, solved⟩
      have labelled : label 2 = q two := by simp [label]
      rw [labelled] at consistent
      exact (not_consistent_p_q two [(q x, q two)] consistent).elim
    · have equation := solved (p x, label 4) (by simp)
      change subst σ (p x) = subst σ (label 4) at equation
      simp only [label, show (4 : Nat) ≠ 0 by decide, show (4 : Nat) ≠ 1 by decide,
        show (4 : Nat) ≠ 2 by decide, show (4 : Nat) ≠ 6 by decide, if_false, p,
        Insertion.subst_wrap] at equation
      exact absurd equation.symm (atom_ne_wrap _ _)
  · intro member
    simp only [Finset.mem_singleton] at member
    subst member
    refine ⟨by decide, Insertion.single "x" two, ?_⟩
    intro e member
    simp only [List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change subst _ (q x) = subst _ (q two)
      simp [q, x, two, subst, Insertion.single]
    · change subst _ (p x) = subst _ (label 1)
      simp [p, x, two, label, subst, Insertion.single]

theorem singleton_val : ({1} : Finset Nat).val = {1} := rfl

theorem constrain_first_bag : encodedAnswers label (p x) x constrained = {two} := by
  unfold encodedAnswers
  rw [constrain_first, singleton_val]
  simp [label, answer_p]

/-- The two orders observe different bags: `((1 2) 2)` against `((2) 2)`. -/
theorem order_matters :
    encodedAnswers label (p x) x before = {one, two} ∧ constrain.Valid atomAction label (rule (q x) x) before ∧
      (∀ σ, atomAction.Models σ constrained.equations → subst σ x = two) ∧
      encodedAnswers label (p x) x constrained = {two} ∧
      encodedAnswers label (p x) x constrained ≠ encodedAnswers label (p x) x before := by
  refine ⟨collapse_first_bag, constrain_valid, constrained_resolves, constrain_first_bag, ?_⟩
  rw [constrain_first_bag, collapse_first_bag]
  intro same
  have sizes := congrArg Multiset.card same
  simp at sizes


theorem bound_of_constrained {σ : Subst} {rest : EquationStore Atom}
    (solved : atomAction.Models σ ([(q x, q two)] ++ rest)) : subst σ x = two := by
  have equation := solved (q x, q two) (by simp)
  change subst σ (q x) = subst σ (q two) at equation
  simp only [q, Insertion.subst_wrap] at equation
  simpa [Insertion.wrap, two, subst] using equation

theorem supply_private_before : ∃ m, m ∉ before.present ∧ label m = y := ⟨6, by decide, rfl⟩

theorem supply_private_constrained : ∃ m, m ∉ constrained.present ∧ label m = y :=
  ⟨6, by rw [constrained_present]; decide, rfl⟩

def both (vx vy : Atom) : Subst := fun v => if v = "x" then some vx else if v = "y" then some vy else none

/-- The same query with a private variable, as in the CeTTa draft's `prime`
lane, observes the answers `1 2` in both orders. -/
theorem private_query_ignores_order :
    answerOccurrences label (p y) y before = {0, 1} ∧
      answerOccurrences label (p y) y constrained = {0, 1} := by
  constructor
  · ext o
    rw [mem_answerOccurrences_iff_consistent supply_private_before]
    constructor
    · rintro ⟨present, ⟨σ, solved⟩⟩
      simp only [before, Finset.mem_insert, Finset.mem_singleton] at present ⊢
      rcases present with rfl | rfl | rfl
      · exact .inl rfl
      · exact .inr rfl
      · have equation := solved (p y, label 2) (by simp [before])
        change subst σ (p y) = subst σ (label 2) at equation
        simp only [label, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, if_true,
          if_false, p, q, Insertion.subst_wrap] at equation
        simp [Insertion.wrap] at equation
    · intro member
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl
      · refine ⟨by decide, Insertion.single "y" one, ?_⟩
        intro e member
        simp only [before, List.nil_append, List.mem_singleton] at member
        subst member
        change subst _ (p y) = subst _ (label 0)
        simp [p, y, one, label, subst, Insertion.single]
      · refine ⟨by decide, Insertion.single "y" two, ?_⟩
        intro e member
        simp only [before, List.nil_append, List.mem_singleton] at member
        subst member
        change subst _ (p y) = subst _ (label 1)
        simp [p, y, two, label, subst, Insertion.single]
  · ext o
    rw [mem_answerOccurrences_iff_consistent supply_private_constrained, constrained_present,
      constrained_equations]
    constructor
    · rintro ⟨present, ⟨σ, solved⟩⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at present ⊢
      have bound := bound_of_constrained solved
      rcases present with rfl | rfl | rfl | rfl
      · exact .inl rfl
      · exact .inr rfl
      · have equation := solved (p y, label 2) (by simp)
        change subst σ (p y) = subst σ (label 2) at equation
        simp only [label, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, if_true,
          if_false, p, q, Insertion.subst_wrap] at equation
        simp [Insertion.wrap] at equation
      · have equation := solved (p y, label 4) (by simp)
        change subst σ (p y) = subst σ (label 4) at equation
        simp only [label, show (4 : Nat) ≠ 0 by decide, show (4 : Nat) ≠ 1 by decide,
          show (4 : Nat) ≠ 2 by decide, show (4 : Nat) ≠ 6 by decide, if_false, p,
          Insertion.subst_wrap] at equation
        rw [bound] at equation
        simp [Insertion.wrap, two] at equation
    · intro member
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl
      · refine ⟨by decide, both two one, ?_⟩
        intro e member
        simp only [List.cons_append, List.nil_append, List.mem_cons,
          List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · change subst _ (q x) = subst _ (q two)
          simp [q, x, two, both, subst]
        · change subst _ (p y) = subst _ (label 0)
          simp [p, y, one, label, both, subst]
      · refine ⟨by decide, both two two, ?_⟩
        intro e member
        simp only [List.cons_append, List.nil_append, List.mem_cons,
          List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · change subst _ (q x) = subst _ (q two)
          simp [q, x, two, both, subst]
        · change subst _ (p y) = subst _ (label 1)
          simp [p, y, two, label, both, subst]

end OrderEffect

/-! ## Validity never certifies completeness -/

/-- Replace one symbol everywhere; variables and grounded values are unchanged. -/
def renameSym (old new : String) : Atom → Atom
  | .symbol s => .symbol (if s = old then new else s)
  | .var v => .var v
  | .grounded g => .grounded g
  | .expression es => .expression (renameList old new es)
where
  renameList (old new : String) : List Atom → List Atom
    | [] => []
    | a :: as => renameSym old new a :: renameList old new as

/-- The symbols of an atom. -/
def syms : Atom → List String
  | .symbol s => [s]
  | .var _ => []
  | .grounded _ => []
  | .expression es => symsList es
where
  symsList : List Atom → List String
    | [] => []
    | a :: as => syms a ++ symsList as

/-- Rename inside every value of a substitution. -/
def renameSubst (old new : String) (σ : Subst) : Subst := fun v => (σ v).map (renameSym old new)

theorem rename_subst (old new : String) (σ : Subst) (atom : Atom) :
    renameSym old new (subst σ atom) = subst (renameSubst old new σ) (renameSym old new atom) := by
  induction atom using Atom.rec
      (motive_2 := fun atoms =>
        renameSym.renameList old new (subst.substList σ atoms) =
          subst.substList (renameSubst old new σ) (renameSym.renameList old new atoms)) with
  | symbol name => simp [renameSym, subst]
  | var name =>
    cases h : σ name <;> simp [renameSym, subst, renameSubst, h]
  | grounded value => simp [renameSym, subst]
  | expression atoms ih => simp only [subst, renameSym, ih]
  | nil => rfl
  | cons atom atoms head tail => simp only [subst.substList, renameSym.renameList, head, tail]

theorem rename_of_not_mem {old new : String} (atom : Atom) (absent : old ∉ syms atom) :
    renameSym old new atom = atom := by
  revert absent
  induction atom using Atom.rec
      (motive_2 := fun atoms => old ∉ syms.symsList atoms → renameSym.renameList old new atoms = atoms) with
  | symbol name =>
    intro absent
    have different : name ≠ old := fun same => absent (by simp [syms, same])
    simp [renameSym, different]
  | var name => intro _; rfl
  | grounded value => intro _; rfl
  | expression atoms ih =>
    intro absent
    simp only [renameSym]
    rw [ih (by simpa [syms] using absent)]
  | nil => rfl
  | cons atom atoms head tail =>
    rename_i absent
    simp only [syms.symsList, List.mem_append, not_or] at absent
    simp only [renameSym.renameList, head absent.1, tail absent.2]

theorem rename_back {c d : String} (atom : Atom) (absent : c ∉ syms atom) :
    renameSym c d (renameSym d c atom) = atom := by
  revert absent
  induction atom using Atom.rec
      (motive_2 := fun atoms => c ∉ syms.symsList atoms →
        renameSym.renameList c d (renameSym.renameList d c atoms) = atoms) with
  | symbol name =>
    intro absent
    have different : name ≠ c := fun same => absent (by simp [syms, same])
    by_cases moved : name = d
    · subst moved
      simp [renameSym]
    · simp [renameSym, moved, different]
  | var name => intro _; rfl
  | grounded value => intro _; rfl
  | expression atoms ih =>
    intro absent
    simp only [renameSym]
    rw [ih (by simpa [syms] using absent)]
  | nil => rfl
  | cons atom atoms head tail =>
    rename_i absent
    simp only [syms.symsList, List.mem_append, not_or] at absent
    simp only [renameSym.renameList, head absent.1, tail absent.2]

theorem mem_syms_rename {c d : String} (atom : Atom) (present : d ∈ syms atom) :
    c ∈ syms (renameSym d c atom) := by
  revert present
  induction atom using Atom.rec
      (motive_2 := fun atoms => d ∈ syms.symsList atoms →
        c ∈ syms.symsList (renameSym.renameList d c atoms)) with
  | symbol name =>
    intro present
    obtain rfl : d = name := by simpa [syms] using present
    simp [renameSym, syms]
  | var name => intro present; simp [syms] at present
  | grounded value => intro present; simp [syms] at present
  | expression atoms ih =>
    intro present
    simp only [renameSym, syms]
    exact ih (by simpa [syms] using present)
  | nil => rename_i present; simp [syms.symsList] at present
  | cons atom atoms head tail =>
    rename_i present
    simp only [syms.symsList, renameSym.renameList, List.mem_append] at present ⊢
    rcases present with here | there
    · exact .inl (head here)
    · exact .inr (tail there)

theorem vars_rename (old new : String) (atom : Atom) : vars (renameSym old new atom) = vars atom := by
  induction atom using Atom.rec
      (motive_2 := fun atoms =>
        vars.varsList (renameSym.renameList old new atoms) = vars.varsList atoms) with
  | symbol name => simp [renameSym, vars]
  | var name => rfl
  | grounded value => rfl
  | expression atoms ih => simp only [renameSym, vars, ih]
  | nil => rfl
  | cons atom atoms head tail => simp only [renameSym.renameList, vars.varsList, head, tail]

/-- The symbol `c` occurs nowhere in a check. -/
def CheckFree (c : String) : Check Atom → Prop
  | .equal left right => c ∉ syms left ∧ c ∉ syms right
  | .absent pattern => c ∉ syms pattern
  | .count pattern _ => c ∉ syms pattern

/-- The symbol `c` occurs nowhere in a rule instance. -/
structure RuleFree (c : String) (rule : RuleInstance Atom) : Prop where
  take : ∀ t ∈ rule.take, c ∉ syms t
  read : ∀ t ∈ rule.read, c ∉ syms t
  tell : ∀ e ∈ rule.tell, c ∉ syms e.1 ∧ c ∉ syms e.2
  checks : ∀ check ∈ rule.checks, CheckFree c check

/-- The symbol `c` occurs nowhere in an equation store. -/
def StoreFree (c : String) (store : EquationStore Atom) : Prop :=
  ∀ e ∈ store, c ∉ syms e.1 ∧ c ∉ syms e.2

theorem mem_zipWith_pair {α β γ : Type*} {f : α → β → γ} :
    ∀ {l : List α} {l' : List β} {z : γ}, z ∈ List.zipWith f l l' → ∃ a ∈ l, ∃ b ∈ l', z = f a b
  | [], _, _, member => by simp at member
  | _ :: _, [], _, member => by simp at member
  | a :: as, b :: bs, z, member => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨a, by simp, b, by simp, rfl⟩
    · obtain ⟨a', inA, b', inB, rfl⟩ := mem_zipWith_pair member
      exact ⟨a', by simp [inA], b', by simp [inB], rfl⟩

/-- A valid firing's joint problem mentions only symbols of its rule, its
store and the labels it selects. -/
theorem problem_free {label : O → Atom} {rule : RuleInstance Atom} {selection : Selection O}
    {before : Configuration Atom O} {c : String}
    (valid : selection.Valid atomAction label rule before) (ruleFree : RuleFree c rule)
    (storeFree : StoreFree c before.equations)
    (labelsFree : ∀ o ∈ before.present, c ∉ syms (label o)) :
    StoreFree c (selection.problem label rule before) := by
  intro e member
  simp only [Selection.problem, List.mem_append] at member
  rcases member with ((old | taken) | read) | told
  · exact storeFree e old
  · obtain ⟨pattern, inTake, o, inTaken, rfl⟩ := mem_zipWith_pair taken
    exact ⟨ruleFree.take pattern inTake, labelsFree o
      (valid.occurrences.taken_subset (by simpa [Selection.commit] using inTaken))⟩
  · obtain ⟨pattern, inRead, o, inRead', rfl⟩ := mem_zipWith_pair read
    exact ⟨ruleFree.read pattern inRead, labelsFree o
      (valid.occurrences.kept_subset (by simpa [Selection.commit] using inRead'))⟩
  · exact ruleFree.tell e told

/-- Renaming a symbol absent from a store transports its solutions. -/
theorem models_rename {store : EquationStore Atom} {c d : String} (free : StoreFree c store)
    {σ : Subst} (solved : atomAction.Models σ store) :
    atomAction.Models (renameSubst c d σ) store := by
  intro e member
  have equation := solved e member
  change subst σ e.1 = subst σ e.2 at equation
  change subst (renameSubst c d σ) e.1 = subst (renameSubst c d σ) e.2
  have first := rename_subst c d σ e.1
  have second := rename_subst c d σ e.2
  rw [rename_of_not_mem e.1 (free e member).1] at first
  rw [rename_of_not_mem e.2 (free e member).2] at second
  rw [← first, ← second, equation]

/-- **Twin genericity.** Add an occurrence `n` whose label copies a stored
label with a symbol `d` replaced by a symbol `c` occurring nowhere in the
firing's data. Every valid firing that does not allocate `n` stays valid. -/
theorem twin_preserves_validity {label : O → Atom} {rule : RuleInstance Atom}
    {selection : Selection O} {before : Configuration Atom O} {c d : String} {source n : O}
    (valid : selection.Valid atomAction label rule before) (ruleFree : RuleFree c rule)
    (storeFree : StoreFree c before.equations)
    (labelsFree : ∀ o ∈ before.present, c ∉ syms (label o))
    (ground : ∀ o ∈ before.present, vars (label o) = [])
    (sourcePresent : source ∈ before.present) (moved : d ∈ syms (label source))
    (twin : label n = renameSym d c (label source)) (absent : n ∉ before.present)
    (notMade : n ∉ selection.made) :
    selection.Valid atomAction label rule ⟨before.equations, insert n before.present⟩ := by
  classical
  have free := problem_free valid ruleFree storeFree labelsFree
  have groundTwin : vars (label n) = [] := by
    rw [twin, vars_rename]
    exact ground source sourcePresent
  have twinHasC : c ∈ syms (label n) := twin ▸ mem_syms_rename (label source) moved
  -- A solution that sees the twin through a free pattern yields one that sees the source.
  have transport : ∀ (t : Atom), c ∉ syms t → ∀ σ : Subst,
      atomAction.Models σ (selection.problem label rule before) → subst σ t = label n →
      atomAction.Models (renameSubst c d σ) (selection.problem label rule before) ∧
        subst (renameSubst c d σ) t = label source := by
    intro t tFree σ solved sees
    refine ⟨models_rename free solved, ?_⟩
    have moved := rename_subst c d σ t
    rw [rename_of_not_mem t tFree, sees, twin, rename_back (label source)
      (labelsFree source sourcePresent)] at moved
    exact moved.symm
  refine ⟨valid.take_distinct, valid.output_distinct, valid.take_length, valid.read_length,
    valid.outputs, ?_, valid.consistent, ?_⟩
  · refine ⟨valid.occurrences.taken_subset.trans (Finset.subset_insert _ _),
      valid.occurrences.kept_subset.trans (Finset.subset_insert _ _), valid.occurrences.apart, ?_, ?_⟩
    · rw [Finset.disjoint_insert_right]
      exact ⟨by simpa [Selection.commit] using notMade, valid.occurrences.fresh⟩
    · intro query member
      simp [Selection.commit] at member
  · intro check member σ solved
    have original := valid.checks check member σ solved
    have ruleCheck := ruleFree.checks check member
    cases check with
    | equal left right => exact original
    | absent t =>
      intro o inserted
      rcases Finset.mem_insert.mp inserted with isTwin | old
      · subst isTwin
        intro sees
        change subst σ t = subst σ (label o) at sees
        rw [subst_of_vars_eq_nil σ _ groundTwin] at sees
        obtain ⟨solved', seesSource⟩ := transport t ruleCheck σ solved sees
        have refuted := valid.checks (.absent t) member _ solved' source sourcePresent
        apply refuted
        change subst _ t = subst _ (label source)
        rw [seesSource, subst_of_vars_eq_nil _ _ (ground source sourcePresent)]
      · exact original o old
    | count t k =>
      have unseen : ¬ atomAction.E (atomAction.apply σ t) (atomAction.apply σ (label n)) := by
        intro sees
        change subst σ t = subst σ (label n) at sees
        rw [subst_of_vars_eq_nil σ _ groundTwin] at sees
        obtain ⟨solved', seesSource⟩ := transport t ruleCheck σ solved sees
        have atSolution : (Check.matches atomAction σ label before.present t).card = k := original
        have atRenamed : (Check.matches atomAction (renameSubst c d σ) label before.present t).card = k :=
          valid.checks (.count t k) member _ solved'
        have empty : Check.matches atomAction σ label before.present t = ∅ := by
          unfold Check.matches
          apply Finset.filter_eq_empty_iff.mpr
          intro o present same
          change subst σ t = subst σ (label o) at same
          rw [sees, subst_of_vars_eq_nil σ _ (ground o present)] at same
          exact labelsFree o present (same ▸ twinHasC)
        have nonempty : 0 < (Check.matches atomAction (renameSubst c d σ) label before.present t).card := by
          apply Finset.card_pos.mpr
          refine ⟨source, ?_⟩
          unfold Check.matches
          rw [Finset.mem_filter]
          refine ⟨sourcePresent, ?_⟩
          change subst _ t = subst _ (label source)
          rw [seesSource, subst_of_vars_eq_nil _ _ (ground source sourcePresent)]
        rw [empty, Finset.card_empty] at atSolution
        omega
      change (Check.matches atomAction σ label (insert n before.present) t).card = k
      have same : Check.matches atomAction σ label (insert n before.present) t =
          Check.matches atomAction σ label before.present t := by
        unfold Check.matches
        rw [Finset.filter_insert, if_neg unseen]
      rw [same]
      exact original

/-- **No firing certifies the completeness of an open query.** Whatever a
valid firing reads, the same firing remains valid next to an unread answer. -/
theorem validity_never_certifies_completeness {label : O → Atom} {rule : RuleInstance Atom}
    {selection : Selection O} {before : Configuration Atom O} {c d : String} {source n : O}
    {query : Atom}
    (valid : selection.Valid atomAction label rule before) (ruleFree : RuleFree c rule)
    (storeFree : StoreFree c before.equations)
    (labelsFree : ∀ o ∈ before.present, c ∉ syms (label o))
    (ground : ∀ o ∈ before.present, vars (label o) = [])
    (sourcePresent : source ∈ before.present) (moved : d ∈ syms (label source))
    (twin : label n = renameSym d c (label source)) (absent : n ∉ before.present)
    (notMade : n ∉ selection.made) (matched : Matches query (label source))
    (queryKeeps : d ∉ syms query) :
    selection.Valid atomAction label rule ⟨before.equations, insert n before.present⟩ ∧
      Matches query (label n) ∧ n ∉ selection.read ∧ n ∉ selection.taken := by
  refine ⟨twin_preserves_validity valid ruleFree storeFree labelsFree ground sourcePresent moved twin
    absent notMade, ?_, ?_, ?_⟩
  · obtain ⟨τ, solves⟩ := matched
    refine ⟨renameSubst d c τ, ?_⟩
    have renamed := rename_subst d c τ query
    rw [rename_of_not_mem query queryKeeps, solves] at renamed
    rw [twin, renamed]
  · intro read
    exact absent (valid.occurrences.kept_subset (by simpa [Selection.commit] using read))
  · intro taken
    exact absent (valid.occurrences.taken_subset (by simpa [Selection.commit] using taken))

/-! ## The primitive the step lacks -/

/-- A predicate query of the occurrence-commit layer is spoiled by an added
occurrence that its predicate selects: completeness is checked at commit. -/
theorem predicate_query_detects_twin {R : Type*} (label : O → R) (store : Finset O)
    (query : PredicateQuery O R) (holds : query.Holds label store) (n : O) (absent : n ∉ store)
    (selected : query.region (label n) = true) :
    ¬ query.Holds label (insert n store) := by
  intro extended
  have seenSubset : query.seen ⊆ store := by
    rw [← holds]
    exact Finset.filter_subset _ _
  have mem : n ∈ regionOf label (insert n store) query.region := by
    simp [regionOf, selected]
  change regionOf label (insert n store) query.region = query.seen at extended
  rw [extended] at mem
  exact absent (seenSubset mem)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsCollapse
