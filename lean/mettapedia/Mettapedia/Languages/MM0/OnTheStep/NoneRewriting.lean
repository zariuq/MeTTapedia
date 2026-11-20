import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Rewriting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.NoneReading

/-!
# Rewriting of bags with the none query is the step

`RuleSyntax.Machines.Rewriting` proves that the step (`RuleSyntax.step` at the one frame over rows with
unknowns: a bag store, one match per firing, guards asked after the firing's own tells, a fixed set of rules,
one store of knowledge) is rewriting of bags by matching, for range-restricted positive programs.
`RuleSyntax.Machines.NoneReading` shows that `Machines.Rewrites` is not the step for a rule with a none query
query. This module gives the correspondence for rules with none queries.

* **The fragment** (`NoneRestricted`): no collect pattern, no count query; equation guards and none queries
  queries; range restriction (`RangeRestricted`): every unknown of a tell, of a check (a none pattern
  included) and of a made row occurs in a take or read pattern. Every range-restricted positive rule is in it
  (`noneRestricted_of_positive`).
* **Rewriting with none queries** (`RewritesNone`): a rewrite of `Machines.Rewrites` whose instantiation sends no
  none pattern of the rule to a row of the bag. The bag is the whole bag, taken rows included: a none query
  query reads the store before the firing.
* **At a state that reads as a bag, a none query holds at every solution of an admitted firing's
  information exactly when the instance of its pattern is no row of the bag** (`none_of_admitted`, and the
  none part of `admitted_of_rewrite_none`).
* **The correspondence**: `rewrite_of_admitted_none`, `admitted_of_rewrite_none`,
  `readsBag_backward_none`, `readsBag_forward_none`, `correspondenceNone`, `reachable_iff_none`: the
  statements of `Machines.Rewriting` for this fragment. Their proofs follow the proofs there, with the none query
  part added; the theorems there take positive rules only, and the forward one does not expose the selected
  rows, which the none part needs.
* **Controls** (`Controls`): the rule `NoneReading.noneRule` (take `sym 0`, ask that no row is `sym 1`,
  make `sym 2`) rewrites the bag `{sym 0}` to `{sym 2}`, has no rewrite at `{sym 0, sym 1}` (where
  `Machines.Rewrites` has one), and the step agrees at states that read as these bags.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.OnTheStep.NoneRewriting

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open OneFrame (frames ext)
open NamesOnTheStep (Expr)
open LogicOverTheStep.StepSpan (Succ)
open Presentation (exists_taken exists_read exists_fresh bagOf_split)
open Presentation.Schematic
open Machines (Reads ReadsBag Rewrites knowledge_of_information agree_of_reads map_eq_map_of_zip result_reads
  rowsAfter bag_after stateBound lt_stateBound shift_fresh_of_bound mixedSolution mixed_below mixed_reads
  stepSystem listState listState_reads)

universe uO

/-! ## The fragment -/

/-- The pattern of a `none` predicate query; nothing for the other checks. -/
def nonePatternOf : Check Tm → List Tm
  | .predicate .none p => [p]
  | _ => []

/-- **The none patterns of a rule.** -/
def nonePatternsOf (r : SRule) : List Tm := r.body.checks.flatMap nonePatternOf

/-- An equation guard or a `none` predicate query. -/
def isGuardOrNone : Check Tm → Bool
  | .equal _ _ => true
  | .predicate .none _ => true
  | .predicate .any _ => false
  | .count _ _ => false

/-- **The fragment**: no collect pattern, equation guards and `none` predicate queries only, range
restriction. -/
def NoneRestricted (r : SRule) : Prop :=
  r.collect = [] ∧ r.body.checks.all isGuardOrNone = true ∧ RangeRestricted r

instance (r : SRule) : Decidable (NoneRestricted r) := by
  unfold NoneRestricted
  infer_instance

/-- **Every range-restricted positive rule is in the fragment.** -/
theorem noneRestricted_of_positive {r : SRule} (positive : RangeRestrictedPositive r) :
    NoneRestricted r := by
  refine ⟨positive.1, List.all_eq_true.mpr fun c member => ?_, positive.2.2⟩
  have guard := List.all_eq_true.mp positive.2.1 c member
  cases c with
  | equal _ _ => rfl
  | predicate quantifier _ => simp [isGuard] at guard
  | count _ _ => simp [isGuard] at guard

/-- A positive rule has no none pattern. -/
theorem nonePatternsOf_of_positive {r : SRule} (positive : RangeRestrictedPositive r) : nonePatternsOf r = [] := by
  unfold nonePatternsOf
  rw [List.flatMap_eq_nil_iff]
  intro c member
  have guard := List.all_eq_true.mp positive.2.1 c member
  cases c with
  | equal _ _ => rfl
  | predicate quantifier _ => simp [isGuard] at guard
  | count _ _ => simp [isGuard] at guard

theorem none_mem_checks {r : SRule} {p : Tm} (member : p ∈ nonePatternsOf r) : Check.predicate .none p ∈ r.body.checks := by
  obtain ⟨c, inChecks, inNonePattern⟩ := List.mem_flatMap.mp member
  cases c with
  | predicate quantifier q =>
      cases quantifier with
      | any => simp [nonePatternOf] at inNonePattern
      | none =>
          rw [nonePatternOf, List.mem_singleton] at inNonePattern
          rw [inNonePattern]
          exact inChecks
  | equal _ _ => simp [nonePatternOf] at inNonePattern
  | count _ _ => simp [nonePatternOf] at inNonePattern

/-- A none pattern is a term the rule writes. -/
theorem mem_written_of_nonePattern {r : SRule} {p : Tm} (member : p ∈ nonePatternsOf r) : p ∈ written r := by
  simp only [written, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inr ⟨.predicate .none p, none_mem_checks member, by simp [checkTerms]⟩)

theorem mem_nonePatternsOf {r : SRule} {p : Tm} (member : Check.predicate .none p ∈ r.body.checks) : p ∈ nonePatternsOf r :=
  List.mem_flatMap.mpr ⟨.predicate .none p, member, List.mem_singleton_self p⟩

/-! ## An admitted firing at a state that reads as rows -/

section Firing

variable {O : Type uO} [DecidableEq O] {rules : List SRule}

/-- **A none query of an admitted firing, at a state that reads as rows**: where every solution of the
information reads the bound unknowns as `θ`, the instance of the none pattern at `θ` is the row of no present
identity. -/
theorem none_of_admitted {s : SState O} {rows : O → Expr} (reads : Reads s rows)
    (g : Firing O E {r | r ∈ rules} s.frame) (admitted : (schematicStep O rules).Admits (s := s) g)
    (restricted : RangeRestricted g.rule) (θ : ℕ → Expr)
    (agree : ∀ σ : Subst rowSig, A.Models σ (g.information X s) →
      ∀ x, Bound g.rule x → σ.applyTerm (g.opening x) = toTerm (θ x))
    {p : Tm} (member : p ∈ nonePatternsOf g.rule) : ∀ o ∈ s.present, inst θ p ≠ rows o := by
  intro o present same
  obtain ⟨-, -, -, solvable, checks, -⟩ := (admits_iff g).mp admitted
  obtain ⟨σ, solved⟩ := (Frames.ofSubstitution_solvable_iff A _).mp solvable
  have holds : checkHolds X σ (g.row X s) s.present (Check.map g.opening.applyTerm (.predicate .none p)) :=
    checks _ (List.mem_map_of_mem (none_mem_checks member)) PUnit.unit σ solved
  apply holds o present
  show σ.applyTerm (g.opening.applyTerm p) = σ.applyTerm (g.row X s o)
  rw [written_reads g (agree σ solved) fun x vars => restricted p (mem_written_of_nonePattern member) x vars,
    row_eq, reads.reads σ (knowledge_of_information g solved) o present, same]

/-- **An admitted firing of a rule of the fragment, at a state that reads as rows, is a firing by matching
whose none patterns have no instance among the rows**, and its result reads as the rows after the firing. -/
theorem rewrite_of_admitted_none {s : SState O} {rows : O → Expr} (reads : Reads s rows)
    (fragment : ∀ r ∈ rules, NoneRestricted r)
    (g : Firing O E {r | r ∈ rules} s.frame) (admitted : (schematicStep O rules).Admits (s := s) g) :
    ∃ θ : ℕ → Expr,
      g.rule.body.take.map (inst θ) = g.selection.taken.map rows ∧
      g.rule.body.read.map (inst θ) = g.selection.read.map rows ∧
      (∀ e ∈ equationsOf g.rule, inst θ e.1 = inst θ e.2) ∧
      (∀ p ∈ nonePatternsOf g.rule, inst θ p ∉ s.present.val.map rows) ∧
      Reads ((schematicStep O rules).result g admitted)
        (rowsAfter rows g.selection.made (g.rule.body.produce.map (inst θ))) := by
  obtain ⟨-, ⟨-, -, takeLength, readLength, -, -⟩, enabled, solvable, checks, -⟩ :=
    (admits_iff g).mp admitted
  have fragmentRule := fragment g.rule g.member
  obtain ⟨σ, solved⟩ := (Frames.ofSubstitution_solvable_iff A _).mp solvable
  have known := knowledge_of_information g solved
  let θ := groundPart (σ.comp g.opening)
  have takenPresent : ∀ o ∈ g.selection.taken, o ∈ s.present := fun o member =>
    enabled.taken_subset (List.mem_toFinset.mpr member)
  have readPresent : ∀ o ∈ g.selection.read, o ∈ s.present := fun o member =>
    enabled.kept_subset (List.mem_toFinset.mpr member)
  have matchedBy : ∀ {p : Tm} {o : O}, o ∈ s.present →
      σ.applyTerm (g.opening.applyTerm p) = σ.applyTerm (g.row X s o) → inst θ p = rows o := by
    intro p o present equation
    rw [row_eq, reads.reads σ known o present, ← Subst.applyTerm_comp] at equation
    exact (inst_groundPart _ p (rows o) equation).1
  have takesMatch : ∀ x ∈ g.rule.body.take.zip g.selection.taken, inst θ x.1 = rows x.2 := fun x inside =>
    matchedBy (takenPresent x.2 (List.of_mem_zip inside).2)
      (g.take_solved (b := PUnit.unit) solved (mem_zip_map_left inside))
  have readsMatch : ∀ x ∈ g.rule.body.read.zip g.selection.read, inst θ x.1 = rows x.2 := fun x inside =>
    matchedBy (readPresent x.2 (List.of_mem_zip inside).2)
      (g.read_solved (b := PUnit.unit) solved (mem_zip_map_left inside))
  have agree : ∀ σ' : Subst rowSig, A.Models σ' (g.information X s) →
      ∀ x, Bound g.rule x → σ'.applyTerm (g.opening x) = toTerm (θ x) := fun σ' solved' =>
    agree_of_reads reads g θ takeLength readLength takenPresent readPresent takesMatch readsMatch solved'
  have writes : ∀ σ' : Subst rowSig, A.Models σ' (g.information X s) → ∀ t : Tm,
      (∀ x ∈ t.freeVars, Bound g.rule x) →
      σ'.applyTerm (g.opening.applyTerm t) = toTerm (inst θ t) := fun σ' solved' t bound =>
    written_reads g (agree σ' solved') bound
  refine ⟨θ, map_eq_map_of_zip takeLength takesMatch, map_eq_map_of_zip readLength readsMatch, ?_, ?_,
    result_reads reads g admitted fragmentRule.2.2 θ agree⟩
  · intro e member
    have written := mem_written_of_equation member
    have boundLeft : ∀ x ∈ e.1.freeVars, Bound g.rule x := fun x vars => fragmentRule.2.2 _ written.1 x vars
    have boundRight : ∀ x ∈ e.2.freeVars, Bound g.rule x := fun x vars => fragmentRule.2.2 _ written.2 x vars
    have equal : σ.applyTerm (g.opening.applyTerm e.1) = σ.applyTerm (g.opening.applyTerm e.2) := by
      rcases List.mem_append.mp member with told | guarded
      · exact g.tell_solved (b := PUnit.unit) solved (List.mem_map_of_mem (f := fun pair =>
          (g.opening.applyTerm pair.1, g.opening.applyTerm pair.2)) told)
      · obtain ⟨c, inChecks, inGuard⟩ := List.mem_flatMap.mp guarded
        cases c with
        | equal l r =>
            rw [guardOf, List.mem_singleton] at inGuard
            subst inGuard
            exact checks (Check.map g.opening.applyTerm (.equal l r)) (List.mem_map_of_mem inChecks)
              PUnit.unit σ solved
        | predicate quantifier _ => simp [guardOf] at inGuard
        | count _ _ => simp [guardOf] at inGuard
    rw [writes σ solved e.1 boundLeft, writes σ solved e.2 boundRight] at equal
    exact toTerm_injective equal
  · intro p member inBag
    obtain ⟨o, present, same⟩ := Multiset.mem_map.mp inBag
    exact none_of_admitted reads g admitted fragmentRule.2.2 θ agree member o (Finset.mem_val.mp present)
      same.symm

/-- **Every firing by matching at a state that reads as rows, whose none patterns have no instance among the
rows, is an admitted firing**, and its result reads as the made rows' instances beside the rest, when
identities are infinitely many. -/
theorem admitted_of_rewrite_none [Infinite O] {s : SState O} {rows : O → Expr} (reads : Reads s rows)
    {r : SRule} (member : r ∈ rules) (fragmentRule : NoneRestricted r) {θ : ℕ → Expr}
    {restM : Multiset Expr}
    (split : (r.body.take.map (inst θ) : Multiset Expr) + restM = s.present.val.map rows)
    (readsIn : ∀ q ∈ r.body.read, inst θ q ∈ restM) (equations : ∀ e ∈ equationsOf r, inst θ e.1 = inst θ e.2)
    (missing : ∀ p ∈ nonePatternsOf r, inst θ p ∉ s.present.val.map rows) :
    ∃ (g : Firing O E {r | r ∈ rules} s.frame) (admitted : (schematicStep O rules).Admits (s := s) g),
      g.rule = r ∧ ∃ rows' : O → Expr, Reads ((schematicStep O rules).result g admitted) rows' ∧
        ((schematicStep O rules).result g admitted).present.val.map rows' =
          (r.body.produce.map (inst θ) : Multiset Expr) + restM := by
  obtain ⟨taken, takenNodup, takenIn, takenRows⟩ := exists_taken rows (r.body.take.map (inst θ)) s.present
    (show ((r.body.take.map (inst θ) : List Expr) : Multiset Expr) ≤ s.present.val.map rows from
      (le_add_right le_rfl).trans_eq split)
  have takenSub : taken.toFinset ⊆ s.present := fun o member => takenIn o (List.mem_toFinset.mp member)
  have restEq : restM = (s.present \ taken.toFinset).val.map rows := by
    have whole := bagOf_split rows (C := ⟨[], s.present⟩) takenNodup takenSub
    rw [takenRows] at whole
    exact add_left_cancel (split.trans whole)
  obtain ⟨read, readIn, readRows⟩ := exists_read rows (r.body.read.map (inst θ)) (s.present \ taken.toFinset)
    (fun x inside => by
      obtain ⟨q, inRead, rfl⟩ := List.mem_map.mp inside
      rw [← restEq]
      exact readsIn q inRead)
  obtain ⟨made, madeNodup, madeLength, madeFresh⟩ := exists_fresh s.present r.body.produce.length
  have collectEmpty : r.collect = [] := fragmentRule.1
  let g : Firing O E {r | r ∈ rules} s.frame :=
    ⟨r, member, PUnit.unit, shift (stateBound s), ⟨taken, read, made⟩, []⟩
  have takeLength : r.body.take.length = taken.length := by
    rw [← List.length_map (f := inst θ), ← takenRows, List.length_map]
  have readLength : r.body.read.length = read.length := by
    rw [← List.length_map (f := inst θ), ← readRows, List.length_map]
  have takenPresent : ∀ o ∈ taken, o ∈ s.present := takenIn
  have readPresent : ∀ o ∈ read, o ∈ s.present := fun o inside => (Finset.mem_sdiff.mp (readIn o inside)).1
  have takesMatch : ∀ x ∈ r.body.take.zip taken, inst θ x.1 = rows x.2 := pairs_of_map_eq takenRows.symm
  have readsMatch : ∀ x ∈ r.body.read.zip read, inst θ x.1 = rows x.2 := pairs_of_map_eq readRows.symm
  have agree : ∀ σ' : Subst rowSig, A.Models σ' (g.information X s) →
      ∀ x, Bound g.rule x → σ'.applyTerm (g.opening x) = toTerm (θ x) := fun σ' solved' =>
    agree_of_reads reads g θ takeLength readLength takenPresent readPresent takesMatch readsMatch solved'
  have known : X.applyStore ((ext A).weaken g.ext) s.knowledge = s.knowledge :=
    Frames.applyStore_id (X := X) s.knowledge
  obtain ⟨σ₀, solved₀⟩ := reads.solvable
  have labelRead : ∀ o ∈ s.present,
      (mixedSolution (stateBound s) θ σ₀).applyTerm (s.label o) = toTerm (rows o) := by
    intro o present
    rw [mixed_below (stateBound s) θ σ₀ (t := s.label o) fun v vars =>
      lt_stateBound (Or.inr (Or.inr ⟨o, present, rfl⟩)) vars]
    exact reads.reads σ₀ solved₀ o present
  have solved : A.Models (mixedSolution (stateBound s) θ σ₀) (g.information X s) := by
    intro e inside
    unfold Firing.information at inside
    rw [known] at inside
    simp only [List.mem_append] at inside
    rcases inside with ((old | taking) | reading) | told
    · show Subst.applyTerm _ e.1 = Subst.applyTerm _ e.2
      rw [mixed_below (stateBound s) θ σ₀ (t := e.1) fun v vars =>
          lt_stateBound (Or.inl (List.mem_map_of_mem old)) vars,
        mixed_below (stateBound s) θ σ₀ (t := e.2) fun v vars =>
          lt_stateBound (Or.inr (Or.inl (List.mem_map_of_mem old))) vars]
      exact solved₀ e old
    · obtain ⟨p, o, pair, rfl⟩ := mem_matching g taking
      show Subst.applyTerm _ (Subst.applyTerm (shift _) p) = Subst.applyTerm _ (s.label o)
      rw [mixed_reads, labelRead o (takenPresent o (List.of_mem_zip pair).2), takesMatch _ pair]
    · obtain ⟨p, o, pair, rfl⟩ := mem_matching g reading
      show Subst.applyTerm _ (Subst.applyTerm (shift _) p) = Subst.applyTerm _ (s.label o)
      rw [mixed_reads, labelRead o (readPresent o (List.of_mem_zip pair).2), readsMatch _ pair]
    · obtain ⟨pair, inTell, rfl⟩ := List.mem_map.mp told
      show Subst.applyTerm _ (Subst.applyTerm (shift _) pair.1) =
        Subst.applyTerm _ (Subst.applyTerm (shift _) pair.2)
      rw [mixed_reads, mixed_reads, equations pair (List.mem_append_left _ inTell)]
  have admitted : (schematicStep O rules).Admits (s := s) g := by
    refine (admits_iff g).mpr ⟨shift_fresh_of_bound g rfl, ⟨takenNodup, madeNodup, takeLength, readLength,
      madeLength.symm, by rw [collectEmpty]; rfl⟩, ?_,
      (Frames.ofSubstitution_solvable_iff A _).mpr ⟨_, solved⟩, ?_, ?_⟩
    · exact ⟨takenSub, fun o inside => readPresent o (List.mem_toFinset.mp inside),
        Finset.disjoint_left.mpr fun o taking reading =>
          (Finset.mem_sdiff.mp (readIn o (List.mem_toFinset.mp reading))).2 taking,
        Finset.disjoint_left.mpr fun o inside present => madeFresh o (List.mem_toFinset.mp inside) present,
        fun query inside => by simp [Selection.commit] at inside⟩
    · intro c inChecks _ σ' solved'
      obtain ⟨c₀, inRule, rfl⟩ := List.mem_map.mp inChecks
      have kind := List.all_eq_true.mp fragmentRule.2.1 c₀ inRule
      cases c₀ with
      | equal l r' =>
          have inEquations : (l, r') ∈ equationsOf r :=
            List.mem_append_right _ (List.mem_flatMap.mpr ⟨.equal l r', inRule, List.mem_singleton_self _⟩)
          have written := mem_written_of_equation inEquations
          show Subst.applyTerm σ' (Subst.applyTerm (shift _) l) = Subst.applyTerm σ' (Subst.applyTerm (shift _) r')
          rw [written_reads g (agree σ' solved') fun x vars => fragmentRule.2.2 _ written.1 x vars,
            written_reads g (agree σ' solved') fun x vars => fragmentRule.2.2 _ written.2 x vars,
            equations _ inEquations]
      | predicate quantifier q =>
          cases quantifier with
          | any => simp [isGuardOrNone] at kind
          | none =>
            have inNonePatterns : q ∈ nonePatternsOf r := mem_nonePatternsOf inRule
            show ∀ o ∈ s.present,
              ¬ Subst.applyTerm σ' (Subst.applyTerm (shift (stateBound s)) q) = Subst.applyTerm σ' (g.row X s o)
            intro o present same
            rw [written_reads g (agree σ' solved') fun x vars =>
                fragmentRule.2.2 q (mem_written_of_nonePattern inNonePatterns) x vars,
              row_eq, reads.reads σ' (knowledge_of_information g solved') o present] at same
            exact missing q inNonePatterns
              (Multiset.mem_map.mpr ⟨o, Finset.mem_val.mpr present, (toTerm_injective same).symm⟩)
      | count _ _ => simp [isGuardOrNone] at kind
    · intro q inside
      have none : (g.collectOpened X).zip g.seen = [] := by
        simp [Firing.collectOpened, g, collectEmpty]
      rw [none] at inside
      exact absurd inside List.not_mem_nil
  have lengths : made.length = (r.body.produce.map (inst θ)).length := by
    rw [List.length_map]
    exact madeLength
  have fresh : Disjoint made.toFinset s.present :=
    Finset.disjoint_left.mpr fun o inside present => madeFresh o (List.mem_toFinset.mp inside) present
  refine ⟨g, admitted, rfl, rowsAfter rows made (r.body.produce.map (inst θ)),
    result_reads reads g admitted fragmentRule.2.2 θ agree, ?_⟩
  rw [restEq]
  exact (bag_after s.present rows g.selection madeNodup lengths fresh).trans (add_comm _ _)

/-! ## Rewriting of bags with none queries, and the correspondence -/

/-- **One rewrite of a bag of rows by matching, with none queries**: a rule of the list, a ground instantiation of its
unknowns and a rest; the takes' instances beside the rest are the bag, each read's instance is a row of the
rest, the rule's equations hold at the instantiation, no none pattern's instance is a row of the bag, and the
result is the made rows' instances beside the rest. -/
def RewritesNone (rules : List SRule) (bag bag' : Multiset Expr) : Prop :=
  ∃ r ∈ rules, ∃ (θ : ℕ → Expr) (rest : Multiset Expr),
    (r.body.take.map (inst θ) : Multiset Expr) + rest = bag ∧
    (∀ q ∈ r.body.read, inst θ q ∈ rest) ∧
    (∀ e ∈ equationsOf r, inst θ e.1 = inst θ e.2) ∧
    (∀ p ∈ nonePatternsOf r, inst θ p ∉ bag) ∧
    bag' = (r.body.produce.map (inst θ) : Multiset Expr) + rest

/-- **For positive programs, rewriting with the none query is `Machines.Rewrites`.** -/
theorem rewritesNone_iff_of_positive (fragment : ∀ r ∈ rules, RangeRestrictedPositive r)
    {bag bag' : Multiset Expr} : RewritesNone rules bag bag' ↔ Rewrites rules bag bag' := by
  constructor
  · rintro ⟨r, member, θ, rest, split, readsIn, equations, -, after⟩
    exact ⟨r, member, θ, rest, split, readsIn, equations, after⟩
  · rintro ⟨r, member, θ, rest, split, readsIn, equations, after⟩
    refine ⟨r, member, θ, rest, split, readsIn, equations, fun p inside => ?_, after⟩
    rw [nonePatternsOf_of_positive (fragment r member)] at inside
    exact absurd inside List.not_mem_nil

/-- **An admitted firing at a state that reads as a bag is one rewrite of the bag with none queries, and its result
reads as the rewritten bag.** -/
theorem readsBag_backward_none (fragment : ∀ r ∈ rules, NoneRestricted r) {s : SState O}
    {bag : Multiset Expr} (reads : ReadsBag s bag) (g : Firing O E {r | r ∈ rules} s.frame)
    (admitted : (schematicStep O rules).Admits (s := s) g) :
    ∃ bag', RewritesNone rules bag bag' ∧ ReadsBag ((schematicStep O rules).result g admitted) bag' := by
  obtain ⟨rows, reads, rfl⟩ := reads
  obtain ⟨θ, takes, readsMatch, equations, nones, after⟩ :=
    rewrite_of_admitted_none reads fragment g admitted
  obtain ⟨-, ⟨takenNodup, madeNodup, -, readLength, produceLength, -⟩, enabled, -⟩ :=
    (admits_iff g).mp admitted
  have lengths : g.selection.made.length = (g.rule.body.produce.map (inst θ)).length := by
    rw [List.length_map]
    exact produceLength.symm
  refine ⟨_, ⟨g.rule, g.member, θ, (s.present \ g.selection.taken.toFinset).val.map rows, ?_, ?_, equations,
    nones, rfl⟩, ⟨_, after, (bag_after s.present rows g.selection madeNodup lengths enabled.fresh).trans
      (add_comm _ _)⟩⟩
  · have whole := bagOf_split rows (C := ⟨[], s.present⟩) takenNodup enabled.taken_subset
    rw [takes]
    exact whole.symm
  · intro q member
    obtain ⟨o, inside⟩ := exists_zip_of_mem readLength member
    have matched : inst θ q = rows o := pairs_of_map_eq readsMatch (q, o) inside
    rw [matched]
    refine Multiset.mem_map_of_mem _ (Finset.mem_val.mpr (Finset.mem_sdiff.mpr ⟨?_, fun taken => ?_⟩))
    · exact enabled.kept_subset (List.mem_toFinset.mpr (List.of_mem_zip inside).2)
    · exact Finset.disjoint_left.mp enabled.apart taken (List.mem_toFinset.mpr (List.of_mem_zip inside).2)

/-- **Every rewrite with none queries of the bag a state reads as is an admitted firing whose result reads as the
rewritten bag**, when identities are infinitely many. -/
theorem readsBag_forward_none [Infinite O] (fragment : ∀ r ∈ rules, NoneRestricted r) {s : SState O}
    {bag bag' : Multiset Expr} (reads : ReadsBag s bag) (rewrites : RewritesNone rules bag bag') :
    ∃ (g : Firing O E {r | r ∈ rules} s.frame) (admitted : (schematicStep O rules).Admits (s := s) g),
      ReadsBag ((schematicStep O rules).result g admitted) bag' := by
  obtain ⟨rows, reads, rfl⟩ := reads
  obtain ⟨r, member, θ, rest, split, readsIn, equations, nones, rfl⟩ := rewrites
  obtain ⟨g, admitted, -, rows', reads', bagEq⟩ :=
    admitted_of_rewrite_none reads member (fragment r member) split readsIn equations nones
  exact ⟨g, admitted, rows', reads', bagEq⟩

/-- **Rewriting of bags of rows with none queries, as a system.** -/
def rewritingNone (rules : List SRule) : GSLT := equalityGSLT (Multiset Expr) (RewritesNone rules)

/-- **The correspondence**: rewriting of bags with none queries and the step of a program of the fragment, related by
reading a state as a bag. A firing is read back as one rewrite, and a rewrite is realized by one firing. -/
def correspondenceNone [Infinite O] (fragment : ∀ r ∈ rules, NoneRestricted r) :
    OperationalCorrespondence (rewritingNone rules) (stepSystem O rules) where
  related bag s := ReadsBag s bag
  readStep := by
    intro bag s s' reads stepped
    obtain ⟨g, admitted, rfl⟩ := stepped
    obtain ⟨bag', rewrites, reads'⟩ := readsBag_backward_none fragment reads g admitted
    exact Or.inr ⟨bag', rewrites, reads'⟩
  forward := by
    intro bag bag' s reads rewrites
    obtain ⟨g, admitted, reads'⟩ := readsBag_forward_none fragment reads rewrites
    exact ⟨_, (executionPath_nonempty_iff_multiStep (stepSystem O rules) _ _).mpr
      (.step ⟨g, admitted, rfl⟩ (.refl _)), reads'⟩

/-- **Reachability transfers both ways**: a bag with a property is reachable by rewriting with none queries exactly
when a state that reads as such a bag is reachable by the step. -/
theorem reachable_iff_none [Infinite O] (fragment : ∀ r ∈ rules, NoneRestricted r)
    (property : Multiset Expr → Prop) {s : SState O} {bag : Multiset Expr} (reads : ReadsBag s bag) :
    (∃ bag', (rewritingNone rules).MultiStep bag bag' ∧ property bag') ↔
      ∃ s', (stepSystem O rules).MultiStep s s' ∧ ∃ bag', ReadsBag s' bag' ∧ property bag' := by
  refine (correspondenceNone (O := O) fragment).reachable_iff property
    (fun s' => ∃ bag', ReadsBag s' bag' ∧ property bag') (fun {origin current} related => ?_) reads
  have readsHere : ReadsBag current origin := related
  constructor
  · exact fun holds => ⟨origin, readsHere, holds⟩
  · rintro ⟨other, readsOther, holds⟩
    have same : origin = other :=
      readsAs_unique readsHere.readsAs.1 readsHere.readsAs.2 readsOther.readsAs.2
    rw [same]
    exact holds

end Firing

/-! ## Controls -/

namespace Controls

open Machines.NoneReading (noneRule)

theorem noneRule_restricted : NoneRestricted noneRule := by decide

/-- **Where `sym 1` is not present, the none rule rewrites `{sym 0}` to `{sym 2}`.** -/
theorem noneRule_rewrites :
    RewritesNone [noneRule] (([.sym 0] : List Expr) : Multiset Expr) (([.sym 2] : List Expr) : Multiset Expr) :=
  ⟨noneRule, List.mem_singleton_self _, fun _ => .sym 0, 0, rfl,
    fun q member => absurd member List.not_mem_nil,
    fun e member => by simp [equationsOf, noneRule, guardOf] at member,
    fun p member => by
      simp only [nonePatternsOf, noneRule, List.flatMap_cons, List.flatMap_nil, nonePatternOf, List.append_nil,
        List.mem_singleton] at member
      subst member
      decide,
    rfl⟩

/-- **Where `sym 1` is present, the none rule has no rewrite**, though `Machines.Rewrites` has one
(`NoneReading.rewrites_but_refused`). -/
theorem noneRule_refused (bag' : Multiset Expr) :
    ¬ RewritesNone [noneRule] (([.sym 0, .sym 1] : List Expr) : Multiset Expr) bag' := by
  rintro ⟨r, member, _, _, -, -, -, nones, -⟩
  rw [List.mem_singleton.mp member] at nones
  apply nones (toTerm (.sym 1)) (by simp [nonePatternsOf, noneRule, nonePatternOf])
  rw [inst_toTerm]
  decide

/-- **The step agrees**: from a state that reads as `{sym 0}` an admitted firing reaches a state that reads as
`{sym 2}`; at a state that reads as `{sym 0, sym 1}` no firing is admitted. -/
theorem noneRule_on_the_step :
    (∃ (g : Firing ℕ E {r | r ∈ [noneRule]} (listState [.sym 0]).frame)
        (admitted : (schematicStep ℕ [noneRule]).Admits (s := listState [.sym 0]) g),
        ReadsBag ((schematicStep ℕ [noneRule]).result g admitted)
          (([.sym 2] : List Expr) : Multiset Expr)) ∧
      ∀ g : Firing ℕ E {r | r ∈ [noneRule]} (listState [.sym 0, .sym 1]).frame,
        ¬ (schematicStep ℕ [noneRule]).Admits (s := listState [.sym 0, .sym 1]) g := by
  have fragment : ∀ r ∈ [noneRule], NoneRestricted r := by
    intro r member
    rw [List.mem_singleton.mp member]
    exact noneRule_restricted
  refine ⟨readsBag_forward_none fragment (listState_reads _) noneRule_rewrites, fun g admitted => ?_⟩
  obtain ⟨bag', rewrites, -⟩ := readsBag_backward_none fragment (listState_reads _) g admitted
  exact noneRule_refused bag' rewrites

end Controls

#print axioms none_of_admitted
#print axioms rewrite_of_admitted_none
#print axioms admitted_of_rewrite_none
#print axioms rewritesNone_iff_of_positive
#print axioms readsBag_backward_none
#print axioms readsBag_forward_none
#print axioms correspondenceNone
#print axioms reachable_iff_none
#print axioms Controls.noneRule_rewrites
#print axioms Controls.noneRule_refused
#print axioms Controls.noneRule_on_the_step

end Mettapedia.Languages.MM0.OnTheStep.NoneRewriting
