import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Rewriting

/-!
# Unknowns determined by tells: the step on states that read as bags, beyond range restriction

`Machines.Rewriting` proves, for a finite list of rules that are range restricted (every unknown of a tell, a
check or a made row occurs in a take or read pattern), that the step on states that read as bags of rows
(`Machines.Reads`, `Machines.ReadsBag`) is rewriting of the bags by matching, one firing for one rewrite, along
runs of every length. A rule evaluated at a point of a function tells its value pattern equal to the function's
value and makes a row that holds it: the made unknown is bound by the tell and by no take or read pattern, so the
rule is not range restricted; and a program evaluated by an interpretation has one rule for each point of
evaluation, so it is not the program of a finite list. This module proves the same correspondence for the wider
class, for programs that are sets of rules, on the same notions.

* **Determined unknowns** (`Determines r x`): a take or read pattern binds `x`, or `x` occurs in one side of a
  tell whose other side holds determined unknowns only. A rule **makes determined rows** (`MakesDetermined`)
  when every unknown of a made row is determined, **writes determined terms** (`WritesDetermined`) when every
  unknown of a tell, a check or a made row is, and is in **the wider fragment** (`DeterminedPositive`) when it
  also has no collect pattern and only equation checks. Range-restricted positive rules are in it
  (`determinedPositive_of_fragment`).
* `matches_of_admitted`: **an admitted firing at a state that reads as rows is a firing by matching**, for every
  rule; and if the rule makes determined rows the result reads as the rows after the firing
  (`Machines.rowsAfter`). With range restriction this is `Machines.rewrite_of_admitted`.
* `admitted_of_matches`: **every firing by matching is an admitted firing** whose result reads as the made rows'
  instances beside the rest, for a rule of the wider fragment, when identities are infinitely many. With range
  restriction this is `Machines.admitted_of_rewrite`.
* `readsBag_backward_determined`, `readsBag_forward_determined`: the two directions on bags, for one rewrite by
  the firing's rule (`Machines.Rewrites` at the one rule).
* `stepCorrespondence`: the two directions as one `OperationalCorrespondence` from rewriting of bags by the rules
  of a program (`RewritesBy`, `rewritingBy`) to the step of the program (`programSystem`), related by
  `Machines.ReadsBag`: one rewrite for one firing each way, no firing silent. For the program of a list of rules
  the source is `Machines.Rewrites` (`rewritesBy_list`).
* `readsBag_of_run`: **states that read as bags are closed under the step** of a program whose rules make
  determined rows.
* `result_not_reads`: **the class cannot be widened to an unknown nothing binds.** If a made row holds an unknown
  that occurs in no take or read pattern and in no tell, the result of an admitted firing reads as no rows: two
  solutions of its knowledge read the made row differently.

Admission and the result of a firing do not depend on the rest of the program (`alone`), which is how the
lemmas of `Machines.Rewriting` and `Presentation.Schematic.Firings` about a firing of a list of rules are used
here for a firing of any program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open OneFrame (frames ext)
open NamesOnTheStep (Expr)
open LogicOverTheStep.StepSpan (Succ)
open Presentation (exists_taken exists_read exists_fresh bagOf_split)
open Presentation.Schematic
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (Reads ReadsBag Rewrites
  stateBound lt_stateBound mixedSolution mixed_reads mixed_below rowsAfter bag_after relabel_reads
  map_eq_map_of_zip)

universe uO

/-! ## Lists in pairs -/

theorem mem_zip_map_right {α β γ : Type*} {f : β → γ} {l₁ : List α} {l₂ : List β} {a : α} {b : β}
    (member : (a, b) ∈ l₁.zip l₂) : (a, f b) ∈ l₁.zip (l₂.map f) := by
  rw [List.zip_map_right]
  exact List.mem_map.mpr ⟨(a, b), member, rfl⟩

theorem exists_zip_of_mem_right {α β : Type*} : ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
    ∀ {b : β}, b ∈ l₂ → ∃ a, (a, b) ∈ l₁.zip l₂
  | _, [], _, _, member => absurd member List.not_mem_nil
  | [], _ :: _, lengths, _, _ => by simp at lengths
  | x :: xs, y :: ys, lengths, b, member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨x, List.mem_cons_self⟩
      · obtain ⟨a, inside⟩ := exists_zip_of_mem_right (Nat.succ.inj lengths) member
        exact ⟨a, List.mem_cons_of_mem _ inside⟩

/-! ## Solutions that read terms as ground rows -/

/-- Where every solution of a store reads a term through an opening as one ground row, every solution reads each
unknown of the term as the ground part of one solution does. -/
theorem unknowns_read {opening σ : Subst rowSig} {K : EquationStore Tm} (solved : A.Models σ K) {t : Tm}
    {e : Expr} (reads : ∀ τ : Subst rowSig, A.Models τ K → τ.applyTerm (opening.applyTerm t) = toTerm e) :
    ∀ x ∈ t.freeVars, ∀ τ : Subst rowSig, A.Models τ K →
      τ.applyTerm (opening x) = toTerm (groundPart (σ.comp opening) x) := by
  have composed : ∀ τ : Subst rowSig, A.Models τ K → (τ.comp opening).applyTerm t = toTerm e := fun τ sol =>
    (Subst.applyTerm_comp τ opening t).trans (reads τ sol)
  intro x vars τ sol
  have own := (inst_groundPart (σ.comp opening) t e (composed σ solved)).2 x vars
  have same := agree_of_applyTerm_eq t ((composed τ sol).trans (composed σ solved).symm) x vars
  exact same.trans own

/-- Where every solution reads each unknown of a term as an instantiation does, every solution reads the term as
its instance. -/
theorem term_reads {opening : Subst rowSig} {K : EquationStore Tm} {θ : ℕ → Expr} {t : Tm}
    (each : ∀ x ∈ t.freeVars, ∀ τ : Subst rowSig, A.Models τ K → τ.applyTerm (opening x) = toTerm (θ x))
    (τ : Subst rowSig) (sol : A.Models τ K) : τ.applyTerm (opening.applyTerm t) = toTerm (inst θ t) := by
  rw [← Subst.applyTerm_comp, ← applyTerm_lift]
  exact Subst.applyTerm_congr fun x vars => each x vars τ sol

/-- **A solution made ground**: every unknown it leaves is read as the symbol `0`. -/
def grounded (σ : Subst rowSig) : Subst rowSig := (lift fun _ => Expr.sym 0).comp σ

theorem grounded_models {K : EquationStore Tm} {σ : Subst rowSig} (solved : A.Models σ K) :
    A.Models (grounded σ) K :=
  A.models_compose solved (lift fun _ => Expr.sym 0)

theorem grounded_applyTerm (σ : Subst rowSig) (t : Tm) :
    (grounded σ).applyTerm t = toTerm (inst (fun _ => Expr.sym 0) (σ.applyTerm t)) := by
  unfold grounded
  rw [Subst.applyTerm_comp, applyTerm_lift]

/-- **A ground solution reads every term through an opening as the instance at its ground part.** -/
theorem inst_grounded (σ opening : Subst rowSig) (t : Tm) :
    toTerm (inst (groundPart ((grounded σ).comp opening)) t) = (grounded σ).applyTerm (opening.applyTerm t) := by
  have ground : ((grounded σ).comp opening).applyTerm t =
      toTerm (inst (fun _ => Expr.sym 0) (σ.applyTerm (opening.applyTerm t))) := by
    rw [Subst.applyTerm_comp, grounded_applyTerm]
  rw [(inst_groundPart _ t _ ground).1, grounded_applyTerm]

/-- **The reading that sends one unknown to a given row** and reads every other unknown as a substitution does. -/
def readingWith (τ : Subst rowSig) (x : ℕ) (value : Expr) : Subst rowSig :=
  fun y => if y = x then toTerm value else τ y

theorem readingWith_self (τ : Subst rowSig) (x : ℕ) (value : Expr) : readingWith τ x value x = toTerm value :=
  if_pos rfl

theorem readingWith_apart (τ : Subst rowSig) {x : ℕ} (value : Expr) {p : Tm} (apart : x ∉ p.freeVars) :
    (readingWith τ x value).applyTerm p = τ.applyTerm p := by
  apply Subst.applyTerm_congr
  intro y vars
  show (if y = x then toTerm value else τ y) = τ y
  exact if_neg fun (same : y = x) => apart (same ▸ vars)

/-! ## Determined unknowns -/

/-- **An unknown a rule determines**: a take or read pattern binds it, or it occurs in one side of a tell whose
other side holds determined unknowns only. -/
inductive Determines (r : SRule) : ℕ → Prop
  | bound {x : ℕ} : Bound r x → Determines r x
  | toldLeft {e : Tm × Tm} {x : ℕ} : e ∈ r.body.tell → (∀ y ∈ e.2.freeVars, Determines r y) →
      x ∈ e.1.freeVars → Determines r x
  | toldRight {e : Tm × Tm} {x : ℕ} : e ∈ r.body.tell → (∀ y ∈ e.1.freeVars, Determines r y) →
      x ∈ e.2.freeVars → Determines r x

/-- **A rule makes determined rows**: every unknown of a made row is determined. -/
def MakesDetermined (r : SRule) : Prop := ∀ t : Tm, t ∈ r.body.produce → ∀ x ∈ t.freeVars, Determines r x

/-- **A rule writes determined terms**: every unknown of a tell, a check or a made row is determined. -/
def WritesDetermined (r : SRule) : Prop := ∀ t : Tm, t ∈ written r → ∀ x ∈ t.freeVars, Determines r x

/-- **The wider fragment**: no collect pattern, only equation checks, and every unknown of a tell, a check or a
made row determined by matching or by a tell. -/
def DeterminedPositive (r : SRule) : Prop :=
  r.collect = [] ∧ r.body.checks.all isGuard = true ∧ WritesDetermined r

theorem makesDetermined_of_writes {r : SRule} (writes : WritesDetermined r) : MakesDetermined r :=
  fun t inProduce x vars => writes t (mem_written_of_produce inProduce) x vars

/-- **Range-restricted rules write determined terms.** -/
theorem writesDetermined_of_rangeRestricted {r : SRule} (restricted : RangeRestricted r) : WritesDetermined r :=
  fun t member x vars => .bound (restricted t member x vars)

/-- **The fragment of range-restricted positive rules lies in the wider fragment.** -/
theorem determinedPositive_of_fragment {r : SRule} (fragment : RangeRestrictedPositive r) :
    DeterminedPositive r :=
  ⟨fragment.1, fragment.2.1, writesDetermined_of_rangeRestricted fragment.2.2⟩

/-- The terms of a rule, by where they occur. -/
theorem mem_terms_iff (r : SRule) {t : Tm} :
    t ∈ r.terms ↔ t ∈ r.body.take ∨ t ∈ r.body.read ∨ t ∈ r.body.tell.map Prod.fst ∨
      t ∈ r.body.tell.map Prod.snd ∨ t ∈ r.body.checks.flatMap checkTerms ∨ t ∈ r.body.produce ∨ t ∈ r.collect := by
  simp only [Rule.terms, List.mem_append]
  tauto

section States

variable {O : Type uO} {P : Program (OneFrame.Terms Tm)}

/-! ## A firing of any program -/

/-- **A firing of a program as a firing of the program of its one rule**: the same rule, extension, opening and
selection. Admission and the result of a firing do not depend on the rest of the program. -/
def alone {s : SState O} (g : Firing O E P s.frame) : Firing O E {r | r ∈ [g.rule]} s.frame :=
  ⟨g.rule, List.mem_singleton_self _, g.ext, g.opening, g.selection, g.seen⟩

theorem row_label {s : SState O} (g : Firing O E P s.frame) (o : O) : g.row X s o = s.label o :=
  row_eq (alone g) o

/-- A solution of a firing's information solves the state's knowledge. -/
theorem knowledge_of_information {s : SState O} (g : Firing O E P s.frame) {σ : Subst rowSig}
    (solved : A.Models σ (g.information X s)) : A.Models σ s.knowledge :=
  Machines.knowledge_of_information (alone g) solved

/-- An equation of the information matching a pattern with a selected row. -/
theorem mem_matching_of {s : SState O} (g : Firing O E P s.frame) {patterns : List Tm} {selected : List O}
    {e : Equation Tm} (member : e ∈ g.matching X s (patterns.map g.opening.applyTerm) selected) :
    ∃ p o, (p, o) ∈ patterns.zip selected ∧ e = (g.opening.applyTerm p, s.label o) :=
  mem_matching (alone g) member

/-- **Renaming the rule's unknowns beyond every unknown the state mentions is a fresh opening**, for a firing of
any program. -/
theorem shift_fresh_at {s : SState O} (g : Firing O E P s.frame) (opening : g.opening = shift (stateBound s)) :
    g.Fresh X s :=
  Machines.shift_fresh_of_bound (alone g) opening

/-- **Every solution of the information reads each determined unknown as the ground part of one solution does**,
at a state that reads as rows: a pattern is read as the row it is matched with, and a tell carries the reading
from one side to the other. -/
theorem determined_reads {s : SState O} {rows : O → Expr} (reads : Reads s rows)
    (g : Firing O E P s.frame) (takeLength : g.rule.body.take.length = g.selection.taken.length)
    (readLength : g.rule.body.read.length = g.selection.read.length)
    (takenPresent : ∀ o ∈ g.selection.taken, o ∈ s.present)
    (readPresent : ∀ o ∈ g.selection.read, o ∈ s.present) {σ : Subst rowSig}
    (solved : A.Models σ (g.information X s)) {x : ℕ} (determined : Determines g.rule x) :
    ∀ τ : Subst rowSig, A.Models τ (g.information X s) →
      τ.applyTerm (g.opening x) = toTerm (groundPart (σ.comp g.opening) x) := by
  induction determined with
  | bound isBound =>
      obtain ⟨t, member, vars⟩ := isBound
      have matched : ∃ o ∈ s.present, ∀ τ : Subst rowSig, A.Models τ (g.information X s) →
          τ.applyTerm (g.opening.applyTerm t) = toTerm (rows o) := by
        rcases List.mem_append.mp member with taken | read
        · obtain ⟨o, inside⟩ := exists_zip_of_mem takeLength taken
          have present := takenPresent o (List.of_mem_zip inside).2
          refine ⟨o, present, fun τ sol => ?_⟩
          have equation : τ.applyTerm (g.opening.applyTerm t) = τ.applyTerm (g.row X s o) :=
            g.take_solved (b := PUnit.unit) sol (mem_zip_map_left inside)
          exact (equation.trans (congrArg τ.applyTerm (row_label g o))).trans
            (reads.reads τ (knowledge_of_information g sol) o present)
        · obtain ⟨o, inside⟩ := exists_zip_of_mem readLength read
          have present := readPresent o (List.of_mem_zip inside).2
          refine ⟨o, present, fun τ sol => ?_⟩
          have equation : τ.applyTerm (g.opening.applyTerm t) = τ.applyTerm (g.row X s o) :=
            g.read_solved (b := PUnit.unit) sol (mem_zip_map_left inside)
          exact (equation.trans (congrArg τ.applyTerm (row_label g o))).trans
            (reads.reads τ (knowledge_of_information g sol) o present)
      obtain ⟨o, -, matchedRow⟩ := matched
      exact unknowns_read solved matchedRow _ vars
  | @toldLeft e x member _ inside ih =>
      have told : ∀ τ : Subst rowSig, A.Models τ (g.information X s) →
          τ.applyTerm (g.opening.applyTerm e.1) = τ.applyTerm (g.opening.applyTerm e.2) := fun τ sol =>
        g.tell_solved (b := PUnit.unit) sol (List.mem_map_of_mem (f := fun pair : Tm × Tm =>
          (g.opening.applyTerm pair.1, g.opening.applyTerm pair.2)) member)
      exact unknowns_read solved (fun τ sol => (told τ sol).trans (term_reads ih τ sol)) x inside
  | @toldRight e x member _ inside ih =>
      have told : ∀ τ : Subst rowSig, A.Models τ (g.information X s) →
          τ.applyTerm (g.opening.applyTerm e.1) = τ.applyTerm (g.opening.applyTerm e.2) := fun τ sol =>
        g.tell_solved (b := PUnit.unit) sol (List.mem_map_of_mem (f := fun pair : Tm × Tm =>
          (g.opening.applyTerm pair.1, g.opening.applyTerm pair.2)) member)
      exact unknowns_read solved (fun τ sol => (told τ sol).symm.trans (term_reads ih τ sol)) x inside

variable [DecidableEq O]

/-! ## Admitted firings at states that read as rows are firings by matching -/

/-- **The result of an admitted firing of a rule that makes determined rows reads as the rows after it**, at a
state that reads as rows: each made identity carries the instance of its made row, every other identity keeps
its row. -/
theorem result_reads_determined {s : SState O} {rows : O → Expr} (reads : Reads s rows)
    (g : Firing O E P s.frame) (admitted : (step X O E P).Admits (s := s) g) (makes : MakesDetermined g.rule)
    {θ : ℕ → Expr} (agree : ∀ x, Determines g.rule x → ∀ τ : Subst rowSig, A.Models τ (g.information X s) →
      τ.applyTerm (g.opening x) = toTerm (θ x)) :
    Reads (g.result X s) (rowsAfter rows g.selection.made (g.rule.body.produce.map (inst θ))) := by
  obtain ⟨-, ⟨-, -, -, -, produceLength, -⟩, -, solvable, -⟩ := (admits_iff g).mp admitted
  refine ⟨(Frames.ofSubstitution_solvable_iff A _).mp solvable, fun σ solved o present => ?_⟩
  have solved' : A.Models σ (g.information X s) := solved
  have inFire : o ∈ fire s.present (g.selection.commit (T := Unit)) := present
  exact relabel_reads (g.row X s) rows g.opening.applyTerm (inst θ) g.selection.made g.rule.body.produce
    produceLength.symm
    (fun p member => term_reads (fun x vars => agree x (makes p member x vars)) σ solved')
    (fun notMade => by
      rcases mem_fire.mp inFire with ⟨inStore, -⟩ | made
      · rw [row_label]
        exact reads.reads σ (knowledge_of_information g solved') o inStore
      · exact absurd (List.mem_toFinset.mp made) notMade)

/-- **An admitted firing at a state that reads as rows is a firing by matching**, for every rule: some ground
instantiation of the rule's unknowns sends the takes and reads to the rows of the selected identities and solves
the rule's tells and equation guards. If the rule makes determined rows, the result reads as the rows after the
firing. -/
theorem matches_of_admitted {s : SState O} {rows : O → Expr} (reads : Reads s rows)
    (g : Firing O E P s.frame) (admitted : (step X O E P).Admits (s := s) g) :
    ∃ θ : ℕ → Expr,
      g.rule.body.take.map (inst θ) = g.selection.taken.map rows ∧
      g.rule.body.read.map (inst θ) = g.selection.read.map rows ∧
      (∀ e ∈ equationsOf g.rule, inst θ e.1 = inst θ e.2) ∧
      (MakesDetermined g.rule →
        Reads (g.result X s) (rowsAfter rows g.selection.made (g.rule.body.produce.map (inst θ)))) := by
  obtain ⟨-, ⟨-, -, takeLength, readLength, -, -⟩, enabled, solvable, checks, -⟩ :=
    (admits_iff g).mp admitted
  obtain ⟨σ₀, solved₀⟩ := (Frames.ofSubstitution_solvable_iff A _).mp solvable
  have solved : A.Models (grounded σ₀) (g.information X s) := grounded_models solved₀
  have takenPresent : ∀ o ∈ g.selection.taken, o ∈ s.present := fun o member =>
    enabled.taken_subset (List.mem_toFinset.mpr member)
  have readPresent : ∀ o ∈ g.selection.read, o ∈ s.present := fun o member =>
    enabled.kept_subset (List.mem_toFinset.mpr member)
  have matchedBy : ∀ {p : Tm} {o : O}, o ∈ s.present →
      (grounded σ₀).applyTerm (g.opening.applyTerm p) = (grounded σ₀).applyTerm (g.row X s o) →
        inst (groundPart ((grounded σ₀).comp g.opening)) p = rows o := by
    intro p o present equation
    exact toTerm_injective (((inst_grounded σ₀ g.opening p).trans equation).trans
      ((congrArg (grounded σ₀).applyTerm (row_label g o)).trans
        (reads.reads (grounded σ₀) (knowledge_of_information g solved) o present)))
  have takesMatch : ∀ x ∈ g.rule.body.take.zip g.selection.taken,
      inst (groundPart ((grounded σ₀).comp g.opening)) x.1 = rows x.2 := fun x inside =>
    matchedBy (takenPresent x.2 (List.of_mem_zip inside).2)
      (g.take_solved (b := PUnit.unit) solved (mem_zip_map_left inside))
  have readsMatch : ∀ x ∈ g.rule.body.read.zip g.selection.read,
      inst (groundPart ((grounded σ₀).comp g.opening)) x.1 = rows x.2 := fun x inside =>
    matchedBy (readPresent x.2 (List.of_mem_zip inside).2)
      (g.read_solved (b := PUnit.unit) solved (mem_zip_map_left inside))
  refine ⟨groundPart ((grounded σ₀).comp g.opening), map_eq_map_of_zip takeLength takesMatch,
    map_eq_map_of_zip readLength readsMatch, ?_, fun makes =>
      result_reads_determined reads g admitted makes fun x determined =>
        determined_reads reads g takeLength readLength takenPresent readPresent solved determined⟩
  intro e member
  have equal : (grounded σ₀).applyTerm (g.opening.applyTerm e.1) =
      (grounded σ₀).applyTerm (g.opening.applyTerm e.2) := by
    rcases List.mem_append.mp member with told | guarded
    · exact g.tell_solved (b := PUnit.unit) solved (List.mem_map_of_mem (f := fun pair : Tm × Tm =>
        (g.opening.applyTerm pair.1, g.opening.applyTerm pair.2)) told)
    · obtain ⟨c, inChecks, inGuard⟩ := List.mem_flatMap.mp guarded
      cases c with
      | equal l r =>
          rw [guardOf, List.mem_singleton] at inGuard
          subst inGuard
          exact checks (Check.map g.opening.applyTerm (.equal l r)) (List.mem_map_of_mem inChecks)
            PUnit.unit (grounded σ₀) solved
      | predicate quantifier _ => simp [guardOf] at inGuard
      | count _ _ => simp [guardOf] at inGuard
  exact toTerm_injective (((inst_grounded σ₀ g.opening e.1).trans equal).trans
    (inst_grounded σ₀ g.opening e.2).symm)

/-! ## Firings by matching at states that read as rows are admitted firings -/

/-- **Every firing by matching at a state that reads as rows is an admitted firing of `RuleSyntax.step`**, for a
rule of the wider fragment, when identities are infinitely many; its result reads as the made rows' instances
beside the rest. -/
theorem admitted_of_matches [Infinite O] {s : SState O} {rows : O → Expr} (reads : Reads s rows) {r : SRule}
    (member : r ∈ P) (fragment : DeterminedPositive r) {θ : ℕ → Expr} {restM : Multiset Expr}
    (split : (r.body.take.map (inst θ) : Multiset Expr) + restM = s.present.val.map rows)
    (readsIn : ∀ q ∈ r.body.read, inst θ q ∈ restM)
    (equations : ∀ e ∈ equationsOf r, inst θ e.1 = inst θ e.2) :
    ∃ (g : Firing O E P s.frame) (_ : (step X O E P).Admits (s := s) g), g.rule = r ∧
      ∃ rows' : O → Expr, Reads (g.result X s) rows' ∧
        (g.result X s).present.val.map rows' = (r.body.produce.map (inst θ) : Multiset Expr) + restM := by
  obtain ⟨noCollect, guards, writes⟩ := fragment
  obtain ⟨σ₀, solved₀⟩ := reads.solvable
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
  let g : Firing O E P s.frame := ⟨r, member, PUnit.unit, shift (stateBound s), ⟨taken, read, made⟩, []⟩
  have takeLength : r.body.take.length = taken.length := by
    rw [← List.length_map (f := inst θ), ← takenRows, List.length_map]
  have readLength : r.body.read.length = read.length := by
    rw [← List.length_map (f := inst θ), ← readRows, List.length_map]
  have takenPresent : ∀ o ∈ taken, o ∈ s.present := takenIn
  have readPresent : ∀ o ∈ read, o ∈ s.present := fun o inside => (Finset.mem_sdiff.mp (readIn o inside)).1
  have takesMatch : ∀ x ∈ r.body.take.zip taken, inst θ x.1 = rows x.2 := pairs_of_map_eq takenRows.symm
  have readsMatch : ∀ x ∈ r.body.read.zip read, inst θ x.1 = rows x.2 := pairs_of_map_eq readRows.symm
  have labelRead : ∀ o ∈ s.present,
      (mixedSolution (stateBound s) θ σ₀).applyTerm (s.label o) = toTerm (rows o) := by
    intro o present
    rw [mixed_below (stateBound s) θ σ₀ (t := s.label o) fun v vars =>
      lt_stateBound (Or.inr (Or.inr ⟨o, present, rfl⟩)) vars]
    exact reads.reads σ₀ solved₀ o present
  have knownStore : X.applyStore ((ext A).weaken g.ext) s.knowledge = s.knowledge :=
    Frames.applyStore_id (X := X) s.knowledge
  have solved : A.Models (mixedSolution (stateBound s) θ σ₀) (g.information X s) := by
    intro e inside
    unfold Firing.information at inside
    rw [knownStore] at inside
    simp only [List.mem_append] at inside
    rcases inside with ((old | taking) | reading) | told
    · show Subst.applyTerm _ e.1 = Subst.applyTerm _ e.2
      rw [mixed_below (stateBound s) θ σ₀ (t := e.1) fun v vars =>
          lt_stateBound (Or.inl (List.mem_map_of_mem old)) vars,
        mixed_below (stateBound s) θ σ₀ (t := e.2) fun v vars =>
          lt_stateBound (Or.inr (Or.inl (List.mem_map_of_mem old))) vars]
      exact solved₀ e old
    · obtain ⟨p, o, pair, rfl⟩ := mem_matching_of g taking
      show Subst.applyTerm _ (Subst.applyTerm (shift _) p) = Subst.applyTerm _ (s.label o)
      rw [mixed_reads, labelRead o (takenPresent o (List.of_mem_zip pair).2), takesMatch _ pair]
    · obtain ⟨p, o, pair, rfl⟩ := mem_matching_of g reading
      show Subst.applyTerm _ (Subst.applyTerm (shift _) p) = Subst.applyTerm _ (s.label o)
      rw [mixed_reads, labelRead o (readPresent o (List.of_mem_zip pair).2), readsMatch _ pair]
    · obtain ⟨pair, inTell, rfl⟩ := List.mem_map.mp told
      show Subst.applyTerm _ (Subst.applyTerm (shift _) pair.1) =
        Subst.applyTerm _ (Subst.applyTerm (shift _) pair.2)
      rw [mixed_reads, mixed_reads, equations pair (List.mem_append_left _ inTell)]
  have part : ∀ x, groundPart ((mixedSolution (stateBound s) θ σ₀).comp (shift (stateBound s))) x = θ x :=
    fun x => groundPart_spec (mixed_reads (stateBound s) θ σ₀ (.var x))
  have agree : ∀ x, Determines r x → ∀ τ : Subst rowSig, A.Models τ (g.information X s) →
      τ.applyTerm (shift (stateBound s) x) = toTerm (θ x) := fun x determined τ sol =>
    (determined_reads reads g takeLength readLength takenPresent readPresent solved determined τ sol).trans
      (congrArg toTerm (part x))
  have admitted : (step X O E P).Admits (s := s) g := by
    refine (admits_iff g).mpr ⟨shift_fresh_at g rfl, ⟨takenNodup, madeNodup, takeLength, readLength,
      madeLength.symm, by rw [noCollect]; rfl⟩, ?_,
      (Frames.ofSubstitution_solvable_iff A _).mpr ⟨_, solved⟩, ?_, ?_⟩
    · exact ⟨takenSub, fun o inside => readPresent o (List.mem_toFinset.mp inside),
        Finset.disjoint_left.mpr fun o taking reading =>
          (Finset.mem_sdiff.mp (readIn o (List.mem_toFinset.mp reading))).2 taking,
        Finset.disjoint_left.mpr fun o inside present => madeFresh o (List.mem_toFinset.mp inside) present,
        fun query inside => by simp [Selection.commit] at inside⟩
    · intro c inChecks b σ' solved'
      obtain ⟨c₀, inRule, rfl⟩ := List.mem_map.mp inChecks
      have isGuardC := List.all_eq_true.mp guards c₀ inRule
      cases c₀ with
      | equal l r' =>
          have inEquations : (l, r') ∈ equationsOf r :=
            List.mem_append_right _ (List.mem_flatMap.mpr ⟨.equal l r', inRule, List.mem_singleton_self _⟩)
          have inWritten := mem_written_of_equation inEquations
          show Subst.applyTerm σ' (Subst.applyTerm (shift _) l) = Subst.applyTerm σ' (Subst.applyTerm (shift _) r')
          rw [term_reads (fun x vars => agree x (writes l inWritten.1 x vars)) σ' solved',
            term_reads (fun x vars => agree x (writes r' inWritten.2 x vars)) σ' solved',
            equations _ inEquations]
      | predicate quantifier _ => simp [isGuard] at isGuardC
      | count _ _ => simp [isGuard] at isGuardC
    · intro q inside
      have none : (g.collectOpened X).zip g.seen = [] := by
        simp [Firing.collectOpened, g, noCollect]
      rw [none] at inside
      exact absurd inside List.not_mem_nil
  have lengths : made.length = (r.body.produce.map (inst θ)).length := by
    rw [List.length_map]
    exact madeLength
  have fresh : Disjoint made.toFinset s.present :=
    Finset.disjoint_left.mpr fun o inside present => madeFresh o (List.mem_toFinset.mp inside) present
  refine ⟨g, admitted, rfl, rowsAfter rows made (r.body.produce.map (inst θ)),
    result_reads_determined reads g admitted (makesDetermined_of_writes writes) agree, ?_⟩
  rw [restEq]
  exact (bag_after s.present rows g.selection madeNodup lengths fresh).trans (add_comm _ _)

/-! ## Rewriting of bags by the rules of a program, and the correspondence -/

/-- **One rewrite of a bag by a rule of a program**: `Machines.Rewrites` at one rule of the set. -/
def RewritesBy (P : Program (OneFrame.Terms Tm)) (bag bag' : Multiset Expr) : Prop :=
  ∃ r ∈ P, Rewrites [r] bag bag'

omit [DecidableEq O] in
/-- For the program of a list of rules, it is rewriting by the list. -/
theorem rewritesBy_list {rules : List SRule} {bag bag' : Multiset Expr} :
    RewritesBy {r | r ∈ rules} bag bag' ↔ Rewrites rules bag bag' := by
  constructor
  · rintro ⟨r, member, single⟩
    exact Machines.rewrites_of_mem member single
  · rintro ⟨r, member, rewritten⟩
    exact ⟨r, member, r, List.mem_singleton_self _, rewritten⟩

/-- **An admitted firing at a state that reads as a bag is one rewrite of the bag by the firing's rule, and its
result reads as the rewritten bag**, when the rule makes determined rows. -/
theorem readsBag_backward_determined {s : SState O} {bag : Multiset Expr} (reads : ReadsBag s bag)
    (g : Firing O E P s.frame) (admitted : (step X O E P).Admits (s := s) g) (makes : MakesDetermined g.rule) :
    ∃ bag', Rewrites [g.rule] bag bag' ∧ ReadsBag (g.result X s) bag' := by
  obtain ⟨rows, reads, rfl⟩ := reads
  obtain ⟨θ, takes, readsMatch, equations, after⟩ := matches_of_admitted reads g admitted
  obtain ⟨-, ⟨takenNodup, madeNodup, -, readLength, produceLength, -⟩, enabled, -⟩ :=
    (admits_iff g).mp admitted
  have lengths : g.selection.made.length = (g.rule.body.produce.map (inst θ)).length := by
    rw [List.length_map]
    exact produceLength.symm
  refine ⟨_, ⟨g.rule, List.mem_singleton_self _, θ, (s.present \ g.selection.taken.toFinset).val.map rows, ?_, ?_,
    equations, rfl⟩, ⟨_, after makes, (bag_after s.present rows g.selection madeNodup lengths enabled.fresh).trans
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

/-- **Every rewrite of the bag a state reads as, by a rule of the program in the wider fragment, is an admitted
firing of that rule whose result reads as the rewritten bag**, when identities are infinitely many. -/
theorem readsBag_forward_determined [Infinite O] {r : SRule} (member : r ∈ P) (fragment : DeterminedPositive r)
    {s : SState O} {bag bag' : Multiset Expr} (reads : ReadsBag s bag) (rewrites : Rewrites [r] bag bag') :
    ∃ (g : Firing O E P s.frame) (_ : (step X O E P).Admits (s := s) g), g.rule = r ∧
      ReadsBag (g.result X s) bag' := by
  obtain ⟨rows, reads, rfl⟩ := reads
  obtain ⟨r', inside, θ, rest, split, readsIn, equations, rfl⟩ := rewrites
  obtain rfl := List.mem_singleton.mp inside
  obtain ⟨g, admitted, isRule, rows', reads', bagEq⟩ :=
    admitted_of_matches reads member fragment split readsIn equations
  exact ⟨g, admitted, isRule, rows', reads', bagEq⟩

/-- **Rewriting of bags by the rules of a program, as a system**: bags, equal when identical, under
`RewritesBy`. -/
def rewritingBy (P : Program (OneFrame.Terms Tm)) : GSLT := equalityGSLT (Multiset Expr) (RewritesBy P)

/-- **The step of a program, as a system**: states, equal when identical, under the successor relation of
`RuleSyntax.step`. For the program of a list of rules it is `Machines.stepSystem`. -/
def programSystem (O : Type uO) [DecidableEq O] (P : Program (OneFrame.Terms Tm)) : GSLT :=
  equalityGSLT (SState O) (Succ (step X O E P).toStep)

/-- **The correspondence, for the wider fragment and any program**: rewriting of bags by the rules of the
program and the step of the program, related by reading a state as a bag. A firing of the step is read back as
one rewrite, and a rewrite is realized by one firing. -/
def stepCorrespondence [Infinite O] (fragment : ∀ r ∈ P, DeterminedPositive r) :
    OperationalCorrespondence (rewritingBy P) (programSystem O P) where
  related bag s := ReadsBag s bag
  readStep := by
    intro bag s s' reads stepped
    obtain ⟨g, admitted, rfl⟩ := stepped
    obtain ⟨bag', rewrites, reads'⟩ := readsBag_backward_determined reads g admitted
      (makesDetermined_of_writes (fragment g.rule g.member).2.2)
    exact Or.inr ⟨bag', ⟨g.rule, g.member, rewrites⟩, reads'⟩
  forward := by
    intro bag bag' s reads rewrites
    obtain ⟨r, member, single⟩ := rewrites
    obtain ⟨g, admitted, -, reads'⟩ := readsBag_forward_determined member (fragment r member) reads single
    exact ⟨_, (executionPath_nonempty_iff_multiStep (programSystem O P) _ _).mpr
      (.step ⟨g, admitted, rfl⟩ (.refl _)), reads'⟩

/-- **States that read as bags are closed under the step** of a program whose rules make determined rows. -/
theorem readsBag_of_succ (makes : ∀ r ∈ P, MakesDetermined r) {s t : SState O}
    (moved : Succ (step X O E P).toStep s t) (reads : ∃ bag, ReadsBag s bag) : ∃ bag, ReadsBag t bag := by
  obtain ⟨bag, readsBag⟩ := reads
  obtain ⟨g, admitted, rfl⟩ := moved
  obtain ⟨bag', -, reads'⟩ := readsBag_backward_determined readsBag g admitted (makes g.rule g.member)
  exact ⟨bag', reads'⟩

/-- **Along every run of a program whose rules make determined rows, from a state that reads as a bag, every
state reads as a bag.** -/
theorem readsBag_of_run (makes : ∀ r ∈ P, MakesDetermined r) {s t : SState O}
    (run : Relation.ReflTransGen (Succ (step X O E P).toStep) s t) (reads : ∃ bag, ReadsBag s bag) :
    ∃ bag, ReadsBag t bag := by
  induction run with
  | refl => exact reads
  | tail _ moved ih => exact readsBag_of_succ makes moved ih

/-! ## A made unknown that nothing binds is not read -/

/-- **The class cannot be widened to an unknown nothing binds.** If a made row of the rule holds an unknown that
occurs in no take or read pattern and in no tell, then the result of an admitted firing reads as no rows: two
solutions of its knowledge read that made row as two different rows. -/
theorem result_not_reads {s : SState O} (g : Firing O E P s.frame)
    (admitted : (step X O E P).Admits (s := s) g) {t : Tm} (inProduce : t ∈ g.rule.body.produce) {x : ℕ}
    (inRow : x ∈ t.freeVars) (unbound : ∀ u : Tm, u ∈ g.rule.body.take ++ g.rule.body.read → x ∉ u.freeVars)
    (untold : ∀ e : Tm × Tm, e ∈ g.rule.body.tell → x ∉ e.1.freeVars ∧ x ∉ e.2.freeVars) :
    ¬ ∃ rows : O → Expr, Reads (g.result X s) rows := by
  rintro ⟨rows, reads⟩
  obtain ⟨fresh, ⟨-, madeNodup, -, -, produceLength, -⟩, enabled, solvable, -, -⟩ :=
    (admits_iff g).mp admitted
  obtain ⟨σ, solved⟩ := (Frames.ofSubstitution_solvable_iff A _).mp solvable
  have knownStore : X.applyStore ((ext A).weaken g.ext) s.knowledge = s.knowledge :=
    Frames.applyStore_id (X := X) s.knowledge
  -- for every row there is a solution that reads the unknown as that row
  have other : ∀ value : Expr, ∃ u : Subst rowSig, A.Models u (g.information X s) ∧
      u.applyTerm (g.opening.applyTerm t) = (readingWith (σ.comp g.opening) x value).applyTerm t := by
    intro value
    obtain ⟨u, onState, onRule⟩ := fresh PUnit.unit σ (readingWith (σ.comp g.opening) x value)
    have stateReads : ∀ m : Tm, s.Mentions m → u.applyTerm m = σ.applyTerm m := by
      intro m mentioned
      have read : u.applyTerm ((Subst.id rowSig).applyTerm m) = σ.applyTerm m := onState m mentioned
      rw [Subst.applyTerm_id] at read
      exact read
    have ruleReads : ∀ p : Tm, p ∈ g.rule.terms → x ∉ p.freeVars →
        u.applyTerm (g.opening.applyTerm p) = σ.applyTerm (g.opening.applyTerm p) := by
      intro p inTerms apart
      have read : u.applyTerm (g.opening.applyTerm p) = (readingWith (σ.comp g.opening) x value).applyTerm p :=
        onRule p inTerms
      rw [read, readingWith_apart _ value apart, Subst.applyTerm_comp]
    refine ⟨u, ?_, onRule t ((mem_terms_iff g.rule).mpr (.inr (.inr (.inr (.inr (.inr (.inl inProduce)))))))⟩
    intro e inside
    unfold Firing.information at inside
    rw [knownStore] at inside
    simp only [List.mem_append] at inside
    rcases inside with ((old | taking) | reading) | told
    · show u.applyTerm e.1 = u.applyTerm e.2
      rw [stateReads e.1 (.inl (List.mem_map_of_mem old)), stateReads e.2 (.inr (.inl (List.mem_map_of_mem old)))]
      exact knowledge_of_information g solved e old
    · obtain ⟨p, o, pair, rfl⟩ := mem_matching_of g taking
      have inTake := (List.of_mem_zip pair).1
      have present : o ∈ s.present := enabled.taken_subset (List.mem_toFinset.mpr (List.of_mem_zip pair).2)
      have equation : σ.applyTerm (g.opening.applyTerm p) = σ.applyTerm (g.row X s o) :=
        g.take_solved (b := PUnit.unit) solved (mem_zip_map_left pair)
      show u.applyTerm (g.opening.applyTerm p) = u.applyTerm (s.label o)
      rw [ruleReads p ((mem_terms_iff g.rule).mpr (.inl inTake)) (unbound p (List.mem_append_left _ inTake)),
        stateReads (s.label o) (.inr (.inr ⟨o, present, rfl⟩)), equation, row_label]
    · obtain ⟨p, o, pair, rfl⟩ := mem_matching_of g reading
      have inRead := (List.of_mem_zip pair).1
      have present : o ∈ s.present := enabled.kept_subset (List.mem_toFinset.mpr (List.of_mem_zip pair).2)
      have equation : σ.applyTerm (g.opening.applyTerm p) = σ.applyTerm (g.row X s o) :=
        g.read_solved (b := PUnit.unit) solved (mem_zip_map_left pair)
      show u.applyTerm (g.opening.applyTerm p) = u.applyTerm (s.label o)
      rw [ruleReads p ((mem_terms_iff g.rule).mpr (.inr (.inl inRead)))
          (unbound p (List.mem_append_right _ inRead)),
        stateReads (s.label o) (.inr (.inr ⟨o, present, rfl⟩)), equation, row_label]
    · obtain ⟨pair, inTell, rfl⟩ := List.mem_map.mp told
      have equation : σ.applyTerm (g.opening.applyTerm pair.1) = σ.applyTerm (g.opening.applyTerm pair.2) :=
        g.tell_solved (b := PUnit.unit) solved (List.mem_map_of_mem (f := fun pair : Tm × Tm =>
          (g.opening.applyTerm pair.1, g.opening.applyTerm pair.2)) inTell)
      show u.applyTerm (g.opening.applyTerm pair.1) = u.applyTerm (g.opening.applyTerm pair.2)
      rw [ruleReads pair.1 ((mem_terms_iff g.rule).mpr (.inr (.inr (.inl (List.mem_map_of_mem inTell)))))
          (untold pair inTell).1,
        ruleReads pair.2 ((mem_terms_iff g.rule).mpr (.inr (.inr (.inr (.inl (List.mem_map_of_mem inTell))))))
          (untold pair inTell).2, equation]
  -- the made identity of the row, and its label
  obtain ⟨o, paired⟩ := exists_zip_of_mem_right produceLength.symm inProduce
  have lengths : g.selection.made.length = (g.opened X).produce.length := by
    simp only [Firing.opened, RuleInstance.map, List.length_map]
    exact produceLength.symm
  have label : (g.result X s).label o = g.opening.applyTerm t :=
    Firing.relabel_zip (g.row X s) g.selection.made (g.opened X).produce madeNodup lengths
      (o, g.opening.applyTerm t) (mem_zip_map_right (f := g.opening.applyTerm) paired)
  have present : o ∈ (g.result X s).present :=
    mem_fire.mpr (.inr (List.mem_toFinset.mpr (List.of_mem_zip paired).1))
  obtain ⟨u₀, solved₀, reads₀⟩ := other (.sym 0)
  obtain ⟨u₁, solved₁, reads₁⟩ := other (.sym 1)
  have row₀ := reads.reads u₀ solved₀ o present
  have row₁ := reads.reads u₁ solved₁ o present
  rw [label] at row₀ row₁
  have same : (readingWith (σ.comp g.opening) x (.sym 0)).applyTerm t =
      (readingWith (σ.comp g.opening) x (.sym 1)).applyTerm t :=
    reads₀.symm.trans (row₀.trans (row₁.symm.trans reads₁))
  have atX := agree_of_applyTerm_eq t same x inRow
  rw [readingWith_self, readingWith_self] at atX
  exact absurd (toTerm_injective atX) (by decide)

end States

#print axioms unknowns_read
#print axioms inst_grounded
#print axioms determined_reads
#print axioms shift_fresh_at
#print axioms result_reads_determined
#print axioms matches_of_admitted
#print axioms admitted_of_matches
#print axioms rewritesBy_list
#print axioms readsBag_backward_determined
#print axioms readsBag_forward_determined
#print axioms stepCorrespondence
#print axioms readsBag_of_run
#print axioms result_not_reads

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions
