import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondenceChild
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondenceLive

/-!
# Solution-wise token phases and the three-state child epoch

`ReflLocatedStep` proves the one-step-per-child phase discipline (`PendingPhase`, `DonePhase`,
`at_most_one_step`, `exactly_one_before_close`) against a fixed location term, so its progress
bridges (`child_steps_once`, `child_closes_once`) ask for a ground child location
(`pvars (pendingTok (childLoc m x p) m) = []`). When a reflected process binds a variable — as in
`for(y <- @0) y` — that variable occurs inside `childLoc m x p`, so the child location is not ground.

Here every phase predicate instantiates the location and parent by the same solution as the row's
label, matching `ReflCorrespondence.Clean` and `ReflCorrespondence.Live`:

* **Location depth** (`locDepth`, `not_nameLaws_childLoc_self`, `not_nameLaws_childLoc_rootLoc`):
  `NameLaws` preserves the nesting depth of `Child` constructors, so no child location equals its own
  parent or `Root` at any solution.
* **Solution-wise phases** (`PendingPhaseS`, `DonePhaseS`, `StepAtS`, `CloseAtS`): before the child's
  step, a unique present row reads as `Pending(l, m)` at every solution and no row may read as
  `Done(l, _, _)`; after the step, a unique present row reads as `Done(l, m, _)` at every solution
  and no row may read as `Pending(l, _)`.
* **Phase transitions and uniqueness** (`pending_phase_step_S`, `done_phase_step_S`,
  `close_refused_before_step_S`, `at_most_one_step_S`, `exactly_one_before_close_S`): at most one
  source step (`commChild` or `closeChild`) fires at `l` before its close, and a close of `l` fires
  only after such a step, with no groundness hypothesis on `m`, `x`, or `p`.
* **Progress without groundness** (`child_steps_once_S`, `child_closes_once_S`), plus the full
  three-state epoch cycle `Clean -> PendingPhaseS -> DonePhaseS -> Clean`
  (`clean_preserved_unless_open_S`, `openRoot_enters_pending_S`, `close_returns_to_clean_S`).
* **Positive and negative examples**: a non-ground child location carrying a bound variable inhabits
  both `PendingPhaseS` and `DonePhaseS` while failing `ReflLocatedStep`'s groundness side condition
  (`nonGround_pending_phase_example`, `nonGround_not_ground_example`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar nQuote tProc pReflect demoChan)
open MeTTaOperationsComm (psubst PSubst pvars psubst_none psubst_comp psubst_of_pvars_nil psubst_pZero)
open MeTTaCalculus.Corrected (psubstList_eq_map)
open FiniteProgram (commRule heatRule clearRule leftPart rightPart firstPattern secondPattern
  channelUnknown firstBody secondBody predot)
open Comm (Tm)
open OneFrame (embed)
open ReflNames (NameLaws NameRewrite nameAction QN QNE nameLaws_heads nameLaws_apply_iff IsQuote)
open ReflLocated (atLoc rootLoc childLoc pendingTok doneTok locL locM reflP accC anyY anyZ atRule
  located commChild heatChild cool closeRoot closeChild openRoot openChild
  exists_mem_zip psubst_apply psubst_rootLoc psubst_atLoc_any psubst_pendingTok locatedFrame_name)
open ReflPacking (psubst_doneTok nameLaws_doneTok_iff)
open ReflLocatedStep (located_cases produce_shapes take_shapes head_of_reading head_of_reading₂
  psubst_childLoc nameLaws_pendingTok_iff nameLaws_childLoc_iff exists_mem_zip_right res resConf
  info_known take_reads read_reads taken_row solution_of_admitted result_present result_label_old
  result_label_made made_label made_not_present result_row opened_check_mem check_fails_pending
  check_fails_done openRoot_checks openChild_checks commChildAt closeChildAt child_comm_admitted
  child_close_admitted psubst_pReflect nameLaws_pReflect_iff PendingPhase DonePhase)
open ReflCorrespondence (Clean Live openRootAt openRoot_reads)

/-! ## Nesting depth of child locations -/

/-- Nesting depth along the parent chain of `Child(m, x, p)` constructors. -/
def locDepth : Pattern → ℕ
  | .apply "Child" [m, _, _] => locDepth m + 1
  | _ => 0

theorem locDepth_rootLoc : locDepth rootLoc = 0 := rfl

theorem locDepth_childLoc (m x p : Pattern) : locDepth (childLoc m x p) = locDepth m + 1 := rfl

theorem locDepth_apply_nonChild {c : String} (notChild : c ≠ "Child") (args : List Pattern) :
    locDepth (.apply c args) = 0 := by
  unfold locDepth
  split
  · rename_i m x p heq
    simp only [Pattern.apply.injEq] at heq
    exact absurd heq.1 notChild
  · rfl

theorem locDepth_apply_len {c : String} {args : List Pattern} (badLen : args.length ≠ 3) :
    locDepth (.apply c args) = 0 := by
  unfold locDepth
  split
  · rename_i m x p heq
    simp only [Pattern.apply.injEq] at heq
    have : args.length = 3 := by rw [heq.2]; rfl
    exact absurd this badLen
  · rfl

/-- One rewrite step inside a quote preserves `locDepth`. -/
theorem locDepth_nameRewrite {a b : Pattern} (step : NameRewrite a b) : locDepth a = locDepth b := by
  induction step with
  | @quote c quoting p q _ =>
      have notChild : c ≠ "Child" := by
        rcases quoting with rfl | rfl <;> decide
      rw [locDepth_apply_nonChild notChild, locDepth_apply_nonChild notChild]
  | @apply c pre post u v _ ih =>
      by_cases isChild : c = "Child"
      · subst isChild
        by_cases len3 : (pre ++ u :: post).length = 3
        · match pre, post, len3 with
          | [], [x, p], _ => exact congrArg (· + 1) ih
          | [m], [p], _ => rfl
          | [m, x], [], _ => rfl
          | _ :: _ :: _ :: _, _, len3 => simp at len3
        · have len3' : (pre ++ v :: post).length ≠ 3 := by
            simpa [List.length_append] using len3
          rw [locDepth_apply_len len3, locDepth_apply_len len3']
      · rw [locDepth_apply_nonChild isChild, locDepth_apply_nonChild isChild]
  | lambda _ _ _ => rfl
  | multiLambda _ _ _ => rfl
  | substBody _ _ _ => rfl
  | substRepl _ _ _ => rfl
  | collection _ _ _ _ _ _ => rfl

/-- Equality modulo the name laws preserves `locDepth`. -/
theorem locDepth_nameLaws {a b : Pattern} (same : NameLaws a b) : locDepth a = locDepth b := by
  induction same with
  | rel _ _ r => exact locDepth_nameRewrite r
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **No child location equals its own parent modulo the name laws.** -/
theorem not_nameLaws_childLoc_self (m x p : Pattern) : ¬ NameLaws (childLoc m x p) m := by
  intro same
  have eqDepth := locDepth_nameLaws same
  rw [locDepth_childLoc] at eqDepth
  omega

/-- **No child location equals `Root` modulo the name laws.** -/
theorem not_nameLaws_childLoc_rootLoc (m x p : Pattern) : ¬ NameLaws (childLoc m x p) rootLoc := by
  intro same
  have eqDepth := locDepth_nameLaws same
  rw [locDepth_childLoc, locDepth_rootLoc] at eqDepth
  omega

/-- Well-formed locations built from `Root` by nested `Child` constructors. -/
inductive WellFormedLoc : Pattern → Prop where
  | root : WellFormedLoc rootLoc
  | child {m : Pattern} (x p : Pattern) : WellFormedLoc m → WellFormedLoc (childLoc m x p)

theorem locDepth_psubst_of_wellFormed {l : Pattern} (wf : WellFormedLoc l) (σ : PSubst) :
    locDepth (psubst σ l) = locDepth l := by
  induction wf with
  | root => rw [psubst_rootLoc]
  | child x p _ ih => rw [psubst_childLoc, locDepth_childLoc, locDepth_childLoc, ih]

theorem not_nameLaws_of_wellFormed_depth_ne {l₁ l₂ : Pattern} (wf₁ : WellFormedLoc l₁)
    (wf₂ : WellFormedLoc l₂) (diff : locDepth l₁ ≠ locDepth l₂) (σ : PSubst) :
    ¬ NameLaws (psubst σ l₁) (psubst σ l₂) := by
  intro same
  have eqDepth := locDepth_nameLaws same
  rw [locDepth_psubst_of_wellFormed wf₁ σ, locDepth_psubst_of_wellFormed wf₂ σ] at eqDepth
  exact diff eqDepth

/-! ## Universal none query of rows at a location -/

section NoneCheck

variable {O : Type*} [DecidableEq O]

/-- **Universal row-none check refutes any present row at that location**: if a rule checks
`.predicate .none (atLoc anyY childPat)` and does not mention `"Y"` in its takes, reads, tells, or `childPat`,
then at no solution `σ` of an admitted firing's information can a present row read at `childPat`. -/
theorem check_fails_row_at {label : O → Pattern} {C : Configuration Pattern O}
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    {childPat : Pattern}
    (hasCheck : Check.predicate .none (atLoc anyY childPat) ∈ g.rule.body.checks)
    (noTells : g.rule.body.tell = [])
    (takesApart : ∀ t ∈ g.rule.body.take, "Y" ∉ pvars t)
    (readsApart : ∀ t ∈ g.rule.body.read, "Y" ∉ pvars t)
    (patApart : "Y" ∉ pvars childPat)
    {σ : PSubst} (solved : nameAction.Models σ (g.information QN (embed label C)))
    {l y : Pattern} (child : NameLaws (psubst σ (psubst g.opening childPat)) l)
    {r : O} (present : r ∈ C.present) (reads : NameLaws (psubst σ (label r)) (atLoc y l)) :
    False := by
  obtain ⟨fresh, _, enabled, _, checks, _⟩ := (RuleSyntax.admits_iff g).mp admitted
  let h : PSubst := fun v => if v = "Y" then some y else some (psubst σ (psubst g.opening (.fvar v)))
  have away : ∀ t : Pattern, "Y" ∉ pvars t → psubst h t = psubst σ (psubst g.opening t) := by
    intro t apart
    rw [psubst_comp]
    apply MeTTaCalculus.Corrected.psubst_getD_congr_on
    intro v occurs
    have notY : v ≠ "Y" := fun same => apart (same ▸ occurs)
    simp only [h, if_neg notY, Option.getD_some]
    rw [psubst_comp]
    rfl
  obtain ⟨u, solvedU, onState, onRule⟩ := Comm.information_amalgamates_matched (Y := QN) (s := embed label C) g
    fresh (b := PUnit.unit) σ h (info_known g solved)
    (by rw [noTells]; exact fun _ member => absurd member List.not_mem_nil)
    (fun o member => enabled.taken_subset (by simpa [Selection.commit] using member))
    (fun o member => enabled.kept_subset (by simpa [Selection.commit] using member))
    (fun qq member => by
      have apart := takesApart qq.1 (List.of_mem_zip member).1
      show NameLaws (psubst h qq.1) (psubst σ (label qq.2))
      rw [away qq.1 apart]
      exact take_reads g solved member)
    (fun qq member => by
      have apart := readsApart qq.1 (List.of_mem_zip member).1
      show NameLaws (psubst h qq.1) (psubst σ (label qq.2))
      rw [away qq.1 apart]
      exact read_reads g solved member)
  have holds : ∀ o ∈ C.present, ¬ NameLaws
      (psubst u (psubst g.opening (atLoc anyY childPat)))
      (psubst u (g.row QN (embed label C) o)) :=
    checks _ (opened_check_mem hasCheck) PUnit.unit u solvedU
  apply holds r present
  rw [OneFrame.row_eq]
  have term : atLoc anyY childPat ∈ g.rule.terms := by
    simp only [Rule.terms, List.mem_append]
    exact .inl (.inl (.inr (List.mem_flatMap.mpr ⟨_, hasCheck, by simp [checkTerms]⟩)))
  have ruleSide : NameLaws (psubst u (psubst g.opening (atLoc anyY childPat)))
      (psubst h (atLoc anyY childPat)) := onRule _ term
  have stateSide : NameLaws (psubst u (psubst (fun _ => none) (label r))) (psubst σ (label r)) :=
    onState (label r) (Or.inr (Or.inr ⟨r, present, rfl⟩))
  rw [psubst_none] at stateSide
  have hCheck : psubst h (atLoc anyY childPat) = atLoc y (psubst σ (psubst g.opening childPat)) := by
    rw [psubst_atLoc_any, away childPat patApart]
    simp [h, anyY, psubst]
  refine ruleSide.trans ?_
  rw [hCheck]
  exact ((locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨NameLaws.refl _, child⟩).trans
    (reads.symm.trans stateSide.symm)

end NoneCheck

/-! ## Solution-wise phases of a child location -/

section Phases

variable {O : Type*} [DecidableEq O]

/-- A row may read as a `Pending` token of `l` at some solution of the knowledge. -/
def MayPendS (l : Pattern) (label : O → Pattern) (C : Configuration Pattern O) (o : O) : Prop :=
  ∃ σ : PSubst, nameAction.Models σ C.equations ∧
    ∃ m', NameLaws (psubst σ (label o)) (pendingTok (psubst σ l) m')

/-- A row may read as a `Done` token of `l` at some solution of the knowledge. -/
def MayDoneS (l : Pattern) (label : O → Pattern) (C : Configuration Pattern O) (o : O) : Prop :=
  ∃ σ : PSubst, nameAction.Models σ C.equations ∧
    ∃ m' c, NameLaws (psubst σ (label o)) (doneTok (psubst σ l) m' c)

/-- **First phase (solution-wise)**: `q` is present, reads as `Pending(l, m)` at every solution,
is the unique row that may read as a `Pending` token of `l`, and no row may read as `Done(l, _, _)`. -/
structure PendingPhaseS (l m : Pattern) (label : O → Pattern) (C : Configuration Pattern O) (q : O) :
    Prop where
  present : q ∈ C.present
  reads : ∀ σ : PSubst, nameAction.Models σ C.equations →
    NameLaws (psubst σ (label q)) (psubst σ (pendingTok l m))
  unique : ∀ o ∈ C.present, MayPendS l label C o → o = q
  noDone : ∀ o ∈ C.present, ¬ MayDoneS l label C o

/-- **Second phase (solution-wise)**: `d` is present, reads as `Done(l, m, _)` at every solution,
is the unique row that may read as a `Done` token of `l`, and no row may read as `Pending(l, _)`. -/
structure DonePhaseS (l m : Pattern) (label : O → Pattern) (C : Configuration Pattern O) (d : O) :
    Prop where
  present : d ∈ C.present
  reads : ∀ σ : PSubst, nameAction.Models σ C.equations →
    ∃ c, NameLaws (psubst σ (label d)) (doneTok (psubst σ l) (psubst σ m) c)
  unique : ∀ o ∈ C.present, MayDoneS l label C o → o = d
  noPend : ∀ o ∈ C.present, ¬ MayPendS l label C o

/-- **A source step at `l` (solution-wise)**: `commChild` or `closeChild` whose `locL` reads as `l`
at some solution of the firing's information. -/
def StepAtS (l : Pattern) (label : O → Pattern) (C : Configuration Pattern O)
    (g : Firing O QNE located PUnit.unit) : Prop :=
  (g.rule = commChild ∨ g.rule = closeChild) ∧
    ∃ σ : PSubst, nameAction.Models σ (g.information QN (embed label C)) ∧
      NameLaws (psubst σ (psubst g.opening locL)) (psubst σ l)

/-- **A close of `l` (solution-wise)**: `closeRoot` or `closeChild` whose closed child reads as `l`
at some solution of the firing's information. -/
def CloseAtS (l : Pattern) (label : O → Pattern) (C : Configuration Pattern O)
    (g : Firing O QNE located PUnit.unit) : Prop :=
  (g.rule = closeRoot ∧ ∃ σ : PSubst, nameAction.Models σ (g.information QN (embed label C)) ∧
      NameLaws (psubst σ (psubst g.opening (childLoc rootLoc channelUnknown reflP))) (psubst σ l)) ∨
    (g.rule = closeChild ∧ ∃ σ : PSubst, nameAction.Models σ (g.information QN (embed label C)) ∧
      NameLaws (psubst σ (psubst g.opening (childLoc locL channelUnknown reflP))) (psubst σ l))

omit [DecidableEq O] in
/-- On ground locations `PendingPhaseS` agrees with `ReflLocatedStep.PendingPhase`. -/
theorem pendingPhaseS_iff_ground {l m : Pattern} (groundL : pvars l = []) (groundM : pvars m = [])
    {label : O → Pattern} {C : Configuration Pattern O} {q : O} :
    PendingPhaseS l m label C q ↔ PendingPhase l m label C q := by
  have groundTok : pvars (pendingTok l m) = [] := by
    simp [pendingTok, pvars, pvars.pvarsList, groundL, groundM]
  constructor
  · intro phase
    refine ⟨phase.present, fun σ solved => ?_, fun o inside ⟨σ, solved, m', same⟩ => ?_,
      fun o inside ⟨σ, solved, m', c, same⟩ => ?_⟩
    · have read := phase.reads σ solved
      rw [psubst_of_pvars_nil σ _ groundTok] at read
      exact read
    · exact phase.unique o inside ⟨σ, solved, m', by rw [psubst_of_pvars_nil σ l groundL]; exact same⟩
    · exact phase.noDone o inside ⟨σ, solved, m', c, by rw [psubst_of_pvars_nil σ l groundL]; exact same⟩
  · intro phase
    refine ⟨phase.present, fun σ solved => ?_, fun o inside ⟨σ, solved, m', same⟩ => ?_,
      fun o inside ⟨σ, solved, m', c, same⟩ => ?_⟩
    · rw [psubst_of_pvars_nil σ _ groundTok]
      exact phase.reads σ solved
    · rw [psubst_of_pvars_nil σ l groundL] at same
      exact phase.unique o inside ⟨σ, solved, m', same⟩
    · rw [psubst_of_pvars_nil σ l groundL] at same
      exact phase.noDone o inside ⟨σ, solved, m', c, same⟩

omit [DecidableEq O] in
theorem donePhase_of_donePhaseS_ground {l m : Pattern} (groundL : pvars l = []) (groundM : pvars m = [])
    {label : O → Pattern} {C : Configuration Pattern O} {d : O}
    (phase : DonePhaseS l m label C d) : DonePhase l m label C d := by
  refine ⟨phase.present, fun σ solved => ?_, fun o inside ⟨σ, solved, m', same⟩ => ?_⟩
  · obtain ⟨c, read⟩ := phase.reads σ solved
    rw [psubst_of_pvars_nil σ l groundL, psubst_of_pvars_nil σ m groundM] at read
    exact ⟨c, read⟩
  · exact phase.noPend o inside ⟨σ, solved, m', by rw [psubst_of_pvars_nil σ l groundL]; exact same⟩

end Phases

/-! ## Token readings and one-firing transitions -/

section Transitions

variable {O : Type*} [DecidableEq O] {m x p : Pattern} {label : O → Pattern}
  {C : Configuration Pattern O}

theorem pending_reading_S {σ ρ : PSubst} {a b l m' : Pattern}
    (same : NameLaws (psubst σ (psubst ρ (pendingTok a b))) (pendingTok l m')) :
    NameLaws (psubst σ (psubst ρ a)) l ∧ NameLaws (psubst σ (psubst ρ b)) m' :=
  ReflLocatedStep.pending_reading same

theorem done_reading_S {σ ρ : PSubst} {a b c l m' c' : Pattern}
    (same : NameLaws (psubst σ (psubst ρ (doneTok a b c))) (doneTok l m' c')) :
    NameLaws (psubst σ (psubst ρ a)) l ∧ NameLaws (psubst σ (psubst ρ b)) m' ∧
      NameLaws (psubst σ (psubst ρ c)) c' :=
  ReflLocatedStep.done_reading same

/-- In the first phase no made row may read as a `Pending` token of `l`. -/
theorem made_not_pending_first_S {q : O} (phase : PendingPhaseS (childLoc m x p) m label C q)
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    {o : O} (made : o ∈ g.selection.made) {σ : PSubst}
    (solved : nameAction.Models σ (g.information QN (embed label C))) (m' : Pattern) :
    ¬ NameLaws (psubst σ ((res label C g).label o)) (pendingTok (psubst σ (childLoc m x p)) m') := by
  intro same
  obtain ⟨t, inside, labelEq⟩ := made_label admitted made
  rw [labelEq, psubst_childLoc] at same
  have qRead : NameLaws (psubst σ (label q))
      (pendingTok (childLoc (psubst σ m) (psubst σ x) (psubst σ p)) (psubst σ m)) := by
    have r := phase.reads σ (info_known g solved)
    simpa [psubst_pendingTok, psubst_childLoc] using r
  rcases produce_shapes g.member inside with ⟨args, rfl⟩ | ⟨isOpen, rfl⟩ | ⟨isOpen, rfl⟩ | ⟨-, c₀, rfl⟩
  · exact absurd (head_of_reading₂ same) (by decide)
  · exact check_fails_pending admitted (by rw [isOpen]; exact openRoot_checks.1) solved
      (pending_reading_S same).1 phase.present qRead
  · exact check_fails_pending admitted (by rw [isOpen]; exact openChild_checks.1) solved
      (pending_reading_S same).1 phase.present qRead
  · exact absurd (head_of_reading₂ same) (by decide)

/-- In the second phase no made row may read as a `Pending` token of `l`. -/
theorem made_not_pending_second_S {d : O} (phase : DonePhaseS (childLoc m x p) m label C d)
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    {o : O} (made : o ∈ g.selection.made) {σ : PSubst}
    (solved : nameAction.Models σ (g.information QN (embed label C))) (m' : Pattern) :
    ¬ NameLaws (psubst σ ((res label C g).label o)) (pendingTok (psubst σ (childLoc m x p)) m') := by
  intro same
  obtain ⟨t, inside, labelEq⟩ := made_label admitted made
  rw [labelEq, psubst_childLoc] at same
  obtain ⟨c, token⟩ := phase.reads σ (info_known g solved)
  rw [psubst_childLoc] at token
  rcases produce_shapes g.member inside with ⟨args, rfl⟩ | ⟨isOpen, rfl⟩ | ⟨isOpen, rfl⟩ | ⟨-, c₀, rfl⟩
  · exact absurd (head_of_reading₂ same) (by decide)
  · exact check_fails_done admitted (by rw [isOpen]; exact openRoot_checks.2) (by rw [isOpen]; rfl)
      (by rw [isOpen]; rfl) (by rw [isOpen]; decide) (by decide) solved
      (pending_reading_S same).1 phase.present token
  · exact check_fails_done admitted (by rw [isOpen]; exact openChild_checks.2) (by rw [isOpen]; rfl)
      (by rw [isOpen]; rfl) (by rw [isOpen]; decide) (by decide) solved
      (pending_reading_S same).1 phase.present token
  · exact absurd (head_of_reading₂ same) (by decide)

/-- In the first phase, a firing that is not a source step at `l` makes no `Done` token of `l`. -/
theorem made_not_done_first_S {q : O} (phase : PendingPhaseS (childLoc m x p) m label C q)
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (notStep : ¬ StepAtS (childLoc m x p) label C g) {o : O} (made : o ∈ g.selection.made)
    {σ : PSubst} (solved : nameAction.Models σ (g.information QN (embed label C)))
    (m' c : Pattern) :
    ¬ NameLaws (psubst σ ((res label C g).label o)) (doneTok (psubst σ (childLoc m x p)) m' c) := by
  intro same
  obtain ⟨t, inside, labelEq⟩ := made_label admitted made
  rw [labelEq] at same
  rcases produce_shapes g.member inside with ⟨args, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨rule, c₀, rfl⟩
  · exact absurd (head_of_reading₂ same) (by decide)
  · exact absurd (head_of_reading₂ same) (by decide)
  · exact absurd (head_of_reading₂ same) (by decide)
  · have loc := (done_reading_S same).1
    rcases rule with isComm | isCool | isClose
    · exact notStep ⟨.inl isComm, σ, solved, loc⟩
    · obtain ⟨o₁, zipped, present₁⟩ := taken_row admitted (t := doneTok locL locM accC)
        (by rw [isCool]; simp [cool])
      have read := take_reads g solved zipped
      rw [psubst_doneTok, psubst_doneTok] at read
      exact phase.noDone o₁ present₁ ⟨σ, info_known g solved, _, _,
        read.symm.trans (nameLaws_doneTok_iff.mpr ⟨loc, NameLaws.refl _, NameLaws.refl _⟩)⟩
    · exact notStep ⟨.inr isClose, σ, solved, loc⟩

/-- In the first phase, a firing that is not a source step at `l` keeps `q`. -/
theorem token_kept_first_S {q : O} (phase : PendingPhaseS (childLoc m x p) m label C q)
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (notStep : ¬ StepAtS (childLoc m x p) label C g) : q ∉ g.selection.taken := by
  intro taken
  obtain ⟨_, shapes, -⟩ := (RuleSyntax.admits_iff g).mp admitted
  obtain ⟨t, zipped⟩ := exists_mem_zip_right shapes.2.2.1 taken
  obtain ⟨σ, solved⟩ := solution_of_admitted admitted
  have qRead := phase.reads σ (info_known g solved)
  rw [psubst_pendingTok] at qRead
  have both := (take_reads g solved zipped).trans qRead
  rcases take_shapes g.member (List.of_mem_zip zipped).1 with ⟨args, rfl⟩ | ⟨rule, rfl⟩ |
    ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact absurd (head_of_reading₂ both) (by decide)
  · exact notStep ⟨rule, σ, solved, (pending_reading_S both).1⟩
  · exact absurd (head_of_reading₂ both) (by decide)
  · exact absurd (head_of_reading₂ both) (by decide)
  · exact absurd (head_of_reading₂ both) (by decide)

/-- **A source step at `l` takes `q`** and equates `(locL, locM)` with `(l, m)` at every solution. -/
theorem step_reads_token_S {q : O} (phase : PendingPhaseS (childLoc m x p) m label C q)
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (step : StepAtS (childLoc m x p) label C g) :
    (pendingTok locL locM, q) ∈ g.rule.body.take.zip g.selection.taken ∧
      ∀ σ : PSubst, nameAction.Models σ (g.information QN (embed label C)) →
        NameLaws (psubst σ (psubst g.opening locL)) (psubst σ (childLoc m x p)) ∧
          NameLaws (psubst σ (psubst g.opening locM)) (psubst σ m) := by
  obtain ⟨rule, σ₀, solved₀, loc₀⟩ := step
  have inside : pendingTok locL locM ∈ g.rule.body.take := by
    rcases rule with isComm | isClose
    · rw [isComm]; simp [commChild]
    · rw [isClose]; simp [closeChild]
  obtain ⟨o₃, zipped, present₃⟩ := taken_row admitted inside
  have read₀ := take_reads g solved₀ zipped
  rw [psubst_pendingTok, psubst_pendingTok] at read₀
  have isQ : o₃ = q := phase.unique o₃ present₃ ⟨σ₀, info_known g solved₀,
    psubst σ₀ (psubst g.opening locM),
    read₀.symm.trans (nameLaws_pendingTok_iff.mpr ⟨loc₀, NameLaws.refl _⟩)⟩
  subst isQ
  refine ⟨zipped, fun σ solved => ?_⟩
  have qRead := phase.reads σ (info_known g solved)
  rw [psubst_pendingTok] at qRead
  exact pending_reading_S ((take_reads g solved zipped).trans qRead)

/-- Helper: if `made.length = produce.length` and `pat` appears at a unique index of `produce`,
two zipped pairs with `pat` on the right have equal left identity. -/
theorem eq_of_mem_zip_unique_right {α β : Type*} {xs : List α} {ys : List β}
    {x₁ x₂ : α} {y : β} (len : xs.length = ys.length)
    (z₁ : (x₁, y) ∈ xs.zip ys) (z₂ : (x₂, y) ∈ xs.zip ys)
    (uniqueIdx : ∀ (i j : ℕ) (hi : i < ys.length) (hj : j < ys.length),
      ys[i] = y → ys[j] = y → i = j) : x₁ = x₂ := by
  rw [List.mem_iff_getElem] at z₁ z₂
  obtain ⟨i, hi, eq₁⟩ := z₁
  obtain ⟨j, hj, eq₂⟩ := z₂
  have hiY : i < ys.length := by rw [List.length_zip, len, Nat.min_self] at hi; exact hi
  have hjY : j < ys.length := by rw [List.length_zip, len, Nat.min_self] at hj; exact hj
  have hiX : i < xs.length := len ▸ hiY
  have hjX : j < xs.length := len ▸ hjY
  rw [List.getElem_zip] at eq₁ eq₂
  obtain ⟨rfl, yi⟩ := Prod.mk.inj eq₁
  obtain ⟨rfl, yj⟩ := Prod.mk.inj eq₂
  have ij : i = j := uniqueIdx i j hiY hjY yi yj
  subst ij
  rfl

/-- **From the first phase, one firing (solution-wise)**: every admitted firing either is not a
source step at `l` and keeps `PendingPhaseS`, or is a source step at `l` and enters `DonePhaseS`. -/
theorem pending_phase_step_S {q : O} (phase : PendingPhaseS (childLoc m x p) m label C q)
    (g : Firing O QNE located PUnit.unit)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g) :
    (¬ StepAtS (childLoc m x p) label C g ∧
        PendingPhaseS (childLoc m x p) m (res label C g).label (resConf label C g) q) ∨
      (StepAtS (childLoc m x p) label C g ∧
        ∃ d, DonePhaseS (childLoc m x p) m (res label C g).label (resConf label C g) d) := by
  by_cases step : StepAtS (childLoc m x p) label C g
  · right
    refine ⟨step, ?_⟩
    obtain ⟨tokenTaken, reads⟩ := step_reads_token_S phase admitted step
    obtain ⟨rule, -⟩ := step
    have produceIn : doneTok locL locM pZero ∈ g.rule.body.produce := by
      rcases rule with isComm | isClose
      · rw [isComm]; simp [commChild]
      · rw [isClose]; simp [closeChild]
    obtain ⟨_, shapes, -⟩ := (RuleSyntax.admits_iff g).mp admitted
    obtain ⟨d, zippedMade⟩ := exists_mem_zip_right shapes.2.2.2.2.1.symm produceIn
    have qTaken : q ∈ g.selection.taken := (List.of_mem_zip tokenTaken).2
    refine ⟨d, ⟨(result_present g d).mpr (.inr (List.of_mem_zip zippedMade).1),
      fun σ solved => ?_, ?_, ?_⟩⟩
    · rw [result_label_made admitted zippedMade, psubst_doneTok]
      obtain ⟨loc, parent⟩ := reads σ solved
      exact ⟨_, nameLaws_doneTok_iff.mpr ⟨loc, parent, NameLaws.refl _⟩⟩
    · rintro o present ⟨σ, solved, m', c', same⟩
      rcases result_row present with made | ⟨old, -, -, labelOld⟩
      · obtain ⟨t, zippedO⟩ := exists_mem_zip shapes.2.2.2.2.1.symm made
        rw [result_label_made admitted zippedO] at same
        have tEq : t = doneTok locL locM pZero := by
          rcases rule with isComm | isClose
          · rw [isComm] at zippedO
            simp only [commChild] at zippedO
            have memP := (List.of_mem_zip zippedO).2
            simp only [List.mem_cons, List.not_mem_nil, or_false] at memP
            rcases memP with rfl | rfl | rfl
            · exact absurd (head_of_reading₂ same) (by decide)
            · exact absurd (head_of_reading₂ same) (by decide)
            · rfl
          · rw [isClose] at zippedO
            simp only [closeChild] at zippedO
            have memP := (List.of_mem_zip zippedO).2
            simp only [List.mem_cons, List.not_mem_nil, or_false] at memP
            rcases memP with rfl | rfl
            · exact absurd (head_of_reading₂ same) (by decide)
            · rfl
        subst tEq
        refine eq_of_mem_zip_unique_right shapes.2.2.2.2.1.symm zippedO zippedMade ?_
        rcases rule with isComm | isClose
        · rw [isComm]
          intro i j hi hj yi yj
          simp only [commChild, List.length_cons, List.length_nil] at hi hj
          rcases i with _ | _ | _ | i
          · simp [commChild, atLoc, doneTok] at yi
          · simp [commChild, atLoc, doneTok] at yi
          · rcases j with _ | _ | _ | j
            · simp [commChild, atLoc, doneTok] at yj
            · simp [commChild, atLoc, doneTok] at yj
            · rfl
            · omega
          · omega
        · rw [isClose]
          intro i j hi hj yi yj
          simp only [closeChild, List.length_cons, List.length_nil] at hi hj
          rcases i with _ | _ | i
          · simp [closeChild, atLoc, doneTok] at yi
          · rcases j with _ | _ | j
            · simp [closeChild, atLoc, doneTok] at yj
            · rfl
            · omega
          · omega
      · rw [labelOld] at same
        exact absurd ⟨σ, info_known g solved, m', c', same⟩ (phase.noDone o old)
    · rintro o present ⟨σ, solved, m', same⟩
      rcases result_row present with made | ⟨old, notTaken, -, labelOld⟩
      · exact made_not_pending_first_S phase admitted made solved m' same
      · rw [labelOld] at same
        have isQ := phase.unique o old ⟨σ, info_known g solved, m', same⟩
        subst isQ
        exact notTaken qTaken
  · left
    refine ⟨step, ⟨?_, fun σ solved => ?_, ?_, ?_⟩⟩
    · exact (result_present g q).mpr (.inl ⟨phase.present, token_kept_first_S phase admitted step⟩)
    · rw [result_label_old g (fun made => made_not_present admitted made phase.present)]
      exact phase.reads σ (info_known g solved)
    · rintro o present ⟨σ, solved, m', same⟩
      rcases result_row present with made | ⟨old, -, -, labelOld⟩
      · exact absurd same (made_not_pending_first_S phase admitted made solved m')
      · rw [labelOld] at same
        exact phase.unique o old ⟨σ, info_known g solved, m', same⟩
    · rintro o present ⟨σ, solved, m', c, same⟩
      rcases result_row present with made | ⟨old, -, -, labelOld⟩
      · exact made_not_done_first_S phase admitted step made solved m' c same
      · rw [labelOld] at same
        exact phase.noDone o old ⟨σ, info_known g solved, m', c, same⟩

/-- **From the second phase, one firing (solution-wise)**: every admitted firing that is not a
close of `l` is not a source step at `l` and keeps `DonePhaseS` (uniqueness of `Done` included). -/
theorem done_phase_step_S {d : O} (phase : DonePhaseS (childLoc m x p) m label C d)
    (g : Firing O QNE located PUnit.unit)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (notClose : ¬ CloseAtS (childLoc m x p) label C g) :
    ¬ StepAtS (childLoc m x p) label C g ∧
      ∃ d', DonePhaseS (childLoc m x p) m (res label C g).label (resConf label C g) d' := by
  have noStep : ¬ StepAtS (childLoc m x p) label C g := by
    rintro ⟨rule, σ₀, solved₀, loc₀⟩
    have inside : pendingTok locL locM ∈ g.rule.body.take := by
      rcases rule with isComm | isClose
      · rw [isComm]; simp [commChild]
      · rw [isClose]; simp [closeChild]
    obtain ⟨o₃, zipped, present₃⟩ := taken_row admitted inside
    have read₀ := take_reads g solved₀ zipped
    rw [psubst_pendingTok, psubst_pendingTok] at read₀
    exact phase.noPend o₃ present₃ ⟨σ₀, info_known g solved₀, psubst σ₀ (psubst g.opening locM),
      read₀.symm.trans (nameLaws_pendingTok_iff.mpr ⟨loc₀, NameLaws.refl _⟩)⟩
  have noPend : ∀ o ∈ (resConf label C g).present,
      ¬ MayPendS (childLoc m x p) (res label C g).label (resConf label C g) o := by
    rintro o present ⟨σ, solved, m', same⟩
    rcases result_row present with made | ⟨old, -, -, labelOld⟩
    · exact made_not_pending_second_S phase admitted made solved m' same
    · rw [labelOld] at same
      exact phase.noPend o old ⟨σ, info_known g solved, m', same⟩
  refine ⟨noStep, ?_⟩
  obtain ⟨_, shapes, -⟩ := (RuleSyntax.admits_iff g).mp admitted
  by_cases taken : d ∈ g.selection.taken
  · obtain ⟨t, zipped⟩ := exists_mem_zip_right shapes.2.2.1 taken
    obtain ⟨σ₀, solved₀⟩ := solution_of_admitted admitted
    obtain ⟨c₀, token₀⟩ := phase.reads σ₀ (info_known g solved₀)
    have both₀ := (take_reads g solved₀ zipped).trans token₀
    rcases take_shapes g.member (List.of_mem_zip zipped).1 with ⟨args, rfl⟩ | ⟨-, rfl⟩ |
      ⟨isCool, rfl⟩ | ⟨isRoot, rfl⟩ | ⟨isChild, rfl⟩
    · exact absurd (head_of_reading₂ both₀) (by decide)
    · exact absurd (head_of_reading₂ both₀) (by decide)
    · have produceIn : doneTok locL locM (par accC leftPart) ∈ g.rule.body.produce := by
        rw [isCool]; simp [cool]
      obtain ⟨d₁, zippedMade⟩ := exists_mem_zip_right shapes.2.2.2.2.1.symm produceIn
      refine ⟨d₁, ⟨(result_present g d₁).mpr (.inr (List.of_mem_zip zippedMade).1),
        fun σ solved => ?_, ?_, noPend⟩⟩
      · rw [result_label_made admitted zippedMade, psubst_doneTok, psubst_doneTok]
        obtain ⟨c, token⟩ := phase.reads σ (info_known g solved)
        obtain ⟨loc, parent, -⟩ := done_reading_S ((take_reads g solved zipped).trans token)
        exact ⟨_, nameLaws_doneTok_iff.mpr ⟨loc, parent, NameLaws.refl _⟩⟩
      · rintro o present ⟨σ, solved, m', c', same⟩
        rcases result_row present with made | ⟨old, notTaken, -, labelOld⟩
        · have lenOne : g.selection.made.length = 1 := by
            rw [shapes.2.2.2.2.1.symm, isCool]; rfl
          match hMade : g.selection.made, lenOne with
          | [onlyD], _ =>
              have oEq : o = onlyD := by rw [hMade, List.mem_singleton] at made; exact made
              have d₁Eq : d₁ = onlyD := by
                have inM := (List.of_mem_zip zippedMade).1
                rw [hMade, List.mem_singleton] at inM
                exact inM
              exact oEq.trans d₁Eq.symm
        · rw [labelOld] at same
          have isD := phase.unique o old ⟨σ, info_known g solved, m', c', same⟩
          subst isD
          exact absurd taken notTaken
    · exact absurd (.inl ⟨isRoot, σ₀, solved₀, (done_reading_S both₀).1⟩) notClose
    · exact absurd (.inr ⟨isChild, σ₀, solved₀, (done_reading_S both₀).1⟩) notClose
  · refine ⟨d, ⟨(result_present g d).mpr (.inl ⟨phase.present, taken⟩), fun σ solved => ?_,
      ?_, noPend⟩⟩
    · rw [result_label_old g (fun made => made_not_present admitted made phase.present)]
      exact phase.reads σ (info_known g solved)
    · rintro o present ⟨σ, solved, m', c', same⟩
      rcases result_row present with made | ⟨old, -, -, labelOld⟩
      · obtain ⟨t, inside, labelEq⟩ := made_label admitted made
        rw [labelEq] at same
        rcases produce_shapes g.member inside with ⟨args, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ |
          ⟨rule, c₀, rfl⟩
        · exact absurd (head_of_reading₂ same) (by decide)
        · exact absurd (head_of_reading₂ same) (by decide)
        · exact absurd (head_of_reading₂ same) (by decide)
        · have loc := (done_reading_S same).1
          rcases rule with isComm | isCool | isClose
          · exact absurd ⟨.inl isComm, σ, solved, loc⟩ noStep
          · obtain ⟨o₁, zipped₁, present₁⟩ := taken_row admitted (t := doneTok locL locM accC)
              (by rw [isCool]; simp [cool])
            have read₁ := take_reads g solved zipped₁
            rw [psubst_doneTok, psubst_doneTok] at read₁
            have isD := phase.unique o₁ present₁ ⟨σ, info_known g solved, _, _,
              read₁.symm.trans (nameLaws_doneTok_iff.mpr ⟨loc, NameLaws.refl _, NameLaws.refl _⟩)⟩
            subst isD
            exact absurd (List.of_mem_zip zipped₁).2 taken
          · exact absurd ⟨.inr isClose, σ, solved, loc⟩ noStep
      · rw [labelOld] at same
        exact phase.unique o old ⟨σ, info_known g solved, m', c', same⟩

/-- **No close before the step (solution-wise)**: in `PendingPhaseS`, every `CloseAtS` is refused. -/
theorem close_refused_before_step_S {q : O} (phase : PendingPhaseS (childLoc m x p) m label C q)
    (g : Firing O QNE located PUnit.unit) (close : CloseAtS (childLoc m x p) label C g) :
    ¬ (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g := by
  intro admitted
  rcases close with ⟨isRoot, σ₀, solved₀, child₀⟩ | ⟨isChild, σ₀, solved₀, child₀⟩
  · obtain ⟨o₂, zipped, present₂⟩ := taken_row admitted
      (t := doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC)
      (by rw [isRoot]; simp [closeRoot])
    have read := take_reads g solved₀ zipped
    rw [psubst_doneTok, psubst_doneTok] at read
    exact phase.noDone o₂ present₂ ⟨σ₀, info_known g solved₀, _, _,
      read.symm.trans (nameLaws_doneTok_iff.mpr ⟨child₀, NameLaws.refl _, NameLaws.refl _⟩)⟩
  · obtain ⟨o₂, zipped, present₂⟩ := taken_row admitted
      (t := doneTok (childLoc locL channelUnknown reflP) locL accC)
      (by rw [isChild]; simp [closeChild])
    have read := take_reads g solved₀ zipped
    rw [psubst_doneTok, psubst_doneTok] at read
    exact phase.noDone o₂ present₂ ⟨σ₀, info_known g solved₀, _, _,
      read.symm.trans (nameLaws_doneTok_iff.mpr ⟨child₀, NameLaws.refl _, NameLaws.refl _⟩)⟩

end Transitions

/-! ## Runs of a non-ground child location -/

section Runs

variable {O : Type*} [DecidableEq O]

/-- **A run of `located` in which `l` is not closed (solution-wise)**, counting source steps at `l`. -/
inductive ChildRunS (l : Pattern) :
    (O → Pattern) → Configuration Pattern O → (O → Pattern) → Configuration Pattern O → ℕ → Prop where
  | refl (label : O → Pattern) (C : Configuration Pattern O) : ChildRunS l label C label C 0
  | source {label : O → Pattern} {C : Configuration Pattern O} {label' : O → Pattern}
      {C' : Configuration Pattern O} {n : ℕ} (g : Firing O QNE located PUnit.unit)
      (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
      (notClose : ¬ CloseAtS l label C g) (isStep : StepAtS l label C g)
      (rest : ChildRunS l (res label C g).label (resConf label C g) label' C' n) :
      ChildRunS l label C label' C' (n + 1)
  | other {label : O → Pattern} {C : Configuration Pattern O} {label' : O → Pattern}
      {C' : Configuration Pattern O} {n : ℕ} (g : Firing O QNE located PUnit.unit)
      (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
      (notClose : ¬ CloseAtS l label C g) (notStep : ¬ StepAtS l label C g)
      (rest : ChildRunS l (res label C g).label (resConf label C g) label' C' n) :
      ChildRunS l label C label' C' n

theorem done_run_S {m x p : Pattern} {label label' : O → Pattern} {C C' : Configuration Pattern O}
    {n : ℕ} (run : ChildRunS (childLoc m x p) label C label' C' n) :
    ∀ {d : O}, DonePhaseS (childLoc m x p) m label C d →
      n = 0 ∧ ∃ d', DonePhaseS (childLoc m x p) m label' C' d' := by
  induction run with
  | refl label C => exact fun phase => ⟨rfl, _, phase⟩
  | source g admitted notClose isStep _ _ =>
      intro d phase
      exact absurd isStep (done_phase_step_S phase g admitted notClose).1
  | other g admitted notClose _ _ ih =>
      intro d phase
      obtain ⟨d', phase'⟩ := (done_phase_step_S phase g admitted notClose).2
      exact ih phase'

theorem pending_run_S {m x p : Pattern} {label label' : O → Pattern} {C C' : Configuration Pattern O}
    {n : ℕ} (run : ChildRunS (childLoc m x p) label C label' C' n) :
    ∀ {q : O}, PendingPhaseS (childLoc m x p) m label C q →
      (n = 0 ∧ ∃ q', PendingPhaseS (childLoc m x p) m label' C' q') ∨
        (n = 1 ∧ ∃ d, DonePhaseS (childLoc m x p) m label' C' d) := by
  induction run with
  | refl label C => exact fun phase => .inl ⟨rfl, _, phase⟩
  | source g admitted _ isStep rest _ =>
      intro q phase
      rcases pending_phase_step_S phase g admitted with ⟨notStep, -⟩ | ⟨-, d, phase'⟩
      · exact absurd isStep notStep
      · obtain ⟨zero, d', phase''⟩ := done_run_S rest phase'
        exact .inr ⟨by omega, d', phase''⟩
  | other g admitted _ notStep _ ih =>
      intro q phase
      rcases pending_phase_step_S phase g admitted with ⟨-, phase'⟩ | ⟨isStep, -⟩
      · exact ih phase'
      · exact absurd isStep notStep

/-- **At most one source step at `l` (solution-wise)**, for any (possibly non-ground) `m`, `x`, `p`. -/
theorem at_most_one_step_S {m x p : Pattern} {label label' : O → Pattern}
    {C C' : Configuration Pattern O} {n : ℕ} {q : O}
    (phase : PendingPhaseS (childLoc m x p) m label C q)
    (run : ChildRunS (childLoc m x p) label C label' C' n) : n ≤ 1 := by
  rcases pending_run_S run phase with ⟨zero, -⟩ | ⟨one, -⟩ <;> omega

/-- **Exactly one source step before the close (solution-wise)**, for any `m`, `x`, `p`. -/
theorem exactly_one_before_close_S {m x p : Pattern} {label label' : O → Pattern}
    {C C' : Configuration Pattern O} {n : ℕ} {q : O}
    (phase : PendingPhaseS (childLoc m x p) m label C q)
    (run : ChildRunS (childLoc m x p) label C label' C' n)
    (g : Firing O QNE located PUnit.unit)
    (close : CloseAtS (childLoc m x p) label' C' g)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label' C') g) : n = 1 := by
  rcases pending_run_S run phase with ⟨-, _, phase'⟩ | ⟨one, -⟩
  · exact absurd admitted (close_refused_before_step_S phase' g close)
  · exact one

end Runs

/-! ## Progress without groundness, and the three-state epoch cycle -/

section Epoch

variable {O : Type*} [DecidableEq O]

/-- **The child steps once by COMM without any groundness side condition.** -/
theorem child_steps_once_S {m x p : Pattern} (label : O → Pattern) (C : Configuration Pattern O)
    {q : O} (phase : PendingPhaseS (childLoc m x p) m label C q) (t u channel K₁ K₂ : Pattern)
    (first second made₁ made₂ madeTok : O)
    (readsFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (atLoc (pFor t channel K₁) (childLoc m x p))))
    (readsSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (atLoc (pFor u channel K₂) (childLoc m x p))))
    (distinct : [first, second, q].Nodup) (madeDistinct : [made₁, made₂, madeTok].Nodup)
    (present : first ∈ C.present ∧ second ∈ C.present)
    (fresh : made₁ ∉ C.present ∧ made₂ ∉ C.present ∧ madeTok ∉ C.present)
    {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations)
    (unifies : NameLaws (psubst σ₀ t) (psubst σ₀ u))
    {ρ : PSubst}
    (opensFreshly : (commChildAt ρ first second q made₁ made₂ madeTok).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
        (commChildAt ρ first second q made₁ made₂ madeTok) ∧
      StepAtS (childLoc m x p) label C (commChildAt ρ first second q made₁ made₂ madeTok) ∧
      ∃ d, DonePhaseS (childLoc m x p) m
        (res label C (commChildAt ρ first second q made₁ made₂ madeTok)).label
        (resConf label C (commChildAt ρ first second q made₁ made₂ madeTok)) d := by
  have admitted := child_comm_admitted label C t u channel K₁ K₂ (childLoc m x p) m
    first second q made₁ made₂ madeTok readsFirst readsSecond phase.reads distinct madeDistinct
    ⟨present.1, present.2, phase.present⟩ fresh known unifies opensFreshly
  obtain ⟨σ, solved⟩ := solution_of_admitted admitted
  have zipped : (pendingTok locL locM, q) ∈
      (commChildAt ρ first second q made₁ made₂ madeTok).rule.body.take.zip
        (commChildAt ρ first second q made₁ made₂ madeTok).selection.taken := by
    simp [commChildAt, commChild]
  have qRead := phase.reads σ (info_known _ solved)
  rw [psubst_pendingTok] at qRead
  have loc := (pending_reading_S ((take_reads _ solved zipped).trans qRead)).1
  have step : StepAtS (childLoc m x p) label C (commChildAt ρ first second q made₁ made₂ madeTok) :=
    ⟨.inl rfl, σ, solved, loc⟩
  rcases pending_phase_step_S phase _ admitted with ⟨notStep, -⟩ | ⟨-, done⟩
  · exact absurd step notStep
  · exact ⟨admitted, step, done⟩

/-- **The child steps once by an inner close without any groundness side condition.** -/
theorem child_closes_once_S {m x p : Pattern} (label : O → Pattern) (C : Configuration Pattern O)
    {q : O} (phase : PendingPhaseS (childLoc m x p) m label C q) (x' p' c : Pattern)
    (reflection innerToken made₁ madeTok : O)
    (readsReflection : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x' p') (childLoc m x p))))
    (readsInner : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label innerToken))
        (psubst σ (doneTok (childLoc (childLoc m x p) x' p') (childLoc m x p) c)))
    (packed : ∀ o ∈ C.present, ∀ σ : PSubst, nameAction.Models σ C.equations → ∀ y : Pattern,
      ¬ NameLaws (psubst σ (label o)) (atLoc y (psubst σ (childLoc (childLoc m x p) x' p'))))
    (distinct : [reflection, innerToken, q].Nodup) (madeDistinct : [made₁, madeTok].Nodup)
    (present : reflection ∈ C.present ∧ innerToken ∈ C.present)
    (fresh : made₁ ∉ C.present ∧ madeTok ∉ C.present)
    {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations)
    {ρ : PSubst}
    (opensFreshly : (closeChildAt ρ reflection innerToken q made₁ madeTok).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
        (closeChildAt ρ reflection innerToken q made₁ madeTok) ∧
      StepAtS (childLoc m x p) label C (closeChildAt ρ reflection innerToken q made₁ madeTok) ∧
      ∃ d, DonePhaseS (childLoc m x p) m
        (res label C (closeChildAt ρ reflection innerToken q made₁ madeTok)).label
        (resConf label C (closeChildAt ρ reflection innerToken q made₁ madeTok)) d := by
  have admitted := child_close_admitted label C x' p' c (childLoc m x p) m
    reflection innerToken q made₁ madeTok readsReflection readsInner phase.reads packed distinct
    madeDistinct ⟨present.1, present.2, phase.present⟩ fresh known opensFreshly
  obtain ⟨σ, solved⟩ := solution_of_admitted admitted
  have zipped : (pendingTok locL locM, q) ∈
      (closeChildAt ρ reflection innerToken q made₁ madeTok).rule.body.take.zip
        (closeChildAt ρ reflection innerToken q made₁ madeTok).selection.taken := by
    simp [closeChildAt, closeChild]
  have qRead := phase.reads σ (info_known _ solved)
  rw [psubst_pendingTok] at qRead
  have loc := (pending_reading_S ((take_reads _ solved zipped).trans qRead)).1
  have step : StepAtS (childLoc m x p) label C (closeChildAt ρ reflection innerToken q made₁ madeTok) :=
    ⟨.inr rfl, σ, solved, loc⟩
  rcases pending_phase_step_S phase _ admitted with ⟨notStep, -⟩ | ⟨-, done⟩
  · exact absurd step notStep
  · exact ⟨admitted, step, done⟩

/-- **An opening at `l`** (`openRoot` or `openChild` whose child reads as `l` at some solution). -/
def OpenAtS (l : Pattern) (label : O → Pattern) (C : Configuration Pattern O)
    (g : Firing O QNE located PUnit.unit) : Prop :=
  (g.rule = openRoot ∧ ∃ σ : PSubst, nameAction.Models σ (g.information QN (embed label C)) ∧
      NameLaws (psubst σ (psubst g.opening (childLoc rootLoc channelUnknown reflP))) (psubst σ l)) ∨
    (g.rule = openChild ∧ ∃ σ : PSubst, nameAction.Models σ (g.information QN (embed label C)) ∧
      NameLaws (psubst σ (psubst g.opening (childLoc locL channelUnknown reflP))) (psubst σ l))

/-- **A clean child location stays clean under every admitted firing except an opening of it.** -/
theorem clean_preserved_unless_open_S {m x p : Pattern} {label : O → Pattern}
    {C : Configuration Pattern O} (clean : Clean (childLoc m x p) label C)
    (g : Firing O QNE located PUnit.unit)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (notOpen : ¬ OpenAtS (childLoc m x p) label C g) :
    Clean (childLoc m x p) (res label C g).label (resConf label C g) := by
  intro o present σ solved
  have known : nameAction.Models σ C.equations := info_known g solved
  rcases result_row present with made | ⟨old, -, -, labelOld⟩
  · obtain ⟨t, inside, labelEq⟩ := made_label admitted made
    refine ⟨fun m' same => ?_, fun m' c' same => ?_, fun y same => ?_⟩
    · rw [labelEq] at same
      rcases produce_shapes g.member inside with ⟨args, rfl⟩ | ⟨isOpen, rfl⟩ | ⟨isOpen, rfl⟩ | ⟨-, _, rfl⟩
      · exact absurd (head_of_reading₂ same) (by decide)
      · exact notOpen (.inl ⟨isOpen, σ, solved, (pending_reading_S same).1⟩)
      · exact notOpen (.inr ⟨isOpen, σ, solved, (pending_reading_S same).1⟩)
      · exact absurd (head_of_reading₂ same) (by decide)
    · rw [labelEq] at same
      rcases produce_shapes g.member inside with ⟨args, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨rule, c₀, rfl⟩
      · exact absurd (head_of_reading₂ same) (by decide)
      · exact absurd (head_of_reading₂ same) (by decide)
      · exact absurd (head_of_reading₂ same) (by decide)
      · have loc := (done_reading_S same).1
        have pendRefute : g.rule = commChild ∨ g.rule = closeChild → False := fun hRule => by
          obtain ⟨o₁, zipped, present₁⟩ := taken_row admitted (t := pendingTok locL locM)
            (by rcases hRule with isC | isC <;> { rw [isC]; simp [commChild, closeChild] })
          have r₁ := take_reads g solved zipped
          rw [psubst_pendingTok, psubst_pendingTok] at r₁
          exact (clean o₁ present₁ σ known).1 _
            (r₁.symm.trans (nameLaws_pendingTok_iff.mpr ⟨loc, NameLaws.refl _⟩))
        rcases rule with isComm | isCool | isClose
        · exact pendRefute (.inl isComm)
        · obtain ⟨o₁, zipped, present₁⟩ := taken_row admitted (t := doneTok locL locM accC)
            (by rw [isCool]; simp [cool])
          have r₁ := take_reads g solved zipped
          rw [psubst_doneTok, psubst_doneTok] at r₁
          exact (clean o₁ present₁ σ known).2.1 _ _
            (r₁.symm.trans (nameLaws_doneTok_iff.mpr ⟨loc, NameLaws.refl _, NameLaws.refl _⟩))
        · exact pendRefute (.inr isClose)
    · rw [labelEq] at same
      have notAtRoot : ∀ body, NameLaws (psubst σ (psubst g.opening (atLoc body rootLoc)))
          (atLoc y (psubst σ (childLoc m x p))) → False := fun body hAt => by
        rw [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at hAt
        exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp hAt).2.symm
      have notAtPend : (g.rule = commChild ∨ g.rule = closeChild) → ∀ body,
          NameLaws (psubst σ (psubst g.opening (atLoc body locL)))
            (atLoc y (psubst σ (childLoc m x p))) → False := fun hRule body hAt => by
        obtain ⟨o₁, zipped, present₁⟩ := taken_row admitted (t := pendingTok locL locM)
          (by rcases hRule with isC | isC <;> { rw [isC]; simp [commChild, closeChild] })
        rw [psubst_atLoc_any] at hAt
        have loc := ((locatedFrame_name.atLoc_iff _ _ _ _).mp hAt).2
        have r₁ := take_reads g solved zipped
        rw [psubst_pendingTok, psubst_pendingTok] at r₁
        exact (clean o₁ present₁ σ known).1 _
          (r₁.symm.trans (nameLaws_pendingTok_iff.mpr ⟨loc, NameLaws.refl _⟩))
      rcases located_cases g.member with isRComm | isRHeat | isRClear | isComm | isHeat | isCool |
        isCloseR | isCloseC | isOpenR | isOpenC
      · rw [isRComm] at inside
        simp only [atRule, RuleInstance.map, commRule, List.map_cons, List.map_nil, List.mem_cons,
          List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl <;> exact notAtRoot _ same
      · rw [isRHeat] at inside
        simp only [atRule, RuleInstance.map, heatRule, List.map_cons, List.map_nil, List.mem_cons,
          List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl <;> exact notAtRoot _ same
      · rw [isRClear] at inside
        simp [atRule, RuleInstance.map, clearRule] at inside
      · rw [isComm] at inside
        simp only [commChild, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl
        · exact notAtPend (.inl isComm) _ same
        · exact notAtPend (.inl isComm) _ same
        · exact absurd (head_of_reading₂ same) (by decide)
      · have readIn : pendingTok locL locM ∈ g.rule.body.read := by rw [isHeat]; simp [heatChild]
        obtain ⟨_, shapes, enabled, -⟩ := (RuleSyntax.admits_iff g).mp admitted
        obtain ⟨o₁, zipped⟩ := exists_mem_zip shapes.2.2.2.1 readIn
        have present₁ : o₁ ∈ C.present :=
          enabled.kept_subset (by simpa [Selection.commit] using (List.of_mem_zip zipped).2)
        rw [isHeat] at inside
        simp only [heatChild, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl <;>
          { rw [psubst_atLoc_any] at same
            have loc := ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2
            have r₁ := read_reads g solved zipped
            rw [psubst_pendingTok, psubst_pendingTok] at r₁
            exact (clean o₁ present₁ σ known).1 _
              (r₁.symm.trans (nameLaws_pendingTok_iff.mpr ⟨loc, NameLaws.refl _⟩)) }
      · rw [isCool] at inside
        simp only [cool, List.mem_singleton] at inside
        subst inside
        exact absurd (head_of_reading₂ same) (by decide)
      · rw [isCloseR] at inside
        simp only [closeRoot, List.mem_singleton] at inside
        subst inside
        exact notAtRoot _ same
      · rw [isCloseC] at inside
        simp only [closeChild, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl
        · exact notAtPend (.inr isCloseC) _ same
        · exact absurd (head_of_reading₂ same) (by decide)
      · rw [isOpenR] at inside
        simp only [openRoot, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl
        · rw [psubst_atLoc_any, psubst_atLoc_any] at same
          exact notOpen (.inl ⟨isOpenR, σ, solved, ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2⟩)
        · exact absurd (head_of_reading₂ same) (by decide)
      · rw [isOpenC] at inside
        simp only [openChild, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl
        · rw [psubst_atLoc_any, psubst_atLoc_any] at same
          exact notOpen (.inr ⟨isOpenC, σ, solved, ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2⟩)
        · exact absurd (head_of_reading₂ same) (by decide)
  · rw [labelOld]
    exact clean o old σ known

/-- **Opening at the root enters `PendingPhaseS`** for any (possibly non-ground) `x` and `p`. -/
theorem openRoot_enters_pending_S (label : O → Pattern) (C : Configuration Pattern O)
    (x p : Pattern) (reflection pr tk : O) (ρ : PSubst)
    (readsReflection : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) rootLoc)))
    (clean : Clean (childLoc rootLoc x p) label C)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (openRootAt ρ reflection pr tk)) :
    PendingPhaseS (childLoc rootLoc x p) rootLoc
      (res label C (openRootAt ρ reflection pr tk)).label
      (resConf label C (openRootAt ρ reflection pr tk)) tk := by
  obtain ⟨_, shapes, enabled, _, _, _⟩ := (RuleSyntax.admits_iff _).mp admitted
  have prTk : pr ≠ tk := by simpa [openRootAt] using shapes.2.1
  have freshPr : pr ∉ C.present := fun inside =>
    Finset.disjoint_left.mp enabled.fresh (by simp [openRootAt, Selection.commit]) inside
  refine ⟨(ReflCorrespondence.open_present label C ρ reflection pr tk tk).mpr (.inr (.inr rfl)),
    fun σ solved => (openRoot_reads label C x p reflection pr tk ρ readsReflection prTk solved).2.2,
    ?_, ?_⟩
  · rintro o present ⟨σ, solved, m', same⟩
    rcases (ReflCorrespondence.open_present label C ρ reflection pr tk o).mp present with
      inC | isPr | isTk
    · by_cases eqTk : o = tk
      · exact eqTk
      · have nePr : o ≠ pr := fun e => freshPr (e ▸ inC)
        rw [ReflCorrespondence.open_label_old label C ρ reflection pr tk nePr eqTk] at same
        exact absurd same ((clean o inC σ (info_known _ solved)).1 m')
    · subst isPr
      have prRead := (openRoot_reads label C x p reflection o tk ρ readsReflection prTk solved).2.1
      have both := same.symm.trans prRead
      rw [psubst_atLoc_any] at both
      exact absurd (nameLaws_heads both.symm) (by decide)
    · exact isTk
  · rintro o present ⟨σ, solved, m', c, same⟩
    rcases (ReflCorrespondence.open_present label C ρ reflection pr tk o).mp present with
      inC | isPr | isTk
    · have nePr : o ≠ pr := fun e => freshPr (e ▸ inC)
      have neTk : o ≠ tk := by
        intro eqTk
        subst eqTk
        have tkRead := (openRoot_reads label C x p reflection pr o ρ readsReflection prTk solved).2.2
        have both := same.symm.trans tkRead
        rw [psubst_pendingTok] at both
        exact absurd (nameLaws_heads both) (by decide)
      rw [ReflCorrespondence.open_label_old label C ρ reflection pr tk nePr neTk] at same
      exact (clean o inC σ (info_known _ solved)).2.1 m' c same
    · subst isPr
      have prRead := (openRoot_reads label C x p reflection o tk ρ readsReflection prTk solved).2.1
      have both := same.symm.trans prRead
      rw [psubst_atLoc_any] at both
      exact absurd (nameLaws_heads both) (by decide)
    · subst isTk
      have tkRead := (openRoot_reads label C x p reflection pr o ρ readsReflection prTk solved).2.2
      have both := same.symm.trans tkRead
      rw [psubst_pendingTok] at both
      exact absurd (nameLaws_heads both) (by decide)

/-- **Closing a child in `DonePhaseS` returns it to `Clean`**, completing the three-state epoch. -/
theorem close_returns_to_clean_S {m x p : Pattern} {label : O → Pattern}
    {C : Configuration Pattern O} {d : O} (phase : DonePhaseS (childLoc m x p) m label C d)
    (g : Firing O QNE located PUnit.unit)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (close : CloseAtS (childLoc m x p) label C g) :
    d ∈ g.selection.taken ∧
      Clean (childLoc m x p) (res label C g).label (resConf label C g) := by
  -- First unify the taken `Done` token with `d` so `d ∈ g.selection.taken` and at EVERY solution
  -- `σ` of `g.information`, the closed child pattern reads as `psubst σ (childLoc m x p)`.
  have dSpec : d ∈ g.selection.taken ∧
      ((g.rule = closeRoot ∧ ∀ σ : PSubst, nameAction.Models σ (g.information QN (embed label C)) →
          NameLaws (psubst σ (psubst g.opening (childLoc rootLoc channelUnknown reflP)))
            (psubst σ (childLoc m x p))) ∨
       (g.rule = closeChild ∧ ∀ σ : PSubst, nameAction.Models σ (g.information QN (embed label C)) →
          NameLaws (psubst σ (psubst g.opening (childLoc locL channelUnknown reflP)))
            (psubst σ (childLoc m x p)))) := by
    rcases close with ⟨isRoot, σ₀, solved₀, child₀⟩ | ⟨isChild, σ₀, solved₀, child₀⟩
    · obtain ⟨o₂, zipped, present₂⟩ := taken_row admitted
        (t := doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC)
        (by rw [isRoot]; simp [closeRoot])
      have read₀ := take_reads g solved₀ zipped
      rw [psubst_doneTok, psubst_doneTok] at read₀
      have isD := phase.unique o₂ present₂ ⟨σ₀, info_known g solved₀, _, _,
        read₀.symm.trans (nameLaws_doneTok_iff.mpr ⟨child₀, NameLaws.refl _, NameLaws.refl _⟩)⟩
      subst isD
      refine ⟨(List.of_mem_zip zipped).2, .inl ⟨isRoot, fun σ solved => ?_⟩⟩
      obtain ⟨c, tok⟩ := phase.reads σ (info_known g solved)
      exact (done_reading_S ((take_reads g solved zipped).trans tok)).1
    · obtain ⟨o₂, zipped, present₂⟩ := taken_row admitted
        (t := doneTok (childLoc locL channelUnknown reflP) locL accC)
        (by rw [isChild]; simp [closeChild])
      have read₀ := take_reads g solved₀ zipped
      rw [psubst_doneTok, psubst_doneTok] at read₀
      have isD := phase.unique o₂ present₂ ⟨σ₀, info_known g solved₀, _, _,
        read₀.symm.trans (nameLaws_doneTok_iff.mpr ⟨child₀, NameLaws.refl _, NameLaws.refl _⟩)⟩
      subst isD
      refine ⟨(List.of_mem_zip zipped).2, .inr ⟨isChild, fun σ solved => ?_⟩⟩
      obtain ⟨c, tok⟩ := phase.reads σ (info_known g solved)
      exact (done_reading_S ((take_reads g solved zipped).trans tok)).1
  refine ⟨dSpec.1, fun o present σ solved => ?_⟩
  have known : nameAction.Models σ C.equations := info_known g solved
  refine ⟨fun m' same => ?_, fun m' c' same => ?_, fun y same => ?_⟩
  · rcases result_row present with made | ⟨old, -, -, labelOld⟩
    · exact made_not_pending_second_S phase admitted made solved m' same
    · rw [labelOld] at same
      exact phase.noPend o old ⟨σ, known, m', same⟩
  · rcases result_row present with made | ⟨old, notTaken, -, labelOld⟩
    · obtain ⟨t, inside, labelEq⟩ := made_label admitted made
      rw [labelEq] at same
      rcases dSpec.2 with ⟨isRoot, _⟩ | ⟨isChild, childAll⟩
      · rw [isRoot] at inside
        simp only [closeRoot, List.mem_singleton] at inside
        subst inside
        exact absurd (head_of_reading₂ same) (by decide)
      · rw [isChild] at inside
        simp only [closeChild, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl
        · exact absurd (head_of_reading₂ same) (by decide)
        · have parentEq := (done_reading_S same).1
          have childEq := childAll σ solved
          rw [psubst_childLoc, psubst_childLoc] at childEq
          exact not_nameLaws_childLoc_self _ _ _ (childEq.trans parentEq.symm)
    · rw [labelOld] at same
      have isD := phase.unique o old ⟨σ, known, m', c', same⟩
      subst isD
      exact notTaken dSpec.1
  · rcases result_row present with made | ⟨old, -, -, labelOld⟩
    · obtain ⟨t, inside, labelEq⟩ := made_label admitted made
      rw [labelEq] at same
      rcases dSpec.2 with ⟨isRoot, _⟩ | ⟨isChild, childAll⟩
      · rw [isRoot] at inside
        simp only [closeRoot, List.mem_singleton] at inside
        subst inside
        rw [psubst_atLoc_any, psubst_atLoc_any, psubst_rootLoc, psubst_rootLoc,
          psubst_childLoc] at same
        exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2.symm
      · rw [isChild] at inside
        simp only [closeChild, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl
        · rw [psubst_atLoc_any, psubst_atLoc_any] at same
          have parentEq := ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2
          have childEq := childAll σ solved
          rw [psubst_childLoc, psubst_childLoc] at childEq
          exact not_nameLaws_childLoc_self _ _ _ (childEq.trans parentEq.symm)
        · exact absurd (head_of_reading₂ same) (by decide)
    · rw [labelOld] at same
      rcases dSpec.2 with ⟨isRoot, childAll⟩ | ⟨isChild, childAll⟩
      · exact check_fails_row_at admitted (by rw [isRoot]; simp [closeRoot])
          (by rw [isRoot]; rfl) (by rw [isRoot]; decide) (by rw [isRoot]; decide) (by decide)
          solved (childAll σ solved) old same
      · exact check_fails_row_at admitted (by rw [isChild]; simp [closeChild])
          (by rw [isChild]; rfl) (by rw [isChild]; decide) (by rw [isChild]; decide) (by decide)
          solved (childAll σ solved) old same

omit [DecidableEq O] in
/-- **Once a child enters `DonePhaseS`, every child below it is dead** (for any depth). -/
theorem donePhaseS_child_dead {m x p y q : Pattern} {label : O → Pattern}
    {C : Configuration Pattern O} {d : O}
    (solvable : ∃ σ : PSubst, nameAction.Models σ C.equations)
    (phase : DonePhaseS (childLoc m x p) m label C d) :
    ¬ Live label C (childLoc (childLoc m x p) y q) := by
  suffices dead : ∀ l, Live label C l → l ≠ childLoc (childLoc m x p) y q from
    fun live => dead _ live rfl
  intro l live
  cases live with
  | root x' p' =>
      intro same
      have parents := congrArg (fun t : Pattern => match t with
        | .apply _ (a :: _) => a
        | other => other) same
      simp [childLoc, rootLoc] at parents
  | @child m₀ x' p' _ pending =>
      intro same
      have parentEq : m₀ = childLoc m x p := by
        have parents := congrArg (fun t : Pattern => match t with
          | .apply _ (a :: _) => a
          | other => other) same
        simpa [childLoc] using parents
      subst parentEq
      obtain ⟨o, inside, reads⟩ := pending
      obtain ⟨σ, solved⟩ := solvable
      obtain ⟨m', same'⟩ := reads σ solved
      rw [psubst_pendingTok] at same'
      exact phase.noPend o inside ⟨σ, solved, psubst σ m', same'⟩

end Epoch

/-! ## Positive and negative examples on non-ground child locations -/

/-- A non-ground reflected body carrying the bound variable `"y"`: `for(y <- @0) @y`. -/
def nonGroundBody : Pattern := predot (pFor (.fvar "y") demoChan (.fvar "y"))

/-- Its child location at the root: `Child(Root, @0, for(y <- @0) @y)`. -/
def nonGroundLoc : Pattern := childLoc rootLoc demoChan nonGroundBody

/-- **Negative for Step 3's hypothesis**: `nonGroundLoc` is NOT ground (`"y"` occurs in its `pvars`),
so `ReflLocatedStep.pendingOnly_phase` does not apply to it. -/
theorem nonGround_not_ground_example : pvars (pendingTok nonGroundLoc rootLoc) ≠ [] := by
  decide +kernel

/-- **Positive for `PendingPhaseS`**: the state holding `Pending(nonGroundLoc, Root)` inhabits
`PendingPhaseS nonGroundLoc rootLoc` despite `"y"` occurring in `nonGroundLoc`. -/
theorem nonGround_pending_phase_example :
    PendingPhaseS nonGroundLoc rootLoc (ReflLocatedStep.pendingOnly nonGroundLoc rootLoc) ⟨[], {0}⟩ 0 := by
  refine ⟨by simp, fun σ _ => NameLaws.refl _, fun o present _ => by simpa using present, ?_⟩
  rintro o - ⟨σ, -, m', c, same⟩
  simp only [ReflLocatedStep.pendingOnly, psubst_pendingTok] at same
  exact absurd (nameLaws_heads same) (by decide)

/-- **Positive for `DonePhaseS`**: the state holding `Done(nonGroundLoc, Root, 0)` inhabits
`DonePhaseS nonGroundLoc rootLoc`. -/
theorem nonGround_done_phase_example :
    DonePhaseS nonGroundLoc rootLoc (ReflLocatedStep.doneOnly nonGroundLoc rootLoc) ⟨[], {0}⟩ 0 := by
  refine ⟨by simp, fun σ _ => ⟨pZero, ?_⟩, fun o present _ => by simpa using present, ?_⟩
  · simp only [ReflLocatedStep.doneOnly, psubst_doneTok, psubst_pZero]
    exact NameLaws.refl _
  · rintro o - ⟨σ, -, m', same⟩
    simp only [ReflLocatedStep.doneOnly, psubst_doneTok] at same
    exact absurd (nameLaws_heads same) (by decide)

#print axioms locDepth_nameLaws
#print axioms not_nameLaws_childLoc_self
#print axioms not_nameLaws_childLoc_rootLoc
#print axioms check_fails_row_at
#print axioms pending_phase_step_S
#print axioms done_phase_step_S
#print axioms close_refused_before_step_S
#print axioms at_most_one_step_S
#print axioms exactly_one_before_close_S
#print axioms child_steps_once_S
#print axioms child_closes_once_S
#print axioms clean_preserved_unless_open_S
#print axioms openRoot_enters_pending_S
#print axioms close_returns_to_clean_S
#print axioms donePhaseS_child_dead
#print axioms nonGround_not_ground_example
#print axioms nonGround_pending_phase_example
#print axioms nonGround_done_phase_example

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem
