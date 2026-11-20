import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystemInterleaving

/-!
# Child-segment isolation and reflection across arbitrary interleaved runs

`ReflCorrespondenceChild` proves `child_reflects` for runs confined to a single child (`HeatRun`,
one `commChild`, `CoolRun`, `closeRoot`). Building on `ReflSystemPhases` and
`ReflSystemInterleaving`, this module lifts child reflection to **arbitrary runs of the whole
`located` program** at any parent location `m` (`Root` or an outer `Child`):

* **Pre-commit isolation** (`cells_step_or_keep`, `cells_run_reflects`): in `PendingPhaseS`, any
  admitted firing of `located` that is not a source step at `l` either heats one cell of `l`
  (`heat_cell`) or leaves `Cells l m` completely untouched — even when concurrent firings open,
  heat, commit, cool, or close other locations (siblings, `Root`, or speculative grandchildren).
* **Post-commit isolation** (`DoneCells`, `doneCells_step_or_keep`, `doneCells_run_reflects`): in
  `DonePhaseS`, any admitted firing that does not close `l` either cools one cell of `l` into the
  `Done` accumulator or leaves `d`, `acc`, and `cells` completely untouched, preserving
  `par acc (pPar cells)` modulo `BagLaws` at every solution.
* **Interleaved child reflection** (`interleaved_child_reflects`): across any pre-commit
  `ChildRunS`, any admitted `commChild` commit at `l`, any post-commit `ChildRunS`, and any
  admitted `closeRootAt`, the commit is a source `BagComm` on `P`'s heated parts and the made
  listener row reads as the represented reduct's quote modulo `NameLaws`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar tProc pReflect applyDot)
open MeTTaOperationsComm (psubst PSubst pvars psubst_pFor psubst_tProc psubst_pZero GroundPrincipal
  firstOrder)
open MeTTaCalculus.Corrected (Apart)
open FiniteProgram (commRule heatRule clearRule leftPart channelUnknown predot)
open OneFrame (embed)
open ReflQuotient (BagLaws bagCanon groundBags)
open ReflNames (NameLaws nameAction QN QNE nameCanon nameLaws_pFor_iff nameLaws_tProc)
open ReflLocated (atLoc rootLoc childLoc pendingTok doneTok locL locM reflP accC atRule
  located commChild heatChild heatChildN cool closeRoot closeChild openRoot openChild
  exists_mem_zip psubst_rootLoc psubst_atLoc_any psubst_pendingTok locatedFrame_name)
open ReflPacking (psubst_doneTok nameLaws_doneTok_iff coolAt cool_reads)
open ReflLocatedStep (located_cases take_shapes head_of_reading₂ psubst_childLoc
  nameLaws_pendingTok_iff nameLaws_childLoc_iff exists_mem_zip_right res resConf info_known
  take_reads read_reads taken_row solution_of_admitted result_present result_label_old
  made_label made_not_present result_row commChildAt check_fails_done)
open ReflCorrespondence (closeRootAt closeRoot_reads Cells heat_cell child_commit_sound)

section InterleavedReflection

variable {O : Type*} [DecidableEq O]

/-- A firing heats `l` when its rule is `heatChild` and `locL` reads as `l` at some solution. -/
def HeatAtS (l : Pattern) (label : O → Pattern) (C : Configuration Pattern O)
    (g : Firing O QNE located PUnit.unit) : Prop :=
  g.rule = heatChild ∧ ∃ σ : PSubst, nameAction.Models σ (g.information QN (embed label C)) ∧
    NameLaws (psubst σ (psubst g.opening locL)) (psubst σ l)

/-- A firing cools `l` when its rule is `cool` and `locL` reads as `l` at some solution. -/
def CoolAtS (l : Pattern) (label : O → Pattern) (C : Configuration Pattern O)
    (g : Firing O QNE located PUnit.unit) : Prop :=
  g.rule = cool ∧ ∃ σ : PSubst, nameAction.Models σ (g.information QN (embed label C)) ∧
    NameLaws (psubst σ (psubst g.opening locL)) (psubst σ l)

/-- **Pre-commit isolation**: in `PendingPhaseS (childLoc m x p) m`, any admitted firing `g` with
`¬ StepAtS` either heats one cell of `l` (`heat_cell`) or leaves `Cells` completely unchanged. -/
theorem cells_step_or_keep {m x p : Pattern} {label : O → Pattern} {C : Configuration Pattern O}
    {tk : O} {cells : List (O × Pattern)}
    (phase : PendingPhaseS (childLoc m x p) m label C tk)
    (inv : Cells (childLoc m x p) m label C tk cells)
    (g : Firing O QNE located PUnit.unit)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (notStep : ¬ StepAtS (childLoc m x p) label C g) :
    ∃ cells' : List (O × Pattern),
      Cells (childLoc m x p) m (res label C g).label (resConf label C g) tk cells' ∧
      BagLaws (pPar (cells'.map Prod.snd)) (pPar (cells.map Prod.snd)) ∧
      ∀ reflOcc ∈ C.present, reflOcc ≠ tk → reflOcc ∉ cells.map Prod.fst →
        reflOcc ∉ g.selection.taken →
        reflOcc ∈ (resConf label C g).present ∧
          (res label C g).label reflOcc = label reflOcc ∧
          reflOcc ∉ cells'.map Prod.fst := by
  by_cases isHeat : HeatAtS (childLoc m x p) label C g
  · obtain ⟨hRule, σ₀, solved₀, loc₀⟩ := isHeat
    obtain ⟨o, m₁, m₂, gEq⟩ := eq_heatChildN phase admitted hRule solved₀ loc₀
    rw [gEq] at admitted ⊢
    obtain ⟨cells', inv', bag⟩ := heat_cell inv g.opening o m₁ m₂ admitted
    refine ⟨cells', inv', bag, fun reflOcc rIn rTk rNotCell rNotTaken => ?_⟩
    have rIn' : reflOcc ∈ (resConf label C (heatChildN g.opening o tk m₁ m₂)).present :=
      (result_present _ reflOcc).mpr (.inl ⟨rIn, rNotTaken⟩)
    have rNotMade : reflOcc ∉ (heatChildN g.opening o tk m₁ m₂).selection.made :=
      fun inM => made_not_present admitted inM rIn
    have lblEq := result_label_old (label := label) (C := C)
      (heatChildN g.opening o tk m₁ m₂) rNotMade
    refine ⟨rIn', lblEq, fun inCells' => ?_⟩
    obtain ⟨q, qIn', rEq⟩ := List.mem_map.mp inCells'
    obtain ⟨σ₁, sol₁⟩ := solution_of_admitted admitted
    have rowRead := (inv'.rows q qIn').2.2 σ₁ sol₁
    rw [rEq, lblEq, psubst_atLoc_any] at rowRead
    exact inv.others reflOcc rIn rTk rNotCell σ₁ (info_known _ sol₁) _ rowRead
  · have tkNotTaken : tk ∉ g.selection.taken := token_kept_first_S phase admitted notStep
    have tkNotMade : tk ∉ g.selection.made := fun m => made_not_present admitted m inv.token.1
    have cellNotTaken : ∀ q ∈ cells, q.1 ∉ g.selection.taken := by
      intro q qIn taken
      obtain ⟨_, shapes, -⟩ := (RuleSyntax.admits_iff g).mp admitted
      obtain ⟨t, zipped⟩ := exists_mem_zip_right shapes.2.2.1 taken
      obtain ⟨σ₀, solved₀⟩ := solution_of_admitted admitted
      have known₀ := info_known g solved₀
      have both := (take_reads g solved₀ zipped).trans ((inv.rows q qIn).2.2 σ₀ known₀)
      have tMem := (List.of_mem_zip zipped).1
      rcases located_cases g.member with rC | rH | rCl | cC | cH | cCl | clR | clC | opR | opC
      · rw [rC] at tMem
        simp only [atRule, RuleInstance.map, commRule, List.map_cons, List.map_nil,
          List.mem_cons, List.not_mem_nil, or_false] at tMem
        rcases tMem with rfl | rfl <;>
          { simp only [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at both
            exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2.symm }
      · rw [rH] at tMem
        simp only [atRule, RuleInstance.map, heatRule, List.map_cons, List.map_nil,
          List.mem_singleton] at tMem
        subst tMem
        simp only [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at both
        exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2.symm
      · rw [rCl] at tMem
        simp only [atRule, RuleInstance.map, clearRule, List.map_cons, List.map_nil,
          List.mem_singleton] at tMem
        subst tMem
        simp only [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at both
        exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2.symm
      · rw [cC] at tMem
        simp only [commChild, List.mem_cons, List.not_mem_nil, or_false] at tMem
        rcases tMem with rfl | rfl | rfl
        · simp only [psubst_atLoc_any] at both
          exact notStep ⟨.inl cC, σ₀, solved₀, ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2⟩
        · simp only [psubst_atLoc_any] at both
          exact notStep ⟨.inl cC, σ₀, solved₀, ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2⟩
        · simp only [psubst_atLoc_any] at both
          exact absurd (head_of_reading₂ both) (by decide)
      · rw [cH] at tMem
        simp only [heatChild, List.mem_singleton] at tMem
        subst tMem
        simp only [psubst_atLoc_any] at both
        exact isHeat ⟨cH, σ₀, solved₀, ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2⟩
      · rw [cCl] at tMem
        simp only [cool, List.mem_cons, List.not_mem_nil, or_false] at tMem
        rcases tMem with rfl | rfl
        · simp only [psubst_atLoc_any] at both
          exact absurd (head_of_reading₂ both) (by decide)
        · simp only [psubst_atLoc_any] at both
          have loc := ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2
          obtain ⟨o₁, z₁, p₁⟩ := taken_row admitted (t := doneTok locL locM accC)
            (by rw [cCl]; simp [cool])
          have r₁ := take_reads g solved₀ z₁
          rw [psubst_doneTok, psubst_doneTok] at r₁
          exact phase.noDone o₁ p₁ ⟨σ₀, known₀, _, _,
            r₁.symm.trans (nameLaws_doneTok_iff.mpr ⟨loc, NameLaws.refl _, NameLaws.refl _⟩)⟩
      · rw [clR] at tMem
        simp only [closeRoot, List.mem_cons, List.not_mem_nil, or_false] at tMem
        rcases tMem with rfl | rfl
        · simp only [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at both
          exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2.symm
        · simp only [psubst_atLoc_any] at both
          exact absurd (head_of_reading₂ both) (by decide)
      · rw [clC] at tMem
        simp only [closeChild, List.mem_cons, List.not_mem_nil, or_false] at tMem
        rcases tMem with rfl | rfl | rfl
        · simp only [psubst_atLoc_any] at both
          exact notStep ⟨.inr clC, σ₀, solved₀, ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2⟩
        · simp only [psubst_atLoc_any] at both
          exact absurd (head_of_reading₂ both) (by decide)
        · simp only [psubst_atLoc_any] at both
          exact absurd (head_of_reading₂ both) (by decide)
      · rw [opR] at tMem; simp [openRoot] at tMem
      · rw [opC] at tMem; simp [openChild] at tMem
    refine ⟨cells, ⟨⟨(result_present g tk).mpr (.inl ⟨inv.token.1, tkNotTaken⟩), fun σ solved => ?_⟩,
      inv.nodup, fun q qIn => ?_, fun o oPres oTk oNotCell σ solved y same => ?_, inv.heatable⟩,
      BagLaws.refl _, fun reflOcc rIn rTk rNotCell rNotTaken =>
        ⟨(result_present g reflOcc).mpr (.inl ⟨rIn, rNotTaken⟩),
          result_label_old g (fun m => made_not_present admitted m rIn), rNotCell⟩⟩
    · rw [result_label_old g tkNotMade]
      exact inv.token.2 σ (info_known g solved)
    · obtain ⟨qPres, qTk, qReads⟩ := inv.rows q qIn
      refine ⟨(result_present g q.1).mpr (.inl ⟨qPres, cellNotTaken q qIn⟩), qTk, fun σ solved => ?_⟩
      rw [result_label_old g (fun m => made_not_present admitted m qPres)]
      exact qReads σ (info_known g solved)
    · have known := info_known g solved
      rcases result_row oPres with made | ⟨old, -, -, labelOld⟩
      · obtain ⟨t, inside, labelEq⟩ := made_label admitted made
        rw [labelEq] at same
        rcases located_cases g.member with rC | rH | rCl | cC | cH | cCl | clR | clC | opR | opC
        · rw [rC] at inside
          simp only [atRule, RuleInstance.map, commRule, List.map_cons, List.map_nil,
            List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl <;>
            { rw [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at same
              exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2.symm }
        · rw [rH] at inside
          simp only [atRule, RuleInstance.map, heatRule, List.map_cons, List.map_nil,
            List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl <;>
            { rw [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at same
              exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2.symm }
        · rw [rCl] at inside; simp [atRule, RuleInstance.map, clearRule] at inside
        · rw [cC] at inside
          simp only [commChild, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl | rfl
          · rw [psubst_atLoc_any] at same
            exact notStep ⟨.inl cC, σ, solved, ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2⟩
          · rw [psubst_atLoc_any] at same
            exact notStep ⟨.inl cC, σ, solved, ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2⟩
          · exact absurd (head_of_reading₂ same) (by decide)
        · rw [cH] at inside
          simp only [heatChild, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl <;>
            { rw [psubst_atLoc_any] at same
              exact isHeat ⟨cH, σ, solved, ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2⟩ }
        · rw [cCl] at inside
          simp only [cool, List.mem_singleton] at inside
          subst inside
          exact absurd (head_of_reading₂ same) (by decide)
        · rw [clR] at inside
          simp only [closeRoot, List.mem_singleton] at inside
          subst inside
          rw [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at same
          exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2.symm
        · rw [clC] at inside
          simp only [closeChild, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl
          · rw [psubst_atLoc_any] at same
            exact notStep ⟨.inr clC, σ, solved, ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2⟩
          · exact absurd (head_of_reading₂ same) (by decide)
        · rw [opR] at inside
          simp only [openRoot, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl
          · rw [psubst_atLoc_any, psubst_childLoc] at same
            have qRead := phase.reads σ known
            rw [psubst_pendingTok, psubst_childLoc] at qRead
            exact ReflLocatedStep.check_fails_pending admitted
              (by rw [opR]; exact ReflLocatedStep.openRoot_checks.1)
              solved ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2 phase.present qRead
          · exact absurd (head_of_reading₂ same) (by decide)
        · rw [opC] at inside
          simp only [openChild, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl
          · rw [psubst_atLoc_any, psubst_childLoc] at same
            have qRead := phase.reads σ known
            rw [psubst_pendingTok, psubst_childLoc] at qRead
            exact ReflLocatedStep.check_fails_pending admitted
              (by rw [opC]; exact ReflLocatedStep.openChild_checks.1)
              solved ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2 phase.present qRead
          · exact absurd (head_of_reading₂ same) (by decide)
      · rw [labelOld] at same
        exact inv.others o old oTk oNotCell σ known y same

/-- Post-commit cell invariant at `l`: `d` reads `Done(l, m, acc)` and `cells` lists all remaining
rows at `l` (stored directly by their represented patterns `q.2`). -/
structure DoneCells (l m : Pattern) (label : O → Pattern) (C : Configuration Pattern O)
    (d : O) (acc : Pattern) (cells : List (O × Pattern)) : Prop where
  phase : DonePhaseS l m label C d
  readsTok : ∀ σ : PSubst, nameAction.Models σ C.equations →
    NameLaws (psubst σ (label d)) (psubst σ (doneTok l m acc))
  nodup : (cells.map Prod.fst).Nodup
  rows : ∀ q ∈ cells, q.1 ∈ C.present ∧ q.1 ≠ d ∧
    ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label q.1)) (psubst σ (atLoc q.2 l))
  others : ∀ o ∈ C.present, o ≠ d → o ∉ cells.map Prod.fst →
    ∀ σ : PSubst, nameAction.Models σ C.equations →
      ∀ y : Pattern, ¬ NameLaws (psubst σ (label o)) (atLoc y (psubst σ l))

/-- **Post-commit isolation**: in `DoneCells (childLoc m x p) m`, any admitted firing `g` with
`¬ CloseAtS` either cools one cell `(r, a) ∈ cells` into `acc` (`acc' = par acc a`) or leaves
`d`, `acc`, and `cells` completely unchanged; in both cases `par acc' (pPar cells')` equals
`par acc (pPar cells)` modulo `BagLaws` at every solution. -/
theorem doneCells_step_or_keep {m x p : Pattern} {label : O → Pattern}
    {C : Configuration Pattern O} {d : O} {acc : Pattern} {cells : List (O × Pattern)}
    (inv : DoneCells (childLoc m x p) m label C d acc cells)
    (g : Firing O QNE located PUnit.unit)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (notClose : ¬ CloseAtS (childLoc m x p) label C g) :
    ∃ (d' : O) (acc' : Pattern) (cells' : List (O × Pattern)),
      DoneCells (childLoc m x p) m (res label C g).label (resConf label C g) d' acc' cells' ∧
      (∀ σ : PSubst, nameAction.Models σ (resConf label C g).equations →
        BagLaws (psubst σ (par acc' (pPar (cells'.map Prod.snd))))
          (psubst σ (par acc (pPar (cells.map Prod.snd))))) ∧
      ∀ reflOcc ∈ C.present, reflOcc ≠ d → reflOcc ∉ cells.map Prod.fst →
        reflOcc ∉ g.selection.taken →
        reflOcc ∈ (resConf label C g).present ∧
          (res label C g).label reflOcc = label reflOcc ∧
          reflOcc ≠ d' ∧ reflOcc ∉ cells'.map Prod.fst := by
  obtain ⟨noStep, dNext, nextPhase⟩ := done_phase_step_S inv.phase g admitted notClose
  by_cases isCool : CoolAtS (childLoc m x p) label C g
  · obtain ⟨cRule, σ₀, solved₀, loc₀⟩ := isCool
    obtain ⟨r, d₁, gEq⟩ := eq_coolAt inv.phase admitted cRule solved₀ loc₀
    rw [gEq] at admitted solved₀ notClose noStep ⊢
    obtain ⟨_, shapes, enabled, -⟩ := (RuleSyntax.admits_iff _).mp admitted
    have rPres : r ∈ C.present := enabled.taken_subset (by simp [coolAt, Selection.commit])
    have rNeD : r ≠ d := by
      intro same; have nd := shapes.1; simp [coolAt, same] at nd
    have d₁Fresh : d₁ ∉ C.present := fun inC =>
      Finset.disjoint_left.mp enabled.fresh (by simp [coolAt, Selection.commit]) inC
    have zippedR : (atLoc leftPart locL, r) ∈
        (coolAt g.opening d r d₁).rule.body.take.zip (coolAt g.opening d r d₁).selection.taken := by
      simp [coolAt, cool]
    have known₀ := info_known _ solved₀
    have rRead₀ := take_reads (coolAt g.opening d r d₁) solved₀ zippedR
    rw [psubst_atLoc_any] at rRead₀
    have rInCells : r ∈ cells.map Prod.fst := by
      by_contra notCell
      exact inv.others r rPres rNeD notCell σ₀ known₀ _
        (rRead₀.symm.trans ((locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨NameLaws.refl _, loc₀⟩))
    obtain ⟨⟨r', qPart⟩, qIn, qFst⟩ := List.mem_map.mp rInCells
    change r' = r at qFst
    subst qFst
    obtain ⟨pre, post, cellsEq⟩ := List.append_of_mem qIn
    have permCells : cells.Perm ((r', qPart) :: (pre ++ post)) := by
      rw [cellsEq]; exact List.perm_middle
    obtain ⟨rOut, restNodup⟩ := List.nodup_cons.mp ((permCells.map Prod.fst).nodup_iff.mp inv.nodup)
    have restIn : ∀ q ∈ pre ++ post, q ∈ cells := fun q m =>
      permCells.symm.subset (List.mem_cons.mpr (.inr m))
    have restNeR : ∀ q ∈ pre ++ post, q.1 ≠ r' := fun q m eqR =>
      rOut (eqR ▸ List.mem_map.mpr ⟨q, m, rfl⟩)
    obtain ⟨_, phase₁⟩ := done_phase_step_S inv.phase (coolAt g.opening d r' d₁) admitted notClose
    have d₁Reads : ∀ σ : PSubst,
        nameAction.Models σ (resConf label C (coolAt g.opening d r' d₁)).equations →
        NameLaws (psubst σ ((res label C (coolAt g.opening d r' d₁)).label d₁))
          (psubst σ (doneTok (childLoc m x p) m (par acc qPart))) :=
      fun σ solved => cool_reads label C g.opening d r' d₁ (childLoc m x p) m acc qPart
        inv.readsTok (inv.rows (r', qPart) qIn).2.2 solved
    obtain ⟨dPhase, dPhaseSpec⟩ := phase₁
    have d₁Eq : d₁ = dPhase := by
      obtain ⟨σ₁, sol₁⟩ := solution_of_admitted admitted
      exact dPhaseSpec.unique d₁
        ((result_present _ d₁).mpr (.inr (by simp [coolAt])))
        ⟨σ₁, sol₁, _, _, by simpa [psubst_doneTok] using d₁Reads σ₁ sol₁⟩
    subst d₁Eq
    refine ⟨d₁, par acc qPart, pre ++ post,
      ⟨dPhaseSpec, d₁Reads, restNodup, fun q m => ?_, fun o oPres oNeD₁ oNotRest σ solved y same => ?_⟩,
      fun σ solved => ?_, fun reflOcc rIn rNeD rNotCell rNotTaken => ?_⟩
    · obtain ⟨qPres, qNeD, qR⟩ := inv.rows q (restIn q m)
      have qNeD₁ : q.1 ≠ d₁ := fun eqD => d₁Fresh (eqD ▸ qPres)
      refine ⟨(result_present _ q.1).mpr (.inl ⟨qPres, by
        simp [coolAt, qNeD, restNeR q m]⟩), qNeD₁, fun σ solved => ?_⟩
      rw [result_label_old _ (by simp [coolAt, qNeD₁])]
      exact qR σ (info_known _ solved)
    · rcases result_row oPres with made | ⟨old, notTaken, -, labelOld⟩
      · simp [coolAt] at made
        exact absurd made oNeD₁
      · rw [labelOld] at same
        have oNeD : o ≠ d := fun eqD => notTaken (by simp [coolAt, eqD])
        have oNeR : o ≠ r' := fun eqR => notTaken (by simp [coolAt, eqR])
        refine inv.others o old oNeD (fun inC => ?_) σ (info_known _ solved) y same
        obtain ⟨q, inQ, eqO⟩ := List.mem_map.mp inC
        rcases List.mem_cons.mp (permCells.subset inQ) with rfl | inRest
        · exact oNeR eqO.symm
        · exact oNotRest (List.mem_map.mpr ⟨q, inRest, eqO⟩)
    · have assocStep : BagLaws (par (par acc qPart) (pPar ((pre ++ post).map Prod.snd)))
          (par acc (pPar (((r', qPart) :: (pre ++ post)).map Prod.snd))) := by
        let restL := (pre ++ post).map Prod.snd
        have s₁ : BagLaws (pPar [pPar [acc, qPart], pPar restL]) (pPar [acc, qPart, pPar restL]) :=
          BagLaws.of_axiom (.flatten [] [acc, qPart] [pPar restL])
        have s₂ : BagLaws (pPar [acc, qPart, pPar restL]) (pPar (acc :: qPart :: restL)) := by
          simpa using BagLaws.of_axiom (.flatten [acc, qPart] restL [])
        have s₃ : BagLaws (pPar (acc :: qPart :: restL)) (pPar [acc, pPar (qPart :: restL)]) := by
          simpa using (BagLaws.of_axiom (.flatten [acc] (qPart :: restL) [])).symm
        exact s₁.trans (s₂.trans s₃)
      have permStep : BagLaws (par acc (pPar (((r', qPart) :: (pre ++ post)).map Prod.snd)))
          (par acc (pPar (cells.map Prod.snd))) :=
        ReflQuotient.bagLaws_collection _ _ (.cons (BagLaws.refl _)
          (.cons (BagLaws.of_axiom (.perm (permCells.symm.map Prod.snd))) .nil))
      exact ReflQuotient.bagLaws_psubst σ (assocStep.trans permStep)
    · have rNeD₁ : reflOcc ≠ d₁ := fun eqD => d₁Fresh (eqD ▸ rIn)
      refine ⟨(result_present _ reflOcc).mpr (.inl ⟨rIn, rNotTaken⟩),
        result_label_old _ (by simp [coolAt, rNeD₁]), rNeD₁, fun inRest => ?_⟩
      obtain ⟨q, qInR, eqR⟩ := List.mem_map.mp inRest
      exact rNotCell (List.mem_map.mpr ⟨q, restIn q qInR, eqR⟩)
  · have dNotTaken : d ∉ g.selection.taken := by
      intro taken
      obtain ⟨_, shapes, -⟩ := (RuleSyntax.admits_iff g).mp admitted
      obtain ⟨t, zipped⟩ := exists_mem_zip_right shapes.2.2.1 taken
      obtain ⟨σ₀, solved₀⟩ := solution_of_admitted admitted
      have dRead := inv.readsTok σ₀ (info_known g solved₀)
      rw [psubst_doneTok] at dRead
      have both := (take_reads g solved₀ zipped).trans dRead
      rcases take_shapes g.member (List.of_mem_zip zipped).1 with ⟨_, rfl⟩ | ⟨_, rfl⟩ |
        ⟨cRule, rfl⟩ | ⟨clR, rfl⟩ | ⟨clC, rfl⟩
      · exact absurd (head_of_reading₂ both) (by decide)
      · exact absurd (head_of_reading₂ both) (by decide)
      · exact isCool ⟨cRule, σ₀, solved₀, (done_reading_S both).1⟩
      · exact notClose (.inl ⟨clR, σ₀, solved₀, (done_reading_S both).1⟩)
      · exact notClose (.inr ⟨clC, σ₀, solved₀, (done_reading_S both).1⟩)
    have dNotMade : d ∉ g.selection.made := fun m => made_not_present admitted m inv.phase.present
    have dEqNext : d = dNext := by
      obtain ⟨σ₀, sol₀⟩ := solution_of_admitted admitted
      have dInNext : d ∈ (resConf label C g).present :=
        (result_present g d).mpr (.inl ⟨inv.phase.present, dNotTaken⟩)
      have dR : NameLaws (psubst σ₀ ((res label C g).label d))
          (psubst σ₀ (doneTok (childLoc m x p) m acc)) := by
        rw [result_label_old g dNotMade]
        exact inv.readsTok σ₀ (info_known g sol₀)
      exact nextPhase.unique d dInNext ⟨σ₀, sol₀, _, _, by simpa [psubst_doneTok] using dR⟩
    subst dEqNext
    have cellNotTaken : ∀ q ∈ cells, q.1 ∉ g.selection.taken := by
      intro q qIn taken
      obtain ⟨_, shapes, enabled, -⟩ := (RuleSyntax.admits_iff g).mp admitted
      obtain ⟨t, zipped⟩ := exists_mem_zip_right shapes.2.2.1 taken
      obtain ⟨σ₀, solved₀⟩ := solution_of_admitted admitted
      have known₀ := info_known g solved₀
      have both := (take_reads g solved₀ zipped).trans ((inv.rows q qIn).2.2 σ₀ known₀)
      have tMem := (List.of_mem_zip zipped).1
      rcases located_cases g.member with rC | rH | rCl | cC | cH | cCl | clR | clC | opR | opC
      · rw [rC] at tMem
        simp only [atRule, RuleInstance.map, commRule, List.map_cons, List.map_nil,
          List.mem_cons, List.not_mem_nil, or_false] at tMem
        rcases tMem with rfl | rfl <;>
          { simp only [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at both
            exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2.symm }
      · rw [rH] at tMem
        simp only [atRule, RuleInstance.map, heatRule, List.map_cons, List.map_nil,
          List.mem_singleton] at tMem
        subst tMem
        simp only [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at both
        exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2.symm
      · rw [rCl] at tMem
        simp only [atRule, RuleInstance.map, clearRule, List.map_cons, List.map_nil,
          List.mem_singleton] at tMem
        subst tMem
        simp only [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at both
        exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2.symm
      · rw [cC] at tMem
        simp only [commChild, List.mem_cons, List.not_mem_nil, or_false] at tMem
        rcases tMem with rfl | rfl | rfl
        · simp only [psubst_atLoc_any] at both
          exact noStep ⟨.inl cC, σ₀, solved₀, ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2⟩
        · simp only [psubst_atLoc_any] at both
          exact noStep ⟨.inl cC, σ₀, solved₀, ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2⟩
        · simp only [psubst_atLoc_any] at both
          exact absurd (head_of_reading₂ both) (by decide)
      · rw [cH] at tMem
        simp only [heatChild, List.mem_singleton] at tMem
        subst tMem
        simp only [psubst_atLoc_any] at both
        have loc := ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2
        obtain ⟨o₁, z₁⟩ := exists_mem_zip shapes.2.2.2.1 (x := pendingTok locL locM)
          (by rw [cH]; simp [heatChild])
        have p₁ : o₁ ∈ C.present := enabled.kept_subset
          (by simpa [Selection.commit] using (List.of_mem_zip z₁).2)
        have r₁ := read_reads g solved₀ z₁
        rw [psubst_pendingTok] at r₁
        exact inv.phase.noPend o₁ p₁ ⟨σ₀, known₀, _,
          r₁.symm.trans (nameLaws_pendingTok_iff.mpr ⟨loc, NameLaws.refl _⟩)⟩
      · rw [cCl] at tMem
        simp only [cool, List.mem_cons, List.not_mem_nil, or_false] at tMem
        rcases tMem with rfl | rfl
        · simp only [psubst_atLoc_any] at both
          exact absurd (head_of_reading₂ both) (by decide)
        · simp only [psubst_atLoc_any] at both
          exact isCool ⟨cCl, σ₀, solved₀, ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2⟩
      · rw [clR] at tMem
        simp only [closeRoot, List.mem_cons, List.not_mem_nil, or_false] at tMem
        rcases tMem with rfl | rfl
        · simp only [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at both
          exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2.symm
        · simp only [psubst_atLoc_any] at both
          exact absurd (head_of_reading₂ both) (by decide)
      · rw [clC] at tMem
        simp only [closeChild, List.mem_cons, List.not_mem_nil, or_false] at tMem
        rcases tMem with rfl | rfl | rfl
        · simp only [psubst_atLoc_any] at both
          exact noStep ⟨.inr clC, σ₀, solved₀, ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2⟩
        · simp only [psubst_atLoc_any] at both
          exact absurd (head_of_reading₂ both) (by decide)
        · simp only [psubst_atLoc_any] at both
          exact absurd (head_of_reading₂ both) (by decide)
      · rw [opR] at tMem; simp [openRoot] at tMem
      · rw [opC] at tMem; simp [openChild] at tMem
    refine ⟨d, acc, cells,
      ⟨nextPhase, fun σ solved => by
          rw [result_label_old g dNotMade]; exact inv.readsTok σ (info_known g solved),
        inv.nodup, fun q qIn => ?_, fun o oPres oNeD oNotCell σ solved y same => ?_⟩,
      fun _ _ => BagLaws.refl _, fun reflOcc rIn rNeD rNotCell rNotTaken =>
        ⟨(result_present g reflOcc).mpr (.inl ⟨rIn, rNotTaken⟩),
          result_label_old g (fun m => made_not_present admitted m rIn), rNeD, rNotCell⟩⟩
    · obtain ⟨qPres, qNeD, qR⟩ := inv.rows q qIn
      refine ⟨(result_present g q.1).mpr (.inl ⟨qPres, cellNotTaken q qIn⟩), qNeD, fun σ solved => ?_⟩
      rw [result_label_old g (fun m => made_not_present admitted m qPres)]
      exact qR σ (info_known g solved)
    · have known := info_known g solved
      rcases result_row oPres with made | ⟨old, -, -, labelOld⟩
      · obtain ⟨t, inside, labelEq⟩ := made_label admitted made
        rw [labelEq] at same
        obtain ⟨_, shapes, enabled, -⟩ := (RuleSyntax.admits_iff g).mp admitted
        rcases located_cases g.member with rC | rH | rCl | cC | cH | cCl | clR | clC | opR | opC
        · rw [rC] at inside
          simp only [atRule, RuleInstance.map, commRule, List.map_cons, List.map_nil,
            List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl <;>
            { rw [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at same
              exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2.symm }
        · rw [rH] at inside
          simp only [atRule, RuleInstance.map, heatRule, List.map_cons, List.map_nil,
            List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl <;>
            { rw [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at same
              exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2.symm }
        · rw [rCl] at inside; simp [atRule, RuleInstance.map, clearRule] at inside
        · rw [cC] at inside
          simp only [commChild, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl | rfl
          · rw [psubst_atLoc_any] at same
            exact noStep ⟨.inl cC, σ, solved, ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2⟩
          · rw [psubst_atLoc_any] at same
            exact noStep ⟨.inl cC, σ, solved, ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2⟩
          · exact absurd (head_of_reading₂ same) (by decide)
        · rw [cH] at inside
          simp only [heatChild, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl <;>
            { rw [psubst_atLoc_any] at same
              have loc := ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2
              obtain ⟨o₁, z₁⟩ := exists_mem_zip shapes.2.2.2.1 (x := pendingTok locL locM)
                (by rw [cH]; simp [heatChild])
              have p₁ : o₁ ∈ C.present := enabled.kept_subset
                (by simpa [Selection.commit] using (List.of_mem_zip z₁).2)
              have r₁ := read_reads g solved z₁
              rw [psubst_pendingTok] at r₁
              exact inv.phase.noPend o₁ p₁ ⟨σ, known, _,
                r₁.symm.trans (nameLaws_pendingTok_iff.mpr ⟨loc, NameLaws.refl _⟩)⟩ }
        · rw [cCl] at inside
          simp only [cool, List.mem_singleton] at inside
          subst inside
          exact absurd (head_of_reading₂ same) (by decide)
        · rw [clR] at inside
          simp only [closeRoot, List.mem_singleton] at inside
          subst inside
          rw [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at same
          exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2.symm
        · rw [clC] at inside
          simp only [closeChild, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl
          · rw [psubst_atLoc_any] at same
            exact noStep ⟨.inr clC, σ, solved, ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2⟩
          · exact absurd (head_of_reading₂ same) (by decide)
        · rw [opR] at inside
          simp only [openRoot, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl
          · rw [psubst_atLoc_any, psubst_childLoc] at same
            have tok := inv.readsTok σ known
            rw [psubst_doneTok, psubst_childLoc] at tok
            exact check_fails_done admitted (by rw [opR]; exact ReflLocatedStep.openRoot_checks.2)
              (by rw [opR]; rfl) (by rw [opR]; rfl) (by rw [opR]; decide) (by decide) solved
              ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2 inv.phase.present tok
          · exact absurd (head_of_reading₂ same) (by decide)
        · rw [opC] at inside
          simp only [openChild, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl
          · rw [psubst_atLoc_any, psubst_childLoc] at same
            have tok := inv.readsTok σ known
            rw [psubst_doneTok, psubst_childLoc] at tok
            exact check_fails_done admitted (by rw [opC]; exact ReflLocatedStep.openChild_checks.2)
              (by rw [opC]; rfl) (by rw [opC]; rfl) (by rw [opC]; decide) (by decide) solved
              ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2 inv.phase.present tok
          · exact absurd (head_of_reading₂ same) (by decide)
      · rw [labelOld] at same
        exact inv.others o old oNeD oNotCell σ known y same

theorem childRunS_back {l : Pattern} {label label' : O → Pattern}
    {C C' : Configuration Pattern O} {n : ℕ}
    (run : ChildRunS l label C label' C' n) :
    ∀ σ : PSubst, nameAction.Models σ C'.equations → nameAction.Models σ C.equations := by
  induction run with
  | refl => exact fun _ s => s
  | source g _ _ _ _ ih => exact fun σ s => info_known g (ih σ s)
  | other g _ _ _ _ ih => exact fun σ s => info_known g (ih σ s)

/-- Multi-step post-commit run preserving `DoneCells` across arbitrary interleaved non-close firings. -/
theorem doneCells_run_reflects {m x p : Pattern} {label label' : O → Pattern}
    {C C' : Configuration Pattern O} {n : ℕ}
    (run : ChildRunS (childLoc m x p) label C label' C' n) :
    ∀ {d : O} {acc : Pattern} {cells : List (O × Pattern)},
      DoneCells (childLoc m x p) m label C d acc cells →
      ∃ (d' : O) (acc' : Pattern) (cells' : List (O × Pattern)),
        DoneCells (childLoc m x p) m label' C' d' acc' cells' ∧
        (∀ σ : PSubst, nameAction.Models σ C'.equations →
          BagLaws (psubst σ (par acc' (pPar (cells'.map Prod.snd))))
            (psubst σ (par acc (pPar (cells.map Prod.snd))))) := by
  induction run with
  | refl label C => exact fun inv => ⟨_, _, _, inv, fun _ _ => BagLaws.refl _⟩
  | source g admitted notClose isStep _ _ =>
      intro d acc cells inv
      exact absurd isStep (done_phase_step_S inv.phase g admitted notClose).1
  | other g admitted notClose _ rest ih =>
      intro d acc cells inv
      obtain ⟨d₁, acc₁, cells₁, inv₁, bag₁, -⟩ := doneCells_step_or_keep inv g admitted notClose
      obtain ⟨d', acc', cells', inv', bag'⟩ := ih inv₁
      exact ⟨d', acc', cells', inv',
        fun σ s => (bag' σ s).trans (bag₁ σ (childRunS_back rest σ s))⟩

/-- Multi-step pre-commit run preserving `Cells` across arbitrary interleaved non-step firings. -/
theorem cells_run_reflects {m x p : Pattern} {label label' : O → Pattern}
    {C C' : Configuration Pattern O}
    (run : ChildRunS (childLoc m x p) label C label' C' 0) :
    ∀ {tk : O} {cells : List (O × Pattern)},
      PendingPhaseS (childLoc m x p) m label C tk →
      Cells (childLoc m x p) m label C tk cells →
      ∃ cells' : List (O × Pattern),
        PendingPhaseS (childLoc m x p) m label' C' tk ∧
        Cells (childLoc m x p) m label' C' tk cells' ∧
        BagLaws (pPar (cells'.map Prod.snd)) (pPar (cells.map Prod.snd)) := by
  generalize hZero : (0 : ℕ) = n at run
  induction run with
  | refl label C => exact fun phase inv => ⟨_, phase, inv, BagLaws.refl _⟩
  | source _ _ _ _ _ _ => omega
  | other g admitted _ notStep rest ih =>
      intro tk cells phase inv
      rcases pending_phase_step_S phase g admitted with ⟨-, phase₁⟩ | ⟨isStep, -⟩
      · obtain ⟨cells₁, inv₁, bag₁, -⟩ := cells_step_or_keep phase inv g admitted notStep
        obtain ⟨cells', phase', inv', bag'⟩ := ih hZero phase₁ inv₁
        exact ⟨cells', phase', inv', bag'.trans bag₁⟩
      · exact absurd isStep notStep

/-- **`child_reflects` extended to arbitrary interleaved runs**: after any pre-commit `ChildRunS`,
any admitted `commChild` on two input cells at `l`, any post-commit `ChildRunS`, and an admitted
`closeRootAt` of `reflection`, the commit is a source `BagComm` on `P`'s heated parts and the made
listener reads as the represented reduct's quote modulo `NameLaws`. -/
theorem interleaved_child_reflects (label₀ : O → Pattern) (C₀ : Configuration Pattern O)
    (x P : Pattern) (reflection tk pr : O)
    (phase₀ : PendingPhaseS (childLoc rootLoc x (predot P)) rootLoc label₀ C₀ tk)
    (opened : Cells (childLoc rootLoc x (predot P)) rootLoc label₀ C₀ tk [(pr, P)])
    {label₂ : O → Pattern} {C₂ : Configuration Pattern O}
    (preRun : ChildRunS (childLoc rootLoc x (predot P)) label₀ C₀ label₂ C₂ 0)
    (pre mid post : List (O × Pattern)) (first second made₁ made₂ madeTok listener : O)
    (t u ch ch' A B : Pattern)
    (groundCh : pvars ch = []) (groundCh' : pvars ch' = [])
    (canonicalCh : nameCanon ch = ch) (canonicalCh' : nameCanon ch' = ch')
    (unifiable : (∃ σ : PSubst, psubst σ t = psubst σ u) →
      ∃ bs : Bindings, GroundPrincipal t u bs ∧ ∀ y v, bs.lookup y = some v → firstOrder v = true)
    (convention : Apart t A u B) (foA : firstOrder A = true) (foB : firstOrder B = true)
    (groundT : groundBags t = true) (groundU : groundBags u = true)
    (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u)
    (ρc : PSubst)
    (committed : (RuleSyntax.step QN O QNE located).Admits (s := embed label₂ C₂)
      (commChildAt ρc first second tk made₁ made₂ madeTok))
    {label₄ : O → Pattern} {C₄ : Configuration Pattern O} {nPost : ℕ}
    (postRun : ChildRunS (childLoc rootLoc x (predot P))
      (res label₂ C₂ (commChildAt ρc first second tk made₁ made₂ madeTok)).label
      (resConf label₂ C₂ (commChildAt ρc first second tk made₁ made₂ madeTok)) label₄ C₄ nPost)
    (readsRefl₄ : ∀ σ : PSubst, nameAction.Models σ C₄.equations →
      NameLaws (psubst σ (label₄ reflection)) (psubst σ (atLoc (pReflect x (predot P)) rootLoc)))
    (d₄ : O) (ρ₅ : PSubst)
    (closed : (RuleSyntax.step QN O QNE located).Admits (s := embed label₄ C₄)
      (closeRootAt ρ₅ reflection d₄ listener)) :
    ∃ cells : List (O × Pattern),
      Cells (childLoc rootLoc x (predot P)) rootLoc label₂ C₂ tk cells ∧
      BagLaws (pPar (cells.map Prod.snd)) (pPar [P]) ∧
      (cells = pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch' B) :: post) →
        ch = ch' ∧ ∃ bs : Bindings,
          FiniteProgram.BagComm
            (pFor t ch A ::ₘ pFor u ch B ::ₘ ((pre ++ mid ++ post).map Prod.snd : Multiset Pattern))
            ((FiniteProgram.parts (applyDot bs A) : Multiset Pattern) +
              (FiniteProgram.parts (applyDot bs B) : Multiset Pattern) +
                ((pre ++ mid ++ post).map Prod.snd : Multiset Pattern)) ∧
          ∀ σ : PSubst,
            nameAction.Models σ (res label₄ C₄ (closeRootAt ρ₅ reflection d₄ listener)).knowledge →
              NameLaws (psubst σ ((res label₄ C₄ (closeRootAt ρ₅ reflection d₄ listener)).label listener))
                (psubst σ (atLoc (pFor (tProc (pPar ((pre ++ mid ++ post).map (fun q => predot q.2) ++
                  [predot (applyDot bs A), predot (applyDot bs B)]))) x pZero) rootLoc))) := by
  obtain ⟨cells, phase₂, inv₂, bag₂⟩ := cells_run_reflects preRun phase₀ opened
  refine ⟨cells, inv₂, bag₂, fun shape => ?_⟩
  subst shape
  have firstIn : (first, pFor t ch A) ∈
      pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch' B) :: post) := by simp
  have secondIn : (second, pFor u ch' B) ∈
      pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch' B) :: post) := by simp
  obtain ⟨sameCh, bs, bagComm, commitReads⟩ := child_commit_sound label₂ C₂ t u ch ch' A B
    (childLoc rootLoc x (predot P)) rootLoc first second tk made₁ made₂ madeTok ρc
    (inv₂.rows _ firstIn).2.2 (inv₂.rows _ secondIn).2.2 phase₂.reads groundCh groundCh'
    canonicalCh canonicalCh' unifiable convention foA foB groundT groundU canonicalT canonicalU
    committed ((pre ++ mid ++ post).map Prod.snd : Multiset Pattern)
  refine ⟨sameCh, bs, bagComm, ?_⟩
  obtain ⟨σc, solc⟩ := solution_of_admitted committed
  have zTok : (pendingTok locL locM, tk) ∈
      (commChildAt ρc first second tk made₁ made₂ madeTok).rule.body.take.zip
        (commChildAt ρc first second tk made₁ made₂ madeTok).selection.taken := by
    simp [commChildAt, commChild]
  have tkR := phase₂.reads σc (info_known _ solc)
  rw [psubst_pendingTok] at tkR
  have stepAt : StepAtS (childLoc rootLoc x (predot P)) label₂ C₂
      (commChildAt ρc first second tk made₁ made₂ madeTok) :=
    ⟨.inl rfl, σc, solc, (pending_reading_S ((take_reads _ solc zTok).trans tkR)).1⟩
  rcases pending_phase_step_S phase₂ _ committed with ⟨notS, -⟩ | ⟨-, d₃, done₃⟩
  · exact absurd stepAt notS
  · have mTokEq : madeTok = d₃ := done₃.unique madeTok
      ((result_present _ madeTok).mpr (.inr (by simp [commChildAt])))
      ⟨σc, solc, _, _, by simpa [psubst_doneTok] using (commitReads σc solc).2.2.2⟩
    subst mTokEq
    obtain ⟨_, shapes, enabled, -⟩ := (RuleSyntax.admits_iff _).mp committed
    have madeNd : [made₁, made₂, madeTok].Nodup := shapes.2.1
    have ne₁₂ : made₁ ≠ made₂ := fun s => (List.nodup_cons.mp madeNd).1 (by simp [s])
    have ne₁T : made₁ ≠ madeTok := fun s => (List.nodup_cons.mp madeNd).1 (by simp [s])
    have ne₂T : made₂ ≠ madeTok := fun s => (List.nodup_cons.mp (List.nodup_cons.mp madeNd).2).1 (by simp [s])
    have freshM : ∀ o, o = made₁ ∨ o = made₂ ∨ o = madeTok → o ∉ C₂.present := fun o h inC =>
      Finset.disjoint_left.mp enabled.fresh (by rcases h with rfl | rfl | rfl <;>
        simp [commChildAt, Selection.commit]) inC
    have permIds : ((pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch' B) :: post)).map Prod.fst).Perm
        (first :: second :: (pre ++ mid ++ post).map Prod.fst) := by
      simp only [List.map_append, List.map_cons]
      exact List.perm_middle.trans (List.Perm.cons _ (by rw [← List.append_assoc]; exact List.perm_middle))
    obtain ⟨firstOut, ndFront⟩ := List.nodup_cons.mp (permIds.nodup_iff.mp inv₂.nodup)
    obtain ⟨secondOut, restNd⟩ := List.nodup_cons.mp ndFront
    have restIn : ∀ q ∈ pre ++ mid ++ post,
        q ∈ pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch' B) :: post) := by
      intro q m; simp only [List.mem_append, List.mem_cons] at m ⊢
      rcases m with (h | h) | h
      · exact .inl h
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr (.inr h)))
    let postCells : List (O × Pattern) :=
      (pre ++ mid ++ post).map (fun q => (q.1, predot q.2)) ++
        [(made₁, predot (applyDot bs A)), (made₂, predot (applyDot bs B))]
    have doneInv₃ : DoneCells (childLoc rootLoc x (predot P)) rootLoc
        (res label₂ C₂ (commChildAt ρc first second tk made₁ made₂ madeTok)).label
        (resConf label₂ C₂ (commChildAt ρc first second tk made₁ made₂ madeTok))
        madeTok pZero postCells := by
      refine ⟨done₃, fun σ s => (commitReads σ s).2.2.2, ?_, ?_, ?_⟩
      · have mapFst : postCells.map Prod.fst = (pre ++ mid ++ post).map Prod.fst ++ [made₁, made₂] := by
          simp [postCells, List.map_map, Function.comp_def]
        rw [mapFst, List.nodup_append]
        refine ⟨restNd, by simp [ne₁₂], fun a inRest b inMade ab => ?_⟩
        obtain ⟨q, qIn, rfl⟩ := List.mem_map.mp inRest
        have qPres := (inv₂.rows q (restIn q qIn)).1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inMade
        rcases inMade with isM₁ | isM₂
        · exact freshM b (.inl isM₁) (ab ▸ qPres)
        · exact freshM b (.inr (.inl isM₂)) (ab ▸ qPres)
      · intro q qIn
        have qCases : q ∈ (pre ++ mid ++ post).map (fun q => (q.1, predot q.2)) ∨
            q = (made₁, predot (applyDot bs A)) ∨ q = (made₂, predot (applyDot bs B)) := by
          rcases List.mem_append.mp qIn with inMap | inMade
          · exact .inl inMap
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at inMade
            exact .inr inMade
        rcases qCases with inMap | rfl | rfl
        · obtain ⟨q₀, q₀In, rfl⟩ := List.mem_map.mp inMap
          obtain ⟨qPres, qNeTk, qR⟩ := inv₂.rows q₀ (restIn q₀ q₀In)
          have neF : q₀.1 ≠ first := fun e => firstOut (e ▸ List.mem_cons.mpr (.inr
            (List.mem_map.mpr ⟨q₀, q₀In, rfl⟩)))
          have neS : q₀.1 ≠ second := fun e => secondOut (e ▸ List.mem_map.mpr ⟨q₀, q₀In, rfl⟩)
          have neM₁ : q₀.1 ≠ made₁ := fun e => freshM made₁ (.inl rfl) (e ▸ qPres)
          have neM₂ : q₀.1 ≠ made₂ := fun e => freshM made₂ (.inr (.inl rfl)) (e ▸ qPres)
          have neMT : q₀.1 ≠ madeTok := fun e => freshM madeTok (.inr (.inr rfl)) (e ▸ qPres)
          refine ⟨(result_present _ q₀.1).mpr (.inl ⟨qPres, by simp [commChildAt, neF, neS, qNeTk]⟩),
            neMT, fun σ s => ?_⟩
          rw [result_label_old _ (by simp [commChildAt, neM₁, neM₂, neMT])]
          exact qR σ (commitReads σ s).1
        · exact ⟨(result_present _ made₁).mpr (.inr (by simp [commChildAt])), ne₁T,
            fun σ s => (commitReads σ s).2.1⟩
        · exact ⟨(result_present _ made₂).mpr (.inr (by simp [commChildAt])), ne₂T,
            fun σ s => (commitReads σ s).2.2.1⟩
      · intro o oPres oNeMT oNotPost σ s y same
        rcases result_row oPres with made | ⟨old, notTaken, -, lblOld⟩
        · simp only [commChildAt, List.mem_cons, List.not_mem_nil, or_false] at made
          rcases made with rfl | rfl | rfl
          · exact oNotPost (by simp [postCells])
          · exact oNotPost (by simp [postCells])
          · exact oNeMT rfl
        · rw [lblOld] at same
          have oNeTk : o ≠ tk := fun e => notTaken (by simp [commChildAt, e])
          have oNeF : o ≠ first := fun e => notTaken (by simp [commChildAt, e])
          have oNeS : o ≠ second := fun e => notTaken (by simp [commChildAt, e])
          refine inv₂.others o old oNeTk (fun inAll => ?_) σ (commitReads σ s).1 y same
          have inPerm := permIds.subset inAll
          simp only [List.mem_cons] at inPerm
          rcases inPerm with rfl | rfl | inRest
          · exact oNeF rfl
          · exact oNeS rfl
          · have mapFst : postCells.map Prod.fst =
                (pre ++ mid ++ post).map Prod.fst ++ [made₁, made₂] := by
              simp [postCells, List.map_map, Function.comp_def]
            exact oNotPost (by rw [mapFst]; exact List.mem_append_left _ inRest)
    obtain ⟨d', acc', cells', doneInv₄, bag₄⟩ := doneCells_run_reflects postRun doneInv₃
    obtain ⟨σ₅, sol₅⟩ := solution_of_admitted closed
    obtain ⟨chEq₅, pEq₅⟩ := ReflCorrespondence.close_reflection_reading label₄ C₄ x (predot P)
      reflection d₄ listener ρ₅ readsRefl₄ sol₅
    have childEq₅ : NameLaws
        (psubst σ₅ (psubst ρ₅ (childLoc rootLoc channelUnknown reflP)))
        (psubst σ₅ (childLoc rootLoc x (predot P))) := by
      rw [psubst_childLoc, psubst_childLoc, psubst_rootLoc, psubst_rootLoc]
      exact nameLaws_childLoc_iff.mpr ⟨NameLaws.refl _, chEq₅, pEq₅⟩
    have zDone : (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC, d₄) ∈
        (closeRootAt ρ₅ reflection d₄ listener).rule.body.take.zip
          (closeRootAt ρ₅ reflection d₄ listener).selection.taken := by
      simp [closeRootAt, closeRoot]
    obtain ⟨_, _, en₅, -⟩ := (RuleSyntax.admits_iff _).mp closed
    have d₄Pres : d₄ ∈ C₄.present := en₅.taken_subset (by simp [closeRootAt, Selection.commit])
    have rDone := take_reads _ sol₅ zDone
    rw [psubst_doneTok] at rDone
    have d₄Eq : d₄ = d' := doneInv₄.phase.unique d₄ d₄Pres ⟨σ₅, info_known _ sol₅, _, _,
      rDone.symm.trans (nameLaws_doneTok_iff.mpr ⟨childEq₅, NameLaws.refl _, NameLaws.refl _⟩)⟩
    subst d₄Eq
    have cells'Nil : cells' = [] := by
      cases cells' with
      | nil => rfl
      | cons q _ =>
          have qFacts := doneInv₄.rows q (List.mem_cons_self ..)
          exact False.elim (ReflCorrespondence.closeRoot_waits label₄ C₄ x (predot P)
            reflection d₄ listener ρ₅ readsRefl₄ qFacts.1 qFacts.2.2 closed)
    subst cells'Nil
    intro σ sClose
    obtain ⟨known₄, listenerR⟩ := closeRoot_reads label₄ C₄ x (predot P) acc' reflection d₄ listener
      ρ₅ readsRefl₄ doneInv₄.readsTok sClose
    have bagAcc : BagLaws (psubst σ acc')
        (psubst σ (pPar (postCells.map Prod.snd))) := by
      have step₀ := bag₄ σ known₄
      have leftUnit : BagLaws (psubst σ acc') (psubst σ (par acc' (pPar []))) := by
        have u₁ : BagLaws (par acc' (pPar [])) (pPar [acc']) := by
          simpa [par] using BagLaws.of_axiom (.flatten [acc'] [] [])
        exact ReflQuotient.bagLaws_psubst σ (u₁.trans (BagLaws.of_axiom (.single acc'))).symm
      have rightUnit : BagLaws (psubst σ (par pZero (pPar (postCells.map Prod.snd))))
          (psubst σ (pPar (postCells.map Prod.snd))) := by
        let X := pPar (postCells.map Prod.snd)
        have u₂ : BagLaws (par pZero X) (pPar [X]) := by
          simpa [par] using BagLaws.of_axiom (.zero [] [X])
        exact ReflQuotient.bagLaws_psubst σ (u₂.trans (BagLaws.of_axiom (.single X)))
      exact leftUnit.trans (step₀.trans rightUnit)
    have postSnd : postCells.map Prod.snd =
        (pre ++ mid ++ post).map (fun q => predot q.2) ++
          [predot (applyDot bs A), predot (applyDot bs B)] := by
      simp [postCells, List.map_map, Function.comp_def]
    rw [postSnd] at bagAcc
    refine listenerR.trans ?_
    simp only [psubst_atLoc_any, psubst_pFor, psubst_tProc, psubst_pZero, psubst_rootLoc]
    exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr
      ⟨nameLaws_pFor_iff.mpr ⟨nameLaws_tProc bagAcc, NameLaws.refl _, NameLaws.refl _⟩,
        NameLaws.refl _⟩

end InterleavedReflection

#print axioms cells_step_or_keep
#print axioms doneCells_step_or_keep
#print axioms doneCells_run_reflects
#print axioms cells_run_reflects
#print axioms interleaved_child_reflects

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem
