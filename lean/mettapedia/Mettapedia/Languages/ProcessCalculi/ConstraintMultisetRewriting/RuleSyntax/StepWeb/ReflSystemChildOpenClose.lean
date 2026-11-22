import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystemRootBag

/-!
# Non-root segment closers, `openChild`, `closeChild`, and solution extension across child steps

This module completes the whole-system depth-1 `REFL` integration of milestone P3 and builds the
firing-level foundation (`openChild` and `closeChild`) of milestone P4 at the name frame `QN`:

* **Non-root child runs and whole-system `REFL` closers** (`LocatedRunNoRoot`,
  `rootCells_keep_noRootRun`, `noRootRun_to_rootChildRunS`, `rootCells_closeRoot_N`,
  `rootCells_closeRoot_C`, `rootCells_refl_comm_backward`): connects arbitrary interleaved child
  runs directly to `RootCells` under both **Interface N** (`BagStep`, all reducts `R`) and
  **Interface C** (`CanonicalBagStep`, ground reducts `pvars R = []`).
* **Opening at a child** (`openChildAt`, `openChild_admitted`, `openChild_reads`,
  `openChild_enters_pending_S`, `openChild_extends`): opens a nested reflection `y?(Q) @ l` while
  `Pending(l, m)` is present and `Child(l, y, Q)` is `Clean`.
* **Inner close at a child & solution extensions** (`closeChild_fresh_exists`,
  `closeChild_reads`, `closeChild_waits`, `closeChild_extends`, `cool_extends`,
  `closeRoot_extends`, `commChild_extends`): reads the made listener and `Done(l, m, 0)` token of
  `closeChildAt`, proves its universal absence guard waits for grandchild cooling, and extends
  solutions across every child rule so `FreeOnPats` persists across recursive `REFL` segments.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar tProc pReflect applyDot)
open MeTTaOperationsComm (psubst PSubst pvars psubst_none psubst_pFor psubst_tProc psubst_pZero
  GroundPrincipal firstOrder)
open MeTTaCalculus.Corrected (Apart psubstList_eq_map canonicalBag BagStep CanonicalBagStep
  conventional listener)
open FiniteProgram (commRule heatRule clearRule leftPart firstPattern secondPattern channelUnknown
  firstBody secondBody parts predot)
open Comm (Tm X E renameBy ruleVars)
open OneFrame (embed)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open ReflQuotient (BagLaws bagCanon groundBags)
open ReflNames (NameLaws nameAction QN QNE nameCanon nameFiring fresh_name nameLaws_heads
  nameLaws_pFor_iff nameLaws_tProc nameLaws_psubst)
open ReflLocated (atLoc rootLoc childLoc pendingTok doneTok locL locM reflP accC anyY anyZ atRule
  located commChild heatChild cool closeRoot closeChild openRoot openChild psubst_rootLoc
  psubst_atLoc_any psubst_pendingTok psubst_par locatedFrame_name)
open ReflPacking (coolAt psubst_doneTok nameLaws_doneTok_iff CoolRun)
open ReflLocatedStep (psubst_childLoc nameLaws_pendingTok_iff nameLaws_childLoc_iff res resConf
  info_known take_reads read_reads solution_of_admitted result_present result_label_old
  commChildAt closeChild_mem closeChildAt childInstance innerCloseInstance psubst_pReflect
  nameLaws_pReflect_iff)
open ReflUniform (predotU)
open ReflCorrespondence (Clean LocatedRun openRootAt closeRootAt coolInstance closeInstance)
open ReflLocatedStep.Ownership (Store Candidate LabelForms Mark withWrittenComm
  written_comm_admits_iff writtenBinding_child writtenComm_pFor_iff writtenPairTells
  writtenPairTells_at readWrittenPair_child written_result_models written_result_publications
  child_comm_plan_iff)

section NonRootAndOpenClose

variable {O : Type*} [DecidableEq O]

/-! ## Non-root rule witnesses and `LocatedRunNoRoot` -/

private theorem nonRoot_of_openRoot :
    openRoot ≠ atRule rootLoc commRule ∧ openRoot ≠ atRule rootLoc heatRule ∧
      openRoot ≠ atRule rootLoc clearRule ∧ openRoot ≠ closeRoot := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;>
    { have h := congrArg (fun r => r.body.take.length) e
      simp [openRoot, atRule, commRule, heatRule, clearRule, closeRoot, RuleInstance.map] at h }

private theorem nonRoot_of_openChild :
    openChild ≠ atRule rootLoc commRule ∧ openChild ≠ atRule rootLoc heatRule ∧
      openChild ≠ atRule rootLoc clearRule ∧ openChild ≠ closeRoot := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;>
    { have h := congrArg (fun r => r.body.take.length) e
      simp [openChild, atRule, commRule, heatRule, clearRule, closeRoot, RuleInstance.map] at h }

private theorem nonRoot_of_commChild :
    commChild ≠ atRule rootLoc commRule ∧ commChild ≠ atRule rootLoc heatRule ∧
      commChild ≠ atRule rootLoc clearRule ∧ commChild ≠ closeRoot := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;>
    { have h := congrArg (fun r => r.body.take.length) e
      simp [commChild, atRule, commRule, heatRule, clearRule, closeRoot, RuleInstance.map] at h }

private theorem nonRoot_of_closeChild :
    closeChild ≠ atRule rootLoc commRule ∧ closeChild ≠ atRule rootLoc heatRule ∧
      closeChild ≠ atRule rootLoc clearRule ∧ closeChild ≠ closeRoot := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;>
    { have h := congrArg (fun r => r.body.take.length) e
      simp [closeChild, atRule, commRule, heatRule, clearRule, closeRoot, RuleInstance.map] at h }

private theorem nonRoot_of_heatChild :
    heatChild ≠ atRule rootLoc commRule ∧ heatChild ≠ atRule rootLoc heatRule ∧
      heatChild ≠ atRule rootLoc clearRule ∧ heatChild ≠ closeRoot := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;>
    { have h := congrArg (fun r => r.body.read.length) e
      simp [heatChild, atRule, commRule, heatRule, clearRule, closeRoot, RuleInstance.map] at h }

private theorem nonRoot_of_cool :
    cool ≠ atRule rootLoc commRule ∧ cool ≠ atRule rootLoc heatRule ∧
      cool ≠ atRule rootLoc clearRule ∧ cool ≠ closeRoot := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · have h := congrArg (fun r => r.body.produce.length) e
    simp [cool, atRule, commRule, RuleInstance.map] at h
  · have h := congrArg (fun r => r.body.produce.length) e
    simp [cool, atRule, heatRule, RuleInstance.map] at h
  · have h := congrArg (fun r => r.body.produce.length) e
    simp [cool, atRule, clearRule, RuleInstance.map] at h
  · have h := congrArg (fun r => r.body.checks.length) e
    simp [cool, closeRoot] at h

private theorem nonempty_take_ne_openRoot {rule : Rule Tm} (nonempty : rule.body.take ≠ []) :
    rule ≠ openRoot := by
  rintro rfl
  exact nonempty rfl

/-- A run preserving root process rows. In the `false` instance it
does not even open a root child; that stronger trace records what the
recursive packing proof actually does after the selected opening. -/
inductive LocatedRunNoRoot :
    (O → Pattern) → Configuration Pattern O → (O → Pattern) → Configuration Pattern O →
      (allowOpenRoot : Bool := true) → Prop where
  | refl {allowOpenRoot : Bool} (label : O → Pattern) (C : Configuration Pattern O) :
      LocatedRunNoRoot label C label C allowOpenRoot
  | step {label label' : O → Pattern} {C C' : Configuration Pattern O}
      {allowOpenRoot : Bool}
      (g : Firing O QNE located PUnit.unit)
      (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
      (notRootComm : g.rule ≠ atRule rootLoc commRule)
      (notRootHeat : g.rule ≠ atRule rootLoc heatRule)
      (notRootClear : g.rule ≠ atRule rootLoc clearRule)
      (notCloseRoot : g.rule ≠ closeRoot)
      (opening : allowOpenRoot = true ∨ g.rule ≠ openRoot)
      (rest : LocatedRunNoRoot (res label C g).label (resConf label C g) label' C' allowOpenRoot) :
      LocatedRunNoRoot label C label' C' allowOpenRoot

theorem LocatedRunNoRoot.toRun {label label' : O → Pattern} {C C' : Configuration Pattern O}
    {allowOpenRoot : Bool} (run : LocatedRunNoRoot label C label' C' allowOpenRoot) :
    LocatedRun label C label' C' := by
  induction run with
  | refl label C => exact .refl label C
  | step g admitted _ _ _ _ _ _ ih => exact .step g admitted ih

theorem LocatedRunNoRoot.allowOpening {label label' : O → Pattern} {C C' : Configuration Pattern O}
    {allowOpenRoot : Bool} (run : LocatedRunNoRoot label C label' C' allowOpenRoot) :
    LocatedRunNoRoot label C label' C' := by
  induction run with
  | refl label C => exact .refl label C
  | step g adm nC nH nCl nCR _ _ ih => exact .step g adm nC nH nCl nCR (.inl rfl) ih

theorem LocatedRunNoRoot.trans {label₁ label₂ label₃ : O → Pattern}
    {C₁ C₂ C₃ : Configuration Pattern O} {allowOpenRoot : Bool}
    (r₁ : LocatedRunNoRoot label₁ C₁ label₂ C₂ allowOpenRoot)
    (r₂ : LocatedRunNoRoot label₂ C₂ label₃ C₃ allowOpenRoot) :
    LocatedRunNoRoot label₁ C₁ label₃ C₃ allowOpenRoot := by
  revert r₂; induction r₁ with
  | refl => exact id
  | step g adm nC nH nCl nCR opening _ ih => exact fun r₂ => .step g adm nC nH nCl nCR opening (ih r₂)

theorem step_openRoot_noRoot {label label' : O → Pattern} {C C' : Configuration Pattern O}
    {ρ : PSubst} {r m₁ mt : O} {allowOpenRoot : Bool}
    (adm : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) (openRootAt ρ r m₁ mt))
    (rest : LocatedRunNoRoot (res label C (openRootAt ρ r m₁ mt)).label
      (resConf label C (openRootAt ρ r m₁ mt)) label' C' allowOpenRoot) :
    LocatedRunNoRoot label C label' C' :=
  .step _ adm nonRoot_of_openRoot.1 nonRoot_of_openRoot.2.1 nonRoot_of_openRoot.2.2.1
    nonRoot_of_openRoot.2.2.2 (.inl rfl) rest.allowOpening

theorem step_commChild_noRoot {label label' : O → Pattern} {C C' : Configuration Pattern O}
    {ρ : PSubst} {f s tk m₁ m₂ mt : O} {allowOpenRoot : Bool}
    (adm : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (commChildAt ρ f s tk m₁ m₂ mt))
    (rest : LocatedRunNoRoot (res label C (commChildAt ρ f s tk m₁ m₂ mt)).label
      (resConf label C (commChildAt ρ f s tk m₁ m₂ mt)) label' C' allowOpenRoot) :
    LocatedRunNoRoot label C label' C' allowOpenRoot :=
  .step _ adm nonRoot_of_commChild.1 nonRoot_of_commChild.2.1 nonRoot_of_commChild.2.2.1
    nonRoot_of_commChild.2.2.2
    (.inr (nonempty_take_ne_openRoot (rule := commChild) (by simp [commChild]))) rest

theorem step_closeChild_noRoot {label label' : O → Pattern} {C C' : Configuration Pattern O}
    {ρ : PSubst} {r it tk m₁ mt : O} {allowOpenRoot : Bool}
    (adm : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (closeChildAt ρ r it tk m₁ mt))
    (rest : LocatedRunNoRoot (res label C (closeChildAt ρ r it tk m₁ mt)).label
      (resConf label C (closeChildAt ρ r it tk m₁ mt)) label' C' allowOpenRoot) :
    LocatedRunNoRoot label C label' C' allowOpenRoot :=
  .step _ adm nonRoot_of_closeChild.1 nonRoot_of_closeChild.2.1 nonRoot_of_closeChild.2.2.1
    nonRoot_of_closeChild.2.2.2
    (.inr (nonempty_take_ne_openRoot (rule := closeChild) (by simp [closeChild]))) rest

theorem step_heatChild_noRoot {label label' : O → Pattern} {C C' : Configuration Pattern O}
    {ρ : PSubst} {o p m₁ m₂ : O} {allowOpenRoot : Bool}
    (adm : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (ReflLocated.heatChildN ρ o p m₁ m₂))
    (rest : LocatedRunNoRoot (res label C (ReflLocated.heatChildN ρ o p m₁ m₂)).label
      (resConf label C (ReflLocated.heatChildN ρ o p m₁ m₂)) label' C' allowOpenRoot) :
    LocatedRunNoRoot label C label' C' allowOpenRoot :=
  .step _ adm nonRoot_of_heatChild.1 nonRoot_of_heatChild.2.1 nonRoot_of_heatChild.2.2.1
    nonRoot_of_heatChild.2.2.2
    (.inr (nonempty_take_ne_openRoot (rule := heatChild) (by simp [heatChild]))) rest

theorem coolRun_noRoot {l m : Pattern} {label label' : O → Pattern}
    {C C' : Configuration Pattern O} {d d' : O} {rows : List Pattern} {allowOpenRoot : Bool}
    (run : CoolRun l m label C d label' C' d' rows) :
    LocatedRunNoRoot label C label' C' allowOpenRoot := by
  induction run with
  | refl label C d => exact .refl label C
  | step ρ r d₁ a admitted _ _ ih =>
      exact .step _ admitted nonRoot_of_cool.1 nonRoot_of_cool.2.1 nonRoot_of_cool.2.2.1
        nonRoot_of_cool.2.2.2 (.inr (nonempty_take_ne_openRoot (rule := cool) (by simp [cool]))) ih

/-- **Every `LocatedRunNoRoot` preserves both `NoRootTokens` and `RootCells`.** -/
theorem rootCells_keep_noRootRun {label label' : O → Pattern} {C C' : Configuration Pattern O}
    {rootRows : List (O × Pattern)} {allowOpenRoot : Bool} (run : LocatedRunNoRoot label C label' C' allowOpenRoot)
    (noTok : NoRootTokens label C) (inv : RootCells label C rootRows) :
    NoRootTokens label' C' ∧ RootCells label' C' rootRows := by
  induction run with
  | refl => exact ⟨noTok, inv⟩
  | step g adm nC nH nCl nCR _ _ ih =>
      exact ih (noRootTokens_preserved noTok g adm)
        (rootCells_keep_nonRoot noTok inv g adm nC nH nCl nCR)

/-- Every `LocatedRunNoRoot` from a `NoRootTokens` state is a `ChildRunS` at any root child
`childLoc rootLoc x p` (no firing in `LocatedRunNoRoot` can close a depth-1 root child). -/
theorem noRootRun_to_rootChildRunS {x p : Pattern} {label label' : O → Pattern}
    {C C' : Configuration Pattern O} {allowOpenRoot : Bool} (run : LocatedRunNoRoot label C label' C' allowOpenRoot)
    (noTok : NoRootTokens label C) :
    ∃ n : ℕ, ChildRunS (childLoc rootLoc x p) label C label' C' n := by
  induction run with
  | refl label C => exact ⟨0, .refl label C⟩
  | @step label₁ label₂ C₁ C₂ _ g adm nC nH nCl nCR _ _ ih =>
      obtain ⟨n, subRun⟩ := ih (noRootTokens_preserved noTok g adm)
      have notCl : ¬ CloseAtS (childLoc rootLoc x p) label₁ C₁ g := by
        rintro (⟨isR, -⟩ | ⟨isC, σ, solved, same⟩)
        · exact nCR isR
        · simp only [psubst_childLoc, psubst_rootLoc] at same
          have locRoot := (nameLaws_childLoc_iff.mp same).1
          obtain ⟨oP, zP, pP⟩ := ReflLocatedStep.taken_row adm (t := pendingTok locL locM)
            (by rw [isC]; simp [closeChild])
          have rP := take_reads g solved zP
          rw [psubst_pendingTok, psubst_pendingTok] at rP
          exact (noTok oP pP σ (info_known g solved)).1 _
            (rP.symm.trans (nameLaws_pendingTok_iff.mpr ⟨locRoot, NameLaws.refl _⟩))
      by_cases isS : StepAtS (childLoc rootLoc x p) label₁ C₁ g
      · exact ⟨n + 1, .source g adm notCl isS subRun⟩
      · exact ⟨n, .other g adm notCl isS subRun⟩

/-- **Whole-system `REFL` segment closer — Interface N (`BagStep`)**. -/
theorem rootCells_closeRoot_N {admit : MeTTaCalculus.Corrected.Admission}
    {label label₄ : O → Pattern} {C C₄ : Configuration Pattern O}
    {pre post : List (O × Pattern)} {reflOcc d₄ made : O} {ρ₅ : PSubst}
    {x P_sub R : Pattern} (noTok : NoRootTokens label C)
    (inv : RootCells label C (pre ++ (reflOcc, pReflect x P_sub) :: post))
    (groundX : pvars x = [])
    (segRun : LocatedRunNoRoot label C label₄ C₄)
    (dReads : ∃ σ₀ : PSubst, nameAction.Models σ₀ C₄.equations ∧
      ∃ l' m' c', NameLaws (psubst σ₀ (label₄ d₄)) (doneTok l' m' c'))
    (closed : (RuleSyntax.step QN O QNE located).Admits (s := embed label₄ C₄)
      (closeRootAt ρ₅ reflOcc d₄ made))
    (madeQuote : ∀ σ : PSubst,
      nameAction.Models σ (res label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)).knowledge →
        NameLaws (psubst σ ((res label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)).label made))
          (psubst σ (atLoc (pFor (tProc (predotU R)) x pZero) rootLoc)))
    (stepSub : BagStep admit P_sub R) :
    LocatedRun label C (res label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)).label
        (resConf label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)) ∧
      NoRootTokens (res label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)).label
        (resConf label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)) ∧
      RootCells (res label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)).label
        (resConf label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made))
        (pre ++ (made, pFor (tProc R) x pZero) :: post) ∧
      BagStep admit (rootBagProcess (pre ++ (reflOcc, pReflect x P_sub) :: post))
        (rootBagProcess (pre ++ (made, pFor (tProc R) x pZero) :: post)) := by
  obtain ⟨noTok₄, inv₄⟩ := rootCells_keep_noRootRun segRun noTok inv
  exact ⟨segRun.toRun.trans (.step _ closed (.refl _ _)),
    noRootTokens_preserved noTok₄ _ closed,
    rootCells_closeRoot inv₄ dReads closed fun σ s => by
      rw [predotU_named_listener groundX R]; exact madeQuote σ s,
    by simpa [rootBagProcess, List.map_append] using
      bagStep_of_pPar_refl (pre.map Prod.snd) (post.map Prod.snd) x P_sub R stepSub⟩

/-- Settle a named-quote source reaction at the actual owner's root
row. The selected packed token supplies the reduct; its source
reaction is an independent premise, not a consequence of routing or
solvability in the name quotient. Other root rows are retained. -/
theorem rootCells_owned_closeRoot_N (policy : ReflLocatedStep.Ownership.GuardPolicy)
    {label : O → Pattern} {C : Configuration Pattern O}
    (ledger : LocatedSubstitution.Authority.Ledger O ReflLocatedStep.Ownership.Phase)
    {pre post : List (O × Pattern)} {owner d made : O} {x P R acc : Pattern} {ρ : PSubst}
    (inv : RootCells label C (pre ++ (owner, pReflect x P) :: post))
    (groundX : pvars x = [])
    (readsToken : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label d)) (psubst σ (doneTok (childLoc rootLoc x (predotU P)) rootLoc acc)))
    (pack : BagLaws acc (predotU R)) (childStep : BagStep conventional P R)
    (formed : LabelForms ((Store.plain (embed label C) ledger) : Store O))
    (admitted : (ReflLocatedStep.Ownership.step (O := O) policy).Admits
      (s := (Store.plain (embed label C) ledger)) ⟨closeRootAt ρ owner d made, .closeRoot, rfl⟩) :
    let s : Store O := (Store.plain (embed label C) ledger)
    let f : Candidate s := ⟨closeRootAt ρ owner d made, .closeRoot, rfl⟩
    let after := (ReflLocatedStep.Ownership.step (O := O) policy).toStep.result f admitted
    ∃ t, s.route d = some (.control t .done) ∧ t.owner = owner ∧ t.parent = none ∧
      RootCells after.raw.label ⟨after.raw.knowledge, after.raw.present⟩
        (pre ++ (made, pFor (tProc R) x pZero) :: post) ∧
      BagStep conventional (rootBagProcess (pre ++ (owner, pReflect x P) :: post))
        (rootBagProcess (pre ++ (made, pFor (tProc R) x pZero) :: post)) := by
  intro s f after
  obtain ⟨t, mark, ownerEq, root, _, _, _, _⟩ :=
    ReflCorrespondence.closeRoot_owned_readback policy label C ledger ρ owner d made formed admitted
  let g := closeRootAt ρ owner d made
  have readOwner (σ : PSubst) (known : nameAction.Models σ C.equations) :
      NameLaws (psubst σ (label owner)) (psubst σ (atLoc (pReflect x (predotU P)) rootLoc)) := by
    have row := (inv.rows (owner, pReflect x P) (by simp)).2 σ known
    rw [predotU_pReflect, ReflUniform.predotU_ground x groundX] at row
    exact row
  obtain ⟨_, σ, solved⟩ := admitted.1.2.2.1
  have known := info_known g solved
  have token := readsToken σ known
  rw [psubst_doneTok] at token
  have dReads : ∃ σ₀ : PSubst, nameAction.Models σ₀ C.equations ∧
      ∃ l m c, NameLaws (psubst σ₀ (label d)) (doneTok l m c) :=
    ⟨σ, known, _, _, _, token⟩
  have readMade (υ : PSubst) (models : nameAction.Models υ (res label C g).knowledge) :
      NameLaws (psubst υ ((res label C g).label made))
        (psubst υ (atLoc (predotU (pFor (tProc R) x pZero)) rootLoc)) := by
    have returned := (ReflCorrespondence.closeRoot_reads label C x (predotU P) acc owner d made
      ρ readOwner readsToken models).2
    rw [predotU_named_listener groundX]
    exact returned.trans (nameLaws_psubst υ ((locatedFrame_name.atLoc_iff _ _ _ _).mpr
      ⟨nameLaws_pFor_iff.mpr ⟨nameLaws_tProc pack, NameLaws.refl _, NameLaws.refl _⟩, NameLaws.refl _⟩))
  have raw : after.raw = res label C g :=
    ReflLocatedStep.Ownership.raw_result (policy := policy) admitted
  refine ⟨t, mark, ownerEq, root, ?_, ?_⟩
  · rw [raw]
    exact rootCells_closeRoot_of_enabled inv dReads admitted.1.2.1 readMade
  · simpa [rootBagProcess, List.map_append] using
      bagStep_of_pPar_refl (pre.map Prod.snd) (post.map Prod.snd) x P R childStep

/-- **Whole-system `REFL` segment closer — Interface C (`CanonicalBagStep`, `pvars R = []`)**. -/
theorem rootCells_closeRoot_C {admit : MeTTaCalculus.Corrected.Admission}
    {label label₄ : O → Pattern} {C C₄ : Configuration Pattern O}
    {pre post : List (O × Pattern)} {reflOcc d₄ made : O} {ρ₅ : PSubst}
    {x P_sub R : Pattern} (noTok : NoRootTokens label C)
    (inv : RootCells label C (pre ++ (reflOcc, pReflect x P_sub) :: post))
    (groundX : pvars x = []) (groundR : pvars R = [])
    (segRun : LocatedRunNoRoot label C label₄ C₄)
    (dReads : ∃ σ₀ : PSubst, nameAction.Models σ₀ C₄.equations ∧
      ∃ l' m' c', NameLaws (psubst σ₀ (label₄ d₄)) (doneTok l' m' c'))
    (closed : (RuleSyntax.step QN O QNE located).Admits (s := embed label₄ C₄)
      (closeRootAt ρ₅ reflOcc d₄ made))
    (madeQuote : ∀ σ : PSubst,
      nameAction.Models σ (res label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)).knowledge →
        NameLaws (psubst σ ((res label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)).label made))
          (psubst σ (atLoc (pFor (tProc (predotU R)) x pZero) rootLoc)))
    (stepSub : CanonicalBagStep admit P_sub R) :
    LocatedRun label C (res label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)).label
        (resConf label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)) ∧
      NoRootTokens (res label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)).label
        (resConf label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)) ∧
      RootCells (res label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)).label
        (resConf label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made))
        (pre ++ (made, listener x R) :: post) ∧
      CanonicalBagStep admit (rootBagProcess (pre ++ (reflOcc, pReflect x P_sub) :: post))
        (rootBagProcess (pre ++ (made, listener x R) :: post)) := by
  obtain ⟨noTok₄, inv₄⟩ := rootCells_keep_noRootRun segRun noTok inv
  have eqCanon : NameLaws (tProc (predotU R)) (tProc (canonicalBag R)) :=
    nameLaws_tProc (ReflCorrespondence.quote_closed_ground R groundR).symm
  refine ⟨segRun.toRun.trans (.step _ closed (.refl _ _)),
    noRootTokens_preserved noTok₄ _ closed,
    rootCells_closeRoot (listenerTerm := listener x R) inv₄ dReads closed fun σ s => ?_,
    by simpa [rootBagProcess, List.map_append] using
      canonicalBagStep_of_pPar_refl (pre.map Prod.snd) (post.map Prod.snd) x P_sub R stepSub⟩
  rw [predotU_closed_listener groundX R]
  refine (madeQuote σ s).trans (nameLaws_psubst σ ?_)
  exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr
    ⟨nameLaws_pFor_iff.mpr ⟨eqCanon, NameLaws.refl _, NameLaws.refl _⟩, NameLaws.refl _⟩

/-- **Backward reflection of an arbitrary interleaved depth-1 `REFL` run on `RootCells`**. -/
theorem rootCells_refl_comm_backward {label₀ label₂ label₄ : O → Pattern}
    {C₀ C₂ C₄ : Configuration Pattern O} {pre post : List (O × Pattern)}
    {reflOcc pr tk first second made₁ made₂ madeTok d₄ listenerOcc : O}
    {ρ₁ ρc ρ₅ : PSubst} {x P_sub : Pattern}
    (noTok₀ : NoRootTokens label₀ C₀)
    (inv₀ : RootCells label₀ C₀ (pre ++ (reflOcc, pReflect x P_sub) :: post))
    (groundX : pvars x = []) (plainSub : PlainPatterns P_sub)
    (clean₀ : Clean (childLoc rootLoc x (predot P_sub)) label₀ C₀)
    (heatSub : ReflCorrespondence.Heatable P_sub)
    (opened : (RuleSyntax.step QN O QNE located).Admits (s := embed label₀ C₀)
      (openRootAt ρ₁ reflOcc pr tk))
    (preRun : LocatedRunNoRoot (res label₀ C₀ (openRootAt ρ₁ reflOcc pr tk)).label
      (resConf label₀ C₀ (openRootAt ρ₁ reflOcc pr tk)) label₂ C₂)
    (committed : (RuleSyntax.step QN O QNE located).Admits (s := embed label₂ C₂)
      (commChildAt ρc first second tk made₁ made₂ madeTok))
    (stepAt : StepAtS (childLoc rootLoc x (predot P_sub)) label₂ C₂
      (commChildAt ρc first second tk made₁ made₂ madeTok))
    (postRun : LocatedRunNoRoot
      (res label₂ C₂ (commChildAt ρc first second tk made₁ made₂ madeTok)).label
      (resConf label₂ C₂ (commChildAt ρc first second tk made₁ made₂ madeTok)) label₄ C₄)
    (closed : (RuleSyntax.step QN O QNE located).Admits (s := embed label₄ C₄)
      (closeRootAt ρ₅ reflOcc d₄ listenerOcc))
    {cPre cMid cPost : List (O × Pattern)} {t u ch ch' A B : Pattern}
    (groundCh : pvars ch = []) (groundCh' : pvars ch' = [])
    (canonicalCh : nameCanon ch = ch) (canonicalCh' : nameCanon ch' = ch')
    (unifiable : (∃ σ : PSubst, psubst σ t = psubst σ u) →
      ∃ bs : Bindings, GroundPrincipal t u bs ∧ ∀ y v, bs.lookup y = some v → firstOrder v = true)
    (convention : Apart t A u B) (foA : firstOrder A = true) (foB : firstOrder B = true)
    (groundT : groundBags t = true) (groundU : groundBags u = true)
    (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u) :
    ∃ cells : List (O × Pattern),
      ReflCorrespondence.Cells (childLoc rootLoc x (predot P_sub)) rootLoc label₂ C₂ tk cells ∧
      BagLaws (pPar (cells.map Prod.snd)) (pPar [P_sub]) ∧
      (cells = cPre ++ (first, pFor t ch A) :: (cMid ++ (second, pFor u ch' B) :: cPost) →
        ch = ch' ∧ ∃ bs : Bindings,
          let rawReduct := pPar ((cPre ++ cMid ++ cPost).map (fun q => predot q.2) ++
            [predot (applyDot bs A), predot (applyDot bs B)])
          FiniteProgram.BagComm
            (pFor t ch A ::ₘ pFor u ch B ::ₘ
              ((cPre ++ cMid ++ cPost).map Prod.snd : Multiset Pattern))
            ((parts (applyDot bs A) : Multiset Pattern) +
              (parts (applyDot bs B) : Multiset Pattern) +
              ((cPre ++ cMid ++ cPost).map Prod.snd : Multiset Pattern)) ∧
          (∀ R : Pattern, BagLaws rawReduct (predotU R) →
            BagStep conventional P_sub R →
            RootCells (res label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ listenerOcc)).label
              (resConf label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ listenerOcc))
              (pre ++ (listenerOcc, pFor (tProc R) x pZero) :: post) ∧
            BagStep conventional (rootBagProcess (pre ++ (reflOcc, pReflect x P_sub) :: post))
              (rootBagProcess (pre ++ (listenerOcc, pFor (tProc R) x pZero) :: post)))) := by
  have reflR₀ : ∀ σ : PSubst, nameAction.Models σ C₀.equations →
      NameLaws (psubst σ (label₀ reflOcc))
        (psubst σ (atLoc (pReflect x (predot P_sub)) rootLoc)) := by
    intro σ s; have r := (inv₀.rows (reflOcc, pReflect x P_sub) (by simp)).2 σ s
    rwa [predotU_pReflect, ReflUniform.predotU_ground x groundX,
      predotU_eq_predot_of_plain P_sub plainSub] at r
  have phase₁ := openRoot_enters_pending_S label₀ C₀ x (predot P_sub) reflOcc pr tk ρ₁ reflR₀
    clean₀ opened
  have cells₁ := ReflCorrespondence.opened_cells label₀ C₀ x P_sub reflOcc pr tk ρ₁ reflR₀
    clean₀ heatSub opened
  have noTok₁ := noRootTokens_preserved noTok₀ _ opened
  obtain ⟨nPre, preChild⟩ := noRootRun_to_rootChildRunS (x := x) (p := predot P_sub) preRun noTok₁
  have nPreZero : nPre = 0 := by
    rcases pending_run_S preChild phase₁ with ⟨hZ, -⟩ | ⟨-, d₂, done₂⟩
    · exact hZ
    · have notClC : ¬ CloseAtS (childLoc rootLoc x (predot P_sub)) label₂ C₂
          (commChildAt ρc first second tk made₁ made₂ madeTok) := by
        rintro (⟨isR, -⟩ | ⟨isC, -⟩)
        · exact nonRoot_of_commChild.2.2.2 isR
        · have h := congrArg (fun r => r.body.produce.length) isC
          simp [commChildAt, commChild, closeChild] at h
      exact absurd stepAt (done_phase_step_S done₂ _ committed notClC).1
  subst nPreZero
  have segPre := step_openRoot_noRoot opened preRun
  obtain ⟨noTok₂, -⟩ := rootCells_keep_noRootRun segPre noTok₀ inv₀
  have noTok₃ := noRootTokens_preserved noTok₂ _ committed
  obtain ⟨_, postChild⟩ :=
    noRootRun_to_rootChildRunS (x := x) (p := predot P_sub) postRun noTok₃
  have segRun := segPre.trans (step_commChild_noRoot committed postRun)
  obtain ⟨-, inv₄⟩ := rootCells_keep_noRootRun segRun noTok₀ inv₀
  have reflR₄ : ∀ σ : PSubst, nameAction.Models σ C₄.equations →
      NameLaws (psubst σ (label₄ reflOcc))
        (psubst σ (atLoc (pReflect x (predot P_sub)) rootLoc)) := by
    intro σ s; have r := (inv₄.rows (reflOcc, pReflect x P_sub) (by simp)).2 σ s
    rwa [predotU_pReflect, ReflUniform.predotU_ground x groundX,
      predotU_eq_predot_of_plain P_sub plainSub] at r
  obtain ⟨cells, cellsInv, bagCells, onShape⟩ :=
    interleaved_child_reflects (res label₀ C₀ (openRootAt ρ₁ reflOcc pr tk)).label
      (resConf label₀ C₀ (openRootAt ρ₁ reflOcc pr tk)) x P_sub reflOcc tk pr phase₁ cells₁
      preChild cPre cMid cPost first second made₁ made₂ madeTok listenerOcc t u ch ch' A B
      groundCh groundCh' canonicalCh canonicalCh' unifiable convention foA foB
      groundT groundU canonicalT canonicalU ρc committed postChild reflR₄ d₄ ρ₅ closed
  refine ⟨cells, cellsInv, bagCells, fun shape => ?_⟩
  obtain ⟨sameCh, bs, bagComm, listenerR⟩ := onShape shape
  refine ⟨sameCh, bs, bagComm, fun R eqR stepSub => ?_⟩
  obtain ⟨σ₅, sol₅⟩ := solution_of_admitted closed
  have zDone : (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC, d₄) ∈
      (closeRootAt ρ₅ reflOcc d₄ listenerOcc).rule.body.take.zip
        (closeRootAt ρ₅ reflOcc d₄ listenerOcc).selection.taken := by
    simp [closeRootAt, closeRoot]
  have rDone := take_reads _ sol₅ zDone
  rw [psubst_doneTok, psubst_doneTok] at rDone
  have dReads : ∃ σ₀ : PSubst, nameAction.Models σ₀ C₄.equations ∧
      ∃ l' m' c', NameLaws (psubst σ₀ (label₄ d₄)) (doneTok l' m' c') :=
    ⟨σ₅, info_known _ sol₅, _, _, _, rDone.symm⟩
  have madeQuote : ∀ σ : PSubst,
      nameAction.Models σ (res label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ listenerOcc)).knowledge →
        NameLaws
          (psubst σ ((res label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ listenerOcc)).label listenerOcc))
          (psubst σ (atLoc (pFor (tProc (predotU R)) x pZero) rootLoc)) := fun σ s =>
    (listenerR σ s).trans (nameLaws_psubst σ ((locatedFrame_name.atLoc_iff _ _ _ _).mpr
      ⟨nameLaws_pFor_iff.mpr ⟨nameLaws_tProc eqR, NameLaws.refl _, NameLaws.refl _⟩,
        NameLaws.refl _⟩))
  obtain ⟨-, -, inv₅, stepRoot⟩ := rootCells_closeRoot_N noTok₀ inv₀ groundX segRun dReads closed
    madeQuote stepSub
  exact ⟨inv₅, stepRoot⟩

/-! ## Opening at a child (`openChildAt`) -/

theorem openChild_mem : openChild ∈ located :=
  Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- Opening at a child `l`: read `reflection` (`x?(p) @ l`) and `parentToken` (`Pending(l, m)`);
make `made₁` (`p @ Child(l, x, p)`) and `madeTok` (`Pending(Child(l, x, p), l)`). -/
def openChildAt (ρ : PSubst) (reflection parentToken made₁ madeTok : O) :
    Firing O QNE located PUnit.unit :=
  ⟨openChild, openChild_mem, PUnit.unit, ρ, ⟨[], [reflection, parentToken], [made₁, madeTok]⟩, []⟩

def openChildAtX (ρ : PSubst) (reflection parentToken made₁ madeTok : O) :
    Firing O E located PUnit.unit :=
  ⟨openChild, openChild_mem, PUnit.unit, ρ, ⟨[], [reflection, parentToken], [made₁, madeTok]⟩, []⟩

omit [DecidableEq O] in
theorem openChild_fresh_exists (label : O → Pattern) (C : Configuration Pattern O)
    (reflection parentToken made₁ madeTok : O) :
    ∃ ρ : PSubst,
      (openChildAt ρ reflection parentToken made₁ madeTok).Fresh QN (embed label C) := by
  obtain ⟨g, inj, avoids⟩ := Comm.exists_apart_renaming (embed label C) (ruleVars openChild)
  refine ⟨renameBy g, ?_⟩
  change (nameFiring (openChildAtX (renameBy g) reflection parentToken made₁ madeTok)).Fresh QN
    (embed label C)
  exact fresh_name (Comm.fresh_of_renaming (embed label C)
    (openChildAtX (renameBy g) reflection parentToken made₁ madeTok) g rfl inj avoids)

theorem step_openChild_noRoot {label label' : O → Pattern} {C C' : Configuration Pattern O}
    {ρ : PSubst} {r pt m₁ mt : O} {allowOpenRoot : Bool}
    (adm : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (openChildAt ρ r pt m₁ mt))
    (rest : LocatedRunNoRoot (res label C (openChildAt ρ r pt m₁ mt)).label
      (resConf label C (openChildAt ρ r pt m₁ mt)) label' C' allowOpenRoot) :
    LocatedRunNoRoot label C label' C' allowOpenRoot :=
  .step _ adm nonRoot_of_openChild.1 nonRoot_of_openChild.2.1 nonRoot_of_openChild.2.2.1
    nonRoot_of_openChild.2.2.2 (.inr (fun equal => by
      have size := congrArg (fun rule => rule.body.read.length) equal
      change (2 : ℕ) = 1 at size
      nomatch size)) rest

theorem openChild_present (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (reflection parentToken made₁ madeTok o : O) :
    o ∈ (res label C (openChildAt ρ reflection parentToken made₁ madeTok)).present ↔
      o ∈ C.present ∨ o = made₁ ∨ o = madeTok := by
  rw [result_present]; simp [openChildAt]

theorem openChild_label_old (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (reflection parentToken made₁ madeTok : O) {o : O} (ne₁ : o ≠ made₁) (neT : o ≠ madeTok) :
    (res label C (openChildAt ρ reflection parentToken made₁ madeTok)).label o = label o :=
  result_label_old _ (by simp [openChildAt, ne₁, neT])

omit [DecidableEq O] in
theorem openChild_reading (label : O → Pattern) (C : Configuration Pattern O)
    (x p l m : Pattern) (reflection parentToken made₁ madeTok : O) (ρ : PSubst)
    (readsRefl : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) l)))
    (readsTok : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label parentToken)) (psubst σ (pendingTok l m)))
    {σ : PSubst}
    (solved : nameAction.Models σ
      ((openChildAt ρ reflection parentToken made₁ madeTok).information QN (embed label C))) :
    NameLaws (psubst σ (psubst ρ locL)) (psubst σ l) ∧
      NameLaws (psubst σ (psubst ρ locM)) (psubst σ m) ∧
      NameLaws (psubst σ (psubst ρ channelUnknown)) (psubst σ x) ∧
      NameLaws (psubst σ (psubst ρ reflP)) (psubst σ p) := by
  have known := info_known _ solved
  have zR : (atLoc (pReflect channelUnknown reflP) locL, reflection) ∈
      (openChildAt ρ reflection parentToken made₁ madeTok).rule.body.read.zip
        (openChildAt ρ reflection parentToken made₁ madeTok).selection.read := by
    simp [openChildAt, openChild]
  have zT : (pendingTok locL locM, parentToken) ∈
      (openChildAt ρ reflection parentToken made₁ madeTok).rule.body.read.zip
        (openChildAt ρ reflection parentToken made₁ madeTok).selection.read := by
    simp [openChildAt, openChild]
  have rR := (read_reads _ solved zR).trans (readsRefl σ known)
  have rT := (read_reads _ solved zT).trans (readsTok σ known)
  simp only [psubst_atLoc_any, psubst_pReflect] at rR
  simp only [psubst_pendingTok] at rT
  obtain ⟨partsR, locEq⟩ := (locatedFrame_name.atLoc_iff _ _ _ _).mp rR
  obtain ⟨chEq, pEq⟩ := nameLaws_pReflect_iff.mp partsR
  obtain ⟨-, mEq⟩ := nameLaws_pendingTok_iff.mp rT
  exact ⟨locEq, mEq, chEq, pEq⟩

/-- **`openChildAt` is admitted whenever `x?(p) @ l` and `Pending(l, m)` are present and
`Child(l, x, p)` is `Clean`.** -/
theorem openChild_admitted (label : O → Pattern) (C : Configuration Pattern O)
    (x p l m : Pattern) (reflection parentToken made₁ madeTok : O)
    (readsRefl : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) l)))
    (readsTok : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label parentToken)) (psubst σ (pendingTok l m)))
    (clean : Clean (childLoc l x p) label C)
    (presentR : reflection ∈ C.present) (presentT : parentToken ∈ C.present)
    (madeDistinct : made₁ ≠ madeTok)
    (fresh : made₁ ∉ C.present ∧ madeTok ∉ C.present)
    {σ₀ : PSubst} (known₀ : nameAction.Models σ₀ C.equations)
    {ρ : PSubst}
    (opensFreshly : (openChildAt ρ reflection parentToken made₁ madeTok).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (openChildAt ρ reflection parentToken made₁ madeTok) := by
  let h : PSubst := innerCloseInstance (psubst σ₀ x) (psubst σ₀ p) pZero (psubst σ₀ l) (psubst σ₀ m)
  have hRefl : psubst h (atLoc (pReflect channelUnknown reflP) locL) =
      psubst σ₀ (atLoc (pReflect x p) l) := by
    simp [h, innerCloseInstance, atLoc, pReflect, channelUnknown, reflP, locL, psubst,
      psubstList_eq_map]
  have hTok : psubst h (pendingTok locL locM) = psubst σ₀ (pendingTok l m) := by
    simp [h, innerCloseInstance, pendingTok, locL, locM, psubst, psubstList_eq_map]
  obtain ⟨w, solved, -, -⟩ := Comm.information_amalgamates_matched (Y := QN) (s := embed label C)
    (openChildAt ρ reflection parentToken made₁ madeTok) opensFreshly (b := PUnit.unit) σ₀ h known₀
    (fun _ m => (List.not_mem_nil m).elim)
    (fun _ m => (List.not_mem_nil m).elim)
    (fun o m => by
      simp only [openChildAt, List.mem_cons, List.not_mem_nil, or_false] at m
      rcases m with rfl | rfl
      · exact presentR
      · exact presentT)
    (fun _ m => (List.not_mem_nil m).elim)
    (fun q m => by
      simp only [openChildAt, openChild, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
        List.not_mem_nil, or_false] at m
      rcases m with rfl | rfl
      · show NameLaws (psubst h (atLoc (pReflect channelUnknown reflP) locL))
            (psubst σ₀ (label reflection))
        rw [hRefl]; exact (readsRefl σ₀ known₀).symm
      · show NameLaws (psubst h (pendingTok locL locM)) (psubst σ₀ (label parentToken))
        rw [hTok]; exact (readsTok σ₀ known₀).symm)
  refine (RuleSyntax.admits_iff _).mpr ⟨opensFreshly,
    ⟨by simp [openChildAt], by simp [openChildAt, madeDistinct], rfl, rfl, rfl, rfl⟩,
    ⟨fun _ m => by simp [openChildAt, Selection.commit] at m,
     fun o m => by
       simp only [openChildAt, Selection.commit, List.toFinset_cons, List.toFinset_nil,
         insert_empty_eq, Finset.mem_insert, Finset.mem_singleton] at m
       rcases m with rfl | rfl
       · exact presentR
       · exact presentT,
     by simp [openChildAt, Selection.commit],
     by rw [Finset.disjoint_left]; intro o m
        simp only [openChildAt, Selection.commit, List.toFinset_cons, List.toFinset_nil,
          insert_empty_eq, Finset.mem_insert, Finset.mem_singleton] at m
        rcases m with rfl | rfl
        · exact fresh.1
        · exact fresh.2,
     fun _ m => by simp [Selection.commit] at m⟩,
    ⟨PUnit.unit, w, solved⟩, ?_, fun _ m => (List.not_mem_nil m).elim⟩
  intro check mem _ σ solvedσ
  have checksEq : ((openChildAt ρ reflection parentToken made₁ madeTok).opened QN).checks =
      [.predicate .none (psubst ρ (pendingTok (childLoc locL channelUnknown reflP) locL)),
       .predicate .none (psubst ρ (doneTok (childLoc locL channelUnknown reflP) locL anyZ)),
       .predicate .none (psubst ρ (atLoc anyY (childLoc locL channelUnknown reflP)))] := rfl
  rw [checksEq] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  obtain ⟨lEq, -, chEq, pEq⟩ := openChild_reading label C x p l m reflection parentToken
    made₁ madeTok ρ readsRefl readsTok solvedσ
  have gEq : NameLaws (psubst σ (psubst ρ (childLoc locL channelUnknown reflP)))
      (psubst σ (childLoc l x p)) := by
    rw [psubst_childLoc, psubst_childLoc, psubst_childLoc]
    exact nameLaws_childLoc_iff.mpr ⟨lEq, chEq, pEq⟩
  have knownσ := info_known _ solvedσ
  rcases mem with rfl | rfl | rfl
  · intro o oPres same
    rw [OneFrame.row_eq] at same
    change NameLaws
      (psubst σ (psubst ρ (pendingTok (childLoc locL channelUnknown reflP) locL)))
      (psubst σ (label o)) at same
    rw [psubst_pendingTok, psubst_pendingTok] at same
    exact (clean o oPres σ knownσ).1 (psubst σ (psubst ρ locL))
      (same.symm.trans (nameLaws_pendingTok_iff.mpr ⟨gEq, NameLaws.refl _⟩))
  · intro o oPres same
    rw [OneFrame.row_eq] at same
    change NameLaws
      (psubst σ (psubst ρ (doneTok (childLoc locL channelUnknown reflP) locL anyZ)))
      (psubst σ (label o)) at same
    rw [psubst_doneTok, psubst_doneTok] at same
    exact (clean o oPres σ knownσ).2.1 (psubst σ (psubst ρ locL)) (psubst σ (psubst ρ anyZ))
      (same.symm.trans (nameLaws_doneTok_iff.mpr ⟨gEq, NameLaws.refl _, NameLaws.refl _⟩))
  · intro o oPres same
    rw [OneFrame.row_eq] at same
    change NameLaws
      (psubst σ (psubst ρ (atLoc anyY (childLoc locL channelUnknown reflP))))
      (psubst σ (label o)) at same
    rw [psubst_atLoc_any, psubst_atLoc_any] at same
    exact (clean o oPres σ knownσ).2.2 (psubst σ (psubst ρ anyY))
      (same.symm.trans ((locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨NameLaws.refl _, gEq⟩))

/-- Readouts of `made₁` and `madeTok` after `openChildAt`. -/
theorem openChild_reads (label : O → Pattern) (C : Configuration Pattern O)
    (x p l m : Pattern) (reflection parentToken made₁ madeTok : O) (ρ : PSubst)
    (readsRefl : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) l)))
    (readsTok : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label parentToken)) (psubst σ (pendingTok l m)))
    (madeDistinct : made₁ ≠ madeTok) {σ : PSubst}
    (solved : nameAction.Models σ
      (res label C (openChildAt ρ reflection parentToken made₁ madeTok)).knowledge) :
    nameAction.Models σ C.equations ∧
      NameLaws (psubst σ
        ((res label C (openChildAt ρ reflection parentToken made₁ madeTok)).label made₁))
        (psubst σ (atLoc p (childLoc l x p))) ∧
      NameLaws (psubst σ
        ((res label C (openChildAt ρ reflection parentToken made₁ madeTok)).label madeTok))
        (psubst σ (pendingTok (childLoc l x p) l)) := by
  have solvedInfo : nameAction.Models σ
      ((openChildAt ρ reflection parentToken made₁ madeTok).information QN (embed label C)) :=
    solved
  obtain ⟨lEq, -, chEq, pEq⟩ := openChild_reading label C x p l m reflection parentToken
    made₁ madeTok ρ readsRefl readsTok solvedInfo
  have gEq : NameLaws (psubst σ (psubst ρ (childLoc locL channelUnknown reflP)))
      (psubst σ (childLoc l x p)) := by
    rw [psubst_childLoc, psubst_childLoc, psubst_childLoc]
    exact nameLaws_childLoc_iff.mpr ⟨lEq, chEq, pEq⟩
  have lbl₁ : (res label C (openChildAt ρ reflection parentToken made₁ madeTok)).label made₁ =
      psubst ρ (atLoc reflP (childLoc locL channelUnknown reflP)) := by
    show (if made₁ = made₁ then _ else _) = _; rw [if_pos rfl]; rfl
  have lblT : (res label C (openChildAt ρ reflection parentToken made₁ madeTok)).label madeTok =
      psubst ρ (pendingTok (childLoc locL channelUnknown reflP) locL) := by
    show (if madeTok = made₁ then _ else if madeTok = madeTok then _ else _) = _
    rw [if_neg (Ne.symm madeDistinct), if_pos rfl]; rfl
  rw [lbl₁, lblT]
  simp only [psubst_atLoc_any, psubst_pendingTok]
  exact ⟨info_known _ solvedInfo,
    (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨pEq, gEq⟩,
    nameLaws_pendingTok_iff.mpr ⟨gEq, lEq⟩⟩

/-- **`openChildAt` enters `PendingPhaseS` at `Child(l, x, p)`.** -/
theorem openChild_enters_pending_S (label : O → Pattern) (C : Configuration Pattern O)
    (x p l m : Pattern) (reflection parentToken pr tk : O) (ρ : PSubst)
    (readsRefl : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) l)))
    (readsTok : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label parentToken)) (psubst σ (pendingTok l m)))
    (clean : Clean (childLoc l x p) label C)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (openChildAt ρ reflection parentToken pr tk)) :
    PendingPhaseS (childLoc l x p) l
      (res label C (openChildAt ρ reflection parentToken pr tk)).label
      (resConf label C (openChildAt ρ reflection parentToken pr tk)) tk := by
  obtain ⟨_, shapes, enabled, _, _, _⟩ := (RuleSyntax.admits_iff _).mp admitted
  have prTk : pr ≠ tk := by simpa [openChildAt] using shapes.2.1
  have freshPr : pr ∉ C.present := fun inside =>
    Finset.disjoint_left.mp enabled.fresh (by simp [openChildAt, Selection.commit]) inside
  refine ⟨(openChild_present label C ρ reflection parentToken pr tk tk).mpr (.inr (.inr rfl)),
    fun σ solved => (openChild_reads label C x p l m reflection parentToken pr tk ρ
      readsRefl readsTok prTk solved).2.2, ?_, ?_⟩
  · rintro o oPres ⟨σ, solved, m', same⟩
    rcases (openChild_present label C ρ reflection parentToken pr tk o).mp oPres with
      inC | isPr | isTk
    · by_cases eqTk : o = tk
      · exact eqTk
      · have nePr : o ≠ pr := fun e => freshPr (e ▸ inC)
        rw [openChild_label_old label C ρ reflection parentToken pr tk nePr eqTk] at same
        exact absurd same ((clean o inC σ (info_known _ solved)).1 m')
    · subst isPr
      have prR := (openChild_reads label C x p l m reflection parentToken o tk ρ
        readsRefl readsTok prTk solved).2.1
      have both := same.symm.trans prR; rw [psubst_atLoc_any] at both
      exact absurd (nameLaws_heads both.symm) (by decide)
    · exact isTk
  · rintro o oPres ⟨σ, solved, m', c, same⟩
    rcases (openChild_present label C ρ reflection parentToken pr tk o).mp oPres with
      inC | isPr | isTk
    · have nePr : o ≠ pr := fun e => freshPr (e ▸ inC)
      have neTk : o ≠ tk := by
        intro eqTk; subst eqTk
        have tkR := (openChild_reads label C x p l m reflection parentToken pr o ρ
          readsRefl readsTok prTk solved).2.2
        have both := same.symm.trans tkR; rw [psubst_pendingTok] at both
        exact absurd (nameLaws_heads both) (by decide)
      rw [openChild_label_old label C ρ reflection parentToken pr tk nePr neTk] at same
      exact (clean o inC σ (info_known _ solved)).2.1 m' c same
    · subst isPr
      have prR := (openChild_reads label C x p l m reflection parentToken o tk ρ
        readsRefl readsTok prTk solved).2.1
      have both := same.symm.trans prR; rw [psubst_atLoc_any] at both
      exact absurd (nameLaws_heads both) (by decide)
    · subst isTk
      have tkR := (openChild_reads label C x p l m reflection parentToken pr o ρ
        readsRefl readsTok prTk solved).2.2
      have both := same.symm.trans tkR; rw [psubst_pendingTok] at both
      exact absurd (nameLaws_heads both) (by decide)

/-- Solutions extend across `openChildAt`. -/
theorem openChild_extends (label : O → Pattern) (C : Configuration Pattern O)
    (x p l m : Pattern) (reflection parentToken made₁ madeTok : O)
    (readsRefl : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) l)))
    (readsTok : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label parentToken)) (psubst σ (pendingTok l m)))
    (presentR : reflection ∈ C.present) (presentT : parentToken ∈ C.present)
    {ρ : PSubst}
    (opensFreshly : (openChildAt ρ reflection parentToken made₁ madeTok).Fresh QN (embed label C))
    {τ : PSubst} (known : nameAction.Models τ C.equations) :
    ∃ w : PSubst,
      nameAction.Models w
        (resConf label C (openChildAt ρ reflection parentToken made₁ madeTok)).equations ∧
      ∀ o ∈ C.present, NameLaws (psubst w (label o)) (psubst τ (label o)) := by
  let h : PSubst := innerCloseInstance (psubst τ x) (psubst τ p) pZero (psubst τ l) (psubst τ m)
  have hRefl : psubst h (atLoc (pReflect channelUnknown reflP) locL) =
      psubst τ (atLoc (pReflect x p) l) := by
    simp [h, innerCloseInstance, atLoc, pReflect, channelUnknown, reflP, locL, psubst,
      psubstList_eq_map]
  have hTok : psubst h (pendingTok locL locM) = psubst τ (pendingTok l m) := by
    simp [h, innerCloseInstance, pendingTok, locL, locM, psubst, psubstList_eq_map]
  obtain ⟨w, solved, onState, -⟩ := Comm.information_amalgamates_matched (Y := QN)
    (s := embed label C) (openChildAt ρ reflection parentToken made₁ madeTok) opensFreshly
    (b := PUnit.unit) τ h known
    (fun _ m => (List.not_mem_nil m).elim)
    (fun _ m => (List.not_mem_nil m).elim)
    (fun o m => by
      simp only [openChildAt, List.mem_cons, List.not_mem_nil, or_false] at m
      rcases m with rfl | rfl
      · exact presentR
      · exact presentT)
    (fun _ m => (List.not_mem_nil m).elim)
    (fun q m => by
      simp only [openChildAt, openChild, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
        List.not_mem_nil, or_false] at m
      rcases m with rfl | rfl
      · show NameLaws (psubst h (atLoc (pReflect channelUnknown reflP) locL))
            (psubst τ (label reflection))
        rw [hRefl]; exact (readsRefl τ known).symm
      · show NameLaws (psubst h (pendingTok locL locM)) (psubst τ (label parentToken))
        rw [hTok]; exact (readsTok τ known).symm)
  refine ⟨w, solved, fun o p' => ?_⟩
  have agree : NameLaws (psubst w (psubst (fun _ => none) (label o))) (psubst τ (label o)) :=
    onState (label o) (Or.inr (Or.inr ⟨o, p', rfl⟩))
  rwa [psubst_none] at agree

/-! ## Inner close (`closeChildAt`) readouts, absence guard, and child solution extensions -/

def closeChildAtX (ρ : PSubst) (reflection innerToken token made₁ madeTok : O) :
    Firing O E located PUnit.unit :=
  ⟨closeChild, closeChild_mem, PUnit.unit, ρ,
    ⟨[reflection, innerToken, token], [], [made₁, madeTok]⟩, []⟩

omit [DecidableEq O] in
theorem closeChild_fresh_exists (label : O → Pattern) (C : Configuration Pattern O)
    (reflection innerToken token made₁ madeTok : O) :
    ∃ ρ : PSubst,
      (closeChildAt ρ reflection innerToken token made₁ madeTok).Fresh QN (embed label C) := by
  obtain ⟨g, inj, avoids⟩ := Comm.exists_apart_renaming (embed label C) (ruleVars closeChild)
  refine ⟨renameBy g, ?_⟩
  change (nameFiring (closeChildAtX (renameBy g) reflection innerToken token made₁ madeTok)).Fresh
    QN (embed label C)
  exact fresh_name (Comm.fresh_of_renaming (embed label C)
    (closeChildAtX (renameBy g) reflection innerToken token made₁ madeTok) g rfl inj avoids)

/-- Readouts of `made₁` (`for(@c <- x') 0 @ l`) and `madeTok` (`Done(l, m, 0)`) after
`closeChildAt`. -/
theorem closeChild_reads (label : O → Pattern) (C : Configuration Pattern O)
    (x' p' c l m : Pattern) (reflection innerToken token made₁ madeTok : O) (ρ : PSubst)
    (readsRefl : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x' p') l)))
    (readsInner : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label innerToken)) (psubst σ (doneTok (childLoc l x' p') l c)))
    (readsTok : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label token)) (psubst σ (pendingTok l m)))
    (madeDistinct : made₁ ≠ madeTok) {σ : PSubst}
    (solved : nameAction.Models σ
      (res label C (closeChildAt ρ reflection innerToken token made₁ madeTok)).knowledge) :
    nameAction.Models σ C.equations ∧
      NameLaws (psubst σ
        ((res label C (closeChildAt ρ reflection innerToken token made₁ madeTok)).label made₁))
        (psubst σ (atLoc (pFor (tProc c) x' pZero) l)) ∧
      NameLaws (psubst σ
        ((res label C (closeChildAt ρ reflection innerToken token made₁ madeTok)).label madeTok))
        (psubst σ (doneTok l m pZero)) := by
  have solvedInfo : nameAction.Models σ
      ((closeChildAt ρ reflection innerToken token made₁ madeTok).information QN (embed label C)) :=
    solved
  have known := info_known _ solvedInfo
  have zR : (atLoc (pReflect channelUnknown reflP) locL, reflection) ∈
      (closeChildAt ρ reflection innerToken token made₁ madeTok).rule.body.take.zip
        (closeChildAt ρ reflection innerToken token made₁ madeTok).selection.taken := by
    simp [closeChildAt, closeChild]
  have zI : (doneTok (childLoc locL channelUnknown reflP) locL accC, innerToken) ∈
      (closeChildAt ρ reflection innerToken token made₁ madeTok).rule.body.take.zip
        (closeChildAt ρ reflection innerToken token made₁ madeTok).selection.taken := by
    simp [closeChildAt, closeChild]
  have zT : (pendingTok locL locM, token) ∈
      (closeChildAt ρ reflection innerToken token made₁ madeTok).rule.body.take.zip
        (closeChildAt ρ reflection innerToken token made₁ madeTok).selection.taken := by
    simp [closeChildAt, closeChild]
  have rR := (take_reads _ solvedInfo zR).trans (readsRefl σ known)
  have rI := (take_reads _ solvedInfo zI).trans (readsInner σ known)
  have rT := (take_reads _ solvedInfo zT).trans (readsTok σ known)
  simp only [psubst_atLoc_any, psubst_pReflect] at rR
  simp only [psubst_doneTok] at rI
  simp only [psubst_pendingTok] at rT
  obtain ⟨partsR, lEq⟩ := (locatedFrame_name.atLoc_iff _ _ _ _).mp rR
  obtain ⟨chEq, -⟩ := nameLaws_pReflect_iff.mp partsR
  obtain ⟨-, -, accEq⟩ := nameLaws_doneTok_iff.mp rI
  obtain ⟨-, mEq⟩ := nameLaws_pendingTok_iff.mp rT
  have lbl₁ :
      (res label C (closeChildAt ρ reflection innerToken token made₁ madeTok)).label made₁ =
        psubst ρ (atLoc (pFor (tProc accC) channelUnknown pZero) locL) := by
    show (if made₁ = made₁ then _ else _) = _; rw [if_pos rfl]; rfl
  have lblT :
      (res label C (closeChildAt ρ reflection innerToken token made₁ madeTok)).label madeTok =
        psubst ρ (doneTok locL locM pZero) := by
    show (if madeTok = made₁ then _ else if madeTok = madeTok then _ else _) = _
    rw [if_neg (Ne.symm madeDistinct), if_pos rfl]; rfl
  rw [lbl₁, lblT]
  simp only [psubst_atLoc_any, psubst_pFor, psubst_tProc, psubst_pZero, psubst_doneTok]
  exact ⟨known,
    (locatedFrame_name.atLoc_iff _ _ _ _).mpr
      ⟨nameLaws_pFor_iff.mpr ⟨nameLaws_tProc (ReflNames.bagLaws_of_nameLaws accEq),
        chEq, NameLaws.refl _⟩, lEq⟩,
    nameLaws_doneTok_iff.mpr ⟨lEq, mEq, NameLaws.refl _⟩⟩

/-- Read an actual nested return using its selected child and parent.
The listener uses the accumulator of the taken child token. The other
output carries the pending parent's exact stamp, now done. All three
taken slots retire, and symbolic readback holds at every result solution. -/
theorem closeChild_owned_readback (policy : ReflLocatedStep.Ownership.GuardPolicy)
    (label : O → Pattern) (C : Configuration Pattern O)
    (ledger : LocatedSubstitution.Authority.Ledger O ReflLocatedStep.Ownership.Phase)
    (ρ : PSubst) (owner child parent made next : O)
    (covered : ledger.Covers C.present) (formed : LabelForms ((Store.plain (embed label C) ledger) : Store O))
    (admitted : (ReflLocatedStep.Ownership.step (O := O) policy).Admits
      (s := (Store.plain (embed label C) ledger)) ⟨closeChildAt ρ owner child parent made next, .closeChild, rfl⟩) :
    let s : Store O := (Store.plain (embed label C) ledger)
    let f : Candidate s := ⟨closeChildAt ρ owner child parent made next, .closeChild, rfl⟩
    let after := (ReflLocatedStep.Ownership.step (O := O) policy).toStep.result f admitted
    ∃ t p, s.route child = some (.control t .done) ∧ s.route parent = some (.control p .pending) ∧
      t.owner = owner ∧ t.parent = some p.key ∧ s.childRows t.key = ∅ ∧ s.nested t.key = ∅ ∧
      after.route owner = none ∧ after.route child = none ∧ after.route parent = none ∧
      after.route made = some (.cell (some p.key)) ∧ after.route next = some (.control p .done) ∧
      (∀ σ : PSubst, ∀ body loc, ∀ slot ∈ s.region t.key,
        ¬ NameLaws (psubst σ (atLoc body loc)) (psubst σ (label slot))) ∧
      ∀ σ : PSubst, nameAction.Models σ after.raw.knowledge →
        let x := psubst σ (psubst ρ channelUnknown)
        let b := psubst σ (psubst ρ reflP)
        let l := psubst σ (psubst ρ locL)
        let m := psubst σ (psubst ρ locM)
        let c := psubst σ (psubst ρ accC)
        nameAction.Models σ C.equations ∧
        NameLaws (psubst σ (label owner)) (atLoc (pReflect x b) l) ∧
        NameLaws (psubst σ (label child)) (doneTok (childLoc l x b) l c) ∧
        NameLaws (psubst σ (label parent)) (pendingTok l m) ∧
        NameLaws (psubst σ (after.raw.label made)) (atLoc (pFor (tProc c) x pZero) l) ∧
        NameLaws (psubst σ (after.raw.label next)) (doneTok l m pZero) := by
  intro s f after
  obtain ⟨out, plan⟩ : ∃ out, f.plan = some out := Option.isSome_iff_exists.mp admitted.2.1
  obtain ⟨t, p, childMark, parentMark, owns, home, _, _, packed, nested, _, planTags⟩ :=
    (ReflLocatedStep.Ownership.close_child_plan_eq_iff s owner child parent made next out).mp plan
  have moved : after = ReflLocatedStep.Ownership.update f #v[.cell (some p.key), .control p .done] := by
    have result := ReflLocatedStep.Ownership.routed_result (policy := policy) admitted plan
    exact result.trans (congrArg (ReflLocatedStep.Ownership.update f) planTags)
  have retire (slot : O) (selected : slot ∈ [owner, child, parent]) : after.route slot = none :=
    ReflLocatedStep.Ownership.result_taken_unmarked (policy := policy) admitted covered selected
  have writes {slot : O} {tag : Mark O}
      (paired : (slot, tag) ∈ [made, next].zip ([.cell (some p.key), .control p .done] : List (Mark O))) :
      after.route slot = some tag := by
    rw [moved]
    exact LocatedSubstitution.Authority.Ledger.mark_installed ledger C.present _ admitted.1.1.2.2.1 paired
  refine ⟨t, p, childMark, parentMark, owns, home, packed, nested,
    retire owner (by simp), retire child (by simp), retire parent (by simp),
    writes (by simp), writes (by simp), ?_, ?_⟩
  · intro σ body loc
    apply (ReflLocatedStep.Ownership.region_row_absence_iff formed t.key σ body loc).mp
    rw [packed]
    simp
  · have raw : after.raw = res label C (closeChildAt ρ owner child parent made next) :=
      ReflLocatedStep.Ownership.raw_result (policy := policy) admitted
    rw [raw]
    intro σ solved
    let g := closeChildAt ρ owner child parent made next
    have ownerRead := (take_reads g solved (t := atLoc (pReflect channelUnknown reflP) locL) (o := owner)
      (by simp [g, closeChildAt, closeChild])).symm
    have childRead := (take_reads g solved (t := doneTok (childLoc locL channelUnknown reflP) locL accC) (o := child)
      (by simp [g, closeChildAt, closeChild])).symm
    have parentRead := (take_reads g solved (t := pendingTok locL locM) (o := parent)
      (by simp [g, closeChildAt, closeChild])).symm
    have madeLabel : (res label C g).label made = psubst ρ (atLoc (pFor (tProc accC) channelUnknown pZero) locL) :=
      ReflLocatedStep.result_label_made_from_shapes admitted.1.1 (by simp [closeChildAt, closeChild])
    have nextLabel : (res label C g).label next = psubst ρ (doneTok locL locM pZero) :=
      ReflLocatedStep.result_label_made_from_shapes admitted.1.1 (by simp [closeChildAt, closeChild])
    refine ⟨info_known g solved, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [g, closeChildAt, psubst_atLoc_any, psubst_pReflect] using ownerRead
    · simpa only [g, closeChildAt, psubst_doneTok, psubst_childLoc] using childRead
    · simpa only [g, closeChildAt, psubst_pendingTok] using parentRead
    · change NameLaws (psubst σ ((res label C g).label made)) _
      rw [madeLabel]
      simp only [psubst_atLoc_any, psubst_pFor, psubst_tProc, psubst_pZero]
      exact NameLaws.refl _
    · change NameLaws (psubst σ ((res label C g).label next)) _
      rw [nextLabel]
      simp only [psubst_doneTok, psubst_pZero]
      exact NameLaws.refl _

/-- **`closeChildAt` waits until no row remains at the grandchild `Child(l, x', p')`.** -/
theorem closeChild_waits (label : O → Pattern) (C : Configuration Pattern O)
    (x' p' l : Pattern) (reflection innerToken token made₁ madeTok : O) (ρ : PSubst)
    (readsRefl : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x' p') l)))
    {o : O} (oPres : o ∈ C.present) {y : Pattern}
    (atGrandchild : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label o)) (psubst σ (atLoc y (childLoc l x' p'))))
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (closeChildAt ρ reflection innerToken token made₁ madeTok)) : False := by
  obtain ⟨σ, solved⟩ := solution_of_admitted admitted
  have known := info_known _ solved
  have zR : (atLoc (pReflect channelUnknown reflP) locL, reflection) ∈
      (closeChildAt ρ reflection innerToken token made₁ madeTok).rule.body.take.zip
        (closeChildAt ρ reflection innerToken token made₁ madeTok).selection.taken := by
    simp [closeChildAt, closeChild]
  have rR := (take_reads _ solved zR).trans (readsRefl σ known)
  simp only [psubst_atLoc_any, psubst_pReflect] at rR
  obtain ⟨partsR, lEq⟩ := (locatedFrame_name.atLoc_iff _ _ _ _).mp rR
  obtain ⟨chEq, pEq⟩ := nameLaws_pReflect_iff.mp partsR
  have gEq : NameLaws (psubst σ (psubst ρ (childLoc locL channelUnknown reflP)))
      (psubst σ (childLoc l x' p')) := by
    rw [psubst_childLoc, psubst_childLoc, psubst_childLoc]
    exact nameLaws_childLoc_iff.mpr ⟨lEq, chEq, pEq⟩
  have rAt : NameLaws (psubst σ (label o)) (atLoc (psubst σ y) (psubst σ (childLoc l x' p'))) := by
    simpa [psubst_atLoc_any] using atGrandchild σ known
  exact check_fails_row_at admitted (by simp [closeChildAt, closeChild]) rfl
    (by change ∀ t ∈ closeChild.body.take, "Y" ∉ pvars t; decide)
    (by change ∀ t ∈ closeChild.body.read, "Y" ∉ pvars t; decide)
    (by decide) solved gEq oPres rAt

/-- Solutions extend across `coolAt`. -/
theorem cool_extends (label : O → Pattern) (C : Configuration Pattern O) (l m c a : Pattern)
    (d r d₁ : O)
    (readsTok : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label d)) (psubst σ (doneTok l m c)))
    (readsRow : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label r)) (psubst σ (atLoc a l)))
    (presentD : d ∈ C.present) (presentR : r ∈ C.present)
    {ρ : PSubst} (opensFreshly : (coolAt ρ d r d₁).Fresh QN (embed label C))
    {τ : PSubst} (known : nameAction.Models τ C.equations) :
    ∃ w : PSubst, nameAction.Models w (resConf label C (coolAt ρ d r d₁)).equations ∧
      ∀ o ∈ C.present, NameLaws (psubst w (label o)) (psubst τ (label o)) := by
  let h : PSubst := coolInstance (psubst τ l) (psubst τ m) (psubst τ c) (psubst τ a)
  have hTok : psubst h (doneTok locL locM accC) = psubst τ (doneTok l m c) := by
    simp [h, coolInstance, doneTok, locL, locM, accC, psubst, psubstList_eq_map]
  have hRow : psubst h (atLoc leftPart locL) = psubst τ (atLoc a l) := by
    simp [h, coolInstance, atLoc, leftPart, locL, psubst, psubstList_eq_map]
  obtain ⟨w, solved, onState, -⟩ := Comm.information_amalgamates_matched (Y := QN)
    (s := embed label C) (coolAt ρ d r d₁) opensFreshly (b := PUnit.unit) τ h known
    (fun _ m => (List.not_mem_nil m).elim)
    (fun o m => by
      simp only [coolAt, List.mem_cons, List.not_mem_nil, or_false] at m
      rcases m with rfl | rfl
      · exact presentD
      · exact presentR)
    (fun _ m => (List.not_mem_nil m).elim)
    (fun q m => by
      simp only [coolAt, cool, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
        List.not_mem_nil, or_false] at m
      rcases m with rfl | rfl
      · show NameLaws (psubst h (doneTok locL locM accC)) (psubst τ (label d))
        rw [hTok]; exact (readsTok τ known).symm
      · show NameLaws (psubst h (atLoc leftPart locL)) (psubst τ (label r))
        rw [hRow]; exact (readsRow τ known).symm)
    (fun _ m => (List.not_mem_nil m).elim)
  refine ⟨w, solved, fun o p' => ?_⟩
  have agree : NameLaws (psubst w (psubst (fun _ => none) (label o))) (psubst τ (label o)) :=
    onState (label o) (Or.inr (Or.inr ⟨o, p', rfl⟩))
  rwa [psubst_none] at agree

/-- Solutions extend across `closeRootAt`. -/
theorem closeRoot_extends (label : O → Pattern) (C : Configuration Pattern O) (x p c : Pattern)
    (reflection token made₁ : O)
    (readsRefl : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) rootLoc)))
    (readsTok : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label token)) (psubst σ (doneTok (childLoc rootLoc x p) rootLoc c)))
    (presentR : reflection ∈ C.present) (presentT : token ∈ C.present)
    {ρ : PSubst} (opensFreshly : (closeRootAt ρ reflection token made₁).Fresh QN (embed label C))
    {τ : PSubst} (known : nameAction.Models τ C.equations) :
    ∃ w : PSubst, nameAction.Models w (resConf label C (closeRootAt ρ reflection token made₁)).equations ∧
      ∀ o ∈ C.present, NameLaws (psubst w (label o)) (psubst τ (label o)) := by
  let h : PSubst := closeInstance (psubst τ x) (psubst τ p) (psubst τ c)
  have hRefl : psubst h (atLoc (pReflect channelUnknown reflP) rootLoc) =
      psubst τ (atLoc (pReflect x p) rootLoc) := by
    simp [h, closeInstance, atLoc, pReflect, channelUnknown, reflP, rootLoc, psubst,
      psubstList_eq_map]
  have hTok : psubst h (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC) =
      psubst τ (doneTok (childLoc rootLoc x p) rootLoc c) := by
    simp [h, closeInstance, doneTok, childLoc, channelUnknown, reflP, rootLoc, accC, psubst,
      psubstList_eq_map]
  obtain ⟨w, solved, onState, -⟩ := Comm.information_amalgamates_matched (Y := QN)
    (s := embed label C) (closeRootAt ρ reflection token made₁) opensFreshly (b := PUnit.unit)
    τ h known
    (fun _ m => (List.not_mem_nil m).elim)
    (fun o m => by
      simp only [closeRootAt, List.mem_cons, List.not_mem_nil, or_false] at m
      rcases m with rfl | rfl
      · exact presentR
      · exact presentT)
    (fun _ m => (List.not_mem_nil m).elim)
    (fun q m => by
      simp only [closeRootAt, closeRoot, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
        List.not_mem_nil, or_false] at m
      rcases m with rfl | rfl
      · show NameLaws (psubst h (atLoc (pReflect channelUnknown reflP) rootLoc))
            (psubst τ (label reflection))
        rw [hRefl]; exact (readsRefl τ known).symm
      · show NameLaws (psubst h (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC))
            (psubst τ (label token))
        rw [hTok]; exact (readsTok τ known).symm)
    (fun _ m => (List.not_mem_nil m).elim)
  refine ⟨w, solved, fun o p' => ?_⟩
  have agree : NameLaws (psubst w (psubst (fun _ => none) (label o))) (psubst τ (label o)) :=
    onState (label o) (Or.inr (Or.inr ⟨o, p', rfl⟩))
  rwa [psubst_none] at agree

/-- A written child COMM spends the selected pending token, publishes the
authored reducts in that ticket's physical region, and installs the same
ticket as done. The source reaction uses the actual selected binding
and is independent of any extra solutions of the quotient match. -/
theorem commChild_written_readback (policy : ReflLocatedStep.Ownership.GuardPolicy)
    (label : O → Pattern) (C : Configuration Pattern O)
    (ledger : LocatedSubstitution.Authority.Ledger O ReflLocatedStep.Ownership.Phase)
    (authored : Store O → Option O → List (O × Pattern))
    (ρ : PSubst) (first second token m₁ m₂ done : O)
    (ticket : LocatedSubstitution.Authority.Ticket O) (t u x y A B : Pattern)
    (tokenMark : ledger.mark token = some (.control ticket .pending))
    (covered : ledger.Covers C.present)
    (leftAt : (authored (Store.plain (embed label C) ledger) (some ticket.key)).lookup first = some (pFor t x A))
    (rightAt : (authored (Store.plain (embed label C) ledger) (some ticket.key)).lookup second = some (pFor u y B))
    (admitted : (withWrittenComm policy authored).Admits (s := (Store.plain (embed label C) ledger))
      ⟨commChildAt ρ first second token m₁ m₂ done, .childComm, rfl⟩) :
    let s : Store O := (Store.plain (embed label C) ledger)
    let f : Candidate s := ⟨commChildAt ρ first second token m₁ m₂ done, .childComm, rfl⟩
    let after := (withWrittenComm policy authored).result f admitted
    ∃ bs, ReflLocatedStep.Ownership.writtenBinding (authored s) f = some bs ∧
      let completed := MeTTaCalculus.Corrected.completeBindings (pvars t ++ pvars u) bs
      BagStep conventional (par (pFor t x A) (pFor u y B)) (par (applyDot completed A) (applyDot completed B)) ∧
      after.route token = none ∧ after.route m₁ = some (.cell (some ticket.key)) ∧
        after.route m₂ = some (.cell (some ticket.key)) ∧ after.route done = some (.control ticket .done) ∧
      ∀ σ : PSubst, nameAction.Models σ after.raw.knowledge →
        let l := psubst σ (psubst ρ locL)
        let m := psubst σ (psubst ρ locM)
        nameAction.Models σ C.equations ∧
        NameLaws (psubst σ (label token)) (pendingTok l m) ∧
        NameLaws (psubst σ (after.raw.label m₁)) (atLoc (psubst σ (predotU (applyDot completed A))) l) ∧
        NameLaws (psubst σ (after.raw.label m₂)) (atLoc (psubst σ (predotU (applyDot completed B))) l) ∧
        NameLaws (psubst σ (after.raw.label done)) (doneTok l m pZero) := by
  intro s f after
  obtain ⟨armed, permitted⟩ := (written_comm_admits_iff policy authored f).mp admitted
  obtain ⟨bs, receipt⟩ := Option.isSome_iff_exists.mp permitted
  have checked := writtenBinding_child (authored s) (f := f) rfl rfl tokenMark leftAt rightAt
  rw [checked] at receipt
  obtain ⟨rfl, apart, found⟩ := (writtenComm_pFor_iff t x A u y B bs).mp receipt
  let completed := MeTTaCalculus.Corrected.completeBindings (pvars t ++ pvars u) bs
  have principal := MeTTaCalculus.Corrected.principal_completeBindings
    (MeTTaCalculus.Corrected.unify_principal found)
  have tells := (readWrittenPair_child (authored s) (f := f)
    (writtenPairTells f.raw.opening) rfl rfl tokenMark leftAt rightAt).trans (writtenPairTells_at ρ receipt)
  have base := ReflLocatedStep.Ownership.admits_without_comm_tells policy _ (Or.inr rfl) armed
  have shapes := base.1.1
  obtain ⟨out, plan⟩ := Option.isSome_iff_exists.mp armed.2.1
  obtain ⟨actual, selected, _, made⟩ := (child_comm_plan_iff s first second token m₁ m₂ done out).mp plan
  have same : actual = ticket := by
    change ledger.mark token = some (.control actual .pending) at selected
    rw [tokenMark] at selected
    exact (LocatedSubstitution.Authority.Mark.control.inj (Option.some.inj selected)).1.symm
  subst actual
  subst out
  have moved := ReflLocatedStep.Ownership.written_routed_result authored admitted plan
  have marksSame : after.ledger = ((ReflLocatedStep.Ownership.step policy).toStep.result f base).ledger :=
    (congrArg Store.ledger moved).trans
      ((congrArg Store.ledger (ReflLocatedStep.Ownership.routed_result base plan)).symm)
  have retired : after.route token = none := by
    change after.ledger.mark token = none
    rw [marksSame]
    exact ReflLocatedStep.Ownership.result_taken_unmarked base covered (by simp [f, commChildAt])
  have writes {slot : O} {tag : Mark O}
      (paired : (slot, tag) ∈ [m₁, m₂, done].zip
        ([.cell (some ticket.key), .cell (some ticket.key), .control ticket .done] : List (Mark O))) :
      after.route slot = some tag := by
    change ((withWrittenComm policy authored).result f admitted).route slot = _
    rw [moved]
    exact LocatedSubstitution.Authority.Ledger.mark_installed ledger C.present _ shapes.2.2.1 paired
  refine ⟨bs, checked.trans receipt, .comm t u x A B completed principal apart,
    retired, writes (by simp), writes (by simp), writes (by simp), ?_⟩
  intro σ solved
  have raw := (written_result_models policy authored admitted solved).1
  let g := commChildAt ρ first second token m₁ m₂ done
  have tok := (take_reads g raw (t := pendingTok locL locM) (o := token) (by simp [g, commChildAt, commChild])).symm
  have left : (res label C g).label m₁ = psubst ρ (atLoc firstBody locL) :=
    ReflLocatedStep.result_label_made_from_shapes (g := g) shapes (t := atLoc firstBody locL)
      (by simp [g, commChildAt, commChild])
  have right : (res label C g).label m₂ = psubst ρ (atLoc secondBody locL) :=
    ReflLocatedStep.result_label_made_from_shapes (g := g) shapes (t := atLoc secondBody locL)
      (by simp [g, commChildAt, commChild])
  have stamp : (res label C g).label done = psubst ρ (doneTok locL locM pZero) :=
    ReflLocatedStep.result_label_made_from_shapes (g := g) shapes (t := doneTok locL locM pZero)
      (by simp [g, commChildAt, commChild])
  obtain ⟨readA, readB⟩ := written_result_publications policy authored admitted tells left right solved
  refine ⟨info_known g raw, ?_, readA, readB, ?_⟩
  · simpa only [g, commChildAt, psubst_pendingTok] using tok
  · change NameLaws (psubst σ ((res label C g).label done)) _
    rw [stamp]
    simp only [psubst_doneTok, psubst_pZero]
    exact NameLaws.refl _

/-- Solutions extend across `closeChildAt`. -/
theorem closeChild_extends (label : O → Pattern) (C : Configuration Pattern O)
    (x' p' c l m : Pattern) (reflection innerToken token made₁ madeTok : O)
    (readsRefl : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x' p') l)))
    (readsInner : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label innerToken)) (psubst σ (doneTok (childLoc l x' p') l c)))
    (readsTok : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label token)) (psubst σ (pendingTok l m)))
    (presentR : reflection ∈ C.present) (presentI : innerToken ∈ C.present)
    (presentT : token ∈ C.present) {ρ : PSubst}
    (opensFreshly : (closeChildAt ρ reflection innerToken token made₁ madeTok).Fresh QN
      (embed label C))
    {τ : PSubst} (known : nameAction.Models τ C.equations) :
    ∃ w : PSubst,
      nameAction.Models w
        (resConf label C (closeChildAt ρ reflection innerToken token made₁ madeTok)).equations ∧
      ∀ o ∈ C.present, NameLaws (psubst w (label o)) (psubst τ (label o)) := by
  let h : PSubst := innerCloseInstance (psubst τ x') (psubst τ p') (psubst τ c)
    (psubst τ l) (psubst τ m)
  have hR : psubst h (atLoc (pReflect channelUnknown reflP) locL) =
      psubst τ (atLoc (pReflect x' p') l) := by
    simp [h, innerCloseInstance, atLoc, pReflect, channelUnknown, reflP, locL, psubst,
      psubstList_eq_map]
  have hI : psubst h (doneTok (childLoc locL channelUnknown reflP) locL accC) =
      psubst τ (doneTok (childLoc l x' p') l c) := by
    simp [h, innerCloseInstance, doneTok, childLoc, channelUnknown, reflP, locL, accC, psubst,
      psubstList_eq_map]
  have hT : psubst h (pendingTok locL locM) = psubst τ (pendingTok l m) := by
    simp [h, innerCloseInstance, pendingTok, locL, locM, psubst, psubstList_eq_map]
  obtain ⟨w, solved, onState, -⟩ := Comm.information_amalgamates_matched (Y := QN)
    (s := embed label C) (closeChildAt ρ reflection innerToken token made₁ madeTok) opensFreshly
    (b := PUnit.unit) τ h known
    (fun _ m => (List.not_mem_nil m).elim)
    (fun o m => by
      simp only [closeChildAt, List.mem_cons, List.not_mem_nil, or_false] at m
      rcases m with rfl | rfl | rfl
      · exact presentR
      · exact presentI
      · exact presentT)
    (fun _ m => (List.not_mem_nil m).elim)
    (fun q m => by
      simp only [closeChildAt, closeChild, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
        List.not_mem_nil, or_false] at m
      rcases m with rfl | rfl | rfl
      · show NameLaws (psubst h (atLoc (pReflect channelUnknown reflP) locL))
            (psubst τ (label reflection))
        rw [hR]; exact (readsRefl τ known).symm
      · show NameLaws (psubst h (doneTok (childLoc locL channelUnknown reflP) locL accC))
            (psubst τ (label innerToken))
        rw [hI]; exact (readsInner τ known).symm
      · show NameLaws (psubst h (pendingTok locL locM)) (psubst τ (label token))
        rw [hT]; exact (readsTok τ known).symm)
    (fun _ m => (List.not_mem_nil m).elim)
  refine ⟨w, solved, fun o p' => ?_⟩
  have agree : NameLaws (psubst w (psubst (fun _ => none) (label o))) (psubst τ (label o)) :=
    onState (label o) (Or.inr (Or.inr ⟨o, p', rfl⟩))
  rwa [psubst_none] at agree

/-- Solutions unifying `t` and `u` extend across `commChildAt`. -/
theorem commChild_extends (label : O → Pattern) (C : Configuration Pattern O)
    (t u channel K₁ K₂ l m : Pattern) (first second token made₁ made₂ madeTok : O)
    (readsFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (atLoc (pFor t channel K₁) l)))
    (readsSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (atLoc (pFor u channel K₂) l)))
    (readsTok : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label token)) (psubst σ (pendingTok l m)))
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present) (presentT : token ∈ C.present)
    {ρ : PSubst}
    (opensFreshly : (commChildAt ρ first second token made₁ made₂ madeTok).Fresh QN (embed label C))
    {τ : PSubst} (known : nameAction.Models τ C.equations)
    (unifies : NameLaws (psubst τ t) (psubst τ u)) :
    ∃ w : PSubst,
      nameAction.Models w
        (resConf label C (commChildAt ρ first second token made₁ made₂ madeTok)).equations ∧
      ∀ o ∈ C.present, NameLaws (psubst w (label o)) (psubst τ (label o)) := by
  let h : PSubst := childInstance (psubst τ t) (psubst τ u) (psubst τ channel)
    (psubst τ K₁) (psubst τ K₂) (psubst τ l) (psubst τ m)
  have hT₁ : psubst h (atLoc (pFor firstPattern channelUnknown firstBody) locL) =
      psubst τ (atLoc (pFor t channel K₁) l) := by
    simp [h, childInstance, atLoc, pFor, firstPattern, channelUnknown, firstBody, locL, psubst,
      psubstList_eq_map]
  have hT₂ : psubst h (atLoc (pFor secondPattern channelUnknown secondBody) locL) =
      psubst τ (atLoc (pFor u channel K₂) l) := by
    simp [h, childInstance, atLoc, pFor, secondPattern, channelUnknown, secondBody, locL, psubst,
      psubstList_eq_map]
  have hTok : psubst h (pendingTok locL locM) = psubst τ (pendingTok l m) := by
    simp [h, childInstance, pendingTok, locL, locM, psubst, psubstList_eq_map]
  have hEq : psubst h (atLoc firstPattern locL) = atLoc (psubst τ t) (psubst τ l) ∧
      psubst h (atLoc secondPattern locL) = atLoc (psubst τ u) (psubst τ l) := by
    constructor <;>
      simp [h, childInstance, atLoc, firstPattern, secondPattern, locL, psubst, psubstList_eq_map]
  obtain ⟨w, solved, onState, -⟩ := Comm.information_amalgamates_matched (Y := QN)
    (s := embed label C) (commChildAt ρ first second token made₁ made₂ madeTok) opensFreshly
    (b := PUnit.unit) τ h known
    (fun e m => by
      obtain rfl := List.mem_singleton.mp m
      show NameLaws (psubst h (atLoc firstPattern locL)) (psubst h (atLoc secondPattern locL))
      rw [hEq.1, hEq.2]
      exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨unifies, NameLaws.refl _⟩)
    (fun o m => by
      simp only [commChildAt, List.mem_cons, List.not_mem_nil, or_false] at m
      rcases m with rfl | rfl | rfl
      · exact present₁
      · exact present₂
      · exact presentT)
    (fun _ m => (List.not_mem_nil m).elim)
    (fun q m => by
      simp only [commChildAt, commChild, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
        List.not_mem_nil, or_false] at m
      rcases m with rfl | rfl | rfl
      · show NameLaws (psubst h (atLoc (pFor firstPattern channelUnknown firstBody) locL))
            (psubst τ (label first))
        rw [hT₁]; exact (readsFirst τ known).symm
      · show NameLaws (psubst h (atLoc (pFor secondPattern channelUnknown secondBody) locL))
            (psubst τ (label second))
        rw [hT₂]; exact (readsSecond τ known).symm
      · show NameLaws (psubst h (pendingTok locL locM)) (psubst τ (label token))
        rw [hTok]; exact (readsTok τ known).symm)
    (fun _ m => (List.not_mem_nil m).elim)
  refine ⟨w, solved, fun o p' => ?_⟩
  have agree : NameLaws (psubst w (psubst (fun _ => none) (label o))) (psubst τ (label o)) :=
    onState (label o) (Or.inr (Or.inr ⟨o, p', rfl⟩))
  rwa [psubst_none] at agree

end NonRootAndOpenClose

#print axioms rootCells_keep_noRootRun
#print axioms noRootRun_to_rootChildRunS
#print axioms rootCells_closeRoot_N
#print axioms rootCells_closeRoot_C
#print axioms rootCells_refl_comm_backward
#print axioms openChild_admitted
#print axioms openChild_reads
#print axioms openChild_enters_pending_S
#print axioms openChild_extends
#print axioms closeChild_reads
#print axioms closeChild_waits
#print axioms cool_extends
#print axioms closeRoot_extends
#print axioms closeChild_extends
#print axioms commChild_extends

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem
