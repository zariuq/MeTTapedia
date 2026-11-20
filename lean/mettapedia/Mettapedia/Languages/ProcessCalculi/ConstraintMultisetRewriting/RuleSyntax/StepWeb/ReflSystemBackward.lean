import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystemBackwardState

/-!
# Whole-system arbitrary-interleaving backward reflection (`P5` backward)

This module proves the single-firing and multi-step backward stuttering reflection theorems (`P5`)
at the name frame `QN` across all 10 rule schemas of `ReflLocated.located`, arbitrary location
interleavings, repeated child epochs, and dead locations (`¬ Live`):

* **`located_firing_backward_N`** and **`located_firing_backward_C`**: every admitted firing `g` of
  `located` at `QN` from a `BackwardReadyN` / `BackwardReadyC` state in `SystemInvBy` is either
  `Administrative` (preserving `SystemInvN` / `SystemInvC` with the **same** source process `P`) or
  `RootVisible` (`rootComm` or `closeRoot`, producing `P'` with `BagStep conventional P P'` /
  `CanonicalBagStep conventional P P'` and `SystemInvN ... P'` / `SystemInvC ... P'`).
* **`located_run_backward_N`** and **`located_run_backward_C`**: multi-step runs reflect to
  `Relation.ReflTransGen (BagStep conventional)` and
  `Relation.ReflTransGen (CanonicalBagStep conventional)`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar tProc pReflect applyDot)
open MeTTaOperationsComm (psubst PSubst pvars psubst_pFor psubst_tProc commSelection GroundPrincipal)
open MeTTaCalculus.Corrected (BagEq BagStep CanonicalBagStep conventional listener)
open FiniteProgram (commRule heatRule clearRule firstPattern secondPattern channelUnknown firstBody
  secondBody)
open OneFrame (embed)
open ReflQuotient (BagLaws bagLaws_psubst)
open ReflNames (NameLaws nameAction QN QNE nameLaws_heads nameLaws_pFor_iff nameLaws_tProc
  nameLaws_psubst commAtN)
open ReflLocated (atLoc rootLoc childLoc pendingTok doneTok locL locM reflP accC atRule located
  commChild heatChild heatChildN cool closeRoot closeChild openRoot openChild exists_mem_zip
  psubst_rootLoc psubst_atLoc_any psubst_pendingTok locatedFrame_name rootFiring widen atFiring
  heatN)
open ReflPacking (cooled bagLaws_cooled_zero psubst_doneTok nameLaws_doneTok_iff)
open ReflLocatedStep (located_cases psubst_childLoc nameLaws_pendingTok_iff nameLaws_childLoc_iff
  res resConf info_known take_reads read_reads taken_row solution_of_admitted result_row
  commChildAt closeChildAt psubst_pReflect nameLaws_pReflect_iff openRoot_checks openChild_checks)
open ReflUniform (predotU predotU_pPar predotU_ground)
open ReflCorrespondence (openRootAt closeRootAt openRoot_reads closeRoot_reads closeRoot_waits
  quote_closed_ground)

/-! ## Individual rule transitions preserving `SystemInvBy` -/

section RuleSteps

variable {O : Type*} [DecidableEq O]

private theorem step_rootHeat {StepRel : Pattern → Pattern → Prop}
    {label : O → Pattern} {C : Configuration Pattern O} {P : Pattern}
    {rootRows : List (O × Pattern)} {active : List (ActiveEntry O)}
    (sys : SystemInvBy StepRel label C P rootRows active)
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (rEq : g.rule = atRule rootLoc heatRule) :
    SystemInv StepRel (res label C g).label (resConf label C g) P := by
  obtain ⟨o, m₁, m₂, gEq, -⟩ := eq_rootHeatAt admitted rEq
  rw [gEq] at admitted ⊢
  obtain ⟨rows', rInv', rNodes', bEq, memIff⟩ :=
    rootCells_heat_node_reflects sys.rootInv sys.rootNodes admitted
  refine ⟨rows', active, solution_of_admitted admitted,
    noRootTokens_preserved sys.noRootTok _ admitted, rInv', rNodes', bEq.trans sys.rootBag,
    fun e eIn => (active_keep_nonChildRule (sys.activeValid e eIn) admitted (.inr (.inl rfl))).1,
    sys.activeApart.imp (apartOn_mono _), fun z zP => ?_⟩
  rcases result_row zP with made | ⟨old, notT, -, -⟩
  · simp only [rootHeatAt, rootFiring, widen, atFiring, heatN, List.mem_cons, List.not_mem_nil, or_false] at made
    exact .inl ((memIff z).mpr (.inr made))
  · have neO : z ≠ o := fun e => notT (by simp [rootHeatAt, rootFiring, widen, atFiring, heatN, e])
    rcases sys.presentCover z old with inR | inA
    · exact .inl ((memIff z).mpr (.inl ⟨inR, neO⟩))
    · exact .inr inA

private theorem step_rootClear {StepRel : Pattern → Pattern → Prop}
    {label : O → Pattern} {C : Configuration Pattern O} {P : Pattern}
    {rootRows : List (O × Pattern)} {active : List (ActiveEntry O)}
    (sys : SystemInvBy StepRel label C P rootRows active)
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (rEq : g.rule = atRule rootLoc clearRule) :
    SystemInv StepRel (res label C g).label (resConf label C g) P := by
  obtain ⟨o, gEq, -⟩ := eq_rootClearAt admitted rEq
  rw [gEq] at admitted ⊢
  obtain ⟨rows', rInv', rNodes', bEq, memIff⟩ :=
    rootCells_clear_node_reflects sys.rootInv sys.rootNodes admitted
  refine ⟨rows', active, solution_of_admitted admitted,
    noRootTokens_preserved sys.noRootTok _ admitted, rInv', rNodes', bEq.trans sys.rootBag,
    fun e eIn => (active_keep_nonChildRule (sys.activeValid e eIn) admitted (.inr (.inr (.inl rfl)))).1,
    sys.activeApart.imp (apartOn_mono _), fun z zP => ?_⟩
  rcases result_row zP with made | ⟨old, notT, -, -⟩
  · simp [rootClearAt, rootFiring, widen, atFiring, clearN] at made
  · have neO : z ≠ o := fun e => notT (by simp [rootClearAt, rootFiring, widen, atFiring, clearN, e])
    rcases sys.presentCover z old with inR | inA
    · exact .inl ((memIff z).mpr ⟨inR, neO⟩)
    · exact .inr inA

private theorem step_rootComm {StepRel : Pattern → Pattern → Prop}
    {label : O → Pattern} {C : Configuration Pattern O} {P : Pattern}
    {rootRows : List (O × Pattern)} {active : List (ActiveEntry O)}
    (sys : SystemInvBy StepRel label C P rootRows active)
    (commReady : ∀ q₁ ∈ rootRows, ∀ q₂ ∈ rootRows, ∀ t ch A u ch' B : Pattern,
      q₁.1 ≠ q₂.1 → q₁.2 = pFor t ch A → q₂.2 = pFor u ch' B → CommAdmissibleN t ch A u ch' B)
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (rEq : g.rule = atRule rootLoc commRule) :
    ∃ P', BagStep conventional P P' ∧ CanonicalBagStep conventional P P' ∧
      SystemInv StepRel (res label C g).label (resConf label C g) P' := by
  obtain ⟨first, second, m₁, m₂, gEq, distinct, -, p₁, p₂, -⟩ := eq_rootCommAt admitted rEq
  rw [gEq] at admitted ⊢
  obtain ⟨σ₀, sol₀⟩ := solution_of_admitted admitted
  have known₀ := info_known _ sol₀
  have z₁ : (atLoc (pFor firstPattern channelUnknown firstBody) rootLoc, first) ∈
      (rootCommAt g.opening first second m₁ m₂).rule.body.take.zip
        (rootCommAt g.opening first second m₁ m₂).selection.taken := by
    simp [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, atRule, commRule, RuleInstance.map]
  have z₂ : (atLoc (pFor secondPattern channelUnknown secondBody) rootLoc, second) ∈
      (rootCommAt g.opening first second m₁ m₂).rule.body.take.zip
        (rootCommAt g.opening first second m₁ m₂).selection.taken := by
    simp [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, atRule, commRule, RuleInstance.map]
  have r₁ := take_reads _ sol₀ z₁; simp only [psubst_atLoc_any, psubst_pFor, psubst_rootLoc] at r₁
  have r₂ := take_reads _ sol₀ z₂; simp only [psubst_atLoc_any, psubst_pFor, psubst_rootLoc] at r₂
  have fIn : first ∈ rootRows.map Prod.fst := by
    by_contra notIn; exact sys.rootInv.others first p₁ notIn σ₀ known₀ _ r₁.symm
  have sIn : second ∈ rootRows.map Prod.fst := by
    by_contra notIn; exact sys.rootInv.others second p₂ notIn σ₀ known₀ _ r₂.symm
  obtain ⟨⟨f₀, Pf⟩, fMem, eqF⟩ := List.mem_map.mp fIn; subst eqF
  obtain ⟨⟨s₀, Ps⟩, sMem, eqS⟩ := List.mem_map.mp sIn; subst eqS
  have hF := r₁.trans ((sys.rootInv.rows _ fMem).2 σ₀ known₀)
  simp only [psubst_atLoc_any, psubst_rootLoc] at hF
  have hS := r₂.trans ((sys.rootInv.rows _ sMem).2 σ₀ known₀)
  simp only [psubst_atLoc_any, psubst_rootLoc] at hS
  obtain ⟨t, ch, A, rfl, -⟩ := hostedNode_match_for (sys.rootNodes _ fMem)
    ((locatedFrame_name.atLoc_iff _ _ _ _).mp hF).1
  obtain ⟨u, ch', B, rfl, -⟩ := hostedNode_match_for (sys.rootNodes _ sMem)
    ((locatedFrame_name.atLoc_iff _ _ _ _).mp hS).1
  obtain ⟨rest, pm, -⟩ := list_perm_pick2 sys.rootInv.nodup fMem sMem distinct
  have admPair := commReady _ fMem _ sMem t ch A u ch' B distinct rfl rfl
  obtain ⟨rfl, bs, _, rInv', rNodes', bStep, cStep⟩ := rootCells_comm_admissible
    (sys.rootInv.perm pm) (fun q m => sys.rootNodes q (pm.symm.subset m)) admPair admitted
  let outRows := rest ++ [(m₁, applyDot bs A), (m₂, applyDot bs B)]
  have bagPerm : BagEq P (rootBagProcess ((f₀, pFor t ch A) :: (s₀, pFor u ch B) :: rest)) :=
    sys.rootBag.symm.trans (bagEq_pPar_perm (pm.map Prod.snd))
  refine ⟨rootBagProcess outRows, .congruence bagPerm bStep (BagEq.refl _),
    .congruence bagPerm cStep (BagEq.refl _), outRows, active, ⟨σ₀, sol₀⟩,
    noRootTokens_preserved sys.noRootTok _ admitted, rInv', rNodes', BagEq.refl _,
    fun e eIn => (active_keep_nonChildRule (sys.activeValid e eIn) admitted (.inl rfl)).1,
    sys.activeApart.imp (apartOn_mono _), fun z zP => ?_⟩
  rcases result_row zP with made | ⟨old, notT, -, -⟩
  · simp only [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, List.mem_cons,
      List.not_mem_nil, or_false] at made
    exact .inl (by rcases made with rfl | rfl <;> simp [outRows])
  · have neF : z ≠ f₀ := fun e => notT (by simp [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, e])
    have neS : z ≠ s₀ := fun e => notT (by simp [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, e])
    rcases sys.presentCover z old with inR | inA
    · have inPerm := (pm.map Prod.fst).subset inR
      simp only [List.map_cons, List.mem_cons] at inPerm
      rcases inPerm with rfl | rfl | inRest
      · exact absurd rfl neF
      · exact absurd rfl neS
      · exact .inl (by simp [outRows, inRest])
    · exact .inr inA

private theorem step_openRoot {StepRel : Pattern → Pattern → Prop}
    {label : O → Pattern} {C : Configuration Pattern O} {P : Pattern}
    {rootRows : List (O × Pattern)} {active : List (ActiveEntry O)}
    (sys : SystemInvBy StepRel label C P rootRows active)
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (rEq : g.rule = openRoot) :
    SystemInv StepRel (res label C g).label (resConf label C g) P := by
  obtain ⟨r, pr, tk, gEq⟩ := eq_openRootAt admitted rEq
  rw [gEq] at admitted ⊢
  obtain ⟨_, shapes, enabled, ⟨_, w, solved⟩, -⟩ := (RuleSyntax.admits_iff _).mp admitted
  have known := info_known _ solved
  have prNeTk : pr ≠ tk := by simpa [openRootAt] using shapes.2.1
  have rPres : r ∈ C.present := enabled.kept_subset (by simp [openRootAt, Selection.commit])
  have zR : (atLoc (pReflect channelUnknown reflP) rootLoc, r) ∈
      (openRootAt g.opening r pr tk).rule.body.read.zip (openRootAt g.opening r pr tk).selection.read := by
    simp [openRootAt, openRoot]
  have rRead := read_reads _ solved zR
  simp only [psubst_atLoc_any, psubst_pReflect, psubst_rootLoc] at rRead
  have rIn : r ∈ rootRows.map Prod.fst := by
    by_contra notIn; exact sys.rootInv.others r rPres notIn w known _ rRead.symm
  obtain ⟨⟨r₀, Pr⟩, rMem, eqR⟩ := List.mem_map.mp rIn; subst eqR
  have hR := rRead.trans ((sys.rootInv.rows _ rMem).2 w known)
  simp only [psubst_atLoc_any, psubst_rootLoc] at hR
  obtain ⟨x, Q, rfl, hX, hQ⟩ := hostedNode_match_reflect (sys.rootNodes _ rMem)
    ((locatedFrame_name.atLoc_iff _ _ _ _).mp hR).1
  have rRefl : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label r₀)) (psubst σ (atLoc (pReflect x (predotU Q)) rootLoc)) := by
    intro σ s; have h := (sys.rootInv.rows _ rMem).2 σ s; rwa [predotU_pReflect, predotU_ground x hX.1] at h
  have lEq : ∀ σ : PSubst, nameAction.Models σ (resConf label C (openRootAt g.opening r₀ pr tk)).equations →
      NameLaws (psubst σ (psubst g.opening (childLoc rootLoc channelUnknown reflP)))
        (psubst σ (childLoc rootLoc x (predotU Q))) := by
    intro σ s
    have h := (read_reads _ s zR).trans (rRefl σ (info_known _ s))
    simp only [psubst_atLoc_any, psubst_pReflect, psubst_rootLoc] at h
    obtain ⟨chEq, qEq⟩ := nameLaws_pReflect_iff.mp ((locatedFrame_name.atLoc_iff _ _ _ _).mp h).1
    rw [psubst_childLoc, psubst_childLoc, psubst_childLoc, psubst_rootLoc, psubst_rootLoc]
    exact nameLaws_childLoc_iff.mpr ⟨NameLaws.refl _, chEq, qEq⟩
  obtain ⟨apartE, cleanPost⟩ := open_apart_and_clean sys admitted openRoot_checks.1 openRoot_checks.2
    rfl rfl (by show ∀ t ∈ openRoot.body.read, "Z" ∉ pvars t; decide) (by decide) lEq
  have cNew : CellsU (childLoc rootLoc x (predotU Q)) rootLoc
      (res label C (openRootAt g.opening r₀ pr tk)).label
      (resConf label C (openRootAt g.opening r₀ pr tk)) tk [(pr, Q)] :=
    cellsU_of_open admitted rfl
      (fun σ s => (openRoot_reads label C x (predotU Q) r₀ pr tk g.opening rRefl prNeTk s).2.1)
      (fun σ s => (openRoot_reads label C x (predotU Q) r₀ pr tk g.opening rRefl prNeTk s).2.2)
      cleanPost
  let e_new : ActiveEntry O := ⟨rootLoc, x, Q, .root, hX, hQ, .pending tk [(pr, Q)]⟩
  have nonRoot : (openRootAt g.opening r₀ pr tk).rule ≠ atRule rootLoc commRule ∧
      (openRootAt g.opening r₀ pr tk).rule ≠ atRule rootLoc heatRule ∧
      (openRootAt g.opening r₀ pr tk).rule ≠ atRule rootLoc clearRule ∧
      (openRootAt g.opening r₀ pr tk).rule ≠ closeRoot := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;>
      { have c := congrArg (fun rl => rl.body.take.length) h
        simp [openRootAt, openRoot, atRule, RuleInstance.map, commRule, heatRule, clearRule, closeRoot] at c }
  refine ⟨rootRows, active ++ [e_new], ⟨w, solved⟩, noRootTokens_preserved sys.noRootTok _ admitted,
    rootCells_keep_nonRoot sys.noRootTok sys.rootInv _ admitted nonRoot.1 nonRoot.2.1 nonRoot.2.2.1 nonRoot.2.2.2,
    sys.rootNodes, sys.rootBag, ?_, ?_, ?_⟩
  · intro e m; rcases List.mem_append.mp m with inA | inN
    · exact (active_keep_nonChildRule (sys.activeValid e inA) admitted (.inr (.inr (.inr (.inl rfl))))).1
    · simp only [List.mem_singleton] at inN; subst inN
      exact ⟨cNew, fun q qM => by simp only [List.mem_singleton] at qM; subst qM; exact hQ,
        bagEq_pPar_singleton Q⟩
  · rw [List.pairwise_append]
    refine ⟨sys.activeApart.imp (apartOn_mono _), List.pairwise_singleton _ _, fun e₁ inA e₂ inN => ?_⟩
    simp only [List.mem_singleton] at inN; subst inN; exact apartE e₁ inA
  · intro z zP; rcases result_row zP with made | ⟨old, -, -, -⟩
    · simp only [openRootAt, List.mem_cons, List.not_mem_nil, or_false] at made
      rcases made with rfl | rfl
      · exact .inr ⟨e_new, by simp, .inr (by simp [e_new, ActiveEntry.cells])⟩
      · exact .inr ⟨e_new, by simp, .inl (by simp [e_new, ActiveEntry.tok])⟩
    · rcases sys.presentCover z old with inR | ⟨e, inA, hE⟩
      · exact .inl inR
      · exact .inr ⟨e, List.mem_append_left _ inA, hE⟩

private theorem step_openChild {StepRel : Pattern → Pattern → Prop}
    {label : O → Pattern} {C : Configuration Pattern O} {P : Pattern}
    {rootRows : List (O × Pattern)} {active : List (ActiveEntry O)}
    (sys : SystemInvBy StepRel label C P rootRows active)
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (rEq : g.rule = openChild) :
    SystemInv StepRel (res label C g).label (resConf label C g) P := by
  obtain ⟨r, tk_p, pr_g, tk_g, gEq⟩ := eq_openChildAt admitted rEq
  rw [gEq] at admitted ⊢
  obtain ⟨_, shapes, enabled, ⟨_, w, solved⟩, -⟩ := (RuleSyntax.admits_iff _).mp admitted
  have known := info_known _ solved
  have prNeTk : pr_g ≠ tk_g := by simpa [openChildAt] using shapes.2.1
  have rPres : r ∈ C.present := enabled.kept_subset (by simp [openChildAt, Selection.commit])
  have tkpPres : tk_p ∈ C.present := enabled.kept_subset (by simp [openChildAt, Selection.commit])
  have zR : (atLoc (pReflect channelUnknown reflP) locL, r) ∈
      (openChildAt g.opening r tk_p pr_g tk_g).rule.body.read.zip
        (openChildAt g.opening r tk_p pr_g tk_g).selection.read := by simp [openChildAt, openChild]
  have zT : (pendingTok locL locM, tk_p) ∈
      (openChildAt g.opening r tk_p pr_g tk_g).rule.body.read.zip
        (openChildAt g.opening r tk_p pr_g tk_g).selection.read := by simp [openChildAt, openChild]
  have rTkp := read_reads _ solved zT; rw [psubst_pendingTok, psubst_pendingTok] at rTkp
  obtain ⟨e_p, epIn, cs_p, epPend⟩ := presentCover_identify_pending sys tkpPres known rTkp.symm
  have vp := sys.activeValid e_p epIn; simp only [ActiveEntry.Valid, epPend] at vp
  have hTkp := rTkp.trans (by simpa [psubst_pendingTok] using vp.1.phase.reads w known)
  have lEqP : NameLaws (psubst w (psubst g.opening locL)) (psubst w e_p.loc) :=
    (nameLaws_pendingTok_iff.mp hTkp).1
  have rRead := read_reads _ solved zR; simp only [psubst_atLoc_any, psubst_pReflect] at rRead
  have rNeTkp : r ≠ tk_p := fun e => by
    have rR' : NameLaws (atLoc (pReflect (psubst w (psubst g.opening channelUnknown))
        (psubst w (psubst g.opening reflP))) (psubst w (psubst g.opening locL)))
        (psubst w (label r)) := rRead
    have rT' : NameLaws (pendingTok (psubst w (psubst g.opening locL))
        (psubst w (psubst g.opening locM))) (psubst w (label tk_p)) := rTkp
    rw [e] at rR'
    exact absurd (nameLaws_heads (rR'.trans rT'.symm)) (by decide)
  have rIn : r ∈ cs_p.map Prod.fst := by
    by_contra notIn
    have eqAt : NameLaws (atLoc (pReflect (psubst w (psubst g.opening channelUnknown))
        (psubst w (psubst g.opening reflP))) (psubst w (psubst g.opening locL)))
        (atLoc (pReflect (psubst w (psubst g.opening channelUnknown))
          (psubst w (psubst g.opening reflP))) (psubst w e_p.loc)) :=
      (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨NameLaws.refl _, lEqP⟩
    exact vp.1.others r rPres rNeTkp notIn w known _ (rRead.symm.trans eqAt)
  obtain ⟨⟨r₀, Pr⟩, rMem, eqR⟩ := List.mem_map.mp rIn; subst eqR
  have hR := rRead.trans ((vp.1.rows _ rMem).2.2 w known)
  simp only [psubst_atLoc_any] at hR
  obtain ⟨y, Q, rfl, hY, hQ⟩ := hostedNode_match_reflect (vp.2.1 _ rMem)
    ((locatedFrame_name.atLoc_iff _ _ _ _).mp hR).1
  have rRefl : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label r₀)) (psubst σ (atLoc (pReflect y (predotU Q)) e_p.loc)) := by
    intro σ s; have h := (vp.1.rows _ rMem).2.2 σ s; rwa [predotU_pReflect, predotU_ground y hY.1] at h
  have lEq : ∀ σ : PSubst,
      nameAction.Models σ (resConf label C (openChildAt g.opening r₀ tk_p pr_g tk_g)).equations →
        NameLaws (psubst σ (psubst g.opening (childLoc locL channelUnknown reflP)))
          (psubst σ (childLoc e_p.loc y (predotU Q))) := by
    intro σ s
    obtain ⟨lpS, -, chS, qS⟩ := openChild_reading label C y (predotU Q) e_p.loc e_p.parent r₀ tk_p
      pr_g tk_g g.opening rRefl vp.1.phase.reads s
    rw [psubst_childLoc, psubst_childLoc, psubst_childLoc]
    exact nameLaws_childLoc_iff.mpr ⟨lpS, chS, qS⟩
  obtain ⟨apartE, cleanPost⟩ := open_apart_and_clean sys admitted openChild_checks.1 openChild_checks.2
    rfl rfl (by show ∀ t ∈ openChild.body.read, "Z" ∉ pvars t; decide) (by decide) lEq
  have cNew : CellsU (childLoc e_p.loc y (predotU Q)) e_p.loc
      (res label C (openChildAt g.opening r₀ tk_p pr_g tk_g)).label
      (resConf label C (openChildAt g.opening r₀ tk_p pr_g tk_g)) tk_g [(pr_g, Q)] :=
    cellsU_of_open admitted rfl
      (fun σ s => (openChild_reads label C y (predotU Q) e_p.loc e_p.parent r₀ tk_p pr_g tk_g
        g.opening rRefl vp.1.phase.reads prNeTk s).2.1)
      (fun σ s => (openChild_reads label C y (predotU Q) e_p.loc e_p.parent r₀ tk_p pr_g tk_g
        g.opening rRefl vp.1.phase.reads prNeTk s).2.2)
      cleanPost
  let e_new : ActiveEntry O := ⟨e_p.loc, y, Q, e_p.spLoc, hY, hQ, .pending tk_g [(pr_g, Q)]⟩
  have nonRoot : (openChildAt g.opening r₀ tk_p pr_g tk_g).rule ≠ atRule rootLoc commRule ∧
      (openChildAt g.opening r₀ tk_p pr_g tk_g).rule ≠ atRule rootLoc heatRule ∧
      (openChildAt g.opening r₀ tk_p pr_g tk_g).rule ≠ atRule rootLoc clearRule ∧
      (openChildAt g.opening r₀ tk_p pr_g tk_g).rule ≠ closeRoot := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;>
      { have c := congrArg (fun rl => rl.body.take.length) h
        simp [openChildAt, openChild, atRule, RuleInstance.map, commRule, heatRule, clearRule, closeRoot] at c }
  refine ⟨rootRows, active ++ [e_new], ⟨w, solved⟩, noRootTokens_preserved sys.noRootTok _ admitted,
    rootCells_keep_nonRoot sys.noRootTok sys.rootInv _ admitted nonRoot.1 nonRoot.2.1 nonRoot.2.2.1 nonRoot.2.2.2,
    sys.rootNodes, sys.rootBag, ?_, ?_, ?_⟩
  · intro e m; rcases List.mem_append.mp m with inA | inN
    · exact (active_keep_nonChildRule (sys.activeValid e inA) admitted (.inr (.inr (.inr (.inr rfl))))).1
    · simp only [List.mem_singleton] at inN; subst inN
      exact ⟨cNew, fun q qM => by simp only [List.mem_singleton] at qM; subst qM; exact hQ,
        bagEq_pPar_singleton Q⟩
  · rw [List.pairwise_append]
    refine ⟨sys.activeApart.imp (apartOn_mono _), List.pairwise_singleton _ _, fun e₁ inA e₂ inN => ?_⟩
    simp only [List.mem_singleton] at inN; subst inN; exact apartE e₁ inA
  · intro z zP; rcases result_row zP with made | ⟨old, -, -, -⟩
    · simp only [openChildAt, List.mem_cons, List.not_mem_nil, or_false] at made
      rcases made with rfl | rfl
      · exact .inr ⟨e_new, by simp, .inr (by simp [e_new, ActiveEntry.cells])⟩
      · exact .inr ⟨e_new, by simp, .inl (by simp [e_new, ActiveEntry.tok])⟩
    · rcases sys.presentCover z old with inR | ⟨e, inA, hE⟩
      · exact .inl inR
      · exact .inr ⟨e, List.mem_append_left _ inA, hE⟩

private theorem step_heatChild {StepRel : Pattern → Pattern → Prop}
    {label : O → Pattern} {C : Configuration Pattern O} {P : Pattern}
    {rootRows : List (O × Pattern)} {active : List (ActiveEntry O)}
    (sys : SystemInvBy StepRel label C P rootRows active)
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (rEq : g.rule = heatChild) :
    SystemInv StepRel (res label C g).label (resConf label C g) P := by
  obtain ⟨_, shapes, enabled, ⟨_, w, solved⟩, -⟩ := (RuleSyntax.admits_iff g).mp admitted
  have known := info_known g solved
  obtain ⟨tk₀, zTk⟩ := exists_mem_zip shapes.2.2.2.1 (x := pendingTok locL locM)
    (by rw [rEq]; simp [heatChild])
  have tkPres : tk₀ ∈ C.present := enabled.kept_subset (by simpa [Selection.commit] using (List.of_mem_zip zTk).2)
  have rTkW := read_reads g solved zTk; rw [psubst_pendingTok, psubst_pendingTok] at rTkW
  obtain ⟨e₀, e₀In, cs₀, e₀Pend⟩ := presentCover_identify_pending sys tkPres known rTkW.symm
  have v₀ := sys.activeValid e₀ e₀In; simp only [ActiveEntry.Valid, e₀Pend] at v₀
  have locAll : ∀ σ : PSubst, nameAction.Models σ (g.information QN (embed label C)) →
      NameLaws (psubst σ (psubst g.opening locL)) (psubst σ e₀.loc) := by
    intro σ s; have r := (read_reads g s zTk).trans (v₀.1.phase.reads σ (info_known g s))
    rw [psubst_pendingTok, psubst_pendingTok] at r; exact (nameLaws_pendingTok_iff.mp r).1
  obtain ⟨o, m₁, m₂, gEq⟩ := eq_heatChildN v₀.1.phase admitted rEq solved (locAll w solved)
  rw [gEq] at admitted solved zTk locAll ⊢
  obtain ⟨cs₀', cInv', cNodes', bEq, memIff⟩ := cellsU_heat_reflects v₀.1 v₀.2.1 admitted
  obtain ⟨restA, pmA, pwRest, inRest⟩ := active_remove_one sys.activeApart e₀In
  let e₀' : ActiveEntry O := { e₀ with phaseState := .pending tk₀ cs₀' }
  have locEq' : e₀'.loc = e₀.loc := rfl
  have nonRoot : (heatChildN g.opening o tk₀ m₁ m₂).rule ≠ atRule rootLoc commRule ∧
      (heatChildN g.opening o tk₀ m₁ m₂).rule ≠ atRule rootLoc heatRule ∧
      (heatChildN g.opening o tk₀ m₁ m₂).rule ≠ atRule rootLoc clearRule ∧
      (heatChildN g.opening o tk₀ m₁ m₂).rule ≠ closeRoot := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;>
      { have c := congrArg (fun rl => rl.body.read.length) h
        simp [heatChildN, heatChild, atRule, RuleInstance.map, commRule, heatRule, clearRule, closeRoot] at c }
  have keepRest : ∀ e ∈ restA,
      e.Valid StepRel (res label C (heatChildN g.opening o tk₀ m₁ m₂)).label
        (resConf label C (heatChildN g.opening o tk₀ m₁ m₂)) ∧
      (∀ z ∈ C.present, z ∈ (heatChildN g.opening o tk₀ m₁ m₂).selection.taken →
        z ≠ e.tok ∧ z ∉ e.cells.map Prod.fst) := by
    intro e m; obtain ⟨eIn, ap⟩ := inRest e m
    exact e.valid_keep_other (sys.activeValid e eIn) _ admitted
      (by rintro ⟨h | h, -⟩ <;> { have c := congrArg (fun rl => rl.body.take.length) h; simp [heatChildN, heatChild, commChild, closeChild] at c })
      (by rintro ⟨_, σ, s, lE⟩; exact ap σ (info_known _ s) (lE.symm.trans (locAll σ s)))
      (by rintro ⟨h, -⟩; have c := congrArg (fun rl => rl.body.take.length) h; simp [heatChildN, heatChild, cool] at c)
      (by rintro (⟨h, -⟩ | ⟨h, -⟩) <;> { have c := congrArg (fun rl => rl.body.take.length) h; simp [heatChildN, heatChild, closeRoot, closeChild] at c })
  refine ⟨rootRows, e₀' :: restA, ⟨w, solved⟩, noRootTokens_preserved sys.noRootTok _ admitted,
    rootCells_keep_nonRoot sys.noRootTok sys.rootInv _ admitted nonRoot.1 nonRoot.2.1 nonRoot.2.2.1 nonRoot.2.2.2,
    sys.rootNodes, sys.rootBag, ?_, ?_, ?_⟩
  · intro e m; rcases List.mem_cons.mp m with rfl | inR
    · exact ⟨cInv', cNodes', bEq.trans v₀.2.2⟩
    · exact (keepRest e inR).1
  · refine List.pairwise_cons.mpr ⟨fun e inR σ s => ?_, pwRest.imp (apartOn_mono _)⟩
    rw [locEq']; exact apartOn_symm (inRest e inR).2 σ (info_known _ s)
  · intro z zP; rcases result_row zP with made | ⟨old, notT, -, -⟩
    · simp only [heatChildN, List.mem_cons, List.not_mem_nil, or_false] at made
      exact .inr ⟨e₀', by simp, .inr ((memIff z).mpr (.inr made))⟩
    · have neO : z ≠ o := fun e => notT (by simp [heatChildN, e])
      rcases sys.presentCover z old with inR | ⟨e, eIn, hE⟩
      · exact .inl inR
      · rcases List.mem_cons.mp (pmA.subset eIn) with rfl | inR
        · rcases hE with isT | inC
          · exact .inr ⟨e₀', by simp, .inl (by simpa [ActiveEntry.tok, e₀Pend] using isT)⟩
          · simp only [ActiveEntry.cells, e₀Pend] at inC
            exact .inr ⟨e₀', by simp, .inr ((memIff z).mpr (.inl ⟨inC, neO⟩))⟩
        · exact .inr ⟨e, List.mem_cons_of_mem _ inR, hE⟩

private theorem step_cool {StepRel : Pattern → Pattern → Prop}
    {label : O → Pattern} {C : Configuration Pattern O} {P : Pattern}
    {rootRows : List (O × Pattern)} {active : List (ActiveEntry O)}
    (sys : SystemInvBy StepRel label C P rootRows active)
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (rEq : g.rule = cool) :
    SystemInv StepRel (res label C g).label (resConf label C g) P := by
  obtain ⟨_, _, _, ⟨_, w, solved⟩, -⟩ := (RuleSyntax.admits_iff g).mp admitted
  have known := info_known g solved
  obtain ⟨d₀, zD, dPres⟩ := taken_row admitted (t := doneTok locL locM accC) (by rw [rEq]; simp [cool])
  have rDW := take_reads g solved zD; rw [psubst_doneTok, psubst_doneTok] at rDW
  obtain ⟨e₀, e₀In, acc₀, cs₀, red₀, e₀Done⟩ := presentCover_identify_done sys dPres known rDW.symm
  have v₀ := sys.activeValid e₀ e₀In; simp only [ActiveEntry.Valid, e₀Done] at v₀
  have locAll : ∀ σ : PSubst, nameAction.Models σ (g.information QN (embed label C)) →
      NameLaws (psubst σ (psubst g.opening locL)) (psubst σ e₀.loc) := by
    intro σ s; have r := (take_reads g s zD).trans (v₀.1.readsTok σ (info_known g s))
    rw [psubst_doneTok, psubst_doneTok] at r; exact (nameLaws_doneTok_iff.mp r).1
  have notClose₀ : ¬ CloseAtS e₀.loc label C g := by
    rintro (⟨h, -⟩ | ⟨h, -⟩) <;> { rw [rEq] at h; have c := congrArg (fun rl => rl.body.checks.length) h; simp [cool, closeRoot, closeChild] at c }
  obtain ⟨d', acc', cs', dInv', cNodes', bLaws', -, iffP⟩ :=
    doneCellsU_step_or_keep v₀.1 v₀.2.1 v₀.2.2.1 g admitted notClose₀
  obtain ⟨restA, pmA, pwRest, inRest⟩ := active_remove_one sys.activeApart e₀In
  let e₀' : ActiveEntry O := { e₀ with phaseState := .done d' acc' cs' red₀ }
  have nonRoot : g.rule ≠ atRule rootLoc commRule ∧ g.rule ≠ atRule rootLoc heatRule ∧
      g.rule ≠ atRule rootLoc clearRule ∧ g.rule ≠ closeRoot := by
    rw [rEq]; refine ⟨?_, ?_, ?_, ?_⟩
    · intro h; have c := congrArg (fun rl => rl.body.produce.length) h; simp [cool, atRule, RuleInstance.map, commRule] at c
    · intro h; have c := congrArg (fun rl => rl.body.take.length) h; simp [cool, atRule, RuleInstance.map, heatRule] at c
    · intro h; have c := congrArg (fun rl => rl.body.take.length) h; simp [cool, atRule, RuleInstance.map, clearRule] at c
    · intro h; have c := congrArg (fun rl => rl.body.checks.length) h; simp [cool, closeRoot] at c
  have keepRest : ∀ e ∈ restA,
      e.Valid StepRel (res label C g).label (resConf label C g) ∧
      (∀ z ∈ C.present, z ∈ g.selection.taken → z ≠ e.tok ∧ z ∉ e.cells.map Prod.fst) := by
    intro e m; obtain ⟨eIn, ap⟩ := inRest e m
    exact e.valid_keep_other (sys.activeValid e eIn) g admitted
      (by rintro ⟨h | h, -⟩ <;> { rw [rEq] at h; have c := congrArg (fun rl => rl.body.take.length) h; simp [cool, commChild, closeChild] at c })
      (by rintro ⟨h, -⟩; rw [rEq] at h; have c := congrArg (fun rl => rl.body.take.length) h; simp [cool, heatChild] at c)
      (by rintro ⟨_, σ, s, lE⟩; exact ap σ (info_known g s) (lE.symm.trans (locAll σ s)))
      (by rintro (⟨h, -⟩ | ⟨h, -⟩) <;> { rw [rEq] at h; have c := congrArg (fun rl => rl.body.checks.length) h; simp [cool, closeRoot, closeChild] at c })
  refine ⟨rootRows, e₀' :: restA, ⟨w, solved⟩, noRootTokens_preserved sys.noRootTok g admitted,
    rootCells_keep_nonRoot sys.noRootTok sys.rootInv g admitted nonRoot.1 nonRoot.2.1 nonRoot.2.2.1 nonRoot.2.2.2,
    sys.rootNodes, sys.rootBag, ?_, ?_, ?_⟩
  · intro e m; rcases List.mem_cons.mp m with rfl | inR
    · exact ⟨dInv', cNodes', bLaws', v₀.2.2.2⟩
    · exact (keepRest e inR).1
  · refine List.pairwise_cons.mpr ⟨fun e inR σ s => ?_, pwRest.imp (apartOn_mono g)⟩
    exact apartOn_symm (inRest e inR).2 σ (info_known g s)
  · intro z zP; rcases result_row zP with made | ⟨old, notT, -, -⟩
    · exact .inr ⟨e₀', by simp, (iffP z zP).mpr (.inl ⟨made, ⟨rEq, w, solved, locAll w solved⟩⟩)⟩
    · rcases sys.presentCover z old with inR | ⟨e, eIn, hE⟩
      · exact .inl inR
      · rcases List.mem_cons.mp (pmA.subset eIn) with rfl | inR
        · simp only [ActiveEntry.tok, ActiveEntry.cells, e₀Done] at hE
          exact .inr ⟨e₀', by simp, (iffP z zP).mpr (.inr ⟨old, notT, hE⟩)⟩
        · exact .inr ⟨e, List.mem_cons_of_mem _ inR, hE⟩

private theorem step_commChild_core {StepRel : Pattern → Pattern → Prop}
    {label : O → Pattern} {C : Configuration Pattern O} {P : Pattern}
    {rootRows : List (O × Pattern)} {active : List (ActiveEntry O)}
    (sys : SystemInvBy StepRel label C P rootRows active)
    (commReady : ∀ e ∈ active, ∀ (tk : O) (cs : List (O × Pattern)),
      e.phaseState = .pending tk cs →
      ∀ q₁ ∈ cs, ∀ q₂ ∈ cs, ∀ t ch A u ch' B : Pattern,
        q₁.1 ≠ q₂.1 → q₁.2 = pFor t ch A → q₂.2 = pFor u ch' B →
        CommAdmissibleN t ch A u ch' B ∧
        (ch = ch' → ∀ bs : Bindings, GroundPrincipal t u bs →
          ∀ rest : List (O × Pattern), cs.Perm ((q₁.1, pFor t ch A) :: (q₂.1, pFor u ch' B) :: rest) →
          ∀ m₁ m₂ : O,
            BagStep conventional
              (pPar (((q₁.1, pFor t ch A) :: (q₂.1, pFor u ch' B) :: rest).map Prod.snd))
              (pPar ((rest ++ [(m₁, applyDot bs A), (m₂, applyDot bs B)]).map Prod.snd)) →
            CanonicalBagStep conventional
              (pPar (((q₁.1, pFor t ch A) :: (q₂.1, pFor u ch' B) :: rest).map Prod.snd))
              (pPar ((rest ++ [(m₁, applyDot bs A), (m₂, applyDot bs B)]).map Prod.snd)) →
            StepRel e.proc (pPar ((rest ++ [(m₁, applyDot bs A), (m₂, applyDot bs B)]).map Prod.snd))))
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (rEq : g.rule = commChild) :
    SystemInv StepRel (res label C g).label (resConf label C g) P := by
  obtain ⟨_, _, _, ⟨_, w, solved⟩, -⟩ := (RuleSyntax.admits_iff g).mp admitted
  have known := info_known g solved
  obtain ⟨tk₀, zTk, tkPres⟩ := taken_row admitted (t := pendingTok locL locM) (by rw [rEq]; simp [commChild])
  have rTkW := take_reads g solved zTk; rw [psubst_pendingTok, psubst_pendingTok] at rTkW
  obtain ⟨e₀, e₀In, cs₀, e₀Pend⟩ := presentCover_identify_pending sys tkPres known rTkW.symm
  have v₀ := sys.activeValid e₀ e₀In; simp only [ActiveEntry.Valid, e₀Pend] at v₀
  have locAll : ∀ σ : PSubst, nameAction.Models σ (g.information QN (embed label C)) →
      NameLaws (psubst σ (psubst g.opening locL)) (psubst σ e₀.loc) := by
    intro σ s; have r := (take_reads g s zTk).trans (v₀.1.phase.reads σ (info_known g s))
    rw [psubst_pendingTok, psubst_pendingTok] at r; exact (nameLaws_pendingTok_iff.mp r).1
  obtain ⟨first, second, m₁, m₂, mTok, gEq⟩ := eq_commChildAt v₀.1.phase admitted rEq solved (locAll w solved)
  rw [gEq] at admitted solved zTk locAll ⊢
  obtain ⟨_, shapes, enabled, -⟩ := (RuleSyntax.admits_iff _).mp admitted
  have ndT : [first, second, tk₀].Nodup := shapes.1
  have distinct : first ≠ second := fun e => (List.nodup_cons.mp ndT).1 (by simp [e])
  have fNeTk : first ≠ tk₀ := fun e => (List.nodup_cons.mp ndT).1 (by simp [e])
  have sNeTk : second ≠ tk₀ := fun e => (List.nodup_cons.mp (List.nodup_cons.mp ndT).2).1 (by simp [e])
  have p₁ : first ∈ C.present := enabled.taken_subset (by simp [commChildAt, Selection.commit])
  have p₂ : second ∈ C.present := enabled.taken_subset (by simp [commChildAt, Selection.commit])
  have z₁ : (atLoc (pFor firstPattern channelUnknown firstBody) locL, first) ∈
      (commChildAt g.opening first second tk₀ m₁ m₂ mTok).rule.body.take.zip
        (commChildAt g.opening first second tk₀ m₁ m₂ mTok).selection.taken := by simp [commChildAt, commChild]
  have z₂ : (atLoc (pFor secondPattern channelUnknown secondBody) locL, second) ∈
      (commChildAt g.opening first second tk₀ m₁ m₂ mTok).rule.body.take.zip
        (commChildAt g.opening first second tk₀ m₁ m₂ mTok).selection.taken := by simp [commChildAt, commChild]
  have r₁ := take_reads _ solved z₁; simp only [psubst_atLoc_any, psubst_pFor] at r₁
  have r₂ := take_reads _ solved z₂; simp only [psubst_atLoc_any, psubst_pFor] at r₂
  have fIn : first ∈ cs₀.map Prod.fst := by
    by_contra notIn
    have eqAt : NameLaws (atLoc (pFor (psubst w (psubst g.opening firstPattern))
        (psubst w (psubst g.opening channelUnknown)) (psubst w (psubst g.opening firstBody)))
        (psubst w (psubst g.opening locL)))
        (atLoc (pFor (psubst w (psubst g.opening firstPattern))
          (psubst w (psubst g.opening channelUnknown)) (psubst w (psubst g.opening firstBody)))
          (psubst w e₀.loc)) :=
      (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨NameLaws.refl _, locAll w solved⟩
    exact v₀.1.others first p₁ fNeTk notIn w known _ (r₁.symm.trans eqAt)
  have sIn : second ∈ cs₀.map Prod.fst := by
    by_contra notIn
    have eqAt : NameLaws (atLoc (pFor (psubst w (psubst g.opening secondPattern))
        (psubst w (psubst g.opening channelUnknown)) (psubst w (psubst g.opening secondBody)))
        (psubst w (psubst g.opening locL)))
        (atLoc (pFor (psubst w (psubst g.opening secondPattern))
          (psubst w (psubst g.opening channelUnknown)) (psubst w (psubst g.opening secondBody)))
          (psubst w e₀.loc)) :=
      (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨NameLaws.refl _, locAll w solved⟩
    exact v₀.1.others second p₂ sNeTk notIn w known _ (r₂.symm.trans eqAt)
  obtain ⟨⟨f₀, Pf⟩, fMem, eqF⟩ := List.mem_map.mp fIn; subst eqF
  obtain ⟨⟨s₀, Ps⟩, sMem, eqS⟩ := List.mem_map.mp sIn; subst eqS
  have hF := r₁.trans ((v₀.1.rows _ fMem).2.2 w known); simp only [psubst_atLoc_any] at hF
  have hS := r₂.trans ((v₀.1.rows _ sMem).2.2 w known); simp only [psubst_atLoc_any] at hS
  obtain ⟨t, ch, A, rfl, -⟩ := hostedNode_match_for (v₀.2.1 _ fMem)
    ((locatedFrame_name.atLoc_iff _ _ _ _).mp hF).1
  obtain ⟨u, ch', B, rfl, -⟩ := hostedNode_match_for (v₀.2.1 _ sMem)
    ((locatedFrame_name.atLoc_iff _ _ _ _).mp hS).1
  obtain ⟨rest, pm, -⟩ := list_perm_pick2 v₀.1.nodup fMem sMem distinct
  obtain ⟨admPair, mkStep⟩ := commReady e₀ e₀In tk₀ cs₀ e₀Pend _ fMem _ sMem t ch A u ch' B distinct rfl rfl
  obtain ⟨chEq, bs, gp, dInv', cNodes', bLaws', bStep, cStep⟩ := cellsU_comm_admissible
    (v₀.1.perm pm) (fun q m => v₀.2.1 q (pm.symm.subset m)) admPair admitted
  let outCells := rest ++ [(m₁, applyDot bs A), (m₂, applyDot bs B)]
  let e₀' : ActiveEntry O := { e₀ with phaseState := .done mTok pZero outCells (pPar (outCells.map Prod.snd)) }
  obtain ⟨restA, pmA, pwRest, inRest⟩ := active_remove_one sys.activeApart e₀In
  have nonRoot : (commChildAt g.opening f₀ s₀ tk₀ m₁ m₂ mTok).rule ≠ atRule rootLoc commRule ∧
      (commChildAt g.opening f₀ s₀ tk₀ m₁ m₂ mTok).rule ≠ atRule rootLoc heatRule ∧
      (commChildAt g.opening f₀ s₀ tk₀ m₁ m₂ mTok).rule ≠ atRule rootLoc clearRule ∧
      (commChildAt g.opening f₀ s₀ tk₀ m₁ m₂ mTok).rule ≠ closeRoot := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;>
      { have c := congrArg (fun rl => rl.body.take.length) h
        simp [commChildAt, commChild, atRule, RuleInstance.map, commRule, heatRule, clearRule, closeRoot] at c }
  have keepRest : ∀ e ∈ restA,
      e.Valid StepRel (res label C (commChildAt g.opening f₀ s₀ tk₀ m₁ m₂ mTok)).label
        (resConf label C (commChildAt g.opening f₀ s₀ tk₀ m₁ m₂ mTok)) := by
    intro e m; obtain ⟨eIn, ap⟩ := inRest e m
    exact (e.valid_keep_other (sys.activeValid e eIn) _ admitted
      (by rintro ⟨h | h, σ, s, lE⟩
          · exact ap σ (info_known _ s) (lE.symm.trans (locAll σ s))
          · have c := congrArg (fun rl => rl.body.produce.length) h; simp [commChildAt, commChild, closeChild] at c)
      (by rintro ⟨h, -⟩; have c := congrArg (fun rl => rl.body.take.length) h; simp [commChildAt, commChild, heatChild] at c)
      (by rintro ⟨h, -⟩; have c := congrArg (fun rl => rl.body.take.length) h; simp [commChildAt, commChild, cool] at c)
      (by rintro (⟨h, -⟩ | ⟨h, -⟩) <;>
          { have c := congrArg (fun rl => rl.body.produce.length) h; simp [commChildAt, commChild, closeRoot, closeChild] at c })).1
  refine ⟨rootRows, e₀' :: restA, ⟨w, solved⟩, noRootTokens_preserved sys.noRootTok _ admitted,
    rootCells_keep_nonRoot sys.noRootTok sys.rootInv _ admitted nonRoot.1 nonRoot.2.1 nonRoot.2.2.1 nonRoot.2.2.2,
    sys.rootNodes, sys.rootBag, ?_, ?_, ?_⟩
  · intro e m; rcases List.mem_cons.mp m with rfl | inR
    · exact ⟨dInv', cNodes', bLaws', mkStep chEq bs gp rest pm m₁ m₂ bStep cStep⟩
    · exact keepRest e inR
  · refine List.pairwise_cons.mpr ⟨fun e inR σ s => ?_, pwRest.imp (apartOn_mono _)⟩
    exact apartOn_symm (inRest e inR).2 σ (info_known _ s)
  · intro z zP; rcases result_row zP with made | ⟨old, notT, -, -⟩
    · simp only [commChildAt, List.mem_cons, List.not_mem_nil, or_false] at made
      rcases made with rfl | rfl | rfl
      · exact .inr ⟨e₀', by simp, .inr (by simp [e₀', ActiveEntry.cells, outCells])⟩
      · exact .inr ⟨e₀', by simp, .inr (by simp [e₀', ActiveEntry.cells, outCells])⟩
      · exact .inr ⟨e₀', by simp, .inl (by simp [e₀', ActiveEntry.tok])⟩
    · have neF : z ≠ f₀ := fun e => notT (by simp [commChildAt, e])
      have neS : z ≠ s₀ := fun e => notT (by simp [commChildAt, e])
      have neTk : z ≠ tk₀ := fun e => notT (by simp [commChildAt, e])
      rcases sys.presentCover z old with inR | ⟨e, eIn, hE⟩
      · exact .inl inR
      · rcases List.mem_cons.mp (pmA.subset eIn) with rfl | inR
        · rcases hE with isT | inC
          · exact absurd (by simpa [ActiveEntry.tok, e₀Pend] using isT) neTk
          · simp only [ActiveEntry.cells, e₀Pend] at inC
            have inPerm := (pm.map Prod.fst).subset inC
            simp only [List.map_cons, List.mem_cons] at inPerm
            rcases inPerm with rfl | rfl | inRestC
            · exact absurd rfl neF
            · exact absurd rfl neS
            · exact .inr ⟨e₀', by simp, .inr (by simp [e₀', ActiveEntry.cells, outCells, inRestC])⟩
        · exact .inr ⟨e, List.mem_cons_of_mem _ inR, hE⟩

private theorem step_closeChild_core {StepRel : Pattern → Pattern → Prop}
    {label : O → Pattern} {C : Configuration Pattern O} {P : Pattern}
    {rootRows : List (O × Pattern)} {active : List (ActiveEntry O)}
    (sys : SystemInvBy StepRel label C P rootRows active)
    (noCap : ∀ e_g ∈ active, ∀ e_p ∈ active, ∀ (tk : O) (cs : List (O × Pattern)),
      e_p.phaseState = .pending tk cs →
      ∀ q ∈ cs, ∀ y Q : Pattern, q.2 = pReflect y Q →
        (∃ σ : PSubst, nameAction.Models σ C.equations ∧
          NameLaws (psubst σ e_g.loc) (psubst σ (childLoc e_p.loc y (predotU Q)))) →
        e_g.parent = e_p.loc ∧ e_g.chan = y ∧ e_g.proc = Q)
    (mkListener : Pattern → Pattern → Pattern)
    (hListenerNode : ∀ {y R_in}, HostedChan y → HostedNode (mkListener y R_in))
    (commitBridge : ∀ {e_p : ActiveEntry O} (_ : e_p ∈ active) {tk reflIn d_g d_in madeL madeTok : O}
      {ρ : PSubst} {preC postC : List (O × Pattern)} {y Q acc_g R_in : Pattern}
      (_ : e_p.phaseState = .pending tk (preC ++ (reflIn, pReflect y Q) :: postC))
      (_ : HostedChan y)
      (_ : CellsU e_p.loc e_p.parent label C tk (preC ++ (reflIn, pReflect y Q) :: postC))
      (_ : DoneCellsU (childLoc e_p.loc y (predotU Q)) e_p.loc label C d_g acc_g [])
      (_ : BagLaws acc_g (predotU R_in)) (_ : StepRel Q R_in)
      (_ : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
        (closeChildAt ρ reflIn d_in tk madeL madeTok)),
      d_in = d_g ∧
      DoneCellsU e_p.loc e_p.parent
        (res label C (closeChildAt ρ reflIn d_in tk madeL madeTok)).label
        (resConf label C (closeChildAt ρ reflIn d_in tk madeL madeTok))
        madeTok pZero ((preC ++ postC) ++ [(madeL, mkListener y R_in)]) ∧
      StepRel e_p.proc (pPar (((preC ++ postC) ++ [(madeL, mkListener y R_in)]).map Prod.snd)))
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (rEq : g.rule = closeChild) :
    SystemInv StepRel (res label C g).label (resConf label C g) P := by
  obtain ⟨reflIn, d_in, tk, madeL, madeTok, gEq⟩ := eq_closeChildAt admitted rEq
  rw [gEq] at admitted ⊢
  obtain ⟨_, shapes, enabled, ⟨_, w, solved⟩, -⟩ := (RuleSyntax.admits_iff _).mp admitted
  have known := info_known _ solved
  have ndT : [reflIn, d_in, tk].Nodup := shapes.1
  have rNeTk : reflIn ≠ tk := fun e => (List.nodup_cons.mp ndT).1 (by simp [e])
  have rPres : reflIn ∈ C.present := enabled.taken_subset (by simp [closeChildAt, Selection.commit])
  have dPres : d_in ∈ C.present := enabled.taken_subset (by simp [closeChildAt, Selection.commit])
  have tkPres : tk ∈ C.present := enabled.taken_subset (by simp [closeChildAt, Selection.commit])
  have zR : (atLoc (pReflect channelUnknown reflP) locL, reflIn) ∈
      (closeChildAt g.opening reflIn d_in tk madeL madeTok).rule.body.take.zip
        (closeChildAt g.opening reflIn d_in tk madeL madeTok).selection.taken := by simp [closeChildAt, closeChild]
  have zI : (doneTok (childLoc locL channelUnknown reflP) locL accC, d_in) ∈
      (closeChildAt g.opening reflIn d_in tk madeL madeTok).rule.body.take.zip
        (closeChildAt g.opening reflIn d_in tk madeL madeTok).selection.taken := by simp [closeChildAt, closeChild]
  have zT : (pendingTok locL locM, tk) ∈
      (closeChildAt g.opening reflIn d_in tk madeL madeTok).rule.body.take.zip
        (closeChildAt g.opening reflIn d_in tk madeL madeTok).selection.taken := by simp [closeChildAt, closeChild]
  have rTkW := take_reads _ solved zT; rw [psubst_pendingTok, psubst_pendingTok] at rTkW
  have rIW := take_reads _ solved zI; rw [psubst_doneTok, psubst_doneTok] at rIW
  obtain ⟨e_p, epIn, cs_p, epPend⟩ := presentCover_identify_pending sys tkPres known rTkW.symm
  obtain ⟨e_g, egIn, acc_g, cs_g, R_in, egDone⟩ := presentCover_identify_done sys dPres known rIW.symm
  have epNeEg : e_p ≠ e_g := fun e => by rw [e, egDone] at epPend; cases epPend
  have vp := sys.activeValid e_p epIn; simp only [ActiveEntry.Valid, epPend] at vp
  have vg := sys.activeValid e_g egIn; simp only [ActiveEntry.Valid, egDone] at vg
  have locPAll : ∀ σ : PSubst,
      nameAction.Models σ ((closeChildAt g.opening reflIn d_in tk madeL madeTok).information QN (embed label C)) →
        NameLaws (psubst σ (psubst g.opening locL)) (psubst σ e_p.loc) := by
    intro σ s; have r := (take_reads _ s zT).trans (vp.1.phase.reads σ (info_known _ s))
    rw [psubst_pendingTok, psubst_pendingTok] at r; exact (nameLaws_pendingTok_iff.mp r).1
  have locGAll : ∀ σ : PSubst,
      nameAction.Models σ ((closeChildAt g.opening reflIn d_in tk madeL madeTok).information QN (embed label C)) →
        NameLaws (psubst σ (psubst g.opening (childLoc locL channelUnknown reflP))) (psubst σ e_g.loc) := by
    intro σ s; have r := (take_reads _ s zI).trans (vg.1.readsTok σ (info_known _ s))
    rw [psubst_doneTok, psubst_doneTok] at r; exact (nameLaws_doneTok_iff.mp r).1
  have rRW := take_reads _ solved zR; simp only [psubst_atLoc_any, psubst_pReflect] at rRW
  have rIn : reflIn ∈ cs_p.map Prod.fst := by
    by_contra notIn
    have eqAt : NameLaws (atLoc (pReflect (psubst w (psubst g.opening channelUnknown))
        (psubst w (psubst g.opening reflP))) (psubst w (psubst g.opening locL)))
        (atLoc (pReflect (psubst w (psubst g.opening channelUnknown))
          (psubst w (psubst g.opening reflP))) (psubst w e_p.loc)) :=
      (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨NameLaws.refl _, locPAll w solved⟩
    exact vp.1.others reflIn rPres rNeTk notIn w known _ (rRW.symm.trans eqAt)
  obtain ⟨⟨r₀, Pr⟩, rMem, eqR⟩ := List.mem_map.mp rIn; subst eqR
  have hR₀ := rRW.trans ((vp.1.rows _ rMem).2.2 w known); simp only [psubst_atLoc_any] at hR₀
  obtain ⟨y, Q, rfl, hY, -⟩ := hostedNode_match_reflect (vp.2.1 _ rMem)
    ((locatedFrame_name.atLoc_iff _ _ _ _).mp hR₀).1
  have rRefl : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label r₀)) (psubst σ (atLoc (pReflect y (predotU Q)) e_p.loc)) := by
    intro σ s; have h := (vp.1.rows _ rMem).2.2 σ s; rwa [predotU_pReflect, predotU_ground y hY.1] at h
  have gMatchW : NameLaws (psubst w e_g.loc) (psubst w (childLoc e_p.loc y (predotU Q))) := by
    have hR := (take_reads _ solved zR).trans (rRefl w known)
    simp only [psubst_atLoc_any, psubst_pReflect] at hR
    obtain ⟨chEq, qEq⟩ := nameLaws_pReflect_iff.mp ((locatedFrame_name.atLoc_iff _ _ _ _).mp hR).1
    refine (locGAll w solved).symm.trans ?_
    rw [psubst_childLoc, psubst_childLoc, psubst_childLoc]
    exact nameLaws_childLoc_iff.mpr ⟨locPAll w solved, chEq, qEq⟩
  obtain ⟨egPar, egCh, egPr⟩ := noCap e_g egIn e_p epIn tk cs_p epPend _ rMem y Q rfl ⟨w, known, gMatchW⟩
  have egLocEq : e_g.loc = childLoc e_p.loc y (predotU Q) := by simp [ActiveEntry.loc, egPar, egCh, egPr]
  obtain ⟨preC, postC, rfl⟩ := List.append_of_mem rMem
  have gNil : cs_g = [] := by
    cases cs_g with
    | nil => rfl
    | cons q _ =>
        have qF := vg.1.rows q (List.mem_cons_self ..)
        exact False.elim (closeChild_waits label C y (predotU Q) e_p.loc r₀ d_in tk madeL madeTok
          g.opening rRefl qF.1 (by simpa [egLocEq] using qF.2.2) admitted)
  subst gNil
  have dInvG : DoneCellsU (childLoc e_p.loc y (predotU Q)) e_p.loc label C d_in acc_g [] := by
    simpa [egLocEq, egPar] using vg.1
  have bAccG : BagLaws acc_g (predotU R_in) := by simpa [cooled] using vg.2.2.1
  have sInG : StepRel Q R_in := egPr ▸ vg.2.2.2
  obtain ⟨-, dInvP', stepP⟩ := commitBridge epIn epPend hY vp.1 dInvG bAccG sInG admitted
  let outCells := (preC ++ postC) ++ [(madeL, mkListener y R_in)]
  let e_p' : ActiveEntry O := { e_p with phaseState := .done madeTok pZero outCells (pPar (outCells.map Prod.snd)) }
  obtain ⟨active₁, pmG, pw₁, in₁⟩ := active_remove_one sys.activeApart egIn
  have epIn₁ : e_p ∈ active₁ := by
    rcases List.mem_cons.mp (pmG.subset epIn) with rfl | m
    · exact absurd rfl epNeEg
    · exact m
  obtain ⟨restA, pmP, pwRest, inRest⟩ := active_remove_one pw₁ epIn₁
  have nonRoot : (closeChildAt g.opening r₀ d_in tk madeL madeTok).rule ≠ atRule rootLoc commRule ∧
      (closeChildAt g.opening r₀ d_in tk madeL madeTok).rule ≠ atRule rootLoc heatRule ∧
      (closeChildAt g.opening r₀ d_in tk madeL madeTok).rule ≠ atRule rootLoc clearRule ∧
      (closeChildAt g.opening r₀ d_in tk madeL madeTok).rule ≠ closeRoot := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;>
      { have c := congrArg (fun rl => rl.body.take.length) h
        simp [closeChildAt, closeChild, atRule, RuleInstance.map, commRule, heatRule, clearRule, closeRoot] at c }
  have keepRest : ∀ e ∈ restA,
      e.Valid StepRel (res label C (closeChildAt g.opening r₀ d_in tk madeL madeTok)).label
        (resConf label C (closeChildAt g.opening r₀ d_in tk madeL madeTok)) := by
    intro e m
    obtain ⟨eIn₁, apP⟩ := inRest e m
    obtain ⟨eIn, apG⟩ := in₁ e eIn₁
    exact (e.valid_keep_other (sys.activeValid e eIn) _ admitted
      (by rintro ⟨h | _, σ, s, lE⟩
          · have c := congrArg (fun rl => rl.body.produce.length) h; simp [closeChildAt, commChild, closeChild] at c
          · exact apP σ (info_known _ s) (lE.symm.trans (locPAll σ s)))
      (by rintro ⟨h, -⟩; have c := congrArg (fun rl => rl.body.take.length) h; simp [closeChildAt, heatChild, closeChild] at c)
      (by rintro ⟨h, -⟩; have c := congrArg (fun rl => rl.body.take.length) h; simp [closeChildAt, cool, closeChild] at c)
      (by rintro (⟨h, -⟩ | ⟨_, σ, s, lE⟩)
          · have c := congrArg (fun rl => rl.body.take.length) h; simp [closeChildAt, closeRoot, closeChild] at c
          · exact apG σ (info_known _ s) (lE.symm.trans (locGAll σ s)))).1
  refine ⟨rootRows, e_p' :: restA, ⟨w, solved⟩, noRootTokens_preserved sys.noRootTok _ admitted,
    rootCells_keep_nonRoot sys.noRootTok sys.rootInv _ admitted nonRoot.1 nonRoot.2.1 nonRoot.2.2.1 nonRoot.2.2.2,
    sys.rootNodes, sys.rootBag, ?_, ?_, ?_⟩
  · intro e m; rcases List.mem_cons.mp m with rfl | inR
    · refine ⟨dInvP', fun q qM => ?_, ?_, stepP⟩
      · rcases List.mem_append.mp qM with inRestC | inM
        · exact vp.2.1 q ((List.mem_append.mp inRestC).elim (List.mem_append_left _)
            (fun r => List.mem_append_right _ (List.mem_cons_of_mem _ r)))
        · simp only [List.mem_singleton] at inM; subst inM; exact hListenerNode hY
      · rw [predotU_pPar, List.map_map]; exact bagLaws_cooled_zero _
    · exact keepRest e inR
  · refine List.pairwise_cons.mpr ⟨fun e inR σ s => ?_, pwRest.imp (apartOn_mono _)⟩
    exact apartOn_symm (inRest e inR).2 σ (info_known _ s)
  · intro z zP; rcases result_row zP with made | ⟨old, notT, -, -⟩
    · simp only [closeChildAt, List.mem_cons, List.not_mem_nil, or_false] at made
      rcases made with rfl | rfl
      · exact .inr ⟨e_p', by simp, .inr (by simp [e_p', ActiveEntry.cells, outCells])⟩
      · exact .inr ⟨e_p', by simp, .inl (by simp [e_p', ActiveEntry.tok])⟩
    · have neR : z ≠ r₀ := fun e => notT (by simp [closeChildAt, e])
      have neD : z ≠ d_in := fun e => notT (by simp [closeChildAt, e])
      have neTk : z ≠ tk := fun e => notT (by simp [closeChildAt, e])
      rcases sys.presentCover z old with inR | ⟨e, eIn, hE⟩
      · exact .inl inR
      · rcases List.mem_cons.mp (pmG.subset eIn) with rfl | inA₁
        · simp only [ActiveEntry.tok, ActiveEntry.cells, egDone, List.map_nil, List.not_mem_nil, or_false] at hE
          exact absurd hE neD
        · rcases List.mem_cons.mp (pmP.subset inA₁) with rfl | inRestA
          · rcases hE with isT | inC
            · exact absurd (by simpa [ActiveEntry.tok, epPend] using isT) neTk
            · simp only [ActiveEntry.cells, epPend, List.map_append, List.map_cons, List.mem_append,
                List.mem_cons] at inC
              rcases inC with inPre | rfl | inPost
              · exact .inr ⟨e_p', by simp, .inr (by simp [e_p', ActiveEntry.cells, outCells, inPre])⟩
              · exact absurd rfl neR
              · exact .inr ⟨e_p', by simp, .inr (by simp [e_p', ActiveEntry.cells, outCells, inPost])⟩
          · exact .inr ⟨e, List.mem_cons_of_mem _ inRestA, hE⟩

private theorem step_closeRoot_core {StepRel ResultStep : Pattern → Pattern → Prop}
    {label : O → Pattern} {C : Configuration Pattern O} {P : Pattern}
    {rootRows : List (O × Pattern)} {active : List (ActiveEntry O)}
    (sys : SystemInvBy StepRel label C P rootRows active)
    (noCap : ∀ e ∈ active, ∀ q ∈ rootRows, ∀ x Q : Pattern,
      q.2 = pReflect x Q →
      (∃ σ : PSubst, nameAction.Models σ C.equations ∧
        NameLaws (psubst σ e.loc) (psubst σ (childLoc rootLoc x (predotU Q)))) →
      e.parent = rootLoc ∧ e.chan = x ∧ e.proc = Q)
    (mkListener : Pattern → Pattern → Pattern)
    (hListenerNode : ∀ {x R}, HostedChan x → HostedNode (mkListener x R))
    (listenerBridge : ∀ {x Q R : Pattern} (_ : HostedChan x) (_ : StepRel Q R)
      (preR postR : List (O × Pattern)) (made : O),
      (∀ σ : PSubst, NameLaws (psubst σ (pFor (tProc (predotU R)) x pZero))
        (psubst σ (predotU (mkListener x R)))) ∧
      (BagEq P (rootBagProcess (preR ++ (made, pReflect x Q) :: postR)) →
        ResultStep P (rootBagProcess (preR ++ (made, mkListener x R) :: postR))))
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (rEq : g.rule = closeRoot) :
    ∃ P', ResultStep P P' ∧
      SystemInv StepRel (res label C g).label (resConf label C g) P' := by
  obtain ⟨reflOcc, d, made, gEq⟩ := eq_closeRootAt admitted rEq
  rw [gEq] at admitted ⊢
  obtain ⟨_, _, enabled, ⟨_, w, solved⟩, -⟩ := (RuleSyntax.admits_iff _).mp admitted
  have known := info_known _ solved
  have rPres : reflOcc ∈ C.present := enabled.taken_subset (by simp [closeRootAt, Selection.commit])
  have dPres : d ∈ C.present := enabled.taken_subset (by simp [closeRootAt, Selection.commit])
  have zR : (atLoc (pReflect channelUnknown reflP) rootLoc, reflOcc) ∈
      (closeRootAt g.opening reflOcc d made).rule.body.take.zip
        (closeRootAt g.opening reflOcc d made).selection.taken := by simp [closeRootAt, closeRoot]
  have zD : (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC, d) ∈
      (closeRootAt g.opening reflOcc d made).rule.body.take.zip
        (closeRootAt g.opening reflOcc d made).selection.taken := by simp [closeRootAt, closeRoot]
  have rRW := take_reads _ solved zR; simp only [psubst_atLoc_any, psubst_pReflect, psubst_rootLoc] at rRW
  have rDW := take_reads _ solved zD; rw [psubst_doneTok, psubst_doneTok] at rDW
  have rIn : reflOcc ∈ rootRows.map Prod.fst := by
    by_contra notIn; exact sys.rootInv.others reflOcc rPres notIn w known _ rRW.symm
  obtain ⟨⟨r₀, Pr⟩, rMem, eqR⟩ := List.mem_map.mp rIn; subst eqR
  have hR₀ := rRW.trans ((sys.rootInv.rows _ rMem).2 w known); simp only [psubst_atLoc_any, psubst_rootLoc] at hR₀
  obtain ⟨x, Q, rfl, hX, -⟩ := hostedNode_match_reflect (sys.rootNodes _ rMem)
    ((locatedFrame_name.atLoc_iff _ _ _ _).mp hR₀).1
  obtain ⟨e₀, e₀In, acc₀, cs₀, R, e₀Done⟩ := presentCover_identify_done sys dPres known rDW.symm
  have v₀ := sys.activeValid e₀ e₀In; simp only [ActiveEntry.Valid, e₀Done] at v₀
  have rRefl : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label r₀)) (psubst σ (atLoc (pReflect x (predotU Q)) rootLoc)) := by
    intro σ s; have h := (sys.rootInv.rows _ rMem).2 σ s; rwa [predotU_pReflect, predotU_ground x hX.1] at h
  have locAll : ∀ σ : PSubst,
      nameAction.Models σ ((closeRootAt g.opening r₀ d made).information QN (embed label C)) →
        NameLaws (psubst σ (psubst g.opening (childLoc rootLoc channelUnknown reflP))) (psubst σ e₀.loc) := by
    intro σ s; have r := (take_reads _ s zD).trans (v₀.1.readsTok σ (info_known _ s))
    rw [psubst_doneTok, psubst_doneTok] at r; exact (nameLaws_doneTok_iff.mp r).1
  have matchW : NameLaws (psubst w e₀.loc) (psubst w (childLoc rootLoc x (predotU Q))) := by
    have hR := (take_reads _ solved zR).trans (rRefl w known)
    simp only [psubst_atLoc_any, psubst_pReflect, psubst_rootLoc] at hR
    obtain ⟨chEq, qEq⟩ := nameLaws_pReflect_iff.mp ((locatedFrame_name.atLoc_iff _ _ _ _).mp hR).1
    refine (locAll w solved).symm.trans ?_
    rw [psubst_childLoc, psubst_childLoc, psubst_childLoc, psubst_rootLoc, psubst_rootLoc]
    exact nameLaws_childLoc_iff.mpr ⟨NameLaws.refl _, chEq, qEq⟩
  obtain ⟨ePar, eCh, ePr⟩ := noCap e₀ e₀In _ rMem x Q rfl ⟨w, known, matchW⟩
  have eLocEq : e₀.loc = childLoc rootLoc x (predotU Q) := by simp [ActiveEntry.loc, ePar, eCh, ePr]
  have csNil : cs₀ = [] := by
    cases cs₀ with
    | nil => rfl
    | cons q _ =>
        have qF := v₀.1.rows q (List.mem_cons_self ..)
        exact False.elim (closeRoot_waits label C x (predotU Q) r₀ d made g.opening rRefl qF.1
          (by simpa [eLocEq] using qF.2.2) admitted)
  subst csNil
  have bAcc : BagLaws acc₀ (predotU R) := by simpa [cooled] using v₀.2.2.1
  have sSub : StepRel Q R := ePr ▸ v₀.2.2.2
  obtain ⟨preR, postR, rfl⟩ := List.append_of_mem rMem
  obtain ⟨quoteEq, mkStep⟩ := listenerBridge hX sSub preR postR made
  have rInv' : RootCells (res label C (closeRootAt g.opening r₀ d made)).label
      (resConf label C (closeRootAt g.opening r₀ d made))
      (preR ++ (made, mkListener x R) :: postR) :=
    rootCells_closeRoot sys.rootInv
      ⟨w, known, _, _, _, by simpa [psubst_doneTok] using v₀.1.readsTok w known⟩
      admitted fun σ s => by
        have cr := (closeRoot_reads label C x (predotU Q) acc₀ r₀ d made g.opening rRefl
          (by simpa [eLocEq, ePar] using v₀.1.readsTok) s).2
        have accR : NameLaws (psubst σ (atLoc (pFor (tProc acc₀) x pZero) rootLoc))
            (psubst σ (atLoc (pFor (tProc (predotU R)) x pZero) rootLoc)) := by
          simp only [psubst_atLoc_any, psubst_pFor, psubst_tProc, psubst_rootLoc]
          exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr
            ⟨nameLaws_pFor_iff.mpr ⟨nameLaws_tProc (bagLaws_psubst σ bAcc), NameLaws.refl _, NameLaws.refl _⟩,
             NameLaws.refl _⟩
        refine (cr.trans accR).trans ?_
        simp only [psubst_atLoc_any, psubst_rootLoc]
        exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨quoteEq σ, NameLaws.refl _⟩
  obtain ⟨restA, pmA, pwRest, inRest⟩ := active_remove_one sys.activeApart e₀In
  have keepRest : ∀ e ∈ restA,
      e.Valid StepRel (res label C (closeRootAt g.opening r₀ d made)).label
        (resConf label C (closeRootAt g.opening r₀ d made)) := by
    intro e m; obtain ⟨eIn, ap⟩ := inRest e m
    exact (e.valid_keep_other (sys.activeValid e eIn) _ admitted
      (by rintro ⟨h | h, -⟩ <;> { have c := congrArg (fun rl => rl.body.take.length) h; simp [closeRootAt, closeRoot, commChild, closeChild] at c })
      (by rintro ⟨h, -⟩; have c := congrArg (fun rl => rl.body.take.length) h; simp [closeRootAt, closeRoot, heatChild] at c)
      (by rintro ⟨h, -⟩; have c := congrArg (fun rl => rl.body.checks.length) h; simp [closeRootAt, closeRoot, cool] at c)
      (by rintro (⟨_, σ, s, lE⟩ | ⟨h, -⟩)
          · exact ap σ (info_known _ s) (lE.symm.trans (locAll σ s))
          · have c := congrArg (fun rl => rl.body.take.length) h; simp [closeRootAt, closeRoot, closeChild] at c)).1
  let outRows := preR ++ (made, mkListener x R) :: postR
  have eqSrc : rootBagProcess (preR ++ (r₀, pReflect x Q) :: postR) =
      rootBagProcess (preR ++ (made, pReflect x Q) :: postR) := by
    simp [rootBagProcess]
  refine ⟨rootBagProcess outRows, mkStep (eqSrc ▸ sys.rootBag.symm), outRows, restA,
    ⟨w, solved⟩, noRootTokens_preserved sys.noRootTok _ admitted, rInv', ?_, BagEq.refl _,
    keepRest, pwRest.imp (apartOn_mono _), ?_⟩
  · intro q qM; simp only [outRows, List.mem_append, List.mem_cons] at qM
    rcases qM with inPre | rfl | inPost
    · exact sys.rootNodes q (List.mem_append_left _ inPre)
    · exact hListenerNode hX
    · exact sys.rootNodes q (List.mem_append_right _ (List.mem_cons_of_mem _ inPost))
  · intro z zP; rcases result_row zP with mMade | ⟨old, notT, -, -⟩
    · simp only [closeRootAt, List.mem_singleton] at mMade; subst mMade
      exact .inl (by simp [outRows])
    · have neR : z ≠ r₀ := fun e => notT (by simp [closeRootAt, e])
      have neD : z ≠ d := fun e => notT (by simp [closeRootAt, e])
      rcases sys.presentCover z old with inR | ⟨e, eIn, hE⟩
      · simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at inR
        rcases inR with inPre | rfl | inPost
        · exact .inl (by simp [outRows, inPre])
        · exact absurd rfl neR
        · exact .inl (by simp [outRows, inPost])
      · rcases List.mem_cons.mp (pmA.subset eIn) with rfl | inRestA
        · simp only [ActiveEntry.tok, ActiveEntry.cells, e₀Done, List.map_nil, List.not_mem_nil, or_false] at hE
          exact absurd hE neD
        · exact .inr ⟨e, inRestA, hE⟩

end RuleSteps

/-! ## Headline single-firing and multi-step backward stuttering reflection (`N` and `C`) -/

section BackwardTheorems

variable {O : Type*} [DecidableEq O]

/-- **Single-firing backward stuttering reflection — Interface N (named quotes)**:
Every admitted firing `g` of `located` at `QN` from a `BackwardReadyN` state in `SystemInvBy` is
either `Administrative` (preserving `SystemInvN` with the **same** source process `P`) or
`RootVisible` (producing `P'` with `BagStep conventional P P'` and `SystemInvN ... P'`). -/
theorem located_firing_backward_N {label : O → Pattern} {C : Configuration Pattern O} {P : Pattern}
    {rootRows : List (O × Pattern)} {active : List (ActiveEntry O)}
    (sys : SystemInvBy StepRelN label C P rootRows active)
    (ready : BackwardReadyN C rootRows active)
    (g : Firing O QNE located PUnit.unit)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g) :
    (Administrative g ∧ SystemInvN (res label C g).label (resConf label C g) P) ∨
    (RootVisible g ∧ ∃ P', BagStep conventional P P' ∧
      SystemInvN (res label C g).label (resConf label C g) P') := by
  rcases located_cases g.member with rC | rH | rCl | cC | cH | cCl | clR | clC | opR | opC
  · obtain ⟨P', bStep, -, inv'⟩ := step_rootComm sys ready.rootCommReady admitted rC
    exact .inr ⟨.inl rC, P', bStep, inv'⟩
  · exact .inl ⟨.inl rH, step_rootHeat sys admitted rH⟩
  · exact .inl ⟨.inr (.inl rCl), step_rootClear sys admitted rCl⟩
  · refine .inl ⟨.inr (.inr (.inl cC)), step_commChild_core sys
      (fun e eIn tk cs hP q₁ m₁ q₂ m₂ t ch A u ch' B ne e₁ e₂ =>
        ⟨ready.childCommReady e eIn tk cs hP q₁ m₁ q₂ m₂ t ch A u ch' B ne e₁ e₂,
         fun _ _ _ _ pm _ _ bStep _ => ?_⟩) admitted cC⟩
    have v := sys.activeValid e eIn; simp only [ActiveEntry.Valid, hP] at v
    exact .congruence (v.2.2.symm.trans (bagEq_pPar_perm (pm.map Prod.snd))) bStep (BagEq.refl _)
  · exact .inl ⟨.inr (.inr (.inr (.inl cH))), step_heatChild sys admitted cH⟩
  · exact .inl ⟨.inr (.inr (.inr (.inr (.inl cCl)))), step_cool sys admitted cCl⟩
  · refine .inr ⟨.inr clR, step_closeRoot_core sys ready.noCaptureRoot
      (fun x R => pFor (tProc R) x pZero) (fun hX => .guard hX)
      (fun {x Q R} hX sSub preR postR made => ⟨fun σ => ?_, fun bEq => ?_⟩) admitted clR⟩
    · rw [predotU_named_listener hX.1 R]; exact NameLaws.refl _
    · exact .congruence bEq
        (by simpa [rootBagProcess, List.map_append] using
          bagStep_of_pPar_refl (preR.map Prod.snd) (postR.map Prod.snd) x Q R sSub)
        (BagEq.refl _)
  · refine .inl ⟨.inr (.inr (.inr (.inr (.inr (.inl clC))))),
      step_closeChild_core sys ready.noCaptureChild (fun y R_in => pFor (tProc R_in) y pZero)
        (fun hY => .guard hY)
        (fun {e_p} epIn {tk reflIn d_g d_in madeL madeTok ρ preC postC y Q acc_g R_in}
          hPend hY pInv gInv bAcc sIn adm => ?_) admitted clC⟩
    have v := sys.activeValid e_p epIn; simp only [ActiveEntry.Valid, hPend] at v
    obtain ⟨dEq, -, -, dInvP, bStep⟩ := closeChild_commits_parent_N (m := e_p.parent) (x_l := e_p.chan)
      (P_l := predotU e_p.proc) hY.1 pInv gInv (fun σ _ => bagLaws_psubst σ bAcc) sIn adm
    exact ⟨dEq, dInvP, .congruence v.2.2.symm bStep (BagEq.refl _)⟩
  · exact .inl ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inl opR)))))), step_openRoot sys admitted opR⟩
  · exact .inl ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inr opC)))))), step_openChild sys admitted opC⟩

/-- **Single-firing backward stuttering reflection — Interface C (closed quotes)**:
Every admitted firing `g` of `located` at `QN` from a `BackwardReadyC` state in `SystemInvBy` is
either `Administrative` (preserving `SystemInvC` with the **same** source process `P`) or
`RootVisible` (producing `P'` with `CanonicalBagStep conventional P P'` and `SystemInvC ... P'`). -/
theorem located_firing_backward_C {label : O → Pattern} {C : Configuration Pattern O} {P : Pattern}
    {rootRows : List (O × Pattern)} {active : List (ActiveEntry O)}
    (sys : SystemInvBy StepRelC label C P rootRows active)
    (ready : BackwardReadyC C rootRows active)
    (g : Firing O QNE located PUnit.unit)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g) :
    (Administrative g ∧ SystemInvC (res label C g).label (resConf label C g) P) ∨
    (RootVisible g ∧ ∃ P', CanonicalBagStep conventional P P' ∧
      SystemInvC (res label C g).label (resConf label C g) P') := by
  rcases located_cases g.member with rC | rH | rCl | cC | cH | cCl | clR | clC | opR | opC
  · obtain ⟨P', -, cStep, inv'⟩ := step_rootComm sys ready.rootCommReady admitted rC
    exact .inr ⟨.inl rC, P', cStep, inv'⟩
  · exact .inl ⟨.inl rH, step_rootHeat sys admitted rH⟩
  · exact .inl ⟨.inr (.inl rCl), step_rootClear sys admitted rCl⟩
  · refine .inl ⟨.inr (.inr (.inl cC)), step_commChild_core sys
      (fun e eIn tk cs hP q₁ m₁ q₂ m₂ t ch A u ch' B ne e₁ e₂ => ?_) admitted cC⟩
    obtain ⟨admC, coGround⟩ := ready.childCommReady e eIn tk cs hP q₁ m₁ q₂ m₂ t ch A u ch' B ne e₁ e₂
    refine ⟨admC.1, fun _ bs gp rest pm _ _ _ cStep => ?_⟩
    have v := sys.activeValid e eIn; simp only [ActiveEntry.Valid, hP] at v
    obtain ⟨gA, gB⟩ := admC.2 bs gp
    obtain ⟨out₁, ndTail⟩ := List.nodup_cons.mp ((pm.map Prod.fst).nodup_iff.mp v.1.nodup)
    obtain ⟨out₂, -⟩ := List.nodup_cons.mp ndTail
    refine ⟨.congruence (v.2.2.symm.trans (bagEq_pPar_perm (pm.map Prod.snd))) cStep (BagEq.refl _),
      pvars_pPar_eq_nil fun p pM => ?_⟩
    obtain ⟨q, qM, rfl⟩ := List.mem_map.mp pM
    rcases List.mem_append.mp qM with inRest | inOut
    · have inCs : q ∈ cs := pm.symm.subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ inRest))
      have qInF : q.1 ∈ rest.map Prod.fst := List.mem_map.mpr ⟨q, inRest, rfl⟩
      exact coGround q inCs
        (fun eq₁ => out₁ (List.mem_cons_of_mem _ (eq₁ ▸ qInF)))
        (fun eq₂ => out₂ (eq₂ ▸ qInF))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at inOut
      rcases inOut with rfl | rfl
      · exact gA
      · exact gB
  · exact .inl ⟨.inr (.inr (.inr (.inl cH))), step_heatChild sys admitted cH⟩
  · exact .inl ⟨.inr (.inr (.inr (.inr (.inl cCl)))), step_cool sys admitted cCl⟩
  · refine .inr ⟨.inr clR, step_closeRoot_core sys ready.noCaptureRoot
      listener (fun hX => .guard hX)
      (fun {x Q R} hX sSub preR postR made => ⟨fun σ => ?_, fun bEq => ?_⟩) admitted clR⟩
    · rw [predotU_closed_listener hX.1 R]
      exact nameLaws_psubst σ (nameLaws_pFor_iff.mpr
        ⟨nameLaws_tProc (quote_closed_ground R sSub.2).symm, NameLaws.refl _, NameLaws.refl _⟩)
    · exact .congruence bEq
        (by simpa [rootBagProcess, List.map_append] using
          canonicalBagStep_of_pPar_refl (preR.map Prod.snd) (postR.map Prod.snd) x Q R sSub.1)
        (BagEq.refl _)
  · refine .inl ⟨.inr (.inr (.inr (.inr (.inr (.inl clC))))),
      step_closeChild_core sys ready.noCaptureChild listener (fun hY => .guard hY)
        (fun {e_p} epIn {tk reflIn d_g d_in madeL madeTok ρ preC postC y Q acc_g R_in}
          hPend hY pInv gInv bAcc sIn adm => ?_) admitted clC⟩
    have v := sys.activeValid e_p epIn; simp only [ActiveEntry.Valid, hPend] at v
    obtain ⟨dEq, -, -, dInvP, cStep⟩ := closeChild_commits_parent_C (m := e_p.parent) (x_l := e_p.chan)
      (P_l := predotU e_p.proc) hY.1 sIn.2 pInv gInv (fun σ _ => bagLaws_psubst σ bAcc) sIn.1 adm
    have pmC : ((preC ++ (reflIn, pReflect y Q) :: postC).map Prod.fst).Perm
        (reflIn :: (preC ++ postC).map Prod.fst) := by
      simp only [List.map_append, List.map_cons]; exact List.perm_middle
    obtain ⟨rOut, -⟩ := List.nodup_cons.mp (pmC.nodup_iff.mp pInv.nodup)
    have coGround := ready.childCloseReady e_p epIn tk _ hPend (reflIn, pReflect y Q) (by simp) y Q rfl
    refine ⟨dEq, dInvP, ⟨.congruence v.2.2.symm cStep (BagEq.refl _),
      pvars_pPar_eq_nil fun p pM => ?_⟩⟩
    obtain ⟨q, qM, rfl⟩ := List.mem_map.mp pM
    rcases List.mem_append.mp qM with inRest | inOut
    · have inCs : q ∈ preC ++ (reflIn, pReflect y Q) :: postC :=
        (List.mem_append.mp inRest).elim (List.mem_append_left _)
          (fun r => List.mem_append_right _ (List.mem_cons_of_mem _ r))
      exact coGround q inCs (fun eqR => by
        have eqR' : q.1 = reflIn := eqR
        exact rOut (eqR' ▸ List.mem_map.mpr ⟨q, inRest, rfl⟩))
    · simp only [List.mem_singleton] at inOut; subst inOut
      exact pvars_listener_eq_nil hY.1 sIn.2
  · exact .inl ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inl opR)))))), step_openRoot sys admitted opR⟩
  · exact .inl ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inr opC)))))), step_openChild sys admitted opC⟩

/-- Multi-step ready run under **Interface N** (arbitrary interleavings of `located` firings). -/
inductive ReadyLocatedRunN :
    (O → Pattern) → Configuration Pattern O → Pattern →
    (O → Pattern) → Configuration Pattern O → Prop where
  | refl {label : O → Pattern} {C : Configuration Pattern O} {P : Pattern}
      (inv : SystemInvN label C P) : ReadyLocatedRunN label C P label C
  | step {label label' : O → Pattern} {C C' : Configuration Pattern O} {P : Pattern}
      {rootRows : List (O × Pattern)} {active : List (ActiveEntry O)}
      (sys : SystemInvBy StepRelN label C P rootRows active)
      (ready : BackwardReadyN C rootRows active)
      (g : Firing O QNE located PUnit.unit)
      (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
      (next : ∀ P₁, SystemInvN (res label C g).label (resConf label C g) P₁ →
        ReadyLocatedRunN (res label C g).label (resConf label C g) P₁ label' C') :
      ReadyLocatedRunN label C P label' C'

/-- **Multi-step backward stuttering reflection — Interface N**: every `ReadyLocatedRunN` from `P`
reflects to `Relation.ReflTransGen (BagStep conventional) P P'` with `SystemInvN label' C' P'`. -/
theorem located_run_backward_N {label label' : O → Pattern} {C C' : Configuration Pattern O}
    {P : Pattern} (run : ReadyLocatedRunN label C P label' C') :
    ∃ P', Relation.ReflTransGen (BagStep conventional) P P' ∧ SystemInvN label' C' P' := by
  induction run with
  | refl inv => exact ⟨_, .refl, inv⟩
  | step sys ready g admitted _ ih =>
      rcases located_firing_backward_N sys ready g admitted with ⟨-, inv₁⟩ | ⟨-, P₁, st₁, inv₁⟩
      · exact ih _ inv₁
      · obtain ⟨P', rt, inv'⟩ := ih P₁ inv₁
        exact ⟨P', Relation.ReflTransGen.head st₁ rt, inv'⟩

/-- Multi-step ready run under **Interface C** (arbitrary interleavings of `located` firings). -/
inductive ReadyLocatedRunC :
    (O → Pattern) → Configuration Pattern O → Pattern →
    (O → Pattern) → Configuration Pattern O → Prop where
  | refl {label : O → Pattern} {C : Configuration Pattern O} {P : Pattern}
      (inv : SystemInvC label C P) : ReadyLocatedRunC label C P label C
  | step {label label' : O → Pattern} {C C' : Configuration Pattern O} {P : Pattern}
      {rootRows : List (O × Pattern)} {active : List (ActiveEntry O)}
      (sys : SystemInvBy StepRelC label C P rootRows active)
      (ready : BackwardReadyC C rootRows active)
      (g : Firing O QNE located PUnit.unit)
      (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
      (next : ∀ P₁, SystemInvC (res label C g).label (resConf label C g) P₁ →
        ReadyLocatedRunC (res label C g).label (resConf label C g) P₁ label' C') :
      ReadyLocatedRunC label C P label' C'

/-- **Multi-step backward stuttering reflection — Interface C**: every `ReadyLocatedRunC` from `P`
reflects to `Relation.ReflTransGen (CanonicalBagStep conventional) P P'` with
`SystemInvC label' C' P'`. -/
theorem located_run_backward_C {label label' : O → Pattern} {C C' : Configuration Pattern O}
    {P : Pattern} (run : ReadyLocatedRunC label C P label' C') :
    ∃ P', Relation.ReflTransGen (CanonicalBagStep conventional) P P' ∧ SystemInvC label' C' P' := by
  induction run with
  | refl inv => exact ⟨_, .refl, inv⟩
  | step sys ready g admitted _ ih =>
      rcases located_firing_backward_C sys ready g admitted with ⟨-, inv₁⟩ | ⟨-, P₁, st₁, inv₁⟩
      · exact ih _ inv₁
      · obtain ⟨P', rt, inv'⟩ := ih P₁ inv₁
        exact ⟨P', Relation.ReflTransGen.head st₁ rt, inv'⟩

end BackwardTheorems

#print axioms located_firing_backward_N
#print axioms located_firing_backward_C
#print axioms located_run_backward_N
#print axioms located_run_backward_C

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem
