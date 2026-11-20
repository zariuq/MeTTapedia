import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystemRecursionBase

/-!
# Recursive reflection through the inner close (`P4`)

This module proves the forward arbitrary-depth reflection theorems (`P4`) at the name frame `QN`:

* **Master forward depth-`d` induction** (`child_pack_of_packStep`, `child_pack_of_subStep_N`,
  `child_pack_of_subStep_C`): by explicit structural induction on the reflection depth `d : ℕ`,
  an inner `closeChildAt` (`child_closes_once_S`) acts as the parent child's one step across
  arbitrarily nested `Child(Child(...))` locations, packs all cells into a single `Done` token
  modulo `BagLaws`, restores `CleanAboveDepth`, and extends solutions (`FreeOnPats`).
* **Whole-system recursive `REFL` forward at `Root`** (`refl_depth_root_pack`,
  `refl_depth_root_forward_N`, `refl_depth_root_forward_C`): lifts any depth-`d` inner derivation
  to a root `REFL` step inside a multi-row `RootCells` configuration under both **Interface N**
  (`BagStep` and `ReflClosureDepth`) and **Interface C** (`CanonicalBagStep` on ground reducts).
* **Concrete nested-reflection showcases** (`nested_canary_hosted_N`, `nested_canary_hosted_C`,
  `nested_openReduct_hosted_N`): hosts both `@0?(@0?(for((0) <- @0)0 | for(y <- @0)y))` (under
  **N** and **C**) and `@0?(@0?(for(a1 <- @0)a1 | for(0 <- @0)a))` (whose inner reduct carries a
  free variable `"a"`, matching `CorrectedControls.corrected_nested`, hosted under **N**).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar nQuote tProc pReflect
  applyDot demoChan)
open MeTTaOperationsComm (psubst PSubst pvars dotted GroundPrincipal)
open MeTTaCalculus.Corrected (BagStep CanonicalBagStep conventional listener)
open FiniteProgram (predot predot_pFor)
open OneFrame (embed)
open ReflQuotient (BagLaws)
open ReflNames (NameLaws nameAction QN QNE nameLaws_heads nameLaws_pFor_iff nameLaws_tProc
  nameLaws_psubst)
open ReflLocated (atLoc rootLoc childLoc pendingTok doneTok located exists_mem_zip psubst_rootLoc
  psubst_atLoc_any psubst_pendingTok psubst_par locatedFrame_name)
open ReflPacking (cooled psubst_doneTok nameLaws_doneTok_iff bagLaws_cooled_zero)
open ReflLocatedStep (psubst_childLoc res resConf info_known solution_of_admitted result_present
  result_label_old commChildAt closeChildAt psubst_pReflect nameLaws_pReflect_iff)
open ReflUniform (predotU predotU_pPar predotU_ground)
open ReflCorrespondence (Clean LocatedRun Splits openRootAt closeRootAt openRoot_admitted
  openRoot_reads closeRoot_admitted closeRoot_reads open_fresh_exists close_fresh_exists
  commit_fresh_exists commit_present commit_label_old commit_back child_commit exists_fresh_list
  open_present open_label_old close_present openRoot_extends)

section ForwardRecursion

variable {O : Type*} [DecidableEq O]

/-- **Master forward child-segment packing by explicit structural induction on reflection depth `d`**
across arbitrarily nested `Child(Child(...))` locations. -/
theorem child_pack_of_packStep [Infinite O] {d : ℕ} {P R : Pattern}
    {pair : Pattern × Pattern} {bs : Bindings} (sub : HostedPackStep d P R pair bs) :
    ∀ {m : Pattern}, IsLocSpine m → ∀ (x_l : Pattern) (label : O → Pattern)
      (C : Configuration Pattern O) (pr tk : O) (extPats : List Pattern),
      let l := childLoc m x_l (predotU P)
      PendingPhaseS l m label C tk →
      pr ∈ C.present → pr ≠ tk →
      (∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label pr)) (psubst σ (atLoc (predotU P) l))) →
      (∀ o ∈ C.present, o ≠ pr → ∀ σ : PSubst, nameAction.Models σ C.equations →
        ∀ y : Pattern, ¬ NameLaws (psubst σ (label o)) (atLoc y (psubst σ l))) →
      CleanAboveDepth (locDepth l) label C →
      (∀ q ∈ extPats, ∀ v ∈ pvars q, v ∉ pvars pair.1 ++ pvars pair.2) →
      FreeOnPats (pair.1 :: pair.2 :: extPats) C.equations →
      (∀ q ∈ extPats, ∃ o' ∈ C.present, o' ≠ pr ∧ o' ≠ tk ∧ ∃ R' l' : Pattern,
        (∀ σ : PSubst, nameAction.Models σ C.equations →
          NameLaws (psubst σ (label o')) (psubst σ (atLoc R' l'))) ∧
        SpineHasPattern q R') →
      ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (d' : O) (acc : Pattern),
        LocatedRunNoRoot label C label' C' false ∧
        DonePhaseS l m label' C' d' ∧
        (∀ σ : PSubst, nameAction.Models σ C'.equations →
          NameLaws (psubst σ (label' d')) (psubst σ (doneTok l m acc))) ∧
        BagLaws acc (predotU R) ∧
        (∀ o ∈ C'.present, ∀ σ : PSubst, nameAction.Models σ C'.equations →
          ∀ y : Pattern, ¬ NameLaws (psubst σ (label' o)) (atLoc y (psubst σ l))) ∧
        (∀ o ∈ C'.present, o = d' ∨ (o ∈ C.present ∧ o ≠ pr ∧ o ≠ tk ∧ label' o = label o)) ∧
        (∀ o ∈ C.present, o ≠ pr → o ≠ tk → o ∈ C'.present ∧ label' o = label o) ∧
        CleanAboveDepth (locDepth l) label' C' ∧
        FreeOnPats extPats C'.equations ∧
        (∀ σ : PSubst, nameAction.Models σ C'.equations → nameAction.Models σ C.equations) := by
  induction sub with
  | @congr d P R R' pair bs base bagU ih =>
      intro m spM x_l label C pr tk extPats l phase prPres prNeTk readsPr onlyPr cleanBelow
        disj free anchExt
      obtain ⟨label', C', d', acc, run, done', rD', bagAcc, packed, cov, keep, clean', free',
        mono⟩ := ih spM x_l label C pr tk extPats phase prPres prNeTk readsPr onlyPr cleanBelow
          disj free anchExt
      exact ⟨label', C', d', acc, run, done', rD', bagAcc.trans bagU, packed, cov, keep, clean',
        free', mono⟩
  | @comm P cPre cMid cPost t u ch A B bs split noBT noBU groundCh noBA noBB plainOutA plainOutB
      gp conv foA foB groundT groundU canonicalT canonicalU =>
      have ⟨solvesTU, hasT, hasU⟩ :=
        (HostedPackStep.comm cPre cMid cPost t u ch A B bs split noBT noBU groundCh noBA noBB
          plainOutA plainOutB gp conv foA foB groundT groundU canonicalT canonicalU).solves
      intro m spM x_l label C pr tk extPats l phase prPres prNeTk readsPr onlyPr cleanBelow
        disj free anchExt
      have spL : IsLocSpine l := .child x_l (predotU P) spM
      obtain ⟨σ_init, known_init⟩ := freeOnPats_consistent free
      obtain ⟨label₂, C₂, rows, runH, lenR, ndR, readsR, factsR, frameH, covH, monoH, extH, _⟩ :=
        heating_noRoot l m (splits_map_predotU split) label C pr tk prPres phase.present prNeTk
          readsPr phase.reads ⟨σ_init, known_init⟩
      have lenMap : rows.length =
          (cPre.map predotU ++ predotU (pFor t ch A) ::
            (cMid.map predotU ++ predotU (pFor u ch B) :: cPost.map predotU)).length := by
        simpa [List.map_append] using lenR
      obtain ⟨rPre, first, rMid, second, rPost, rowsEq, lPre, lMid, lPost⟩ := split_rows_2 lenMap
      have permR : rows.Perm (first :: second :: (rPre ++ rMid ++ rPost)) := by
        rw [rowsEq]
        exact List.perm_middle.trans
          (List.Perm.cons _ (by rw [← List.append_assoc]; exact List.perm_middle))
      obtain ⟨firstOut, ndFront⟩ := List.nodup_cons.mp (permR.nodup_iff.mp ndR)
      obtain ⟨secondOut, ndRest⟩ := List.nodup_cons.mp ndFront
      have firstNeSecond : first ≠ second := fun e => firstOut (by simp [e])
      have firstIn : first ∈ rows := permR.symm.subset (List.mem_cons_self ..)
      have secondIn : second ∈ rows :=
        permR.symm.subset (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have restInRows : ∀ r ∈ rPre ++ rMid ++ rPost, r ∈ rows := fun r rIn =>
        permR.symm.subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ rIn))
      have firstZip : (first, predotU (pFor t ch A)) ∈
          rows.zip ((cPre ++ pFor t ch A :: (cMid ++ pFor u ch B :: cPost)).map predotU) := by
        simp only [rowsEq, List.map_append, List.map_cons]
        rw [List.zip_append lPre]; exact List.mem_append_right _ (List.mem_cons_self ..)
      have secondZip : (second, predotU (pFor u ch B)) ∈
          rows.zip ((cPre ++ pFor t ch A :: (cMid ++ pFor u ch B :: cPost)).map predotU) := by
        simp only [rowsEq, List.map_append, List.map_cons]
        rw [List.zip_append lPre, List.zip_cons_cons, List.zip_append lMid]
        exact List.mem_append_right _ (List.mem_cons_of_mem _
          (List.mem_append_right _ (List.mem_cons_self ..)))
      have rFirst : ∀ σ : PSubst, nameAction.Models σ C₂.equations →
          NameLaws (psubst σ (label₂ first)) (psubst σ (atLoc (predot (pFor t ch A)) l)) := by
        intro σ s; have r := readsR _ firstZip σ s
        rwa [predotU_pFor_eq_predot_plain noBT groundCh noBA] at r
      have rSecond : ∀ σ : PSubst, nameAction.Models σ C₂.equations →
          NameLaws (psubst σ (label₂ second)) (psubst σ (atLoc (predot (pFor u ch B)) l)) := by
        intro σ s; have r := readsR _ secondZip σ s
        rwa [predotU_pFor_eq_predot_plain noBU groundCh noBB] at r
      have tokKept₂ := frameH tk phase.present prNeTk.symm
      have phase₂ : PendingPhaseS l m label₂ C₂ tk := by
        refine ⟨tokKept₂.1, fun σ s => by rw [tokKept₂.2]; exact phase.reads σ (monoH σ s), ?_, ?_⟩
        · rintro o oP ⟨σ, s, m', same⟩
          rcases covH o oP with inRows | ⟨inC, _, lblEq⟩
          · obtain ⟨p_o, z_o⟩ := exists_mem_zip lenR inRows
            have both := same.symm.trans (readsR (o, p_o) z_o σ s); rw [psubst_atLoc_any] at both
            exact absurd (nameLaws_heads both) (by decide)
          · rw [lblEq] at same; exact phase.unique o inC ⟨σ, monoH σ s, m', same⟩
        · rintro o oP ⟨σ, s, m', c', same⟩
          rcases covH o oP with inRows | ⟨inC, _, lblEq⟩
          · obtain ⟨p_o, z_o⟩ := exists_mem_zip lenR inRows
            have both := same.symm.trans (readsR (o, p_o) z_o σ s); rw [psubst_atLoc_any] at both
            exact absurd (nameLaws_heads both) (by decide)
          · rw [lblEq] at same; exact phase.noDone o inC ⟨σ, monoH σ s, m', c', same⟩
      obtain ⟨σ_u, k_u, unif_u, -⟩ := freeOnPats_glue_unifier solvesTU disj free (fun _ => none)
      obtain ⟨w₂_u, s₂_u, ag₂_u⟩ := extH σ_u k_u
      have onP_u := pending_anchor_P phase.reads monoH s₂_u k_u (ag₂_u tk phase.present prNeTk.symm)
      have unifies₂ : NameLaws (psubst w₂_u t) (psubst w₂_u u) :=
        (spineHasPattern_nameLaws hasT onP_u).trans
          (unif_u.trans (spineHasPattern_nameLaws hasU onP_u).symm)
      obtain ⟨madeIds, lenMade, ndMade, freshMade⟩ := exists_fresh_list C₂.present 3
      obtain ⟨made₁, made₂, madeTok, rfl⟩ : ∃ a b c, madeIds = [a, b, c] := by
        match madeIds, lenMade with | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
      have distTaken : [first, second, tk].Nodup := by
        simp [firstNeSecond, (factsR first firstIn).2.1, (factsR second secondIn).2.1]
      have freshM₁ : made₁ ∉ C₂.present := freshMade made₁ (by simp)
      have freshM₂ : made₂ ∉ C₂.present := freshMade made₂ (by simp)
      have freshMT : madeTok ∉ C₂.present := freshMade madeTok (by simp)
      have m₁NeM₂ : made₁ ≠ made₂ := fun e => (List.nodup_cons.mp ndMade).1 (by simp [e])
      have m₁NeMT : made₁ ≠ madeTok := fun e => (List.nodup_cons.mp ndMade).1 (by simp [e])
      have m₂NeMT : made₂ ≠ madeTok :=
        fun e => (List.nodup_cons.mp (List.nodup_cons.mp ndMade).2).1 (by simp [e])
      obtain ⟨ρc, freshC⟩ := commit_fresh_exists label₂ C₂ first second tk made₁ made₂ madeTok
      obtain ⟨committed, commitR⟩ := child_commit label₂ C₂ t u ch A B l m bs gp conv foA foB
        groundT groundU canonicalT canonicalU first second tk made₁ made₂ madeTok rFirst rSecond
        phase₂.reads distTaken ndMade
        ⟨(factsR first firstIn).1, (factsR second secondIn).1, phase₂.present⟩
        ⟨freshM₁, freshM₂, freshMT⟩ s₂_u unifies₂ freshC
      obtain ⟨-, _, d_tmp, done₃'⟩ := child_steps_once_S label₂ C₂ phase₂ t u (predot ch)
        (dotted (pvars t) (predot A)) (dotted (pvars u) (predot B)) first second made₁ made₂
        madeTok (fun σ s => by have r := rFirst σ s; rwa [predot_pFor] at r)
        (fun σ s => by have r := rSecond σ s; rwa [predot_pFor] at r)
        distTaken ndMade ⟨(factsR first firstIn).1, (factsR second secondIn).1⟩
        ⟨freshM₁, freshM₂, freshMT⟩ s₂_u unifies₂ freshC
      obtain ⟨σ₃_0, sol₃_0⟩ := solution_of_admitted committed
      have mtEq : madeTok = d_tmp := done₃'.unique madeTok
        ((commit_present label₂ C₂ ρc first second tk made₁ made₂ madeTok madeTok).mpr
          (.inr (.inr (.inr rfl))))
        ⟨σ₃_0, sol₃_0, _, _, by simpa [psubst_doneTok] using (commitR σ₃_0 sol₃_0).2.2.2⟩
      subst mtEq
      let label₃ := (res label₂ C₂ (commChildAt ρc first second tk made₁ made₂ madeTok)).label
      let C₃ := resConf label₂ C₂ (commChildAt ρc first second tk made₁ made₂ madeTok)
      let remCells : List (O × Pattern) :=
        rPre.zip (cPre.map predotU) ++ rMid.zip (cMid.map predotU) ++ rPost.zip (cPost.map predotU)
      let order : List (O × Pattern) :=
        remCells ++ [(made₁, predotU (applyDot bs A)), (made₂, predotU (applyDot bs B))]
      have remFst : remCells.map Prod.fst = rPre ++ rMid ++ rPost := by
        simp [remCells, List.map_fst_zip (by simp [lPre] : rPre.length ≤ (cPre.map predotU).length),
          List.map_fst_zip (by simp [lMid] : rMid.length ≤ (cMid.map predotU).length),
          List.map_fst_zip (by simp [lPost] : rPost.length ≤ (cPost.map predotU).length)]
      have remSnd : remCells.map Prod.snd = (cPre ++ cMid ++ cPost).map predotU := by
        simp [remCells, List.map_snd_zip (by simp [lPre] : (cPre.map predotU).length ≤ rPre.length),
          List.map_snd_zip (by simp [lMid] : (cMid.map predotU).length ≤ rMid.length),
          List.map_snd_zip (by simp [lPost] : (cPost.map predotU).length ≤ rPost.length),
          List.append_assoc]
      have orderFst : order.map Prod.fst = (rPre ++ rMid ++ rPost) ++ [made₁, made₂] := by
        simp [order, remFst]
      have orderSnd : order.map Prod.snd =
          ((cPre ++ cMid ++ cPost) ++ [applyDot bs A, applyDot bs B]).map predotU := by
        simp [order, remSnd, List.append_assoc]
      have remInZip : ∀ q ∈ remCells,
          q ∈ rows.zip ((cPre ++ pFor t ch A :: (cMid ++ pFor u ch B :: cPost)).map predotU) := by
        intro q qM; simp only [rowsEq, List.map_append, List.map_cons]
        rw [List.zip_append lPre, List.zip_cons_cons, List.zip_append lMid, List.zip_cons_cons]
        simp only [remCells, List.mem_append] at qM
        rcases qM with (inPre | inMid) | inPost
        · exact List.mem_append_left _ inPre
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ inMid))
        · exact List.mem_append_right _ (List.mem_cons_of_mem _
            (List.mem_append_right _ (List.mem_cons_of_mem _ inPost)))
      have ndOrder : (order.map Prod.fst).Nodup := by
        rw [orderFst]; refine List.nodup_append.mpr ⟨ndRest, by simp [m₁NeM₂], fun a inR b inM ab => ?_⟩
        have aPres := (factsR a (restInRows a inR)).1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inM
        rcases inM with rfl | rfl
        · exact freshM₁ (ab ▸ aPres)
        · exact freshM₂ (ab ▸ aPres)
      have orderPres : ∀ q ∈ order, q.1 ∈ C₃.present ∧ q.1 ≠ madeTok := by
        intro q qM; rcases List.mem_append.mp qM with inRem | inM
        · have qInFst : q.1 ∈ rPre ++ rMid ++ rPost := remFst ▸ List.mem_map.mpr ⟨q, inRem, rfl⟩
          have qF := factsR q.1 (restInRows q.1 qInFst)
          have neF : q.1 ≠ first := fun e => firstOut (List.mem_cons_of_mem _ (e ▸ qInFst))
          have neS : q.1 ≠ second := fun e => secondOut (e ▸ qInFst)
          exact ⟨(commit_present label₂ C₂ ρc first second tk made₁ made₂ madeTok q.1).mpr
            (.inl ⟨qF.1, neF, neS, qF.2.1⟩), fun e => freshMT (e ▸ qF.1)⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at inM
          rcases inM with rfl | rfl
          · exact ⟨(commit_present label₂ C₂ ρc first second tk made₁ made₂ madeTok made₁).mpr
              (.inr (.inl rfl)), m₁NeMT⟩
          · exact ⟨(commit_present label₂ C₂ ρc first second tk made₁ made₂ madeTok made₂).mpr
              (.inr (.inr (.inl rfl))), m₂NeMT⟩
      have orderReads : ∀ q ∈ order, ∀ σ : PSubst, nameAction.Models σ C₃.equations →
          NameLaws (psubst σ (label₃ q.1)) (psubst σ (atLoc q.2 l)) := by
        intro q qM σ s; rcases List.mem_append.mp qM with inRem | inM
        · have qInFst : q.1 ∈ rPre ++ rMid ++ rPost := remFst ▸ List.mem_map.mpr ⟨q, inRem, rfl⟩
          have qPres := (factsR q.1 (restInRows q.1 qInFst)).1
          dsimp only [label₃]
          rw [commit_label_old label₂ C₂ ρc first second tk made₁ made₂ madeTok
            (fun e => freshM₁ (e ▸ qPres)) (fun e => freshM₂ (e ▸ qPres))
            (fun e => freshMT (e ▸ qPres))]
          exact readsR q (remInZip q inRem) σ (commit_back label₂ C₂ ρc first second tk
            made₁ made₂ madeTok s)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at inM
          rcases inM with rfl | rfl
          · rw [predotU_eq_predot_of_plain (applyDot bs A) plainOutA]; exact (commitR σ s).2.1
          · rw [predotU_eq_predot_of_plain (applyDot bs B) plainOutB]; exact (commitR σ s).2.2.1
      obtain ⟨supply, lenSup, ndSup, freshSup⟩ := exists_fresh_list C₃.present order.length
      obtain ⟨label₄, C₄, d₄, runCool, _, pD₄, rD₄, monoCool, extCool, _, covCool, keepCool⟩ :=
        cooling_noRoot_extends l m order supply label₃ C₃ madeTok pZero lenSup ndSup freshSup
          done₃'.present ndOrder orderPres orderReads (fun σ s => (commitR σ s).2.2.2) ⟨σ₃_0, sol₃_0⟩
      have cov₄ : ∀ o ∈ C₄.present,
          o = d₄ ∨ (o ∈ C.present ∧ o ≠ pr ∧ o ≠ tk ∧ label₄ o = label o) := by
        intro o oP; rcases covCool o oP with isD | ⟨inC₃, notOrd, neMT, l₄⟩
        · exact .inl isD
        · rcases (commit_present label₂ C₂ ρc first second tk made₁ made₂ madeTok o).mp inC₃ with
            ⟨inC₂, neF, neS, neTk⟩ | isM₁ | isM₂ | isMT
          · rcases covH o inC₂ with inRows | ⟨inC, nePr, l₂⟩
            · rcases List.mem_cons.mp (permR.subset inRows) with rfl | inTail
              · exact absurd rfl neF
              · rcases List.mem_cons.mp inTail with rfl | inRemFst
                · exact absurd rfl neS
                · exact absurd (by rw [orderFst]; exact List.mem_append_left _ inRemFst) notOrd
            · have l₃ : label₃ o = label₂ o := commit_label_old label₂ C₂ ρc first second tk
                made₁ made₂ madeTok (fun e => freshM₁ (e ▸ inC₂)) (fun e => freshM₂ (e ▸ inC₂))
                (fun e => freshMT (e ▸ inC₂))
              exact .inr ⟨inC, nePr, neTk, l₄.trans (l₃.trans l₂)⟩
          · exact absurd (by rw [orderFst, isM₁]; simp) notOrd
          · exact absurd (by rw [orderFst, isM₂]; simp) notOrd
          · exact absurd isMT neMT
      have keep₄ : ∀ o ∈ C.present, o ≠ pr → o ≠ tk → o ∈ C₄.present ∧ label₄ o = label o := by
        intro o inC nePr neTk
        obtain ⟨inC₂, l₂⟩ := frameH o inC nePr
        have notRows : o ∉ rows := fun inR =>
          (factsR o inR).2.2.elim (fun e => nePr e) (fun nC => nC inC)
        have neF : o ≠ first := fun e => notRows (e ▸ firstIn)
        have neS : o ≠ second := fun e => notRows (e ▸ secondIn)
        have neM₁ : o ≠ made₁ := fun e => freshM₁ (e ▸ inC₂)
        have neM₂ : o ≠ made₂ := fun e => freshM₂ (e ▸ inC₂)
        have neMT : o ≠ madeTok := fun e => freshMT (e ▸ inC₂)
        have inC₃ := (commit_present label₂ C₂ ρc first second tk made₁ made₂ madeTok o).mpr
          (.inl ⟨inC₂, neF, neS, neTk⟩)
        have l₃ : label₃ o = label₂ o :=
          commit_label_old label₂ C₂ ρc first second tk made₁ made₂ madeTok neM₁ neM₂ neMT
        have notOrd : o ∉ order.map Prod.fst := by
          rw [orderFst]; intro inM
          rcases List.mem_append.mp inM with inRem | inMade
          · exact notRows (restInRows o inRem)
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at inMade
            exact inMade.elim neM₁ neM₂
        obtain ⟨inC₄, l₄⟩ := keepCool o inC₃ notOrd neMT
        exact ⟨inC₄, l₄.trans (l₃.trans l₂)⟩
      have monoAll : ∀ σ : PSubst, nameAction.Models σ C₄.equations →
          nameAction.Models σ C.equations :=
        fun σ s => monoH σ (commit_back label₂ C₂ ρc first second tk made₁ made₂ madeTok
          (monoCool σ s))
      have done₄ := donePhaseS_after_cool done₃' pD₄ rD₄ monoCool covCool
      have packed₄ : ∀ o ∈ C₄.present, ∀ σ : PSubst, nameAction.Models σ C₄.equations →
          ∀ y : Pattern, ¬ NameLaws (psubst σ (label₄ o)) (atLoc y (psubst σ l)) := by
        intro o oP σ s y same
        rcases cov₄ o oP with rfl | ⟨inC, nePr, -, lblEq⟩
        · have both := same.symm.trans (rD₄ σ s); rw [psubst_doneTok] at both
          exact absurd (nameLaws_heads both) (by decide)
        · rw [lblEq] at same; exact onlyPr o inC nePr σ (monoAll σ s) y same
      have clean₄ : CleanAboveDepth (locDepth l) label₄ C₄ :=
        cleanAboveDepth_of_subset cleanBelow monoAll fun o oP => by
          rcases cov₄ o oP with rfl | ⟨inC, -, -, lblEq⟩
          · exact .inr ⟨l, spL, le_rfl, fun σ s => .inr (.inr ⟨_, _, by
              simpa [psubst_doneTok] using rD₄ σ s⟩)⟩
          · exact .inl ⟨inC, lblEq⟩
      have free₄ : FreeOnPats extPats C₄.equations := by
        intro τ₀
        obtain ⟨σ₀, k₀, unif₀, ag₀⟩ := freeOnPats_glue_unifier solvesTU disj free τ₀
        obtain ⟨w₂, s₂, ag₂⟩ := extH σ₀ k₀
        have onP₂ := pending_anchor_P phase.reads monoH s₂ k₀ (ag₂ tk phase.present prNeTk.symm)
        have unif₂ : NameLaws (psubst w₂ t) (psubst w₂ u) :=
          (spineHasPattern_nameLaws hasT onP₂).trans
            (unif₀.trans (spineHasPattern_nameLaws hasU onP₂).symm)
        obtain ⟨w₃, s₃, ag₃⟩ := commChild_extends label₂ C₂ t u (predot ch)
          (dotted (pvars t) (predot A)) (dotted (pvars u) (predot B)) l m first second tk
          made₁ made₂ madeTok (fun σ s => by have r := rFirst σ s; rwa [predot_pFor] at r)
          (fun σ s => by have r := rSecond σ s; rwa [predot_pFor] at r) phase₂.reads
          (factsR first firstIn).1 (factsR second secondIn).1 phase₂.present freshC s₂ unif₂
        obtain ⟨w₄, s₄, ag₄⟩ := extCool w₃ s₃
        refine ⟨w₄, s₄, fun q qIn => ?_⟩
        obtain ⟨o', inC, nePr, neTk, R', l', rO', hasQ⟩ := anchExt q qIn
        obtain ⟨inC₂, l₂⟩ := frameH o' inC nePr
        have notRows : o' ∉ rows := fun inR =>
          (factsR o' inR).2.2.elim (fun e => nePr e) (fun nC => nC inC)
        have neM₁ : o' ≠ made₁ := fun e => freshM₁ (e ▸ inC₂)
        have neM₂ : o' ≠ made₂ := fun e => freshM₂ (e ▸ inC₂)
        have neMT : o' ≠ madeTok := fun e => freshMT (e ▸ inC₂)
        have inC₃ := (commit_present label₂ C₂ ρc first second tk made₁ made₂ madeTok o').mpr
          (.inl ⟨inC₂, fun e => notRows (e ▸ firstIn), fun e => notRows (e ▸ secondIn), neTk⟩)
        have l₃ : label₃ o' = label₂ o' :=
          commit_label_old label₂ C₂ ρc first second tk made₁ made₂ madeTok neM₁ neM₂ neMT
        have notOrd : o' ∉ order.map Prod.fst := by
          rw [orderFst]; intro inM
          rcases List.mem_append.mp inM with inRem | inMade
          · exact notRows (restInRows o' inRem)
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at inMade
            exact inMade.elim neM₁ neM₂
        have a₄ := ag₄ o' inC₃ notOrd neMT; rw [l₃, l₂] at a₄
        have a₃ := ag₃ o' inC₂; rw [l₂] at a₃
        have onRow := a₄.trans (a₃.trans (ag₂ o' inC nePr))
        have onR' := row_extends_target rO' monoAll s₄ k₀ onRow
        exact (spineHasPattern_nameLaws hasQ onR').trans (ag₀ q qIn)
      refine ⟨label₄, C₄, d₄, cooled pZero (order.map Prod.snd),
        runH.trans (step_commChild_noRoot committed runCool),
        done₄, rD₄, ?_, packed₄, cov₄, keep₄, clean₄, free₄, monoAll⟩
      rw [orderSnd, predotU_pPar]
      exact bagLaws_cooled_zero _
  | @reflect d P Q R_in pair bs cPre cPost y split groundY inner ih =>
      have ⟨_, hasP₁, hasP₂⟩ := inner.solves
      intro m spM x_l label C pr tk extPats l phase prPres prNeTk readsPr onlyPr cleanBelow
        disj free anchExt
      have spL : IsLocSpine l := .child x_l (predotU P) spM
      let gLoc := childLoc l y (predotU Q)
      have spG : IsLocSpine gLoc := .child y (predotU Q) spL
      obtain ⟨σ_init, known_init⟩ := freeOnPats_consistent free
      obtain ⟨label₂, C₂, rows, runH, lenR, ndR, readsR, factsR, frameH, covH, monoH, extH, _⟩ :=
        heating_noRoot l m (splits_map_predotU split) label C pr tk prPres phase.present prNeTk
          readsPr phase.reads ⟨σ_init, known_init⟩
      have lenMap : rows.length =
          (cPre.map predotU ++ predotU (pReflect y Q) :: cPost.map predotU).length := by
        simpa [List.map_append] using lenR
      obtain ⟨rPre, reflIn, rPost, rowsEq, lPre, lPost⟩ := split_rows_1 lenMap
      have permR : rows.Perm (reflIn :: (rPre ++ rPost)) := by
        rw [rowsEq]; exact List.perm_middle
      obtain ⟨reflOut, ndRest⟩ := List.nodup_cons.mp (permR.nodup_iff.mp ndR)
      have reflInRows : reflIn ∈ rows := permR.symm.subset (List.mem_cons_self ..)
      have reflZip : (reflIn, predotU (pReflect y Q)) ∈
          rows.zip ((cPre ++ pReflect y Q :: cPost).map predotU) := by
        simp only [rowsEq, List.map_append, List.map_cons]
        rw [List.zip_append lPre]; exact List.mem_append_right _ (List.mem_cons_self ..)
      have rRefl₂ : ∀ σ : PSubst, nameAction.Models σ C₂.equations →
          NameLaws (psubst σ (label₂ reflIn)) (psubst σ (atLoc (pReflect y (predotU Q)) l)) := by
        intro σ s; have r := readsR _ reflZip σ s
        rwa [predotU_pReflect, predotU_ground y groundY] at r
      have tokKept₂ := frameH tk phase.present prNeTk.symm
      have phase₂ : PendingPhaseS l m label₂ C₂ tk := by
        refine ⟨tokKept₂.1, fun σ s => by rw [tokKept₂.2]; exact phase.reads σ (monoH σ s), ?_, ?_⟩
        · rintro o oP ⟨σ, s, m', same⟩
          rcases covH o oP with inRows | ⟨inC, _, lblEq⟩
          · obtain ⟨p_o, z_o⟩ := exists_mem_zip lenR inRows
            have both := same.symm.trans (readsR (o, p_o) z_o σ s); rw [psubst_atLoc_any] at both
            exact absurd (nameLaws_heads both) (by decide)
          · rw [lblEq] at same; exact phase.unique o inC ⟨σ, monoH σ s, m', same⟩
        · rintro o oP ⟨σ, s, m', c', same⟩
          rcases covH o oP with inRows | ⟨inC, _, lblEq⟩
          · obtain ⟨p_o, z_o⟩ := exists_mem_zip lenR inRows
            have both := same.symm.trans (readsR (o, p_o) z_o σ s); rw [psubst_atLoc_any] at both
            exact absurd (nameLaws_heads both) (by decide)
          · rw [lblEq] at same; exact phase.noDone o inC ⟨σ, monoH σ s, m', c', same⟩
      have clean₂ : CleanAboveDepth (locDepth l) label₂ C₂ :=
        cleanAboveDepth_of_subset cleanBelow monoH fun o oP => by
          rcases covH o oP with inRows | ⟨inC, -, lblEq⟩
          · obtain ⟨p_o, z_o⟩ := exists_mem_zip lenR inRows
            exact .inr ⟨l, spL, le_rfl, fun σ s => .inl ⟨psubst σ p_o,
              by simpa [psubst_atLoc_any] using readsR (o, p_o) z_o σ s⟩⟩
          · exact .inl ⟨inC, lblEq⟩
      have cleanG : Clean gLoc label₂ C₂ := clean₂ l y (predotU Q) spL le_rfl
      obtain ⟨pr_g, freshPrG⟩ := Infinite.exists_notMem_finset C₂.present
      obtain ⟨tk_g, freshTkG'⟩ := Infinite.exists_notMem_finset (insert pr_g C₂.present)
      have prNeTkG : pr_g ≠ tk_g := fun e => freshTkG' (Finset.mem_insert.mpr (.inl e.symm))
      have freshTkG : tk_g ∉ C₂.present := fun m' => freshTkG' (Finset.mem_insert.mpr (.inr m'))
      obtain ⟨_, s₂_0, -⟩ := extH σ_init known_init
      obtain ⟨ρ_op, freshOp⟩ := openChild_fresh_exists label₂ C₂ reflIn tk pr_g tk_g
      have openedG := openChild_admitted label₂ C₂ y (predotU Q) l m reflIn tk pr_g tk_g
        rRefl₂ phase₂.reads cleanG (factsR reflIn reflInRows).1 phase₂.present prNeTkG
        ⟨freshPrG, freshTkG⟩ s₂_0 freshOp
      let label_g₀ := (res label₂ C₂ (openChildAt ρ_op reflIn tk pr_g tk_g)).label
      let C_g₀ := resConf label₂ C₂ (openChildAt ρ_op reflIn tk pr_g tk_g)
      have phase_g₀ := openChild_enters_pending_S label₂ C₂ y (predotU Q) l m reflIn tk pr_g tk_g
        ρ_op rRefl₂ phase₂.reads cleanG openedG
      have prG_pres : pr_g ∈ C_g₀.present :=
        (openChild_present label₂ C₂ ρ_op reflIn tk pr_g tk_g pr_g).mpr (.inr (.inl rfl))
      have rPrG : ∀ σ : PSubst, nameAction.Models σ C_g₀.equations →
          NameLaws (psubst σ (label_g₀ pr_g)) (psubst σ (atLoc (predotU Q) gLoc)) :=
        fun σ s => (openChild_reads label₂ C₂ y (predotU Q) l m reflIn tk pr_g tk_g ρ_op
          rRefl₂ phase₂.reads prNeTkG (σ := σ) s).2.1
      have onlyPrG : ∀ o ∈ C_g₀.present, o ≠ pr_g → ∀ σ : PSubst,
          nameAction.Models σ C_g₀.equations → ∀ z : Pattern,
            ¬ NameLaws (psubst σ (label_g₀ o)) (atLoc z (psubst σ gLoc)) := by
        intro o oP nePrG σ s z same
        rcases (openChild_present label₂ C₂ ρ_op reflIn tk pr_g tk_g o).mp oP with
          inC₂ | isPrG | isTkG
        · dsimp only [label_g₀] at same
          rw [openChild_label_old label₂ C₂ ρ_op reflIn tk pr_g tk_g
            (fun e => freshPrG (e ▸ inC₂)) (fun e => freshTkG (e ▸ inC₂))] at same
          exact (cleanG o inC₂ σ (info_known _ s)).2.2 z same
        · exact nePrG isPrG
        · subst isTkG
          have both := same.symm.trans (phase_g₀.reads σ s)
          rw [psubst_pendingTok] at both
          exact absurd (nameLaws_heads both) (by decide)
      have cleanBelowG : CleanAboveDepth (locDepth gLoc) label_g₀ C_g₀ :=
        cleanAboveDepth_of_subset (cleanAboveDepth_mono (by simp [gLoc, locDepth_childLoc]) clean₂)
          (fun _ s => info_known _ s) fun o oP => by
            rcases (openChild_present label₂ C₂ ρ_op reflIn tk pr_g tk_g o).mp oP with
              inC₂ | rfl | rfl
            · exact .inl ⟨inC₂, openChild_label_old label₂ C₂ ρ_op reflIn tk pr_g tk_g
                (fun e => freshPrG (e ▸ inC₂)) (fun e => freshTkG (e ▸ inC₂))⟩
            · exact .inr ⟨gLoc, spG, le_rfl, fun σ s => .inl ⟨_,
                by simpa [psubst_atLoc_any] using rPrG σ s⟩⟩
            · exact .inr ⟨gLoc, spG, le_rfl, fun σ s => .inr (.inl ⟨_,
                by simpa [psubst_pendingTok] using phase_g₀.reads σ s⟩)⟩
      have free_g₀ : FreeOnPats (pair.1 :: pair.2 :: extPats) C_g₀.equations := by
        intro τ₀
        obtain ⟨σ₀, k₀, ag₀⟩ := free τ₀
        obtain ⟨w₂, s₂, ag₂⟩ := extH σ₀ k₀
        obtain ⟨w_g, s_g, ag_g⟩ := openChild_extends label₂ C₂ y (predotU Q) l m reflIn tk
          pr_g tk_g rRefl₂ phase₂.reads (factsR reflIn reflInRows).1 phase₂.present freshOp s₂
        have onRefl := ag_g reflIn (factsR reflIn reflInRows).1
        have onQ : NameLaws (psubst w_g (predotU Q)) (psubst σ₀ (predotU Q)) := by
          have onY_Q := row_extends_target rRefl₂ (fun _ s => info_known _ s) s_g s₂ onRefl
          rw [psubst_pReflect, psubst_pReflect] at onY_Q
          have step₁ := (nameLaws_pReflect_iff.mp onY_Q).2
          have onP₂ := pending_anchor_P phase.reads monoH s₂ k₀ (ag₂ tk phase.present prNeTk.symm)
          have memSp : ∀ {X : Pattern} {L : List Pattern}, Splits X L →
              ∀ p ∈ L, NameLaws (psubst w₂ (predotU X)) (psubst σ₀ (predotU X)) →
                NameLaws (psubst w₂ (predotU p)) (psubst σ₀ (predotU p)) := by
            intro X L s; induction s with
            | leaf X => intro p m' h; obtain rfl := List.mem_singleton.mp m'; exact h
            | split _ _ iA iB =>
                intro p m' h; rw [predotU_par, psubst_par, psubst_par] at h
                obtain ⟨hL, hR⟩ := ReflNames.nameLaws_pair_iff.mp h
                exact (List.mem_append.mp m').elim (fun mA => iA p mA hL) (fun mB => iB p mB hR)
          have onReflP := memSp split (pReflect y Q) (by simp) onP₂
          rw [predotU_pReflect, psubst_pReflect, psubst_pReflect] at onReflP
          exact step₁.trans (nameLaws_pReflect_iff.mp onReflP).2
        refine ⟨w_g, s_g, fun q qM => ?_⟩
        simp only [List.mem_cons] at qM
        rcases qM with rfl | rfl | inExt
        · exact (spineHasPattern_nameLaws hasP₁ onQ).trans (ag₀ _ (by simp))
        · exact (spineHasPattern_nameLaws hasP₂ onQ).trans (ag₀ _ (by simp))
        · obtain ⟨o', inC, nePr, -, R', l', rO', hasQ⟩ := anchExt q inExt
          obtain ⟨inC₂, l₂⟩ := frameH o' inC nePr
          have a_g := ag_g o' inC₂; rw [l₂] at a_g
          have onRow := a_g.trans (ag₂ o' inC nePr)
          have onR' := row_extends_target rO' (fun σ s => monoH σ (info_known _ s)) s_g k₀ onRow
          exact (spineHasPattern_nameLaws hasQ onR').trans (ag₀ q (by simp [inExt]))
      have anchExt_g₀ : ∀ q ∈ extPats, ∃ o' ∈ C_g₀.present, o' ≠ pr_g ∧ o' ≠ tk_g ∧
          ∃ R' l' : Pattern,
            (∀ σ : PSubst, nameAction.Models σ C_g₀.equations →
              NameLaws (psubst σ (label_g₀ o')) (psubst σ (atLoc R' l'))) ∧
            SpineHasPattern q R' := by
        intro q qIn
        obtain ⟨o', inC, nePr, -, R', l', rO', hasQ⟩ := anchExt q qIn
        obtain ⟨inC₂, l₂⟩ := frameH o' inC nePr
        have nePG : o' ≠ pr_g := fun e => freshPrG (e ▸ inC₂)
        have neTG : o' ≠ tk_g := fun e => freshTkG (e ▸ inC₂)
        refine ⟨o', (openChild_present label₂ C₂ ρ_op reflIn tk pr_g tk_g o').mpr (.inl inC₂),
          nePG, neTG, R', l', fun σ s => ?_, hasQ⟩
        dsimp only [label_g₀]
        rw [openChild_label_old label₂ C₂ ρ_op reflIn tk pr_g tk_g nePG neTG, l₂]
        exact rO' σ (monoH σ (info_known _ s))
      obtain ⟨label_g₄, C_g₄, d_g, acc_g, runG, doneG, rDG, bagAccG, packedG, covG, keepG,
        _, free_g₄, monoG⟩ :=
        ih spL y label_g₀ C_g₀ pr_g tk_g extPats phase_g₀ prG_pres prNeTkG rPrG onlyPrG
          cleanBelowG disj free_g₀ anchExt_g₀
      have covG_C₂ : ∀ o ∈ C_g₄.present, o = d_g ∨ (o ∈ C₂.present ∧ label_g₄ o = label₂ o) := by
        intro o oP; rcases covG o oP with isDG | ⟨inG₀, nePG, neTG, lG⟩
        · exact .inl isDG
        · rcases (openChild_present label₂ C₂ ρ_op reflIn tk pr_g tk_g o).mp inG₀ with
            inC₂ | isPG | isTG
          · exact .inr ⟨inC₂, lG.trans
              (openChild_label_old label₂ C₂ ρ_op reflIn tk pr_g tk_g nePG neTG)⟩
          · exact absurd isPG nePG
          · exact absurd isTG neTG
      have keepG_C₂ : ∀ o ∈ C₂.present, o ∈ C_g₄.present ∧ label_g₄ o = label₂ o := by
        intro o inC₂
        have nePG : o ≠ pr_g := fun e => freshPrG (e ▸ inC₂)
        have neTG : o ≠ tk_g := fun e => freshTkG (e ▸ inC₂)
        obtain ⟨inG₄, lG⟩ := keepG o
          ((openChild_present label₂ C₂ ρ_op reflIn tk pr_g tk_g o).mpr (.inl inC₂)) nePG neTG
        exact ⟨inG₄, lG.trans (openChild_label_old label₂ C₂ ρ_op reflIn tk pr_g tk_g nePG neTG)⟩
      have monoG_C₂ : ∀ σ : PSubst, nameAction.Models σ C_g₄.equations →
          nameAction.Models σ C₂.equations := fun σ s => info_known _ (monoG σ s)
      have phase_l_g₄ : PendingPhaseS l m label_g₄ C_g₄ tk := by
        refine ⟨(keepG_C₂ tk phase₂.present).1,
          fun σ s => by rw [(keepG_C₂ tk phase₂.present).2]; exact phase₂.reads σ (monoG_C₂ σ s),
          ?_, ?_⟩
        · rintro o oP ⟨σ, s, m', same⟩
          rcases covG_C₂ o oP with rfl | ⟨inC₂, lEq⟩
          · have both := same.symm.trans (rDG σ s); rw [psubst_doneTok] at both
            exact absurd (nameLaws_heads both) (by decide)
          · rw [lEq] at same; exact phase₂.unique o inC₂ ⟨σ, monoG_C₂ σ s, m', same⟩
        · rintro o oP ⟨σ, s, m', c', same⟩
          rcases covG_C₂ o oP with rfl | ⟨inC₂, lEq⟩
          · have both := same.symm.trans (rDG σ s); rw [psubst_doneTok] at both
            have eqLoc := (nameLaws_doneTok_iff.mp both).1
            have dEq := locDepth_nameLaws eqLoc
            rw [locDepth_psubst_spine spL, locDepth_psubst_spine spG] at dEq
            simp [gLoc, locDepth_childLoc] at dEq
          · rw [lEq] at same; exact phase₂.noDone o inC₂ ⟨σ, monoG_C₂ σ s, m', c', same⟩
      obtain ⟨σ_g₄, s_g₄⟩ := freeOnPats_consistent free_g₄
      have reflIn_g₄ := keepG_C₂ reflIn (factsR reflIn reflInRows).1
      have rRefl_g₄ : ∀ σ : PSubst, nameAction.Models σ C_g₄.equations →
          NameLaws (psubst σ (label_g₄ reflIn)) (psubst σ (atLoc (pReflect y (predotU Q)) l)) := by
        intro σ s; rw [reflIn_g₄.2]; exact rRefl₂ σ (monoG_C₂ σ s)
      have dG_not_C₂ : d_g ∉ C₂.present := by
        intro inC₂
        have lEq := (keepG_C₂ d_g inC₂).2
        have rD := rDG σ_g₄ s_g₄
        rw [lEq, psubst_doneTok] at rD
        exact (cleanG d_g inC₂ σ_g₄ (monoG_C₂ σ_g₄ s_g₄)).2.1 _ _ rD
      have reflNeDG : reflIn ≠ d_g := fun e => dG_not_C₂ (e ▸ (factsR reflIn reflInRows).1)
      have dGNeTk : d_g ≠ tk := fun e => dG_not_C₂ (e ▸ phase₂.present)
      have distClose : [reflIn, d_g, tk].Nodup :=
        List.nodup_cons.mpr ⟨by simp [reflNeDG, (factsR reflIn reflInRows).2.1],
          List.nodup_cons.mpr ⟨by simp [dGNeTk], List.nodup_singleton _⟩⟩
      obtain ⟨madeL, freshML⟩ := Infinite.exists_notMem_finset C_g₄.present
      obtain ⟨madeTok, freshMT'⟩ := Infinite.exists_notMem_finset (insert madeL C_g₄.present)
      have mLNeMT : madeL ≠ madeTok := fun e => freshMT' (Finset.mem_insert.mpr (.inl e.symm))
      have freshMT : madeTok ∉ C_g₄.present := fun m' => freshMT' (Finset.mem_insert.mpr (.inr m'))
      obtain ⟨ρ_cl, freshCl⟩ := closeChild_fresh_exists label_g₄ C_g₄ reflIn d_g tk madeL madeTok
      obtain ⟨closedInner, _, d_tmp, done₃'⟩ :=
        child_closes_once_S label_g₄ C_g₄ phase_l_g₄ y (predotU Q) acc_g reflIn d_g madeL madeTok
          rRefl_g₄ rDG packedG distClose (by simp [mLNeMT]) ⟨reflIn_g₄.1, doneG.present⟩
          ⟨freshML, freshMT⟩ s_g₄ freshCl
      have closeR : ∀ {σ : PSubst},
          nameAction.Models σ
            (res label_g₄ C_g₄ (closeChildAt ρ_cl reflIn d_g tk madeL madeTok)).knowledge →
          _ := fun {σ} s =>
        closeChild_reads label_g₄ C_g₄ y (predotU Q) acc_g l m reflIn d_g tk madeL madeTok ρ_cl
          rRefl_g₄ rDG phase_l_g₄.reads mLNeMT (σ := σ) s
      obtain ⟨σ₃_0, sol₃_0⟩ := solution_of_admitted closedInner
      have clPres : ∀ o,
          o ∈ (resConf label_g₄ C_g₄ (closeChildAt ρ_cl reflIn d_g tk madeL madeTok)).present ↔
            (o ∈ C_g₄.present ∧ o ≠ reflIn ∧ o ≠ d_g ∧ o ≠ tk) ∨ o = madeL ∨ o = madeTok := by
        intro o; rw [result_present]; simp [closeChildAt]
      have mtEq : madeTok = d_tmp := done₃'.unique madeTok ((clPres madeTok).mpr (.inr (.inr rfl)))
        ⟨σ₃_0, sol₃_0, _, _, by simpa [psubst_doneTok] using (closeR sol₃_0).2.2⟩
      subst mtEq
      let label₃ := (res label_g₄ C_g₄ (closeChildAt ρ_cl reflIn d_g tk madeL madeTok)).label
      let C₃ := resConf label_g₄ C_g₄ (closeChildAt ρ_cl reflIn d_g tk madeL madeTok)
      have clOld : ∀ {o : O}, o ≠ madeL → o ≠ madeTok → label₃ o = label_g₄ o :=
        fun h₁ h₂ => result_label_old _ (by simp [closeChildAt, h₁, h₂])
      let listenerU := predotU (pFor (tProc R_in) y pZero)
      let order : List (O × Pattern) :=
        rPre.zip (cPre.map predotU) ++ (madeL, listenerU) :: rPost.zip (cPost.map predotU)
      have preFst : (rPre.zip (cPre.map predotU)).map Prod.fst = rPre :=
        List.map_fst_zip (by simp [lPre])
      have postFst : (rPost.zip (cPost.map predotU)).map Prod.fst = rPost :=
        List.map_fst_zip (by simp [lPost])
      have orderFst : order.map Prod.fst = rPre ++ madeL :: rPost := by
        simp [order, preFst, postFst]
      have orderSnd : order.map Prod.snd =
          (cPre ++ pFor (tProc R_in) y pZero :: cPost).map predotU := by
        simp [order, listenerU, List.map_snd_zip (by simp [lPre] : (cPre.map predotU).length ≤ rPre.length),
          List.map_snd_zip (by simp [lPost] : (cPost.map predotU).length ≤ rPost.length)]
      have permOrdFst : (rPre ++ madeL :: rPost).Perm (madeL :: (rPre ++ rPost)) := List.perm_middle
      have ndOrder : (order.map Prod.fst).Nodup := by
        rw [orderFst]; refine permOrdFst.nodup_iff.mpr (List.nodup_cons.mpr ⟨fun inRP => ?_, ndRest⟩)
        have inC₂ := (factsR madeL (permR.symm.subset (List.mem_cons_of_mem _ inRP))).1
        exact freshML (keepG_C₂ madeL inC₂).1
      have orderPres : ∀ q ∈ order, q.1 ∈ C₃.present ∧ q.1 ≠ madeTok := by
        intro q qM; simp only [order, List.mem_append, List.mem_cons] at qM
        rcases qM with inPre | rfl | inPost
        · have qInRP : q.1 ∈ rPre ++ rPost := List.mem_append_left _ (preFst ▸ List.mem_map.mpr ⟨q, inPre, rfl⟩)
          have qF := factsR q.1 (permR.symm.subset (List.mem_cons_of_mem _ qInRP))
          have inG₄ := (keepG_C₂ q.1 qF.1).1
          exact ⟨(clPres q.1).mpr (.inl ⟨inG₄, fun e => reflOut (e ▸ qInRP),
            fun e => dG_not_C₂ (e ▸ qF.1), qF.2.1⟩), fun e => freshMT (e ▸ inG₄)⟩
        · exact ⟨(clPres madeL).mpr (.inr (.inl rfl)), mLNeMT⟩
        · have qInRP : q.1 ∈ rPre ++ rPost := List.mem_append_right _ (postFst ▸ List.mem_map.mpr ⟨q, inPost, rfl⟩)
          have qF := factsR q.1 (permR.symm.subset (List.mem_cons_of_mem _ qInRP))
          have inG₄ := (keepG_C₂ q.1 qF.1).1
          exact ⟨(clPres q.1).mpr (.inl ⟨inG₄, fun e => reflOut (e ▸ qInRP),
            fun e => dG_not_C₂ (e ▸ qF.1), qF.2.1⟩), fun e => freshMT (e ▸ inG₄)⟩
      have orderReads : ∀ q ∈ order, ∀ σ : PSubst, nameAction.Models σ C₃.equations →
          NameLaws (psubst σ (label₃ q.1)) (psubst σ (atLoc q.2 l)) := by
        intro q qM σ s; simp only [order, List.mem_append, List.mem_cons] at qM
        rcases qM with inPre | rfl | inPost
        · have qInRP : q.1 ∈ rPre ++ rPost := List.mem_append_left _ (preFst ▸ List.mem_map.mpr ⟨q, inPre, rfl⟩)
          have qPres := (factsR q.1 (permR.symm.subset (List.mem_cons_of_mem _ qInRP))).1
          have inG₄ := keepG_C₂ q.1 qPres
          rw [clOld (fun e => freshML (e ▸ inG₄.1)) (fun e => freshMT (e ▸ inG₄.1)), inG₄.2]
          have qZ : q ∈ rows.zip ((cPre ++ pReflect y Q :: cPost).map predotU) := by
            simp only [rowsEq, List.map_append]; rw [List.zip_append lPre]
            exact List.mem_append_left _ inPre
          exact readsR q qZ σ (monoG_C₂ σ (info_known _ s))
        · have mR := (closeR s).2.1
          have qQuote : NameLaws (atLoc (pFor (tProc acc_g) y pZero) l) (atLoc listenerU l) := by
            dsimp only [listenerU]; rw [predotU_named_listener groundY R_in]
            exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr
              ⟨nameLaws_pFor_iff.mpr ⟨nameLaws_tProc bagAccG, NameLaws.refl _, NameLaws.refl _⟩,
                NameLaws.refl _⟩
          exact mR.trans (nameLaws_psubst σ qQuote)
        · have qInRP : q.1 ∈ rPre ++ rPost := List.mem_append_right _ (postFst ▸ List.mem_map.mpr ⟨q, inPost, rfl⟩)
          have qPres := (factsR q.1 (permR.symm.subset (List.mem_cons_of_mem _ qInRP))).1
          have inG₄ := keepG_C₂ q.1 qPres
          rw [clOld (fun e => freshML (e ▸ inG₄.1)) (fun e => freshMT (e ▸ inG₄.1)), inG₄.2]
          have qZ : q ∈ rows.zip ((cPre ++ pReflect y Q :: cPost).map predotU) := by
            simp only [rowsEq, List.map_append, List.map_cons]
            rw [List.zip_append lPre, List.zip_cons_cons]
            exact List.mem_append_right _ (List.mem_cons_of_mem _ inPost)
          exact readsR q qZ σ (monoG_C₂ σ (info_known _ s))
      obtain ⟨supply, lenSup, ndSup, freshSup⟩ := exists_fresh_list C₃.present order.length
      obtain ⟨label₄, C₄, d₄, runCool, _, pD₄, rD₄, monoCool, extCool, _, covCool, keepCool⟩ :=
        cooling_noRoot_extends l m order supply label₃ C₃ madeTok pZero lenSup ndSup freshSup
          done₃'.present ndOrder orderPres orderReads (fun _ s => (closeR s).2.2) ⟨σ₃_0, sol₃_0⟩
      have cov₄ : ∀ o ∈ C₄.present,
          o = d₄ ∨ (o ∈ C.present ∧ o ≠ pr ∧ o ≠ tk ∧ label₄ o = label o) := by
        intro o oP; rcases covCool o oP with isD | ⟨inC₃, notOrd, neMT, l₄⟩
        · exact .inl isD
        · rcases (clPres o).mp inC₃ with ⟨inG₄, neRefl, neDG, neTk⟩ | isML | isMT
          · rcases covG_C₂ o inG₄ with isDG | ⟨inC₂, lG⟩
            · exact absurd isDG neDG
            · rcases covH o inC₂ with inRows | ⟨inC, nePr, l₂⟩
              · rcases List.mem_cons.mp (permR.subset inRows) with rfl | inRP
                · exact absurd rfl neRefl
                · exact absurd (by rw [orderFst]; exact permOrdFst.symm.subset (List.mem_cons_of_mem _ inRP))
                    notOrd
              · have l₃ := clOld (fun e => freshML (e ▸ inG₄)) (fun e => freshMT (e ▸ inG₄))
                exact .inr ⟨inC, nePr, neTk, l₄.trans (l₃.trans (lG.trans l₂))⟩
          · exact absurd (by rw [orderFst, isML]; simp) notOrd
          · exact absurd isMT neMT
      have keep₄ : ∀ o ∈ C.present, o ≠ pr → o ≠ tk → o ∈ C₄.present ∧ label₄ o = label o := by
        intro o inC nePr neTk
        obtain ⟨inC₂, l₂⟩ := frameH o inC nePr
        have notRows : o ∉ rows := fun inR =>
          (factsR o inR).2.2.elim (fun e => nePr e) (fun nC => nC inC)
        obtain ⟨inG₄, lG⟩ := keepG_C₂ o inC₂
        have neML : o ≠ madeL := fun e => freshML (e ▸ inG₄)
        have neMT : o ≠ madeTok := fun e => freshMT (e ▸ inG₄)
        have inC₃ := (clPres o).mpr (.inl ⟨inG₄, fun e => notRows (e ▸ reflInRows),
          fun e => dG_not_C₂ (e ▸ inC₂), neTk⟩)
        have l₃ := clOld neML neMT
        have notOrd : o ∉ order.map Prod.fst := by
          rw [orderFst]; intro inM
          rcases List.mem_cons.mp (permOrdFst.subset inM) with rfl | inRP
          · exact neML rfl
          · exact notRows (permR.symm.subset (List.mem_cons_of_mem _ inRP))
        obtain ⟨inC₄, l₄⟩ := keepCool o inC₃ notOrd neMT
        exact ⟨inC₄, l₄.trans (l₃.trans (lG.trans l₂))⟩
      have monoAll : ∀ σ : PSubst, nameAction.Models σ C₄.equations →
          nameAction.Models σ C.equations :=
        fun σ s => monoH σ (monoG_C₂ σ (info_known _ (monoCool σ s)))
      have done₄ := donePhaseS_after_cool done₃' pD₄ rD₄ monoCool covCool
      have packed₄ : ∀ o ∈ C₄.present, ∀ σ : PSubst, nameAction.Models σ C₄.equations →
          ∀ z : Pattern, ¬ NameLaws (psubst σ (label₄ o)) (atLoc z (psubst σ l)) := by
        intro o oP σ s z same
        rcases cov₄ o oP with rfl | ⟨inC, nePr, -, lblEq⟩
        · have both := same.symm.trans (rD₄ σ s); rw [psubst_doneTok] at both
          exact absurd (nameLaws_heads both) (by decide)
        · rw [lblEq] at same; exact onlyPr o inC nePr σ (monoAll σ s) z same
      have clean₄ : CleanAboveDepth (locDepth l) label₄ C₄ :=
        cleanAboveDepth_of_subset cleanBelow monoAll fun o oP => by
          rcases cov₄ o oP with rfl | ⟨inC, -, -, lblEq⟩
          · exact .inr ⟨l, spL, le_rfl, fun σ s => .inr (.inr ⟨_, _,
              by simpa [psubst_doneTok] using rD₄ σ s⟩)⟩
          · exact .inl ⟨inC, lblEq⟩
      have free₄ : FreeOnPats extPats C₄.equations := by
        intro τ₀
        obtain ⟨σ_g, s_g, ag_g⟩ := free_g₄ τ₀
        obtain ⟨w₃, s₃, ag₃⟩ := closeChild_extends label_g₄ C_g₄ y (predotU Q) acc_g l m
          reflIn d_g tk madeL madeTok rRefl_g₄ rDG phase_l_g₄.reads reflIn_g₄.1 doneG.present
          phase_l_g₄.present freshCl s_g
        obtain ⟨w₄, s₄, ag₄⟩ := extCool w₃ s₃
        refine ⟨w₄, s₄, fun q qIn => ?_⟩
        obtain ⟨o', inC, nePr, neTk, R', l', rO', hasQ⟩ := anchExt q qIn
        obtain ⟨inC₂, l₂⟩ := frameH o' inC nePr
        have notRows : o' ∉ rows := fun inR =>
          (factsR o' inR).2.2.elim (fun e => nePr e) (fun nC => nC inC)
        obtain ⟨inG₄, lG⟩ := keepG_C₂ o' inC₂
        have neML : o' ≠ madeL := fun e => freshML (e ▸ inG₄)
        have neMT : o' ≠ madeTok := fun e => freshMT (e ▸ inG₄)
        have inC₃ := (clPres o').mpr (.inl ⟨inG₄, fun e => notRows (e ▸ reflInRows),
          fun e => dG_not_C₂ (e ▸ inC₂), neTk⟩)
        have l₃ := clOld neML neMT
        have notOrd : o' ∉ order.map Prod.fst := by
          rw [orderFst]; intro inM
          rcases List.mem_cons.mp (permOrdFst.subset inM) with rfl | inRP
          · exact neML rfl
          · exact notRows (permR.symm.subset (List.mem_cons_of_mem _ inRP))
        have a₄ := ag₄ o' inC₃ notOrd neMT; rw [l₃, lG, l₂] at a₄
        have a₃ := ag₃ o' inG₄; rw [lG, l₂] at a₃
        have rO_g₄ : ∀ σ : PSubst, nameAction.Models σ C_g₄.equations →
            NameLaws (psubst σ (label_g₄ o')) (psubst σ (atLoc R' l')) := by
          intro σ s; rw [lG, l₂]; exact rO' σ (monoH σ (monoG_C₂ σ s))
        have onR' := row_extends_target rO_g₄
          (fun σ s => info_known _ (monoCool σ s)) s₄ s_g
          (by rw [lG, l₂]; exact a₄.trans a₃)
        exact (spineHasPattern_nameLaws hasQ onR').trans (ag_g q qIn)
      refine ⟨label₄, C₄, d₄, cooled pZero (order.map Prod.snd),
        runH.trans (step_openChild_noRoot openedG (runG.trans (step_closeChild_noRoot closedInner runCool))),
        done₄, rD₄, ?_, packed₄, cov₄, keep₄, clean₄, free₄, monoAll⟩
      rw [orderSnd, predotU_pPar]
      exact bagLaws_cooled_zero _

/-- Specializes `child_pack_of_packStep` to **Interface N** (`HostedSubStepN`). -/
theorem child_pack_of_subStep_N [Infinite O] {d : ℕ} {P R : Pattern}
    {pair : Pattern × Pattern} {bs : Bindings} (sub : HostedSubStepN d P R pair bs)
    {m : Pattern} (spM : IsLocSpine m) (x_l : Pattern) (label : O → Pattern)
    (C : Configuration Pattern O) (pr tk : O) (extPats : List Pattern) :
    let l := childLoc m x_l (predotU P)
    PendingPhaseS l m label C tk → pr ∈ C.present → pr ≠ tk →
    (∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label pr)) (psubst σ (atLoc (predotU P) l))) →
    (∀ o ∈ C.present, o ≠ pr → ∀ σ : PSubst, nameAction.Models σ C.equations →
      ∀ y : Pattern, ¬ NameLaws (psubst σ (label o)) (atLoc y (psubst σ l))) →
    CleanAboveDepth (locDepth l) label C →
    (∀ q ∈ extPats, ∀ v ∈ pvars q, v ∉ pvars pair.1 ++ pvars pair.2) →
    FreeOnPats (pair.1 :: pair.2 :: extPats) C.equations →
    (∀ q ∈ extPats, ∃ o' ∈ C.present, o' ≠ pr ∧ o' ≠ tk ∧ ∃ R' l' : Pattern,
      (∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label o')) (psubst σ (atLoc R' l'))) ∧ SpineHasPattern q R') →
    ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (d' : O) (acc : Pattern),
      LocatedRunNoRoot label C label' C' false ∧ DonePhaseS l m label' C' d' ∧
      (∀ σ : PSubst, nameAction.Models σ C'.equations →
        NameLaws (psubst σ (label' d')) (psubst σ (doneTok l m acc))) ∧
      BagLaws acc (predotU R) ∧
      (∀ o ∈ C'.present, ∀ σ : PSubst, nameAction.Models σ C'.equations →
        ∀ y : Pattern, ¬ NameLaws (psubst σ (label' o)) (atLoc y (psubst σ l))) ∧
      (∀ o ∈ C'.present, o = d' ∨ (o ∈ C.present ∧ o ≠ pr ∧ o ≠ tk ∧ label' o = label o)) ∧
      (∀ o ∈ C.present, o ≠ pr → o ≠ tk → o ∈ C'.present ∧ label' o = label o) ∧
      CleanAboveDepth (locDepth l) label' C' ∧ FreeOnPats extPats C'.equations ∧
      (∀ σ : PSubst, nameAction.Models σ C'.equations → nameAction.Models σ C.equations) :=
  child_pack_of_packStep sub.toPackStep spM x_l label C pr tk extPats

/-- Specializes `child_pack_of_packStep` to **Interface C** (`HostedSubStepC`). -/
theorem child_pack_of_subStep_C [Infinite O] {d : ℕ} {P R : Pattern}
    {pair : Pattern × Pattern} {bs : Bindings} (sub : HostedSubStepC d P R pair bs)
    {m : Pattern} (spM : IsLocSpine m) (x_l : Pattern) (label : O → Pattern)
    (C : Configuration Pattern O) (pr tk : O) (extPats : List Pattern) :
    let l := childLoc m x_l (predotU P)
    PendingPhaseS l m label C tk → pr ∈ C.present → pr ≠ tk →
    (∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label pr)) (psubst σ (atLoc (predotU P) l))) →
    (∀ o ∈ C.present, o ≠ pr → ∀ σ : PSubst, nameAction.Models σ C.equations →
      ∀ y : Pattern, ¬ NameLaws (psubst σ (label o)) (atLoc y (psubst σ l))) →
    CleanAboveDepth (locDepth l) label C →
    (∀ q ∈ extPats, ∀ v ∈ pvars q, v ∉ pvars pair.1 ++ pvars pair.2) →
    FreeOnPats (pair.1 :: pair.2 :: extPats) C.equations →
    (∀ q ∈ extPats, ∃ o' ∈ C.present, o' ≠ pr ∧ o' ≠ tk ∧ ∃ R' l' : Pattern,
      (∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label o')) (psubst σ (atLoc R' l'))) ∧ SpineHasPattern q R') →
    ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (d' : O) (acc : Pattern),
      LocatedRunNoRoot label C label' C' false ∧ DonePhaseS l m label' C' d' ∧
      (∀ σ : PSubst, nameAction.Models σ C'.equations →
        NameLaws (psubst σ (label' d')) (psubst σ (doneTok l m acc))) ∧
      BagLaws acc (predotU R) ∧
      (∀ o ∈ C'.present, ∀ σ : PSubst, nameAction.Models σ C'.equations →
        ∀ y : Pattern, ¬ NameLaws (psubst σ (label' o)) (atLoc y (psubst σ l))) ∧
      (∀ o ∈ C'.present, o = d' ∨ (o ∈ C.present ∧ o ≠ pr ∧ o ≠ tk ∧ label' o = label o)) ∧
      (∀ o ∈ C.present, o ≠ pr → o ≠ tk → o ∈ C'.present ∧ label' o = label o) ∧
      CleanAboveDepth (locDepth l) label' C' ∧ FreeOnPats extPats C'.equations ∧
      (∀ σ : PSubst, nameAction.Models σ C'.equations → nameAction.Models σ C.equations) :=
  child_pack_of_packStep sub.toPackStep spM x_l label C pr tk extPats

/-! ## Whole-system recursive `REFL` forward at `Root` under **N** and **C** -/

/-- Open the selected reflection occurrence and execute its child to the
packed phase. Keep the opening separate from the child run: the origin of
this completion is the occurrence selected at that opening. -/
theorem refl_depth_root_ready [Infinite O] {d : ℕ} {P_sub R : Pattern}
    {pair : Pattern × Pattern} {bs : Bindings} (sub : HostedPackStep d P_sub R pair bs)
    {label : O → Pattern} {C : Configuration Pattern O} {pre post : List (O × Pattern)}
    {reflOcc : O} {x : Pattern} {extPats : List Pattern}
    (inv : RootCells label C (pre ++ (reflOcc, pReflect x P_sub) :: post))
    (groundX : pvars x = []) (cleanAll : CleanChildren label C)
    (disj : ∀ q ∈ extPats, ∀ v ∈ pvars q, v ∉ pvars pair.1 ++ pvars pair.2)
    (free : FreeOnPats (pair.1 :: pair.2 :: extPats) C.equations)
    (anchExt : ∀ q ∈ extPats, ∃ c ∈ pre ++ post, SpineHasPattern q (predotU c.2)) :
    let l := childLoc rootLoc x (predotU P_sub)
    ∃ (pr tk : O) (opening : PSubst),
      let birth := openRootAt opening reflOcc pr tk
      (RuleSyntax.step QN O QNE located).Admits (s := embed label C) birth ∧
      ∃ (label₄ : O → Pattern) (C₄ : Configuration Pattern O) (d₄ : O) (acc : Pattern),
        LocatedRunNoRoot (res label C birth).label (resConf label C birth) label₄ C₄ false ∧
        DonePhaseS l rootLoc label₄ C₄ d₄ ∧
        (∀ σ : PSubst, nameAction.Models σ C₄.equations →
          NameLaws (psubst σ (label₄ d₄)) (psubst σ (doneTok l rootLoc acc))) ∧
        BagLaws acc (predotU R) ∧
        (∀ o ∈ C₄.present, ∀ σ : PSubst, nameAction.Models σ C₄.equations →
          ∀ y : Pattern, ¬ NameLaws (psubst σ (label₄ o)) (atLoc y (psubst σ l))) ∧
        (∀ o ∈ C₄.present, o = d₄ ∨ (o ∈ C.present ∧ label₄ o = label o)) ∧
        (∀ o ∈ C.present, o ∈ C₄.present ∧ label₄ o = label o) ∧
        (∀ σ : PSubst, nameAction.Models σ C₄.equations → nameAction.Models σ C.equations) ∧
        FreeOnPats extPats C₄.equations := by
  have ⟨_, hasP₁, hasP₂⟩ := sub.solves
  have reflPres := (inv.rows (reflOcc, pReflect x P_sub) (by simp)).1
  have rRefl : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflOcc))
        (psubst σ (atLoc (pReflect x (predotU P_sub)) rootLoc)) := by
    intro σ s; have r := (inv.rows (reflOcc, pReflect x P_sub) (by simp)).2 σ s
    rwa [predotU_pReflect, predotU_ground x groundX] at r
  let l := childLoc rootLoc x (predotU P_sub)
  have spL : IsLocSpine l := .child x (predotU P_sub) .root
  have cleanL : Clean l label C := cleanAll rootLoc x (predotU P_sub) .root (Nat.zero_le _)
  obtain ⟨σ₀, k₀⟩ := freeOnPats_consistent free
  obtain ⟨pr, freshPr⟩ := Infinite.exists_notMem_finset C.present
  obtain ⟨tk, freshTk'⟩ := Infinite.exists_notMem_finset (insert pr C.present)
  have prNeTk : pr ≠ tk := fun e => freshTk' (Finset.mem_insert.mpr (.inl e.symm))
  have freshTk : tk ∉ C.present := fun m' => freshTk' (Finset.mem_insert.mpr (.inr m'))
  obtain ⟨ρ₁, fresh₁⟩ := open_fresh_exists label C reflOcc pr tk
  have opened := openRoot_admitted label C x (predotU P_sub) reflOcc pr tk rRefl cleanL reflPres
    prNeTk ⟨freshPr, freshTk⟩ k₀ fresh₁
  let label₁ := (res label C (openRootAt ρ₁ reflOcc pr tk)).label
  let C₁ := resConf label C (openRootAt ρ₁ reflOcc pr tk)
  have phase₁ := openRoot_enters_pending_S label C x (predotU P_sub) reflOcc pr tk ρ₁ rRefl
    cleanL opened
  have prPres₁ : pr ∈ C₁.present :=
    (open_present label C ρ₁ reflOcc pr tk pr).mpr (.inr (.inl rfl))
  have rPr₁ : ∀ σ : PSubst, nameAction.Models σ C₁.equations →
      NameLaws (psubst σ (label₁ pr)) (psubst σ (atLoc (predotU P_sub) l)) :=
    fun σ s => (openRoot_reads label C x (predotU P_sub) reflOcc pr tk ρ₁ rRefl prNeTk (σ := σ) s).2.1
  have onlyPr₁ : ∀ o ∈ C₁.present, o ≠ pr → ∀ σ : PSubst, nameAction.Models σ C₁.equations →
      ∀ y : Pattern, ¬ NameLaws (psubst σ (label₁ o)) (atLoc y (psubst σ l)) := by
    intro o oP nePr σ s y same
    rcases (open_present label C ρ₁ reflOcc pr tk o).mp oP with inC | isPr | isTk
    · dsimp only [label₁] at same
      rw [open_label_old label C ρ₁ reflOcc pr tk (fun e => freshPr (e ▸ inC))
        (fun e => freshTk (e ▸ inC))] at same
      exact (cleanL o inC σ (info_known _ s)).2.2 y same
    · exact nePr isPr
    · subst isTk; have both := same.symm.trans (phase₁.reads σ s)
      rw [psubst_pendingTok] at both; exact absurd (nameLaws_heads both) (by decide)
  have cleanBelow₁ : CleanAboveDepth (locDepth l) label₁ C₁ :=
    cleanAboveDepth_of_subset (cleanAboveDepth_mono (Nat.zero_le _) cleanAll)
      (fun _ s => info_known _ s) fun o oP => by
        rcases (open_present label C ρ₁ reflOcc pr tk o).mp oP with inC | rfl | rfl
        · exact .inl ⟨inC, open_label_old label C ρ₁ reflOcc pr tk (fun e => freshPr (e ▸ inC))
            (fun e => freshTk (e ▸ inC))⟩
        · exact .inr ⟨l, spL, le_rfl, fun σ s => .inl ⟨_, by simpa [psubst_atLoc_any] using rPr₁ σ s⟩⟩
        · exact .inr ⟨l, spL, le_rfl, fun σ s => .inr (.inl ⟨_,
            by simpa [psubst_pendingTok] using phase₁.reads σ s⟩)⟩
  have restInOld : ∀ c ∈ pre ++ post, c ∈ pre ++ (reflOcc, pReflect x P_sub) :: post := fun c m' =>
    (List.mem_append.mp m').elim (List.mem_append_left _)
      (fun r => List.mem_append_right _ (List.mem_cons_of_mem _ r))
  have free₁ : FreeOnPats (pair.1 :: pair.2 :: extPats) C₁.equations :=
    freeOnPats_of_extends free (fun _ s => info_known _ s)
      (fun _ k => openRoot_extends label C x (predotU P_sub) reflOcc pr tk rRefl reflPres fresh₁ k)
      (fun q qM => by
        simp only [List.mem_cons] at qM
        rcases qM with rfl | rfl | inExt
        · exact ⟨reflOcc, reflPres, pReflect x (predotU P_sub), rootLoc, rRefl, .reflect x hasP₁⟩
        · exact ⟨reflOcc, reflPres, pReflect x (predotU P_sub), rootLoc, rRefl, .reflect x hasP₂⟩
        · obtain ⟨c, cIn, hasQ⟩ := anchExt q inExt
          exact ⟨c.1, (inv.rows c (restInOld c cIn)).1, predotU c.2, rootLoc,
            (inv.rows c (restInOld c cIn)).2, hasQ⟩)
  have anchExt₁ : ∀ q ∈ extPats, ∃ o' ∈ C₁.present, o' ≠ pr ∧ o' ≠ tk ∧ ∃ R' l' : Pattern,
      (∀ σ : PSubst, nameAction.Models σ C₁.equations →
        NameLaws (psubst σ (label₁ o')) (psubst σ (atLoc R' l'))) ∧ SpineHasPattern q R' := by
    intro q qIn
    obtain ⟨c, cIn, hasQ⟩ := anchExt q qIn
    have cPres := (inv.rows c (restInOld c cIn)).1
    have nePr : c.1 ≠ pr := fun e => freshPr (e ▸ cPres)
    have neTk : c.1 ≠ tk := fun e => freshTk (e ▸ cPres)
    refine ⟨c.1, (open_present label C ρ₁ reflOcc pr tk c.1).mpr (.inl cPres), nePr, neTk,
      predotU c.2, rootLoc, fun σ s => ?_, hasQ⟩
    dsimp only [label₁]
    rw [open_label_old label C ρ₁ reflOcc pr tk nePr neTk]
    exact (inv.rows c (restInOld c cIn)).2 σ (info_known _ s)
  obtain ⟨label₄, C₄, d₄, acc, runPack, done₄, rD₄, bagAcc, packed₄, cov₄, keep₄, _, free₄,
    mono₄⟩ := child_pack_of_packStep sub .root x label₁ C₁ pr tk extPats phase₁ prPres₁ prNeTk
      rPr₁ onlyPr₁ cleanBelow₁ disj free₁ anchExt₁
  have cov₄_C : ∀ o ∈ C₄.present, o = d₄ ∨ (o ∈ C.present ∧ label₄ o = label o) := by
    intro o oP; rcases cov₄ o oP with isD | ⟨inC₁, nePr, neTk, l₄⟩
    · exact .inl isD
    · rcases (open_present label C ρ₁ reflOcc pr tk o).mp inC₁ with inC | isPr | isTk
      · exact .inr ⟨inC, l₄.trans (open_label_old label C ρ₁ reflOcc pr tk nePr neTk)⟩
      · exact absurd isPr nePr
      · exact absurd isTk neTk
  have keep₄_C : ∀ o ∈ C.present, o ∈ C₄.present ∧ label₄ o = label o := by
    intro o inC
    have nePr : o ≠ pr := fun e => freshPr (e ▸ inC)
    have neTk : o ≠ tk := fun e => freshTk (e ▸ inC)
    obtain ⟨inC₄, l₄⟩ := keep₄ o ((open_present label C ρ₁ reflOcc pr tk o).mpr (.inl inC))
      nePr neTk
    exact ⟨inC₄, l₄.trans (open_label_old label C ρ₁ reflOcc pr tk nePr neTk)⟩
  have mono₄_C : ∀ σ : PSubst, nameAction.Models σ C₄.equations →
      nameAction.Models σ C.equations := fun σ s => info_known _ (mono₄ σ s)
  exact ⟨pr, tk, ρ₁, opened, label₄, C₄, d₄, acc, runPack, done₄, rD₄, bagAcc, packed₄,
    cov₄_C, keep₄_C, mono₄_C, free₄⟩

/-- Execute the selected root reflection: open, pack the child, then close
back into the opening occurrence. The prefix is `refl_depth_root_ready`. -/
theorem refl_depth_root_pack [Infinite O] {d : ℕ} {P_sub R : Pattern}
    {pair : Pattern × Pattern} {bs : Bindings} (sub : HostedPackStep d P_sub R pair bs)
    {label : O → Pattern} {C : Configuration Pattern O} {pre post : List (O × Pattern)}
    {reflOcc : O} {x : Pattern} {extPats : List Pattern}
    (_noTok : NoRootTokens label C)
    (inv : RootCells label C (pre ++ (reflOcc, pReflect x P_sub) :: post))
    (groundX : pvars x = []) (cleanAll : CleanChildren label C)
    (disj : ∀ q ∈ extPats, ∀ v ∈ pvars q, v ∉ pvars pair.1 ++ pvars pair.2)
    (free : FreeOnPats (pair.1 :: pair.2 :: extPats) C.equations)
    (anchExt : ∀ q ∈ extPats, ∃ c ∈ pre ++ post, SpineHasPattern q (predotU c.2)) :
    ∃ (label₄ : O → Pattern) (C₄ : Configuration Pattern O) (d₄ made : O) (ρ₅ : PSubst),
      LocatedRunNoRoot label C label₄ C₄ ∧
      (∃ σ₀ : PSubst, nameAction.Models σ₀ C₄.equations ∧
        ∃ l' m' c', NameLaws (psubst σ₀ (label₄ d₄)) (doneTok l' m' c')) ∧
      (RuleSyntax.step QN O QNE located).Admits (s := embed label₄ C₄)
        (closeRootAt ρ₅ reflOcc d₄ made) ∧
      (∀ σ : PSubst,
        nameAction.Models σ (res label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)).knowledge →
          NameLaws (psubst σ ((res label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)).label made))
            (psubst σ (atLoc (pFor (tProc (predotU R)) x pZero) rootLoc))) ∧
      CleanChildren (res label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)).label
        (resConf label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)) ∧
      FreeOnPats extPats (resConf label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)).equations := by
  obtain ⟨pr, tk, opening, opened, label₄, C₄, d₄, acc, runPack, done₄, rD₄, bagAcc, packed₄,
    cov₄_C, keep₄_C, mono₄_C, free₄⟩ :=
    refl_depth_root_ready sub inv groundX cleanAll disj free anchExt
  let l := childLoc rootLoc x (predotU P_sub)
  have cleanL : Clean l label C := cleanAll rootLoc x (predotU P_sub) .root (Nat.zero_le _)
  have reflPres := (inv.rows (reflOcc, pReflect x P_sub) (by simp)).1
  have rRefl : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflOcc)) (psubst σ (atLoc (pReflect x (predotU P_sub)) rootLoc)) := by
    intro σ s; have r := (inv.rows (reflOcc, pReflect x P_sub) (by simp)).2 σ s
    rwa [predotU_pReflect, predotU_ground x groundX] at r
  have restInOld : ∀ c ∈ pre ++ post, c ∈ pre ++ (reflOcc, pReflect x P_sub) :: post := fun c m' =>
    (List.mem_append.mp m').elim (List.mem_append_left _)
      (fun r => List.mem_append_right _ (List.mem_cons_of_mem _ r))
  have segRun : LocatedRunNoRoot label C label₄ C₄ := step_openRoot_noRoot opened runPack
  obtain ⟨σ₄, s₄⟩ := freeOnPats_consistent free₄
  have d₄NotC : d₄ ∉ C.present := by
    intro inC; have rD := rD₄ σ₄ s₄
    rw [(keep₄_C d₄ inC).2, psubst_doneTok] at rD
    exact (cleanL d₄ inC σ₄ (mono₄_C σ₄ s₄)).2.1 _ _ rD
  have reflIn₄ := keep₄_C reflOcc reflPres
  have rRefl₄ : ∀ σ : PSubst, nameAction.Models σ C₄.equations →
      NameLaws (psubst σ (label₄ reflOcc)) (psubst σ (atLoc (pReflect x (predotU P_sub)) rootLoc)) :=
    fun σ s => by rw [reflIn₄.2]; exact rRefl σ (mono₄_C σ s)
  obtain ⟨made, freshM⟩ := Infinite.exists_notMem_finset C₄.present
  obtain ⟨ρ₅, fresh₅⟩ := close_fresh_exists label₄ C₄ reflOcc d₄ made
  have closed := closeRoot_admitted label₄ C₄ x (predotU P_sub) acc reflOcc d₄ made rRefl₄ rD₄
    packed₄ (fun e => d₄NotC (e ▸ reflPres)) ⟨reflIn₄.1, done₄.present⟩ freshM s₄ fresh₅
  have madeQuote : ∀ σ : PSubst,
      nameAction.Models σ (res label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)).knowledge →
        NameLaws (psubst σ ((res label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)).label made))
          (psubst σ (atLoc (pFor (tProc (predotU R)) x pZero) rootLoc)) := by
    intro σ s
    obtain ⟨_, mR⟩ := closeRoot_reads label₄ C₄ x (predotU P_sub) acc reflOcc d₄ made ρ₅ rRefl₄
      rD₄ (σ := σ) s
    exact mR.trans (nameLaws_psubst σ ((locatedFrame_name.atLoc_iff _ _ _ _).mpr
      ⟨nameLaws_pFor_iff.mpr ⟨nameLaws_tProc bagAcc, NameLaws.refl _, NameLaws.refl _⟩,
        NameLaws.refl _⟩))
  have clean₅ : CleanChildren (res label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)).label
      (resConf label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)) :=
    cleanAboveDepth_of_subset cleanAll (fun σ s => mono₄_C σ (info_known _ s)) fun o oP => by
      rcases (close_present label₄ C₄ ρ₅ reflOcc d₄ made o).mp oP with ⟨inC₄, -, neD₄⟩ | rfl
      · rcases cov₄_C o inC₄ with isD | ⟨inC, l₄⟩
        · exact absurd isD neD₄
        · have neM : o ≠ made := fun e => freshM (e ▸ inC₄)
          exact .inl ⟨inC, (result_label_old _ (by simp [closeRootAt, neM])).trans l₄⟩
      · exact .inr ⟨rootLoc, .root, le_rfl, fun σ s => .inl ⟨_,
          by simpa [psubst_atLoc_any, psubst_rootLoc] using madeQuote σ s⟩⟩
  have free₅ : FreeOnPats extPats
      (resConf label₄ C₄ (closeRootAt ρ₅ reflOcc d₄ made)).equations :=
    freeOnPats_of_extends free₄ (fun _ s => info_known _ s)
      (fun _ k => closeRoot_extends label₄ C₄ x (predotU P_sub) acc reflOcc d₄ made rRefl₄ rD₄
        reflIn₄.1 done₄.present fresh₅ k)
      (fun q qIn => by
        obtain ⟨c, cIn, hasQ⟩ := anchExt q qIn
        have cPres := (inv.rows c (restInOld c cIn)).1
        obtain ⟨inC₄, l₄⟩ := keep₄_C c.1 cPres
        refine ⟨c.1, inC₄, predotU c.2, rootLoc, fun σ s => ?_, hasQ⟩
        rw [l₄]; exact (inv.rows c (restInOld c cIn)).2 σ (mono₄_C σ s))
  exact ⟨label₄, C₄, d₄, made, ρ₅, segRun,
    ⟨σ₄, s₄, _, _, _, by simpa [psubst_doneTok] using rD₄ σ₄ s₄⟩,
    closed, madeQuote, clean₅, free₅⟩

/-- **Whole-system recursive `REFL` forward — Interface N (`BagStep` & `ReflClosureDepth`)**. -/
theorem refl_depth_root_forward_N [Infinite O] {d : ℕ} {P_sub R : Pattern}
    {pair : Pattern × Pattern} {bs : Bindings} (sub : HostedSubStepN d P_sub R pair bs)
    {label : O → Pattern} {C : Configuration Pattern O} {pre post : List (O × Pattern)}
    {reflOcc : O} {x : Pattern} {extPats : List Pattern}
    (noTok : NoRootTokens label C)
    (inv : RootCells label C (pre ++ (reflOcc, pReflect x P_sub) :: post))
    (groundX : pvars x = []) (cleanAll : CleanChildren label C)
    (disj : ∀ q ∈ extPats, ∀ v ∈ pvars q, v ∉ pvars pair.1 ++ pvars pair.2)
    (free : FreeOnPats (pair.1 :: pair.2 :: extPats) C.equations)
    (anchExt : ∀ q ∈ extPats, ∃ c ∈ pre ++ post, SpineHasPattern q (predotU c.2)) :
    ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (made : O),
      LocatedRun label C label' C' ∧
      NoRootTokens label' C' ∧
      RootCells label' C' (pre ++ (made, pFor (tProc R) x pZero) :: post) ∧
      CleanChildren label' C' ∧
      FreeOnPats extPats C'.equations ∧
      ReflClosureDepth (d + 1) (pReflect x P_sub) (pFor (tProc R) x pZero) ∧
      BagStep conventional (rootBagProcess (pre ++ (reflOcc, pReflect x P_sub) :: post))
        (rootBagProcess (pre ++ (made, pFor (tProc R) x pZero) :: post)) := by
  obtain ⟨label₄, C₄, d₄, made, ρ₅, segRun, dReads, closed, madeQuote, clean₅, free₅⟩ :=
    refl_depth_root_pack sub.toPackStep noTok inv groundX cleanAll disj free anchExt
  obtain ⟨runFull, noTok₅, inv₅, stepRoot⟩ :=
    rootCells_closeRoot_N noTok inv groundX segRun dReads closed madeQuote sub.toBagStep
  exact ⟨_, _, made, runFull, noTok₅, inv₅, clean₅, free₅,
    .reflect x sub.toReflClosureDepth, stepRoot⟩

/-- **Whole-system recursive `REFL` forward — Interface C (`CanonicalBagStep`, `pvars R = []`)**. -/
theorem refl_depth_root_forward_C [Infinite O] {d : ℕ} {P_sub R : Pattern}
    {pair : Pattern × Pattern} {bs : Bindings} (sub : HostedSubStepC d P_sub R pair bs)
    {label : O → Pattern} {C : Configuration Pattern O} {pre post : List (O × Pattern)}
    {reflOcc : O} {x : Pattern} {extPats : List Pattern}
    (noTok : NoRootTokens label C)
    (inv : RootCells label C (pre ++ (reflOcc, pReflect x P_sub) :: post))
    (groundX : pvars x = []) (cleanAll : CleanChildren label C)
    (disj : ∀ q ∈ extPats, ∀ v ∈ pvars q, v ∉ pvars pair.1 ++ pvars pair.2)
    (free : FreeOnPats (pair.1 :: pair.2 :: extPats) C.equations)
    (anchExt : ∀ q ∈ extPats, ∃ c ∈ pre ++ post, SpineHasPattern q (predotU c.2)) :
    ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (made : O),
      LocatedRun label C label' C' ∧
      NoRootTokens label' C' ∧
      RootCells label' C' (pre ++ (made, listener x R) :: post) ∧
      CleanChildren label' C' ∧
      FreeOnPats extPats C'.equations ∧
      CanonicalBagStep conventional (rootBagProcess (pre ++ (reflOcc, pReflect x P_sub) :: post))
        (rootBagProcess (pre ++ (made, listener x R) :: post)) := by
  obtain ⟨label₄, C₄, d₄, made, ρ₅, segRun, dReads, closed, madeQuote, clean₅, free₅⟩ :=
    refl_depth_root_pack sub.toPackStep noTok inv groundX cleanAll disj free anchExt
  obtain ⟨runFull, noTok₅, inv₅, stepRoot⟩ :=
    rootCells_closeRoot_C noTok inv groundX sub.groundReduct segRun dReads closed madeQuote
      sub.toCanonicalBagStep
  exact ⟨_, _, made, runFull, noTok₅, inv₅, clean₅, free₅, stepRoot⟩

end ForwardRecursion

/-! ## Concrete nested-reflection showcases -/

/-- **Nested reflection showcase — Interface N** on `@0?(@0?(for((0) <- @0)0 | for(y <- @0)y))`. -/
theorem nested_canary_hosted_N :
    let R₀ := pPar [applyDot nestedCanaryUnifier pZero, applyDot nestedCanaryUnifier nestedVarY]
    let R₁ := pPar [pFor (tProc R₀) demoChan pZero]
    let target := pFor (tProc R₁) demoChan pZero
    ∃ (label' : ℕ → Pattern) (C' : Configuration Pattern ℕ) (made : ℕ),
      LocatedRun (encodeLabel nestedCanarySource) encodeConf label' C' ∧
      NoRootTokens label' C' ∧
      RootCells label' C' [(made, target)] ∧
      CleanChildren label' C' ∧
      ReflClosureDepth 2 nestedCanarySource target ∧
      MeTTaCalculus.ReflectionClosure.Step GroundPrincipal BagLaws nestedCanarySource target ∧
      BagStep conventional (rootBagProcess [(0, nestedCanarySource)])
        (rootBagProcess [(made, target)]) := by
  have split₀ : Splits nestedCanaryInner
      ([] ++ pFor nestedZeroTerm demoChan pZero :: ([] ++ pFor nestedVarY demoChan nestedVarY :: [])) :=
    show Splits (par _ _) ([_] ++ [_]) from
      .split (.leaf (pFor nestedZeroTerm demoChan pZero)) (.leaf (pFor nestedVarY demoChan nestedVarY))
  have plainA : PlainPatterns (applyDot nestedCanaryUnifier pZero) := by
    simp [PlainPatterns, PlainPatternsList, applyDot, pZero, Mettapedia.OSLF.MeTTaIL.Match.applyBindings]
  have plainB : PlainPatterns (applyDot nestedCanaryUnifier nestedVarY) := by
    simp [PlainPatterns, PlainPatternsList, applyDot, nestedCanaryUnifier, nestedVarY, nestedZeroTerm,
      tProc, pZero, nQuote, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
      Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.dotBindings]
  have sub₀ : HostedSubStepN 0 nestedCanaryInner
      (pPar [applyDot nestedCanaryUnifier pZero, applyDot nestedCanaryUnifier nestedVarY])
      (nestedZeroTerm, nestedVarY) nestedCanaryUnifier :=
    .comm [] [] [] nestedZeroTerm nestedVarY demoChan pZero nestedVarY nestedCanaryUnifier
      split₀ (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) plainA plainB nestedCanaryUnifier_gp
      ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have sub₁ : HostedSubStepN 1 (pReflect demoChan nestedCanaryInner) _ _ _ :=
    .reflect [] [] demoChan (.leaf _) (by decide +kernel) sub₀
  obtain ⟨noTok, inv, clean, free⟩ :=
    single_root_init nestedCanarySource [nestedZeroTerm, nestedVarY]
  obtain ⟨label', C', made, run, noTok', inv', clean', -, depth₂, stepN⟩ :=
    refl_depth_root_forward_N sub₁ (pre := []) (post := []) noTok inv (by decide +kernel) clean
      (fun _ m => absurd m List.not_mem_nil) free (fun _ m => absurd m List.not_mem_nil)
  exact ⟨label', C', made, run, noTok', inv', clean', depth₂, depth₂.toReflectionClosure, stepN⟩

/-- **Nested reflection showcase — Interface C** on `@0?(@0?(for((0) <- @0)0 | for(y <- @0)y))`. -/
theorem nested_canary_hosted_C :
    let R₀ := pPar [applyDot nestedCanaryUnifier pZero, applyDot nestedCanaryUnifier nestedVarY]
    let R₁ := pPar [listener demoChan R₀]
    let target := listener demoChan R₁
    ∃ (label' : ℕ → Pattern) (C' : Configuration Pattern ℕ) (made : ℕ),
      LocatedRun (encodeLabel nestedCanarySource) encodeConf label' C' ∧
      NoRootTokens label' C' ∧
      RootCells label' C' [(made, target)] ∧
      CleanChildren label' C' ∧
      CanonicalBagStep conventional (rootBagProcess [(0, nestedCanarySource)])
        (rootBagProcess [(made, target)]) := by
  have split₀ : Splits nestedCanaryInner
      ([] ++ pFor nestedZeroTerm demoChan pZero :: ([] ++ pFor nestedVarY demoChan nestedVarY :: [])) :=
    show Splits (par _ _) ([_] ++ [_]) from
      .split (.leaf (pFor nestedZeroTerm demoChan pZero)) (.leaf (pFor nestedVarY demoChan nestedVarY))
  have plainA : PlainPatterns (applyDot nestedCanaryUnifier pZero) := by
    simp [PlainPatterns, PlainPatternsList, applyDot, pZero, Mettapedia.OSLF.MeTTaIL.Match.applyBindings]
  have plainB : PlainPatterns (applyDot nestedCanaryUnifier nestedVarY) := by
    simp [PlainPatterns, PlainPatternsList, applyDot, nestedCanaryUnifier, nestedVarY, nestedZeroTerm,
      tProc, pZero, nQuote, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
      Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.dotBindings]
  have sub₀ : HostedSubStepC 0 nestedCanaryInner
      (pPar [applyDot nestedCanaryUnifier pZero, applyDot nestedCanaryUnifier nestedVarY])
      (nestedZeroTerm, nestedVarY) nestedCanaryUnifier :=
    .comm [] [] [] nestedZeroTerm nestedVarY demoChan pZero nestedVarY nestedCanaryUnifier
      split₀ (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) plainA plainB nestedCanaryUnifier_gp
      ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (fun _ m => absurd m List.not_mem_nil)
      (by decide +kernel) (by decide +kernel)
  have sub₁ : HostedSubStepC 1 (pReflect demoChan nestedCanaryInner) _ _ _ :=
    .reflect [] [] demoChan (.leaf _) (by decide +kernel) (fun _ m => absurd m List.not_mem_nil)
      sub₀
  obtain ⟨noTok, inv, clean, free⟩ :=
    single_root_init nestedCanarySource [nestedZeroTerm, nestedVarY]
  obtain ⟨label', C', made, run, noTok', inv', clean', -, stepC⟩ :=
    refl_depth_root_forward_C sub₁ (pre := []) (post := []) noTok inv (by decide +kernel) clean
      (fun _ m => absurd m List.not_mem_nil) free (fun _ m => absurd m List.not_mem_nil)
  exact ⟨label', C', made, run, noTok', inv', clean', stepC⟩

/-- **Nested reflection with an open reduct — Interface N**: hosts
`@0?(@0?(for(a1 <- @0)a1 | for(0 <- @0)a))` across `Child(Child(Root, ...), ...)` at `QN`,
preserving free `"a"` inside the inner quote. -/
theorem nested_openReduct_hosted_N :
    let R₀ := pPar [applyDot nestedOpenUnifier (.fvar "a1"), applyDot nestedOpenUnifier (.fvar "a")]
    let R₁ := pPar [pFor (tProc R₀) demoChan pZero]
    let target := pFor (tProc R₁) demoChan pZero
    ∃ (label' : ℕ → Pattern) (C' : Configuration Pattern ℕ) (made : ℕ),
      LocatedRun (encodeLabel nestedOpenSource) encodeConf label' C' ∧
      NoRootTokens label' C' ∧
      RootCells label' C' [(made, target)] ∧
      CleanChildren label' C' ∧
      ReflClosureDepth 2 nestedOpenSource target ∧
      BagStep conventional (rootBagProcess [(0, nestedOpenSource)])
        (rootBagProcess [(made, target)]) := by
  have split₀ : Splits nestedOpenInner
      ([] ++ pFor (.fvar "a1") demoChan (.fvar "a1") :: ([] ++ pFor pZero demoChan (.fvar "a") :: [])) :=
    show Splits (par _ _) ([_] ++ [_]) from
      .split (.leaf (pFor (.fvar "a1") demoChan (.fvar "a1"))) (.leaf (pFor pZero demoChan (.fvar "a")))
  have plainA : PlainPatterns (applyDot nestedOpenUnifier (.fvar "a1")) := by
    simp [PlainPatterns, PlainPatternsList, applyDot, nestedOpenUnifier, pZero, nQuote,
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
      Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.dotBindings]
  have plainB : PlainPatterns (applyDot nestedOpenUnifier (.fvar "a")) := by
    simp [PlainPatterns, applyDot, nestedOpenUnifier, pZero, nQuote,
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
      Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.dotBindings]
  have sub₀ : HostedSubStepN 0 nestedOpenInner
      (pPar [applyDot nestedOpenUnifier (.fvar "a1"), applyDot nestedOpenUnifier (.fvar "a")])
      (.fvar "a1", pZero) nestedOpenUnifier :=
    .comm [] [] [] (.fvar "a1") pZero demoChan (.fvar "a1") (.fvar "a") nestedOpenUnifier
      split₀ (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) plainA plainB nestedOpenUnifier_gp
      ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have sub₁ : HostedSubStepN 1 (pReflect demoChan nestedOpenInner) _ _ _ :=
    .reflect [] [] demoChan (.leaf _) (by decide +kernel) sub₀
  obtain ⟨noTok, inv, clean, free⟩ :=
    single_root_init nestedOpenSource [.fvar "a1", pZero]
  obtain ⟨label', C', made, run, noTok', inv', clean', -, depth₂, stepN⟩ :=
    refl_depth_root_forward_N sub₁ (pre := []) (post := []) noTok inv (by decide +kernel) clean
      (fun _ m => absurd m List.not_mem_nil) free (fun _ m => absurd m List.not_mem_nil)
  exact ⟨label', C', made, run, noTok', inv', clean', depth₂, stepN⟩

#print axioms child_pack_of_packStep
#print axioms child_pack_of_subStep_N
#print axioms child_pack_of_subStep_C
#print axioms refl_depth_root_pack
#print axioms refl_depth_root_forward_N
#print axioms refl_depth_root_forward_C
#print axioms nested_canary_hosted_N
#print axioms nested_canary_hosted_C
#print axioms nested_openReduct_hosted_N

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem
