import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystemBackwardCells

/-!
# COMM admissibility and global 3-phase location invariant (`P5` state layer)

This module defines the named COMM admissibility predicates, unified cell-level COMM backward
soundness (`rootCells_comm_admissible`, `cellsU_comm_admissible`), and the global 3-phase location
invariant (`ActiveEntry`, `SystemInvBy`, `SystemInvN`, `SystemInvC`, `BackwardReadyN`,
`BackwardReadyC`) together with its apartness, token-identification, and opening helpers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar nQuote tProc pReflect
  applyDot)
open MeTTaOperationsComm (psubst PSubst pvars psubst_of_pvars_nil psubst_pFor psubst_pZero
  commSelection dotted GroundPrincipal firstOrder)
open MeTTaCalculus.Corrected (binders Apart BagEq BagStep CanonicalBagStep conventional)
open FiniteProgram (commRule heatRule clearRule predot predot_pFor predot_ground firstPattern
  secondPattern channelUnknown firstBody secondBody dotted_nil)
open OneFrame (embed)
open ReflQuotient (BagLaws bagCanon groundBags canonSubst_unifies)
open ReflNames (NameLaws nameAction QN QNE nameLaws_iff nameLaws_heads nameLaws_pFor_iff
  bagLaws_of_nameLaws commAtN)
open ReflLocated (atLoc rootLoc childLoc pendingTok doneTok locL locM reflP anyZ atRule located
  commChild heatChild cool closeRoot closeChild openRoot openChild psubst_rootLoc psubst_atLoc_any
  psubst_pendingTok locatedFrame_name rootFiring widen atFiring)
open ReflPacking (cooled bagLaws_cooled_zero psubst_doneTok nameLaws_doneTok_iff)
open ReflLocatedStep (psubst_childLoc nameLaws_pendingTok_iff nameLaws_childLoc_iff res resConf
  info_known take_reads result_present result_label_old result_row commChildAt
  check_fails_pending check_fails_done)
open ReflUniform (predotU predotU_pPar pvars_predotU)
open ReflCorrespondence (child_commit child_comm_reads)

/-! ## Named COMM admissibility predicates and cell-level COMM backward soundness -/

/-- Named step-1′ + `FiniteHosting` COMM side conditions on two input guards `(t, ch, A)` and
`(u, ch', B)`: binder-free canonical ground-bag patterns, canonical ground channels, binder-free
first-order continuations under `Apart`, and ground principal unifiers yielding `PlainPatterns`
`HostedNode` outputs. -/
structure Step1PrimeComm (t ch A u ch' B : Pattern) : Prop where
  noBT : binders t = []
  noBU : binders u = []
  chanL : HostedChan ch
  chanR : HostedChan ch'
  noBA : binders A = []
  noBB : binders B = []
  foA : firstOrder A = true
  foB : firstOrder B = true
  groundT : groundBags t = true
  groundU : groundBags u = true
  canonicalT : bagCanon t = t
  canonicalU : bagCanon u = u
  convention : Apart t A u B
  unifiable : (∃ σ : PSubst, psubst σ t = psubst σ u) →
    ∃ bs : Bindings, GroundPrincipal t u bs ∧
      (∀ y v, bs.lookup y = some v → firstOrder v = true) ∧
      PlainPatterns (applyDot bs A) ∧ PlainPatterns (applyDot bs B) ∧
      HostedNode (applyDot bs A) ∧ HostedNode (applyDot bs B)

/-- Exact ground-pattern COMM admissibility (e.g. a closed-quote listener `listener x R` meeting a
canonical partner `pFor (tProc (canonicalBag R)) x B`, needing no `bagCanon t = t`). -/
structure ExactGroundComm (t ch A u ch' B : Pattern) : Prop where
  groundT : pvars t = []
  groundU : pvars u = []
  exactOnNameLaws : NameLaws (predotU t) (predotU u) → t = u
  chanL : HostedChan ch
  chanR : HostedChan ch'
  foA : firstOrder A = true
  foB : firstOrder B = true
  nodeA : HostedNode A
  nodeB : HostedNode B

/-- COMM admissibility for **Interface N**: either `Step1PrimeComm` or `ExactGroundComm`. -/
def CommAdmissibleN (t ch A u ch' B : Pattern) : Prop :=
  Step1PrimeComm t ch A u ch' B ∨ ExactGroundComm t ch A u ch' B

/-- COMM admissibility for **Interface C**: `CommAdmissibleN` plus ground outputs (`pvars = []`). -/
def CommAdmissibleC (t ch A u ch' B : Pattern) : Prop :=
  CommAdmissibleN t ch A u ch' B ∧
    ∀ bs : Bindings, GroundPrincipal t u bs →
      pvars (applyDot bs A) = [] ∧ pvars (applyDot bs B) = []

private theorem groundPrincipal_empty {t : Pattern} (groundT : pvars t = []) :
    GroundPrincipal t t [] :=
  ⟨fun _ m => absurd m List.not_mem_nil,
    fun x m => by rw [groundT, List.append_nil] at m; exact absurd m List.not_mem_nil,
    rfl, fun _ _ x m => by rw [groundT, List.append_nil] at m; exact absurd m List.not_mem_nil⟩

private theorem applyDot_empty (A : Pattern) (foA : firstOrder A = true) :
    applyDot [] A = A := by
  rw [MeTTaOperationsComm.applyDot_eq [] A foA]
  exact MeTTaOperationsComm.psubst_none A

section CommUpdates

variable {O : Type*} [DecidableEq O]

/-- Unified backward `rootCommAt` soundness under `CommAdmissibleN` on front-permuted `RootCells`. -/
theorem rootCells_comm_admissible {label : O → Pattern} {C : Configuration Pattern O}
    {rest : List (O × Pattern)} {first second m₁ m₂ : O} {ρ : PSubst}
    {t u ch ch' A B : Pattern}
    (inv : RootCells label C ((first, pFor t ch A) :: (second, pFor u ch' B) :: rest))
    (nodes : ∀ q ∈ (first, pFor t ch A) :: (second, pFor u ch' B) :: rest, HostedNode q.2)
    (admPair : CommAdmissibleN t ch A u ch' B)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (rootCommAt ρ first second m₁ m₂)) :
    ch = ch' ∧ ∃ bs : Bindings, GroundPrincipal t u bs ∧
      RootCells (res label C (rootCommAt ρ first second m₁ m₂)).label
        (resConf label C (rootCommAt ρ first second m₁ m₂))
        (rest ++ [(m₁, applyDot bs A), (m₂, applyDot bs B)]) ∧
      (∀ q ∈ rest ++ [(m₁, applyDot bs A), (m₂, applyDot bs B)], HostedNode q.2) ∧
      BagStep conventional
        (rootBagProcess ((first, pFor t ch A) :: (second, pFor u ch' B) :: rest))
        (rootBagProcess (rest ++ [(m₁, applyDot bs A), (m₂, applyDot bs B)])) ∧
      CanonicalBagStep conventional
        (rootBagProcess ((first, pFor t ch A) :: (second, pFor u ch' B) :: rest))
        (rootBagProcess (rest ++ [(m₁, applyDot bs A), (m₂, applyDot bs B)])) := by
  have restNodes : ∀ q ∈ rest, HostedNode q.2 :=
    fun q m => nodes q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ m))
  rcases admPair with s1 | eg
  · obtain ⟨fresh, shapes, enabled, ⟨_, w, solved⟩, -⟩ := (RuleSyntax.admits_iff _).mp admitted
    have distinct : first ≠ second := by
      simpa [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection] using shapes.1
    have mDist : m₁ ≠ m₂ := by
      simpa [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection] using shapes.2.1
    have rF : ∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label first)) (psubst σ (atLoc (predot (pFor t ch A)) rootLoc)) := by
      intro σ s; have r := (inv.rows (first, pFor t ch A) (by simp)).2 σ s
      rwa [predotU_pFor_eq_predot_plain s1.noBT s1.chanL.1 s1.noBA] at r
    have rS : ∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label second)) (psubst σ (atLoc (predot (pFor u ch' B)) rootLoc)) := by
      intro σ s; have r := (inv.rows (second, pFor u ch' B) (by simp)).2 σ s
      rwa [predotU_pFor_eq_predot_plain s1.noBU s1.chanR.1 s1.noBB] at r
    obtain ⟨knownW, unifyW, chanW, -, -⟩ := rootComm_reads_raw label C t u (predot ch) (predot ch')
      (dotted (pvars t) (predot A)) (dotted (pvars u) (predot B)) first second m₁ m₂
      (fun σ s => by have r := rF σ s; rwa [predot_pFor] at r)
      (fun σ s => by have r := rS σ s; rwa [predot_pFor] at r) mDist ρ solved
    rw [predot_ground ch s1.chanL.1, predot_ground ch' s1.chanR.1,
      psubst_of_pvars_nil w ch s1.chanL.1, psubst_of_pvars_nil w ch' s1.chanR.1] at chanW
    have sameCh : ch = ch' := by
      have c := (nameLaws_iff ch ch').mp chanW; rwa [s1.chanL.2, s1.chanR.2] at c
    subst sameCh
    obtain ⟨bs, gp, _, plA, plB, nA, nB⟩ := s1.unifiable
      ⟨_, canonSubst_unifies s1.groundT s1.groundU s1.canonicalT s1.canonicalU
        (bagLaws_of_nameLaws unifyW)⟩
    have freshM : m₁ ∉ C.present ∧ m₂ ∉ C.present := by
      simpa [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, Selection.commit,
        embed] using enabled.fresh
    obtain ⟨-, reads⟩ := rootComm_commit_mixed label C t u ch A B bs gp s1.convention s1.foA s1.foB
      s1.groundT s1.groundU s1.canonicalT s1.canonicalU first second m₁ m₂ rF rS distinct mDist
      (inv.rows (first, pFor t ch A) (by simp)).1 (inv.rows (second, pFor u ch B) (by simp)).1
      freshM.1 freshM.2 knownW unifyW fresh
    have inv' : RootCells (res label C (rootCommAt ρ first second m₁ m₂)).label
        (resConf label C (rootCommAt ρ first second m₁ m₂))
        (rest ++ [(m₁, applyDot bs A), (m₂, applyDot bs B)]) :=
      rootCells_replace_comm (pre := []) (mid := []) (post := rest) inv admitted fun σ s => by
        obtain ⟨-, b₁, b₂⟩ := reads σ s
        rw [predotU_eq_predot_of_plain (applyDot bs A) plA,
          predotU_eq_predot_of_plain (applyDot bs B) plB]
        exact ⟨b₁, b₂⟩
    refine ⟨rfl, bs, gp, inv', fun q m => ?_,
      by simpa [rootBagProcess] using
        bagStep_of_pPar_comm [] [] (rest.map Prod.snd) t u ch A B bs gp s1.convention,
      by simpa [rootBagProcess] using
        canonicalBagStep_of_pPar_comm [] [] (rest.map Prod.snd) t u ch A B bs gp s1.convention⟩
    rcases List.mem_append.mp m with inR | inM
    · exact restNodes q inR
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at inM
      rcases inM with rfl | rfl
      · exact nA
      · exact nB
  · obtain ⟨_, shapes, _, ⟨_, w, solved⟩, -⟩ := (RuleSyntax.admits_iff _).mp admitted
    have mDist : m₁ ≠ m₂ := by
      simpa [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection] using shapes.2.1
    have rF' : ∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label first))
          (psubst σ (atLoc (pFor t ch (predotU A)) rootLoc)) := by
      intro σ s; have r := (inv.rows (first, pFor t ch A) (by simp)).2 σ s
      rwa [ReflUniform.predotU_ground_guard eg.groundT eg.chanL.1] at r
    have rS' : ∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label second))
          (psubst σ (atLoc (pFor u ch' (predotU B)) rootLoc)) := by
      intro σ s; have r := (inv.rows (second, pFor u ch' B) (by simp)).2 σ s
      rwa [ReflUniform.predotU_ground_guard eg.groundU eg.chanR.1] at r
    obtain ⟨_, unifyW, chanW, -, -⟩ := rootComm_reads_raw label C t u ch ch' (predotU A)
      (predotU B) first second m₁ m₂ rF' rS' mDist ρ solved
    rw [psubst_of_pvars_nil w t eg.groundT, psubst_of_pvars_nil w u eg.groundU] at unifyW
    have tEqU : t = u := eg.exactOnNameLaws (by
      simpa only [ReflUniform.predotU_ground t eg.groundT,
        ReflUniform.predotU_ground u eg.groundU] using unifyW)
    subst tEqU
    rw [psubst_of_pvars_nil w ch eg.chanL.1, psubst_of_pvars_nil w ch' eg.chanR.1] at chanW
    have sameCh : ch = ch' := by
      have c := (nameLaws_iff ch ch').mp chanW; rwa [eg.chanL.2, eg.chanR.2] at c
    subst sameCh
    have inv' := rootCells_replace_comm (pre := []) (mid := []) (post := rest)
      (A' := A) (B' := B) inv admitted (fun σ s => by
        obtain ⟨_, _, _, b₁, b₂⟩ := rootComm_reads_raw label C t t ch ch (predotU A)
          (predotU B) first second m₁ m₂ rF' rS' mDist ρ s
        exact ⟨b₁, b₂⟩)
    have gp₀ := groundPrincipal_empty eg.groundT
    have conv₀ : Apart t A t B := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro v inT <;> rw [eg.groundT] at inT <;> cases inT
    rw [← applyDot_empty A eg.foA, ← applyDot_empty B eg.foB] at inv'
    refine ⟨rfl, [], gp₀, inv', fun q m => ?_,
      by simpa [rootBagProcess] using
        bagStep_of_pPar_comm [] [] (rest.map Prod.snd) t t ch A B [] gp₀ conv₀,
      by simpa [rootBagProcess] using
        canonicalBagStep_of_pPar_comm [] [] (rest.map Prod.snd) t t ch A B [] gp₀ conv₀⟩
    rcases List.mem_append.mp m with inR | inM
    · exact restNodes q inR
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at inM
      rcases inM with rfl | rfl
      · rw [applyDot_empty A eg.foA]; exact eg.nodeA
      · rw [applyDot_empty B eg.foB]; exact eg.nodeB

/-- Unified backward `commChildAt` soundness on front-permuted `CellsU` under `CommAdmissibleN`. -/
theorem cellsU_comm_admissible {m x p : Pattern} {label : O → Pattern} {C : Configuration Pattern O}
    {rest : List (O × Pattern)} {first second tk made₁ made₂ madeTok : O} {ρ : PSubst}
    {t u ch ch' A B : Pattern}
    (inv : CellsU (childLoc m x p) m label C tk
      ((first, pFor t ch A) :: (second, pFor u ch' B) :: rest))
    (nodes : ∀ q ∈ (first, pFor t ch A) :: (second, pFor u ch' B) :: rest, HostedNode q.2)
    (admPair : CommAdmissibleN t ch A u ch' B)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (commChildAt ρ first second tk made₁ made₂ madeTok)) :
    ch = ch' ∧ ∃ bs : Bindings, GroundPrincipal t u bs ∧
      DoneCellsU (childLoc m x p) m
        (res label C (commChildAt ρ first second tk made₁ made₂ madeTok)).label
        (resConf label C (commChildAt ρ first second tk made₁ made₂ madeTok))
        madeTok pZero (rest ++ [(made₁, applyDot bs A), (made₂, applyDot bs B)]) ∧
      (∀ q ∈ rest ++ [(made₁, applyDot bs A), (made₂, applyDot bs B)], HostedNode q.2) ∧
      BagLaws (cooled pZero
          ((rest ++ [(made₁, applyDot bs A), (made₂, applyDot bs B)]).map (fun q => predotU q.2)))
        (predotU (pPar ((rest ++ [(made₁, applyDot bs A), (made₂, applyDot bs B)]).map Prod.snd))) ∧
      BagStep conventional
        (pPar (((first, pFor t ch A) :: (second, pFor u ch' B) :: rest).map Prod.snd))
        (pPar ((rest ++ [(made₁, applyDot bs A), (made₂, applyDot bs B)]).map Prod.snd)) ∧
      CanonicalBagStep conventional
        (pPar (((first, pFor t ch A) :: (second, pFor u ch' B) :: rest).map Prod.snd))
        (pPar ((rest ++ [(made₁, applyDot bs A), (made₂, applyDot bs B)]).map Prod.snd)) := by
  let l := childLoc m x p
  obtain ⟨fresh, shapes, enabled, ⟨_, w, solved⟩, -⟩ := (RuleSyntax.admits_iff _).mp admitted
  have mDist : [made₁, made₂, madeTok].Nodup := shapes.2.1
  have m₁NeM₂ : made₁ ≠ made₂ := fun e => (List.nodup_cons.mp mDist).1 (by simp [e])
  have m₁NeMT : made₁ ≠ madeTok := fun e => (List.nodup_cons.mp mDist).1 (by simp [e])
  have m₂NeMT : made₂ ≠ madeTok :=
    fun e => (List.nodup_cons.mp (List.nodup_cons.mp mDist).2).1 (by simp [e])
  have freshM : made₁ ∉ C.present ∧ made₂ ∉ C.present ∧ madeTok ∉ C.present := by
    simpa [commChildAt, Selection.commit, embed] using enabled.fresh
  have zTk : (pendingTok locL locM, tk) ∈
      (commChildAt ρ first second tk made₁ made₂ madeTok).rule.body.take.zip
        (commChildAt ρ first second tk made₁ made₂ madeTok).selection.taken := by
    simp [commChildAt, commChild]
  have rTk₀ := (take_reads _ solved zTk).trans (inv.phase.reads w (info_known _ solved))
  rw [psubst_pendingTok] at rTk₀
  have stepAt : StepAtS l label C (commChildAt ρ first second tk made₁ made₂ madeTok) :=
    ⟨.inl rfl, w, solved, (pending_reading_S rTk₀).1⟩
  have donePhase : ∃ d_tmp, DonePhaseS l m
      (res label C (commChildAt ρ first second tk made₁ made₂ madeTok)).label
      (resConf label C (commChildAt ρ first second tk made₁ made₂ madeTok)) d_tmp := by
    rcases pending_phase_step_S inv.phase _ admitted with ⟨notS, -⟩ | ⟨-, d_tmp, dP⟩
    · exact absurd stepAt notS
    · exact ⟨d_tmp, dP⟩
  obtain ⟨d_tmp, doneP⟩ := donePhase
  obtain ⟨fOut, ndFront⟩ := List.nodup_cons.mp inv.nodup
  obtain ⟨sOut, ndRest⟩ := List.nodup_cons.mp ndFront
  have restIn : ∀ q ∈ rest, q ∈ (first, pFor t ch A) :: (second, pFor u ch' B) :: rest :=
    fun _ m' => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ m')
  have buildDone : ∀ (bs : Bindings),
      (∀ σ : PSubst,
        nameAction.Models σ
          (res label C (commChildAt ρ first second tk made₁ made₂ madeTok)).knowledge →
          NameLaws
            (psubst σ ((res label C (commChildAt ρ first second tk made₁ made₂ madeTok)).label made₁))
            (psubst σ (atLoc (predotU (applyDot bs A)) l)) ∧
          NameLaws
            (psubst σ ((res label C (commChildAt ρ first second tk made₁ made₂ madeTok)).label made₂))
            (psubst σ (atLoc (predotU (applyDot bs B)) l)) ∧
          NameLaws
            (psubst σ ((res label C (commChildAt ρ first second tk made₁ made₂ madeTok)).label madeTok))
            (psubst σ (doneTok l m pZero))) →
      DoneCellsU l m
        (res label C (commChildAt ρ first second tk made₁ made₂ madeTok)).label
        (resConf label C (commChildAt ρ first second tk made₁ made₂ madeTok))
        madeTok pZero (rest ++ [(made₁, applyDot bs A), (made₂, applyDot bs B)]) := by
    intro bs mReads
    have mtEq : madeTok = d_tmp := doneP.unique madeTok
      ((result_present _ madeTok).mpr (.inr (by simp [commChildAt])))
      ⟨w, solved, _, _, by simpa [psubst_doneTok] using (mReads w solved).2.2⟩
    subst mtEq
    refine ⟨doneP, fun σ s => (mReads σ s).2.2, ?_, ?_, ?_⟩
    · rw [List.map_append, List.nodup_append]
      refine ⟨ndRest, by simp [m₁NeM₂], fun a inR b inM ab => ?_⟩
      obtain ⟨q, qM, rfl⟩ := List.mem_map.mp inR
      have qP := (inv.rows q (restIn q qM)).1
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at inM
      rcases inM with rfl | rfl
      · exact freshM.1 (ab ▸ qP)
      · exact freshM.2.1 (ab ▸ qP)
    · intro q qM; rcases List.mem_append.mp qM with inR | inM
      · have qOld := restIn q inR
        obtain ⟨qP, qNeTk, qR⟩ := inv.rows q qOld
        have qInF : q.1 ∈ rest.map Prod.fst := List.mem_map.mpr ⟨q, inR, rfl⟩
        have neF : q.1 ≠ first := fun e => fOut (List.mem_cons_of_mem _ (e ▸ qInF))
        have neS : q.1 ≠ second := fun e => sOut (e ▸ qInF)
        have neM₁ : q.1 ≠ made₁ := fun e => freshM.1 (e ▸ qP)
        have neM₂ : q.1 ≠ made₂ := fun e => freshM.2.1 (e ▸ qP)
        have neMT : q.1 ≠ madeTok := fun e => freshM.2.2 (e ▸ qP)
        exact ⟨(result_present _ q.1).mpr (.inl ⟨qP, by simp [commChildAt, neF, neS, qNeTk]⟩), neMT,
          fun σ s => by
            rw [result_label_old _ (by simp [commChildAt, neM₁, neM₂, neMT])]
            exact qR σ (info_known _ s)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at inM
        rcases inM with rfl | rfl
        · exact ⟨(result_present _ made₁).mpr (.inr (by simp [commChildAt])), m₁NeMT,
            fun σ s => (mReads σ s).1⟩
        · exact ⟨(result_present _ made₂).mpr (.inr (by simp [commChildAt])), m₂NeMT,
            fun σ s => (mReads σ s).2.1⟩
    · intro z zP zNeMT zNotNew σ s y same
      rcases result_row zP with made | ⟨old, notTaken, -, lblOld⟩
      · simp only [commChildAt, List.mem_cons, List.not_mem_nil, or_false] at made
        rcases made with rfl | rfl | rfl
        · exact zNotNew (by simp)
        · exact zNotNew (by simp)
        · exact zNeMT rfl
      · rw [lblOld] at same
        have neF : z ≠ first := fun e => notTaken (by simp [commChildAt, e])
        have neS : z ≠ second := fun e => notTaken (by simp [commChildAt, e])
        have neTk : z ≠ tk := fun e => notTaken (by simp [commChildAt, e])
        refine inv.others z old neTk (fun inAll => ?_) σ (info_known _ s) y same
        rcases List.mem_cons.mp inAll with rfl | inTail
        · exact neF rfl
        · rcases List.mem_cons.mp inTail with rfl | inRest
          · exact neS rfl
          · exact zNotNew (by rw [List.map_append]; exact List.mem_append_left _ inRest)
  have bagCoolZero : ∀ bs : Bindings,
      BagLaws (cooled pZero
          ((rest ++ [(made₁, applyDot bs A), (made₂, applyDot bs B)]).map (fun q => predotU q.2)))
        (predotU (pPar ((rest ++ [(made₁, applyDot bs A), (made₂, applyDot bs B)]).map Prod.snd))) := by
    intro bs; rw [predotU_pPar, List.map_map]; exact bagLaws_cooled_zero _
  have z₁ : (atLoc (pFor firstPattern channelUnknown firstBody) locL, first) ∈
      (commChildAt ρ first second tk made₁ made₂ madeTok).rule.body.take.zip
        (commChildAt ρ first second tk made₁ made₂ madeTok).selection.taken := by
    simp [commChildAt, commChild]
  have z₂ : (atLoc (pFor secondPattern channelUnknown secondBody) locL, second) ∈
      (commChildAt ρ first second tk made₁ made₂ madeTok).rule.body.take.zip
        (commChildAt ρ first second tk made₁ made₂ madeTok).selection.taken := by
    simp [commChildAt, commChild]
  rcases admPair with s1 | eg
  · have rF : ∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label first)) (psubst σ (atLoc (predot (pFor t ch A)) l)) := by
      intro σ s; have r := (inv.rows (first, pFor t ch A) (by simp)).2.2 σ s
      rwa [predotU_pFor_eq_predot_plain s1.noBT s1.chanL.1 s1.noBA] at r
    have rS : ∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label second)) (psubst σ (atLoc (predot (pFor u ch' B)) l)) := by
      intro σ s; have r := (inv.rows (second, pFor u ch' B) (by simp)).2.2 σ s
      rwa [predotU_pFor_eq_predot_plain s1.noBU s1.chanR.1 s1.noBB] at r
    have rF' := fun σ s => by have r := rF σ s; rwa [predot_pFor] at r
    have rS' := fun σ s => by have r := rS σ s; rwa [predot_pFor] at r
    obtain ⟨knownW, unifyW, -, -⟩ := child_comm_reads label C t u (predot ch) (predot ch')
      (dotted (pvars t) (predot A)) (dotted (pvars u) (predot B)) l first second tk made₁ made₂
      madeTok rF' rS' m₁NeM₂ ρ solved
    have h₁ := (take_reads _ solved z₁).trans (rF' w knownW)
    simp only [psubst_atLoc_any, psubst_pFor] at h₁
    have h₂ := (take_reads _ solved z₂).trans (rS' w knownW)
    simp only [psubst_atLoc_any, psubst_pFor] at h₂
    have c₁ := (nameLaws_pFor_iff.mp ((locatedFrame_name.atLoc_iff _ _ _ _).mp h₁).1).2.1
    have c₂ := (nameLaws_pFor_iff.mp ((locatedFrame_name.atLoc_iff _ _ _ _).mp h₂).1).2.1
    have chLaws : NameLaws ch ch' := by
      have both := c₁.symm.trans c₂
      rwa [predot_ground ch s1.chanL.1, predot_ground ch' s1.chanR.1,
        psubst_of_pvars_nil w ch s1.chanL.1, psubst_of_pvars_nil w ch' s1.chanR.1] at both
    have sameCh : ch = ch' := by
      have c := (nameLaws_iff ch ch').mp chLaws; rwa [s1.chanL.2, s1.chanR.2] at c
    subst sameCh
    obtain ⟨bs, gp, _, plA, plB, nA, nB⟩ := s1.unifiable
      ⟨_, canonSubst_unifies s1.groundT s1.groundU s1.canonicalT s1.canonicalU
        (bagLaws_of_nameLaws unifyW)⟩
    obtain ⟨-, reads⟩ := child_commit label C t u ch A B l m bs gp s1.convention s1.foA s1.foB
      s1.groundT s1.groundU s1.canonicalT s1.canonicalU first second tk made₁ made₂ madeTok rF rS
      inv.phase.reads shapes.1 mDist
      ⟨(inv.rows (first, pFor t ch A) (by simp)).1,
        (inv.rows (second, pFor u ch B) (by simp)).1, inv.phase.present⟩
      freshM knownW unifyW fresh
    refine ⟨rfl, bs, gp, buildDone bs (fun σ s => by
      obtain ⟨-, b₁, b₂, bT⟩ := reads σ s
      rw [predotU_eq_predot_of_plain (applyDot bs A) plA,
        predotU_eq_predot_of_plain (applyDot bs B) plB]
      exact ⟨b₁, b₂, bT⟩), fun q m' => ?_, bagCoolZero bs,
      by simpa [List.map_append] using
        bagStep_of_pPar_comm [] [] (rest.map Prod.snd) t u ch A B bs gp s1.convention,
      by simpa [List.map_append] using
        canonicalBagStep_of_pPar_comm [] [] (rest.map Prod.snd) t u ch A B bs gp s1.convention⟩
    rcases List.mem_append.mp m' with inR | inM
    · exact nodes q (restIn q inR)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at inM
      rcases inM with rfl | rfl
      · exact nA
      · exact nB
  · have rF' : ∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label first))
          (psubst σ (atLoc (pFor t ch (predotU A)) l)) := by
      intro σ s; have r := (inv.rows (first, pFor t ch A) (by simp)).2.2 σ s
      rwa [ReflUniform.predotU_ground_guard eg.groundT eg.chanL.1] at r
    have rS' : ∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label second))
          (psubst σ (atLoc (pFor u ch' (predotU B)) l)) := by
      intro σ s; have r := (inv.rows (second, pFor u ch' B) (by simp)).2.2 σ s
      rwa [ReflUniform.predotU_ground_guard eg.groundU eg.chanR.1] at r
    obtain ⟨knownW, unifyW, -, -⟩ := child_comm_reads label C t u
      ch ch' (predotU A) (predotU B) l first second tk made₁ made₂ madeTok
      rF' rS' m₁NeM₂ ρ solved
    rw [psubst_of_pvars_nil w t eg.groundT, psubst_of_pvars_nil w u eg.groundU] at unifyW
    have tEqU : t = u := eg.exactOnNameLaws (by
      simpa only [ReflUniform.predotU_ground t eg.groundT,
        ReflUniform.predotU_ground u eg.groundU] using unifyW)
    subst tEqU
    have h₁ := (take_reads _ solved z₁).trans (rF' w knownW)
    simp only [psubst_atLoc_any, psubst_pFor] at h₁
    have h₂ := (take_reads _ solved z₂).trans (rS' w knownW)
    simp only [psubst_atLoc_any, psubst_pFor] at h₂
    have c₁ := (nameLaws_pFor_iff.mp ((locatedFrame_name.atLoc_iff _ _ _ _).mp h₁).1).2.1
    have c₂ := (nameLaws_pFor_iff.mp ((locatedFrame_name.atLoc_iff _ _ _ _).mp h₂).1).2.1
    have chLaws : NameLaws ch ch' := by
      have both := c₁.symm.trans c₂
      rwa [psubst_of_pvars_nil w ch eg.chanL.1,
        psubst_of_pvars_nil w ch' eg.chanR.1] at both
    have sameCh : ch = ch' := by
      have c := (nameLaws_iff ch ch').mp chLaws; rwa [eg.chanL.2, eg.chanR.2] at c
    subst sameCh
    have gp₀ := groundPrincipal_empty eg.groundT
    have conv₀ : Apart t A t B := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro v inT <;> rw [eg.groundT] at inT <;> cases inT
    refine ⟨rfl, [], gp₀, buildDone [] (fun σ s => ?_), fun q m' => ?_, bagCoolZero [],
      by simpa [List.map_append] using
        bagStep_of_pPar_comm [] [] (rest.map Prod.snd) t t ch A B [] gp₀ conv₀,
      by simpa [List.map_append] using
        canonicalBagStep_of_pPar_comm [] [] (rest.map Prod.snd) t t ch A B [] gp₀ conv₀⟩
    · obtain ⟨_, _, b₁, b₂⟩ := child_comm_reads label C t t
        ch ch (predotU A) (predotU B) l first second tk made₁ made₂ madeTok
        rF' rS' m₁NeM₂ ρ s
      rw [applyDot_empty A eg.foA, applyDot_empty B eg.foB]
      have rTkS := (take_reads _ s zTk).trans (inv.phase.reads σ (info_known _ s))
      rw [psubst_pendingTok, psubst_pendingTok] at rTkS
      obtain ⟨lEqS, mEqS⟩ := nameLaws_pendingTok_iff.mp rTkS
      have mtLbl : ((commChildAt ρ first second tk made₁ made₂ madeTok).result QN
          (embed label C)).label madeTok = psubst ρ (doneTok locL locM pZero) := by
        show (if madeTok = made₁ then _ else if madeTok = made₂ then _ else
          if madeTok = madeTok then _ else _) = _
        rw [if_neg m₁NeMT.symm, if_neg m₂NeMT.symm, if_pos rfl]; rfl
      refine ⟨b₁, b₂, ?_⟩
      change NameLaws (psubst σ (((commChildAt ρ first second tk made₁ made₂ madeTok).result QN
        (embed label C)).label madeTok)) _
      rw [mtLbl, psubst_doneTok, psubst_doneTok, psubst_doneTok, psubst_pZero, psubst_pZero]
      exact nameLaws_doneTok_iff.mpr ⟨lEqS, mEqS, NameLaws.refl _⟩
    · rcases List.mem_append.mp m' with inR | inM
      · exact nodes q (restIn q inR)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at inM
        rcases inM with rfl | rfl
        · rw [applyDot_empty A eg.foA]; exact eg.nodeA
        · rw [applyDot_empty B eg.foB]; exact eg.nodeB

end CommUpdates

/-! ## Active child entries and whole-system invariants (`SystemInvN`, `SystemInvC`) -/

/-- Phase state of an active child entry (live or dead). -/
inductive ActivePhase (O : Type*) where
  | pending (tk : O) (cells : List (O × Pattern))
  | done (d : O) (acc : Pattern) (cells : List (O × Pattern)) (reduct : Pattern)

/-- An active (non-`Clean`) child location in the system, either live or dead (`¬ Live`). -/
structure ActiveEntry (O : Type*) where
  parent : Pattern
  chan : Pattern
  proc : Pattern
  spParent : IsLocSpine parent
  hChan : HostedChan chan
  hProc : HostedNode proc
  phaseState : ActivePhase O

namespace ActiveEntry

def loc {O : Type*} (e : ActiveEntry O) : Pattern :=
  childLoc e.parent e.chan (predotU e.proc)

theorem spLoc {O : Type*} (e : ActiveEntry O) : IsLocSpine e.loc :=
  .child e.chan (predotU e.proc) e.spParent

def tok {O : Type*} (e : ActiveEntry O) : O :=
  match e.phaseState with
  | .pending tk _ => tk
  | .done d _ _ _ => d

def cells {O : Type*} (e : ActiveEntry O) : List (O × Pattern) :=
  match e.phaseState with
  | .pending _ cs => cs
  | .done _ _ cs _ => cs

/-- Semantic validity of an `ActiveEntry` parameterized by the child step relation `StepRel`. -/
def Valid {O : Type*} [DecidableEq O] (StepRel : Pattern → Pattern → Prop)
    (label : O → Pattern) (C : Configuration Pattern O) (e : ActiveEntry O) : Prop :=
  match e.phaseState with
  | .pending tk cs =>
      CellsU e.loc e.parent label C tk cs ∧
      (∀ q ∈ cs, HostedNode q.2) ∧
      BagEq (pPar (cs.map Prod.snd)) e.proc
  | .done d acc cs reduct =>
      DoneCellsU e.loc e.parent label C d acc cs ∧
      (∀ q ∈ cs, HostedNode q.2) ∧
      BagLaws (cooled acc (cs.map (fun q => predotU q.2))) (predotU reduct) ∧
      StepRel e.proc reduct

theorem tok_present {O : Type*} [DecidableEq O] {StepRel : Pattern → Pattern → Prop}
    {label : O → Pattern} {C : Configuration Pattern O} {e : ActiveEntry O}
    (v : e.Valid StepRel label C) : e.tok ∈ C.present := by
  cases h : e.phaseState <;> simp only [Valid, tok, h] at v ⊢
  · exact v.1.phase.present
  · exact v.1.phase.present

theorem valid_keep_other {O : Type*} [DecidableEq O] {StepRel : Pattern → Pattern → Prop}
    {label : O → Pattern} {C : Configuration Pattern O} {e : ActiveEntry O}
    (v : e.Valid StepRel label C) (g : Firing O QNE located PUnit.unit)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (notStep : ¬ StepAtS e.loc label C g) (notHeat : ¬ HeatAtS e.loc label C g)
    (notCool : ¬ CoolAtS e.loc label C g) (notClose : ¬ CloseAtS e.loc label C g) :
    e.Valid StepRel (res label C g).label (resConf label C g) ∧
      (∀ o ∈ C.present, o ∈ g.selection.taken → o ≠ e.tok ∧ o ∉ e.cells.map Prod.fst) := by
  cases h : e.phaseState with
  | pending tk cs =>
      simp only [Valid, tok, cells, h] at v ⊢
      obtain ⟨cNext, notT⟩ := cellsU_keep_other v.1 g admitted notStep notHeat
      exact ⟨⟨cNext, v.2.1, v.2.2⟩, notT⟩
  | done d acc cs reduct =>
      simp only [Valid, tok, cells, h] at v ⊢
      obtain ⟨d', acc', cs', dNext, nNext, bNext, eqUncool, iffP⟩ :=
        doneCellsU_step_or_keep v.1 v.2.1 v.2.2.1 g admitted notClose
      obtain ⟨rfl, rfl, rfl⟩ := eqUncool notCool
      refine ⟨⟨dNext, nNext, bNext, v.2.2.2⟩, fun o oP inT => ⟨fun eEq => ?_, fun inC => ?_⟩⟩
      · subst eEq
        have pD := dNext.phase.present
        rcases (iffP o pD).mp (.inl rfl) with ⟨_, cH⟩ | ⟨_, notInT, _⟩
        · exact notCool cH
        · exact notInT inT
      · obtain ⟨q, qM, rfl⟩ := List.mem_map.mp inC
        have pQ := (dNext.rows q qM).1
        rcases (iffP q.1 pQ).mp (.inr (List.mem_map.mpr ⟨q, qM, rfl⟩)) with ⟨_, cH⟩ | ⟨_, notInT, _⟩
        · exact notCool cH
        · exact notInT inT

end ActiveEntry

/-- Child step witness for **Interface N**: `BagStep conventional`. -/
def StepRelN (P R : Pattern) : Prop := BagStep conventional P R

/-- Child step witness for **Interface C**: `CanonicalBagStep conventional` with `pvars R = []`. -/
def StepRelC (P R : Pattern) : Prop := CanonicalBagStep conventional P R ∧ pvars R = []

/-- Witnessed whole-system state invariant parameterized by `StepRel`. -/
structure SystemInvBy {O : Type*} [DecidableEq O] (StepRel : Pattern → Pattern → Prop)
    (label : O → Pattern) (C : Configuration Pattern O) (P : Pattern)
    (rootRows : List (O × Pattern)) (active : List (ActiveEntry O)) : Prop where
  consistent : ∃ σ₀ : PSubst, nameAction.Models σ₀ C.equations
  noRootTok : NoRootTokens label C
  rootInv : RootCells label C rootRows
  rootNodes : ∀ q ∈ rootRows, HostedNode q.2
  rootBag : BagEq (rootBagProcess rootRows) P
  activeValid : ∀ e ∈ active, e.Valid StepRel label C
  activeApart : active.Pairwise fun e₁ e₂ =>
    ∀ σ : PSubst, nameAction.Models σ C.equations →
      ¬ NameLaws (psubst σ e₁.loc) (psubst σ e₂.loc)
  presentCover : ∀ o ∈ C.present,
    o ∈ rootRows.map Prod.fst ∨ ∃ e ∈ active, o = e.tok ∨ o ∈ e.cells.map Prod.fst

/-- Existentially packaged whole-system state invariant parameterized by `StepRel`. -/
def SystemInv {O : Type*} [DecidableEq O] (StepRel : Pattern → Pattern → Prop)
    (label : O → Pattern) (C : Configuration Pattern O) (P : Pattern) : Prop :=
  ∃ rootRows active, SystemInvBy StepRel label C P rootRows active

/-- Whole-system state invariant for **Interface N** (named quotes). -/
abbrev SystemInvN {O : Type*} [DecidableEq O] := SystemInv (O := O) StepRelN

/-- Whole-system state invariant for **Interface C** (closed quotes). -/
abbrev SystemInvC {O : Type*} [DecidableEq O] := SystemInv (O := O) StepRelC

/-- Named state-level side conditions for backward `COMM` and `close` soundness under **N**. -/
structure BackwardReadyN {O : Type*} (C : Configuration Pattern O)
    (rootRows : List (O × Pattern)) (active : List (ActiveEntry O)) : Prop where
  rootCommReady : ∀ q₁ ∈ rootRows, ∀ q₂ ∈ rootRows, ∀ t ch A u ch' B : Pattern,
    q₁.1 ≠ q₂.1 → q₁.2 = pFor t ch A → q₂.2 = pFor u ch' B → CommAdmissibleN t ch A u ch' B
  childCommReady : ∀ e ∈ active, ∀ (tk : O) (cs : List (O × Pattern)),
    e.phaseState = .pending tk cs →
    ∀ q₁ ∈ cs, ∀ q₂ ∈ cs, ∀ t ch A u ch' B : Pattern,
      q₁.1 ≠ q₂.1 → q₁.2 = pFor t ch A → q₂.2 = pFor u ch' B → CommAdmissibleN t ch A u ch' B
  noCaptureRoot : ∀ e ∈ active, ∀ q ∈ rootRows, ∀ x Q : Pattern,
    q.2 = pReflect x Q →
    (∃ σ : PSubst, nameAction.Models σ C.equations ∧
      NameLaws (psubst σ e.loc) (psubst σ (childLoc rootLoc x (predotU Q)))) →
    e.parent = rootLoc ∧ e.chan = x ∧ e.proc = Q
  noCaptureChild : ∀ e_g ∈ active, ∀ e_p ∈ active, ∀ (tk : O) (cs : List (O × Pattern)),
    e_p.phaseState = .pending tk cs →
    ∀ q ∈ cs, ∀ y Q : Pattern, q.2 = pReflect y Q →
      (∃ σ : PSubst, nameAction.Models σ C.equations ∧
        NameLaws (psubst σ e_g.loc) (psubst σ (childLoc e_p.loc y (predotU Q)))) →
      e_g.parent = e_p.loc ∧ e_g.chan = y ∧ e_g.proc = Q

/-- Named state-level side conditions for backward `COMM` and `close` soundness under **C**:
`BackwardReadyN` plus ground outputs and ground co-components (`pvars = []`) at any child commit. -/
structure BackwardReadyC {O : Type*} (C : Configuration Pattern O)
    (rootRows : List (O × Pattern)) (active : List (ActiveEntry O)) : Prop where
  rootCommReady : ∀ q₁ ∈ rootRows, ∀ q₂ ∈ rootRows, ∀ t ch A u ch' B : Pattern,
    q₁.1 ≠ q₂.1 → q₁.2 = pFor t ch A → q₂.2 = pFor u ch' B → CommAdmissibleN t ch A u ch' B
  childCommReady : ∀ e ∈ active, ∀ (tk : O) (cs : List (O × Pattern)),
    e.phaseState = .pending tk cs →
    ∀ q₁ ∈ cs, ∀ q₂ ∈ cs, ∀ t ch A u ch' B : Pattern,
      q₁.1 ≠ q₂.1 → q₁.2 = pFor t ch A → q₂.2 = pFor u ch' B →
        CommAdmissibleC t ch A u ch' B ∧
        ∀ q ∈ cs, q.1 ≠ q₁.1 → q.1 ≠ q₂.1 → pvars q.2 = []
  childCloseReady : ∀ e_p ∈ active, ∀ (tk : O) (cs : List (O × Pattern)),
    e_p.phaseState = .pending tk cs →
    ∀ q_r ∈ cs, ∀ y Q : Pattern, q_r.2 = pReflect y Q →
      ∀ q ∈ cs, q.1 ≠ q_r.1 → pvars q.2 = []
  noCaptureRoot : ∀ e ∈ active, ∀ q ∈ rootRows, ∀ x Q : Pattern,
    q.2 = pReflect x Q →
    (∃ σ : PSubst, nameAction.Models σ C.equations ∧
      NameLaws (psubst σ e.loc) (psubst σ (childLoc rootLoc x (predotU Q)))) →
    e.parent = rootLoc ∧ e.chan = x ∧ e.proc = Q
  noCaptureChild : ∀ e_g ∈ active, ∀ e_p ∈ active, ∀ (tk : O) (cs : List (O × Pattern)),
    e_p.phaseState = .pending tk cs →
    ∀ q ∈ cs, ∀ y Q : Pattern, q.2 = pReflect y Q →
      (∃ σ : PSubst, nameAction.Models σ C.equations ∧
        NameLaws (psubst σ e_g.loc) (psubst σ (childLoc e_p.loc y (predotU Q)))) →
      e_g.parent = e_p.loc ∧ e_g.chan = y ∧ e_g.proc = Q

/-! ## Apartness, token-identification, and opening helpers for `SystemInvBy` -/

/-- All-solutions location apartness on an equation list. -/
def ApartOn {O : Type*} (eqs : List (Pattern × Pattern)) (e₁ e₂ : ActiveEntry O) : Prop :=
  ∀ σ : PSubst, nameAction.Models σ eqs → ¬ NameLaws (psubst σ e₁.loc) (psubst σ e₂.loc)

theorem apartOn_symm {O : Type*} {eqs : List (Pattern × Pattern)} {e₁ e₂ : ActiveEntry O}
    (h : ApartOn eqs e₁ e₂) : ApartOn eqs e₂ e₁ :=
  fun σ s same => h σ s same.symm

theorem apartOn_mono {O : Type*} [DecidableEq O] {C : Configuration Pattern O}
    {label : O → Pattern} (g : Firing O QNE located PUnit.unit) {e₁ e₂ : ActiveEntry O}
    (h : ApartOn C.equations e₁ e₂) : ApartOn (resConf label C g).equations e₁ e₂ :=
  fun σ s => h σ (info_known g s)

theorem active_remove_one {O : Type*} {eqs : List (Pattern × Pattern)}
    {active : List (ActiveEntry O)} (pw : active.Pairwise (ApartOn eqs))
    {e₀ : ActiveEntry O} (inA : e₀ ∈ active) :
    ∃ restA : List (ActiveEntry O),
      active.Perm (e₀ :: restA) ∧ restA.Pairwise (ApartOn eqs) ∧
      ∀ e ∈ restA, e ∈ active ∧ ApartOn eqs e e₀ := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem inA
  have pm : (pre ++ e₀ :: post).Perm (e₀ :: (pre ++ post)) := List.perm_middle
  obtain ⟨hd, tl⟩ := List.pairwise_cons.mp ((pm.pairwise_iff (fun {_ _} h => apartOn_symm h)).mp pw)
  exact ⟨pre ++ post, pm, tl, fun e m => ⟨pm.symm.subset (List.mem_cons_of_mem _ m),
    apartOn_symm (hd e m)⟩⟩

section StateHelpers

variable {O : Type*} [DecidableEq O]

theorem presentCover_identify_pending {StepRel : Pattern → Pattern → Prop}
    {label : O → Pattern} {C : Configuration Pattern O} {P : Pattern}
    {rootRows : List (O × Pattern)} {active : List (ActiveEntry O)}
    (sys : SystemInvBy StepRel label C P rootRows active) {o : O} (oPres : o ∈ C.present)
    {w : PSubst} (known : nameAction.Models w C.equations) {l' m' : Pattern}
    (reads : NameLaws (psubst w (label o)) (pendingTok l' m')) :
    ∃ e ∈ active, ∃ cs, e.phaseState = .pending o cs := by
  rcases sys.presentCover o oPres with inR | ⟨e, eIn, isTok | inC⟩
  · obtain ⟨q, qM, rfl⟩ := List.mem_map.mp inR
    have r := (sys.rootInv.rows q qM).2 w known; rw [psubst_atLoc_any] at r
    exact absurd (nameLaws_heads (reads.symm.trans r)) (by decide)
  · subst isTok; have v := sys.activeValid e eIn
    cases h : e.phaseState with
    | pending tk cs =>
        have eqTk : e.tok = tk := by simp [ActiveEntry.tok, h]
        exact ⟨e, eIn, cs, eqTk ▸ h⟩
    | done d acc cs red =>
        have eqD : e.tok = d := by simp [ActiveEntry.tok, h]
        rw [eqD] at reads
        simp only [ActiveEntry.Valid, h] at v
        have r := v.1.readsTok w known; rw [psubst_doneTok] at r
        exact absurd (nameLaws_heads (reads.symm.trans r)) (by decide)
  · obtain ⟨q, qM, rfl⟩ := List.mem_map.mp inC
    have v := sys.activeValid e eIn
    cases h : e.phaseState <;> simp only [ActiveEntry.Valid, ActiveEntry.cells, h] at v qM
    · have r := (v.1.rows q qM).2.2 w known; rw [psubst_atLoc_any] at r
      exact absurd (nameLaws_heads (reads.symm.trans r)) (by decide)
    · have r := (v.1.rows q qM).2.2 w known; rw [psubst_atLoc_any] at r
      exact absurd (nameLaws_heads (reads.symm.trans r)) (by decide)

theorem presentCover_identify_done {StepRel : Pattern → Pattern → Prop}
    {label : O → Pattern} {C : Configuration Pattern O} {P : Pattern}
    {rootRows : List (O × Pattern)} {active : List (ActiveEntry O)}
    (sys : SystemInvBy StepRel label C P rootRows active) {o : O} (oPres : o ∈ C.present)
    {w : PSubst} (known : nameAction.Models w C.equations) {l' m' c' : Pattern}
    (reads : NameLaws (psubst w (label o)) (doneTok l' m' c')) :
    ∃ e ∈ active, ∃ acc cs red, e.phaseState = .done o acc cs red := by
  rcases sys.presentCover o oPres with inR | ⟨e, eIn, isTok | inC⟩
  · obtain ⟨q, qM, rfl⟩ := List.mem_map.mp inR
    have r := (sys.rootInv.rows q qM).2 w known; rw [psubst_atLoc_any] at r
    exact absurd (nameLaws_heads (reads.symm.trans r)) (by decide)
  · subst isTok; have v := sys.activeValid e eIn
    cases h : e.phaseState with
    | pending tk cs =>
        have eqTk : e.tok = tk := by simp [ActiveEntry.tok, h]
        rw [eqTk] at reads
        simp only [ActiveEntry.Valid, h] at v
        have r := v.1.phase.reads w known; rw [psubst_pendingTok] at r
        exact absurd (nameLaws_heads (reads.symm.trans r)) (by decide)
    | done d acc cs red =>
        have eqD : e.tok = d := by simp [ActiveEntry.tok, h]
        exact ⟨e, eIn, acc, cs, red, eqD ▸ h⟩
  · obtain ⟨q, qM, rfl⟩ := List.mem_map.mp inC
    have v := sys.activeValid e eIn
    cases h : e.phaseState <;> simp only [ActiveEntry.Valid, ActiveEntry.cells, h] at v qM
    · have r := (v.1.rows q qM).2.2 w known; rw [psubst_atLoc_any] at r
      exact absurd (nameLaws_heads (reads.symm.trans r)) (by decide)
    · have r := (v.1.rows q qM).2.2 w known; rw [psubst_atLoc_any] at r
      exact absurd (nameLaws_heads (reads.symm.trans r)) (by decide)

theorem active_keep_nonChildRule {StepRel : Pattern → Pattern → Prop}
    {label : O → Pattern} {C : Configuration Pattern O} {e : ActiveEntry O}
    (v : e.Valid StepRel label C) {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (hRule : g.rule = atRule rootLoc commRule ∨ g.rule = atRule rootLoc heatRule ∨
      g.rule = atRule rootLoc clearRule ∨ g.rule = openRoot ∨ g.rule = openChild) :
    e.Valid StepRel (res label C g).label (resConf label C g) ∧
      (∀ o ∈ C.present, o ∈ g.selection.taken → o ≠ e.tok ∧ o ∉ e.cells.map Prod.fst) := by
  have notCC : g.rule ≠ commChild := by
    intro eq; have c := congrArg (fun r => r.body.take.length) eq
    rcases hRule with h | h | h | h | h <;> rw [h] at c <;>
      simp [atRule, RuleInstance.map, commRule, heatRule, clearRule, openRoot, openChild, commChild] at c
  have notClC : g.rule ≠ closeChild := by
    intro eq; have c := congrArg (fun r => r.body.take.length) eq
    rcases hRule with h | h | h | h | h <;> rw [h] at c <;>
      simp [atRule, RuleInstance.map, commRule, heatRule, clearRule, openRoot, openChild, closeChild] at c
  have notHC : g.rule ≠ heatChild := by
    intro eq; rcases hRule with h | h | h | h | h
    · have c := congrArg (fun r => r.body.take.length) eq; rw [h] at c; simp [atRule, RuleInstance.map, commRule, heatChild] at c
    · have c := congrArg (fun r => r.body.read.length) eq; rw [h] at c; simp [atRule, RuleInstance.map, heatRule, heatChild] at c
    · have c := congrArg (fun r => r.body.produce.length) eq; rw [h] at c; simp [atRule, RuleInstance.map, clearRule, heatChild] at c
    · have c := congrArg (fun r => r.body.take.length) eq; rw [h] at c; simp [openRoot, heatChild] at c
    · have c := congrArg (fun r => r.body.take.length) eq; rw [h] at c; simp [openChild, heatChild] at c
  have notCool : g.rule ≠ cool := by
    intro eq; rcases hRule with h | h | h | h | h
    · have c := congrArg (fun r => r.body.produce.length) eq; rw [h] at c; simp [atRule, RuleInstance.map, commRule, cool] at c
    · have c := congrArg (fun r => r.body.take.length) eq; rw [h] at c; simp [atRule, RuleInstance.map, heatRule, cool] at c
    · have c := congrArg (fun r => r.body.take.length) eq; rw [h] at c; simp [atRule, RuleInstance.map, clearRule, cool] at c
    · have c := congrArg (fun r => r.body.take.length) eq; rw [h] at c; simp [openRoot, cool] at c
    · have c := congrArg (fun r => r.body.take.length) eq; rw [h] at c; simp [openChild, cool] at c
  have notClR : g.rule ≠ closeRoot := by
    intro eq; rcases hRule with h | h | h | h | h
    · have c := congrArg (fun r => r.body.produce.length) eq; rw [h] at c; simp [atRule, RuleInstance.map, commRule, closeRoot] at c
    · have c := congrArg (fun r => r.body.take.length) eq; rw [h] at c; simp [atRule, RuleInstance.map, heatRule, closeRoot] at c
    · have c := congrArg (fun r => r.body.take.length) eq; rw [h] at c; simp [atRule, RuleInstance.map, clearRule, closeRoot] at c
    · have c := congrArg (fun r => r.body.take.length) eq; rw [h] at c; simp [openRoot, closeRoot] at c
    · have c := congrArg (fun r => r.body.take.length) eq; rw [h] at c; simp [openChild, closeRoot] at c
  exact e.valid_keep_other v g admitted
    (fun ⟨h, _⟩ => h.elim notCC notClC) (fun ⟨h, _⟩ => notHC h)
    (fun ⟨h, _⟩ => notCool h) (fun h => h.elim (fun ⟨c, _⟩ => notClR c) (fun ⟨c, _⟩ => notClC c))

theorem open_apart_and_clean {StepRel : Pattern → Pattern → Prop}
    {label : O → Pattern} {C : Configuration Pattern O} {P m_new x_new Q parPat : Pattern}
    {rootRows : List (O × Pattern)} {active : List (ActiveEntry O)}
    (sys : SystemInvBy StepRel label C P rootRows active)
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (hasPend : Check.predicate .none (pendingTok (childLoc parPat channelUnknown reflP) parPat) ∈ g.rule.body.checks)
    (hasDone : Check.predicate .none (doneTok (childLoc parPat channelUnknown reflP) parPat anyZ) ∈ g.rule.body.checks)
    (noTakes : g.rule.body.take = []) (noTells : g.rule.body.tell = [])
    (readsApart : ∀ t ∈ g.rule.body.read, "Z" ∉ pvars t)
    (parApart : "Z" ∉ pvars (childLoc parPat channelUnknown reflP) ∧ "Z" ∉ pvars parPat)
    (lEq : ∀ σ : PSubst, nameAction.Models σ (resConf label C g).equations →
      NameLaws (psubst σ (psubst g.opening (childLoc parPat channelUnknown reflP)))
        (psubst σ (childLoc m_new x_new (predotU Q)))) :
    (∀ e ∈ active, ∀ σ : PSubst, nameAction.Models σ (resConf label C g).equations →
      ¬ NameLaws (psubst σ e.loc) (psubst σ (childLoc m_new x_new (predotU Q)))) ∧
    (∀ o ∈ C.present, ∀ σ : PSubst, nameAction.Models σ (resConf label C g).equations →
      (∀ m', ¬ NameLaws (psubst σ (label o))
        (pendingTok (psubst σ (childLoc m_new x_new (predotU Q))) m')) ∧
      (∀ m' c, ¬ NameLaws (psubst σ (label o))
        (doneTok (psubst σ (childLoc m_new x_new (predotU Q))) m' c)) ∧
      (∀ y, ¬ NameLaws (psubst σ (label o))
        (atLoc y (psubst σ (childLoc m_new x_new (predotU Q)))))) := by
  let l_new := childLoc m_new x_new (predotU Q)
  have apartE : ∀ e ∈ active, ∀ σ : PSubst, nameAction.Models σ (resConf label C g).equations →
      ¬ NameLaws (psubst σ e.loc) (psubst σ l_new) := by
    intro e eIn σ s same
    have known := info_known g s
    have lPat : NameLaws (psubst σ (psubst g.opening (childLoc parPat channelUnknown reflP)))
        (childLoc (psubst σ m_new) (psubst σ x_new) (psubst σ (predotU Q))) := by
      have h := lEq σ s; rwa [psubst_childLoc] at h
    have same' := same
    rw [ActiveEntry.loc, psubst_childLoc, psubst_childLoc] at same'
    obtain ⟨mEq, xEq, qEq⟩ := nameLaws_childLoc_iff.mp same'
    have v := sys.activeValid e eIn
    cases h : e.phaseState with
    | pending tk cs =>
        simp only [ActiveEntry.Valid, h] at v
        have rTk := v.1.phase.reads σ known
        rw [psubst_pendingTok, ActiveEntry.loc, psubst_childLoc] at rTk
        have rTk' := rTk.trans (nameLaws_pendingTok_iff.mpr
          ⟨nameLaws_childLoc_iff.mpr ⟨mEq, xEq, qEq⟩, mEq⟩)
        exact check_fails_pending admitted hasPend s lPat v.1.phase.present rTk'
    | done d acc cs red =>
        simp only [ActiveEntry.Valid, h] at v
        obtain ⟨c, rDn⟩ := v.1.phase.reads σ known
        rw [ActiveEntry.loc, psubst_childLoc] at rDn
        have rDn' := rDn.trans (nameLaws_doneTok_iff.mpr
          ⟨nameLaws_childLoc_iff.mpr ⟨mEq, xEq, qEq⟩, mEq, NameLaws.refl _⟩)
        exact check_fails_done admitted hasDone noTakes noTells readsApart parApart s lPat
          v.1.phase.present rDn'
  refine ⟨apartE, fun o oP σ s => ?_⟩
  have known := info_known g s
  rcases sys.presentCover o oP with inR | ⟨e, eIn, isTok | inC⟩
  · obtain ⟨q, qM, rfl⟩ := List.mem_map.mp inR
    have r := (sys.rootInv.rows q qM).2 σ known
    rw [psubst_atLoc_any, psubst_rootLoc] at r
    refine ⟨fun _ sm => absurd (nameLaws_heads (r.symm.trans sm)) (by decide),
      fun _ _ sm => absurd (nameLaws_heads (r.symm.trans sm)) (by decide), fun y sm => ?_⟩
    have locEq := ((locatedFrame_name.atLoc_iff _ _ _ _).mp (r.symm.trans sm)).2
    rw [psubst_childLoc] at locEq
    exact not_nameLaws_childLoc_rootLoc _ _ _ locEq.symm
  · subst isTok; have v := sys.activeValid e eIn; have notEq := apartE e eIn σ s
    cases h : e.phaseState with
    | pending tk cs =>
        have eqTk : e.tok = tk := by simp [ActiveEntry.tok, h]
        rw [eqTk]; simp only [ActiveEntry.Valid, h] at v
        have r := v.1.phase.reads σ known; rw [psubst_pendingTok] at r
        refine ⟨fun m' sm => notEq (nameLaws_pendingTok_iff.mp (r.symm.trans sm)).1,
          fun _ _ sm => absurd (nameLaws_heads (r.symm.trans sm)) (by decide),
          fun _ sm => absurd (nameLaws_heads (r.symm.trans sm)) (by decide)⟩
    | done d acc cs red =>
        have eqD : e.tok = d := by simp [ActiveEntry.tok, h]
        rw [eqD]; simp only [ActiveEntry.Valid, h] at v
        have r := v.1.readsTok σ known; rw [psubst_doneTok] at r
        refine ⟨fun _ sm => absurd (nameLaws_heads (r.symm.trans sm)) (by decide),
          fun _ _ sm => notEq (nameLaws_doneTok_iff.mp (r.symm.trans sm)).1,
          fun _ sm => absurd (nameLaws_heads (r.symm.trans sm)) (by decide)⟩
  · obtain ⟨q, qM, rfl⟩ := List.mem_map.mp inC
    have v := sys.activeValid e eIn; have notEq := apartE e eIn σ s
    have r : NameLaws (psubst σ (label q.1)) (atLoc (psubst σ (predotU q.2)) (psubst σ e.loc)) := by
      cases h : e.phaseState <;> simp only [ActiveEntry.Valid, ActiveEntry.cells, h] at v qM
      · have r₀ := (v.1.rows q qM).2.2 σ known; rwa [psubst_atLoc_any] at r₀
      · have r₀ := (v.1.rows q qM).2.2 σ known; rwa [psubst_atLoc_any] at r₀
    exact ⟨fun _ sm => absurd (nameLaws_heads (r.symm.trans sm)) (by decide),
      fun _ _ sm => absurd (nameLaws_heads (r.symm.trans sm)) (by decide),
      fun y sm => notEq ((locatedFrame_name.atLoc_iff _ _ _ _).mp (r.symm.trans sm)).2⟩

end StateHelpers

#print axioms rootCells_comm_admissible
#print axioms cellsU_comm_admissible
#print axioms ActiveEntry.valid_keep_other
#print axioms open_apart_and_clean

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem
