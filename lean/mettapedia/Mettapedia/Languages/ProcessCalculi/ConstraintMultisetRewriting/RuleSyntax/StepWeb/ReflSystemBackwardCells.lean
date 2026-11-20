import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystemRecursion

/-!
# Hosted node grammar, firing partition, and cell-level backward transitions (`P5` base)

This module establishes the cell-level building blocks for whole-system backward stuttering
reflection (`P5`) at the name frame `QN`:

* **Visible vs administrative partition** (`RootVisible`, `Administrative`,
  `located_firing_partition`): partitions all firings of `ReflLocated.located` into `RootVisible`
  (`rootComm` or `closeRoot`) and `Administrative` (the remaining 8 housekeeping and child rules).
* **Hosted node grammar** (`HostedChan`, `HostedNode`, `hostedNode_match_*`): extends `RootTerm`
  with quoted values `nQuote v` (`@0`, `@(0)`, etc., emitted by `applyDot` on drop continuations)
  and lifts root `heat` and `clear` reflection (`rootCells_heat_node_reflects`,
  `rootCells_clear_node_reflects`) to `HostedNode`.
* **Canonical firing normal forms** (`eq_openRootAt`, `eq_closeRootAt`, `eq_openChildAt`,
  `eq_closeChildAt`) and **`CellsU` / `DoneCellsU` backward transitions** (`cellsU_keep_other`,
  `cellsU_heat_reflects`, `doneCellsU_step_or_keep`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar nQuote tProc pReflect)
open MeTTaOperationsComm (psubst PSubst pvars psubst_pFor psubst_pZero psubst_nQuote)
open MeTTaCalculus.Corrected (BagEq)
open FiniteProgram (commRule heatRule clearRule leftPart)
open OneFrame (embed)
open ReflQuotient (BagLaws)
open ReflNames (NameLaws nameAction QN QNE nameCanon nameLaws_iff nameLaws_heads
  nameCanon_apply_head nameCanon_collection)
open ReflLocated (atLoc rootLoc childLoc pendingTok doneTok locL locM accC atRule located
  commChild heatChild heatChildN cool closeRoot closeChild openRoot openChild exists_mem_zip
  psubst_rootLoc psubst_atLoc_any psubst_pendingTok psubst_par locatedFrame_name
  heatChild_takes_pair heatChild_reads_determinately rootFiring widen atFiring heatN)
open ReflPacking (cooled bagLaws_cooled psubst_doneTok nameLaws_doneTok_iff coolAt cool_reads)
open ReflLocatedStep (located_cases head_of_reading₂ psubst_childLoc nameLaws_pendingTok_iff
  exists_mem_zip_right res resConf info_known take_reads read_reads taken_row
  solution_of_admitted result_present result_label_old made_label made_not_present result_row
  closeChildAt psubst_pReflect check_fails_pending check_fails_done openRoot_checks
  openChild_checks)
open ReflUniform (predotU predotU_pFor predotU_pZero predotU_nQuote)
open ReflCorrespondence (openRootAt closeRootAt)

/-! ## Partition of `located` into `RootVisible` and `Administrative` -/

/-- A firing of `located` is visible at `Root` when its rule is `rootComm` or `closeRoot`. -/
def RootVisible {O : Type*} (g : Firing O QNE located PUnit.unit) : Prop :=
  g.rule = atRule rootLoc commRule ∨ g.rule = closeRoot

/-- A firing of `located` is administrative when its rule is one of the 8 housekeeping /
child-internal rules. -/
def Administrative {O : Type*} (g : Firing O QNE located PUnit.unit) : Prop :=
  g.rule = atRule rootLoc heatRule ∨ g.rule = atRule rootLoc clearRule ∨
    g.rule = commChild ∨ g.rule = heatChild ∨ g.rule = cool ∨
    g.rule = closeChild ∨ g.rule = openRoot ∨ g.rule = openChild

theorem located_firing_partition {O : Type*} (g : Firing O QNE located PUnit.unit) :
    (RootVisible g ∧ ¬ Administrative g) ∨ (Administrative g ∧ ¬ RootVisible g) := by
  have neRules :
      atRule rootLoc commRule ≠ atRule rootLoc heatRule ∧
      atRule rootLoc commRule ≠ atRule rootLoc clearRule ∧
      atRule rootLoc commRule ≠ commChild ∧
      atRule rootLoc commRule ≠ heatChild ∧
      atRule rootLoc commRule ≠ cool ∧
      atRule rootLoc commRule ≠ closeChild ∧
      atRule rootLoc commRule ≠ openRoot ∧
      atRule rootLoc commRule ≠ openChild ∧
      closeRoot ≠ atRule rootLoc heatRule ∧
      closeRoot ≠ atRule rootLoc clearRule ∧
      closeRoot ≠ commChild ∧
      closeRoot ≠ heatChild ∧
      closeRoot ≠ cool ∧
      closeRoot ≠ closeChild ∧
      closeRoot ≠ openRoot ∧
      closeRoot ≠ openChild := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; have c := congrArg (fun r => r.body.take.length) h; simp [atRule, RuleInstance.map, commRule, heatRule] at c
    · intro h; have c := congrArg (fun r => r.body.take.length) h; simp [atRule, RuleInstance.map, commRule, clearRule] at c
    · intro h; have c := congrArg (fun r => r.body.take.length) h; simp [atRule, RuleInstance.map, commRule, commChild] at c
    · intro h; have c := congrArg (fun r => r.body.take.length) h; simp [atRule, RuleInstance.map, commRule, heatChild] at c
    · intro h; have c := congrArg (fun r => r.body.produce.length) h; simp [atRule, RuleInstance.map, commRule, cool] at c
    · intro h; have c := congrArg (fun r => r.body.take.length) h; simp [atRule, RuleInstance.map, commRule, closeChild] at c
    · intro h; have c := congrArg (fun r => r.body.take.length) h; simp [atRule, RuleInstance.map, commRule, openRoot] at c
    · intro h; have c := congrArg (fun r => r.body.take.length) h; simp [atRule, RuleInstance.map, commRule, openChild] at c
    · intro h; have c := congrArg (fun r => r.body.take.length) h; simp [closeRoot, atRule, RuleInstance.map, heatRule] at c
    · intro h; have c := congrArg (fun r => r.body.take.length) h; simp [closeRoot, atRule, RuleInstance.map, clearRule] at c
    · intro h; have c := congrArg (fun r => r.body.take.length) h; simp [closeRoot, commChild] at c
    · intro h; have c := congrArg (fun r => r.body.take.length) h; simp [closeRoot, heatChild] at c
    · intro h; have c := congrArg (fun r => r.body.checks.length) h; simp [closeRoot, cool] at c
    · intro h; have c := congrArg (fun r => r.body.take.length) h; simp [closeRoot, closeChild] at c
    · intro h; have c := congrArg (fun r => r.body.take.length) h; simp [closeRoot, openRoot] at c
    · intro h; have c := congrArg (fun r => r.body.take.length) h; simp [closeRoot, openChild] at c
  rcases located_cases g.member with rC | rH | rCl | cC | cH | cCl | clR | clC | opR | opC
  · exact .inl ⟨.inl rC, by rw [Administrative, rC]; tauto⟩
  · exact .inr ⟨.inl rH, by rw [RootVisible, rH]; tauto⟩
  · exact .inr ⟨.inr (.inl rCl), by rw [RootVisible, rCl]; tauto⟩
  · exact .inr ⟨.inr (.inr (.inl cC)), by rw [RootVisible, cC]; tauto⟩
  · exact .inr ⟨.inr (.inr (.inr (.inl cH))), by rw [RootVisible, cH]; tauto⟩
  · exact .inr ⟨.inr (.inr (.inr (.inr (.inl cCl)))), by rw [RootVisible, cCl]; tauto⟩
  · exact .inl ⟨.inr clR, by rw [Administrative, clR]; tauto⟩
  · exact .inr ⟨.inr (.inr (.inr (.inr (.inr (.inl clC))))), by rw [RootVisible, clC]; tauto⟩
  · exact .inr ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inl opR)))))), by rw [RootVisible, opR]; tauto⟩
  · exact .inr ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inr opC)))))), by rw [RootVisible, opC]; tauto⟩

/-! ## Hosted channels, hosted nodes, and `NameLaws` head discrimination -/

/-- Ground, name-canonical channel name (`pvars ch = []` and `nameCanon ch = ch`). -/
def HostedChan (ch : Pattern) : Prop := pvars ch = [] ∧ nameCanon ch = ch

/-- Process terms hosted at `Root` or inside a child's heated cells: `0`, quoted values `@v`
(produced by `applyDot` on drop continuations), binary `par`, `pFor`, and `pReflect`. -/
inductive HostedNode : Pattern → Prop where
  | zero : HostedNode pZero
  | quote (v : Pattern) : HostedNode (nQuote v)
  | par {a b : Pattern} : HostedNode a → HostedNode b → HostedNode (par a b)
  | guard {t ch A : Pattern} : HostedChan ch → HostedNode (pFor t ch A)
  | reflect {x Q : Pattern} : HostedChan x → HostedNode Q → HostedNode (pReflect x Q)

private theorem not_nameLaws_par_apply' (d e : Pattern) (c : String) (args : List Pattern) :
    ¬ NameLaws (par d e) (.apply c args) := by
  intro same; have canon := (nameLaws_iff _ _).mp same
  obtain ⟨_, hR⟩ := nameCanon_apply_head c args
  rw [hR, par, pPar, nameCanon_collection] at canon; cases canon

private theorem not_nameLaws_apply_diff' {c₁ c₂ : String} (diff : c₁ ≠ c₂)
    (args₁ args₂ : List Pattern) : ¬ NameLaws (.apply c₁ args₁) (.apply c₂ args₂) := by
  intro same; have canon := (nameLaws_iff _ _).mp same
  obtain ⟨_, h₁⟩ := nameCanon_apply_head c₁ args₁
  obtain ⟨_, h₂⟩ := nameCanon_apply_head c₂ args₂
  rw [h₁, h₂] at canon; exact diff (Pattern.apply.inj canon).1

theorem hostedNode_match_par {P a' b' : Pattern} {σ : PSubst} (h : HostedNode P)
    (same : NameLaws (par a' b') (psubst σ (predotU P))) :
    ∃ a b, P = par a b ∧ HostedNode a ∧ HostedNode b := by
  cases h with
  | zero => rw [predotU_pZero, psubst_pZero] at same; exact absurd same (not_nameLaws_par_apply' _ _ _ _)
  | quote v => rw [predotU_nQuote, psubst_nQuote] at same; exact absurd same (not_nameLaws_par_apply' _ _ _ _)
  | guard _ => rw [predotU_pFor, psubst_pFor] at same; exact absurd same (not_nameLaws_par_apply' _ _ _ _)
  | reflect _ _ => rw [predotU_pReflect, psubst_pReflect] at same; exact absurd same (not_nameLaws_par_apply' _ _ _ _)
  | @par a b hA hB => exact ⟨a, b, rfl, hA, hB⟩

theorem hostedNode_match_zero {P : Pattern} {σ : PSubst} (h : HostedNode P)
    (same : NameLaws pZero (psubst σ (predotU P))) : P = pZero := by
  cases h with
  | zero => rfl
  | quote v =>
      rw [predotU_nQuote, psubst_nQuote] at same
      exact absurd same (not_nameLaws_apply_diff' (by decide) _ _)
  | par _ _ =>
      rw [predotU_par, psubst_par] at same
      exact absurd same.symm (not_nameLaws_par_apply' _ _ _ _)
  | guard _ =>
      rw [predotU_pFor, psubst_pFor] at same
      exact absurd same (not_nameLaws_apply_diff' (by decide) _ _)
  | reflect _ _ =>
      rw [predotU_pReflect, psubst_pReflect] at same
      exact absurd same (not_nameLaws_apply_diff' (by decide) _ _)

theorem hostedNode_match_for {P t' ch' k' : Pattern} {σ : PSubst} (h : HostedNode P)
    (same : NameLaws (pFor t' ch' k') (psubst σ (predotU P))) :
    ∃ t ch A, P = pFor t ch A ∧ HostedChan ch := by
  cases h with
  | zero =>
      rw [predotU_pZero, psubst_pZero] at same
      exact absurd same (not_nameLaws_apply_diff' (by decide) _ _)
  | quote v =>
      rw [predotU_nQuote, psubst_nQuote] at same
      exact absurd same (not_nameLaws_apply_diff' (by decide) _ _)
  | par _ _ =>
      rw [predotU_par, psubst_par] at same
      exact absurd same.symm (not_nameLaws_par_apply' _ _ _ _)
  | @guard t ch A hCh => exact ⟨t, ch, A, rfl, hCh⟩
  | reflect _ _ =>
      rw [predotU_pReflect, psubst_pReflect] at same
      exact absurd same (not_nameLaws_apply_diff' (by decide) _ _)

theorem hostedNode_match_reflect {P x' q' : Pattern} {σ : PSubst} (h : HostedNode P)
    (same : NameLaws (pReflect x' q') (psubst σ (predotU P))) :
    ∃ x Q, P = pReflect x Q ∧ HostedChan x ∧ HostedNode Q := by
  cases h with
  | zero =>
      rw [predotU_pZero, psubst_pZero] at same
      exact absurd same (not_nameLaws_apply_diff' (by decide) _ _)
  | quote v =>
      rw [predotU_nQuote, psubst_nQuote] at same
      exact absurd same (not_nameLaws_apply_diff' (by decide) _ _)
  | par _ _ =>
      rw [predotU_par, psubst_par] at same
      exact absurd same.symm (not_nameLaws_par_apply' _ _ _ _)
  | guard _ =>
      rw [predotU_pFor, psubst_pFor] at same
      exact absurd same (not_nameLaws_apply_diff' (by decide) _ _)
  | @reflect x Q hX hQ => exact ⟨x, Q, rfl, hX, hQ⟩

/-! ## Root `heat` and `clear` reflection on `HostedNode` `RootCells` -/

section RootNodeUpdates

variable {O : Type*} [DecidableEq O]

theorem rootCells_heat_node_reflects {label : O → Pattern} {C : Configuration Pattern O}
    {rootRows : List (O × Pattern)} (inv : RootCells label C rootRows)
    (nodes : ∀ q ∈ rootRows, HostedNode q.2) {ρ : PSubst} {o m₁ m₂ : O}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (rootHeatAt ρ o m₁ m₂)) :
    ∃ rootRows',
      RootCells (res label C (rootHeatAt ρ o m₁ m₂)).label
        (resConf label C (rootHeatAt ρ o m₁ m₂)) rootRows' ∧
      (∀ q ∈ rootRows', HostedNode q.2) ∧
      BagEq (rootBagProcess rootRows') (rootBagProcess rootRows) ∧
      (∀ z, z ∈ rootRows'.map Prod.fst ↔
        (z ∈ rootRows.map Prod.fst ∧ z ≠ o) ∨ z = m₁ ∨ z = m₂) := by
  obtain ⟨_, -, enabled, ⟨_, w, solved⟩, -⟩ := (RuleSyntax.admits_iff _).mp admitted
  have oPres : o ∈ C.present := enabled.taken_subset
    (by simp [rootHeatAt, rootFiring, widen, atFiring, heatN, Selection.commit])
  have known := info_known _ solved
  obtain ⟨a', b', lEq, -, -⟩ := rootHeat_takes_pair label C ρ o m₁ m₂ solved
  have oIn : o ∈ rootRows.map Prod.fst := by
    by_contra notIn; refine inv.others o oPres notIn w known (par a' b') ?_
    rw [lEq]; exact NameLaws.refl _
  obtain ⟨⟨o₀, P⟩, qIn, eqO⟩ := List.mem_map.mp oIn
  have eqO' : o₀ = o := eqO; subst eqO'
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem qIn
  have permOld : ((pre ++ (o₀, P) :: post).map Prod.fst).Perm
      (o₀ :: (pre ++ post).map Prod.fst) := by
    simp only [List.map_append, List.map_cons]; exact List.perm_middle
  obtain ⟨oOut, -⟩ := List.nodup_cons.mp (permOld.nodup_iff.mp inv.nodup)
  have r := (inv.rows (o₀, P) (by simp)).2 w known
  dsimp only at r; rw [lEq, psubst_atLoc_any, psubst_rootLoc] at r
  obtain ⟨a, b, rfl, hA, hB⟩ := hostedNode_match_par (nodes (o₀, P) (by simp))
    ((locatedFrame_name.atLoc_iff _ _ _ _).mp r).1
  obtain ⟨inv', bagEq, -⟩ := rootCells_heat inv admitted
  let rows' := pre ++ (m₁, a) :: (m₂, b) :: post
  have permNew : (rows'.map Prod.fst).Perm (m₁ :: m₂ :: (pre ++ post).map Prod.fst) := by
    simp only [rows', List.map_append, List.map_cons]
    exact List.perm_middle.trans (List.Perm.cons _ List.perm_middle)
  refine ⟨rows', inv', fun q qM => ?_, bagEq, fun z => ?_⟩
  · simp only [rows', List.mem_append, List.mem_cons] at qM
    rcases qM with inPre | rfl | rfl | inPost
    · exact nodes q (List.mem_append_left _ inPre)
    · exact hA
    · exact hB
    · exact nodes q (List.mem_append_right _ (List.mem_cons_of_mem _ inPost))
  · constructor
    · intro zIn
      rcases List.mem_cons.mp (permNew.subset zIn) with rfl | hTail
      · exact .inr (.inl rfl)
      · rcases List.mem_cons.mp hTail with rfl | inR
        · exact .inr (.inr rfl)
        · exact .inl ⟨permOld.symm.subset (List.mem_cons_of_mem _ inR), fun e => oOut (e ▸ inR)⟩
    · rintro (⟨inAll, neO⟩ | rfl | rfl)
      · rcases List.mem_cons.mp (permOld.subset inAll) with rfl | inR
        · exact absurd rfl neO
        · exact permNew.symm.subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ inR))
      · exact permNew.symm.subset (List.mem_cons_self ..)
      · exact permNew.symm.subset (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem rootCells_clear_node_reflects {label : O → Pattern} {C : Configuration Pattern O}
    {rootRows : List (O × Pattern)} (inv : RootCells label C rootRows)
    (nodes : ∀ q ∈ rootRows, HostedNode q.2) {ρ : PSubst} {o : O}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) (rootClearAt ρ o)) :
    ∃ rootRows',
      RootCells (res label C (rootClearAt ρ o)).label
        (resConf label C (rootClearAt ρ o)) rootRows' ∧
      (∀ q ∈ rootRows', HostedNode q.2) ∧
      BagEq (rootBagProcess rootRows') (rootBagProcess rootRows) ∧
      (∀ z, z ∈ rootRows'.map Prod.fst ↔ z ∈ rootRows.map Prod.fst ∧ z ≠ o) := by
  obtain ⟨_, -, enabled, ⟨_, w, solved⟩, -⟩ := (RuleSyntax.admits_iff _).mp admitted
  have oPres : o ∈ C.present := enabled.taken_subset
    (by simp [rootClearAt, rootFiring, widen, atFiring, clearN, Selection.commit])
  have known := info_known _ solved
  have rTake := (rootClear_takes_zero label C ρ o solved).symm
  have oIn : o ∈ rootRows.map Prod.fst := by
    by_contra notIn; exact inv.others o oPres notIn w known pZero rTake.symm
  obtain ⟨⟨o₀, P⟩, qIn, eqO⟩ := List.mem_map.mp oIn
  have eqO' : o₀ = o := eqO; subst eqO'
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem qIn
  have permOld : ((pre ++ (o₀, P) :: post).map Prod.fst).Perm
      (o₀ :: (pre ++ post).map Prod.fst) := by
    simp only [List.map_append, List.map_cons]; exact List.perm_middle
  obtain ⟨oOut, -⟩ := List.nodup_cons.mp (permOld.nodup_iff.mp inv.nodup)
  have r := (inv.rows (o₀, P) (by simp)).2 w known
  dsimp only at r; rw [psubst_atLoc_any, psubst_rootLoc] at r
  have pEq := hostedNode_match_zero (nodes (o₀, P) (by simp))
    ((locatedFrame_name.atLoc_iff _ _ _ _).mp (rTake.trans r)).1
  subst pEq
  obtain ⟨inv', bagEq, -⟩ := rootCells_clear inv admitted
  refine ⟨pre ++ post, inv', fun q qM => ?_, bagEq, fun z => ?_⟩
  · exact (List.mem_append.mp qM).elim (fun l => nodes q (List.mem_append_left _ l))
      (fun r => nodes q (List.mem_append_right _ (List.mem_cons_of_mem _ r)))
  · constructor
    · intro zIn; exact ⟨permOld.symm.subset (List.mem_cons_of_mem _ zIn), fun e => oOut (e ▸ zIn)⟩
    · rintro ⟨inAll, neO⟩
      rcases List.mem_cons.mp (permOld.subset inAll) with rfl | inR
      · exact absurd rfl neO
      · exact inR

end RootNodeUpdates

/-! ## Canonical firing normal forms for open and close rules -/

section NormalForms

variable {O : Type*} [DecidableEq O] {label : O → Pattern} {C : Configuration Pattern O}

theorem eq_openRootAt {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (ruleEq : g.rule = openRoot) :
    ∃ r pr tk : O, g = openRootAt g.opening r pr tk := by
  obtain ⟨_, shapes, -⟩ := (RuleSyntax.admits_iff g).mp admitted
  obtain ⟨_, _, lenT, lenR, lenM, lenC⟩ := shapes
  rw [ruleEq] at lenT lenR lenM lenC
  simp only [openRoot, List.length_cons, List.length_nil] at lenT lenR lenM lenC
  match hm : g.selection, hs : g.seen with
  | ⟨[], [r], [pr, tk]⟩, [] =>
      refine ⟨r, pr, tk, ?_⟩
      cases g with | mk rl mb ex op sel sn =>
        cases ex; simp only at ruleEq hm hs; subst ruleEq hm hs; rfl
  | ⟨_ :: _, _, _⟩, _ => simp [hm] at lenT
  | ⟨[], [], _⟩, _ => simp [hm] at lenR
  | ⟨[], _ :: _ :: _, _⟩, _ => simp [hm] at lenR
  | ⟨[], [_], []⟩, _ => simp [hm] at lenM
  | ⟨[], [_], [_]⟩, _ => simp [hm] at lenM
  | ⟨[], [_], _ :: _ :: _ :: _⟩, _ => simp [hm] at lenM
  | ⟨[], [_], [_, _]⟩, _ :: _ => simp [hs] at lenC

theorem eq_closeRootAt {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (ruleEq : g.rule = closeRoot) :
    ∃ r d made : O, g = closeRootAt g.opening r d made := by
  obtain ⟨_, shapes, -⟩ := (RuleSyntax.admits_iff g).mp admitted
  obtain ⟨_, _, lenT, lenR, lenM, lenC⟩ := shapes
  rw [ruleEq] at lenT lenR lenM lenC
  simp only [closeRoot, List.length_cons, List.length_nil] at lenT lenR lenM lenC
  match hm : g.selection, hs : g.seen with
  | ⟨[r, d], [], [made]⟩, [] =>
      refine ⟨r, d, made, ?_⟩
      cases g with | mk rl mb ex op sel sn =>
        cases ex; simp only at ruleEq hm hs; subst ruleEq hm hs; rfl
  | ⟨[], _, _⟩, _ => simp [hm] at lenT
  | ⟨[_], _, _⟩, _ => simp [hm] at lenT
  | ⟨_ :: _ :: _ :: _, _, _⟩, _ => simp [hm] at lenT
  | ⟨[_, _], _ :: _, _⟩, _ => simp [hm] at lenR
  | ⟨[_, _], [], []⟩, _ => simp [hm] at lenM
  | ⟨[_, _], [], _ :: _ :: _⟩, _ => simp [hm] at lenM
  | ⟨[_, _], [], [_]⟩, _ :: _ => simp [hs] at lenC

theorem eq_openChildAt {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (ruleEq : g.rule = openChild) :
    ∃ r tk pr_g tk_g : O, g = openChildAt g.opening r tk pr_g tk_g := by
  obtain ⟨_, shapes, -⟩ := (RuleSyntax.admits_iff g).mp admitted
  obtain ⟨_, _, lenT, lenR, lenM, lenC⟩ := shapes
  rw [ruleEq] at lenT lenR lenM lenC
  simp only [openChild, List.length_cons, List.length_nil] at lenT lenR lenM lenC
  match hm : g.selection, hs : g.seen with
  | ⟨[], [r, tk], [pr_g, tk_g]⟩, [] =>
      refine ⟨r, tk, pr_g, tk_g, ?_⟩
      cases g with | mk rl mb ex op sel sn =>
        cases ex; simp only at ruleEq hm hs; subst ruleEq hm hs; rfl
  | ⟨_ :: _, _, _⟩, _ => simp [hm] at lenT
  | ⟨[], [], _⟩, _ => simp [hm] at lenR
  | ⟨[], [_], _⟩, _ => simp [hm] at lenR
  | ⟨[], _ :: _ :: _ :: _, _⟩, _ => simp [hm] at lenR
  | ⟨[], [_, _], []⟩, _ => simp [hm] at lenM
  | ⟨[], [_, _], [_]⟩, _ => simp [hm] at lenM
  | ⟨[], [_, _], _ :: _ :: _ :: _⟩, _ => simp [hm] at lenM
  | ⟨[], [_, _], [_, _]⟩, _ :: _ => simp [hs] at lenC

theorem eq_closeChildAt {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (ruleEq : g.rule = closeChild) :
    ∃ r d_in tk madeL madeTok : O, g = closeChildAt g.opening r d_in tk madeL madeTok := by
  obtain ⟨_, shapes, -⟩ := (RuleSyntax.admits_iff g).mp admitted
  obtain ⟨_, _, lenT, lenR, lenM, lenC⟩ := shapes
  rw [ruleEq] at lenT lenR lenM lenC
  simp only [closeChild, List.length_cons, List.length_nil] at lenT lenR lenM lenC
  match hm : g.selection, hs : g.seen with
  | ⟨[r, d_in, tk], [], [madeL, madeTok]⟩, [] =>
      refine ⟨r, d_in, tk, madeL, madeTok, ?_⟩
      cases g with | mk rl mb ex op sel sn =>
        cases ex; simp only at ruleEq hm hs; subst ruleEq hm hs; rfl
  | ⟨[], _, _⟩, _ => simp [hm] at lenT
  | ⟨[_], _, _⟩, _ => simp [hm] at lenT
  | ⟨[_, _], _, _⟩, _ => simp [hm] at lenT
  | ⟨_ :: _ :: _ :: _ :: _, _, _⟩, _ => simp [hm] at lenT
  | ⟨[_, _, _], _ :: _, _⟩, _ => simp [hm] at lenR
  | ⟨[_, _, _], [], []⟩, _ => simp [hm] at lenM
  | ⟨[_, _, _], [], [_]⟩, _ => simp [hm] at lenM
  | ⟨[_, _, _], [], _ :: _ :: _ :: _⟩, _ => simp [hm] at lenM
  | ⟨[_, _, _], [], [_, _]⟩, _ :: _ => simp [hs] at lenC

end NormalForms

/-! ## `CellsU` and `DoneCellsU` non-interference, heating, and cooling -/

section ChildUpdates

variable {O : Type*} [DecidableEq O]

/-- Any admitted firing `g` that neither steps nor heats `l = childLoc m x p` leaves `CellsU`
completely unchanged. -/
theorem cellsU_keep_other {m x p : Pattern} {label : O → Pattern} {C : Configuration Pattern O}
    {tk : O} {cells : List (O × Pattern)}
    (inv : CellsU (childLoc m x p) m label C tk cells)
    (g : Firing O QNE located PUnit.unit)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (notStep : ¬ StepAtS (childLoc m x p) label C g)
    (notHeat : ¬ HeatAtS (childLoc m x p) label C g) :
    CellsU (childLoc m x p) m (res label C g).label (resConf label C g) tk cells ∧
      ∀ o ∈ C.present, o ∈ g.selection.taken → o ≠ tk ∧ o ∉ cells.map Prod.fst := by
  have phase := inv.phase
  have nextPhase : PendingPhaseS (childLoc m x p) m (res label C g).label (resConf label C g) tk := by
    rcases pending_phase_step_S phase g admitted with ⟨-, pNext⟩ | ⟨st, -⟩
    · exact pNext
    · exact absurd st notStep
  have tkNotTaken : tk ∉ g.selection.taken := token_kept_first_S phase admitted notStep
  have cellNotTaken : ∀ q ∈ cells, q.1 ∉ g.selection.taken := by
    intro q qIn taken
    obtain ⟨_, shapes, -⟩ := (RuleSyntax.admits_iff g).mp admitted
    obtain ⟨t, zipped⟩ := exists_mem_zip_right shapes.2.2.1 taken
    obtain ⟨σ₀, solved₀⟩ := solution_of_admitted admitted
    have known₀ := info_known g solved₀
    have both := (take_reads g solved₀ zipped).trans ((inv.rows q qIn).2.2 σ₀ known₀)
    have tMem := (List.of_mem_zip zipped).1
    rcases located_cases g.member with rC | rH | rCl | cC | cH | cCl | clR | clC | opR | opC
    · rw [rC] at tMem; simp only [atRule, RuleInstance.map, commRule, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at tMem
      rcases tMem with rfl | rfl <;>
        { simp only [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at both
          exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2.symm }
    · rw [rH] at tMem; simp only [atRule, RuleInstance.map, heatRule, List.map_cons, List.map_nil,
        List.mem_singleton] at tMem; subst tMem
      simp only [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at both
      exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2.symm
    · rw [rCl] at tMem; simp only [atRule, RuleInstance.map, clearRule, List.map_cons, List.map_nil,
        List.mem_singleton] at tMem; subst tMem
      simp only [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at both
      exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2.symm
    · rw [cC] at tMem; simp only [commChild, List.mem_cons, List.not_mem_nil, or_false] at tMem
      rcases tMem with rfl | rfl | rfl
      · simp only [psubst_atLoc_any] at both
        exact notStep ⟨.inl cC, σ₀, solved₀, ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2⟩
      · simp only [psubst_atLoc_any] at both
        exact notStep ⟨.inl cC, σ₀, solved₀, ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2⟩
      · simp only [psubst_atLoc_any] at both; exact absurd (head_of_reading₂ both) (by decide)
    · rw [cH] at tMem; simp only [heatChild, List.mem_singleton] at tMem; subst tMem
      simp only [psubst_atLoc_any] at both
      exact notHeat ⟨cH, σ₀, solved₀, ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2⟩
    · rw [cCl] at tMem; simp only [cool, List.mem_cons, List.not_mem_nil, or_false] at tMem
      rcases tMem with rfl | rfl
      · simp only [psubst_atLoc_any] at both; exact absurd (head_of_reading₂ both) (by decide)
      · simp only [psubst_atLoc_any] at both
        have loc := ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2
        obtain ⟨o₁, z₁, p₁⟩ := taken_row admitted (t := doneTok locL locM accC) (by rw [cCl]; simp [cool])
        have r₁ := take_reads g solved₀ z₁; rw [psubst_doneTok, psubst_doneTok] at r₁
        exact phase.noDone o₁ p₁ ⟨σ₀, known₀, _, _,
          r₁.symm.trans (nameLaws_doneTok_iff.mpr ⟨loc, NameLaws.refl _, NameLaws.refl _⟩)⟩
    · rw [clR] at tMem; simp only [closeRoot, List.mem_cons, List.not_mem_nil, or_false] at tMem
      rcases tMem with rfl | rfl
      · simp only [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at both
        exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2.symm
      · simp only [psubst_atLoc_any] at both; exact absurd (head_of_reading₂ both) (by decide)
    · rw [clC] at tMem; simp only [closeChild, List.mem_cons, List.not_mem_nil, or_false] at tMem
      rcases tMem with rfl | rfl | rfl
      · simp only [psubst_atLoc_any] at both
        exact notStep ⟨.inr clC, σ₀, solved₀, ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2⟩
      · simp only [psubst_atLoc_any] at both; exact absurd (head_of_reading₂ both) (by decide)
      · simp only [psubst_atLoc_any] at both; exact absurd (head_of_reading₂ both) (by decide)
    · rw [opR] at tMem; simp [openRoot] at tMem
    · rw [opC] at tMem; simp [openChild] at tMem
  refine ⟨⟨nextPhase, inv.nodup, fun q qIn => ?_, fun o oPres oTk oNotCell σ solved y same => ?_⟩,
    fun o _ taken => ⟨fun e => tkNotTaken (e ▸ taken), fun inC => by
      obtain ⟨q, qIn, rfl⟩ := List.mem_map.mp inC; exact cellNotTaken q qIn taken⟩⟩
  · obtain ⟨qPres, qTk, qReads⟩ := inv.rows q qIn
    refine ⟨(result_present g q.1).mpr (.inl ⟨qPres, cellNotTaken q qIn⟩), qTk, fun σ solved => ?_⟩
    rw [result_label_old g (fun m' => made_not_present admitted m' qPres)]
    exact qReads σ (info_known g solved)
  · have known := info_known g solved
    rcases result_row oPres with made | ⟨old, -, -, labelOld⟩
    · obtain ⟨t, inside, labelEq⟩ := made_label admitted made
      rw [labelEq] at same
      rcases located_cases g.member with rC | rH | rCl | cC | cH | cCl | clR | clC | opR | opC
      · rw [rC] at inside; simp only [atRule, RuleInstance.map, commRule, List.map_cons, List.map_nil,
          List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl <;>
          { rw [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at same
            exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2.symm }
      · rw [rH] at inside; simp only [atRule, RuleInstance.map, heatRule, List.map_cons, List.map_nil,
          List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl <;>
          { rw [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at same
            exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2.symm }
      · rw [rCl] at inside; simp [atRule, RuleInstance.map, clearRule] at inside
      · rw [cC] at inside; simp only [commChild, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl
        · rw [psubst_atLoc_any] at same
          exact notStep ⟨.inl cC, σ, solved, ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2⟩
        · rw [psubst_atLoc_any] at same
          exact notStep ⟨.inl cC, σ, solved, ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2⟩
        · exact absurd (head_of_reading₂ same) (by decide)
      · rw [cH] at inside; simp only [heatChild, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl <;>
          { rw [psubst_atLoc_any] at same
            exact notHeat ⟨cH, σ, solved, ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2⟩ }
      · rw [cCl] at inside; simp only [cool, List.mem_singleton] at inside; subst inside
        exact absurd (head_of_reading₂ same) (by decide)
      · rw [clR] at inside; simp only [closeRoot, List.mem_singleton] at inside; subst inside
        rw [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at same
        exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2.symm
      · rw [clC] at inside; simp only [closeChild, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl
        · rw [psubst_atLoc_any] at same
          exact notStep ⟨.inr clC, σ, solved, ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2⟩
        · exact absurd (head_of_reading₂ same) (by decide)
      · rw [opR] at inside; simp only [openRoot, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl
        · rw [psubst_atLoc_any, psubst_childLoc] at same
          have qRead := phase.reads σ known; rw [psubst_pendingTok, psubst_childLoc] at qRead
          exact check_fails_pending admitted (by rw [opR]; exact openRoot_checks.1)
            solved ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2 phase.present qRead
        · exact absurd (head_of_reading₂ same) (by decide)
      · rw [opC] at inside; simp only [openChild, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl
        · rw [psubst_atLoc_any, psubst_childLoc] at same
          have qRead := phase.reads σ known; rw [psubst_pendingTok, psubst_childLoc] at qRead
          exact check_fails_pending admitted (by rw [opC]; exact openChild_checks.1)
            solved ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2 phase.present qRead
        · exact absurd (head_of_reading₂ same) (by decide)
    · rw [labelOld] at same; exact inv.others o old oTk oNotCell σ known y same

/-- Backward reflection of `heatChildN` on `HostedNode` `CellsU`. -/
theorem cellsU_heat_reflects {m x p : Pattern} {label : O → Pattern} {C : Configuration Pattern O}
    {tk o m₁ m₂ : O} {ρ : PSubst} {cells : List (O × Pattern)}
    (inv : CellsU (childLoc m x p) m label C tk cells)
    (nodes : ∀ q ∈ cells, HostedNode q.2)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (heatChildN ρ o tk m₁ m₂)) :
    ∃ cells' : List (O × Pattern),
      CellsU (childLoc m x p) m (res label C (heatChildN ρ o tk m₁ m₂)).label
        (resConf label C (heatChildN ρ o tk m₁ m₂)) tk cells' ∧
      (∀ q ∈ cells', HostedNode q.2) ∧
      BagEq (pPar (cells'.map Prod.snd)) (pPar (cells.map Prod.snd)) ∧
      (∀ z, z ∈ cells'.map Prod.fst ↔ (z ∈ cells.map Prod.fst ∧ z ≠ o) ∨ z = m₁ ∨ z = m₂) := by
  let l := childLoc m x p
  obtain ⟨_, shapes, enabled, ⟨_, w, solved⟩, -⟩ := (RuleSyntax.admits_iff _).mp admitted
  have known := info_known _ solved
  have oPres : o ∈ C.present := enabled.taken_subset (by simp [heatChildN, Selection.commit])
  have mDist : m₁ ≠ m₂ := by simpa [heatChildN] using shapes.2.1
  have freshM : m₁ ∉ C.present ∧ m₂ ∉ C.present := by
    simpa [heatChildN, Selection.commit, embed] using enabled.fresh
  obtain ⟨a', b', l', oSame, -, -, locL_eq, -⟩ := heatChild_takes_pair label C ρ o tk m₁ m₂ solved
  have oNeTk : o ≠ tk := fun e => by
    have rTkO := inv.phase.reads w known
    rw [← e, oSame, psubst_pendingTok] at rTkO
    exact not_nameLaws_apply_diff' (by decide) _ _ rTkO
  have zTk : (pendingTok locL locM, tk) ∈
      (heatChildN ρ o tk m₁ m₂).rule.body.read.zip (heatChildN ρ o tk m₁ m₂).selection.read := by
    simp [heatChildN, heatChild]
  have rTk := (read_reads _ solved zTk).trans (inv.phase.reads w known)
  rw [psubst_pendingTok, psubst_pendingTok] at rTk
  have l'_eq_l : NameLaws l' (psubst w l) := locL_eq.symm.trans (nameLaws_pendingTok_iff.mp rTk).1
  have oIn : o ∈ cells.map Prod.fst := by
    by_contra notIn
    exact inv.others o oPres oNeTk notIn w known (par a' b')
      (by rw [oSame]; exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨NameLaws.refl _, l'_eq_l⟩)
  obtain ⟨⟨o₀, P⟩, qIn, eqO⟩ := List.mem_map.mp oIn
  have eqO' : o₀ = o := eqO; subst eqO'
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem qIn
  have rO := (inv.rows (o₀, P) (by simp)).2.2 w known
  rw [oSame, psubst_atLoc_any] at rO
  have bodyEq := ((locatedFrame_name.atLoc_iff _ _ _ _).mp
    (((locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨NameLaws.refl _, l'_eq_l.symm⟩).trans rO)).1
  obtain ⟨a, b, rfl, hA, hB⟩ := hostedNode_match_par (nodes (o₀, P) (by simp)) bodyEq
  have oReads : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label o₀)) (psubst σ (atLoc (par (predotU a) (predotU b)) l)) := by
    intro σ s; have r := (inv.rows (o₀, par a b) (by simp)).2.2 σ s; rwa [predotU_par] at r
  have notStep : ¬ StepAtS l label C (heatChildN ρ o₀ tk m₁ m₂) := by
    rintro ⟨rEq, -⟩; rcases rEq with h | h <;>
      { have c := congrArg (fun r => r.body.take.length) h; simp [heatChildN, heatChild, commChild, closeChild] at c }
  have nextPhase : PendingPhaseS l m (res label C (heatChildN ρ o₀ tk m₁ m₂)).label
      (resConf label C (heatChildN ρ o₀ tk m₁ m₂)) tk := by
    rcases pending_phase_step_S inv.phase _ admitted with ⟨-, pNext⟩ | ⟨st, -⟩
    · exact pNext
    · exact absurd st notStep
  have permOld : ((pre ++ (o₀, par a b) :: post).map Prod.fst).Perm
      (o₀ :: (pre ++ post).map Prod.fst) := by
    simp only [List.map_append, List.map_cons]; exact List.perm_middle
  obtain ⟨oOut, ndRest⟩ := List.nodup_cons.mp (permOld.nodup_iff.mp inv.nodup)
  have restIn : ∀ q ∈ pre ++ post, q ∈ pre ++ (o₀, par a b) :: post := fun q m' =>
    (List.mem_append.mp m').elim (List.mem_append_left _)
      (fun r => List.mem_append_right _ (List.mem_cons_of_mem _ r))
  let cells' := pre ++ (m₁, a) :: (m₂, b) :: post
  have permNew : (cells'.map Prod.fst).Perm (m₁ :: m₂ :: (pre ++ post).map Prod.fst) := by
    simp only [cells', List.map_append, List.map_cons]; exact List.perm_middle.trans (List.Perm.cons _ List.perm_middle)
  have ndNew : (cells'.map Prod.fst).Nodup := by
    refine permNew.nodup_iff.mpr (List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, ndRest⟩⟩)
    · simp only [List.mem_cons]; rintro (rfl | inR)
      · exact mDist rfl
      · obtain ⟨q, qM, eqM⟩ := List.mem_map.mp inR
        exact freshM.1 (eqM ▸ (inv.rows q (restIn q qM)).1)
    · intro inR; obtain ⟨q, qM, eqM⟩ := List.mem_map.mp inR
      exact freshM.2 (eqM ▸ (inv.rows q (restIn q qM)).1)
  have tkNe₁ : tk ≠ m₁ := fun e => freshM.1 (e ▸ inv.phase.present)
  have tkNe₂ : tk ≠ m₂ := fun e => freshM.2 (e ▸ inv.phase.present)
  refine ⟨cells', ⟨nextPhase, ndNew, fun q qM => ?_, fun z zP zNeTk zNotNew σ s y same => ?_⟩,
    fun q qM => ?_, ?_, fun z => ?_⟩
  · simp only [cells', List.mem_append, List.mem_cons] at qM
    rcases qM with inPre | rfl | rfl | inPost
    · have qOld := restIn q (List.mem_append_left _ inPre)
      obtain ⟨qP, qTk, qR⟩ := inv.rows q qOld
      have neO : q.1 ≠ o₀ := fun e => oOut (e ▸ List.mem_map.mpr ⟨q, List.mem_append_left _ inPre, rfl⟩)
      have ne₁ : q.1 ≠ m₁ := fun e => freshM.1 (e ▸ qP)
      have ne₂ : q.1 ≠ m₂ := fun e => freshM.2 (e ▸ qP)
      exact ⟨(result_present _ q.1).mpr (.inl ⟨qP, by simp [heatChildN, neO]⟩), qTk, fun σ s => by
        rw [result_label_old _ (by simp [heatChildN, ne₁, ne₂])]; exact qR σ (info_known _ s)⟩
    · exact ⟨(result_present _ m₁).mpr (.inr (by simp [heatChildN])), tkNe₁.symm, fun σ s =>
        (heatChild_reads_determinately label C ρ o₀ tk mDist (predotU a) (predotU b) l oReads s).1⟩
    · exact ⟨(result_present _ m₂).mpr (.inr (by simp [heatChildN])), tkNe₂.symm, fun σ s =>
        (heatChild_reads_determinately label C ρ o₀ tk mDist (predotU a) (predotU b) l oReads s).2⟩
    · have qOld := restIn q (List.mem_append_right _ inPost)
      obtain ⟨qP, qTk, qR⟩ := inv.rows q qOld
      have neO : q.1 ≠ o₀ := fun e => oOut (e ▸ List.mem_map.mpr ⟨q, List.mem_append_right _ inPost, rfl⟩)
      have ne₁ : q.1 ≠ m₁ := fun e => freshM.1 (e ▸ qP)
      have ne₂ : q.1 ≠ m₂ := fun e => freshM.2 (e ▸ qP)
      exact ⟨(result_present _ q.1).mpr (.inl ⟨qP, by simp [heatChildN, neO]⟩), qTk, fun σ s => by
        rw [result_label_old _ (by simp [heatChildN, ne₁, ne₂])]; exact qR σ (info_known _ s)⟩
  · rcases result_row zP with made | ⟨old, notTaken, -, lblOld⟩
    · simp only [heatChildN, List.mem_cons, List.not_mem_nil, or_false] at made
      rcases made with rfl | rfl <;> exact zNotNew (by simp [cells'])
    · rw [lblOld] at same
      have neO : z ≠ o₀ := fun e => notTaken (by simp [heatChildN, e])
      refine inv.others z old zNeTk (fun inAll => ?_) σ (info_known _ s) y same
      rcases List.mem_cons.mp (permOld.subset inAll) with rfl | inRest
      · exact neO rfl
      · obtain ⟨q, qM, rfl⟩ := List.mem_map.mp inRest
        apply zNotNew; simp only [cells', List.map_append, List.map_cons, List.mem_append, List.mem_cons]
        exact (List.mem_append.mp qM).elim
          (fun l => .inl (List.mem_map.mpr ⟨q, l, rfl⟩))
          (fun r => .inr (.inr (.inr (List.mem_map.mpr ⟨q, r, rfl⟩))))
  · simp only [cells', List.mem_append, List.mem_cons] at qM
    rcases qM with inPre | rfl | rfl | inPost
    · exact nodes q (List.mem_append_left _ inPre)
    · exact hA
    · exact hB
    · exact nodes q (List.mem_append_right _ (List.mem_cons_of_mem _ inPost))
  · simpa [cells', List.map_append] using bagEq_pPar_heat (pre.map Prod.snd) (post.map Prod.snd) a b
  · constructor
    · intro zIn
      rcases List.mem_cons.mp (permNew.subset zIn) with rfl | hTail
      · exact .inr (.inl rfl)
      · rcases List.mem_cons.mp hTail with rfl | inR
        · exact .inr (.inr rfl)
        · exact .inl ⟨permOld.symm.subset (List.mem_cons_of_mem _ inR), fun e => oOut (e ▸ inR)⟩
    · rintro (⟨inAll, neO⟩ | rfl | rfl)
      · rcases List.mem_cons.mp (permOld.subset inAll) with rfl | inR
        · exact absurd rfl neO
        · exact permNew.symm.subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ inR))
      · exact permNew.symm.subset (List.mem_cons_self ..)
      · exact permNew.symm.subset (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- Backward reflection of `coolAt` / non-close firings on `DoneCellsU`, maintaining ground
`BagLaws (cooled acc (cells.map (predotU ∘ Prod.snd))) (predotU reduct)`. -/
theorem doneCellsU_step_or_keep {m x p : Pattern} {label : O → Pattern}
    {C : Configuration Pattern O} {d : O} {acc reduct : Pattern} {cells : List (O × Pattern)}
    (inv : DoneCellsU (childLoc m x p) m label C d acc cells)
    (nodes : ∀ q ∈ cells, HostedNode q.2)
    (bagAcc : BagLaws (cooled acc (cells.map (fun q => predotU q.2))) (predotU reduct))
    (g : Firing O QNE located PUnit.unit)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (notClose : ¬ CloseAtS (childLoc m x p) label C g) :
    ∃ (d' : O) (acc' : Pattern) (cells' : List (O × Pattern)),
      DoneCellsU (childLoc m x p) m (res label C g).label (resConf label C g) d' acc' cells' ∧
      (∀ q ∈ cells', HostedNode q.2) ∧
      BagLaws (cooled acc' (cells'.map (fun q => predotU q.2))) (predotU reduct) ∧
      (¬ CoolAtS (childLoc m x p) label C g → d' = d ∧ acc' = acc ∧ cells' = cells) ∧
      (∀ z ∈ (resConf label C g).present,
        (z = d' ∨ z ∈ cells'.map Prod.fst) ↔
          (z ∈ g.selection.made ∧ CoolAtS (childLoc m x p) label C g) ∨
          (z ∈ C.present ∧ z ∉ g.selection.taken ∧ (z = d ∨ z ∈ cells.map Prod.fst))) := by
  let l := childLoc m x p
  obtain ⟨noStep, dNext, nextPhase⟩ := done_phase_step_S inv.phase g admitted notClose
  by_cases isCool : CoolAtS l label C g
  · obtain ⟨cRule, σ₀, solved₀, loc₀⟩ := isCool
    obtain ⟨r, d₁, gEq⟩ := eq_coolAt inv.phase admitted cRule solved₀ loc₀
    rw [gEq] at admitted solved₀ notClose noStep nextPhase ⊢
    obtain ⟨_, shapes, enabled, -⟩ := (RuleSyntax.admits_iff _).mp admitted
    have rPres : r ∈ C.present := enabled.taken_subset (by simp [coolAt, Selection.commit])
    have rNeD : r ≠ d := fun same => by have nd := shapes.1; simp [coolAt, same] at nd
    have d₁Fresh : d₁ ∉ C.present :=
      fun inC => Finset.disjoint_left.mp enabled.fresh (by simp [coolAt, Selection.commit]) inC
    have zR : (atLoc leftPart locL, r) ∈
        (coolAt g.opening d r d₁).rule.body.take.zip (coolAt g.opening d r d₁).selection.taken := by
      simp [coolAt, cool]
    have known₀ := info_known _ solved₀
    have rRead₀ := take_reads (coolAt g.opening d r d₁) solved₀ zR
    rw [psubst_atLoc_any] at rRead₀
    have rInCells : r ∈ cells.map Prod.fst := by
      by_contra notCell
      exact inv.others r rPres rNeD notCell σ₀ known₀ _
        (rRead₀.symm.trans ((locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨NameLaws.refl _, loc₀⟩))
    obtain ⟨⟨r₀, aNode⟩, qIn, eqR⟩ := List.mem_map.mp rInCells
    have eqR' : r₀ = r := eqR; subst eqR'
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem qIn
    have permOld : ((pre ++ (r₀, aNode) :: post).map Prod.fst).Perm
        (r₀ :: (pre ++ post).map Prod.fst) := by
      simp only [List.map_append, List.map_cons]; exact List.perm_middle
    obtain ⟨rOut, ndRest⟩ := List.nodup_cons.mp (permOld.nodup_iff.mp inv.nodup)
    have restIn : ∀ q ∈ pre ++ post, q ∈ pre ++ (r₀, aNode) :: post := fun q m' =>
      (List.mem_append.mp m').elim (List.mem_append_left _)
        (fun r => List.mem_append_right _ (List.mem_cons_of_mem _ r))
    have rNewTok : ∀ σ : PSubst,
        nameAction.Models σ (resConf label C (coolAt g.opening d r₀ d₁)).equations →
          NameLaws (psubst σ ((res label C (coolAt g.opening d r₀ d₁)).label d₁))
            (psubst σ (doneTok l m (par acc (predotU aNode)))) :=
      fun σ s => cool_reads label C g.opening d r₀ d₁ l m acc (predotU aNode) inv.readsTok
        (inv.rows (r₀, aNode) (by simp)).2.2 (σ := σ) s
    obtain ⟨σ₁, sol₁⟩ := solution_of_admitted admitted
    have d₁Eq : d₁ = dNext := nextPhase.unique d₁
      ((result_present _ d₁).mpr (.inr (by simp [coolAt])))
      ⟨σ₁, sol₁, _, _, by simpa [psubst_doneTok] using rNewTok σ₁ sol₁⟩
    subst d₁Eq
    have bagCool : BagLaws (cooled (par acc (predotU aNode)) ((pre ++ post).map (fun q => predotU q.2)))
        (cooled acc ((pre ++ (r₀, aNode) :: post).map (fun q => predotU q.2))) := by
      have b₁ := bagLaws_cooled (par acc (predotU aNode)) ((pre ++ post).map (fun q => predotU q.2))
      have b₂ := bagLaws_cooled acc ((pre ++ (r₀, aNode) :: post).map (fun q => predotU q.2))
      have flat : BagLaws (pPar (par acc (predotU aNode) :: (pre ++ post).map (fun q => predotU q.2)))
          (pPar (acc :: predotU aNode :: (pre ++ post).map (fun q => predotU q.2))) :=
        BagLaws.of_axiom (.flatten [] [acc, predotU aNode] _)
      have pm : (acc :: predotU aNode :: (pre ++ post).map (fun q => predotU q.2)).Perm
          (acc :: ((pre ++ (r₀, aNode) :: post).map (fun q => predotU q.2))) := by
        simp only [List.map_append, List.map_cons]
        exact List.Perm.cons _ List.perm_middle.symm
      exact b₁.trans (flat.trans ((BagLaws.of_axiom (.perm pm)).trans b₂.symm))
    refine ⟨d₁, par acc (predotU aNode), pre ++ post,
      ⟨nextPhase, rNewTok, ndRest, fun q qM => ?_, fun z zP zNeD₁ zNotRest σ s y same => ?_⟩,
      fun q qM => nodes q (restIn q qM), bagCool.trans bagAcc,
      fun nc => absurd ⟨rfl, σ₀, solved₀, loc₀⟩ nc, fun z zP => ?_⟩
    · have qOld := restIn q qM
      obtain ⟨qP, qNeD, qR⟩ := inv.rows q qOld
      have neR : q.1 ≠ r₀ := fun e => rOut (e ▸ List.mem_map.mpr ⟨q, qM, rfl⟩)
      have neD₁ : q.1 ≠ d₁ := fun e => d₁Fresh (e ▸ qP)
      exact ⟨(result_present _ q.1).mpr (.inl ⟨qP, by simp [coolAt, qNeD, neR]⟩), neD₁, fun σ s => by
        rw [result_label_old _ (by simp [coolAt, neD₁])]; exact qR σ (info_known _ s)⟩
    · rcases result_row zP with made | ⟨old, notTaken, -, lblOld⟩
      · simp only [coolAt, List.mem_singleton] at made; exact absurd made zNeD₁
      · rw [lblOld] at same
        have neD : z ≠ d := fun e => notTaken (by simp [coolAt, e])
        have neR : z ≠ r₀ := fun e => notTaken (by simp [coolAt, e])
        refine inv.others z old neD (fun inAll => ?_) σ (info_known _ s) y same
        rcases List.mem_cons.mp (permOld.subset inAll) with rfl | inR
        · exact neR rfl
        · exact zNotRest inR
    · constructor
      · rintro (rfl | inRest)
        · exact .inl ⟨by simp [coolAt], rfl, σ₀, solved₀, loc₀⟩
        · obtain ⟨q, qM, rfl⟩ := List.mem_map.mp inRest
          have qOld := restIn q qM
          obtain ⟨qP, qNeD, -⟩ := inv.rows q qOld
          have neR : q.1 ≠ r₀ := fun e => rOut (e ▸ List.mem_map.mpr ⟨q, qM, rfl⟩)
          exact .inr ⟨qP, by simp [coolAt, qNeD, neR], .inr (List.mem_map.mpr ⟨q, qOld, rfl⟩)⟩
      · rintro (⟨mMade, -⟩ | ⟨_, notT, rfl | inAll⟩)
        · simp only [coolAt, List.mem_singleton] at mMade; exact .inl mMade
        · exact absurd (by simp [coolAt]) notT
        · rcases List.mem_cons.mp (permOld.subset inAll) with rfl | inR
          · exact absurd (by simp [coolAt]) notT
          · exact .inr inR
  · have dNotTaken : d ∉ g.selection.taken := by
      intro taken
      obtain ⟨_, shapes, -⟩ := (RuleSyntax.admits_iff g).mp admitted
      obtain ⟨t, zipped⟩ := exists_mem_zip_right shapes.2.2.1 taken
      obtain ⟨σ₀, solved₀⟩ := solution_of_admitted admitted
      have known₀ := info_known g solved₀
      have both := (take_reads g solved₀ zipped).trans (inv.readsTok σ₀ known₀)
      have tMem := (List.of_mem_zip zipped).1
      rcases ReflLocatedStep.take_shapes g.member tMem with
        ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨isC, rfl⟩ | ⟨isCR, rfl⟩ | ⟨isCC, rfl⟩
      · rw [psubst_doneTok] at both; exact absurd (head_of_reading₂ both) (by decide)
      · rw [psubst_doneTok] at both; exact absurd (head_of_reading₂ both) (by decide)
      · rw [psubst_doneTok, psubst_doneTok] at both
        exact isCool ⟨isC, σ₀, solved₀, (nameLaws_doneTok_iff.mp both).1⟩
      · rw [psubst_doneTok, psubst_doneTok] at both
        exact notClose (.inl ⟨isCR, σ₀, solved₀, (nameLaws_doneTok_iff.mp both).1⟩)
      · rw [psubst_doneTok, psubst_doneTok] at both
        exact notClose (.inr ⟨isCC, σ₀, solved₀, (nameLaws_doneTok_iff.mp both).1⟩)
    obtain ⟨σ₁, sol₁⟩ := solution_of_admitted admitted
    have dEq : d = dNext := nextPhase.unique d
      ((result_present g d).mpr (.inl ⟨inv.phase.present, dNotTaken⟩))
      ⟨σ₁, sol₁, _, _, by
        rw [result_label_old g (fun m' => made_not_present admitted m' inv.phase.present)]
        simpa [psubst_doneTok] using inv.readsTok σ₁ (info_known g sol₁)⟩
    subst dEq
    have cellNotTaken : ∀ q ∈ cells, q.1 ∉ g.selection.taken := by
      intro q qIn taken
      obtain ⟨_, shapes, -⟩ := (RuleSyntax.admits_iff g).mp admitted
      obtain ⟨t, zipped⟩ := exists_mem_zip_right shapes.2.2.1 taken
      obtain ⟨σ₀, solved₀⟩ := solution_of_admitted admitted
      have known₀ := info_known g solved₀
      have both := (take_reads g solved₀ zipped).trans ((inv.rows q qIn).2.2 σ₀ known₀)
      have tMem := (List.of_mem_zip zipped).1
      rcases located_cases g.member with rC | rH | rCl | cC | cH | cCl | clR | clC | opR | opC
      · rw [rC] at tMem; simp only [atRule, RuleInstance.map, commRule, List.map_cons, List.map_nil,
          List.mem_cons, List.not_mem_nil, or_false] at tMem
        rcases tMem with rfl | rfl <;>
          { simp only [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at both
            exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2.symm }
      · rw [rH] at tMem; simp only [atRule, RuleInstance.map, heatRule, List.map_cons, List.map_nil,
          List.mem_singleton] at tMem; subst tMem
        simp only [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at both
        exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2.symm
      · rw [rCl] at tMem; simp only [atRule, RuleInstance.map, clearRule, List.map_cons, List.map_nil,
          List.mem_singleton] at tMem; subst tMem
        simp only [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at both
        exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2.symm
      · rw [cC] at tMem; simp only [commChild, List.mem_cons, List.not_mem_nil, or_false] at tMem
        rcases tMem with rfl | rfl | rfl
        · simp only [psubst_atLoc_any] at both
          exact noStep ⟨.inl cC, σ₀, solved₀, ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2⟩
        · simp only [psubst_atLoc_any] at both
          exact noStep ⟨.inl cC, σ₀, solved₀, ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2⟩
        · simp only [psubst_atLoc_any] at both; exact absurd (head_of_reading₂ both) (by decide)
      · rw [cH] at tMem; simp only [heatChild, List.mem_singleton] at tMem; subst tMem
        simp only [psubst_atLoc_any] at both
        obtain ⟨oP, zP⟩ := exists_mem_zip shapes.2.2.2.1 (x := pendingTok locL locM)
          (by rw [cH]; simp [heatChild])
        have pP : oP ∈ C.present :=
          ((RuleSyntax.admits_iff g).mp admitted).2.2.1.kept_subset
            (by simpa [Selection.commit] using (List.of_mem_zip zP).2)
        have rP := read_reads g solved₀ zP; rw [psubst_pendingTok, psubst_pendingTok] at rP
        exact inv.phase.noPend oP pP ⟨σ₀, known₀, _,
          rP.symm.trans (nameLaws_pendingTok_iff.mpr
            ⟨((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2, NameLaws.refl _⟩)⟩
      · rw [cCl] at tMem; simp only [cool, List.mem_cons, List.not_mem_nil, or_false] at tMem
        rcases tMem with rfl | rfl
        · simp only [psubst_atLoc_any] at both; exact absurd (head_of_reading₂ both) (by decide)
        · simp only [psubst_atLoc_any] at both
          exact isCool ⟨cCl, σ₀, solved₀, ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2⟩
      · rw [clR] at tMem; simp only [closeRoot, List.mem_cons, List.not_mem_nil, or_false] at tMem
        rcases tMem with rfl | rfl
        · simp only [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at both
          exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2.symm
        · simp only [psubst_atLoc_any] at both; exact absurd (head_of_reading₂ both) (by decide)
      · rw [clC] at tMem; simp only [closeChild, List.mem_cons, List.not_mem_nil, or_false] at tMem
        rcases tMem with rfl | rfl | rfl
        · simp only [psubst_atLoc_any] at both
          exact noStep ⟨.inr clC, σ₀, solved₀, ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2⟩
        · simp only [psubst_atLoc_any] at both; exact absurd (head_of_reading₂ both) (by decide)
        · simp only [psubst_atLoc_any] at both; exact absurd (head_of_reading₂ both) (by decide)
      · rw [opR] at tMem; simp [openRoot] at tMem
      · rw [opC] at tMem; simp [openChild] at tMem
    refine ⟨d, acc, cells, ⟨nextPhase, fun σ s => ?_, inv.nodup, fun q qM => ?_,
      fun z zP zNeD zNotC σ s y same => ?_⟩, nodes, bagAcc,
      fun _ => ⟨rfl, rfl, rfl⟩, fun z _ => ?_⟩
    · rw [result_label_old g (fun m' => made_not_present admitted m' inv.phase.present)]
      exact inv.readsTok σ (info_known g s)
    · obtain ⟨qP, qNeD, qR⟩ := inv.rows q qM
      exact ⟨(result_present g q.1).mpr (.inl ⟨qP, cellNotTaken q qM⟩), qNeD, fun σ s => by
        rw [result_label_old g (fun m' => made_not_present admitted m' qP)]
        exact qR σ (info_known g s)⟩
    · have known := info_known g s
      rcases result_row zP with made | ⟨old, -, -, lblOld⟩
      · obtain ⟨t, inside, lblEq⟩ := made_label admitted made
        rw [lblEq] at same
        rcases located_cases g.member with rC | rH | rCl | cC | cH | cCl | clR | clC | opR | opC
        · rw [rC] at inside; simp only [atRule, RuleInstance.map, commRule, List.map_cons, List.map_nil,
            List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl <;>
            { rw [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at same
              exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2.symm }
        · rw [rH] at inside; simp only [atRule, RuleInstance.map, heatRule, List.map_cons, List.map_nil,
            List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl <;>
            { rw [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at same
              exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2.symm }
        · rw [rCl] at inside; simp [atRule, RuleInstance.map, clearRule] at inside
        · rw [cC] at inside; simp only [commChild, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl | rfl
          · rw [psubst_atLoc_any] at same
            exact noStep ⟨.inl cC, σ, s, ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2⟩
          · rw [psubst_atLoc_any] at same
            exact noStep ⟨.inl cC, σ, s, ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2⟩
          · exact absurd (head_of_reading₂ same) (by decide)
        · rw [cH] at inside; simp only [heatChild, List.mem_cons, List.not_mem_nil, or_false] at inside
          obtain ⟨_, shapes, enabled, -⟩ := (RuleSyntax.admits_iff g).mp admitted
          obtain ⟨oP, zP⟩ := exists_mem_zip shapes.2.2.2.1 (x := pendingTok locL locM)
            (by rw [cH]; simp [heatChild])
          have pP : oP ∈ C.present := enabled.kept_subset (by simpa [Selection.commit] using (List.of_mem_zip zP).2)
          have rP := read_reads g s zP; rw [psubst_pendingTok, psubst_pendingTok] at rP
          rcases inside with rfl | rfl <;>
            { rw [psubst_atLoc_any] at same
              exact inv.phase.noPend oP pP ⟨σ, known, _,
                rP.symm.trans (nameLaws_pendingTok_iff.mpr
                  ⟨((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2, NameLaws.refl _⟩)⟩ }
        · rw [cCl] at inside; simp only [cool, List.mem_singleton] at inside; subst inside
          exact absurd (head_of_reading₂ same) (by decide)
        · rw [clR] at inside; simp only [closeRoot, List.mem_singleton] at inside; subst inside
          rw [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at same
          exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2.symm
        · rw [clC] at inside; simp only [closeChild, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl
          · rw [psubst_atLoc_any] at same
            exact noStep ⟨.inr clC, σ, s, ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2⟩
          · exact absurd (head_of_reading₂ same) (by decide)
        · rw [opR] at inside; simp only [openRoot, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl
          · rw [psubst_atLoc_any, psubst_childLoc] at same
            obtain ⟨c₀, tokR⟩ := inv.phase.reads σ known; rw [psubst_childLoc] at tokR
            exact check_fails_done admitted (by rw [opR]; exact openRoot_checks.2) (by rw [opR]; rfl)
              (by rw [opR]; rfl) (by rw [opR]; decide) (by decide) s
              ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2 inv.phase.present tokR
          · exact absurd (head_of_reading₂ same) (by decide)
        · rw [opC] at inside; simp only [openChild, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl
          · rw [psubst_atLoc_any, psubst_childLoc] at same
            obtain ⟨c₀, tokR⟩ := inv.phase.reads σ known; rw [psubst_childLoc] at tokR
            exact check_fails_done admitted (by rw [opC]; exact openChild_checks.2) (by rw [opC]; rfl)
              (by rw [opC]; rfl) (by rw [opC]; decide) (by decide) s
              ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2 inv.phase.present tokR
          · exact absurd (head_of_reading₂ same) (by decide)
      · rw [lblOld] at same; exact inv.others z old zNeD zNotC σ known y same
    · constructor
      · intro hZ
        rcases hZ with rfl | inC
        · exact .inr ⟨inv.phase.present, dNotTaken, .inl rfl⟩
        · obtain ⟨q, qM, rfl⟩ := List.mem_map.mp inC
          exact .inr ⟨(inv.rows q qM).1, cellNotTaken q qM, .inr (List.mem_map.mpr ⟨q, qM, rfl⟩)⟩
      · rintro (⟨_, cH⟩ | ⟨_, _, hZ⟩)
        · exact absurd cH isCool
        · exact hZ

omit [DecidableEq O] in
/-- Permutation invariance of `RootCells`. -/
theorem RootCells.perm {label : O → Pattern} {C : Configuration Pattern O}
    {rows₁ rows₂ : List (O × Pattern)} (inv : RootCells label C rows₁)
    (pm : rows₁.Perm rows₂) : RootCells label C rows₂ :=
  ⟨(pm.map Prod.fst).nodup_iff.mp inv.nodup,
   fun q m => inv.rows q (pm.symm.subset m),
   fun o p notIn => inv.others o p (fun m => notIn ((pm.map Prod.fst).subset m))⟩

omit [DecidableEq O] in
/-- Permutation invariance of `CellsU`. -/
theorem CellsU.perm {l m : Pattern} {label : O → Pattern} {C : Configuration Pattern O}
    {tk : O} {cs₁ cs₂ : List (O × Pattern)} (inv : CellsU l m label C tk cs₁)
    (pm : cs₁.Perm cs₂) : CellsU l m label C tk cs₂ :=
  ⟨inv.phase, (pm.map Prod.fst).nodup_iff.mp inv.nodup,
   fun q m' => inv.rows q (pm.symm.subset m'),
   fun o p ne notIn => inv.others o p ne (fun m' => notIn ((pm.map Prod.fst).subset m'))⟩

omit [DecidableEq O] in
/-- Pull two distinct-occurrence pairs `q₁, q₂ ∈ L` (with `(L.map Prod.fst).Nodup` and
`q₁.1 ≠ q₂.1`) to the front of `L`. -/
theorem list_perm_pick2 {L : List (O × Pattern)} (nd : (L.map Prod.fst).Nodup)
    {q₁ q₂ : O × Pattern} (h₁ : q₁ ∈ L) (h₂ : q₂ ∈ L) (ne12 : q₁.1 ≠ q₂.1) :
    ∃ rest : List (O × Pattern), L.Perm (q₁ :: q₂ :: rest) ∧
      ∀ q ∈ rest, q ∈ L ∧ q.1 ≠ q₁.1 ∧ q.1 ≠ q₂.1 := by
  obtain ⟨pre₁, post₁, rfl⟩ := List.append_of_mem h₁
  have pm₁ : (pre₁ ++ q₁ :: post₁).Perm (q₁ :: (pre₁ ++ post₁)) := List.perm_middle
  have q₂In : q₂ ∈ pre₁ ++ post₁ := by
    rcases List.mem_cons.mp (pm₁.subset h₂) with rfl | m
    · exact absurd rfl ne12.symm
    · exact m
  obtain ⟨pre₂, post₂, eq₂⟩ := List.append_of_mem q₂In
  have pm₂ : (pre₁ ++ post₁).Perm (q₂ :: (pre₂ ++ post₂)) := eq₂ ▸ List.perm_middle
  have pm : (pre₁ ++ q₁ :: post₁).Perm (q₁ :: q₂ :: (pre₂ ++ post₂)) := pm₁.trans (.cons q₁ pm₂)
  obtain ⟨out₁, ndTail⟩ := List.nodup_cons.mp ((pm.map Prod.fst).nodup_iff.mp nd)
  obtain ⟨out₂, -⟩ := List.nodup_cons.mp ndTail
  refine ⟨pre₂ ++ post₂, pm, fun q m => ⟨pm.symm.subset (by simp [m]), ?_, ?_⟩⟩
  · exact fun e => out₁ (List.mem_cons_of_mem _ (e ▸ List.mem_map.mpr ⟨q, m, rfl⟩))
  · exact fun e => out₂ (e ▸ List.mem_map.mpr ⟨q, m, rfl⟩)

/-- Unified `CellsU` constructor for `openRootAt` and `openChildAt` from post-state readouts and
non-collision on old `C.present` rows. -/
theorem cellsU_of_open {m x Q : Pattern} {label : O → Pattern} {C : Configuration Pattern O}
    {g : Firing O QNE located PUnit.unit} {pr tk : O}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (madeEq : g.selection.made = [pr, tk])
    (readsPr : ∀ σ : PSubst, nameAction.Models σ (resConf label C g).equations →
      NameLaws (psubst σ ((res label C g).label pr))
        (psubst σ (atLoc (predotU Q) (childLoc m x (predotU Q)))))
    (readsTk : ∀ σ : PSubst, nameAction.Models σ (resConf label C g).equations →
      NameLaws (psubst σ ((res label C g).label tk))
        (psubst σ (pendingTok (childLoc m x (predotU Q)) m)))
    (cleanOnPost : ∀ o ∈ C.present, ∀ σ : PSubst,
      nameAction.Models σ (resConf label C g).equations →
        (∀ m', ¬ NameLaws (psubst σ (label o))
          (pendingTok (psubst σ (childLoc m x (predotU Q))) m')) ∧
        (∀ m' c, ¬ NameLaws (psubst σ (label o))
          (doneTok (psubst σ (childLoc m x (predotU Q))) m' c)) ∧
        (∀ y, ¬ NameLaws (psubst σ (label o))
          (atLoc y (psubst σ (childLoc m x (predotU Q)))))) :
    CellsU (childLoc m x (predotU Q)) m (res label C g).label (resConf label C g) tk [(pr, Q)] := by
  let l := childLoc m x (predotU Q)
  obtain ⟨_, shapes, -⟩ := (RuleSyntax.admits_iff g).mp admitted
  have prNeTk : pr ≠ tk := by
    have nd := shapes.2.1; rw [madeEq] at nd; exact (List.nodup_cons.mp nd).1 ∘ List.mem_singleton.mpr
  have phase : PendingPhaseS l m (res label C g).label (resConf label C g) tk := by
    refine ⟨(result_present g tk).mpr (.inr (by simp [madeEq])), readsTk, ?_, ?_⟩
    · rintro o oP ⟨σ, s, m', same⟩
      rcases result_row oP with made | ⟨old, -, -, lblOld⟩
      · rw [madeEq] at made; simp only [List.mem_cons, List.not_mem_nil, or_false] at made
        rcases made with rfl | rfl
        · have both := same.symm.trans (readsPr σ s); rw [psubst_atLoc_any] at both
          exact absurd (nameLaws_heads both) (by decide)
        · rfl
      · rw [lblOld] at same; exact absurd same ((cleanOnPost o old σ s).1 m')
    · rintro o oP ⟨σ, s, m', c, same⟩
      rcases result_row oP with made | ⟨old, -, -, lblOld⟩
      · rw [madeEq] at made; simp only [List.mem_cons, List.not_mem_nil, or_false] at made
        rcases made with rfl | rfl
        · have both := same.symm.trans (readsPr σ s); rw [psubst_atLoc_any] at both
          exact absurd (nameLaws_heads both) (by decide)
        · have both := same.symm.trans (readsTk σ s); rw [psubst_pendingTok] at both
          exact absurd (nameLaws_heads both) (by decide)
      · rw [lblOld] at same; exact (cleanOnPost o old σ s).2.1 m' c same
  refine ⟨phase, List.nodup_singleton pr, fun q qM => ?_, fun o oP neTk notPr σ s y same => ?_⟩
  · simp only [List.mem_singleton] at qM; subst qM
    exact ⟨(result_present g pr).mpr (.inr (by simp [madeEq])), prNeTk, readsPr⟩
  · rcases result_row oP with made | ⟨old, -, -, lblOld⟩
    · rw [madeEq] at made; simp only [List.mem_cons, List.not_mem_nil, or_false] at made
      rcases made with rfl | rfl
      · exact notPr (by simp)
      · exact neTk rfl
    · rw [lblOld] at same; exact (cleanOnPost o old σ s).2.2 y same

end ChildUpdates

#print axioms located_firing_partition
#print axioms rootCells_heat_node_reflects
#print axioms rootCells_clear_node_reflects
#print axioms cellsU_keep_other
#print axioms cellsU_heat_reflects
#print axioms doneCellsU_step_or_keep
#print axioms cellsU_of_open

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem
