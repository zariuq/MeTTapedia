import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystemRoot

/-!
# Whole-system root bag readout, non-root isolation, and root `COMM`/`PAR`/`EQUIV`/depth-1 `REFL`

This module completes milestone P3 at the name frame `QN`:

* **Universal `FreeOnPats` preservation** (`freeOnPats_of_extends`,
  `freeOnPats_after_comm_extends`, `spineHasPattern_par_iff`): propagates semantic
  pattern-instantiation freedom across any housekeeping or disjoint-binder communication firing
  that extends store solutions.
* **`pPar` structural congruence lemmas** (`components_pPar_eq`, `bagEq_pPar_singleton`,
  `bagEq_pPar_heat`, `bagEq_pPar_clear`, `bagEq_pPar_pick1`, `bagEq_pPar_pick2`,
  `bagStep_of_pPar_comm`, `canonicalBagStep_of_pPar_comm`, `bagStep_of_pPar_refl`,
  `canonicalBagStep_of_pPar_refl`): connect the list of root cells directly to `Corrected.BagEq`,
  `Corrected.BagStep`, and `Corrected.CanonicalBagStep` with no parallel evaluator and no
  `Controls` import.
* **No root tokens & non-root isolation** (`NoRootTokens`, `noRootTokens_preserved`,
  `RootCells`, `rootCells_keep_nonRoot`): no row ever reads as `Pending(Root, _)` or
  `Done(Root, _, _)`, and every admitted child/opening firing leaves `RootCells` untouched.
* **Whole-system root `HEAT`, `CLEAR`, `COMM`, and `closeRoot`** (`rootCells_heat`,
  `rootCells_heat_reflects`, `root_heating_live`, `rootCells_clear`, `rootCells_clear_reflects`,
  `rootCells_comm_forward`, `rootCells_comm_ground_forward`, `rootCells_comm_backward`,
  `rootCells_closeRoot`) on mixed configurations carrying concurrent child rows/tokens, under both
  **Interface N** and **Interface C**.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar nQuote tProc pReflect
  applyDot)
open MeTTaOperationsComm (psubst PSubst pvars psubst_of_pvars_nil psubst_pFor psubst_tProc
  psubst_pZero commSelection dotted GroundPrincipal firstOrder)
open MeTTaCalculus.Corrected (binders Apart psubstList_eq_map components components_par
  components_pZero componentsList_eq_flatMap canonicalBag bagEq_iff BagEq BagStep
  CanonicalBagStep conventional listener)
open FiniteProgram (commRule heatRule clearRule channelUnknown parts predot predot_pFor
  predot_ground predot_of_binders_nil)
open OneFrame (embed)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open ReflQuotient (BagLaws bagCanon groundBags canonSubst_unifies)
open ReflNames (NameLaws nameAction QN QNE nameCanon nameLaws_iff nameLaws_heads
  nameLaws_pFor_iff nameLaws_pair_iff nameCanon_apply_head nameCanon_collection commAtN
  bagLaws_of_nameLaws)
open ReflLocated (atLoc rootLoc childLoc pendingTok doneTok locL locM reflP accC atRule rootFiring
  atFiring widen located commChild heatChild heatN cool closeRoot closeChild openRoot openChild
  exists_mem_zip psubst_rootLoc psubst_atLoc_any psubst_pendingTok psubst_par locatedFrame_name)
open ReflPacking (cooled psubst_doneTok nameLaws_doneTok_iff)
open ReflLocatedStep (located_cases produce_shapes head_of_reading₂ psubst_childLoc
  nameLaws_pendingTok_iff nameLaws_childLoc_iff exists_mem_zip_right res resConf info_known
  take_reads read_reads taken_row solution_of_admitted result_present result_label_old made_label
  made_not_present result_row commChildAt psubst_pReflect)
open ReflUniform (predotU predotU_pFor predotU_pZero)
open ReflCorrespondence (Clean LocatedRun Splits openRootAt closeRootAt)

/-! ## Universal `FreeOnPats` preservation across solution-extending firings -/

/-- Any firing whose solutions refine `C.equations` and extend every solution `τ` on `C.present`
preserves `FreeOnPats pats` whenever every `q ∈ pats` sits at a spine position of some row in
`C.present`. -/
theorem freeOnPats_of_extends {O : Type*} {label : O → Pattern} {C C₁ : Configuration Pattern O}
    {pats : List Pattern} (free : FreeOnPats pats C.equations)
    (refines : ∀ σ : PSubst, nameAction.Models σ C₁.equations → nameAction.Models σ C.equations)
    (extendsSol : ∀ τ : PSubst, nameAction.Models τ C.equations →
      ∃ w : PSubst, nameAction.Models w C₁.equations ∧
        ∀ o' ∈ C.present, NameLaws (psubst w (label o')) (psubst τ (label o')))
    (anchored : ∀ q ∈ pats, ∃ o' ∈ C.present, ∃ R l : Pattern,
      (∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label o')) (psubst σ (atLoc R l))) ∧
      SpineHasPattern q R) :
    FreeOnPats pats C₁.equations := by
  intro τ₀
  obtain ⟨σ₀, known₀, agree₀⟩ := free τ₀
  obtain ⟨w, solvedW, onState⟩ := extendsSol σ₀ known₀
  refine ⟨w, solvedW, fun q qIn => ?_⟩
  obtain ⟨o', oPres, R, l, reads, has⟩ := anchored q qIn
  have onR := row_extends_target reads refines solvedW known₀ (onState o' oPres)
  exact (spineHasPattern_nameLaws has onR).trans (agree₀ q qIn)

/-- Preserves `FreeOnPats pats'` across a communication on `(t, u)` with unifier `bs` when `pats'`
is variable-disjoint from `pvars t ++ pvars u` and anchored in `C.present`. -/
theorem freeOnPats_after_comm_extends {O : Type*} {label : O → Pattern}
    {C C₁ : Configuration Pattern O} {t u : Pattern} {bs : Bindings} {pats' : List Pattern}
    (solves : psubst bs.lookup t = psubst bs.lookup u)
    (disj : ∀ q ∈ pats', ∀ v ∈ pvars q, v ∉ pvars t ++ pvars u)
    (free : FreeOnPats (t :: u :: pats') C.equations)
    (refines : ∀ σ : PSubst, nameAction.Models σ C₁.equations → nameAction.Models σ C.equations)
    (extendsComm : ∀ τ : PSubst, nameAction.Models τ C.equations →
      NameLaws (psubst τ t) (psubst τ u) →
        ∃ w : PSubst, nameAction.Models w C₁.equations ∧
          ∀ o' ∈ C.present, NameLaws (psubst w (label o')) (psubst τ (label o')))
    (anchored : ∀ q ∈ pats', ∃ o' ∈ C.present, ∃ R l : Pattern,
      (∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label o')) (psubst σ (atLoc R l))) ∧
      SpineHasPattern q R) :
    FreeOnPats pats' C₁.equations := by
  intro τ₀
  obtain ⟨σ₀, known₀, unif₀, agree₀⟩ := freeOnPats_glue_unifier solves disj free τ₀
  obtain ⟨w, solvedW, onState⟩ := extendsComm σ₀ known₀ unif₀
  refine ⟨w, solvedW, fun q qIn => ?_⟩
  obtain ⟨o', oPres, R, l, reads, has⟩ := anchored q qIn
  have onR := row_extends_target reads refines solvedW known₀ (onState o' oPres)
  exact (spineHasPattern_nameLaws has onR).trans (agree₀ q qIn)

theorem spineHasPattern_par_iff {q a b : Pattern} :
    SpineHasPattern q (par a b) ↔ SpineHasPattern q a ∨ SpineHasPattern q b := by
  constructor
  · intro h
    generalize e : par a b = p at h
    cases h with
    | guard => simp [par, pPar, pFor] at e
    | reflect => simp [par, pPar, pReflect] at e
    | @parLeft a' b' hA =>
        have eqs : a = a' ∧ b = b' := by simpa [par, pPar] using e
        exact .inl (eqs.1.symm ▸ hA)
    | @parRight a' b' hB =>
        have eqs : a = a' ∧ b = b' := by simpa [par, pPar] using e
        exact .inr (eqs.2.symm ▸ hB)
  · rintro (hA | hB)
    · exact .parLeft b hA
    · exact .parRight a hB

/-! ## `pPar` structural congruence and step lifting (`BagEq`, `BagStep`, `CanonicalBagStep`) -/

theorem components_pPar_eq (xs : List Pattern) :
    components (pPar xs) = xs.flatMap components := by
  simp [pPar, components, componentsList_eq_flatMap]

theorem bagEq_pPar_singleton (P : Pattern) : BagEq (pPar [P]) P := by
  rw [bagEq_iff, components_pPar_eq]; simp

theorem bagEq_pPar_perm {xs ys : List Pattern} (perm : xs.Perm ys) :
    BagEq (pPar xs) (pPar ys) := by
  rw [bagEq_iff, components_pPar_eq, components_pPar_eq]
  refine List.Perm.map _ ?_
  induction perm with
  | nil => rfl
  | cons x _ ih => simp only [List.flatMap_cons]; exact List.Perm.append_left _ ih
  | swap x y l =>
      simp only [List.flatMap_cons, ← List.append_assoc]
      exact List.Perm.append_right _ List.perm_append_comm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem bagEq_pPar_heat (pre post : List Pattern) (a b : Pattern) :
    BagEq (pPar (pre ++ a :: b :: post)) (pPar (pre ++ par a b :: post)) := by
  rw [bagEq_iff, components_pPar_eq, components_pPar_eq]
  simp [List.flatMap_append, components_par, List.append_assoc]

theorem bagEq_pPar_clear (pre post : List Pattern) :
    BagEq (pPar (pre ++ post)) (pPar (pre ++ pZero :: post)) := by
  rw [bagEq_iff, components_pPar_eq, components_pPar_eq]
  simp [List.flatMap_append, components_pZero]

theorem bagEq_pPar_pick1 (pre post : List Pattern) (a : Pattern) :
    BagEq (pPar (pre ++ a :: post)) (par a (pPar (pre ++ post))) := by
  rw [bagEq_iff, components_pPar_eq, components_par, components_pPar_eq]
  simp only [List.flatMap_append, List.flatMap_cons, List.map_append]
  have swap : List.Perm
      ((pre.flatMap components).map MeTTaCalculus.Corrected.close ++
        (components a).map MeTTaCalculus.Corrected.close)
      ((components a).map MeTTaCalculus.Corrected.close ++
        (pre.flatMap components).map MeTTaCalculus.Corrected.close) := List.perm_append_comm
  rw [← List.append_assoc]
  exact (swap.append (List.Perm.refl _)).trans (by rw [List.append_assoc])

theorem bagEq_pPar_pick2 (pre mid post : List Pattern) (a b : Pattern) :
    BagEq (pPar (pre ++ a :: (mid ++ b :: post)))
      (par (par a b) (pPar (pre ++ mid ++ post))) := by
  have step₁ := bagEq_pPar_pick1 pre (mid ++ b :: post) a
  have eqMid : pre ++ (mid ++ b :: post) = (pre ++ mid) ++ b :: post := by simp [List.append_assoc]
  have step₂ := bagEq_pPar_pick1 (pre ++ mid) post b
  exact step₁.trans ((BagEq.par (BagEq.refl a) (eqMid ▸ step₂)).trans
    (BagEq.par_assoc a b _).symm)

theorem bagStep_of_pPar_principal_comm {admit : MeTTaCalculus.Corrected.Admission}
    (pre mid post : List Pattern) (t u x A B : Pattern) (bs : Bindings)
    (principal : MeTTaCalculus.Corrected.Principal t u bs) (adm : admit t A u B bs) :
    BagStep admit (pPar (pre ++ pFor t x A :: (mid ++ pFor u x B :: post)))
      (pPar ((pre ++ mid ++ post) ++ [applyDot bs A, applyDot bs B])) := by
  have before := bagEq_pPar_pick2 pre mid post (pFor t x A) (pFor u x B)
  have after : BagEq (par (par (applyDot bs A) (applyDot bs B)) (pPar (pre ++ mid ++ post)))
      (pPar ((pre ++ mid ++ post) ++ [applyDot bs A, applyDot bs B])) := by
    simpa [List.append_assoc] using
      (bagEq_pPar_pick2 (pre ++ mid ++ post) [] [] (applyDot bs A) (applyDot bs B)).symm
  exact .congruence before (.parallel _ (.comm t u x A B bs principal adm)) after

theorem bagStep_of_pPar_comm {admit : MeTTaCalculus.Corrected.Admission}
    (pre mid post : List Pattern) (t u x A B : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (adm : admit t A u B bs) :
    BagStep admit (pPar (pre ++ pFor t x A :: (mid ++ pFor u x B :: post)))
      (pPar ((pre ++ mid ++ post) ++ [applyDot bs A, applyDot bs B])) :=
  bagStep_of_pPar_principal_comm pre mid post t u x A B bs
    (Comm.principal_of_groundPrincipal gp) adm

theorem canonicalBagStep_of_pPar_comm {admit : MeTTaCalculus.Corrected.Admission}
    (pre mid post : List Pattern) (t u x A B : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (adm : admit t A u B bs) :
    CanonicalBagStep admit (pPar (pre ++ pFor t x A :: (mid ++ pFor u x B :: post)))
      (pPar ((pre ++ mid ++ post) ++ [applyDot bs A, applyDot bs B])) := by
  have before := bagEq_pPar_pick2 pre mid post (pFor t x A) (pFor u x B)
  have after : BagEq (par (par (applyDot bs A) (applyDot bs B)) (pPar (pre ++ mid ++ post)))
      (pPar ((pre ++ mid ++ post) ++ [applyDot bs A, applyDot bs B])) := by
    simpa [List.append_assoc] using
      (bagEq_pPar_pick2 (pre ++ mid ++ post) [] [] (applyDot bs A) (applyDot bs B)).symm
  exact .congruence before
    (.parallel _ (.comm t u x A B bs (Comm.principal_of_groundPrincipal gp) adm)) after

theorem bagStep_of_pPar_refl {admit : MeTTaCalculus.Corrected.Admission}
    (pre post : List Pattern) (x source target : Pattern)
    (inner : BagStep admit source target) :
    BagStep admit (pPar (pre ++ pReflect x source :: post))
      (pPar (pre ++ pFor (tProc target) x pZero :: post)) :=
  .congruence (bagEq_pPar_pick1 pre post (pReflect x source))
    (.parallel _ (.reflect x inner))
    (bagEq_pPar_pick1 pre post (pFor (tProc target) x pZero)).symm

theorem canonicalBagStep_of_pPar_refl {admit : MeTTaCalculus.Corrected.Admission}
    (pre post : List Pattern) (x source target : Pattern)
    (inner : CanonicalBagStep admit source target) :
    CanonicalBagStep admit (pPar (pre ++ pReflect x source :: post))
      (pPar (pre ++ listener x target :: post)) :=
  .congruence (bagEq_pPar_pick1 pre post (pReflect x source))
    (.parallel _ (.reflect x inner))
    (bagEq_pPar_pick1 pre post (listener x target)).symm

/-! ## `NoRootTokens`, `RootCells`, and non-root isolation -/

section RootBag

variable {O : Type*} [DecidableEq O]

/-- No present row reads at any solution as `Pending(Root, _)` or `Done(Root, _, _)`. -/
def NoRootTokens (label : O → Pattern) (C : Configuration Pattern O) : Prop :=
  ∀ o ∈ C.present, ∀ σ : PSubst, nameAction.Models σ C.equations →
    (∀ m, ¬ NameLaws (psubst σ (label o)) (pendingTok rootLoc m)) ∧
    (∀ m c, ¬ NameLaws (psubst σ (label o)) (doneTok rootLoc m c))

/-- **`NoRootTokens` is unconditionally preserved by every admitted firing of `located`.** -/
theorem noRootTokens_preserved {label : O → Pattern} {C : Configuration Pattern O}
    (noTok : NoRootTokens label C) (g : Firing O QNE located PUnit.unit)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g) :
    NoRootTokens (res label C g).label (resConf label C g) := by
  intro o oPres σ solved
  have known := info_known g solved
  rcases result_row oPres with made | ⟨old, -, -, labelOld⟩
  · obtain ⟨t, inside, labelEq⟩ := made_label admitted made
    refine ⟨fun m' same => ?_, fun m' c' same => ?_⟩
    · rw [labelEq] at same
      rcases produce_shapes g.member inside with ⟨args, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨-, _, rfl⟩
      · exact absurd (head_of_reading₂ same) (by decide)
      · have loc := (pending_reading_S same).1
        rw [psubst_childLoc, psubst_childLoc, psubst_rootLoc, psubst_rootLoc] at loc
        exact not_nameLaws_childLoc_rootLoc _ _ _ loc
      · have loc := (pending_reading_S same).1
        rw [psubst_childLoc, psubst_childLoc] at loc
        exact not_nameLaws_childLoc_rootLoc _ _ _ loc
      · exact absurd (head_of_reading₂ same) (by decide)
    · rw [labelEq] at same
      rcases produce_shapes g.member inside with ⟨args, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨rule, c₀, rfl⟩
      · exact absurd (head_of_reading₂ same) (by decide)
      · exact absurd (head_of_reading₂ same) (by decide)
      · exact absurd (head_of_reading₂ same) (by decide)
      · have loc := (done_reading_S same).1
        rcases rule with isComm | isCool | isClose
        · obtain ⟨o₁, z₁, p₁⟩ := taken_row admitted (t := pendingTok locL locM)
            (by rw [isComm]; simp [commChild])
          have r₁ := take_reads g solved z₁; rw [psubst_pendingTok, psubst_pendingTok] at r₁
          exact (noTok o₁ p₁ σ known).1 _
            (r₁.symm.trans (nameLaws_pendingTok_iff.mpr ⟨loc, NameLaws.refl _⟩))
        · obtain ⟨o₁, z₁, p₁⟩ := taken_row admitted (t := doneTok locL locM accC)
            (by rw [isCool]; simp [cool])
          have r₁ := take_reads g solved z₁; rw [psubst_doneTok, psubst_doneTok] at r₁
          exact (noTok o₁ p₁ σ known).2 _ _
            (r₁.symm.trans (nameLaws_doneTok_iff.mpr ⟨loc, NameLaws.refl _, NameLaws.refl _⟩))
        · obtain ⟨o₁, z₁, p₁⟩ := taken_row admitted (t := pendingTok locL locM)
            (by rw [isClose]; simp [closeChild])
          have r₁ := take_reads g solved z₁; rw [psubst_pendingTok, psubst_pendingTok] at r₁
          exact (noTok o₁ p₁ σ known).1 _
            (r₁.symm.trans (nameLaws_pendingTok_iff.mpr ⟨loc, NameLaws.refl _⟩))
  · rw [labelOld]; exact noTok o old σ known

/-- **Whole-system root cells**: `rootRows` lists all present `Root` rows, each reading as
`atLoc (predotU q.2) rootLoc` modulo `NameLaws` at every solution of `C.equations`. -/
structure RootCells (label : O → Pattern) (C : Configuration Pattern O)
    (rootRows : List (O × Pattern)) : Prop where
  nodup : (rootRows.map Prod.fst).Nodup
  rows : ∀ q ∈ rootRows, q.1 ∈ C.present ∧
    ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label q.1)) (psubst σ (atLoc (predotU q.2) rootLoc))
  others : ∀ o ∈ C.present, o ∉ rootRows.map Prod.fst →
    ∀ σ : PSubst, nameAction.Models σ C.equations →
      ∀ y : Pattern, ¬ NameLaws (psubst σ (label o)) (atLoc y rootLoc)

/-- Whole-system source process assembled from `rootRows`. -/
def rootBagProcess (rootRows : List (O × Pattern)) : Pattern := pPar (rootRows.map Prod.snd)

/-- Multiset of leaf parallel parts contributed by `rootRows`. -/
def rootPartsBag (rootRows : List (O × Pattern)) : Multiset Pattern :=
  (rootRows.flatMap fun q => parts q.2 : List Pattern)

/-- Processes built from `pZero`, binary `par`, `pFor`, and `pReflect`. -/
inductive RootTerm : Pattern → Prop where
  | zero : RootTerm pZero
  | par {a b : Pattern} : RootTerm a → RootTerm b → RootTerm (par a b)
  | guard (t x A : Pattern) : RootTerm (pFor t x A)
  | reflect (x P : Pattern) : RootTerm (pReflect x P)

private theorem not_nameLaws_apply_par (c : String) (args : List Pattern) (d e : Pattern) :
    ¬ NameLaws (.apply c args) (par d e) := by
  intro same; have canon := (nameLaws_iff _ _).mp same
  obtain ⟨_, hL⟩ := nameCanon_apply_head c args
  rw [hL, par, pPar, nameCanon_collection] at canon; cases canon

private theorem not_nameLaws_par_apply (d e : Pattern) (c : String) (args : List Pattern) :
    ¬ NameLaws (par d e) (.apply c args) :=
  fun same => not_nameLaws_apply_par c args d e same.symm

private theorem not_nameLaws_apply_diff {c₁ c₂ : String} (diff : c₁ ≠ c₂)
    (args₁ args₂ : List Pattern) : ¬ NameLaws (.apply c₁ args₁) (.apply c₂ args₂) := by
  intro same; have canon := (nameLaws_iff _ _).mp same
  obtain ⟨_, h₁⟩ := nameCanon_apply_head c₁ args₁
  obtain ⟨_, h₂⟩ := nameCanon_apply_head c₂ args₂
  rw [h₁, h₂] at canon; exact diff (Pattern.apply.inj canon).1

private theorem no_root_pending_taken {label : O → Pattern} {C : Configuration Pattern O}
    (noTok : NoRootTokens label C) {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (pendIn : pendingTok locL locM ∈ g.rule.body.take) {σ : PSubst}
    (solved : nameAction.Models σ (g.information QN (embed label C)))
    (locRoot : NameLaws (psubst σ (psubst g.opening locL)) rootLoc) : False := by
  obtain ⟨oP, zP, pP⟩ := taken_row admitted pendIn
  have rP := take_reads g solved zP; rw [psubst_pendingTok, psubst_pendingTok] at rP
  exact (noTok oP pP σ (info_known g solved)).1 _
    (rP.symm.trans (nameLaws_pendingTok_iff.mpr ⟨locRoot, NameLaws.refl _⟩))

/-- **Every non-root firing (`openRoot`, `openChild`, `heatChild`, `commChild`, `cool`,
`closeChild`) preserves `RootCells` with the exact same `rootRows` list.** -/
theorem rootCells_keep_nonRoot {label : O → Pattern} {C : Configuration Pattern O}
    {rootRows : List (O × Pattern)} (noTok : NoRootTokens label C)
    (inv : RootCells label C rootRows) (g : Firing O QNE located PUnit.unit)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (notRootComm : g.rule ≠ atRule rootLoc commRule)
    (notRootHeat : g.rule ≠ atRule rootLoc heatRule)
    (notRootClear : g.rule ≠ atRule rootLoc clearRule)
    (notCloseRoot : g.rule ≠ closeRoot) :
    RootCells (res label C g).label (resConf label C g) rootRows := by
  obtain ⟨_, shapes, enabled, -⟩ := (RuleSyntax.admits_iff g).mp admitted
  have notTaken : ∀ q ∈ rootRows, q.1 ∉ g.selection.taken := by
    intro q qIn taken
    obtain ⟨t, zipped⟩ := exists_mem_zip_right shapes.2.2.1 taken
    obtain ⟨σ₀, solved₀⟩ := solution_of_admitted admitted
    have known₀ := info_known g solved₀
    have both := (take_reads g solved₀ zipped).trans ((inv.rows q qIn).2 σ₀ known₀)
    have tMem := (List.of_mem_zip zipped).1
    rcases located_cases g.member with rC | rH | rCl | cC | cH | cCl | clR | clC | opR | opC
    · exact notRootComm rC
    · exact notRootHeat rH
    · exact notRootClear rCl
    · rw [cC] at tMem; simp only [commChild, List.mem_cons, List.not_mem_nil, or_false] at tMem
      rcases tMem with rfl | rfl | rfl
      · simp only [psubst_atLoc_any, psubst_rootLoc] at both
        exact no_root_pending_taken noTok admitted (by rw [cC]; simp [commChild]) solved₀
          ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2
      · simp only [psubst_atLoc_any, psubst_rootLoc] at both
        exact no_root_pending_taken noTok admitted (by rw [cC]; simp [commChild]) solved₀
          ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2
      · simp only [psubst_atLoc_any] at both; exact absurd (head_of_reading₂ both) (by decide)
    · rw [cH] at tMem; obtain rfl := List.mem_singleton.mp tMem
      simp only [psubst_atLoc_any, psubst_rootLoc] at both
      obtain ⟨oP, zP⟩ := exists_mem_zip shapes.2.2.2.1 (x := pendingTok locL locM)
        (by rw [cH]; simp [heatChild])
      have pP : oP ∈ C.present :=
        enabled.kept_subset (by simpa [Selection.commit] using (List.of_mem_zip zP).2)
      have rP := read_reads g solved₀ zP; rw [psubst_pendingTok, psubst_pendingTok] at rP
      exact (noTok oP pP σ₀ known₀).1 _ (rP.symm.trans
        (nameLaws_pendingTok_iff.mpr ⟨((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2,
          NameLaws.refl _⟩))
    · rw [cCl] at tMem; simp only [cool, List.mem_cons, List.not_mem_nil, or_false] at tMem
      rcases tMem with rfl | rfl
      · simp only [psubst_atLoc_any] at both; exact absurd (head_of_reading₂ both) (by decide)
      · simp only [psubst_atLoc_any, psubst_rootLoc] at both
        obtain ⟨oD, zD, pD⟩ := taken_row admitted (t := doneTok locL locM accC)
          (by rw [cCl]; simp [cool])
        have rD := take_reads g solved₀ zD; rw [psubst_doneTok, psubst_doneTok] at rD
        exact (noTok oD pD σ₀ known₀).2 _ _ (rD.symm.trans (nameLaws_doneTok_iff.mpr
          ⟨((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2, NameLaws.refl _, NameLaws.refl _⟩))
    · exact notCloseRoot clR
    · rw [clC] at tMem; simp only [closeChild, List.mem_cons, List.not_mem_nil, or_false] at tMem
      rcases tMem with rfl | rfl | rfl
      · simp only [psubst_atLoc_any, psubst_rootLoc] at both
        exact no_root_pending_taken noTok admitted (by rw [clC]; simp [closeChild]) solved₀
          ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2
      · simp only [psubst_atLoc_any] at both; exact absurd (head_of_reading₂ both) (by decide)
      · simp only [psubst_atLoc_any] at both; exact absurd (head_of_reading₂ both) (by decide)
    · rw [opR] at tMem; simp [openRoot] at tMem
    · rw [opC] at tMem; simp [openChild] at tMem
  refine ⟨inv.nodup, fun q qIn => ?_, fun o oPres notRoot σ solved y same => ?_⟩
  · obtain ⟨qPres, qR⟩ := inv.rows q qIn
    refine ⟨(result_present g q.1).mpr (.inl ⟨qPres, notTaken q qIn⟩), fun σ solved => ?_⟩
    rw [result_label_old g (fun m => made_not_present admitted m qPres)]
    exact qR σ (info_known g solved)
  · have known := info_known g solved
    rcases result_row oPres with made | ⟨old, -, -, labelOld⟩
    · obtain ⟨t, inside, labelEq⟩ := made_label admitted made
      rw [labelEq] at same
      rcases located_cases g.member with rC | rH | rCl | cC | cH | cCl | clR | clC | opR | opC
      · exact notRootComm rC
      · exact notRootHeat rH
      · exact notRootClear rCl
      · rw [cC] at inside
        simp only [commChild, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl
        · simp only [psubst_atLoc_any] at same
          exact no_root_pending_taken noTok admitted (by rw [cC]; simp [commChild]) solved
            ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2
        · simp only [psubst_atLoc_any] at same
          exact no_root_pending_taken noTok admitted (by rw [cC]; simp [commChild]) solved
            ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2
        · exact absurd (head_of_reading₂ same) (by decide)
      · rw [cH] at inside
        simp only [heatChild, List.mem_cons, List.not_mem_nil, or_false] at inside
        obtain ⟨oP, zP⟩ := exists_mem_zip shapes.2.2.2.1 (x := pendingTok locL locM)
          (by rw [cH]; simp [heatChild])
        have pP : oP ∈ C.present :=
          enabled.kept_subset (by simpa [Selection.commit] using (List.of_mem_zip zP).2)
        have rP := read_reads g solved zP; rw [psubst_pendingTok, psubst_pendingTok] at rP
        rcases inside with rfl | rfl <;>
          { simp only [psubst_atLoc_any] at same
            exact (noTok oP pP σ known).1 _ (rP.symm.trans (nameLaws_pendingTok_iff.mpr
              ⟨((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2, NameLaws.refl _⟩)) }
      · rw [cCl] at inside; simp only [cool, List.mem_singleton] at inside; subst inside
        exact absurd (head_of_reading₂ same) (by decide)
      · exact notCloseRoot clR
      · rw [clC] at inside
        simp only [closeChild, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl
        · simp only [psubst_atLoc_any] at same
          exact no_root_pending_taken noTok admitted (by rw [clC]; simp [closeChild]) solved
            ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2
        · exact absurd (head_of_reading₂ same) (by decide)
      · rw [opR] at inside
        simp only [openRoot, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl
        · simp only [psubst_atLoc_any, psubst_childLoc, psubst_rootLoc] at same
          exact not_nameLaws_childLoc_rootLoc _ _ _
            ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2
        · exact absurd (head_of_reading₂ same) (by decide)
      · rw [opC] at inside
        simp only [openChild, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl
        · simp only [psubst_atLoc_any, psubst_childLoc] at same
          exact not_nameLaws_childLoc_rootLoc _ _ _
            ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2
        · exact absurd (head_of_reading₂ same) (by decide)
    · rw [labelOld] at same; exact inv.others o old notRoot σ known y same

/-! ### `RootCells` transitions under root `heat`, `clear`, `comm`, and `closeRoot` -/

/-- Root heating on `(o, par a b) ∈ rootRows` splits the cell into `(m₁, a)` and `(m₂, b)`. -/
theorem rootCells_heat {label : O → Pattern} {C : Configuration Pattern O}
    {pre post : List (O × Pattern)} {o m₁ m₂ : O} {a b : Pattern} {ρ : PSubst}
    (inv : RootCells label C (pre ++ (o, par a b) :: post))
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (rootHeatAt ρ o m₁ m₂)) :
    RootCells (res label C (rootHeatAt ρ o m₁ m₂)).label
        (resConf label C (rootHeatAt ρ o m₁ m₂))
        (pre ++ (m₁, a) :: (m₂, b) :: post) ∧
      BagEq (rootBagProcess (pre ++ (m₁, a) :: (m₂, b) :: post))
        (rootBagProcess (pre ++ (o, par a b) :: post)) ∧
      rootPartsBag (pre ++ (m₁, a) :: (m₂, b) :: post) =
        rootPartsBag (pre ++ (o, par a b) :: post) := by
  obtain ⟨_, shapes, enabled, -⟩ := (RuleSyntax.admits_iff _).mp admitted
  have madeDistinct : m₁ ≠ m₂ := by
    simpa [rootHeatAt, rootFiring, widen, atFiring, heatN] using shapes.2.1
  have freshMade : m₁ ∉ C.present ∧ m₂ ∉ C.present := by
    simpa [rootHeatAt, rootFiring, widen, atFiring, heatN, Selection.commit, embed]
      using enabled.fresh
  have permOld : ((pre ++ (o, par a b) :: post).map Prod.fst).Perm
      (o :: (pre ++ post).map Prod.fst) := by
    simp only [List.map_append, List.map_cons]; exact List.perm_middle
  obtain ⟨oOut, restNodup⟩ := List.nodup_cons.mp (permOld.nodup_iff.mp inv.nodup)
  have permNew : ((pre ++ (m₁, a) :: (m₂, b) :: post).map Prod.fst).Perm
      (m₁ :: m₂ :: (pre ++ post).map Prod.fst) := by
    simp only [List.map_append, List.map_cons]
    exact List.perm_middle.trans (List.Perm.cons _ List.perm_middle)
  have restInOld : ∀ q ∈ pre ++ post, q ∈ pre ++ (o, par a b) :: post := fun q m =>
    (List.mem_append.mp m).elim (List.mem_append_left _)
      (fun r => List.mem_append_right _ (List.mem_cons_of_mem _ r))
  have nodupNew : ((pre ++ (m₁, a) :: (m₂, b) :: post).map Prod.fst).Nodup := by
    refine permNew.nodup_iff.mpr (List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, restNodup⟩⟩)
    · simp only [List.mem_cons, not_or]
      refine ⟨madeDistinct, fun inR => ?_⟩
      obtain ⟨q, qIn, eqM⟩ := List.mem_map.mp inR
      exact freshMade.1 (eqM ▸ (inv.rows q (restInOld q qIn)).1)
    · intro inR; obtain ⟨q, qIn, eqM⟩ := List.mem_map.mp inR
      exact freshMade.2 (eqM ▸ (inv.rows q (restInOld q qIn)).1)
  have oReads : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label o)) (psubst σ (atLoc (par (predotU a) (predotU b)) rootLoc)) := by
    intro σ s; have r := (inv.rows (o, par a b) (by simp)).2 σ s; rwa [predotU_par] at r
  have keepRest : ∀ q ∈ pre ++ post,
      q.1 ∈ (res label C (rootHeatAt ρ o m₁ m₂)).present ∧
      ∀ σ : PSubst, nameAction.Models σ (resConf label C (rootHeatAt ρ o m₁ m₂)).equations →
        NameLaws (psubst σ ((res label C (rootHeatAt ρ o m₁ m₂)).label q.1))
          (psubst σ (atLoc (predotU q.2) rootLoc)) := by
    intro q qRest
    have qOld := restInOld q qRest
    have qPres := (inv.rows q qOld).1
    have neO : q.1 ≠ o := fun eqO => oOut (eqO ▸ List.mem_map.mpr ⟨q, qRest, rfl⟩)
    have ne₁ : q.1 ≠ m₁ := fun e => freshMade.1 (e ▸ qPres)
    have ne₂ : q.1 ≠ m₂ := fun e => freshMade.2 (e ▸ qPres)
    refine ⟨(result_present _ q.1).mpr (.inl ⟨qPres, by
      simp [rootHeatAt, rootFiring, widen, atFiring, heatN, neO]⟩), fun σ solved => ?_⟩
    rw [result_label_old _ (by simp [rootHeatAt, rootFiring, widen, atFiring, heatN, ne₁, ne₂])]
    exact (inv.rows q qOld).2 σ (info_known _ solved)
  refine ⟨⟨nodupNew, fun q qIn => ?_, fun x xPres xNotNew σ solved y same => ?_⟩, ?_, ?_⟩
  · simp only [List.mem_append, List.mem_cons] at qIn
    rcases qIn with inPre | rfl | rfl | inPost
    · exact keepRest q (List.mem_append_left _ inPre)
    · exact ⟨(result_present _ m₁).mpr (.inr (by
        simp [rootHeatAt, rootFiring, widen, atFiring, heatN])),
        fun σ solved => (rootHeat_reads_mixed label C ρ o madeDistinct _ _ oReads solved).1⟩
    · exact ⟨(result_present _ m₂).mpr (.inr (by
        simp [rootHeatAt, rootFiring, widen, atFiring, heatN])),
        fun σ solved => (rootHeat_reads_mixed label C ρ o madeDistinct _ _ oReads solved).2⟩
    · exact keepRest q (List.mem_append_right _ inPost)
  · rcases result_row xPres with made | ⟨old, notTaken, -, labelOld⟩
    · simp only [rootHeatAt, rootFiring, widen, atFiring, heatN, List.mem_cons,
        List.not_mem_nil, or_false] at made
      rcases made with rfl | rfl <;> exact xNotNew (by simp)
    · rw [labelOld] at same
      have neO : x ≠ o := fun eqO => notTaken (by
        simp [rootHeatAt, rootFiring, widen, atFiring, heatN, eqO])
      refine inv.others x old (fun inOld => ?_) σ (info_known _ solved) y same
      rcases List.mem_cons.mp (permOld.subset inOld) with rfl | inRest
      · exact neO rfl
      · obtain ⟨q, qIn, eqX⟩ := List.mem_map.mp inRest
        apply xNotNew
        rcases List.mem_append.mp qIn with l | r
        · exact List.mem_map.mpr ⟨q, List.mem_append_left _ l, eqX⟩
        · exact List.mem_map.mpr ⟨q, List.mem_append_right _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ r)), eqX⟩
  · unfold rootBagProcess
    simpa [List.map_append] using bagEq_pPar_heat (pre.map Prod.snd) (post.map Prod.snd) a b
  · unfold rootPartsBag
    simp [List.flatMap_append, FiniteProgram.parts_par, List.append_assoc]

/-- **Backward reflection of any admitted `rootHeatAt` firing** on `RootTerm` `RootCells`. -/
theorem rootCells_heat_reflects {label : O → Pattern} {C : Configuration Pattern O}
    {rootRows : List (O × Pattern)} (inv : RootCells label C rootRows)
    (terms : ∀ q ∈ rootRows, RootTerm q.2) {ρ : PSubst} {o m₁ m₂ : O}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (rootHeatAt ρ o m₁ m₂)) :
    ∃ rootRows',
      RootCells (res label C (rootHeatAt ρ o m₁ m₂)).label
        (resConf label C (rootHeatAt ρ o m₁ m₂)) rootRows' ∧
      (∀ q ∈ rootRows', RootTerm q.2) ∧
      BagEq (rootBagProcess rootRows') (rootBagProcess rootRows) := by
  obtain ⟨_, -, enabled, ⟨_, w, solved⟩, -, -⟩ := (RuleSyntax.admits_iff _).mp admitted
  have oPres : o ∈ C.present := enabled.taken_subset
    (by simp [rootHeatAt, rootFiring, widen, atFiring, heatN, Selection.commit])
  have known := info_known _ solved
  obtain ⟨a', b', lEq, -, -⟩ := rootHeat_takes_pair label C ρ o m₁ m₂ solved
  have oIn : o ∈ rootRows.map Prod.fst := by
    by_contra notIn; refine inv.others o oPres notIn w known (par a' b') ?_
    rw [lEq]; exact NameLaws.refl _
  obtain ⟨⟨o₀, P⟩, qIn, eqO⟩ := List.mem_map.mp oIn
  have eqO' : o₀ = o := eqO
  subst eqO'
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem qIn
  have r := (inv.rows (o₀, P) (by simp)).2 w known
  dsimp only at r
  rw [lEq, psubst_atLoc_any, psubst_rootLoc] at r
  have bodyEq : NameLaws (par a' b') (psubst w (predotU P)) :=
    ((locatedFrame_name.atLoc_iff _ _ _ _).mp r).1
  have hTerm : RootTerm P := terms (o₀, P) (by simp)
  cases hTerm with
  | zero =>
      rw [predotU_pZero, psubst_pZero] at bodyEq
      exact absurd bodyEq (not_nameLaws_par_apply a' b' _ _)
  | guard t x A =>
      rw [predotU_pFor, psubst_pFor] at bodyEq
      exact absurd bodyEq (not_nameLaws_par_apply a' b' _ _)
  | reflect x Q =>
      rw [predotU_pReflect, psubst_pReflect] at bodyEq
      exact absurd bodyEq (not_nameLaws_par_apply a' b' _ _)
  | @par a b hA hB =>
      obtain ⟨inv', bagEq, -⟩ := rootCells_heat inv admitted
      refine ⟨pre ++ (m₁, a) :: (m₂, b) :: post, inv', fun q qMem => ?_, bagEq⟩
      simp only [List.mem_append, List.mem_cons] at qMem
      rcases qMem with inPre | rfl | rfl | inPost
      · exact terms q (List.mem_append_left _ inPre)
      · exact hA
      · exact hB
      · exact terms q (List.mem_append_right _ (List.mem_cons_of_mem _ inPost))

/-- Single `rootHeatAt` preserves `FreeOnPats` and its spine anchoring in `RootCells`. -/
theorem freeOnPats_rootHeat {label : O → Pattern} {C : Configuration Pattern O}
    {pre post : List (O × Pattern)} {o m₁ m₂ : O} {a b : Pattern} {ρ : PSubst}
    (inv : RootCells label C (pre ++ (o, par a b) :: post))
    (opensFreshly : (rootHeatAt ρ o m₁ m₂).Fresh QN (embed label C))
    {pats : List Pattern} (free : FreeOnPats pats C.equations)
    (anchored : ∀ q ∈ pats, ∃ c ∈ pre ++ (o, par a b) :: post, SpineHasPattern q (predotU c.2)) :
    FreeOnPats pats (resConf label C (rootHeatAt ρ o m₁ m₂)).equations ∧
      ∀ q ∈ pats, ∃ c ∈ pre ++ (m₁, a) :: (m₂, b) :: post, SpineHasPattern q (predotU c.2) := by
  have oPres := (inv.rows (o, par a b) (by simp)).1
  have oReads : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label o))
        (psubst σ (atLoc (par (predotU a) (predotU b)) rootLoc)) := by
    intro σ s; have r := (inv.rows (o, par a b) (by simp)).2 σ s; rwa [predotU_par] at r
  refine ⟨freeOnPats_of_extends free (fun _ s => info_known _ s)
    (fun _ k => rootHeat_extends label C o m₁ m₂ oPres (predotU a) (predotU b) oReads
      opensFreshly k)
    (fun q qIn => by
      obtain ⟨c, cIn, has⟩ := anchored q qIn
      exact ⟨c.1, (inv.rows c cIn).1, predotU c.2, rootLoc, (inv.rows c cIn).2, has⟩),
    fun q qIn => ?_⟩
  obtain ⟨c, cIn, has⟩ := anchored q qIn
  simp only [List.mem_append, List.mem_cons] at cIn
  rcases cIn with inPre | rfl | inPost
  · exact ⟨c, List.mem_append_left _ inPre, has⟩
  · rw [predotU_par] at has
    rcases spineHasPattern_par_iff.mp has with hA | hB
    · exact ⟨(m₁, a), by simp, hA⟩
    · exact ⟨(m₂, b), by simp, hB⟩
  · exact ⟨c, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ inPost)),
      has⟩

/-- **Forward root spine heating (`Splits`)**: heats `(o, P)` in `RootCells` into leaf cells
matching `L` in order, preserving `FreeOnPats`, `BagEq`, and all untouched rows. -/
theorem root_heating_live [Infinite O] {P : Pattern} {L : List Pattern} (split : Splits P L) :
    ∀ (label : O → Pattern) (C : Configuration Pattern O) (pre post : List (O × Pattern))
      (o : O) (pats : List Pattern),
      RootCells label C (pre ++ (o, P) :: post) →
      FreeOnPats pats C.equations →
      (∀ q ∈ pats, ∃ c ∈ pre ++ (o, P) :: post, SpineHasPattern q (predotU c.2)) →
      ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (newCells : List (O × Pattern)),
        LocatedRun label C label' C' ∧
        newCells.map Prod.snd = L ∧
        RootCells label' C' (pre ++ newCells ++ post) ∧
        BagEq (rootBagProcess (pre ++ newCells ++ post))
          (rootBagProcess (pre ++ (o, P) :: post)) ∧
        FreeOnPats pats C'.equations ∧
        (∀ q ∈ pats, ∃ c ∈ pre ++ newCells ++ post, SpineHasPattern q (predotU c.2)) ∧
        (∀ σ : PSubst, nameAction.Models σ C'.equations → nameAction.Models σ C.equations) ∧
        (∀ o' ∈ C.present, o' ≠ o → o' ∈ C'.present ∧ label' o' = label o') := by
  induction split with
  | leaf P =>
      intro label C pre post o pats inv free anch
      exact ⟨label, C, [(o, P)], .refl label C, rfl, by simpa using inv,
        by simpa [rootBagProcess] using BagEq.refl _, free, by simpa using anch,
        fun _ s => s, fun _ p _ => ⟨p, rfl⟩⟩
  | @split a b LA LB _ _ ihA ihB =>
      intro label C pre post o pats inv free anch
      have oPres := (inv.rows (o, par a b) (by simp)).1
      obtain ⟨σ₀, known₀⟩ := freeOnPats_consistent free
      obtain ⟨m₁, fresh₁⟩ := Infinite.exists_notMem_finset C.present
      obtain ⟨m₂, fresh₂'⟩ := Infinite.exists_notMem_finset (insert m₁ C.present)
      have m₂ne : m₂ ≠ m₁ := fun s => fresh₂' (Finset.mem_insert.mpr (.inl s))
      have fresh₂ : m₂ ∉ C.present := fun s => fresh₂' (Finset.mem_insert.mpr (.inr s))
      obtain ⟨ρ, opensFreshly⟩ := rootHeat_fresh_exists label C o m₁ m₂
      have oReads : ∀ σ : PSubst, nameAction.Models σ C.equations →
          NameLaws (psubst σ (label o))
            (psubst σ (atLoc (par (predotU a) (predotU b)) rootLoc)) := by
        intro σ s; have r := (inv.rows (o, par a b) (by simp)).2 σ s; rwa [predotU_par] at r
      have pair₀ : NameLaws (psubst σ₀ (label o))
          (atLoc (par (psubst σ₀ (predotU a)) (psubst σ₀ (predotU b))) rootLoc) := by
        simpa [psubst_atLoc_any, psubst_par, psubst_rootLoc] using oReads σ₀ known₀
      have admitted := rootHeat_admitted label C o m₁ m₂ oPres m₂ne.symm fresh₁ fresh₂
        known₀ pair₀ opensFreshly
      obtain ⟨inv₁, bag₁, -⟩ := rootCells_heat inv admitted
      obtain ⟨free₁, anch₁⟩ := freeOnPats_rootHeat inv opensFreshly free anch
      let label₁ := (res label C (rootHeatAt ρ o m₁ m₂)).label
      let C₁ := resConf label C (rootHeatAt ρ o m₁ m₂)
      obtain ⟨label₂, C₂, cellsA, runA, mapA, inv₂, bagA, free₂, anch₂, backA, keepA⟩ :=
        ihA label₁ C₁ pre ((m₂, b) :: post) m₁ pats inv₁ free₁ anch₁
      have inv₂' : RootCells label₂ C₂ ((pre ++ cellsA) ++ (m₂, b) :: post) := by
        simpa [List.append_assoc] using inv₂
      have anch₂' : ∀ q ∈ pats, ∃ c ∈ (pre ++ cellsA) ++ (m₂, b) :: post,
          SpineHasPattern q (predotU c.2) := by simpa [List.append_assoc] using anch₂
      obtain ⟨label₃, C₃, cellsB, runB, mapB, inv₃, bagB, free₃, anch₃, backB, keepB⟩ :=
        ihB label₂ C₂ (pre ++ cellsA) post m₂ pats inv₂' free₂ anch₂'
      have inv₃' : RootCells label₃ C₃ (pre ++ (cellsA ++ cellsB) ++ post) := by
        simpa [List.append_assoc] using inv₃
      have anch₃' : ∀ q ∈ pats, ∃ c ∈ pre ++ (cellsA ++ cellsB) ++ post,
          SpineHasPattern q (predotU c.2) := by simpa [List.append_assoc] using anch₃
      have bag₃ : BagEq (rootBagProcess (pre ++ (cellsA ++ cellsB) ++ post))
          (rootBagProcess (pre ++ (o, par a b) :: post)) := by
        have bB : BagEq (rootBagProcess (pre ++ (cellsA ++ cellsB) ++ post))
            (rootBagProcess (pre ++ cellsA ++ (m₂, b) :: post)) := by
          simpa [rootBagProcess, List.append_assoc] using bagB
        exact bB.trans (bagA.trans bag₁)
      refine ⟨label₃, C₃, cellsA ++ cellsB, .step _ admitted (runA.trans runB),
        by simp [mapA, mapB], inv₃', bag₃, free₃, anch₃',
        fun σ s => info_known _ (backA σ (backB σ s)), fun o' p' neO => ?_⟩
      have ne₁ : o' ≠ m₁ := fun e => fresh₁ (e ▸ p')
      have ne₂ : o' ≠ m₂ := fun e => fresh₂ (e ▸ p')
      have in₁ : o' ∈ C₁.present := (result_present _ o').mpr (.inl ⟨p',
        by simp [rootHeatAt, rootFiring, widen, atFiring, heatN, neO]⟩)
      have lbl₁ : label₁ o' = label o' := result_label_old _
        (by simp [rootHeatAt, rootFiring, widen, atFiring, heatN, ne₁, ne₂])
      obtain ⟨in₂, lbl₂⟩ := keepA o' in₁ ne₁
      obtain ⟨in₃, lbl₃⟩ := keepB o' in₂ ne₂
      exact ⟨in₃, lbl₃.trans (lbl₂.trans lbl₁)⟩

/-- Root clearing on `(o, pZero) ∈ rootRows` drops the cell while preserving `BagEq`. -/
theorem rootCells_clear {label : O → Pattern} {C : Configuration Pattern O}
    {pre post : List (O × Pattern)} {o : O} {ρ : PSubst}
    (inv : RootCells label C (pre ++ (o, pZero) :: post))
    (_ : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) (rootClearAt ρ o)) :
    RootCells (res label C (rootClearAt ρ o)).label (resConf label C (rootClearAt ρ o))
        (pre ++ post) ∧
      BagEq (rootBagProcess (pre ++ post))
        (rootBagProcess (pre ++ (o, pZero) :: post)) ∧
      rootPartsBag (pre ++ post) = rootPartsBag (pre ++ (o, pZero) :: post) := by
  have permOld : ((pre ++ (o, pZero) :: post).map Prod.fst).Perm
      (o :: (pre ++ post).map Prod.fst) := by
    simp only [List.map_append, List.map_cons]; exact List.perm_middle
  obtain ⟨oOut, restNodup⟩ := List.nodup_cons.mp (permOld.nodup_iff.mp inv.nodup)
  have restInOld : ∀ q ∈ pre ++ post, q ∈ pre ++ (o, pZero) :: post := fun q m =>
    (List.mem_append.mp m).elim (List.mem_append_left _)
      (fun r => List.mem_append_right _ (List.mem_cons_of_mem _ r))
  refine ⟨⟨restNodup, fun q qIn => ?_, fun x xPres xNotRest σ solved y same => ?_⟩, ?_, ?_⟩
  · have qOld := restInOld q qIn
    have neO : q.1 ≠ o := fun eqO => oOut (eqO ▸ List.mem_map.mpr ⟨q, qIn, rfl⟩)
    refine ⟨(result_present _ q.1).mpr (.inl ⟨(inv.rows q qOld).1, by
      simp [rootClearAt, rootFiring, widen, atFiring, clearN, neO]⟩), fun σ solved => ?_⟩
    rw [result_label_old _ (by simp [rootClearAt, rootFiring, widen, atFiring, clearN])]
    exact (inv.rows q qOld).2 σ (info_known _ solved)
  · rcases result_row xPres with made | ⟨old, notTaken, -, labelOld⟩
    · simp [rootClearAt, rootFiring, widen, atFiring, clearN] at made
    · rw [labelOld] at same
      have neO : x ≠ o := fun eqO => notTaken (by
        simp [rootClearAt, rootFiring, widen, atFiring, clearN, eqO])
      refine inv.others x old (fun inOld => ?_) σ (info_known _ solved) y same
      rcases List.mem_cons.mp (permOld.subset inOld) with rfl | inRest
      · exact neO rfl
      · exact xNotRest inRest
  · unfold rootBagProcess
    simpa [List.map_append] using bagEq_pPar_clear (pre.map Prod.snd) (post.map Prod.snd)
  · unfold rootPartsBag; simp [List.flatMap_append, FiniteProgram.parts_pZero]

/-- **Backward reflection of any admitted `rootClearAt` firing** on `RootTerm` `RootCells`. -/
theorem rootCells_clear_reflects {label : O → Pattern} {C : Configuration Pattern O}
    {rootRows : List (O × Pattern)} (inv : RootCells label C rootRows)
    (terms : ∀ q ∈ rootRows, RootTerm q.2) {ρ : PSubst} {o : O}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (rootClearAt ρ o)) :
    ∃ rootRows',
      RootCells (res label C (rootClearAt ρ o)).label (resConf label C (rootClearAt ρ o))
        rootRows' ∧
      (∀ q ∈ rootRows', RootTerm q.2) ∧
      BagEq (rootBagProcess rootRows') (rootBagProcess rootRows) := by
  obtain ⟨_, -, enabled, ⟨_, w, solved⟩, -, -⟩ := (RuleSyntax.admits_iff _).mp admitted
  have oPres : o ∈ C.present := enabled.taken_subset
    (by simp [rootClearAt, rootFiring, widen, atFiring, clearN, Selection.commit])
  have known := info_known _ solved
  have zEq := rootClear_takes_zero label C ρ o solved
  have oIn : o ∈ rootRows.map Prod.fst := by
    by_contra notIn; exact inv.others o oPres notIn w known pZero zEq
  obtain ⟨⟨o₀, P⟩, qIn, eqO⟩ := List.mem_map.mp oIn
  have eqO' : o₀ = o := eqO
  subst eqO'
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem qIn
  have r := (inv.rows (o₀, P) (by simp)).2 w known
  dsimp only at r
  have both := zEq.symm.trans r
  rw [psubst_atLoc_any, psubst_rootLoc] at both
  have bodyEq : NameLaws pZero (psubst w (predotU P)) :=
    ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).1
  have hTerm : RootTerm P := terms (o₀, P) (by simp)
  cases hTerm with
  | par =>
      rw [predotU_par, psubst_par] at bodyEq
      exact absurd bodyEq (not_nameLaws_apply_par _ _ _ _)
  | guard t x A =>
      rw [predotU_pFor, psubst_pFor] at bodyEq
      exact absurd bodyEq (not_nameLaws_apply_diff (by decide) _ _)
  | reflect x Q =>
      rw [predotU_pReflect, psubst_pReflect] at bodyEq
      exact absurd bodyEq (not_nameLaws_apply_diff (by decide) _ _)
  | zero =>
      obtain ⟨inv', bagEq, -⟩ := rootCells_clear inv admitted
      refine ⟨pre ++ post, inv', fun q qMem => ?_, bagEq⟩
      rcases List.mem_append.mp qMem with inPre | inPost
      · exact terms q (List.mem_append_left _ inPre)
      · exact terms q (List.mem_append_right _ (List.mem_cons_of_mem _ inPost))

/-- Root COMM's occurrence update under a refinement of its committed
information. The untouched rows retain their reading; only the two
new reads must be established at the narrower set of solutions. -/
theorem rootCells_replace_comm_under {label : O → Pattern} {C : Configuration Pattern O}
    {pre mid post : List (O × Pattern)} {first second m₁ m₂ : O} {p₁ p₂ A' B' : Pattern}
    {ρ : PSubst} {K : EquationStore Pattern}
    (inv : RootCells label C (pre ++ (first, p₁) :: (mid ++ (second, p₂) :: post)))
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (rootCommAt ρ first second m₁ m₂))
    (refines : ∀ σ : PSubst, nameAction.Models σ K →
      nameAction.Models σ (res label C (rootCommAt ρ first second m₁ m₂)).knowledge)
    (madeReads : ∀ σ : PSubst, nameAction.Models σ K →
        NameLaws (psubst σ ((res label C (rootCommAt ρ first second m₁ m₂)).label m₁))
          (psubst σ (atLoc (predotU A') rootLoc)) ∧
        NameLaws (psubst σ ((res label C (rootCommAt ρ first second m₁ m₂)).label m₂))
          (psubst σ (atLoc (predotU B') rootLoc))) :
    RootCells (res label C (rootCommAt ρ first second m₁ m₂)).label
      ⟨K, (resConf label C (rootCommAt ρ first second m₁ m₂)).present⟩
      ((pre ++ mid ++ post) ++ [(m₁, A'), (m₂, B')]) := by
  obtain ⟨_, shapes, enabled, -⟩ := (RuleSyntax.admits_iff _).mp admitted
  have madeDistinct : m₁ ≠ m₂ := by
    simpa [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection] using shapes.2.1
  have freshMade : m₁ ∉ C.present ∧ m₂ ∉ C.present := by
    simpa [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, Selection.commit,
      embed] using enabled.fresh
  have permOld : ((pre ++ (first, p₁) :: (mid ++ (second, p₂) :: post)).map Prod.fst).Perm
      (first :: second :: (pre ++ mid ++ post).map Prod.fst) := by
    simp only [List.map_append, List.map_cons]
    exact List.perm_middle.trans
      (List.Perm.cons _ (by rw [← List.append_assoc]; exact List.perm_middle))
  obtain ⟨firstOut, ndFront⟩ := List.nodup_cons.mp (permOld.nodup_iff.mp inv.nodup)
  obtain ⟨secondOut, restNd⟩ := List.nodup_cons.mp ndFront
  have restInOld : ∀ q ∈ pre ++ mid ++ post,
      q ∈ pre ++ (first, p₁) :: (mid ++ (second, p₂) :: post) := by
    intro q m; simp only [List.mem_append, List.mem_cons] at m ⊢
    rcases m with (h | h) | h
    · exact .inl h
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inr h)))
  have nodupNew : (((pre ++ mid ++ post) ++ [(m₁, A'), (m₂, B')]).map Prod.fst).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨restNd, by simp [madeDistinct], fun a inRest b inMade ab => ?_⟩
    obtain ⟨q, qIn, rfl⟩ := List.mem_map.mp inRest
    have qPres := (inv.rows q (restInOld q qIn)).1
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at inMade
    rcases inMade with rfl | rfl
    · exact freshMade.1 (ab ▸ qPres)
    · exact freshMade.2 (ab ▸ qPres)
  refine ⟨nodupNew, fun q qIn => ?_, fun x xPres xNotNew σ solved y same => ?_⟩
  · rcases List.mem_append.mp qIn with inRest | inMade
    · have qOld := restInOld q inRest
      have qPres := (inv.rows q qOld).1
      have neF : q.1 ≠ first := fun e =>
        firstOut (e ▸ List.mem_cons.mpr (.inr (List.mem_map.mpr ⟨q, inRest, rfl⟩)))
      have neS : q.1 ≠ second := fun e => secondOut (e ▸ List.mem_map.mpr ⟨q, inRest, rfl⟩)
      have ne₁ : q.1 ≠ m₁ := fun e => freshMade.1 (e ▸ qPres)
      have ne₂ : q.1 ≠ m₂ := fun e => freshMade.2 (e ▸ qPres)
      refine ⟨(result_present _ q.1).mpr (.inl ⟨qPres, by
        simp [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, neF, neS]⟩),
        fun σ solved => ?_⟩
      rw [result_label_old _ (by
        simp [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, ne₁, ne₂])]
      exact (inv.rows q qOld).2 σ (info_known _ (refines σ solved))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at inMade
      rcases inMade with rfl | rfl
      · exact ⟨(result_present _ m₁).mpr (.inr (by
          simp [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection])),
          fun σ s => (madeReads σ s).1⟩
      · exact ⟨(result_present _ m₂).mpr (.inr (by
          simp [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection])),
          fun σ s => (madeReads σ s).2⟩
  · rcases result_row xPres with made | ⟨old, notTaken, -, labelOld⟩
    · simp only [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection,
        List.mem_cons, List.not_mem_nil, or_false] at made
      rcases made with rfl | rfl <;> exact xNotNew (by simp)
    · rw [labelOld] at same
      have neF : x ≠ first := fun e => notTaken (by
        simp [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, e])
      have neS : x ≠ second := fun e => notTaken (by
        simp [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, e])
      refine inv.others x old (fun inOld => ?_) σ (info_known _ (refines σ solved)) y same
      have inPerm := permOld.subset inOld
      simp only [List.mem_cons] at inPerm
      rcases inPerm with rfl | rfl | inRest
      · exact neF rfl
      · exact neS rfl
      · exact xNotNew (by rw [List.map_append]; exact List.mem_append_left _ inRest)

theorem rootCells_replace_comm {label : O → Pattern} {C : Configuration Pattern O}
    {pre mid post : List (O × Pattern)} {first second m₁ m₂ : O} {p₁ p₂ A' B' : Pattern}
    {ρ : PSubst}
    (inv : RootCells label C (pre ++ (first, p₁) :: (mid ++ (second, p₂) :: post)))
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (rootCommAt ρ first second m₁ m₂))
    (madeReads : ∀ σ : PSubst,
      nameAction.Models σ (res label C (rootCommAt ρ first second m₁ m₂)).knowledge →
        NameLaws (psubst σ ((res label C (rootCommAt ρ first second m₁ m₂)).label m₁))
          (psubst σ (atLoc (predotU A') rootLoc)) ∧
        NameLaws (psubst σ ((res label C (rootCommAt ρ first second m₁ m₂)).label m₂))
          (psubst σ (atLoc (predotU B') rootLoc))) :
    RootCells (res label C (rootCommAt ρ first second m₁ m₂)).label
      (resConf label C (rootCommAt ρ first second m₁ m₂))
      ((pre ++ mid ++ post) ++ [(m₁, A'), (m₂, B')]) :=
  rootCells_replace_comm_under inv admitted (fun _ h => h) madeReads

/-- The written commit reads as a conventional source COMM. Its
continuations are forced by the actual tells at every solution, even
when name-frame unification alone would also permit a different result. -/
theorem rootCells_written_comm {label : O → Pattern} {C : Configuration Pattern O}
    {pre mid post : List (O × Pattern)} {first second m₁ m₂ : O}
    {t u x y A B : Pattern} {ρ : PSubst}
    (policy : ReflLocatedStep.Ownership.GuardPolicy)
    (authored : ReflLocatedStep.Ownership.Store O → Option O → List (O × Pattern))
    (ledger : LocatedSubstitution.Authority.Ledger O ReflLocatedStep.Ownership.Phase)
    (inv : RootCells label C
      (pre ++ (first, pFor t x A) :: (mid ++ (second, pFor u y B) :: post)))
    (writtenHere : authored (ReflLocatedStep.Ownership.Store.plain (embed label C) ledger) none =
      pre ++ (first, pFor t x A) :: (mid ++ (second, pFor u y B) :: post))
    (admitted : (ReflLocatedStep.Ownership.withWrittenComm policy authored).Admits
      (s := (ReflLocatedStep.Ownership.Store.plain (embed label C) ledger)) ⟨rootCommAt ρ first second m₁ m₂, .rootComm, rfl⟩) :
    ∃ bs, ReflLocatedStep.Ownership.writtenBinding (s := (ReflLocatedStep.Ownership.Store.plain (embed label C) ledger))
        (authored (ReflLocatedStep.Ownership.Store.plain (embed label C) ledger))
        ⟨rootCommAt ρ first second m₁ m₂, .rootComm, rfl⟩ = some bs ∧
      let completed := MeTTaCalculus.Corrected.completeBindings (pvars t ++ pvars u) bs
      let oldRows := pre ++ (first, pFor t x A) :: (mid ++ (second, pFor u y B) :: post)
      let newRows := (pre ++ mid ++ post) ++ [(m₁, applyDot completed A), (m₂, applyDot completed B)]
      let after := (ReflLocatedStep.Ownership.withWrittenComm policy authored).result _ admitted
      RootCells after.raw.label ⟨after.raw.knowledge, after.raw.present⟩ newRows ∧
        BagStep conventional (rootBagProcess oldRows) (rootBagProcess newRows) := by
  let f : ReflLocatedStep.Ownership.Candidate (ReflLocatedStep.Ownership.Store.plain (embed label C) ledger) :=
    ⟨rootCommAt ρ first second m₁ m₂, .rootComm, rfl⟩
  obtain ⟨armed, allowed⟩ := (ReflLocatedStep.Ownership.written_comm_admits_iff policy authored f).mp admitted
  obtain ⟨bs, receipt⟩ := Option.isSome_iff_exists.mp allowed
  have inFirst : (first, pFor t x A) ∈ pre ++ (first, pFor t x A) :: (mid ++ (second, pFor u y B) :: post) :=
    by simp
  have inSecond : (second, pFor u y B) ∈ pre ++ (first, pFor t x A) :: (mid ++ (second, pFor u y B) :: post) :=
    by simp
  have writtenFirst : (authored (ReflLocatedStep.Ownership.Store.plain (embed label C) ledger) none).lookup first = some (pFor t x A) := by
    rw [writtenHere]
    exact LocatedSubstitution.Authority.lookup_write _ inv.nodup inFirst
  have writtenSecond : (authored (ReflLocatedStep.Ownership.Store.plain (embed label C) ledger) none).lookup second = some (pFor u y B) := by
    rw [writtenHere]
    exact LocatedSubstitution.Authority.lookup_write _ inv.nodup inSecond
  have checked := ReflLocatedStep.Ownership.writtenBinding_root (authored (ReflLocatedStep.Ownership.Store.plain (embed label C) ledger))
    (f := f) rfl rfl writtenFirst writtenSecond
  rw [checked] at receipt
  obtain ⟨rfl, apart, found⟩ := (ReflLocatedStep.Ownership.writtenComm_pFor_iff t x A u y B bs).mp receipt
  let completed := MeTTaCalculus.Corrected.completeBindings (pvars t ++ pvars u) bs
  refine ⟨bs, checked.trans receipt, ?_, ?_⟩
  · have base := ReflLocatedStep.Ownership.admits_without_comm_tells policy _ (Or.inl rfl) armed
    have raw : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) f.raw := by
      cases policy <;> exact base.1
    have madeDistinct : m₁ ≠ m₂ := by
      have shapes := ((RuleSyntax.admits_iff _).mp raw).2.1
      simpa [f, rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection] using
        shapes.2.1
    have tells := (ReflLocatedStep.Ownership.readWrittenPair_root
      (authored (ReflLocatedStep.Ownership.Store.plain (embed label C) ledger)) (f := f)
      (ReflLocatedStep.Ownership.writtenPairTells f.raw.opening) rfl rfl writtenFirst writtenSecond).trans
        (ReflLocatedStep.Ownership.writtenPairTells_at ρ receipt)
    let K := ((ReflLocatedStep.Ownership.withWrittenComm policy authored).result f admitted).raw.knowledge
    change RootCells (res label C (rootCommAt ρ first second m₁ m₂)).label
      ⟨K, (resConf label C (rootCommAt ρ first second m₁ m₂)).present⟩ _
    have cut (σ : PSubst) (solved : nameAction.Models σ K) :=
      ReflLocatedStep.Ownership.written_result_models policy authored admitted solved
    refine rootCells_replace_comm_under inv raw (fun σ solved => (cut σ solved).1) fun σ solved => ?_
    obtain ⟨left, right⟩ := rootComm_result_labels label C ρ first second m₁ m₂ madeDistinct
    have published := ReflLocatedStep.Ownership.written_result_publications policy authored admitted
      tells left right solved
    simpa only [psubst_atLoc_any, psubst_rootLoc,
      ReflLocatedStep.Ownership.written_result_label] using published
  · have principal := MeTTaCalculus.Corrected.principal_completeBindings
      (MeTTaCalculus.Corrected.unify_principal found)
    simpa [rootBagProcess, List.map_append] using
      bagStep_of_pPar_principal_comm (pre.map Prod.snd) (mid.map Prod.snd) (post.map Prod.snd)
        t u x A B completed principal (admit := conventional) apart

/-- **Forward root COMM on `RootCells`** (under Step 1' hypotheses + `PlainPatterns` on `applyDot`
reducts): fires `rootCommAt` in one step and realizes both `BagStep` and `CanonicalBagStep`. -/
theorem rootCells_comm_forward {label : O → Pattern} {C : Configuration Pattern O}
    {pre mid post : List (O × Pattern)} {first second m₁ m₂ : O}
    {t u ch A B : Pattern} {bs : Bindings}
    (inv : RootCells label C
      (pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch B) :: post)))
    (noBT : binders t = []) (noBU : binders u = [])
    (groundCh : pvars ch = []) (noBA : binders A = []) (noBB : binders B = [])
    (plainOutA : PlainPatterns (applyDot bs A)) (plainOutB : PlainPatterns (applyDot bs B))
    (gp : GroundPrincipal t u bs) (convention : Apart t A u B)
    (foA : firstOrder A = true) (foB : firstOrder B = true)
    (groundT : groundBags t = true) (groundU : groundBags u = true)
    (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u)
    (madeDistinct : m₁ ≠ m₂) (fresh₁ : m₁ ∉ C.present) (fresh₂ : m₂ ∉ C.present)
    {σ₀ : PSubst} (known₀ : nameAction.Models σ₀ C.equations)
    (unifies : NameLaws (psubst σ₀ t) (psubst σ₀ u))
    {ρ : PSubst} (opensFreshly : (rootCommAt ρ first second m₁ m₂).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
        (rootCommAt ρ first second m₁ m₂) ∧
      RootCells (res label C (rootCommAt ρ first second m₁ m₂)).label
        (resConf label C (rootCommAt ρ first second m₁ m₂))
        ((pre ++ mid ++ post) ++ [(m₁, applyDot bs A), (m₂, applyDot bs B)]) ∧
      BagStep conventional
        (rootBagProcess (pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch B) :: post)))
        (rootBagProcess ((pre ++ mid ++ post) ++ [(m₁, applyDot bs A), (m₂, applyDot bs B)])) ∧
      CanonicalBagStep conventional
        (rootBagProcess (pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch B) :: post)))
        (rootBagProcess ((pre ++ mid ++ post) ++ [(m₁, applyDot bs A), (m₂, applyDot bs B)])) := by
  have permOld :
      ((pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch B) :: post)).map Prod.fst).Perm
        (first :: second :: (pre ++ mid ++ post).map Prod.fst) := by
    simp only [List.map_append, List.map_cons]
    exact List.perm_middle.trans
      (List.Perm.cons _ (by rw [← List.append_assoc]; exact List.perm_middle))
  have distinct : first ≠ second := fun eqFS =>
    (List.nodup_cons.mp (permOld.nodup_iff.mp inv.nodup)).1 (by simp [eqFS])
  have rF : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (atLoc (predot (pFor t ch A)) rootLoc)) := by
    intro σ s; have r := (inv.rows (first, pFor t ch A) (by simp)).2 σ s
    rwa [predotU_pFor_eq_predot_plain noBT groundCh noBA] at r
  have rS : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (atLoc (predot (pFor u ch B)) rootLoc)) := by
    intro σ s; have r := (inv.rows (second, pFor u ch B) (by simp)).2 σ s
    rwa [predotU_pFor_eq_predot_plain noBU groundCh noBB] at r
  obtain ⟨adm, reads⟩ := rootComm_commit_mixed label C t u ch A B bs gp convention foA foB
    groundT groundU canonicalT canonicalU first second m₁ m₂ rF rS distinct madeDistinct
    (inv.rows (first, pFor t ch A) (by simp)).1 (inv.rows (second, pFor u ch B) (by simp)).1
    fresh₁ fresh₂ known₀ unifies opensFreshly
  have inv' : RootCells (res label C (rootCommAt ρ first second m₁ m₂)).label
      (resConf label C (rootCommAt ρ first second m₁ m₂))
      ((pre ++ mid ++ post) ++ [(m₁, applyDot bs A), (m₂, applyDot bs B)]) :=
    rootCells_replace_comm inv adm fun σ s => by
      obtain ⟨-, b₁, b₂⟩ := reads σ s
      rw [predotU_eq_predot_of_plain (applyDot bs A) plainOutA,
        predotU_eq_predot_of_plain (applyDot bs B) plainOutB]
      exact ⟨b₁, b₂⟩
  exact ⟨adm, inv',
    by simpa [rootBagProcess, List.map_append] using
      bagStep_of_pPar_comm (pre.map Prod.snd) (mid.map Prod.snd) (post.map Prod.snd)
        t u ch A B bs gp convention,
    by simpa [rootBagProcess, List.map_append] using
      canonicalBagStep_of_pPar_comm (pre.map Prod.snd) (mid.map Prod.snd) (post.map Prod.snd)
        t u ch A B bs gp convention⟩

/-- Ground-pattern root COMM on `RootCells`. It compares the patterns at `QN`
and transports the uniform continuation representations, with no binder
restriction on either continuation. -/
theorem rootCells_comm_ground_forward {label : O → Pattern} {C : Configuration Pattern O}
    {pre mid post : List (O × Pattern)} {first second m₁ m₂ : O}
    {t u ch A B : Pattern}
    (inv : RootCells label C
      (pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch B) :: post)))
    (groundT : pvars t = []) (groundU : pvars u = [])
    (samePat : NameLaws (predotU t) (predotU u))
    (groundCh : pvars ch = [])
    (madeDistinct : m₁ ≠ m₂) (fresh₁ : m₁ ∉ C.present) (fresh₂ : m₂ ∉ C.present)
    {σ₀ : PSubst} (known₀ : nameAction.Models σ₀ C.equations)
    {ρ : PSubst} (opensFreshly : (rootCommAt ρ first second m₁ m₂).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
        (rootCommAt ρ first second m₁ m₂) ∧
      RootCells (res label C (rootCommAt ρ first second m₁ m₂)).label
        (resConf label C (rootCommAt ρ first second m₁ m₂))
        ((pre ++ mid ++ post) ++ [(m₁, A), (m₂, B)]) := by
  have permOld :
      ((pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch B) :: post)).map Prod.fst).Perm
        (first :: second :: (pre ++ mid ++ post).map Prod.fst) := by
    simp only [List.map_append, List.map_cons]
    exact List.perm_middle.trans
      (List.Perm.cons _ (by rw [← List.append_assoc]; exact List.perm_middle))
  have distinct : first ≠ second := fun eqFS =>
    (List.nodup_cons.mp (permOld.nodup_iff.mp inv.nodup)).1 (by simp [eqFS])
  have patterns : NameLaws t u := by
    simpa only [ReflUniform.predotU_ground t groundT, ReflUniform.predotU_ground u groundU]
      using samePat
  have rF : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first))
        (psubst σ (atLoc (pFor t ch (predotU A)) rootLoc)) := by
    intro σ s; have r := (inv.rows (first, pFor t ch A) (by simp)).2 σ s
    rwa [ReflUniform.predotU_ground_guard groundT groundCh] at r
  have rS : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second))
        (psubst σ (atLoc (pFor u ch (predotU B)) rootLoc)) := by
    intro σ s; have r := (inv.rows (second, pFor u ch B) (by simp)).2 σ s
    rwa [ReflUniform.predotU_ground_guard groundU groundCh] at r
  obtain ⟨adm, reads⟩ := rootComm_ground_mixed label C t u ch (predotU A) (predotU B)
    groundT groundU patterns first second m₁ m₂ rF rS distinct madeDistinct
    (inv.rows (first, pFor t ch A) (by simp)).1 (inv.rows (second, pFor u ch B) (by simp)).1
    fresh₁ fresh₂ known₀ opensFreshly
  refine ⟨adm, rootCells_replace_comm inv adm fun σ s => ?_⟩
  obtain ⟨-, b₁, b₂⟩ := reads σ s
  exact ⟨b₁, b₂⟩

/-- **Backward root COMM soundness on `RootCells`**. -/
theorem rootCells_comm_backward {label : O → Pattern} {C : Configuration Pattern O}
    {pre mid post : List (O × Pattern)} {first second m₁ m₂ : O} {ρ : PSubst}
    {t u ch ch' A B : Pattern}
    (inv : RootCells label C
      (pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch' B) :: post)))
    (noBT : binders t = []) (noBU : binders u = [])
    (groundCh : pvars ch = []) (groundCh' : pvars ch' = [])
    (canonicalCh : nameCanon ch = ch) (canonicalCh' : nameCanon ch' = ch')
    (noBA : binders A = []) (noBB : binders B = [])
    (unifiable : (∃ σ : PSubst, psubst σ t = psubst σ u) →
      ∃ bs : Bindings, GroundPrincipal t u bs ∧ ∀ y v, bs.lookup y = some v → firstOrder v = true)
    (plainOut : ∀ bs : Bindings,
      (∀ y v, bs.lookup y = some v → firstOrder v = true) →
        PlainPatterns (applyDot bs A) ∧ PlainPatterns (applyDot bs B))
    (convention : Apart t A u B) (foA : firstOrder A = true) (foB : firstOrder B = true)
    (groundT : groundBags t = true) (groundU : groundBags u = true)
    (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (rootCommAt ρ first second m₁ m₂)) :
    ch = ch' ∧ ∃ bs : Bindings,
      RootCells (res label C (rootCommAt ρ first second m₁ m₂)).label
        (resConf label C (rootCommAt ρ first second m₁ m₂))
        ((pre ++ mid ++ post) ++ [(m₁, applyDot bs A), (m₂, applyDot bs B)]) ∧
      BagStep conventional
        (rootBagProcess (pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch' B) :: post)))
        (rootBagProcess ((pre ++ mid ++ post) ++ [(m₁, applyDot bs A), (m₂, applyDot bs B)])) ∧
      CanonicalBagStep conventional
        (rootBagProcess (pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch' B) :: post)))
        (rootBagProcess ((pre ++ mid ++ post) ++ [(m₁, applyDot bs A), (m₂, applyDot bs B)])) := by
  obtain ⟨fresh, shapes, enabled, ⟨_, w, solved⟩, _, _⟩ := (RuleSyntax.admits_iff _).mp admitted
  have distinct : first ≠ second := by
    simpa [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection] using shapes.1
  have madeDistinct : m₁ ≠ m₂ := by
    simpa [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection] using shapes.2.1
  have rF : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (atLoc (predot (pFor t ch A)) rootLoc)) := by
    intro σ s; have r := (inv.rows (first, pFor t ch A) (by simp)).2 σ s
    rwa [predotU_pFor_eq_predot_plain noBT groundCh noBA] at r
  have rS : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (atLoc (predot (pFor u ch' B)) rootLoc)) := by
    intro σ s; have r := (inv.rows (second, pFor u ch' B) (by simp)).2 σ s
    rwa [predotU_pFor_eq_predot_plain noBU groundCh' noBB] at r
  have rF' : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first))
        (psubst σ (atLoc (pFor t (predot ch) (dotted (pvars t) (predot A))) rootLoc)) :=
    fun σ s => by have r := rF σ s; rwa [predot_pFor] at r
  have rS' : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second))
        (psubst σ (atLoc (pFor u (predot ch') (dotted (pvars u) (predot B))) rootLoc)) :=
    fun σ s => by have r := rS σ s; rwa [predot_pFor] at r
  obtain ⟨knownW, unifyW, chanW, -, -⟩ := rootComm_reads_raw label C t u (predot ch) (predot ch')
    (dotted (pvars t) (predot A)) (dotted (pvars u) (predot B)) first second m₁ m₂ rF' rS'
    madeDistinct ρ solved
  rw [predot_ground ch groundCh, predot_ground ch' groundCh',
    psubst_of_pvars_nil w ch groundCh, psubst_of_pvars_nil w ch' groundCh'] at chanW
  have sameCh : ch = ch' := by
    have canon := (nameLaws_iff ch ch').mp chanW; rwa [canonicalCh, canonicalCh'] at canon
  subst sameCh
  obtain ⟨bs, gp, values⟩ := unifiable
    ⟨_, canonSubst_unifies groundT groundU canonicalT canonicalU (bagLaws_of_nameLaws unifyW)⟩
  have freshMade : m₁ ∉ C.present ∧ m₂ ∉ C.present := by
    simpa [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, Selection.commit,
      embed] using enabled.fresh
  obtain ⟨-, reads⟩ := rootComm_commit_mixed label C t u ch A B bs gp convention foA foB
    groundT groundU canonicalT canonicalU first second m₁ m₂ rF rS distinct madeDistinct
    (inv.rows (first, pFor t ch A) (by simp)).1 (inv.rows (second, pFor u ch B) (by simp)).1
    freshMade.1 freshMade.2 knownW unifyW fresh
  obtain ⟨plA, plB⟩ := plainOut bs values
  have inv' : RootCells (res label C (rootCommAt ρ first second m₁ m₂)).label
      (resConf label C (rootCommAt ρ first second m₁ m₂))
      ((pre ++ mid ++ post) ++ [(m₁, applyDot bs A), (m₂, applyDot bs B)]) :=
    rootCells_replace_comm inv admitted fun σ s => by
      obtain ⟨-, b₁, b₂⟩ := reads σ s
      rw [predotU_eq_predot_of_plain (applyDot bs A) plA,
        predotU_eq_predot_of_plain (applyDot bs B) plB]
      exact ⟨b₁, b₂⟩
  exact ⟨rfl, bs, inv',
    by simpa [rootBagProcess, List.map_append] using
      bagStep_of_pPar_comm (pre.map Prod.snd) (mid.map Prod.snd) (post.map Prod.snd)
        t u ch A B bs gp convention,
    by simpa [rootBagProcess, List.map_append] using
      canonicalBagStep_of_pPar_comm (pre.map Prod.snd) (mid.map Prod.snd) (post.map Prod.snd)
        t u ch A B bs gp convention⟩

/-- Root-row replacement uses enabledness and the token and listener
readouts; it does not depend on which guard view admitted the close. -/
theorem rootCells_closeRoot_of_enabled {label : O → Pattern} {C : Configuration Pattern O}
    {pre post : List (O × Pattern)} {reflOcc d made : O} {x P_sub listenerTerm : Pattern}
    {ρ : PSubst}
    (inv : RootCells label C (pre ++ (reflOcc, pReflect x P_sub) :: post))
    (dReads : ∃ σ₀ : PSubst, nameAction.Models σ₀ C.equations ∧
      ∃ l' m' c', NameLaws (psubst σ₀ (label d)) (doneTok l' m' c'))
    (enabled : Enabled (fun _ : O => ()) C.present
      ((closeRootAt ρ reflOcc d made).selection.commit (T := Unit)))
    (madeReads : ∀ σ : PSubst,
      nameAction.Models σ (res label C (closeRootAt ρ reflOcc d made)).knowledge →
        NameLaws (psubst σ ((res label C (closeRootAt ρ reflOcc d made)).label made))
          (psubst σ (atLoc (predotU listenerTerm) rootLoc))) :
    RootCells (res label C (closeRootAt ρ reflOcc d made)).label
        (resConf label C (closeRootAt ρ reflOcc d made))
        (pre ++ (made, listenerTerm) :: post) := by
  have madeFresh : made ∉ C.present := fun inC =>
    Finset.disjoint_left.mp enabled.fresh (by simp [closeRootAt, Selection.commit]) inC
  have permOld : ((pre ++ (reflOcc, pReflect x P_sub) :: post).map Prod.fst).Perm
      (reflOcc :: (pre ++ post).map Prod.fst) := by
    simp only [List.map_append, List.map_cons]; exact List.perm_middle
  obtain ⟨rOut, restNodup⟩ := List.nodup_cons.mp (permOld.nodup_iff.mp inv.nodup)
  have permNew : ((pre ++ (made, listenerTerm) :: post).map Prod.fst).Perm
      (made :: (pre ++ post).map Prod.fst) := by
    simp only [List.map_append, List.map_cons]; exact List.perm_middle
  have restInOld : ∀ q ∈ pre ++ post, q ∈ pre ++ (reflOcc, pReflect x P_sub) :: post := fun q m =>
    (List.mem_append.mp m).elim (List.mem_append_left _)
      (fun r => List.mem_append_right _ (List.mem_cons_of_mem _ r))
  have dNotRoot : d ∉ (pre ++ (reflOcc, pReflect x P_sub) :: post).map Prod.fst := by
    intro inOld; obtain ⟨q, qIn, eqD⟩ := List.mem_map.mp inOld
    obtain ⟨σ₀, s₀, l', m', c', dTok⟩ := dReads
    have rAt := (inv.rows q qIn).2 σ₀ s₀; rw [eqD, psubst_atLoc_any] at rAt
    exact absurd (nameLaws_heads (rAt.symm.trans dTok)) (by decide)
  have nodupNew : ((pre ++ (made, listenerTerm) :: post).map Prod.fst).Nodup := by
    refine permNew.nodup_iff.mpr (List.nodup_cons.mpr ⟨fun inR => ?_, restNodup⟩)
    obtain ⟨q, qIn, eqM⟩ := List.mem_map.mp inR
    exact madeFresh (eqM ▸ (inv.rows q (restInOld q qIn)).1)
  have keepRest : ∀ q ∈ pre ++ post,
      q.1 ∈ (res label C (closeRootAt ρ reflOcc d made)).present ∧
      ∀ σ : PSubst, nameAction.Models σ (resConf label C (closeRootAt ρ reflOcc d made)).equations →
        NameLaws (psubst σ ((res label C (closeRootAt ρ reflOcc d made)).label q.1))
          (psubst σ (atLoc (predotU q.2) rootLoc)) := by
    intro q qRest
    have qOld := restInOld q qRest
    have qPres := (inv.rows q qOld).1
    have neR : q.1 ≠ reflOcc := fun e => rOut (e ▸ List.mem_map.mpr ⟨q, qRest, rfl⟩)
    have neD : q.1 ≠ d := fun e => dNotRoot (e ▸ List.mem_map.mpr ⟨q, qOld, rfl⟩)
    have neM : q.1 ≠ made := fun e => madeFresh (e ▸ qPres)
    refine ⟨(result_present _ q.1).mpr (.inl ⟨qPres, by simp [closeRootAt, neR, neD]⟩),
      fun σ solved => ?_⟩
    rw [result_label_old _ (by simp [closeRootAt, neM])]
    exact (inv.rows q qOld).2 σ (info_known _ solved)
  refine ⟨nodupNew, fun q qIn => ?_, fun o oPres notNew σ solved y same => ?_⟩
  · simp only [List.mem_append, List.mem_cons] at qIn
    rcases qIn with inPre | rfl | inPost
    · exact keepRest q (List.mem_append_left _ inPre)
    · exact ⟨(result_present _ made).mpr (.inr (by simp [closeRootAt])), madeReads⟩
    · exact keepRest q (List.mem_append_right _ inPost)
  · rcases result_row oPres with isMade | ⟨old, notTaken, -, labelOld⟩
    · simp only [closeRootAt, List.mem_singleton] at isMade; subst isMade; exact notNew (by simp)
    · rw [labelOld] at same
      have neR : o ≠ reflOcc := fun e => notTaken (by simp [closeRootAt, e])
      refine inv.others o old (fun inOld => ?_) σ (info_known _ solved) y same
      rcases List.mem_cons.mp (permOld.subset inOld) with rfl | inRest
      · exact neR rfl
      · obtain ⟨q, qIn, eqO⟩ := List.mem_map.mp inRest
        apply notNew
        rcases List.mem_append.mp qIn with l | r
        · exact List.mem_map.mpr ⟨q, List.mem_append_left _ l, eqO⟩
        · exact List.mem_map.mpr ⟨q, List.mem_append_right _ (List.mem_cons_of_mem _ r), eqO⟩

/-- A whole-store close is one instance of the same root-row replacement. -/
theorem rootCells_closeRoot {label : O → Pattern} {C : Configuration Pattern O}
    {pre post : List (O × Pattern)} {reflOcc d made : O} {x P_sub listenerTerm : Pattern} {ρ : PSubst}
    (inv : RootCells label C (pre ++ (reflOcc, pReflect x P_sub) :: post))
    (dReads : ∃ σ₀ : PSubst, nameAction.Models σ₀ C.equations ∧
      ∃ l' m' c', NameLaws (psubst σ₀ (label d)) (doneTok l' m' c'))
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) (closeRootAt ρ reflOcc d made))
    (madeReads : ∀ σ : PSubst, nameAction.Models σ (res label C (closeRootAt ρ reflOcc d made)).knowledge →
      NameLaws (psubst σ ((res label C (closeRootAt ρ reflOcc d made)).label made))
        (psubst σ (atLoc (predotU listenerTerm) rootLoc))) :
    RootCells (res label C (closeRootAt ρ reflOcc d made)).label
      (resConf label C (closeRootAt ρ reflOcc d made)) (pre ++ (made, listenerTerm) :: post) :=
  rootCells_closeRoot_of_enabled inv dReads admitted.2.1 madeReads

end RootBag

#print axioms freeOnPats_of_extends
#print axioms freeOnPats_after_comm_extends
#print axioms bagStep_of_pPar_comm
#print axioms canonicalBagStep_of_pPar_comm
#print axioms bagStep_of_pPar_refl
#print axioms canonicalBagStep_of_pPar_refl
#print axioms noRootTokens_preserved
#print axioms rootCells_keep_nonRoot
#print axioms rootCells_heat
#print axioms rootCells_heat_reflects
#print axioms root_heating_live
#print axioms rootCells_clear
#print axioms rootCells_clear_reflects
#print axioms rootCells_comm_forward
#print axioms rootCells_comm_ground_forward
#print axioms rootCells_comm_backward
#print axioms rootCells_closeRoot

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem
