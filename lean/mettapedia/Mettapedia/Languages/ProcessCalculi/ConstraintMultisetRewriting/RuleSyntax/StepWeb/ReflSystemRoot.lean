import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystemIsolation
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedCongruence
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedReflection

/-!
# Uniform pre-dotting bridges, solution-extension freedom, and mixed-state root firings

This module establishes the first half of milestone P3 at the name frame `QN`:

* **Uniform pre-dotting bridges** (`predotU_of_binders_nil`, `predotU_pFor_eq_predot`,
  `predotU_named_listener`, `predotU_closed_listener`, `PlainPatterns`,
  `predotU_eq_predot_of_plain`): for every input with ground channel and binder-free continuation,
  `predotU (pFor t x A) = predot (pFor (predotU t) x A)` (and equals `predot (pFor t x A)`
  whenever `binders t = []`). Both named-quote listeners `pFor (tProc R) x pZero` (Interface **N**,
  variables included) and closed-quote listeners `Corrected.listener x R` (Interface **C**) are
  represented uniformly by `predotU`.
* **Semantic solution-extension freedom** (`FreeOnPats`, `freeOnPats_unifies`,
  `freeOnPats_glue_unifier`, `SpineHasPattern`, `row_extends_target`): replaces syntactic
  `storePVars` avoidance (which fails once `openRoot` records a reflected process in `C.equations`)
  by semantic pattern-instantiation freedom modulo `NameLaws`, preserved across every admitted
  firing via `Mentions` amalgamation.
* **Mixed-state root firings of `located` at `QN`** (`rootClearAt`, `rootHeatAt`, `rootCommAt`):
  canonical normal forms (`eq_rootCommAt`, `eq_rootHeatAt`, `eq_rootClearAt`), admission,
  solution-wise readouts, ground-pattern COMM (`rootComm_ground_mixed`, needing no `bagCanon t = t`
  for Interface **C** listeners), backward COMM soundness (`rootComm_sound_mixed`), and solution
  extension (`rootClear_extends`, `rootHeat_extends`, `rootComm_extends`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar nQuote tProc pReflect
  applyDot)
open MeTTaOperationsComm (psubst PSubst pvars psubst_none psubst_congr psubst_of_pvars_nil
  psubst_pFor psubst_tProc psubst_pZero commSelection dotted GroundPrincipal firstOrder)
open MeTTaCalculus.Corrected (binders binders_apply bindersFor_cons3 bindersFor_short Apart
  psubstList_eq_map canonicalBag)
open FiniteProgram (commRule heatRule clearRule commRule_mem heatRule_mem clearRule_mem program
  leftPart rightPart firstPattern secondPattern channelUnknown firstBody secondBody
  commInstance commInstance_firstPattern commInstance_secondPattern commInstance_channel
  commInstance_firstBody commInstance_secondBody parts BagComm predot predot_apply predotFor_cons3
  predotFor_short predotList_eq_map predot_pFor predot_ground predot_of_binders_nil dotted_nil
  keys_of_apart)
open Comm (Tm X E renameBy ruleVars)
open OneFrame (embed)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open ReflQuotient (BagLaws bagCanon groundBags agrees_of_groundPrincipal canonSubst_unifies)
open ReflNames (NameLaws nameAction QN QNE nameCanon nameFiring fresh_name commAtN
  nameLaws_pFor_iff nameLaws_pair_left nameLaws_pair_iff bagLaws_of_nameLaws
  dotted_reads_predot_name)
open ReflLocated (atLoc rootLoc atRule rootRules_sub rootFiring atFiring widen located heatN
  psubst_rootLoc psubst_atLoc_any psubst_par locatedFrame_name)
open ReflLocatedStep (res resConf info_known take_reads psubst_pReflect nameLaws_pReflect_iff)
open ReflUniform (predotU predotU_apply predotUFor_cons3 predotUFor_short predotU_pFor
  predotU_tProc predotU_pZero predotU_pPar pvars_predotU predotU_canonicalBag predotU_ground)

/-! ## Uniform pre-dotting bridges for inputs, reflections, and listeners -/

theorem predotU_par (a b : Pattern) : predotU (par a b) = par (predotU a) (predotU b) := by
  simp [par, predotU_pPar]

theorem predotU_pReflect (x p : Pattern) :
    predotU (pReflect x p) = pReflect (predotU x) (predotU p) := by
  simp [pReflect, predotU_apply]

/-- **Every pattern with `binders p = []` is fixed by `predotU`.** -/
theorem predotU_of_binders_nil (p : Pattern) (noBinders : binders p = []) : predotU p = p := by
  revert noBinders
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, binders q = [] → predotU q = q) with
  | bvar _ => intro _; rfl
  | fvar _ => intro _; rfl
  | apply c args ih =>
      intro noBinders
      rw [binders_apply] at noBinders
      rw [predotU_apply]
      congr 1
      split_ifs at noBinders ⊢ with isFor
      · match args, ih, noBinders with
        | t :: x :: k :: rest, ih, noBinders =>
            rw [bindersFor_cons3] at noBinders
            simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at noBinders
            obtain ⟨⟨⟨tGround, xNone⟩, kNone⟩, restNone⟩ := noBinders
            rw [predotUFor_cons3, predotU_ground t tGround, tGround, dotted_nil,
              ih x (by simp) xNone, ih k (by simp) kNone]
            have restSame : rest.map predotU = rest := by
              conv => rhs; rw [← List.map_id rest]
              exact List.map_congr_left fun q m => ih q (by simp [m]) (restNone q m)
            rw [restSame]
        | [], _, _ => rfl
        | [p], ih, noBinders =>
            rw [bindersFor_short [p] (by simp), List.flatMap_eq_nil_iff] at noBinders
            rw [predotUFor_short [p] (by simp)]
            conv => rhs; rw [← List.map_id [p]]
            exact List.map_congr_left fun q m => ih q m (noBinders q m)
        | [p, q], ih, noBinders =>
            rw [bindersFor_short [p, q] (by simp), List.flatMap_eq_nil_iff] at noBinders
            rw [predotUFor_short [p, q] (by simp)]
            conv => rhs; rw [← List.map_id [p, q]]
            exact List.map_congr_left fun r m => ih r m (noBinders r m)
      · rw [List.flatMap_eq_nil_iff] at noBinders
        conv => rhs; rw [← List.map_id args]
        exact List.map_congr_left fun q m => ih q m (noBinders q m)
  | lambda nm body ih =>
      intro noBinders
      simp only [predotU]
      rw [ih (by simpa [binders] using noBinders)]
  | multiLambda n nms body ih =>
      intro noBinders
      simp only [predotU]
      rw [ih (by simpa [binders] using noBinders)]
  | subst body repl ihb ihr =>
      intro noBinders
      have both : binders body = [] ∧ binders repl = [] := by simpa [binders] using noBinders
      simp only [predotU, ihb both.1, ihr both.2]
  | collection ct elems rest ih =>
      intro noBinders
      have each : ∀ q ∈ elems, binders q = [] := by
        have flat : elems.flatMap binders = [] := by
          simpa [binders, MeTTaCalculus.Corrected.bindersList_eq_flatMap] using noBinders
        exact List.flatMap_eq_nil_iff.mp flat
      simp only [predotU, ReflUniform.predotUList_eq_map]
      congr 1
      conv => rhs; rw [← List.map_id elems]
      exact List.map_congr_left fun q m => ih q m (each q m)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q m noQ
      rcases List.mem_cons.mp m with rfl | later
      · exact head noQ
      · exact tail q later noQ

/-- **Every input with ground channel and binder-free continuation satisfies
`predotU (pFor t x A) = predot (pFor (predotU t) x A)`.** -/
theorem predotU_pFor_eq_predot {t x A : Pattern} (groundX : pvars x = [])
    (noBindersA : binders A = []) :
    predotU (pFor t x A) = predot (pFor (predotU t) x A) := by
  rw [predotU_pFor, predot_pFor, predotU_ground x groundX, predot_ground x groundX,
    predotU_of_binders_nil A noBindersA, predot_of_binders_nil A noBindersA, pvars_predotU]

/-- When `binders t = []` as well, `predotU (pFor t x A) = predot (pFor t x A)`. -/
theorem predotU_pFor_eq_predot_plain {t x A : Pattern} (noBindersT : binders t = [])
    (groundX : pvars x = []) (noBindersA : binders A = []) :
    predotU (pFor t x A) = predot (pFor t x A) := by
  rw [predotU_pFor_eq_predot groundX noBindersA, predotU_of_binders_nil t noBindersT]

theorem dotted_pZero (vs : List String) : dotted vs pZero = pZero := psubst_pZero _

/-- **Interface N listener representation**: for any reduct `R` (even with bound variables),
`predotU` of the literal listener `for(@R <- x) 0` is `for(@(predotU R) <- x) 0`. -/
theorem predotU_named_listener {x : Pattern} (groundX : pvars x = []) (R : Pattern) :
    predotU (pFor (tProc R) x pZero) = pFor (tProc (predotU R)) x pZero := by
  rw [predotU_pFor, predotU_tProc, predotU_ground x groundX, predotU_pZero, dotted_pZero]

/-- **Interface C listener representation**: `predotU` fixes `Corrected.listener x R`. -/
theorem predotU_closed_listener {x : Pattern} (groundX : pvars x = []) (R : Pattern) :
    predotU (MeTTaCalculus.Corrected.listener x R) = MeTTaCalculus.Corrected.listener x R := by
  unfold MeTTaCalculus.Corrected.listener
  rw [predotU_named_listener groundX, predotU_canonicalBag]

mutual
/-- Every `MFor` subterm of `p` has a binder-free pattern (`binders t = []`). -/
def PlainPatterns : Pattern → Prop
  | .bvar _ => True
  | .fvar _ => True
  | .apply c args =>
      (if c = "MFor" then
        match args with
        | t :: _ :: _ :: _ => binders t = []
        | _ => True
      else True) ∧ PlainPatternsList args
  | .lambda _ body => PlainPatterns body
  | .multiLambda _ _ body => PlainPatterns body
  | .subst body repl => PlainPatterns body ∧ PlainPatterns repl
  | .collection _ elems _ => PlainPatternsList elems

def PlainPatternsList : List Pattern → Prop
  | [] => True
  | q :: qs => PlainPatterns q ∧ PlainPatternsList qs
end

theorem plainPatternsList_iff (ps : List Pattern) :
    PlainPatternsList ps ↔ ∀ q ∈ ps, PlainPatterns q := by
  induction ps with
  | nil => simp [PlainPatternsList]
  | cons q qs ih => simp [PlainPatternsList, ih]

/-- **Whenever every `MFor` pattern in `p` is binder-free (`PlainPatterns p`), `predotU p = predot p`.** -/
theorem predotU_eq_predot_of_plain (p : Pattern) (plain : PlainPatterns p) :
    predotU p = predot p := by
  revert plain
  induction p using Pattern.rec
      (motive_2 := fun ps => PlainPatternsList ps → ∀ q ∈ ps, predotU q = predot q) with
  | bvar _ => intro _; rfl
  | fvar _ => intro _; rfl
  | apply c args ih =>
      intro ⟨headPlain, argsPlain⟩
      rw [predotU_apply, predot_apply]
      congr 1
      split_ifs at headPlain ⊢ with isFor
      · match args, headPlain, argsPlain with
        | t :: x :: k :: rest, noBT, argsPlain =>
            rw [predotUFor_cons3, predotFor_cons3, predotU_of_binders_nil t noBT,
              ih argsPlain x (by simp), ih argsPlain k (by simp)]
            congr 3
            exact List.map_congr_left fun q m => ih argsPlain q (by simp [m])
        | [], _, _ => rfl
        | [p], _, argsPlain =>
            rw [predotUFor_short [p] (by simp), predotFor_short [p] (by simp)]
            exact List.map_congr_left fun q m => ih argsPlain q m
        | [p, q], _, argsPlain =>
            rw [predotUFor_short [p, q] (by simp), predotFor_short [p, q] (by simp)]
            exact List.map_congr_left fun r m => ih argsPlain r m
      · exact List.map_congr_left fun q m => ih argsPlain q m
  | lambda _ _ ih => intro pl; simp only [predotU, predot, ih pl]
  | multiLambda _ _ _ ih => intro pl; simp only [predotU, predot, ih pl]
  | subst _ _ ihb ihr => intro ⟨pb, pr⟩; simp only [predotU, predot, ihb pb, ihr pr]
  | collection _ elems _ ih =>
      intro pl
      simp only [predotU, predot, ReflUniform.predotUList_eq_map, predotList_eq_map]
      congr 1
      exact List.map_congr_left fun q m => ih pl q m
  | nil => simp_all
  | cons q qs head tail =>
      rename_i pl r m
      rcases List.mem_cons.mp m with rfl | later
      · exact head pl.1
      · exact tail pl.2 r later

/-! ## Semantic solution-extension freedom (`FreeOnPats`) -/

/-- **Semantic solution-extension freedom on a list of guard patterns**: every substitution `τ` is
matched modulo `NameLaws` on all patterns in `pats` by some solution `σ` of `K`. -/
def FreeOnPats (pats : List Pattern) (K : EquationStore Pattern) : Prop :=
  ∀ τ : PSubst, ∃ σ : PSubst, nameAction.Models σ K ∧
    ∀ q ∈ pats, NameLaws (psubst σ q) (psubst τ q)

theorem freeOnPats_empty_store (pats : List Pattern) : FreeOnPats pats [] :=
  fun τ => ⟨τ, fun _ m => absurd m List.not_mem_nil, fun _ _ => NameLaws.refl _⟩

theorem freeOnPats_consistent {pats : List Pattern} {K : EquationStore Pattern}
    (free : FreeOnPats pats K) : ∃ σ : PSubst, nameAction.Models σ K := by
  obtain ⟨σ, solved, -⟩ := free (fun _ => none)
  exact ⟨σ, solved⟩

theorem freeOnPats_subset {pats pats' : List Pattern} {K : EquationStore Pattern}
    (sub : ∀ q ∈ pats', q ∈ pats) (free : FreeOnPats pats K) : FreeOnPats pats' K := by
  intro τ
  obtain ⟨σ, solved, agree⟩ := free τ
  exact ⟨σ, solved, fun q m => agree q (sub q m)⟩

/-- **`FreeOnPats` produces a store solution unifying any two syntactically unifiable patterns in
`pats` modulo `NameLaws`.** -/
theorem freeOnPats_unifies {pats : List Pattern} {K : EquationStore Pattern}
    (free : FreeOnPats pats K) {t u : Pattern} {bs : Bindings}
    (inT : t ∈ pats) (inU : u ∈ pats) (solves : psubst bs.lookup t = psubst bs.lookup u) :
    ∃ σ₀ : PSubst, nameAction.Models σ₀ K ∧ NameLaws (psubst σ₀ t) (psubst σ₀ u) := by
  obtain ⟨σ₀, solved, agree⟩ := free bs.lookup
  refine ⟨σ₀, solved, ?_⟩
  have aT := agree t inT
  have aU := agree u inU
  rw [solves] at aT
  exact aT.trans aU.symm

/-- Gluing a unifier `bs` on `t, u` with any substitution `τ` on variable-disjoint remaining
patterns `pats'`. -/
theorem freeOnPats_glue_unifier {pats' : List Pattern} {t u : Pattern} {bs : Bindings}
    (solves : psubst bs.lookup t = psubst bs.lookup u)
    (disj : ∀ q ∈ pats', ∀ v ∈ pvars q, v ∉ pvars t ++ pvars u)
    {K : EquationStore Pattern} (free : FreeOnPats (t :: u :: pats') K) (τ : PSubst) :
    ∃ σ₀ : PSubst, nameAction.Models σ₀ K ∧ NameLaws (psubst σ₀ t) (psubst σ₀ u) ∧
      ∀ q ∈ pats', NameLaws (psubst σ₀ q) (psubst τ q) := by
  let τComb : PSubst := fun v => if v ∈ pvars t ++ pvars u then bs.lookup v else τ v
  have onTU : ∀ p, (∀ v ∈ pvars p, v ∈ pvars t ++ pvars u) →
      psubst τComb p = psubst bs.lookup p := by
    intro p sub
    apply psubst_congr
    intro v m
    dsimp only [τComb]
    rw [if_pos (sub v m)]
  have onRest : ∀ q ∈ pats', psubst τComb q = psubst τ q := by
    intro q qIn
    apply psubst_congr
    intro v m
    dsimp only [τComb]
    rw [if_neg (disj q qIn v m)]
  obtain ⟨σ₀, solved, agree⟩ := free τComb
  have eqTU : psubst τComb t = psubst τComb u := by
    rw [onTU t (fun _ m => List.mem_append_left _ m),
      onTU u (fun _ m => List.mem_append_right _ m)]
    exact solves
  have aT := agree t (by simp)
  have aU := agree u (by simp)
  rw [eqTU] at aT
  refine ⟨σ₀, solved, aT.trans aU.symm, fun q qIn => ?_⟩
  have aQ := agree q (by simp [qIn])
  rw [onRest q qIn] at aQ
  exact aQ

/-- A guard pattern `q` sits at a non-quote spine position of `p` (`par`, `pReflect`, `pFor`). -/
inductive SpineHasPattern (q : Pattern) : Pattern → Prop where
  | guard (x A : Pattern) : SpineHasPattern q (pFor q x A)
  | parLeft {a : Pattern} (b : Pattern) : SpineHasPattern q a → SpineHasPattern q (par a b)
  | parRight (a : Pattern) {b : Pattern} : SpineHasPattern q b → SpineHasPattern q (par a b)
  | reflect (x : Pattern) {sub : Pattern} : SpineHasPattern q sub → SpineHasPattern q (pReflect x sub)

/-- `NameLaws` on any process inverts down to every guard pattern at a spine position. -/
theorem spineHasPattern_nameLaws {q p : Pattern} (has : SpineHasPattern q p) {w τ : PSubst}
    (same : NameLaws (psubst w p) (psubst τ p)) : NameLaws (psubst w q) (psubst τ q) := by
  induction has with
  | guard x A =>
      rw [psubst_pFor, psubst_pFor] at same
      exact (nameLaws_pFor_iff.mp same).1
  | parLeft _ _ ih =>
      rw [psubst_par, psubst_par] at same
      exact ih (nameLaws_pair_iff.mp same).1
  | parRight _ _ ih =>
      rw [psubst_par, psubst_par] at same
      exact ih (nameLaws_pair_iff.mp same).2
  | reflect _ _ ih =>
      rw [psubst_pReflect, psubst_pReflect] at same
      exact ih (nameLaws_pReflect_iff.mp same).2

/-- **The three-step `Mentions` triangle**: if row `o` reads as `atLoc R l` at every solution of
`C.equations`, and a solution `w` of an extended store `K'` (refining `C.equations`) agrees modulo
`NameLaws` with `σ₀` on `label o`, then `w` and `σ₀` agree modulo `NameLaws` on `R` (and hence on
every spine guard pattern inside `R`). -/
theorem row_extends_target {O : Type*} {label : O → Pattern} {C : Configuration Pattern O}
    {o : O} {R l : Pattern}
    (reads : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label o)) (psubst σ (atLoc R l)))
    {K' : EquationStore Pattern}
    (refines : ∀ σ : PSubst, nameAction.Models σ K' → nameAction.Models σ C.equations)
    {w σ₀ : PSubst} (solvedW : nameAction.Models w K') (known₀ : nameAction.Models σ₀ C.equations)
    (onRow : NameLaws (psubst w (label o)) (psubst σ₀ (label o))) :
    NameLaws (psubst w R) (psubst σ₀ R) := by
  have both := (reads w (refines w solvedW)).symm.trans (onRow.trans (reads σ₀ known₀))
  rw [psubst_atLoc_any, psubst_atLoc_any] at both
  exact ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).1

/-! ## Root firings of `located` at `QN` on arbitrary mixed configurations -/

section RootFirings

variable {O : Type*} [DecidableEq O]

/-- Clearing firing of the finite program at the name frame. -/
def clearN (ρ : PSubst) (o : O) : Firing O QNE program PUnit.unit :=
  ⟨clearRule, clearRule_mem, PUnit.unit, ρ, ⟨[o], [], []⟩, []⟩

/-- Root COMM firing of `located` at `QN`. -/
def rootCommAt (ρ : PSubst) (first second m₁ m₂ : O) : Firing O QNE located PUnit.unit :=
  rootFiring (commAtN ρ first second m₁ m₂)

/-- Root heating firing of `located` at `QN`. -/
def rootHeatAt (ρ : PSubst) (o m₁ m₂ : O) : Firing O QNE located PUnit.unit :=
  rootFiring (heatN ρ o m₁ m₂)

/-- Root clearing firing of `located` at `QN`. -/
def rootClearAt (ρ : PSubst) (o : O) : Firing O QNE located PUnit.unit :=
  rootFiring (clearN ρ o)

/-- Syntactic-frame counterparts for fresh-opening lifting. -/
def rootCommAtX (ρ : PSubst) (first second m₁ m₂ : O) : Firing O E located PUnit.unit :=
  ⟨atRule rootLoc commRule, rootRules_sub ⟨commRule, commRule_mem, rfl⟩, PUnit.unit, ρ,
    commSelection first second m₁ m₂, []⟩

def rootHeatAtX (ρ : PSubst) (o m₁ m₂ : O) : Firing O E located PUnit.unit :=
  ⟨atRule rootLoc heatRule, rootRules_sub ⟨heatRule, heatRule_mem, rfl⟩, PUnit.unit, ρ,
    ⟨[o], [], [m₁, m₂]⟩, []⟩

def rootClearAtX (ρ : PSubst) (o : O) : Firing O E located PUnit.unit :=
  ⟨atRule rootLoc clearRule, rootRules_sub ⟨clearRule, clearRule_mem, rfl⟩, PUnit.unit, ρ,
    ⟨[o], [], []⟩, []⟩

omit [DecidableEq O] in
theorem rootComm_fresh_exists (label : O → Pattern) (C : Configuration Pattern O)
    (first second m₁ m₂ : O) :
    ∃ ρ : PSubst, (rootCommAt ρ first second m₁ m₂).Fresh QN (embed label C) := by
  obtain ⟨g, inj, avoids⟩ := Comm.exists_apart_renaming (embed label C)
    (ruleVars (atRule rootLoc commRule))
  refine ⟨renameBy g, ?_⟩
  change (nameFiring (rootCommAtX (renameBy g) first second m₁ m₂)).Fresh QN (embed label C)
  exact fresh_name (Comm.fresh_of_renaming (embed label C)
    (rootCommAtX (renameBy g) first second m₁ m₂) g rfl inj avoids)

omit [DecidableEq O] in
theorem rootHeat_fresh_exists (label : O → Pattern) (C : Configuration Pattern O)
    (o m₁ m₂ : O) :
    ∃ ρ : PSubst, (rootHeatAt ρ o m₁ m₂).Fresh QN (embed label C) := by
  obtain ⟨g, inj, avoids⟩ := Comm.exists_apart_renaming (embed label C)
    (ruleVars (atRule rootLoc heatRule))
  refine ⟨renameBy g, ?_⟩
  change (nameFiring (rootHeatAtX (renameBy g) o m₁ m₂)).Fresh QN (embed label C)
  exact fresh_name (Comm.fresh_of_renaming (embed label C)
    (rootHeatAtX (renameBy g) o m₁ m₂) g rfl inj avoids)

omit [DecidableEq O] in
theorem rootClear_fresh_exists (label : O → Pattern) (C : Configuration Pattern O) (o : O) :
    ∃ ρ : PSubst, (rootClearAt ρ o).Fresh QN (embed label C) := by
  obtain ⟨g, inj, avoids⟩ := Comm.exists_apart_renaming (embed label C)
    (ruleVars (atRule rootLoc clearRule))
  refine ⟨renameBy g, ?_⟩
  change (nameFiring (rootClearAtX (renameBy g) o)).Fresh QN (embed label C)
  exact fresh_name (Comm.fresh_of_renaming (embed label C)
    (rootClearAtX (renameBy g) o) g rfl inj avoids)

private theorem len1_of {α : Type*} {xs : List α} (h : xs.length = 1) : ∃ a, xs = [a] := by
  match xs, h with | [a], _ => exact ⟨a, rfl⟩

private theorem len2_of {α : Type*} {xs : List α} (h : xs.length = 2) : ∃ a b, xs = [a, b] := by
  match xs, h with | [a, b], _ => exact ⟨a, b, rfl⟩

/-- Canonical form of any admitted `atRule rootLoc commRule` firing. -/
theorem eq_rootCommAt {label : O → Pattern} {C : Configuration Pattern O}
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (isRule : g.rule = atRule rootLoc commRule) :
    ∃ first second m₁ m₂, g = rootCommAt g.opening first second m₁ m₂ ∧
      first ≠ second ∧ m₁ ≠ m₂ ∧ first ∈ C.present ∧ second ∈ C.present ∧
      m₁ ∉ C.present ∧ m₂ ∉ C.present := by
  obtain ⟨_, shapes, enabled, -⟩ := (RuleSyntax.admits_iff g).mp admitted
  obtain ⟨rule, member, ext, ρ, ⟨taken, read, made⟩, seen⟩ := g
  cases ext
  simp only at isRule shapes
  subst isRule
  obtain ⟨first, second, rfl⟩ := len2_of shapes.2.2.1.symm
  have readNil : read = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.1.symm
  obtain ⟨m₁, m₂, rfl⟩ := len2_of shapes.2.2.2.2.1.symm
  have seenNil : seen = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.2.2.symm
  subst readNil seenNil
  have subMem : member = rootRules_sub ⟨commRule, commRule_mem, rfl⟩ := Subsingleton.elim _ _
  subst subMem
  have freshMade : m₁ ∉ C.present ∧ m₂ ∉ C.present := by
    simpa [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, Selection.commit,
      embed] using enabled.fresh
  exact ⟨first, second, m₁, m₂, rfl, by simpa using shapes.1, by simpa using shapes.2.1,
    enabled.taken_subset (by simp [Selection.commit]),
    enabled.taken_subset (by simp [Selection.commit]),
    freshMade.1, freshMade.2⟩

/-- Canonical form of any admitted `atRule rootLoc heatRule` firing. -/
theorem eq_rootHeatAt {label : O → Pattern} {C : Configuration Pattern O}
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (isRule : g.rule = atRule rootLoc heatRule) :
    ∃ o m₁ m₂, g = rootHeatAt g.opening o m₁ m₂ ∧ m₁ ≠ m₂ ∧ o ∈ C.present ∧
      m₁ ∉ C.present ∧ m₂ ∉ C.present := by
  obtain ⟨_, shapes, enabled, -⟩ := (RuleSyntax.admits_iff g).mp admitted
  obtain ⟨rule, member, ext, ρ, ⟨taken, read, made⟩, seen⟩ := g
  cases ext
  simp only at isRule shapes
  subst isRule
  obtain ⟨o, rfl⟩ := len1_of shapes.2.2.1.symm
  have readNil : read = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.1.symm
  obtain ⟨m₁, m₂, rfl⟩ := len2_of shapes.2.2.2.2.1.symm
  have seenNil : seen = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.2.2.symm
  subst readNil seenNil
  have subMem : member = rootRules_sub ⟨heatRule, heatRule_mem, rfl⟩ := Subsingleton.elim _ _
  subst subMem
  have freshMade : m₁ ∉ C.present ∧ m₂ ∉ C.present := by
    simpa [rootHeatAt, rootFiring, widen, atFiring, heatN, Selection.commit, embed]
      using enabled.fresh
  exact ⟨o, m₁, m₂, rfl, by simpa using shapes.2.1,
    enabled.taken_subset (by simp [Selection.commit]),
    freshMade.1, freshMade.2⟩

/-- Canonical form of any admitted `atRule rootLoc clearRule` firing. -/
theorem eq_rootClearAt {label : O → Pattern} {C : Configuration Pattern O}
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (isRule : g.rule = atRule rootLoc clearRule) :
    ∃ o, g = rootClearAt g.opening o ∧ o ∈ C.present := by
  obtain ⟨_, shapes, enabled, -⟩ := (RuleSyntax.admits_iff g).mp admitted
  obtain ⟨rule, member, ext, ρ, ⟨taken, read, made⟩, seen⟩ := g
  cases ext
  simp only at isRule shapes
  subst isRule
  obtain ⟨o, rfl⟩ := len1_of shapes.2.2.1.symm
  have readNil : read = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.1.symm
  have madeNil : made = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.2.1.symm
  have seenNil : seen = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.2.2.symm
  subst readNil madeNil seenNil
  have subMem : member = rootRules_sub ⟨clearRule, clearRule_mem, rfl⟩ := Subsingleton.elim _ _
  subst subMem
  exact ⟨o, rfl, enabled.taken_subset (by simp [Selection.commit])⟩

/-! ### Root clearing (`0 @ Root`) on mixed configurations -/

theorem rootClear_admitted (label : O → Pattern) (C : Configuration Pattern O) (o : O)
    (present : o ∈ C.present) {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations)
    (isZero : NameLaws (psubst σ₀ (label o)) (atLoc pZero rootLoc))
    {ρ : PSubst} (opensFreshly : (rootClearAt ρ o).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE located).Admits (s := embed label C) (rootClearAt ρ o) := by
  obtain ⟨w, solved, -, -⟩ := Comm.information_amalgamates_matched (Y := QN) (s := embed label C)
    (rootClearAt ρ o) opensFreshly (b := PUnit.unit) σ₀ (fun _ => none) known
    (fun _ m => (List.not_mem_nil m).elim)
    (fun o' m => by obtain rfl := List.mem_singleton.mp m; exact present)
    (fun _ m => (List.not_mem_nil m).elim)
    (fun q m => by
      obtain rfl := List.mem_singleton.mp m
      show NameLaws (psubst (fun _ => none) (atLoc pZero rootLoc)) (psubst σ₀ (label o))
      rw [psubst_none]
      exact isZero.symm)
    (fun _ m => (List.not_mem_nil m).elim)
  refine (RuleSyntax.admits_iff _).mpr ⟨opensFreshly,
    ⟨by simp [rootClearAt, rootFiring, widen, atFiring, clearN],
     by simp [rootClearAt, rootFiring, widen, atFiring, clearN], rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun _ m => by simp [Selection.commit] at m⟩,
    ⟨PUnit.unit, w, solved⟩, fun _ m => (List.not_mem_nil m).elim,
    fun _ m => (List.not_mem_nil m).elim⟩
  · intro x m
    simp only [rootClearAt, rootFiring, widen, atFiring, clearN, Selection.commit,
      List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_singleton] at m
    subst m; exact present
  · intro _ m; simp [rootClearAt, rootFiring, widen, atFiring, clearN, Selection.commit] at m
  · simp [rootClearAt, rootFiring, widen, atFiring, clearN, Selection.commit]
  · simp [rootClearAt, rootFiring, widen, atFiring, clearN, Selection.commit]

omit [DecidableEq O] in
theorem rootClear_takes_zero (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (o : O) {σ : PSubst}
    (solved : nameAction.Models σ ((rootClearAt ρ o).information QN (embed label C))) :
    NameLaws (psubst σ (label o)) (atLoc pZero rootLoc) := by
  have zipped : (atLoc pZero rootLoc, o) ∈
      (rootClearAt ρ o).rule.body.take.zip (rootClearAt ρ o).selection.taken := by
    simp [rootClearAt, rootFiring, widen, atFiring, clearN, atRule, clearRule, RuleInstance.map]
  have r := take_reads (rootClearAt ρ o) solved zipped
  simpa [psubst_atLoc_any, psubst_pZero, psubst_rootLoc] using r.symm

theorem rootClear_extends (label : O → Pattern) (C : Configuration Pattern O) (o : O)
    (present : o ∈ C.present)
    (reads : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label o)) (atLoc pZero rootLoc))
    {ρ : PSubst} (opensFreshly : (rootClearAt ρ o).Fresh QN (embed label C))
    {τ : PSubst} (known : nameAction.Models τ C.equations) :
    ∃ w : PSubst, nameAction.Models w (resConf label C (rootClearAt ρ o)).equations ∧
      ∀ o' ∈ C.present, NameLaws (psubst w (label o')) (psubst τ (label o')) := by
  obtain ⟨w, solved, onState, -⟩ := Comm.information_amalgamates_matched (Y := QN)
    (s := embed label C) (rootClearAt ρ o) opensFreshly (b := PUnit.unit) τ (fun _ => none) known
    (fun _ m => (List.not_mem_nil m).elim)
    (fun o' m => by obtain rfl := List.mem_singleton.mp m; exact present)
    (fun _ m => (List.not_mem_nil m).elim)
    (fun q m => by
      obtain rfl := List.mem_singleton.mp m
      show NameLaws (psubst (fun _ => none) (atLoc pZero rootLoc)) (psubst τ (label o))
      rw [psubst_none]
      exact (reads τ known).symm)
    (fun _ m => (List.not_mem_nil m).elim)
  refine ⟨w, solved, fun o' p' => ?_⟩
  have agree : NameLaws (psubst w (psubst (fun _ => none) (label o'))) (psubst τ (label o')) :=
    onState (label o') (Or.inr (Or.inr ⟨o', p', rfl⟩))
  rwa [psubst_none] at agree

/-! ### Root heating (`(a | b) @ Root`) on mixed configurations -/

theorem rootHeat_admitted (label : O → Pattern) (C : Configuration Pattern O) (o m₁ m₂ : O)
    (present : o ∈ C.present) (madeDistinct : m₁ ≠ m₂)
    (fresh₁ : m₁ ∉ C.present) (fresh₂ : m₂ ∉ C.present)
    {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations) {a b : Pattern}
    (pair : NameLaws (psubst σ₀ (label o)) (atLoc (par a b) rootLoc))
    {ρ : PSubst} (opensFreshly : (rootHeatAt ρ o m₁ m₂).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE located).Admits (s := embed label C) (rootHeatAt ρ o m₁ m₂) := by
  let h : PSubst := fun v => if v = "A" then some a else if v = "B" then some b else none
  have hTake : psubst h (atLoc (par leftPart rightPart) rootLoc) = atLoc (par a b) rootLoc := by
    rw [psubst_atLoc_any, psubst_par, psubst_rootLoc]
    rfl
  obtain ⟨w, solved, -, -⟩ := Comm.information_amalgamates_matched (Y := QN) (s := embed label C)
    (rootHeatAt ρ o m₁ m₂) opensFreshly (b := PUnit.unit) σ₀ h known
    (fun _ m => (List.not_mem_nil m).elim)
    (fun o' m => by obtain rfl := List.mem_singleton.mp m; exact present)
    (fun _ m => (List.not_mem_nil m).elim)
    (fun q m => by
      obtain rfl := List.mem_singleton.mp m
      show NameLaws (psubst h (atLoc (par leftPart rightPart) rootLoc)) (psubst σ₀ (label o))
      rw [hTake]
      exact pair.symm)
    (fun _ m => (List.not_mem_nil m).elim)
  refine (RuleSyntax.admits_iff _).mpr ⟨opensFreshly,
    ⟨by simp [rootHeatAt, rootFiring, widen, atFiring, heatN],
     by simp [rootHeatAt, rootFiring, widen, atFiring, heatN, madeDistinct], rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun _ m => by simp [Selection.commit] at m⟩,
    ⟨PUnit.unit, w, solved⟩, fun _ m => (List.not_mem_nil m).elim,
    fun _ m => (List.not_mem_nil m).elim⟩
  · intro x m
    simp only [rootHeatAt, rootFiring, widen, atFiring, heatN, Selection.commit,
      List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_singleton] at m
    subst m; exact present
  · intro _ m; simp [rootHeatAt, rootFiring, widen, atFiring, heatN, Selection.commit] at m
  · simp [rootHeatAt, rootFiring, widen, atFiring, heatN, Selection.commit]
  · rw [Finset.disjoint_left]
    intro x m
    simp only [rootHeatAt, rootFiring, widen, atFiring, heatN, Selection.commit,
      List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_insert,
      Finset.mem_singleton] at m
    rcases m with rfl | rfl
    · exact fresh₁
    · exact fresh₂

omit [DecidableEq O] in
theorem rootHeat_takes_pair (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (o m₁ m₂ : O) {σ : PSubst}
    (solved : nameAction.Models σ ((rootHeatAt ρ o m₁ m₂).information QN (embed label C))) :
    ∃ a b : Pattern, psubst σ (label o) = atLoc (par a b) rootLoc ∧
      NameLaws (psubst σ (psubst ρ leftPart)) a ∧ NameLaws (psubst σ (psubst ρ rightPart)) b := by
  have zipped : (atLoc (par leftPart rightPart) rootLoc, o) ∈
      (rootHeatAt ρ o m₁ m₂).rule.body.take.zip (rootHeatAt ρ o m₁ m₂).selection.taken := by
    simp [rootHeatAt, rootFiring, widen, atFiring, heatN, atRule, heatRule, RuleInstance.map]
  have take := take_reads (rootHeatAt ρ o m₁ m₂) solved zipped
  rw [psubst_atLoc_any, psubst_atLoc_any, psubst_par, psubst_par, psubst_rootLoc,
    psubst_rootLoc] at take
  obtain ⟨body, l', lEq, pairEq, rootEq⟩ := ReflLocated.nameLaws_atLoc_left take
  obtain ⟨a, b, rfl, leftEq, rightEq⟩ := nameLaws_pair_left pairEq
  have lIsRoot : l' = rootLoc := by
    have canon := (ReflNames.nameLaws_iff rootLoc l').mp rootEq
    have cRoot : ReflNames.nameCanon rootLoc = rootLoc := rfl
    rw [cRoot] at canon
    cases l' with
    | apply c args =>
        obtain ⟨args', hc⟩ := ReflNames.nameCanon_apply_head c args
        have cEq : c = "Root" := by rw [hc] at canon; exact (Pattern.apply.inj canon).1.symm
        subst cEq
        rw [ReflNames.nameCanon_apply_of_not_quote (by unfold ReflNames.IsQuote; decide)] at canon
        have aNil : args = [] := List.map_eq_nil_iff.mp (Pattern.apply.inj canon).2.symm
        subst aNil; rfl
    | bvar _ => simp [ReflNames.nameCanon, rootLoc] at canon
    | fvar _ => simp [ReflNames.nameCanon, rootLoc] at canon
    | lambda _ _ => simp [ReflNames.nameCanon, rootLoc] at canon
    | multiLambda _ _ _ => simp [ReflNames.nameCanon, rootLoc] at canon
    | subst _ _ => simp [ReflNames.nameCanon, rootLoc] at canon
    | collection _ _ _ => rw [ReflNames.nameCanon_collection] at canon; cases canon
  subst lIsRoot
  exact ⟨a, b, lEq, leftEq, rightEq⟩

theorem rootHeat_reads_mixed (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (o : O) {m₁ m₂ : O} (madeDistinct : m₁ ≠ m₂) (a b : Pattern)
    (reads : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label o)) (psubst σ (atLoc (par a b) rootLoc)))
    {σ : PSubst}
    (solved : nameAction.Models σ (res label C (rootHeatAt ρ o m₁ m₂)).knowledge) :
    NameLaws (psubst σ ((res label C (rootHeatAt ρ o m₁ m₂)).label m₁))
        (psubst σ (atLoc a rootLoc)) ∧
      NameLaws (psubst σ ((res label C (rootHeatAt ρ o m₁ m₂)).label m₂))
        (psubst σ (atLoc b rootLoc)) := by
  have solvedInfo : nameAction.Models σ ((rootHeatAt ρ o m₁ m₂).information QN (embed label C)) :=
    solved
  obtain ⟨a', b', same, leftEq, rightEq⟩ := rootHeat_takes_pair label C ρ o m₁ m₂ solvedInfo
  have known := info_known (rootHeatAt ρ o m₁ m₂) solvedInfo
  have read := reads σ known
  rw [same, psubst_atLoc_any, psubst_par, psubst_rootLoc] at read
  obtain ⟨pairR, -⟩ := (locatedFrame_name.atLoc_iff _ _ _ _).mp read
  obtain ⟨rA, rB⟩ := nameLaws_pair_iff.mp pairR
  have lbl₁ : (res label C (rootHeatAt ρ o m₁ m₂)).label m₁ =
      psubst ρ (atLoc leftPart rootLoc) := by
    show (if m₁ = m₁ then psubst ρ (atLoc leftPart rootLoc) else _) = _
    rw [if_pos rfl]
  have lbl₂ : (res label C (rootHeatAt ρ o m₁ m₂)).label m₂ =
      psubst ρ (atLoc rightPart rootLoc) := by
    show (if m₂ = m₁ then _ else if m₂ = m₂ then psubst ρ (atLoc rightPart rootLoc) else _) = _
    rw [if_neg (Ne.symm madeDistinct), if_pos rfl]
  rw [lbl₁, lbl₂]
  simp only [psubst_atLoc_any, psubst_rootLoc]
  exact ⟨(locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨leftEq.trans rA, NameLaws.refl _⟩,
    (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨rightEq.trans rB, NameLaws.refl _⟩⟩

theorem rootHeat_extends (label : O → Pattern) (C : Configuration Pattern O) (o m₁ m₂ : O)
    (present : o ∈ C.present) (a b : Pattern)
    (reads : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label o)) (psubst σ (atLoc (par a b) rootLoc)))
    {ρ : PSubst} (opensFreshly : (rootHeatAt ρ o m₁ m₂).Fresh QN (embed label C))
    {τ : PSubst} (known : nameAction.Models τ C.equations) :
    ∃ w : PSubst, nameAction.Models w (resConf label C (rootHeatAt ρ o m₁ m₂)).equations ∧
      ∀ o' ∈ C.present, NameLaws (psubst w (label o')) (psubst τ (label o')) := by
  let h : PSubst := fun v =>
    if v = "A" then some (psubst τ a) else if v = "B" then some (psubst τ b) else none
  have hTake : psubst h (atLoc (par leftPart rightPart) rootLoc) =
      psubst τ (atLoc (par a b) rootLoc) := by
    simp only [psubst_atLoc_any, psubst_par, psubst_rootLoc]
    rfl
  obtain ⟨w, solved, onState, -⟩ := Comm.information_amalgamates_matched (Y := QN)
    (s := embed label C) (rootHeatAt ρ o m₁ m₂) opensFreshly (b := PUnit.unit) τ h known
    (fun _ m => (List.not_mem_nil m).elim)
    (fun o' m => by obtain rfl := List.mem_singleton.mp m; exact present)
    (fun _ m => (List.not_mem_nil m).elim)
    (fun q m => by
      obtain rfl := List.mem_singleton.mp m
      show NameLaws (psubst h (atLoc (par leftPart rightPart) rootLoc)) (psubst τ (label o))
      rw [hTake]
      exact (reads τ known).symm)
    (fun _ m => (List.not_mem_nil m).elim)
  refine ⟨w, solved, fun o' p' => ?_⟩
  have agree : NameLaws (psubst w (psubst (fun _ => none) (label o'))) (psubst τ (label o')) :=
    onState (label o') (Or.inr (Or.inr ⟨o', p', rfl⟩))
  rwa [psubst_none] at agree

/-! ### Root communication (`rootCommAt`) on mixed configurations -/

theorem rootComm_admitted_mixed (label : O → Pattern) (C : Configuration Pattern O)
    (t u channel K₁ K₂ : Pattern) (first second m₁ m₂ : O)
    (readsFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (atLoc (pFor t channel K₁) rootLoc)))
    (readsSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (atLoc (pFor u channel K₂) rootLoc)))
    (distinct : first ≠ second) (madeDistinct : m₁ ≠ m₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : m₁ ∉ C.present) (fresh₂ : m₂ ∉ C.present)
    {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations)
    (unifies : NameLaws (psubst σ₀ t) (psubst σ₀ u))
    {ρ : PSubst} (opensFreshly : (rootCommAt ρ first second m₁ m₂).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (rootCommAt ρ first second m₁ m₂) := by
  let h : PSubst := commInstance (psubst σ₀ t) (psubst σ₀ u) (psubst σ₀ channel)
    (psubst σ₀ K₁) (psubst σ₀ K₂)
  obtain ⟨w, solved, -, -⟩ := Comm.information_amalgamates_matched (Y := QN) (s := embed label C)
    (rootCommAt ρ first second m₁ m₂) opensFreshly (b := PUnit.unit) σ₀ h known
    (fun e m => by
      obtain rfl := List.mem_singleton.mp m
      show NameLaws (psubst h (atLoc firstPattern rootLoc)) (psubst h (atLoc secondPattern rootLoc))
      rw [psubst_atLoc_any, psubst_atLoc_any, psubst_rootLoc,
        commInstance_firstPattern, commInstance_secondPattern]
      exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨unifies, NameLaws.refl _⟩)
    (fun o m => by
      rcases List.mem_cons.mp m with rfl | m
      · exact present₁
      · obtain rfl := List.mem_singleton.mp m; exact present₂)
    (fun _ m => (List.not_mem_nil m).elim)
    (fun q m => by
      rcases List.mem_cons.mp m with rfl | m
      · show NameLaws (psubst h (atLoc (pFor firstPattern channelUnknown firstBody) rootLoc))
            (psubst σ₀ (label first))
        rw [psubst_atLoc_any, psubst_pFor, psubst_rootLoc, commInstance_firstPattern,
          commInstance_channel, commInstance_firstBody]
        exact (readsFirst σ₀ known).symm
      · obtain rfl := List.mem_singleton.mp m
        show NameLaws (psubst h (atLoc (pFor secondPattern channelUnknown secondBody) rootLoc))
            (psubst σ₀ (label second))
        rw [psubst_atLoc_any, psubst_pFor, psubst_rootLoc, commInstance_secondPattern,
          commInstance_channel, commInstance_secondBody]
        exact (readsSecond σ₀ known).symm)
    (fun _ m => (List.not_mem_nil m).elim)
  refine (RuleSyntax.admits_iff _).mpr ⟨opensFreshly,
    ⟨by simp [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, distinct],
     by simp [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, madeDistinct],
     rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun _ m => by simp [Selection.commit] at m⟩,
    ⟨PUnit.unit, w, solved⟩, fun _ m => (List.not_mem_nil m).elim,
    fun _ m => (List.not_mem_nil m).elim⟩
  · intro o m
    simp only [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, Selection.commit,
      List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_insert,
      Finset.mem_singleton] at m
    rcases m with rfl | rfl
    · exact present₁
    · exact present₂
  · intro _ m
    simp [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, Selection.commit] at m
  · simp [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, Selection.commit]
  · rw [Finset.disjoint_left]
    intro o m
    simp only [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, Selection.commit,
      List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_insert,
      Finset.mem_singleton] at m
    rcases m with rfl | rfl
    · exact fresh₁
    · exact fresh₂

theorem rootComm_result_labels (label : O → Pattern) (C : Configuration Pattern O)
    (ρ : PSubst) (first second m₁ m₂ : O) (madeDistinct : m₁ ≠ m₂) :
    (res label C (rootCommAt ρ first second m₁ m₂)).label m₁ =
      psubst ρ (atLoc firstBody rootLoc) ∧
    (res label C (rootCommAt ρ first second m₁ m₂)).label m₂ =
      psubst ρ (atLoc secondBody rootLoc) := by
  constructor
  · show (if m₁ = m₁ then psubst ρ (atLoc firstBody rootLoc) else _) = _
    rw [if_pos rfl]
  · show (if m₂ = m₁ then _ else if m₂ = m₂ then psubst ρ (atLoc secondBody rootLoc) else _) = _
    rw [if_neg (Ne.symm madeDistinct), if_pos rfl]

theorem rootComm_reads_raw (label : O → Pattern) (C : Configuration Pattern O)
    (t u channel₁ channel₂ K₁ K₂ : Pattern) (first second m₁ m₂ : O)
    (readsFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (atLoc (pFor t channel₁ K₁) rootLoc)))
    (readsSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (atLoc (pFor u channel₂ K₂) rootLoc)))
    (madeDistinct : m₁ ≠ m₂) (ρ : PSubst) {σ : PSubst}
    (solved : nameAction.Models σ (res label C (rootCommAt ρ first second m₁ m₂)).knowledge) :
    nameAction.Models σ C.equations ∧ NameLaws (psubst σ t) (psubst σ u) ∧
      NameLaws (psubst σ channel₁) (psubst σ channel₂) ∧
      NameLaws (psubst σ ((res label C (rootCommAt ρ first second m₁ m₂)).label m₁))
        (psubst σ (atLoc K₁ rootLoc)) ∧
      NameLaws (psubst σ ((res label C (rootCommAt ρ first second m₁ m₂)).label m₂))
        (psubst σ (atLoc K₂ rootLoc)) := by
  have solvedInfo : nameAction.Models σ
      ((rootCommAt ρ first second m₁ m₂).information QN (embed label C)) := solved
  have known := info_known (rootCommAt ρ first second m₁ m₂) solvedInfo
  have z₁ : (atLoc (pFor firstPattern channelUnknown firstBody) rootLoc, first) ∈
      (rootCommAt ρ first second m₁ m₂).rule.body.take.zip
        (rootCommAt ρ first second m₁ m₂).selection.taken := by
    simp [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, atRule, commRule,
      RuleInstance.map]
  have z₂ : (atLoc (pFor secondPattern channelUnknown secondBody) rootLoc, second) ∈
      (rootCommAt ρ first second m₁ m₂).rule.body.take.zip
        (rootCommAt ρ first second m₁ m₂).selection.taken := by
    simp [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, atRule, commRule,
      RuleInstance.map]
  have r₁ := (take_reads _ solvedInfo z₁).trans (readsFirst σ known)
  have r₂ := (take_reads _ solvedInfo z₂).trans (readsSecond σ known)
  have told : NameLaws (psubst σ (psubst ρ (atLoc firstPattern rootLoc)))
      (psubst σ (psubst ρ (atLoc secondPattern rootLoc))) := by
    have infoEq : (rootCommAt ρ first second m₁ m₂).information QN (embed label C) =
        C.equations ++
          [(psubst ρ (atLoc (pFor firstPattern channelUnknown firstBody) rootLoc), label first),
           (psubst ρ (atLoc (pFor secondPattern channelUnknown secondBody) rootLoc), label second)] ++
          [] ++ [(psubst ρ (atLoc firstPattern rootLoc), psubst ρ (atLoc secondPattern rootLoc))] := by
      rw [OneFrame.information_eq]; rfl
    have s' := solvedInfo
    rw [infoEq] at s'
    exact s' (psubst ρ (atLoc firstPattern rootLoc), psubst ρ (atLoc secondPattern rootLoc))
      (by simp)
  simp only [psubst_atLoc_any, psubst_pFor, psubst_rootLoc] at r₁ r₂ told
  obtain ⟨in₁, -⟩ := (locatedFrame_name.atLoc_iff _ _ _ _).mp r₁
  obtain ⟨in₂, -⟩ := (locatedFrame_name.atLoc_iff _ _ _ _).mp r₂
  obtain ⟨pats, -⟩ := (locatedFrame_name.atLoc_iff _ _ _ _).mp told
  obtain ⟨p₁, c₁, b₁⟩ := nameLaws_pFor_iff.mp in₁
  obtain ⟨p₂, c₂, b₂⟩ := nameLaws_pFor_iff.mp in₂
  obtain ⟨lbl₁, lbl₂⟩ := rootComm_result_labels label C ρ first second m₁ m₂ madeDistinct
  rw [lbl₁, lbl₂]
  simp only [psubst_atLoc_any, psubst_rootLoc]
  exact ⟨known, p₁.symm.trans (pats.trans p₂), c₁.symm.trans c₂,
    (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨b₁, NameLaws.refl _⟩,
    (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨b₂, NameLaws.refl _⟩⟩

/-- **Root COMM forward & readout on mixed configurations** (under Step 1' hypotheses). -/
theorem rootComm_commit_mixed (label : O → Pattern) (C : Configuration Pattern O)
    (t u channel A B : Pattern) (bs : Bindings) (gp : GroundPrincipal t u bs)
    (convention : Apart t A u B) (foA : firstOrder A = true) (foB : firstOrder B = true)
    (groundT : groundBags t = true) (groundU : groundBags u = true)
    (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u)
    (first second m₁ m₂ : O)
    (readsFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (atLoc (predot (pFor t channel A)) rootLoc)))
    (readsSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (atLoc (predot (pFor u channel B)) rootLoc)))
    (distinct : first ≠ second) (madeDistinct : m₁ ≠ m₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : m₁ ∉ C.present) (fresh₂ : m₂ ∉ C.present)
    {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations)
    (unifies : NameLaws (psubst σ₀ t) (psubst σ₀ u))
    {ρ : PSubst} (opensFreshly : (rootCommAt ρ first second m₁ m₂).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
        (rootCommAt ρ first second m₁ m₂) ∧
      ∀ σ : PSubst,
        nameAction.Models σ (res label C (rootCommAt ρ first second m₁ m₂)).knowledge →
          nameAction.Models σ C.equations ∧
          NameLaws (psubst σ ((res label C (rootCommAt ρ first second m₁ m₂)).label m₁))
            (psubst σ (atLoc (predot (applyDot bs A)) rootLoc)) ∧
          NameLaws (psubst σ ((res label C (rootCommAt ρ first second m₁ m₂)).label m₂))
            (psubst σ (atLoc (predot (applyDot bs B)) rootLoc)) := by
  have rF : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first))
        (psubst σ (atLoc (pFor t (predot channel) (dotted (pvars t) (predot A))) rootLoc)) :=
    fun σ s => by have r := readsFirst σ s; rwa [predot_pFor] at r
  have rS : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second))
        (psubst σ (atLoc (pFor u (predot channel) (dotted (pvars u) (predot B))) rootLoc)) :=
    fun σ s => by have r := readsSecond σ s; rwa [predot_pFor] at r
  refine ⟨rootComm_admitted_mixed label C t u (predot channel) (dotted (pvars t) (predot A))
    (dotted (pvars u) (predot B)) first second m₁ m₂ rF rS distinct madeDistinct present₁ present₂
    fresh₁ fresh₂ known unifies opensFreshly, fun σ solved => ?_⟩
  obtain ⟨known', unify, -, b₁, b₂⟩ := rootComm_reads_raw label C t u (predot channel)
    (predot channel) (dotted (pvars t) (predot A)) (dotted (pvars u) (predot B))
    first second m₁ m₂ rF rS madeDistinct ρ solved
  have agrees := agrees_of_groundPrincipal gp groundT groundU canonicalT canonicalU
    (bagLaws_of_nameLaws unify)
  obtain ⟨keptA, keptB⟩ := keys_of_apart convention
  have dotA : NameLaws (psubst σ (dotted (pvars t) (predot A)))
      (psubst σ (predot (applyDot bs A))) :=
    dotted_reads_predot_name gp.keys gp.covers agrees A foA
      (fun x m => List.mem_append_left _ m)
      (fun x inA inK => (List.mem_append.mp inK).elim id
        (fun inU => absurd inA (convention.rightOutside x inU))) keptA
  have dotB : NameLaws (psubst σ (dotted (pvars u) (predot B)))
      (psubst σ (predot (applyDot bs B))) :=
    dotted_reads_predot_name gp.keys gp.covers agrees B foB
      (fun x m => List.mem_append_right _ m)
      (fun x inB inK => (List.mem_append.mp inK).elim
        (fun inT => absurd inB (convention.leftOutside x inT)) id) keptB
  simp only [psubst_atLoc_any, psubst_rootLoc] at b₁ b₂ ⊢
  exact ⟨known',
    b₁.trans ((locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨dotA, NameLaws.refl _⟩),
    b₂.trans ((locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨dotB, NameLaws.refl _⟩)⟩

/-- Ground-pattern root COMM on mixed configurations. It compares patterns at
`QN` without canonicalizing their bodies. The reads supply already represented
continuations; the firing passes them through unchanged. -/
theorem rootComm_ground_mixed (label : O → Pattern) (C : Configuration Pattern O)
    (t u channel A B : Pattern) (groundT : pvars t = []) (groundU : pvars u = [])
    (samePat : NameLaws t u) (first second m₁ m₂ : O)
    (readsFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (atLoc (pFor t channel A) rootLoc)))
    (readsSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (atLoc (pFor u channel B) rootLoc)))
    (distinct : first ≠ second) (madeDistinct : m₁ ≠ m₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : m₁ ∉ C.present) (fresh₂ : m₂ ∉ C.present)
    {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations)
    {ρ : PSubst} (opensFreshly : (rootCommAt ρ first second m₁ m₂).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
        (rootCommAt ρ first second m₁ m₂) ∧
      ∀ σ : PSubst,
        nameAction.Models σ (res label C (rootCommAt ρ first second m₁ m₂)).knowledge →
          nameAction.Models σ C.equations ∧
          NameLaws (psubst σ ((res label C (rootCommAt ρ first second m₁ m₂)).label m₁))
            (psubst σ (atLoc A rootLoc)) ∧
          NameLaws (psubst σ ((res label C (rootCommAt ρ first second m₁ m₂)).label m₂))
            (psubst σ (atLoc B rootLoc)) := by
  have unifies : NameLaws (psubst σ₀ t) (psubst σ₀ u) := by
    rwa [psubst_of_pvars_nil σ₀ t groundT, psubst_of_pvars_nil σ₀ u groundU]
  refine ⟨rootComm_admitted_mixed label C t u channel A B
    first second m₁ m₂ readsFirst readsSecond distinct madeDistinct present₁ present₂
    fresh₁ fresh₂ known unifies opensFreshly, fun σ solved => ?_⟩
  obtain ⟨known', -, -, b₁, b₂⟩ := rootComm_reads_raw label C t u channel channel A B
    first second m₁ m₂ readsFirst readsSecond madeDistinct ρ solved
  exact ⟨known', b₁, b₂⟩

/-- **Root COMM backward soundness on mixed configurations**: any admitted `rootCommAt` on two
represented root inputs forces `ch = ch'`, yields `BagComm` via `GroundPrincipal`, and reads the
made rows as the represented dotted continuations. -/
theorem rootComm_sound_mixed (label : O → Pattern) (C : Configuration Pattern O)
    (t u ch ch' A B : Pattern) (first second m₁ m₂ : O) (ρ : PSubst)
    (readsFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (atLoc (predot (pFor t ch A)) rootLoc)))
    (readsSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (atLoc (predot (pFor u ch' B)) rootLoc)))
    (groundCh : pvars ch = []) (groundCh' : pvars ch' = [])
    (canonicalCh : nameCanon ch = ch) (canonicalCh' : nameCanon ch' = ch')
    (unifiable : (∃ σ : PSubst, psubst σ t = psubst σ u) →
      ∃ bs : Bindings, GroundPrincipal t u bs ∧ ∀ y v, bs.lookup y = some v → firstOrder v = true)
    (convention : Apart t A u B) (foA : firstOrder A = true) (foB : firstOrder B = true)
    (groundT : groundBags t = true) (groundU : groundBags u = true)
    (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (rootCommAt ρ first second m₁ m₂))
    (rest : Multiset Pattern) :
    ch = ch' ∧ ∃ bs : Bindings,
      BagComm (pFor t ch A ::ₘ pFor u ch B ::ₘ rest)
        ((parts (applyDot bs A) : Multiset Pattern) +
          (parts (applyDot bs B) : Multiset Pattern) + rest) ∧
      ∀ σ : PSubst,
        nameAction.Models σ (res label C (rootCommAt ρ first second m₁ m₂)).knowledge →
          nameAction.Models σ C.equations ∧
          NameLaws (psubst σ ((res label C (rootCommAt ρ first second m₁ m₂)).label m₁))
            (psubst σ (atLoc (predot (applyDot bs A)) rootLoc)) ∧
          NameLaws (psubst σ ((res label C (rootCommAt ρ first second m₁ m₂)).label m₂))
            (psubst σ (atLoc (predot (applyDot bs B)) rootLoc)) := by
  obtain ⟨fresh, shapes, enabled, ⟨_, w, solved⟩, _, _⟩ := (RuleSyntax.admits_iff _).mp admitted
  have distinct : first ≠ second := by
    simpa [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection] using shapes.1
  have madeDistinct : m₁ ≠ m₂ := by
    simpa [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection] using shapes.2.1
  have rF : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first))
        (psubst σ (atLoc (pFor t (predot ch) (dotted (pvars t) (predot A))) rootLoc)) :=
    fun σ s => by have r := readsFirst σ s; rwa [predot_pFor] at r
  have rS : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second))
        (psubst σ (atLoc (pFor u (predot ch') (dotted (pvars u) (predot B))) rootLoc)) :=
    fun σ s => by have r := readsSecond σ s; rwa [predot_pFor] at r
  obtain ⟨knownW, unifyW, chanW, -, -⟩ := rootComm_reads_raw label C t u (predot ch) (predot ch')
    (dotted (pvars t) (predot A)) (dotted (pvars u) (predot B)) first second m₁ m₂ rF rS
    madeDistinct ρ solved
  rw [predot_ground ch groundCh, predot_ground ch' groundCh',
    psubst_of_pvars_nil w ch groundCh, psubst_of_pvars_nil w ch' groundCh'] at chanW
  have sameCh : ch = ch' := by
    have canon := (ReflNames.nameLaws_iff ch ch').mp chanW
    rwa [canonicalCh, canonicalCh'] at canon
  obtain ⟨bs, gp, values⟩ := unifiable
    ⟨_, canonSubst_unifies groundT groundU canonicalT canonicalU (bagLaws_of_nameLaws unifyW)⟩
  have freshMade : m₁ ∉ C.present ∧ m₂ ∉ C.present := by
    simpa [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, Selection.commit,
      embed] using enabled.fresh
  have p₁ : first ∈ C.present := enabled.taken_subset
    (by simp [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, Selection.commit])
  have p₂ : second ∈ C.present := enabled.taken_subset
    (by simp [rootCommAt, rootFiring, widen, atFiring, commAtN, commSelection, Selection.commit])
  obtain ⟨-, reads⟩ := rootComm_commit_mixed label C t u ch A B bs gp convention foA foB
    groundT groundU canonicalT canonicalU first second m₁ m₂ readsFirst
    (sameCh ▸ readsSecond) distinct madeDistinct p₁ p₂ freshMade.1 freshMade.2 knownW unifyW fresh
  exact ⟨sameCh, bs, BagComm.comm t u ch A B bs rest gp convention values, reads⟩

/-- Solutions unifying the located inputs extend across COMM while
retaining the old rows and the two selected continuation values. -/
theorem rootComm_extends_with_publications (label : O → Pattern) (C : Configuration Pattern O)
    (t u channel K₁ K₂ : Pattern) (first second m₁ m₂ : O)
    (readsFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (atLoc (pFor t channel K₁) rootLoc)))
    (readsSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (atLoc (pFor u channel K₂) rootLoc)))
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    {ρ : PSubst} (opensFreshly : (rootCommAt ρ first second m₁ m₂).Fresh QN (embed label C))
    {τ : PSubst} (known : nameAction.Models τ C.equations)
    (unifies : NameLaws (psubst τ t) (psubst τ u)) :
    ∃ w : PSubst, nameAction.Models w (resConf label C (rootCommAt ρ first second m₁ m₂)).equations ∧
      (∀ o' ∈ C.present, NameLaws (psubst w (label o')) (psubst τ (label o'))) ∧
      NameLaws (psubst w (psubst ρ firstBody)) (psubst τ K₁) ∧
      NameLaws (psubst w (psubst ρ secondBody)) (psubst τ K₂) := by
  let h : PSubst := commInstance (psubst τ t) (psubst τ u) (psubst τ channel)
    (psubst τ K₁) (psubst τ K₂)
  obtain ⟨w, solved, onState, onRule⟩ := Comm.information_amalgamates_matched (Y := QN)
    (s := embed label C) (rootCommAt ρ first second m₁ m₂) opensFreshly (b := PUnit.unit) τ h known
    (fun e m => by
      obtain rfl := List.mem_singleton.mp m
      show NameLaws (psubst h (atLoc firstPattern rootLoc)) (psubst h (atLoc secondPattern rootLoc))
      rw [psubst_atLoc_any, psubst_atLoc_any, psubst_rootLoc,
        commInstance_firstPattern, commInstance_secondPattern]
      exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨unifies, NameLaws.refl _⟩)
    (fun o m => by
      rcases List.mem_cons.mp m with rfl | m
      · exact present₁
      · obtain rfl := List.mem_singleton.mp m; exact present₂)
    (fun _ m => (List.not_mem_nil m).elim)
    (fun q m => by
      rcases List.mem_cons.mp m with rfl | m
      · show NameLaws (psubst h (atLoc (pFor firstPattern channelUnknown firstBody) rootLoc))
            (psubst τ (label first))
        rw [psubst_atLoc_any, psubst_pFor, psubst_rootLoc, commInstance_firstPattern,
          commInstance_channel, commInstance_firstBody]
        exact (readsFirst τ known).symm
      · obtain rfl := List.mem_singleton.mp m
        show NameLaws (psubst h (atLoc (pFor secondPattern channelUnknown secondBody) rootLoc))
            (psubst τ (label second))
        rw [psubst_atLoc_any, psubst_pFor, psubst_rootLoc, commInstance_secondPattern,
          commInstance_channel, commInstance_secondBody]
        exact (readsSecond τ known).symm)
    (fun _ m => (List.not_mem_nil m).elim)
  refine ⟨w, solved, ?_, ?_, ?_⟩
  · intro o' p'
    have agree : NameLaws (psubst w (psubst (fun _ => none) (label o'))) (psubst τ (label o')) :=
      onState (label o') (Or.inr (Or.inr ⟨o', p', rfl⟩))
    rwa [psubst_none] at agree
  · have first : NameLaws (psubst w (psubst ρ (atLoc firstBody rootLoc)))
        (psubst h (atLoc firstBody rootLoc)) :=
      onRule (atLoc firstBody rootLoc) (by
        simp [rootCommAt, rootFiring, widen, atFiring, commAtN, atRule, Rule.terms, commRule, RuleInstance.map])
    simp only [psubst_atLoc_any, psubst_rootLoc] at first
    rw [commInstance_firstBody] at first
    exact ((locatedFrame_name.atLoc_iff _ _ _ _).mp first).1
  · have second : NameLaws (psubst w (psubst ρ (atLoc secondBody rootLoc)))
        (psubst h (atLoc secondBody rootLoc)) :=
      onRule (atLoc secondBody rootLoc) (by
        simp [rootCommAt, rootFiring, widen, atFiring, commAtN, atRule, Rule.terms, commRule, RuleInstance.map])
    simp only [psubst_atLoc_any, psubst_rootLoc] at second
    rw [commInstance_secondBody] at second
    exact ((locatedFrame_name.atLoc_iff _ _ _ _).mp second).1

theorem rootComm_extends (label : O → Pattern) (C : Configuration Pattern O)
    (t u channel K₁ K₂ : Pattern) (first second m₁ m₂ : O)
    (readsFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (atLoc (pFor t channel K₁) rootLoc)))
    (readsSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (atLoc (pFor u channel K₂) rootLoc)))
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    {ρ : PSubst} (opensFreshly : (rootCommAt ρ first second m₁ m₂).Fresh QN (embed label C))
    {τ : PSubst} (known : nameAction.Models τ C.equations)
    (unifies : NameLaws (psubst τ t) (psubst τ u)) :
    ∃ w : PSubst, nameAction.Models w (resConf label C (rootCommAt ρ first second m₁ m₂)).equations ∧
      ∀ o' ∈ C.present, NameLaws (psubst w (label o')) (psubst τ (label o')) := by
  obtain ⟨w, solved, agrees, _, _⟩ := rootComm_extends_with_publications label C t u channel K₁ K₂
    first second m₁ m₂ readsFirst readsSecond present₁ present₂ opensFreshly known unifies
  exact ⟨w, solved, agrees⟩

end RootFirings

#print axioms predotU_of_binders_nil
#print axioms predotU_pFor_eq_predot
#print axioms predotU_named_listener
#print axioms predotU_closed_listener
#print axioms predotU_eq_predot_of_plain
#print axioms freeOnPats_unifies
#print axioms freeOnPats_glue_unifier
#print axioms row_extends_target
#print axioms eq_rootCommAt
#print axioms eq_rootHeatAt
#print axioms eq_rootClearAt
#print axioms rootClear_admitted
#print axioms rootHeat_admitted
#print axioms rootHeat_reads_mixed
#print axioms rootComm_commit_mixed
#print axioms rootComm_ground_mixed
#print axioms rootComm_sound_mixed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem
