import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystemChildOpenClose
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondenceForward
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.ReflectionClosure

/-!
# Reflection-depth derivations, location spines, and inner-close soundness (`P4` base)

This module builds the structural substrate for arbitrary-depth recursive reflection (`P4`) at
the name frame `QN`:

* **Location spines and depth invariance** (`IsLocSpine`, `locDepth_psubst_spine`,
  `CleanAboveDepth`, `CleanChildren`, `cleanAboveDepth_of_subset`): shows that `locDepth` is
  invariant under arbitrary pattern substitutions `σ` along well-formed `Child(Child(...))`
  spines, and transfers `CleanAboveDepth k` across runs whose surviving rows have depth `≤ k`.
* **Explicit reflection-depth derivations** (`ReflClosureDepth`, `HostedPackStep`,
  `HostedSubStepN`, `HostedSubStepC`): refine `ReflectionClosure.Step GroundPrincipal BagLaws`,
  `Corrected.BagStep conventional`, and `Corrected.CanonicalBagStep conventional` by explicit
  reflection nesting depth `d : ℕ`, factoring both **Interface N** and **Interface C** through a
  single packing derivation `HostedPackStep`.
* **Child heating and cooling without root firings** (`heating_noRoot`,
  `cooling_noRoot_extends`): non-root segment helpers with solution extension (`FreeOnPats`
  preservation).
* **Backward recursion through `closeChildAt`** (`CellsU`, `DoneCellsU`,
  `closeChild_commits_parent`, `closeChild_commits_parent_N`, `closeChild_commits_parent_C`):
  any admitted `closeChildAt` on a parent cell `y?(Q) @ l` and a grandchild in `DoneCellsU`
  forces all grandchild cells to be cooled (`gCells = []`), returns the grandchild to `Clean`,
  transitions `l` into `DoneCellsU`, and lifts the grandchild's `BagStep` / `CanonicalBagStep`
  to `l`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar nQuote tProc pReflect
  applyDot demoChan)
open MeTTaOperationsComm (psubst PSubst pvars dotted GroundPrincipal firstOrder
  psubst_of_pvars_nil psubst_pZero psubst_pFor psubst_tProc)
open MeTTaCalculus.Corrected (binders Apart components components_par canonicalBag bagEq_iff BagEq
  BagStep CanonicalBagStep conventional listener)
open FiniteProgram (channelUnknown)
open OneFrame (embed)
open ReflQuotient (BagLaws BagAxiom bagCanon groundBags bagLaws_psubst bagLaws_collection)
open ReflNames (NameLaws nameAction QN QNE nameLaws_heads nameLaws_pFor_iff nameLaws_tProc
  nameLaws_psubst)
open ReflLocated (atLoc rootLoc childLoc pendingTok doneTok locL locM reflP accC located
  heatChildN closeChild heatChild_admitted heatChild_reads_determinately psubst_rootLoc
  psubst_atLoc_any psubst_pendingTok psubst_par locatedFrame_name)
open ReflPacking (cooled psubst_doneTok nameLaws_doneTok_iff)
open ReflLocatedStep (psubst_childLoc nameLaws_pendingTok_iff nameLaws_childLoc_iff res resConf
  info_known take_reads solution_of_admitted result_present result_label_old result_row
  closeChildAt psubst_pReflect nameLaws_pReflect_iff)
open ReflUniform (predotU predotU_pFor predotU_pPar predotU_ground)
open ReflCorrespondence (Clean Splits heat_fresh_exists heat_present heat_label_old heat_back
  heat_extends quote_closed_ground)

/-! ## Location spines and depth invariance under substitution -/

/-- Well-formed location terms `Root` or `Child(m, x, p)` built over a spine `m`. -/
inductive IsLocSpine : Pattern → Prop where
  | root : IsLocSpine rootLoc
  | child {m : Pattern} (x p : Pattern) : IsLocSpine m → IsLocSpine (childLoc m x p)

theorem locDepth_psubst_spine {l : Pattern} (sp : IsLocSpine l) (σ : PSubst) :
    locDepth (psubst σ l) = locDepth l := by
  induction sp with
  | root => rw [psubst_rootLoc]
  | child x p _ ih => rw [psubst_childLoc, locDepth_childLoc, locDepth_childLoc, ih]

/-- Every child location `Child(m, x, p)` with `IsLocSpine m` and `k ≤ locDepth m` is `Clean`. -/
def CleanAboveDepth {O : Type*} (k : ℕ) (label : O → Pattern) (C : Configuration Pattern O) :
    Prop :=
  ∀ m x p, IsLocSpine m → k ≤ locDepth m → Clean (childLoc m x p) label C

/-- `CleanChildren`: every `Child(m, x, p)` over a location spine (`locDepth m ≥ 0`) is `Clean`. -/
abbrev CleanChildren {O : Type*} (label : O → Pattern) (C : Configuration Pattern O) : Prop :=
  CleanAboveDepth 0 label C

theorem cleanAboveDepth_mono {O : Type*} {k₁ k₂ : ℕ} (le : k₁ ≤ k₂) {label : O → Pattern}
    {C : Configuration Pattern O} (clean : CleanAboveDepth k₁ label C) :
    CleanAboveDepth k₂ label C :=
  fun m x p sp h => clean m x p sp (Nat.le_trans le h)

/-- Transfers `CleanAboveDepth k` when every row in `C'.present` is either an old row from `C`
(with the same label) or sits at depth `≤ k`. -/
theorem cleanAboveDepth_of_subset {O : Type*} {k : ℕ} {label label' : O → Pattern}
    {C C' : Configuration Pattern O} (clean : CleanAboveDepth k label C)
    (refines : ∀ σ : PSubst, nameAction.Models σ C'.equations → nameAction.Models σ C.equations)
    (rowsBound : ∀ o ∈ C'.present,
      (o ∈ C.present ∧ label' o = label o) ∨
      ∃ l : Pattern, IsLocSpine l ∧ locDepth l ≤ k ∧
        ∀ σ : PSubst, nameAction.Models σ C'.equations →
          (∃ y, NameLaws (psubst σ (label' o)) (atLoc y (psubst σ l))) ∨
          (∃ m₀, NameLaws (psubst σ (label' o)) (pendingTok (psubst σ l) m₀)) ∨
          (∃ m₀ c₀, NameLaws (psubst σ (label' o)) (doneTok (psubst σ l) m₀ c₀))) :
    CleanAboveDepth k label' C' := by
  intro m x p spM leM o oPres σ solved
  have spChild : IsLocSpine (childLoc m x p) := .child x p spM
  have gtDepth : k < locDepth (psubst σ (childLoc m x p)) := by
    rw [locDepth_psubst_spine spChild, locDepth_childLoc]; omega
  rcases rowsBound o oPres with ⟨inC, lblEq⟩ | ⟨l, spL, leL, shapeO⟩
  · rw [lblEq]; exact clean m x p spM leM o inC σ (refines σ solved)
  · have neLoc : ¬ NameLaws (psubst σ l) (psubst σ (childLoc m x p)) := by
      intro eqL; have dEq := locDepth_nameLaws eqL; rw [locDepth_psubst_spine spL] at dEq; omega
    refine ⟨fun m' same => ?_, fun m' c' same => ?_, fun y same => ?_⟩
    · rcases shapeO σ solved with ⟨_, hAt⟩ | ⟨_, hP⟩ | ⟨_, _, hD⟩
      · exact absurd (nameLaws_heads (hAt.symm.trans same)) (by decide)
      · exact neLoc (nameLaws_pendingTok_iff.mp (hP.symm.trans same)).1
      · exact absurd (nameLaws_heads (hD.symm.trans same)) (by decide)
    · rcases shapeO σ solved with ⟨_, hAt⟩ | ⟨_, hP⟩ | ⟨_, _, hD⟩
      · exact absurd (nameLaws_heads (hAt.symm.trans same)) (by decide)
      · exact absurd (nameLaws_heads (hP.symm.trans same)) (by decide)
      · exact neLoc (nameLaws_doneTok_iff.mp (hD.symm.trans same)).1
    · rcases shapeO σ solved with ⟨_, hAt⟩ | ⟨_, hP⟩ | ⟨_, _, hD⟩
      · exact neLoc ((locatedFrame_name.atLoc_iff _ _ _ _).mp (hAt.symm.trans same)).2
      · exact absurd (nameLaws_heads (hP.symm.trans same)) (by decide)
      · exact absurd (nameLaws_heads (hD.symm.trans same)) (by decide)

/-! ## `Splits` congruences (`BagLaws`, `BagEq`, `predotU`) -/

theorem splits_map_predotU {P : Pattern} {L : List Pattern} (s : Splits P L) :
    Splits (predotU P) (L.map predotU) := by
  induction s with
  | leaf P => exact .leaf (predotU P)
  | split _ _ ihA ihB => rw [predotU_par, List.map_append]; exact .split ihA ihB

theorem bagLaws_par_pPar (LA LB : List Pattern) :
    BagLaws (par (pPar LA) (pPar LB)) (pPar (LA ++ LB)) := by
  have s₁ : BagLaws (pPar [pPar LA, pPar LB]) (pPar (LA ++ [pPar LB])) :=
    BagLaws.of_axiom (.flatten [] LA [pPar LB])
  have s₂ : BagLaws (pPar (LA ++ [pPar LB])) (pPar (LA ++ LB ++ [])) :=
    BagLaws.of_axiom (.flatten LA LB [])
  simpa [par, List.append_nil] using s₁.trans s₂

theorem splits_bagLaws {P : Pattern} {L : List Pattern} (s : Splits P L) :
    BagLaws P (pPar L) := by
  induction s with
  | leaf P => exact (BagLaws.of_axiom (.single P)).symm
  | split _ _ ihA ihB =>
      exact (bagLaws_collection .hashBag none (.cons ihA (.cons ihB .nil))).trans
        (bagLaws_par_pPar _ _)

theorem splits_bagEq {P : Pattern} {L : List Pattern} (s : Splits P L) :
    BagEq P (pPar L) := by
  induction s with
  | leaf P => exact (bagEq_pPar_singleton P).symm
  | split _ _ ihA ihB =>
      refine (BagEq.par ihA ihB).trans ?_
      rw [bagEq_iff, components_par, components_pPar_eq, components_pPar_eq, components_pPar_eq,
        List.flatMap_append, List.map_append]

theorem bagLaws_pPar_pick1 (pre post : List Pattern) (a : Pattern) :
    BagLaws (pPar (pre ++ a :: post)) (par a (pPar (pre ++ post))) := by
  have p₁ : BagLaws (pPar (pre ++ a :: post)) (pPar (a :: (pre ++ post))) :=
    BagLaws.of_axiom (.perm List.perm_middle)
  have p₂ : BagLaws (par a (pPar (pre ++ post))) (pPar (a :: (pre ++ post))) := by
    simpa [par, List.append_nil] using
      (BagLaws.of_axiom (.flatten [a] (pre ++ post) []) :
        BagLaws (pPar [a, pPar (pre ++ post)]) (pPar ([a] ++ (pre ++ post) ++ [])))
  exact p₁.trans p₂.symm

theorem bagLaws_pPar_pick2 (pre mid post : List Pattern) (a b : Pattern) :
    BagLaws (pPar (pre ++ a :: (mid ++ b :: post)))
      (par (par a b) (pPar (pre ++ mid ++ post))) := by
  have perm : (pre ++ a :: (mid ++ b :: post)).Perm (a :: b :: (pre ++ mid ++ post)) :=
    List.perm_middle.trans (List.Perm.cons _ (by rw [← List.append_assoc]; exact List.perm_middle))
  have p₁ : BagLaws (pPar (pre ++ a :: (mid ++ b :: post)))
      (pPar ([a, b] ++ (pre ++ mid ++ post))) := BagLaws.of_axiom (.perm perm)
  have f₁ : BagLaws (par (par a b) (pPar (pre ++ mid ++ post)))
      (pPar (par a b :: (pre ++ mid ++ post))) := by
    simpa [par, List.append_nil] using
      (BagLaws.of_axiom (.flatten [par a b] (pre ++ mid ++ post) []) :
        BagLaws (pPar [par a b, pPar (pre ++ mid ++ post)])
          (pPar ([par a b] ++ (pre ++ mid ++ post) ++ [])))
  have f₂ : BagLaws (pPar ([a, b] ++ (pre ++ mid ++ post)))
      (pPar (par a b :: (pre ++ mid ++ post))) :=
    (BagLaws.of_axiom (.flatten [] [a, b] (pre ++ mid ++ post)) :
      BagLaws (pPar ([] ++ [pPar [a, b]] ++ (pre ++ mid ++ post)))
        (pPar ([] ++ [a, b] ++ (pre ++ mid ++ post)))).symm
  exact p₁.trans (f₂.trans f₁.symm)

/-! ## Explicit reflection-depth derivations (`ReflClosureDepth`, `HostedSubStepN`, `HostedSubStepC`) -/

/-- `ReflectionClosure.Step GroundPrincipal BagLaws` indexed explicitly by reflection depth `d`. -/
inductive ReflClosureDepth : ℕ → Pattern → Pattern → Prop where
  | comm (t u x A B : Pattern) (bs : Bindings) (gp : GroundPrincipal t u bs) :
      ReflClosureDepth 0 (par (pFor t x A) (pFor u x B)) (par (applyDot bs A) (applyDot bs B))
  | parallel {d : ℕ} {src tgt : Pattern} (surr : Pattern) :
      ReflClosureDepth d src tgt → ReflClosureDepth d (par src surr) (par tgt surr)
  | congruence {d : ℕ} {s s' t' t : Pattern} :
      BagLaws s s' → ReflClosureDepth d s' t' → BagLaws t' t → ReflClosureDepth d s t
  | reflect {d : ℕ} (x : Pattern) {src tgt : Pattern} :
      ReflClosureDepth d src tgt →
      ReflClosureDepth (d + 1) (pReflect x src) (pFor (tProc tgt) x pZero)

theorem ReflClosureDepth.toReflectionClosure {d : ℕ} {P Q : Pattern}
    (step : ReflClosureDepth d P Q) :
    MeTTaCalculus.ReflectionClosure.Step GroundPrincipal BagLaws P Q := by
  induction step with
  | comm t u x A B bs gp => exact .comm t u x A B bs gp
  | parallel surr _ ih => exact .parallel surr ih
  | congruence b _ a ih => exact .congruence b ih a
  | reflect x _ ih => exact .reflect x ih

/-- Shared packing derivation of reflection depth `d`. -/
inductive HostedPackStep : ℕ → Pattern → Pattern → (Pattern × Pattern) → Bindings → Prop where
  | comm {P : Pattern} (cPre cMid cPost : List Pattern) (t u ch A B : Pattern) (bs : Bindings)
      (split : Splits P (cPre ++ pFor t ch A :: (cMid ++ pFor u ch B :: cPost)))
      (noBT : binders t = []) (noBU : binders u = []) (groundCh : pvars ch = [])
      (noBA : binders A = []) (noBB : binders B = [])
      (plainOutA : PlainPatterns (applyDot bs A)) (plainOutB : PlainPatterns (applyDot bs B))
      (gp : GroundPrincipal t u bs) (convention : Apart t A u B)
      (foA : firstOrder A = true) (foB : firstOrder B = true)
      (groundT : groundBags t = true) (groundU : groundBags u = true)
      (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u) :
      HostedPackStep 0 P
        (pPar ((cPre ++ cMid ++ cPost) ++ [applyDot bs A, applyDot bs B])) (t, u) bs
  | reflect {d : ℕ} {P Q R_in : Pattern} {pair : Pattern × Pattern} {bs : Bindings}
      (cPre cPost : List Pattern) (y : Pattern)
      (split : Splits P (cPre ++ pReflect y Q :: cPost))
      (groundY : pvars y = [])
      (inner : HostedPackStep d Q R_in pair bs) :
      HostedPackStep (d + 1) P
        (pPar (cPre ++ pFor (tProc R_in) y pZero :: cPost)) pair bs
  | congr {d : ℕ} {P R R' : Pattern} {pair : Pattern × Pattern} {bs : Bindings}
      (base : HostedPackStep d P R pair bs) (bagU : BagLaws (predotU R) (predotU R')) :
      HostedPackStep d P R' pair bs

theorem HostedPackStep.solves {d : ℕ} {P R : Pattern} {pair : Pattern × Pattern} {bs : Bindings}
    (sub : HostedPackStep d P R pair bs) :
    psubst bs.lookup pair.1 = psubst bs.lookup pair.2 ∧
      SpineHasPattern pair.1 (predotU P) ∧ SpineHasPattern pair.2 (predotU P) := by
  have memSplits : ∀ {X : Pattern} {L : List Pattern}, Splits X L →
      ∀ q p, p ∈ L → SpineHasPattern q (predotU p) → SpineHasPattern q (predotU X) := by
    intro X L s; induction s with
    | leaf X => intro q p m h; obtain rfl := List.mem_singleton.mp m; exact h
    | split _ _ ihA ihB =>
        intro q p m h; rw [predotU_par]
        rcases List.mem_append.mp m with mA | mB
        · exact .parLeft _ (ihA q p mA h)
        · exact .parRight _ (ihB q p mB h)
  induction sub with
  | comm cPre cMid cPost t u ch A B bs split noBT noBU _ _ _ _ _ gp _ _ _ _ _ _ =>
      refine ⟨gp.solves, ?_, ?_⟩
      · refine memSplits split t (pFor t ch A) (by simp) ?_
        rw [predotU_pFor, predotU_of_binders_nil t noBT]; exact .guard _ _
      · refine memSplits split u (pFor u ch B) (by simp) ?_
        rw [predotU_pFor, predotU_of_binders_nil u noBU]; exact .guard _ _
  | @reflect _ _ Q _ _ _ cPre cPost y split _ _ ih =>
      refine ⟨ih.1, ?_, ?_⟩
      · refine memSplits split _ (pReflect y Q) (by simp) ?_
        rw [predotU_pReflect]; exact .reflect _ ih.2.1
      · refine memSplits split _ (pReflect y Q) (by simp) ?_
        rw [predotU_pReflect]; exact .reflect _ ih.2.2
  | congr _ _ ih => exact ih

/-- **Hosted inner step of reflection depth `d` under Interface N** (named quotes). -/
inductive HostedSubStepN : ℕ → Pattern → Pattern → (Pattern × Pattern) → Bindings → Prop where
  | comm {P : Pattern} (cPre cMid cPost : List Pattern) (t u ch A B : Pattern) (bs : Bindings)
      (split : Splits P (cPre ++ pFor t ch A :: (cMid ++ pFor u ch B :: cPost)))
      (noBT : binders t = []) (noBU : binders u = []) (groundCh : pvars ch = [])
      (noBA : binders A = []) (noBB : binders B = [])
      (plainOutA : PlainPatterns (applyDot bs A)) (plainOutB : PlainPatterns (applyDot bs B))
      (gp : GroundPrincipal t u bs) (convention : Apart t A u B)
      (foA : firstOrder A = true) (foB : firstOrder B = true)
      (groundT : groundBags t = true) (groundU : groundBags u = true)
      (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u) :
      HostedSubStepN 0 P
        (pPar ((cPre ++ cMid ++ cPost) ++ [applyDot bs A, applyDot bs B])) (t, u) bs
  | reflect {d : ℕ} {P Q R_in : Pattern} {pair : Pattern × Pattern} {bs : Bindings}
      (cPre cPost : List Pattern) (y : Pattern)
      (split : Splits P (cPre ++ pReflect y Q :: cPost))
      (groundY : pvars y = [])
      (inner : HostedSubStepN d Q R_in pair bs) :
      HostedSubStepN (d + 1) P
        (pPar (cPre ++ pFor (tProc R_in) y pZero :: cPost)) pair bs
  | congr {d : ℕ} {P R R' : Pattern} {pair : Pattern × Pattern} {bs : Bindings}
      (base : HostedSubStepN d P R pair bs)
      (bagL : BagLaws R R') (bagE : BagEq R R') (bagU : BagLaws (predotU R) (predotU R')) :
      HostedSubStepN d P R' pair bs

theorem HostedSubStepN.toPackStep {d : ℕ} {P R : Pattern} {pair : Pattern × Pattern} {bs : Bindings}
    (sub : HostedSubStepN d P R pair bs) : HostedPackStep d P R pair bs := by
  induction sub with
  | comm cPre cMid cPost t u ch A B bs sp nT nU gC nA nB pA pB gp cv fA fB gT gU cT cU =>
      exact .comm cPre cMid cPost t u ch A B bs sp nT nU gC nA nB pA pB gp cv fA fB gT gU cT cU
  | reflect cPre cPost y sp gY _ ih => exact .reflect cPre cPost y sp gY ih
  | congr _ _ _ bagU ih => exact .congr ih bagU

theorem HostedSubStepN.toBagStep {d : ℕ} {P R : Pattern} {pair : Pattern × Pattern} {bs : Bindings}
    (sub : HostedSubStepN d P R pair bs) : BagStep conventional P R := by
  induction sub with
  | comm cPre cMid cPost t u ch A B bs split _ _ _ _ _ _ _ gp conv _ _ _ _ _ _ =>
      exact .congruence (splits_bagEq split)
        (bagStep_of_pPar_comm cPre cMid cPost t u ch A B bs gp conv) (BagEq.refl _)
  | reflect cPre cPost y split _ _ ih =>
      exact .congruence (splits_bagEq split)
        (bagStep_of_pPar_refl cPre cPost y _ _ ih) (BagEq.refl _)
  | congr _ _ bagE _ ih => exact .congruence (BagEq.refl _) ih bagE

theorem HostedSubStepN.toReflClosureDepth {d : ℕ} {P R : Pattern} {pair : Pattern × Pattern}
    {bs : Bindings} (sub : HostedSubStepN d P R pair bs) : ReflClosureDepth d P R := by
  induction sub with
  | comm cPre cMid cPost t u ch A B bs split _ _ _ _ _ _ _ gp _ _ _ _ _ _ =>
      have before := (splits_bagLaws split).trans
        (bagLaws_pPar_pick2 cPre cMid cPost (pFor t ch A) (pFor u ch B))
      have after : BagLaws
          (par (par (applyDot bs A) (applyDot bs B)) (pPar (cPre ++ cMid ++ cPost)))
          (pPar ((cPre ++ cMid ++ cPost) ++ [applyDot bs A, applyDot bs B])) := by
        simpa [List.append_assoc] using
          (bagLaws_pPar_pick2 (cPre ++ cMid ++ cPost) [] [] (applyDot bs A) (applyDot bs B)).symm
      exact .congruence before (.parallel _ (.comm t u ch A B bs gp)) after
  | @reflect _ _ Q R_in _ _ cPre cPost y split _ _ ih =>
      have before := (splits_bagLaws split).trans (bagLaws_pPar_pick1 cPre cPost (pReflect y Q))
      have after := (bagLaws_pPar_pick1 cPre cPost (pFor (tProc R_in) y pZero)).symm
      exact .congruence before (.parallel _ (.reflect y ih)) after
  | congr _ bagL _ _ ih => exact .congruence (BagLaws.refl _) ih bagL

/-- **Hosted inner step of reflection depth `d` under Interface C** (closed quotes, `pvars R = []`). -/
inductive HostedSubStepC : ℕ → Pattern → Pattern → (Pattern × Pattern) → Bindings → Prop where
  | comm {P : Pattern} (cPre cMid cPost : List Pattern) (t u ch A B : Pattern) (bs : Bindings)
      (split : Splits P (cPre ++ pFor t ch A :: (cMid ++ pFor u ch B :: cPost)))
      (noBT : binders t = []) (noBU : binders u = []) (groundCh : pvars ch = [])
      (noBA : binders A = []) (noBB : binders B = [])
      (plainOutA : PlainPatterns (applyDot bs A)) (plainOutB : PlainPatterns (applyDot bs B))
      (gp : GroundPrincipal t u bs) (convention : Apart t A u B)
      (foA : firstOrder A = true) (foB : firstOrder B = true)
      (groundT : groundBags t = true) (groundU : groundBags u = true)
      (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u)
      (groundRest : ∀ q ∈ cPre ++ cMid ++ cPost, pvars q = [])
      (groundOutA : pvars (applyDot bs A) = []) (groundOutB : pvars (applyDot bs B) = []) :
      HostedSubStepC 0 P
        (pPar ((cPre ++ cMid ++ cPost) ++ [applyDot bs A, applyDot bs B])) (t, u) bs
  | reflect {d : ℕ} {P Q R_in : Pattern} {pair : Pattern × Pattern} {bs : Bindings}
      (cPre cPost : List Pattern) (y : Pattern)
      (split : Splits P (cPre ++ pReflect y Q :: cPost))
      (groundY : pvars y = [])
      (groundRest : ∀ q ∈ cPre ++ cPost, pvars q = [])
      (inner : HostedSubStepC d Q R_in pair bs) :
      HostedSubStepC (d + 1) P (pPar (cPre ++ listener y R_in :: cPost)) pair bs
  | congr {d : ℕ} {P R R' : Pattern} {pair : Pattern × Pattern} {bs : Bindings}
      (base : HostedSubStepC d P R pair bs)
      (bagE : BagEq R R') (groundR' : pvars R' = [])
      (bagU : BagLaws (predotU R) (predotU R')) :
      HostedSubStepC d P R' pair bs

private theorem forall₂_append {α β : Type*} {R : α → β → Prop} {l₁ t₁ : List α} {l₂ t₂ : List β}
    (h₁ : List.Forall₂ R l₁ l₂) (h₂ : List.Forall₂ R t₁ t₂) :
    List.Forall₂ R (l₁ ++ t₁) (l₂ ++ t₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons hr _ ih => exact .cons hr ih

private theorem mem_pvars_bagRewrite_iff {p q : Pattern} (h : ReflQuotient.BagRewrite p q)
    (v : String) : v ∈ pvars p ↔ v ∈ pvars q := by
  induction h with
  | root ax =>
      cases ax with
      | single a => simp [pPar, pvars, MeTTaOperationsComm.pvars.pvarsList]
      | empty => simp [pPar, pZero, pvars, MeTTaOperationsComm.pvars.pvarsList]
      | flatten pre inner post =>
          simp [pPar, pvars, MeTTaCalculus.Corrected.pvarsList_eq_flatMap, List.flatMap_append]
      | perm perm =>
          simp only [pPar, pvars, MeTTaCalculus.Corrected.pvarsList_eq_flatMap, List.mem_flatMap]
          exact ⟨fun ⟨c, cIn, vIn⟩ => ⟨c, perm.subset cIn, vIn⟩,
            fun ⟨c, cIn, vIn⟩ => ⟨c, perm.symm.subset cIn, vIn⟩⟩
      | zero pre post =>
          simp [pPar, pZero, pvars, MeTTaCalculus.Corrected.pvarsList_eq_flatMap,
            MeTTaOperationsComm.pvars.pvarsList]
  | apply _ pre post _ ih =>
      simp only [pvars, MeTTaCalculus.Corrected.pvarsList_eq_flatMap, List.flatMap_append,
        List.flatMap_cons, List.mem_append, ih]
  | lambda _ _ ih => simpa only [pvars] using ih
  | multiLambda _ _ _ ih => simpa only [pvars] using ih
  | substBody _ _ ih => simp only [pvars, List.mem_append, ih]
  | substRepl _ _ ih => simp only [pvars, List.mem_append, ih]
  | collection _ pre post rest _ ih =>
      cases rest <;>
        simp only [pvars, MeTTaCalculus.Corrected.pvarsList_eq_flatMap, List.flatMap_append,
          List.flatMap_cons, List.mem_append, ih]

private theorem mem_pvars_bagLaws_iff {p q : Pattern} (h : BagLaws p q) (v : String) :
    v ∈ pvars p ↔ v ∈ pvars q := by
  induction h with
  | rel _ _ r => exact mem_pvars_bagRewrite_iff r v
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem pvars_pPar_eq_nil {xs : List Pattern} (h : ∀ q ∈ xs, pvars q = []) :
    pvars (pPar xs) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro v mem
  simp only [pPar, pvars, MeTTaCalculus.Corrected.pvarsList_eq_flatMap, List.mem_flatMap] at mem
  obtain ⟨q, qIn, vIn⟩ := mem; rw [h q qIn] at vIn; exact List.not_mem_nil vIn

theorem pvars_listener_eq_nil {y R : Pattern} (groundY : pvars y = []) (groundR : pvars R = []) :
    pvars (listener y R) = [] := by
  have canonNil : pvars (canonicalBag R) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr; intro v vIn
    have inU := (mem_pvars_bagLaws_iff (quote_closed_ground R groundR) v).mp vIn
    rw [ReflUniform.pvars_predotU, groundR] at inU
    exact List.not_mem_nil inU
  unfold listener
  simp [pFor, tProc, pZero, pvars, MeTTaOperationsComm.pvars.pvarsList, groundY, canonNil]

theorem HostedSubStepC.groundReduct {d : ℕ} {P R : Pattern} {pair : Pattern × Pattern}
    {bs : Bindings} (sub : HostedSubStepC d P R pair bs) : pvars R = [] := by
  induction sub with
  | comm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gRest gA gB =>
      apply pvars_pPar_eq_nil; intro q m
      rcases List.mem_append.mp m with inR | inOut
      · exact gRest q inR
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at inOut
        rcases inOut with rfl | rfl
        · exact gA
        · exact gB
  | reflect _ _ _ _ gY gRest _ ih =>
      apply pvars_pPar_eq_nil; intro q m
      simp only [List.mem_append, List.mem_cons] at m
      rcases m with inPre | rfl | inPost
      · exact gRest q (List.mem_append_left _ inPre)
      · exact pvars_listener_eq_nil gY ih
      · exact gRest q (List.mem_append_right _ inPost)
  | congr _ _ gR' _ _ => exact gR'

theorem HostedSubStepC.toPackStep {d : ℕ} {P R : Pattern} {pair : Pattern × Pattern}
    {bs : Bindings} (sub : HostedSubStepC d P R pair bs) : HostedPackStep d P R pair bs := by
  have reflList : ∀ xs : List Pattern, List.Forall₂ BagLaws xs xs :=
    fun xs => List.forall₂_same.mpr fun _ _ => BagLaws.refl _
  induction sub with
  | comm cPre cMid cPost t u ch A B bs sp nT nU gC nA nB pA pB gp cv fA fB gT gU cT cU _ _ _ =>
      exact .comm cPre cMid cPost t u ch A B bs sp nT nU gC nA nB pA pB gp cv fA fB gT gU cT cU
  | @reflect d P Q R_in pair bs cPre cPost y sp gY _ inner ih =>
      have qEq : BagLaws (predotU R_in) (canonicalBag R_in) :=
        (quote_closed_ground R_in inner.groundReduct).symm
      have lEq : BagLaws (predotU (pFor (tProc R_in) y pZero)) (predotU (listener y R_in)) := by
        rw [predotU_named_listener gY R_in, predotU_closed_listener gY R_in]
        unfold listener
        exact ReflQuotient.bagLaws_apply "MFor"
          (.cons (ReflQuotient.bagLaws_apply "MTermProc" (.cons qEq .nil))
            (.cons (.refl _) (.cons (.refl _) .nil)))
      have forallEq : List.Forall₂ BagLaws
          ((cPre ++ pFor (tProc R_in) y pZero :: cPost).map predotU)
          ((cPre ++ listener y R_in :: cPost).map predotU) := by
        simp only [List.map_append, List.map_cons]
        exact forall₂_append (reflList (cPre.map predotU)) (.cons lEq (reflList (cPost.map predotU)))
      have pEq : BagLaws (predotU (pPar (cPre ++ pFor (tProc R_in) y pZero :: cPost)))
          (predotU (pPar (cPre ++ listener y R_in :: cPost))) := by
        rw [predotU_pPar, predotU_pPar]; exact bagLaws_collection .hashBag none forallEq
      exact .congr (.reflect cPre cPost y sp gY ih) pEq
  | congr _ _ _ bagU ih => exact .congr ih bagU

theorem HostedSubStepC.toCanonicalBagStep {d : ℕ} {P R : Pattern} {pair : Pattern × Pattern}
    {bs : Bindings} (sub : HostedSubStepC d P R pair bs) : CanonicalBagStep conventional P R := by
  induction sub with
  | comm cPre cMid cPost t u ch A B bs split _ _ _ _ _ _ _ gp conv _ _ _ _ _ _ _ _ _ =>
      exact .congruence (splits_bagEq split)
        (canonicalBagStep_of_pPar_comm cPre cMid cPost t u ch A B bs gp conv) (BagEq.refl _)
  | reflect cPre cPost y split _ _ _ ih =>
      exact .congruence (splits_bagEq split)
        (canonicalBagStep_of_pPar_refl cPre cPost y _ _ ih) (BagEq.refl _)
  | congr _ bagE _ _ ih => exact .congruence (BagEq.refl _) ih bagE

/-! ## Non-root child heating, cooling, and backward inner-close soundness -/

section ChildRecursion

variable {O : Type*} [DecidableEq O]

theorem heating_noRoot [Infinite O] (l m : Pattern) {p : Pattern} {L : List Pattern}
    (split : Splits p L) :
    ∀ (label : O → Pattern) (C : Configuration Pattern O) (o token : O),
      o ∈ C.present → token ∈ C.present → o ≠ token →
      (∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label o)) (psubst σ (atLoc p l))) →
      (∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label token)) (psubst σ (pendingTok l m))) →
      (∃ σ₀ : PSubst, nameAction.Models σ₀ C.equations) →
      ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (rows : List O),
        LocatedRunNoRoot label C label' C' false ∧ rows.length = L.length ∧ rows.Nodup ∧
        (∀ q ∈ rows.zip L, ∀ σ : PSubst, nameAction.Models σ C'.equations →
          NameLaws (psubst σ (label' q.1)) (psubst σ (atLoc q.2 l))) ∧
        (∀ r ∈ rows, r ∈ C'.present ∧ r ≠ token ∧ (r = o ∨ r ∉ C.present)) ∧
        (∀ o' ∈ C.present, o' ≠ o → o' ∈ C'.present ∧ label' o' = label o') ∧
        (∀ o' ∈ C'.present, o' ∈ rows ∨ (o' ∈ C.present ∧ o' ≠ o ∧ label' o' = label o')) ∧
        (∀ σ : PSubst, nameAction.Models σ C'.equations → nameAction.Models σ C.equations) ∧
        (∀ τ : PSubst, nameAction.Models τ C.equations →
          ∃ w : PSubst, nameAction.Models w C'.equations ∧
            ∀ o' ∈ C.present, o' ≠ o → NameLaws (psubst w (label o')) (psubst τ (label o'))) ∧
        (∃ σ₁ : PSubst, nameAction.Models σ₁ C'.equations) := by
  induction split with
  | leaf p =>
      intro label C o token present _ apart reads _ solvable
      refine ⟨label, C, [o], .refl label C, rfl,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_, ?_,
        fun o' pO' _ => ⟨pO', rfl⟩, ?_, fun _ s => s,
        fun τ k => ⟨τ, k, fun _ _ _ => NameLaws.refl _⟩, solvable⟩
      · intro q m'; simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at m'
        subst m'; exact reads
      · intro r m'; rw [List.mem_singleton] at m'; subst m'; exact ⟨present, apart, .inl rfl⟩
      · intro o' pO'; by_cases eq : o' = o
        · exact .inl (List.mem_singleton.mpr eq)
        · exact .inr ⟨pO', eq, rfl⟩
  | @split a b LA LB _ _ ihA ihB =>
      intro label C o token present tokenPresent apart reads readsToken ⟨σ₀, known⟩
      obtain ⟨m₁, fresh₁⟩ := Infinite.exists_notMem_finset C.present
      obtain ⟨m₂, fresh₂'⟩ := Infinite.exists_notMem_finset (insert m₁ C.present)
      have m₂ne : m₂ ≠ m₁ := fun s => fresh₂' (Finset.mem_insert.mpr (.inl s))
      have fresh₂ : m₂ ∉ C.present := fun s => fresh₂' (Finset.mem_insert.mpr (.inr s))
      have tokNe₁ : token ≠ m₁ := fun s => fresh₁ (s ▸ tokenPresent)
      have tokNe₂ : token ≠ m₂ := fun s => fresh₂ (s ▸ tokenPresent)
      obtain ⟨ρ, opensFreshly⟩ := heat_fresh_exists label C o token m₁ m₂
      have pair : NameLaws (psubst σ₀ (label o))
          (atLoc (par (psubst σ₀ a) (psubst σ₀ b)) (psubst σ₀ l)) := by
        simpa [psubst_atLoc_any, psubst_par] using reads σ₀ known
      have tokR : NameLaws (psubst σ₀ (label token)) (pendingTok (psubst σ₀ l) (psubst σ₀ m)) := by
        simpa [psubst_pendingTok] using readsToken σ₀ known
      have admitted := heatChild_admitted label C o token m₁ m₂ present tokenPresent apart
        m₂ne.symm fresh₁ fresh₂ known pair tokR opensFreshly
      obtain ⟨σ₁, solved₁⟩ := solution_of_admitted admitted
      have notInC : ∀ r, r ∉ (resConf label C (heatChildN ρ o token m₁ m₂)).present →
          r = o ∨ r ∉ C.present := fun r notC₁ => by
        by_cases eq : r = o
        · exact .inl eq
        · exact .inr fun inC => notC₁ ((heat_present label C ρ o token m₁ m₂ r).mpr (.inl ⟨inC, eq⟩))
      have m₂In₁ : m₂ ∈ (resConf label C (heatChildN ρ o token m₁ m₂)).present :=
        (heat_present label C ρ o token m₁ m₂ m₂).mpr (.inr (.inr rfl))
      have tokIn₁ : token ∈ (resConf label C (heatChildN ρ o token m₁ m₂)).present :=
        (heat_present label C ρ o token m₁ m₂ token).mpr (.inl ⟨tokenPresent, apart.symm⟩)
      obtain ⟨label₂, C₂, rowsA, runA, lenA, ndA, rA, fA, frA, covA, monoA, extA, solA⟩ :=
        ihA (res label C (heatChildN ρ o token m₁ m₂)).label
          (resConf label C (heatChildN ρ o token m₁ m₂)) m₁ token
          ((heat_present label C ρ o token m₁ m₂ m₁).mpr (.inr (.inl rfl))) tokIn₁ tokNe₁.symm
          (fun σ s => (heatChild_reads_determinately label C ρ o token m₂ne.symm a b l reads s).1)
          (fun σ s => by
            rw [heat_label_old label C ρ o token m₁ m₂ tokNe₁ tokNe₂]
            exact readsToken σ (heat_back label C ρ o token m₁ m₂ s))
          ⟨σ₁, solved₁⟩
      have m₂Kept := frA m₂ m₂In₁ m₂ne
      have tokKept := frA token tokIn₁ tokNe₁
      have notM₂ : ∀ r ∈ rowsA, r ≠ m₂ := fun r inA isM₂ => by
        rcases (fA r inA).2.2 with isM₁ | notC₁
        · exact m₂ne (isM₂.symm.trans isM₁)
        · exact notC₁ (isM₂ ▸ m₂In₁)
      obtain ⟨label₃, C₃, rowsB, runB, lenB, ndB, rB, fB, frB, covB, monoB, extB, solB⟩ :=
        ihB label₂ C₂ m₂ token m₂Kept.1 tokKept.1 tokNe₂.symm
          (fun σ s => by
            rw [m₂Kept.2]
            exact (heatChild_reads_determinately label C ρ o token m₂ne.symm a b l reads
              (monoA σ s)).2)
          (fun σ s => by
            rw [tokKept.2, heat_label_old label C ρ o token m₁ m₂ tokNe₁ tokNe₂]
            exact readsToken σ (heat_back label C ρ o token m₁ m₂ (monoA σ s)))
          solA
      refine ⟨label₃, C₃, rowsA ++ rowsB, step_heatChild_noRoot admitted (runA.trans runB),
        by simp [lenA, lenB], ?_, ?_, ?_, ?_, ?_,
        fun σ s => heat_back label C ρ o token m₁ m₂ (monoA σ (monoB σ s)), ?_, solB⟩
      · refine List.nodup_append.mpr ⟨ndA, ndB, fun x inA y inB eq => ?_⟩
        rcases (fB y inB).2.2 with isM₂ | notC₂
        · exact notM₂ x inA (eq.trans isM₂)
        · exact notC₂ (eq ▸ (fA x inA).1)
      · intro q m' σ s; rw [List.zip_append lenA] at m'
        rcases List.mem_append.mp m' with inA | inB
        · have qA := List.of_mem_zip inA
          rw [(frB q.1 (fA q.1 qA.1).1 (notM₂ q.1 qA.1)).2]
          exact rA q inA σ (monoB σ s)
        · exact rB q inB σ s
      · intro r m'; rcases List.mem_append.mp m' with inA | inB
        · obtain ⟨inC₂, nTok, origA⟩ := fA r inA
          refine ⟨(frB r inC₂ (notM₂ r inA)).1, nTok, ?_⟩
          rcases origA with isM₁ | notC₁
          · exact .inr (isM₁ ▸ fresh₁)
          · exact notInC r notC₁
        · obtain ⟨inC₃, nTok, origB⟩ := fB r inB
          refine ⟨inC₃, nTok, ?_⟩
          rcases origB with isM₂ | notC₂
          · exact .inr (isM₂ ▸ fresh₂)
          · by_cases eq : r = o
            · exact .inl eq
            · exact .inr fun inC => notC₂ (frA r ((heat_present label C ρ o token m₁ m₂ r).mpr
                (.inl ⟨inC, eq⟩)) fun isM₁ => fresh₁ (isM₁ ▸ inC)).1
      · intro o' pO' notO
        have ne₁ : o' ≠ m₁ := fun e => fresh₁ (e ▸ pO')
        have ne₂ : o' ≠ m₂ := fun e => fresh₂ (e ▸ pO')
        obtain ⟨inC₂, l₂⟩ := frA o' ((heat_present label C ρ o token m₁ m₂ o').mpr
          (.inl ⟨pO', notO⟩)) ne₁
        obtain ⟨inC₃, l₃⟩ := frB o' inC₂ ne₂
        exact ⟨inC₃, l₃.trans (l₂.trans (heat_label_old label C ρ o token m₁ m₂ ne₁ ne₂))⟩
      · intro o' pO'
        rcases covB o' pO' with inB | ⟨inC₂, ne₂, l₃⟩
        · exact .inl (List.mem_append_right _ inB)
        · rcases covA o' inC₂ with inA | ⟨inC₁, ne₁, l₂⟩
          · exact .inl (List.mem_append_left _ inA)
          · rcases (heat_present label C ρ o token m₁ m₂ o').mp inC₁ with
              ⟨inC, notO⟩ | isM₁ | isM₂
            · exact .inr ⟨inC, notO, l₃.trans (l₂.trans
                (heat_label_old label C ρ o token m₁ m₂ ne₁ ne₂))⟩
            · exact absurd isM₁ ne₁
            · exact absurd isM₂ ne₂
      · intro τ knownτ
        obtain ⟨w₁, s₁, a₁⟩ := heat_extends label C o token m₁ m₂ present tokenPresent l m a b
          reads readsToken opensFreshly knownτ
        obtain ⟨w₂, s₂, a₂⟩ := extA w₁ s₁
        obtain ⟨w₃, s₃, a₃⟩ := extB w₂ s₂
        refine ⟨w₃, s₃, fun o' p' notO => ?_⟩
        have ne₁ : o' ≠ m₁ := fun e => fresh₁ (e ▸ p')
        have ne₂ : o' ≠ m₂ := fun e => fresh₂ (e ▸ p')
        have in₁ := (heat_present label C ρ o token m₁ m₂ o').mpr (.inl ⟨p', notO⟩)
        have lab₁ := heat_label_old label C ρ o token m₁ m₂ ne₁ ne₂
        obtain ⟨in₂, lab₂⟩ := frA o' in₁ ne₁
        have ag₂ := a₂ o' in₁ ne₁; have ag₃ := a₃ o' in₂ ne₂
        rw [lab₂, lab₁] at ag₃; rw [lab₁] at ag₂
        exact ag₃.trans (ag₂.trans (a₁ o' p'))

theorem cooling_noRoot_extends (l m : Pattern) :
    ∀ (order : List (O × Pattern)) (supply : List O) (label : O → Pattern)
      (C : Configuration Pattern O) (d : O) (c : Pattern),
      supply.length = order.length → supply.Nodup → (∀ o ∈ supply, o ∉ C.present) →
      d ∈ C.present → (order.map Prod.fst).Nodup → (∀ q ∈ order, q.1 ∈ C.present ∧ q.1 ≠ d) →
      (∀ q ∈ order, ∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label q.1)) (psubst σ (atLoc q.2 l))) →
      (∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label d)) (psubst σ (doneTok l m c))) →
      (∃ σ₀ : PSubst, nameAction.Models σ₀ C.equations) →
      ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (d' : O),
        LocatedRunNoRoot label C label' C' false ∧ (d' = d ∨ d' ∈ supply) ∧ d' ∈ C'.present ∧
        (∀ σ : PSubst, nameAction.Models σ C'.equations →
          NameLaws (psubst σ (label' d')) (psubst σ (doneTok l m (cooled c (order.map Prod.snd))))) ∧
        (∀ σ : PSubst, nameAction.Models σ C'.equations → nameAction.Models σ C.equations) ∧
        (∀ τ : PSubst, nameAction.Models τ C.equations →
          ∃ w : PSubst, nameAction.Models w C'.equations ∧
            ∀ o' ∈ C.present, o' ∉ order.map Prod.fst → o' ≠ d →
              NameLaws (psubst w (label o')) (psubst τ (label o'))) ∧
        (∃ σ₁ : PSubst, nameAction.Models σ₁ C'.equations) ∧
        (∀ o ∈ C'.present,
          o = d' ∨ (o ∈ C.present ∧ o ∉ order.map Prod.fst ∧ o ≠ d ∧ label' o = label o)) ∧
        (∀ o ∈ C.present, o ∉ order.map Prod.fst → o ≠ d →
          o ∈ C'.present ∧ label' o = label o) := by
  intro order; induction order with
  | nil =>
      intro supply label C d c _ _ _ present _ _ _ readsTok solvable
      refine ⟨label, C, d, .refl label C, .inl rfl, present, readsTok, fun _ s => s,
        fun τ k => ⟨τ, k, fun _ _ _ _ => NameLaws.refl _⟩, solvable, fun o pO => ?_,
        fun o pO _ _ => ⟨pO, rfl⟩⟩
      by_cases eq : o = d
      · exact .inl eq
      · exact .inr ⟨pO, List.not_mem_nil, eq, rfl⟩
  | cons q rest ih =>
      intro supply label C d c lens nd freshSup present ndOrd rowsPres readsRows readsTok solvable
      obtain ⟨r, a⟩ := q
      cases supply with
      | nil => simp at lens
      | cons d₁ supply' =>
          have rF := rowsPres (r, a) (by simp)
          have rR := readsRows (r, a) (by simp)
          have d₁Fresh := freshSup d₁ (by simp)
          obtain ⟨d₁NotSup, ndSup'⟩ := List.nodup_cons.mp nd
          obtain ⟨rNotRest, ndOrd'⟩ := List.nodup_cons.mp ndOrd
          obtain ⟨σ₀, known₀⟩ := solvable
          obtain ⟨ρ, fresh⟩ := ReflCorrespondence.cool_fresh_exists label C d r d₁
          have adm := ReflCorrespondence.cool_admitted label C l m c a d r d₁ readsTok rR
            rF.2.symm present rF.1 d₁Fresh known₀ fresh
          have d₁Pres : d₁ ∈ (res label C (ReflPacking.coolAt ρ d r d₁)).present :=
            (ReflCorrespondence.coolAt_present label C ρ d r d₁ d₁).mpr (.inr rfl)
          obtain ⟨σ₁, sol₁⟩ := solution_of_admitted adm
          obtain ⟨label', C', d', run', orig, pD', rD', mono, ext', sol', fromC₁, keptC₁⟩ :=
            ih supply' (res label C (ReflPacking.coolAt ρ d r d₁)).label
              (resConf label C (ReflPacking.coolAt ρ d r d₁)) d₁ (par c a)
              (by simpa using lens) ndSup'
              (fun o m' inside => by
                rcases (ReflCorrespondence.coolAt_present label C ρ d r d₁ o).mp inside with
                  ⟨old, -⟩ | eq
                · exact freshSup o (List.mem_cons_of_mem _ m') old
                · exact d₁NotSup (eq ▸ m'))
              d₁Pres ndOrd'
              (fun q' m' => by
                have f' := rowsPres q' (List.mem_cons_of_mem _ m')
                have neR : q'.1 ≠ r := fun e => rNotRest (e ▸ List.mem_map.mpr ⟨q', m', rfl⟩)
                exact ⟨(ReflCorrespondence.coolAt_present label C ρ d r d₁ q'.1).mpr
                  (.inl ⟨f'.1, f'.2, neR⟩), fun e => d₁Fresh (e ▸ f'.1)⟩)
              (fun q' m' σ s => by
                have f' := rowsPres q' (List.mem_cons_of_mem _ m')
                rw [ReflCorrespondence.coolAt_label_old label C ρ d r d₁ fun e => d₁Fresh (e ▸ f'.1)]
                exact readsRows q' (List.mem_cons_of_mem _ m') σ
                  (ReflCorrespondence.coolAt_back label C ρ d r d₁ s))
              (fun σ s => ReflPacking.cool_reads label C ρ d r d₁ l m c a readsTok rR s)
              ⟨σ₁, sol₁⟩
          have stepCool : LocatedRunNoRoot label C label' C' false :=
            (coolRun_noRoot (m := m) (.step ρ r d₁ a adm rR (.refl _ _ _))).trans run'
          refine ⟨label', C', d', stepCool,
            orig.elim (fun e => .inr (e ▸ List.mem_cons_self ..))
              (fun m' => .inr (List.mem_cons_of_mem _ m')),
            pD', rD', fun σ s => ReflCorrespondence.coolAt_back label C ρ d r d₁ (mono σ s),
            ?_, sol', ?_, ?_⟩
          · intro τ knownτ
            obtain ⟨w₁, s₁, ag₁⟩ := cool_extends label C l m c a d r d₁ readsTok rR
              present rF.1 fresh knownτ
            obtain ⟨w₂, s₂, ag₂⟩ := ext' w₁ s₁
            refine ⟨w₂, s₂, fun o' p' notOrd notD => ?_⟩
            have neR : o' ≠ r := fun e => notOrd (by simp [e])
            have notRest : o' ∉ rest.map Prod.fst := fun m' => notOrd (by simp [m'])
            have neD₁ : o' ≠ d₁ := fun e => d₁Fresh (e ▸ p')
            have in₁ := (ReflCorrespondence.coolAt_present label C ρ d r d₁ o').mpr
              (.inl ⟨p', notD, neR⟩)
            have a₂ := ag₂ o' in₁ notRest neD₁
            rw [ReflCorrespondence.coolAt_label_old label C ρ d r d₁ neD₁] at a₂
            exact a₂.trans (ag₁ o' p')
          · intro o pO
            rcases fromC₁ o pO with isD' | ⟨inC₁, notRest, neD₁, lblEq⟩
            · exact .inl isD'
            · rcases (ReflCorrespondence.coolAt_present label C ρ d r d₁ o).mp inC₁ with
                ⟨inC, neD, neR⟩ | isD₁
              · exact .inr ⟨inC, fun m' => (List.mem_cons.mp m').elim neR notRest, neD,
                  lblEq.trans (ReflCorrespondence.coolAt_label_old label C ρ d r d₁ neD₁)⟩
              · exact absurd isD₁ neD₁
          · intro o pO notOrd neD
            have neR : o ≠ r := fun e => notOrd (by simp [e])
            have notRest : o ∉ rest.map Prod.fst := fun m' => notOrd (by simp [m'])
            have neD₁ : o ≠ d₁ := fun e => d₁Fresh (e ▸ pO)
            obtain ⟨in', lbl'⟩ := keptC₁ o
              ((ReflCorrespondence.coolAt_present label C ρ d r d₁ o).mpr (.inl ⟨pO, neD, neR⟩))
              notRest neD₁
            exact ⟨in', lbl'.trans (ReflCorrespondence.coolAt_label_old label C ρ d r d₁ neD₁)⟩

/-! ## Backward recursion through `closeChildAt` (`CellsU`, `DoneCellsU`) -/

/-- Pre-commit cells at child `l` represented uniformly by `predotU` (covering nested listeners
with bound variables under Interface **N** as well as closed listeners under **C**). -/
structure CellsU (l m : Pattern) (label : O → Pattern) (C : Configuration Pattern O)
    (tk : O) (cells : List (O × Pattern)) : Prop where
  phase : PendingPhaseS l m label C tk
  nodup : (cells.map Prod.fst).Nodup
  rows : ∀ q ∈ cells, q.1 ∈ C.present ∧ q.1 ≠ tk ∧
    ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label q.1)) (psubst σ (atLoc (predotU q.2) l))
  others : ∀ o ∈ C.present, o ≠ tk → o ∉ cells.map Prod.fst →
    ∀ σ : PSubst, nameAction.Models σ C.equations →
      ∀ y : Pattern, ¬ NameLaws (psubst σ (label o)) (atLoc y (psubst σ l))

/-- Post-commit cells at child `l` represented uniformly by `predotU`. -/
structure DoneCellsU (l m : Pattern) (label : O → Pattern) (C : Configuration Pattern O)
    (d : O) (acc : Pattern) (cells : List (O × Pattern)) : Prop where
  phase : DonePhaseS l m label C d
  readsTok : ∀ σ : PSubst, nameAction.Models σ C.equations →
    NameLaws (psubst σ (label d)) (psubst σ (doneTok l m acc))
  nodup : (cells.map Prod.fst).Nodup
  rows : ∀ q ∈ cells, q.1 ∈ C.present ∧ q.1 ≠ d ∧
    ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label q.1)) (psubst σ (atLoc (predotU q.2) l))
  others : ∀ o ∈ C.present, o ≠ d → o ∉ cells.map Prod.fst →
    ∀ σ : PSubst, nameAction.Models σ C.equations →
      ∀ y : Pattern, ¬ NameLaws (psubst σ (label o)) (atLoc y (psubst σ l))

/-- **Backward inner-close soundness**: any admitted `closeChildAt` taking `(reflIn, pReflect y Q)`
at parent `l = childLoc m x_l P_l` (in `CellsU`) and `d_in` from grandchild
`gLoc = childLoc l y (predotU Q)` (in `DoneCellsU`) forces `d_in = innerTok` and `gCells = []`,
returns `gLoc` to `Clean`, and transitions `l` into `DoneCellsU` with `listenerTerm` whenever
`madeL` reads as `atLoc (predotU listenerTerm) l`. -/
theorem closeChild_commits_parent {m x_l P_l y Q acc_g listenerTerm : Pattern}
    {label : O → Pattern} {C : Configuration Pattern O}
    {pre post gCells : List (O × Pattern)} {tk reflIn innerTok d_in madeL madeTok : O}
    {ρ : PSubst} (groundY : pvars y = [])
    (parentInv : CellsU (childLoc m x_l P_l) m label C tk (pre ++ (reflIn, pReflect y Q) :: post))
    (grandInv : DoneCellsU (childLoc (childLoc m x_l P_l) y (predotU Q)) (childLoc m x_l P_l)
      label C innerTok acc_g gCells)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (closeChildAt ρ reflIn d_in tk madeL madeTok))
    (listenerQuote : ∀ σ : PSubst,
      nameAction.Models σ (res label C (closeChildAt ρ reflIn d_in tk madeL madeTok)).knowledge →
        NameLaws (psubst σ (pFor (tProc acc_g) y pZero)) (psubst σ (predotU listenerTerm))) :
    d_in = innerTok ∧ gCells = [] ∧
      Clean (childLoc (childLoc m x_l P_l) y (predotU Q))
        (res label C (closeChildAt ρ reflIn d_in tk madeL madeTok)).label
        (resConf label C (closeChildAt ρ reflIn d_in tk madeL madeTok)) ∧
      DoneCellsU (childLoc m x_l P_l) m
        (res label C (closeChildAt ρ reflIn d_in tk madeL madeTok)).label
        (resConf label C (closeChildAt ρ reflIn d_in tk madeL madeTok))
        madeTok pZero ((pre ++ post) ++ [(madeL, listenerTerm)]) := by
  let l := childLoc m x_l P_l
  let gLoc := childLoc l y (predotU Q)
  obtain ⟨_, shapes, enabled, ⟨_, σ₀, sol₀⟩, _, _⟩ := (RuleSyntax.admits_iff _).mp admitted
  have known₀ := info_known _ sol₀
  have rRefl : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflIn)) (psubst σ (atLoc (pReflect y (predotU Q)) l)) := by
    intro σ s; have r := (parentInv.rows (reflIn, pReflect y Q) (by simp)).2.2 σ s
    rwa [predotU_pReflect, predotU_ground y groundY] at r
  have zR : (atLoc (pReflect channelUnknown reflP) locL, reflIn) ∈
      (closeChildAt ρ reflIn d_in tk madeL madeTok).rule.body.take.zip
        (closeChildAt ρ reflIn d_in tk madeL madeTok).selection.taken := by
    simp [closeChildAt, closeChild]
  have zI : (doneTok (childLoc locL channelUnknown reflP) locL accC, d_in) ∈
      (closeChildAt ρ reflIn d_in tk madeL madeTok).rule.body.take.zip
        (closeChildAt ρ reflIn d_in tk madeL madeTok).selection.taken := by
    simp [closeChildAt, closeChild]
  have zT : (pendingTok locL locM, tk) ∈
      (closeChildAt ρ reflIn d_in tk madeL madeTok).rule.body.take.zip
        (closeChildAt ρ reflIn d_in tk madeL madeTok).selection.taken := by
    simp [closeChildAt, closeChild]
  have gEq_all : ∀ {σ : PSubst},
      nameAction.Models σ ((closeChildAt ρ reflIn d_in tk madeL madeTok).information QN
        (embed label C)) →
      NameLaws (psubst σ (psubst ρ (childLoc locL channelUnknown reflP))) (psubst σ gLoc) := by
    intro σ sol
    have rR := (take_reads _ sol zR).trans (rRefl σ (info_known _ sol))
    simp only [psubst_atLoc_any, psubst_pReflect] at rR
    obtain ⟨pR, lEq⟩ := (locatedFrame_name.atLoc_iff _ _ _ _).mp rR
    obtain ⟨chEq, qEq⟩ := nameLaws_pReflect_iff.mp pR
    rw [psubst_childLoc, psubst_childLoc, psubst_childLoc]
    exact nameLaws_childLoc_iff.mpr ⟨lEq, chEq, qEq⟩
  have dInPres : d_in ∈ C.present := enabled.taken_subset (by simp [closeChildAt, Selection.commit])
  have rI₀ := take_reads _ sol₀ zI; rw [psubst_doneTok, psubst_doneTok] at rI₀
  have dEq : d_in = innerTok := grandInv.phase.unique d_in dInPres
    ⟨σ₀, known₀, _, _, rI₀.symm.trans (nameLaws_doneTok_iff.mpr
      ⟨gEq_all sol₀, NameLaws.refl _, NameLaws.refl _⟩)⟩
  subst dEq
  have gNil : gCells = [] := by
    cases gCells with
    | nil => rfl
    | cons q _ =>
        have qF := grandInv.rows q (List.mem_cons_self ..)
        exact False.elim (closeChild_waits label C y (predotU Q) l reflIn d_in tk madeL madeTok ρ
          rRefl qF.1 qF.2.2 admitted)
  subst gNil
  have cleanG : Clean gLoc (res label C (closeChildAt ρ reflIn d_in tk madeL madeTok)).label
      (resConf label C (closeChildAt ρ reflIn d_in tk madeL madeTok)) :=
    (close_returns_to_clean_S grandInv.phase _ admitted (.inr ⟨rfl, σ₀, sol₀, gEq_all sol₀⟩)).2
  have rTk₀ := (take_reads _ sol₀ zT).trans (parentInv.phase.reads σ₀ known₀)
  rw [psubst_pendingTok] at rTk₀
  have stepAtL : StepAtS l label C (closeChildAt ρ reflIn d_in tk madeL madeTok) :=
    ⟨.inr rfl, σ₀, sol₀, (pending_reading_S rTk₀).1⟩
  have mLNeMT : madeL ≠ madeTok := by simpa [closeChildAt] using shapes.2.1
  have closeR : ∀ {σ : PSubst},
      nameAction.Models σ (res label C (closeChildAt ρ reflIn d_in tk madeL madeTok)).knowledge →
      _ := fun {σ} s =>
    closeChild_reads label C y (predotU Q) acc_g l m reflIn d_in tk madeL madeTok ρ rRefl
      grandInv.readsTok parentInv.phase.reads mLNeMT (σ := σ) s
  rcases pending_phase_step_S parentInv.phase _ admitted with ⟨notS, -⟩ | ⟨-, d_p, doneP⟩
  · exact absurd stepAtL notS
  · have mtEq : madeTok = d_p := doneP.unique madeTok
      ((result_present _ madeTok).mpr (.inr (by simp [closeChildAt])))
      ⟨σ₀, sol₀, _, _, by simpa [psubst_doneTok] using (closeR sol₀).2.2⟩
    subst mtEq
    have freshMade : madeL ∉ C.present ∧ madeTok ∉ C.present := by
      simpa [closeChildAt, Selection.commit, embed] using enabled.fresh
    have permOld : ((pre ++ (reflIn, pReflect y Q) :: post).map Prod.fst).Perm
        (reflIn :: (pre ++ post).map Prod.fst) := by
      simp only [List.map_append, List.map_cons]; exact List.perm_middle
    obtain ⟨reflOut, ndRest⟩ := List.nodup_cons.mp (permOld.nodup_iff.mp parentInv.nodup)
    have restIn : ∀ q ∈ pre ++ post, q ∈ pre ++ (reflIn, pReflect y Q) :: post := fun q m' =>
      (List.mem_append.mp m').elim (List.mem_append_left _)
        (fun r => List.mem_append_right _ (List.mem_cons_of_mem _ r))
    have dNotCells : d_in ∉ (pre ++ (reflIn, pReflect y Q) :: post).map Prod.fst := by
      intro inM; obtain ⟨q, qIn, eqD⟩ := List.mem_map.mp inM
      have rAt := (parentInv.rows q qIn).2.2 σ₀ known₀
      have rDn := grandInv.readsTok σ₀ known₀
      rw [eqD, psubst_atLoc_any] at rAt; rw [psubst_doneTok] at rDn
      exact absurd (nameLaws_heads (rAt.symm.trans rDn)) (by decide)
    refine ⟨rfl, rfl, cleanG, doneP, fun σ s => (closeR s).2.2, ?_, ?_, ?_⟩
    · rw [List.map_append, List.nodup_append]
      refine ⟨ndRest, by simp, fun a inR b inM ab => ?_⟩
      obtain ⟨q, qIn, rfl⟩ := List.mem_map.mp inR
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at inM; subst inM
      exact freshMade.1 (ab ▸ (parentInv.rows q (restIn q qIn)).1)
    · intro q qM; rcases List.mem_append.mp qM with inRest | inM
      · have qOld := restIn q inRest
        obtain ⟨qPres, qNeTk, qR⟩ := parentInv.rows q qOld
        have neR : q.1 ≠ reflIn := fun e => reflOut (e ▸ List.mem_map.mpr ⟨q, inRest, rfl⟩)
        have neD : q.1 ≠ d_in := fun e => dNotCells (e ▸ List.mem_map.mpr ⟨q, qOld, rfl⟩)
        have neML : q.1 ≠ madeL := fun e => freshMade.1 (e ▸ qPres)
        have neMT : q.1 ≠ madeTok := fun e => freshMade.2 (e ▸ qPres)
        refine ⟨(result_present _ q.1).mpr (.inl ⟨qPres, by simp [closeChildAt, neR, neD, qNeTk]⟩),
          neMT, fun σ s => ?_⟩
        rw [result_label_old _ (by simp [closeChildAt, neML, neMT])]
        exact qR σ (info_known _ s)
      · simp only [List.mem_singleton] at inM; subst inM
        refine ⟨(result_present _ madeL).mpr (.inr (by simp [closeChildAt])), mLNeMT, fun σ s => ?_⟩
        refine (closeR s).2.1.trans ?_
        rw [psubst_atLoc_any, psubst_atLoc_any]
        exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨listenerQuote σ s, NameLaws.refl _⟩
    · intro o oP neMT notPost σ s z same
      rcases result_row oP with made | ⟨old, notTaken, -, lblOld⟩
      · simp only [closeChildAt, List.mem_cons, List.not_mem_nil, or_false] at made
        rcases made with rfl | rfl
        · exact notPost (by simp)
        · exact neMT rfl
      · rw [lblOld] at same
        have neTk : o ≠ tk := fun e => notTaken (by simp [closeChildAt, e])
        have neR : o ≠ reflIn := fun e => notTaken (by simp [closeChildAt, e])
        refine parentInv.others o old neTk (fun inAll => ?_) σ (info_known _ s) z same
        rcases List.mem_cons.mp (permOld.subset inAll) with rfl | inRest
        · exact neR rfl
        · exact notPost (by rw [List.map_append]; exact List.mem_append_left _ inRest)

/-- **Backward inner-close soundness — Interface N (`BagStep`)**. -/
theorem closeChild_commits_parent_N {m x_l P_l y Q R_in acc_g : Pattern}
    {label : O → Pattern} {C : Configuration Pattern O}
    {pre post gCells : List (O × Pattern)} {tk reflIn innerTok d_in madeL madeTok : O}
    {ρ : PSubst} (groundY : pvars y = [])
    (parentInv : CellsU (childLoc m x_l P_l) m label C tk (pre ++ (reflIn, pReflect y Q) :: post))
    (grandInv : DoneCellsU (childLoc (childLoc m x_l P_l) y (predotU Q)) (childLoc m x_l P_l)
      label C innerTok acc_g gCells)
    (bagAcc : ∀ σ : PSubst, nameAction.Models σ C.equations →
      BagLaws (psubst σ acc_g) (psubst σ (predotU R_in)))
    (stepIn : BagStep conventional Q R_in)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (closeChildAt ρ reflIn d_in tk madeL madeTok)) :
    d_in = innerTok ∧ gCells = [] ∧
      Clean (childLoc (childLoc m x_l P_l) y (predotU Q))
        (res label C (closeChildAt ρ reflIn d_in tk madeL madeTok)).label
        (resConf label C (closeChildAt ρ reflIn d_in tk madeL madeTok)) ∧
      DoneCellsU (childLoc m x_l P_l) m
        (res label C (closeChildAt ρ reflIn d_in tk madeL madeTok)).label
        (resConf label C (closeChildAt ρ reflIn d_in tk madeL madeTok))
        madeTok pZero ((pre ++ post) ++ [(madeL, pFor (tProc R_in) y pZero)]) ∧
      BagStep conventional (pPar ((pre ++ (reflIn, pReflect y Q) :: post).map Prod.snd))
        (pPar (((pre ++ post) ++ [(madeL, pFor (tProc R_in) y pZero)]).map Prod.snd)) := by
  obtain ⟨e₁, e₂, clG, doneP⟩ := closeChild_commits_parent (listenerTerm := pFor (tProc R_in) y pZero)
    groundY parentInv grandInv admitted fun σ s => by
      rw [predotU_named_listener groundY R_in, psubst_pFor, psubst_pFor, psubst_tProc, psubst_tProc]
      exact nameLaws_pFor_iff.mpr
        ⟨nameLaws_tProc (bagAcc σ (info_known _ s)), NameLaws.refl _, NameLaws.refl _⟩
  have stepL : BagStep conventional (pPar ((pre ++ (reflIn, pReflect y Q) :: post).map Prod.snd))
      (pPar (((pre ++ post) ++ [(madeL, pFor (tProc R_in) y pZero)]).map Prod.snd)) := by
    have s₁ : BagStep conventional (pPar ((pre ++ (reflIn, pReflect y Q) :: post).map Prod.snd))
        (pPar (pre.map Prod.snd ++ pFor (tProc R_in) y pZero :: post.map Prod.snd)) := by
      simpa [List.map_append] using
        bagStep_of_pPar_refl (pre.map Prod.snd) (post.map Prod.snd) y Q R_in stepIn
    have perm : (pre.map Prod.snd ++ pFor (tProc R_in) y pZero :: post.map Prod.snd).Perm
        (((pre ++ post) ++ [(madeL, pFor (tProc R_in) y pZero)]).map Prod.snd) := by
      simp only [List.map_append, List.map_cons, List.map_nil]
      exact List.perm_middle.trans
        (List.perm_append_comm (l₁ := [pFor (tProc R_in) y pZero])
          (l₂ := pre.map Prod.snd ++ post.map Prod.snd))
    exact .congruence (BagEq.refl _) s₁ (bagEq_pPar_perm perm)
  exact ⟨e₁, e₂, clG, doneP, stepL⟩

/-- **Backward inner-close soundness — Interface C (`CanonicalBagStep`, `pvars R_in = []`)**. -/
theorem closeChild_commits_parent_C {m x_l P_l y Q R_in acc_g : Pattern}
    {label : O → Pattern} {C : Configuration Pattern O}
    {pre post gCells : List (O × Pattern)} {tk reflIn innerTok d_in madeL madeTok : O}
    {ρ : PSubst} (groundY : pvars y = []) (groundRin : pvars R_in = [])
    (parentInv : CellsU (childLoc m x_l P_l) m label C tk (pre ++ (reflIn, pReflect y Q) :: post))
    (grandInv : DoneCellsU (childLoc (childLoc m x_l P_l) y (predotU Q)) (childLoc m x_l P_l)
      label C innerTok acc_g gCells)
    (bagAcc : ∀ σ : PSubst, nameAction.Models σ C.equations →
      BagLaws (psubst σ acc_g) (psubst σ (predotU R_in)))
    (stepIn : CanonicalBagStep conventional Q R_in)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (closeChildAt ρ reflIn d_in tk madeL madeTok)) :
    d_in = innerTok ∧ gCells = [] ∧
      Clean (childLoc (childLoc m x_l P_l) y (predotU Q))
        (res label C (closeChildAt ρ reflIn d_in tk madeL madeTok)).label
        (resConf label C (closeChildAt ρ reflIn d_in tk madeL madeTok)) ∧
      DoneCellsU (childLoc m x_l P_l) m
        (res label C (closeChildAt ρ reflIn d_in tk madeL madeTok)).label
        (resConf label C (closeChildAt ρ reflIn d_in tk madeL madeTok))
        madeTok pZero ((pre ++ post) ++ [(madeL, listener y R_in)]) ∧
      CanonicalBagStep conventional (pPar ((pre ++ (reflIn, pReflect y Q) :: post).map Prod.snd))
        (pPar (((pre ++ post) ++ [(madeL, listener y R_in)]).map Prod.snd)) := by
  have qEq : BagLaws (predotU R_in) (canonicalBag R_in) := (quote_closed_ground R_in groundRin).symm
  obtain ⟨e₁, e₂, clG, doneP⟩ := closeChild_commits_parent (listenerTerm := listener y R_in)
    groundY parentInv grandInv admitted fun σ s => by
      rw [predotU_closed_listener groundY R_in]
      unfold listener
      rw [psubst_pFor, psubst_pFor, psubst_tProc, psubst_tProc]
      exact nameLaws_pFor_iff.mpr
        ⟨nameLaws_tProc ((bagAcc σ (info_known _ s)).trans (bagLaws_psubst σ qEq)),
          NameLaws.refl _, NameLaws.refl _⟩
  have stepL : CanonicalBagStep conventional
      (pPar ((pre ++ (reflIn, pReflect y Q) :: post).map Prod.snd))
      (pPar (((pre ++ post) ++ [(madeL, listener y R_in)]).map Prod.snd)) := by
    have s₁ : CanonicalBagStep conventional
        (pPar ((pre ++ (reflIn, pReflect y Q) :: post).map Prod.snd))
        (pPar (pre.map Prod.snd ++ listener y R_in :: post.map Prod.snd)) := by
      simpa [List.map_append] using
        canonicalBagStep_of_pPar_refl (pre.map Prod.snd) (post.map Prod.snd) y Q R_in stepIn
    have perm : (pre.map Prod.snd ++ listener y R_in :: post.map Prod.snd).Perm
        (((pre ++ post) ++ [(madeL, listener y R_in)]).map Prod.snd) := by
      simp only [List.map_append, List.map_cons, List.map_nil]
      exact List.perm_middle.trans
        (List.perm_append_comm (l₁ := [listener y R_in])
          (l₂ := pre.map Prod.snd ++ post.map Prod.snd))
    exact .congruence (BagEq.refl _) s₁ (bagEq_pPar_perm perm)
  exact ⟨e₁, e₂, clG, doneP, stepL⟩

end ChildRecursion

/-! ## Shared row-splitting, phase, and initial-encoding helpers -/

theorem split_rows_1 {α β : Type*} {rows : List α} {pre post : List β} {b : β}
    (len : rows.length = (pre ++ b :: post).length) :
    ∃ rPre r rPost, rows = rPre ++ r :: rPost ∧ rPre.length = pre.length ∧
      rPost.length = post.length := by
  have h₁ : pre.length < rows.length := by simp at len; omega
  refine ⟨rows.take pre.length, rows[pre.length], rows.drop (pre.length + 1), ?_,
    List.length_take_of_le (Nat.le_of_lt h₁), ?_⟩
  · conv_lhs => rw [← List.take_append_drop pre.length rows, List.drop_eq_getElem_cons h₁]
  · simp at len ⊢; omega

theorem split_rows_2 {α β : Type*} {rows : List α} {pre mid post : List β} {a b : β}
    (len : rows.length = (pre ++ a :: (mid ++ b :: post)).length) :
    ∃ rPre r₁ rMid r₂ rPost,
      rows = rPre ++ r₁ :: (rMid ++ r₂ :: rPost) ∧
      rPre.length = pre.length ∧ rMid.length = mid.length ∧ rPost.length = post.length := by
  obtain ⟨rPre, r₁, tail, rfl, lPre, lTail⟩ := split_rows_1 len
  obtain ⟨rMid, r₂, rPost, rfl, lMid, lPost⟩ := split_rows_1 lTail
  exact ⟨rPre, r₁, rMid, r₂, rPost, rfl, lPre, lMid, lPost⟩

theorem pending_anchor_P {O : Type*} {m x_l P : Pattern} {label : O → Pattern}
    {C : Configuration Pattern O} {tk : O}
    (readsTok : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label tk)) (psubst σ (pendingTok (childLoc m x_l (predotU P)) m)))
    {K' : EquationStore Pattern}
    (refines : ∀ σ : PSubst, nameAction.Models σ K' → nameAction.Models σ C.equations)
    {w σ₀ : PSubst} (solvedW : nameAction.Models w K') (known₀ : nameAction.Models σ₀ C.equations)
    (onTk : NameLaws (psubst w (label tk)) (psubst σ₀ (label tk))) :
    NameLaws (psubst w (predotU P)) (psubst σ₀ (predotU P)) := by
  have both := (readsTok w (refines w solvedW)).symm.trans (onTk.trans (readsTok σ₀ known₀))
  rw [psubst_pendingTok, psubst_pendingTok] at both
  have lEq := (nameLaws_pendingTok_iff.mp both).1
  rw [psubst_childLoc, psubst_childLoc] at lEq
  exact (nameLaws_childLoc_iff.mp lEq).2.2

theorem donePhaseS_after_cool {O : Type*} {l m acc : Pattern} {label₃ label₄ : O → Pattern}
    {C₃ C₄ : Configuration Pattern O} {madeTok d₄ : O} {order : List (O × Pattern)}
    (done₃ : DonePhaseS l m label₃ C₃ madeTok) (pD₄ : d₄ ∈ C₄.present)
    (rD₄ : ∀ σ : PSubst, nameAction.Models σ C₄.equations →
      NameLaws (psubst σ (label₄ d₄)) (psubst σ (doneTok l m acc)))
    (monoCool : ∀ σ : PSubst, nameAction.Models σ C₄.equations → nameAction.Models σ C₃.equations)
    (covCool : ∀ o ∈ C₄.present,
      o = d₄ ∨ (o ∈ C₃.present ∧ o ∉ order.map Prod.fst ∧ o ≠ madeTok ∧ label₄ o = label₃ o)) :
    DonePhaseS l m label₄ C₄ d₄ := by
  refine ⟨pD₄, fun σ s => ⟨psubst σ acc, by simpa [psubst_doneTok] using rD₄ σ s⟩, ?_, ?_⟩
  · rintro o oP ⟨σ, s, m', c', same⟩
    rcases covCool o oP with rfl | ⟨inC₃, -, neMT, lblEq⟩
    · rfl
    · rw [lblEq] at same
      exact absurd (done₃.unique o inC₃ ⟨σ, monoCool σ s, m', c', same⟩) neMT
  · rintro o oP ⟨σ, s, m', same⟩
    rcases covCool o oP with rfl | ⟨inC₃, -, -, lblEq⟩
    · have both := same.symm.trans (rD₄ σ s); rw [psubst_doneTok] at both
      exact absurd (nameLaws_heads both) (by decide)
    · rw [lblEq] at same
      exact done₃.noPend o inC₃ ⟨σ, monoCool σ s, m', same⟩

/-- Canonical single-row root label encoding a source process `P`. -/
def encodeLabel (P : Pattern) : ℕ → Pattern := fun _ => atLoc (predotU P) rootLoc

/-- Canonical single-row configuration (`present = {0}`, `equations = []`). -/
def encodeConf : Configuration Pattern ℕ := ⟨[], {0}⟩

/-- Every source process `P` initializes `NoRootTokens`, `RootCells`, `CleanChildren`, and `FreeOnPats`. -/
theorem single_root_init (P : Pattern) (pats : List Pattern) :
    NoRootTokens (encodeLabel P) encodeConf ∧
    RootCells (encodeLabel P) encodeConf [(0, P)] ∧
    CleanChildren (encodeLabel P) encodeConf ∧
    FreeOnPats pats encodeConf.equations := by
  refine ⟨fun _ _ σ _ => ⟨fun _ h => ?_, fun _ _ h => ?_⟩,
    ⟨by simp, fun c cIn => ?_, fun o oP notIn _ _ _ _ => ?_⟩,
    fun _ _ _ _ _ _ _ σ _ => ⟨fun _ h => ?_, fun _ _ h => ?_, fun _ h => ?_⟩,
    fun τ => ⟨τ, fun _ m => absurd m List.not_mem_nil, fun _ _ => NameLaws.refl _⟩⟩
  · change NameLaws (psubst σ (atLoc (predotU P) rootLoc)) _ at h
    rw [psubst_atLoc_any] at h; exact absurd (nameLaws_heads h) (by decide)
  · change NameLaws (psubst σ (atLoc (predotU P) rootLoc)) _ at h
    rw [psubst_atLoc_any] at h; exact absurd (nameLaws_heads h) (by decide)
  · obtain rfl := List.mem_singleton.mp cIn; exact ⟨by simp [encodeConf], fun _ _ => NameLaws.refl _⟩
  · have oZero : o = 0 := by simpa [encodeConf] using oP
    exact absurd (by simp [oZero]) notIn
  · change NameLaws (psubst σ (atLoc (predotU P) rootLoc)) _ at h
    rw [psubst_atLoc_any] at h; exact absurd (nameLaws_heads h) (by decide)
  · change NameLaws (psubst σ (atLoc (predotU P) rootLoc)) _ at h
    rw [psubst_atLoc_any] at h; exact absurd (nameLaws_heads h) (by decide)
  · change NameLaws (psubst σ (atLoc (predotU P) rootLoc)) _ at h
    rw [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at h
    exact absurd (nameLaws_heads ((locatedFrame_name.atLoc_iff _ _ _ _).mp h).2) (by decide)

/-- `(0)` as a process-quoting term, and the nested showcase source processes. -/
def nestedZeroTerm : Pattern := tProc pZero
def nestedVarY : Pattern := .fvar "y"
def nestedCanaryUnifier : Bindings := [("y", nestedZeroTerm)]
def nestedCanaryInner : Pattern :=
  par (pFor nestedZeroTerm demoChan pZero) (pFor nestedVarY demoChan nestedVarY)
def nestedCanarySource : Pattern := pReflect demoChan (pReflect demoChan nestedCanaryInner)

theorem nestedCanaryUnifier_gp :
    GroundPrincipal nestedZeroTerm nestedVarY nestedCanaryUnifier := by
  refine ⟨by decide +kernel, ?_, by decide +kernel, ?_⟩
  · intro x mem
    have xEq : x = "y" := by
      simpa [nestedZeroTerm, nestedVarY, tProc, pZero, pvars,
        MeTTaOperationsComm.pvars.pvarsList] using mem
    subst xEq; exact ⟨nestedZeroTerm, rfl, by decide +kernel⟩
  · intro σ solves x mem v found
    have xEq : x = "y" := by
      simpa [nestedZeroTerm, nestedVarY, tProc, pZero, pvars,
        MeTTaOperationsComm.pvars.pvarsList] using mem
    subst xEq
    have vEq : v = nestedZeroTerm :=
      (by simpa [nestedCanaryUnifier, Bindings.lookup] using found : nestedZeroTerm = v).symm
    subst vEq
    exact solves.symm.trans (psubst_of_pvars_nil σ nestedZeroTerm (by decide +kernel))

def nestedOpenInner : Pattern :=
  par (pFor (.fvar "a1") demoChan (.fvar "a1")) (pFor pZero demoChan (.fvar "a"))
def nestedOpenSource : Pattern := pReflect demoChan (pReflect demoChan nestedOpenInner)
def nestedOpenUnifier : Bindings := [("a1", pZero)]

theorem nestedOpenUnifier_gp :
    GroundPrincipal (.fvar "a1") pZero nestedOpenUnifier := by
  refine ⟨by decide +kernel, ?_, by decide +kernel, ?_⟩
  · intro x mem
    have xEq : x = "a1" := by
      simpa [pZero, pvars, MeTTaOperationsComm.pvars.pvarsList] using mem
    subst xEq; exact ⟨pZero, rfl, by decide +kernel⟩
  · intro σ solves x mem v found
    have xEq : x = "a1" := by
      simpa [pZero, pvars, MeTTaOperationsComm.pvars.pvarsList] using mem
    subst xEq
    have vEq : v = pZero :=
      (by simpa [nestedOpenUnifier, Bindings.lookup] using found : pZero = v).symm
    subst vEq
    exact solves.trans (psubst_pZero σ)

#print axioms locDepth_psubst_spine
#print axioms cleanAboveDepth_of_subset
#print axioms ReflClosureDepth.toReflectionClosure
#print axioms HostedSubStepN.toPackStep
#print axioms HostedSubStepN.toBagStep
#print axioms HostedSubStepN.toReflClosureDepth
#print axioms HostedSubStepC.groundReduct
#print axioms HostedSubStepC.toPackStep
#print axioms HostedSubStepC.toCanonicalBagStep
#print axioms heating_noRoot
#print axioms cooling_noRoot_extends
#print axioms closeChild_commits_parent
#print axioms closeChild_commits_parent_N
#print axioms closeChild_commits_parent_C

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem
