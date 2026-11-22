import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflLocatedStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflLocatedControls

/-!
# Controls of the one-step token and of the close's guard, at the name frame

* **Without the token a child takes two steps** (`two_steps_without_token`): the comm rule at a child location
  `L` without the `Pending`/`Done` token fires twice at one child holding two redexes, at fresh openings; the
  child's bag after both steps, `0 | 0 | 0 | 0`, is no bag after one step, even under the quote
  (`two_step_bag_differs`), so REFL would quote a two-step reduct. With the token the second step is refused
  (`ReflLocatedStep.done_phase_step`).
* **Without the absence guard a partially cooled child is quoted** (`unguarded_close_quotes_partial`): a close
  that takes the reflection and the child's `Done` token without asking for the absence of the child's rows is
  admitted while a row is left at the child, and quotes the accumulator `0` instead of the child's bag
  (`partial_quote_differs`). The located program's close is refused there (`guarded_close_refused`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflLocatedStep.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar nQuote tProc pReflect demoChan)
open MeTTaOperationsComm (psubst PSubst pvars psubst_of_pvars_nil commSelection psubst_pFor)
open MeTTaCalculus.Corrected (psubstList_eq_map)
open FiniteProgram (commRule firstPattern secondPattern channelUnknown firstBody secondBody)
open Comm (Tm X E renameBy ruleVars)
open OneFrame (embed)
open ReflNames (NameLaws nameAction QN QNE nameLaws_of_eq nameFiring fresh_name nameLaws_tProc bagLaws_of_nameLaws
  nameLaws_pFor_iff)
open ReflLocated (atLoc rootLoc childLoc doneTok locL reflP accC anyY atRule located closeRoot closeRoot_mem
  locatedFrame_name psubst_atLoc_any)
open ReflLocated.Controls (childOne pvars_childOne)

/-! ## Without the token a child takes two steps -/

/-- **The comm rule at a child location `L`, without the token.** -/
def commFree : Rule Tm := atRule locL commRule

/-- Its program. -/
def freeProgram : Program Tm := {commFree}

/-- The token-free COMM at the syntactic frame: take `first` and `second`, make `made₁` and `made₂`. -/
def freeAtX (ρ : PSubst) (first second made₁ made₂ : ℕ) : Firing ℕ E freeProgram PUnit.unit :=
  ⟨commFree, rfl, PUnit.unit, ρ, commSelection first second made₁ made₂, []⟩

/-- The same firing at the name frame. -/
abbrev freeAt (ρ : PSubst) (first second made₁ made₂ : ℕ) : Firing ℕ QNE freeProgram PUnit.unit :=
  nameFiring (freeAtX ρ first second made₁ made₂)

/-- An input with the pattern `0` on `@0`, and one on `@(@0)`. -/
def inputA : Pattern := pFor pZero demoChan pZero
def inputB : Pattern := pFor pZero (nQuote demoChan) pZero

/-- Two redexes at the child: two `inputA` and two `inputB`. -/
def rowsTwoRedexes : ℕ → Pattern := fun o =>
  if o = 0 ∨ o = 1 then atLoc inputA childOne else if o = 2 ∨ o = 3 then atLoc inputB childOne else pZero

/-- No knowledge; identities `0` to `3` present. -/
def twoRedexes : Configuration Pattern ℕ := ⟨[], {0, 1, 2, 3}⟩

/-- The instance of the token-free COMM's unknowns on an input pair with pattern `0` and continuation `0`. -/
def freeInstance (channel : Pattern) : PSubst := fun v =>
  if v = "T1" then some pZero else if v = "T2" then some pZero else if v = "X" then some channel
  else if v = "K1" then some pZero else if v = "K2" then some pZero else if v = "L" then some childOne else none

theorem free_agrees (channel input : Pattern) (same : input = pFor pZero channel pZero) :
    ∀ q ∈ commFree.body.take, psubst (freeInstance channel) q = atLoc input childOne := by
  subst same
  intro q member
  simp only [commFree, atRule, RuleInstance.map, commRule, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    simp [freeInstance, atLoc, pFor, firstPattern, secondPattern, channelUnknown, firstBody, secondBody, locL,
      psubst, psubstList_eq_map]

/-- **Admission of the token-free COMM** on two present rows that read as `input @ l` (ground), at every fresh
opening, at every state whose knowledge has a solution. -/
theorem free_admitted (label : ℕ → Pattern) (C : Configuration Pattern ℕ) (channel input : Pattern)
    (shape : input = pFor pZero channel pZero) (ground : pvars (atLoc input childOne) = [])
    (first second made₁ made₂ : ℕ) (rowFirst : label first = atLoc input childOne)
    (rowSecond : label second = atLoc input childOne) (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present) (fresh₁ : made₁ ∉ C.present)
    (fresh₂ : made₂ ∉ C.present) {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations) {ρ : PSubst}
    (opensFreshly : (freeAt ρ first second made₁ made₂).Fresh QN (embed label C)) :
    (RuleSyntax.step QN ℕ QNE freeProgram).Admits (s := embed label C) (freeAt ρ first second made₁ made₂) := by
  have agrees := free_agrees channel input shape
  obtain ⟨w, solved, -, -⟩ := Comm.information_amalgamates_matched (Y := QN) (s := embed label C)
    (freeAt ρ first second made₁ made₂) opensFreshly (b := PUnit.unit) σ₀ (freeInstance channel) known
    (fun e member => by
      have single : e = (atLoc firstPattern locL, atLoc secondPattern locL) := by
        simpa [freeAt, nameFiring, freeAtX, commFree, atRule, RuleInstance.map, commRule] using member
      subst single
      show NameLaws (psubst (freeInstance channel) (atLoc firstPattern locL))
        (psubst (freeInstance channel) (atLoc secondPattern locL))
      exact nameLaws_of_eq (by simp [freeInstance, atLoc, firstPattern, secondPattern, locL, psubst,
        psubstList_eq_map]))
    (fun o member => by
      simp only [freeAt, nameFiring, freeAtX, commSelection, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact present₁
      · exact present₂)
    (fun _ member => (List.not_mem_nil member).elim)
    (fun q member => by
      have inTake : q.1 ∈ commFree.body.take := (List.of_mem_zip member).1
      have inTaken : q.2 ∈ [first, second] := (List.of_mem_zip member).2
      show NameLaws (psubst (freeInstance channel) q.1) (psubst σ₀ (label q.2))
      rw [agrees q.1 inTake]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inTaken
      rcases inTaken with same | same
      · rw [same, rowFirst, psubst_of_pvars_nil σ₀ _ ground]
        exact ReflNames.NameLaws.refl _
      · rw [same, rowSecond, psubst_of_pvars_nil σ₀ _ ground]
        exact ReflNames.NameLaws.refl _)
    (fun _ member => (List.not_mem_nil member).elim)
  refine (RuleSyntax.admits_iff _).mpr ⟨opensFreshly,
    ⟨by simp [freeAt, nameFiring, freeAtX, commSelection, distinct],
      by simp [freeAt, nameFiring, freeAtX, commSelection, madeDistinct], rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun query member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, w, solved⟩, fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim⟩
  · intro o member
    simp only [freeAt, nameFiring, freeAtX, commSelection, Selection.commit, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact present₁
    · exact present₂
  · intro o member
    simp [freeAt, nameFiring, freeAtX, commSelection, Selection.commit] at member
  · simp [freeAt, nameFiring, freeAtX, commSelection, Selection.commit]
  · rw [Finset.disjoint_left]
    intro o member
    simp only [freeAt, nameFiring, freeAtX, commSelection, Selection.commit, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact fresh₁
    · exact fresh₂

theorem free_fresh_exists (label : ℕ → Pattern) (C : Configuration Pattern ℕ) (first second made₁ made₂ : ℕ) :
    ∃ ρ : PSubst, (freeAt ρ first second made₁ made₂).Fresh QN (embed label C) := by
  obtain ⟨g, injective, avoids⟩ := Comm.exists_apart_renaming (embed label C) (ruleVars commFree)
  exact ⟨renameBy g, fresh_name (Comm.fresh_of_renaming (embed label C)
    (freeAtX (renameBy g) first second made₁ made₂) g rfl injective avoids)⟩

/-- **Without the token, a child takes two steps**: at the child holding two redexes, the token-free COMM fires on
`0` and `1`, and then, at its result, again on `2` and `3`. -/
theorem two_steps_without_token :
    ∃ ρ₁ ρ₂ : PSubst,
      (RuleSyntax.step QN ℕ QNE freeProgram).Admits (s := embed rowsTwoRedexes twoRedexes) (freeAt ρ₁ 0 1 4 5) ∧
      (RuleSyntax.step QN ℕ QNE freeProgram).Admits
        (s := embed ((freeAt ρ₁ 0 1 4 5).result QN (embed rowsTwoRedexes twoRedexes)).label
          ⟨((freeAt ρ₁ 0 1 4 5).result QN (embed rowsTwoRedexes twoRedexes)).knowledge,
            ((freeAt ρ₁ 0 1 4 5).result QN (embed rowsTwoRedexes twoRedexes)).present⟩)
        (freeAt ρ₂ 2 3 6 7) := by
  obtain ⟨ρ₁, fresh₁⟩ := free_fresh_exists rowsTwoRedexes twoRedexes 0 1 4 5
  have first := free_admitted rowsTwoRedexes twoRedexes demoChan inputA rfl (by decide +kernel) 0 1 4 5 rfl rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (σ₀ := fun _ => none)
    (fun _ member => absurd member List.not_mem_nil) fresh₁
  obtain ⟨ρ₂, fresh₂⟩ := free_fresh_exists ((freeAt ρ₁ 0 1 4 5).result QN (embed rowsTwoRedexes twoRedexes)).label
    ⟨((freeAt ρ₁ 0 1 4 5).result QN (embed rowsTwoRedexes twoRedexes)).knowledge,
      ((freeAt ρ₁ 0 1 4 5).result QN (embed rowsTwoRedexes twoRedexes)).present⟩ 2 3 6 7
  refine ⟨ρ₁, ρ₂, first, ?_⟩
  obtain ⟨_, σ₁, solved₁⟩ := ((RuleSyntax.admits_iff _).mp first).2.2.2.1
  have keep : ∀ o, o ∉ [4, 5] → ((freeAt ρ₁ 0 1 4 5).result QN (embed rowsTwoRedexes twoRedexes)).label o =
      rowsTwoRedexes o := by
    intro o notMade
    exact (Firing.result_label_other (X := QN) (s := embed rowsTwoRedexes twoRedexes) _ notMade).trans
      (congrFun (OneFrame.row_eq twoRedexes _) o)
  have presentAfter : ((freeAt ρ₁ 0 1 4 5).result QN (embed rowsTwoRedexes twoRedexes)).present = {2, 3, 4, 5} := by
    show MeTTaCalculus.OccurrenceCommits.fire twoRedexes.present ((commSelection 0 1 4 5).commit (T := Unit)) = _
    decide
  have in₂ : (2 : ℕ) ∈ ((freeAt ρ₁ 0 1 4 5).result QN (embed rowsTwoRedexes twoRedexes)).present := by
    rw [presentAfter]; decide
  have in₃ : (3 : ℕ) ∈ ((freeAt ρ₁ 0 1 4 5).result QN (embed rowsTwoRedexes twoRedexes)).present := by
    rw [presentAfter]; decide
  have out₆ : (6 : ℕ) ∉ ((freeAt ρ₁ 0 1 4 5).result QN (embed rowsTwoRedexes twoRedexes)).present := by
    rw [presentAfter]; decide
  have out₇ : (7 : ℕ) ∉ ((freeAt ρ₁ 0 1 4 5).result QN (embed rowsTwoRedexes twoRedexes)).present := by
    rw [presentAfter]; decide
  exact free_admitted ((freeAt ρ₁ 0 1 4 5).result QN (embed rowsTwoRedexes twoRedexes)).label
    ⟨((freeAt ρ₁ 0 1 4 5).result QN (embed rowsTwoRedexes twoRedexes)).knowledge,
      ((freeAt ρ₁ 0 1 4 5).result QN (embed rowsTwoRedexes twoRedexes)).present⟩
    (nQuote demoChan) inputB rfl (by decide +kernel) 2 3 6 7
    ((keep 2 (by decide)).trans rfl) ((keep 3 (by decide)).trans rfl) (by decide) (by decide)
    in₂ in₃ out₆ out₇ (σ₀ := σ₁) solved₁ fresh₂

/-- **REFL would quote a two-step reduct**: the child's bag after both steps, `0 | 0 | 0 | 0`, is not the bag after
either one step, even under the quote. -/
theorem two_step_bag_differs :
    ¬ NameLaws (tProc (pPar [pZero, pZero, pZero, pZero])) (tProc (pPar [pZero, pZero, inputB, inputB])) ∧
      ¬ NameLaws (tProc (pPar [pZero, pZero, pZero, pZero])) (tProc (pPar [inputA, inputA, pZero, pZero])) := by
  constructor <;> decide +kernel

/-! ## Without the absence guard a partially cooled child is quoted -/

/-- **The close without the absence guard.** -/
def closeUnguarded : Rule Tm :=
  ⟨PUnit.unit, ⟨[atLoc (pReflect channelUnknown reflP) rootLoc,
      doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC], [], [], [],
    [atLoc (pFor (tProc accC) channelUnknown pZero) rootLoc]⟩, []⟩

/-- Its program. -/
def unguardedProgram : Program Tm := {closeUnguarded}

/-- The reflection `@0?(0)` at the root, its child's token with nothing cooled yet, and a row left at the child. -/
def rowsPartial : ℕ → Pattern := fun o =>
  if o = 0 then atLoc (pReflect demoChan pZero) rootLoc else if o = 1 then doneTok childOne rootLoc pZero
  else atLoc inputA childOne

/-- No knowledge; identities `0`, `1`, `2` present. -/
def partialConf : Configuration Pattern ℕ := ⟨[], {0, 1, 2}⟩

/-- The unguarded close at the syntactic frame: take `0` and `1`, make `3`. -/
def unguardedAtX (ρ : PSubst) : Firing ℕ E unguardedProgram PUnit.unit :=
  ⟨closeUnguarded, rfl, PUnit.unit, ρ, ⟨[0, 1], [], [3]⟩, []⟩

/-- The located close at the syntactic frame on the same rows. -/
def guardedAtX (ρ : PSubst) : Firing ℕ E located PUnit.unit :=
  ⟨closeRoot, closeRoot_mem, PUnit.unit, ρ, ⟨[0, 1], [], [3]⟩, []⟩

/-- The instance of the close's unknowns, with the check's `Y` on the leftover row. -/
def closeInstance : PSubst := fun v =>
  if v = "X" then some demoChan else if v = "P" then some pZero else if v = "C" then some pZero
  else if v = "Y" then some inputA else none

theorem unguarded_agrees : ∀ q ∈ closeUnguarded.body.take.zip [0, 1],
    NameLaws (psubst closeInstance q.1) (psubst (fun _ => none) (rowsPartial q.2)) := by
  decide +kernel

theorem guarded_agrees : ∀ q ∈ closeRoot.body.take.zip [0, 1],
    NameLaws (psubst closeInstance q.1) (psubst (fun _ => none) (rowsPartial q.2)) := by
  decide +kernel

theorem guarded_check_leftover :
    NameLaws (psubst closeInstance (atLoc anyY (childLoc rootLoc channelUnknown reflP))) (rowsPartial 2) := by
  decide +kernel

/-- **The unguarded close quotes a partially cooled child**: at every fresh opening it is admitted at the state
with a row left at the child, every solution of its result reads the made row as `for(@0 <- @0) 0 @ Root`, and
the leftover row is still present. -/
theorem unguarded_close_quotes_partial (ρ : PSubst)
    (fresh : (nameFiring (unguardedAtX ρ)).Fresh QN (embed rowsPartial partialConf)) :
    (RuleSyntax.step QN ℕ QNE unguardedProgram).Admits (s := embed rowsPartial partialConf)
        (nameFiring (unguardedAtX ρ)) ∧
      (∀ σ : PSubst,
        nameAction.Models σ ((nameFiring (unguardedAtX ρ)).result QN (embed rowsPartial partialConf)).knowledge →
          NameLaws (psubst σ (((nameFiring (unguardedAtX ρ)).result QN (embed rowsPartial partialConf)).label 3))
            (atLoc (pFor (tProc pZero) demoChan pZero) rootLoc)) ∧
      2 ∈ ((nameFiring (unguardedAtX ρ)).result QN (embed rowsPartial partialConf)).present := by
  obtain ⟨w, solved, -, -⟩ := Comm.information_amalgamates_matched (Y := QN) (s := embed rowsPartial partialConf)
    (nameFiring (unguardedAtX ρ)) fresh (b := PUnit.unit) (fun _ => none) closeInstance
    (fun _ member => absurd member List.not_mem_nil)
    (fun _ member => absurd member List.not_mem_nil)
    (fun o member => by
      have inside : o ∈ ([0, 1] : List ℕ) := member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl <;> decide)
    (fun _ member => absurd member List.not_mem_nil)
    (fun q member => unguarded_agrees q member)
    (fun _ member => absurd member List.not_mem_nil)
  refine ⟨(RuleSyntax.admits_iff _).mpr ⟨fresh,
    ⟨(show ([0, 1] : List ℕ).Nodup by decide), (show ([3] : List ℕ).Nodup by decide), rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun query member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, w, solved⟩, fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim⟩, fun σ known => ?_, ?_⟩
  · intro o member
    simp only [nameFiring, unguardedAtX, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl <;> decide
  · intro o member
    simp [nameFiring, unguardedAtX, Selection.commit] at member
  · simp [nameFiring, unguardedAtX, Selection.commit]
  · rw [Finset.disjoint_left]
    intro o member
    simp only [nameFiring, unguardedAtX, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_singleton] at member
    subst member
    decide
  · have info : ((nameFiring (unguardedAtX ρ)).result QN (embed rowsPartial partialConf)).knowledge =
        (nameFiring (unguardedAtX ρ)).information QN (embed rowsPartial partialConf) := rfl
    rw [info] at known
    have token : NameLaws (psubst σ (psubst ρ (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC)))
        (psubst σ (rowsPartial 1)) := by
      have zipped : (QN.act (a := PUnit.unit) (b := PUnit.unit) ρ
          (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC), (1 : ℕ)) ∈
          ((nameFiring (unguardedAtX ρ)).opened QN).take.zip (nameFiring (unguardedAtX ρ)).selection.taken := by
        show _ ∈ (closeUnguarded.body.take.map _).zip [0, 1]
        simp [closeUnguarded]
        rfl
      have equal := Firing.take_solved (X := QN) (s := embed rowsPartial partialConf) (nameFiring (unguardedAtX ρ))
        (b := PUnit.unit) known zipped
      rw [OneFrame.row_eq] at equal
      exact equal
    rw [psubst_of_pvars_nil σ (rowsPartial 1) (by decide +kernel),
      show rowsPartial 1 = doneTok childOne rootLoc pZero from rfl] at token
    obtain ⟨child, -, acc⟩ := done_reading token
    rw [psubst_childLoc, psubst_childLoc] at child
    obtain ⟨-, chan, -⟩ := nameLaws_childLoc_iff.mp child
    have made : ((nameFiring (unguardedAtX ρ)).result QN (embed rowsPartial partialConf)).label 3 =
        psubst ρ (atLoc (pFor (tProc accC) channelUnknown pZero) rootLoc) := rfl
    rw [made, psubst_atLoc_any, psubst_atLoc_any, psubst_pFor, psubst_pFor,
      psubst_of_pvars_nil ρ pZero rfl, psubst_of_pvars_nil σ pZero rfl,
      psubst_of_pvars_nil ρ rootLoc rfl, psubst_of_pvars_nil σ rootLoc rfl,
      show psubst σ (psubst ρ (tProc accC)) = tProc (psubst σ (psubst ρ accC)) from rfl]
    exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr
      ⟨nameLaws_pFor_iff.mpr ⟨nameLaws_tProc (bagLaws_of_nameLaws acc), chan, ReflNames.NameLaws.refl _⟩,
        ReflNames.NameLaws.refl _⟩
  · show 2 ∈ MeTTaCalculus.OccurrenceCommits.fire partialConf.present (Selection.commit ⟨[0, 1], [], [3]⟩)
    decide

/-- The unguarded close's quote misses the leftover row: `@0` is not the quote of the child's bag `0 | for(0 <- @0)0`. -/
theorem partial_quote_differs : ¬ NameLaws (tProc pZero) (tProc (pPar [pZero, inputA])) := by
  decide +kernel

/-- **The located close is refused there**: some solution of its information reads the check's
`Y @ Child(Root, x, P)` as the leftover row. -/
theorem guarded_close_refused (ρ : PSubst)
    (fresh : (nameFiring (guardedAtX ρ)).Fresh QN (embed rowsPartial partialConf)) :
    ¬ (RuleSyntax.step QN ℕ QNE located).Admits (s := embed rowsPartial partialConf) (nameFiring (guardedAtX ρ)) := by
  intro admitted
  obtain ⟨w, solved, -, onRule⟩ := Comm.information_amalgamates_matched (Y := QN) (s := embed rowsPartial partialConf)
    (nameFiring (guardedAtX ρ)) fresh (b := PUnit.unit) (fun _ => none) closeInstance
    (fun _ member => absurd member List.not_mem_nil)
    (fun _ member => absurd member List.not_mem_nil)
    (fun o member => by
      have inside : o ∈ ([0, 1] : List ℕ) := member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl <;> decide)
    (fun _ member => absurd member List.not_mem_nil)
    (fun q member => guarded_agrees q member)
    (fun _ member => absurd member List.not_mem_nil)
  have checks := ((RuleSyntax.admits_iff _).mp admitted).2.2.2.2.1
  have holds : ∀ o ∈ partialConf.present, ¬ NameLaws
      (psubst w (psubst ρ (atLoc anyY (childLoc rootLoc channelUnknown reflP))))
      (psubst w ((nameFiring (guardedAtX ρ)).row QN (embed rowsPartial partialConf) o)) :=
    checks _ (opened_check_mem (g := nameFiring (guardedAtX ρ))
      (c := .predicate .none (atLoc anyY (childLoc rootLoc channelUnknown reflP)))
      (by simp [nameFiring, guardedAtX, closeRoot])) PUnit.unit w solved
  apply holds 2 (by decide)
  rw [OneFrame.row_eq, psubst_of_pvars_nil w (rowsPartial 2) (by decide +kernel)]
  have term : atLoc anyY (childLoc rootLoc channelUnknown reflP) ∈ (nameFiring (guardedAtX ρ)).rule.terms := by
    simp [nameFiring, guardedAtX, Rule.terms, closeRoot, checkTerms]
  exact (onRule _ term).trans guarded_check_leftover

/-- Fresh openings of both closes exist at that state. -/
theorem close_fresh_exists :
    (∃ ρ : PSubst, (nameFiring (unguardedAtX ρ)).Fresh QN (embed rowsPartial partialConf)) ∧
      ∃ ρ : PSubst, (nameFiring (guardedAtX ρ)).Fresh QN (embed rowsPartial partialConf) := by
  obtain ⟨g, injective, avoids⟩ := Comm.exists_apart_renaming (embed rowsPartial partialConf) (ruleVars closeUnguarded)
  obtain ⟨g', injective', avoids'⟩ := Comm.exists_apart_renaming (embed rowsPartial partialConf) (ruleVars closeRoot)
  exact ⟨⟨renameBy g, fresh_name (Comm.fresh_of_renaming _ (unguardedAtX (renameBy g)) g rfl injective avoids)⟩,
    ⟨renameBy g', fresh_name (Comm.fresh_of_renaming _ (guardedAtX (renameBy g')) g' rfl injective' avoids')⟩⟩

#print axioms free_admitted
#print axioms free_fresh_exists
#print axioms two_steps_without_token
#print axioms two_step_bag_differs
#print axioms unguarded_agrees
#print axioms guarded_agrees
#print axioms unguarded_close_quotes_partial
#print axioms partial_quote_differs
#print axioms guarded_close_refused
#print axioms close_fresh_exists

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflLocatedStep.Controls
