import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystemBackward

/-!
# The hosted correspondence for recursive `REFL` at `QN`

This module collects what is proved between `MeTTaCalculus.Corrected` (recursive `REFL` included,
modulo the bag laws) and the single-firing step `RuleSyntax.step QN O QNE ReflLocated.located` at
the name frame `QN`, for both quotation interfaces. It is NOT a bisimulation; the two gaps are
stated below.

* **Encoding** (`AllLocatedSpines`, `CleanRepresentsBy`, `CleanRepresents`, `encode_in_relation`):
  every `HostedNode` source process encodes into a clean root state satisfying `SystemInvN` and
  `SystemInvC`.
* **Forward simulation of hosted actions and structural changes** (`MultiSplits`, `HostedRootStepN`,
  `HostedRootStepC`, `source_step_forward_N`, `source_step_forward_C`): every `HostedRootStepN`
  (resp. `HostedRootStepC`) from `CleanRepresentsBy` is matched by a `LocatedRun` returning to
  `CleanRepresentsBy`. The relation includes a structural `equiv` constructor, so it is not a
  sub-relation of computational source steps. Its `COMM` cases and the `COMM` premises of its
  `REFL` cases carry side conditions (ground canonical patterns, the
  variable convention, binder-free first-order continuations inside reflection). No theorem here
  shows that every source step of a hosted process is a `HostedRootStepN`.
* **Backward soundness at ready states** (`hosted_correspondence_N`, `hosted_correspondence_C`):
  at a state satisfying `SystemInvBy` and `BackwardReadyN` (resp. `BackwardReadyC`), every admitted
  firing is administrative and keeps the source process, or visible and is a source step. Along a
  run, soundness is proved for `ReadyLocatedRunN` (resp. `ReadyLocatedRunC`) runs, which assume
  readiness before every firing, not at the terminal constructor. Readiness is not preserved
  by every firing from encoded states (`Controls.Readiness.admitted_heating_loses_readiness`).
  `BackwardReadyN` includes restrictions on pairs of inputs and the none query of
  aliasing between child locations, and `ReflSystemControls.cross_reflection_capture_control`
  shows a state where the aliasing occurs.
* **Conservativity on `REFL`-free processes** (`NoReflectNode`, `openRoot_refused_of_noReflect`,
  `conservativity_refl_free`): on `REFL`-free root states `openRoot` is refused, and the transitions
  correspond exactly (`↔`) to those of `FiniteProgram.program` at `QN`
  (`ReflLocated.transitions_at_root`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar nQuote tProc pReflect
  applyDot)
open MeTTaOperationsComm (psubst PSubst pvars psubst_of_pvars_nil dotted GroundPrincipal)
open MeTTaCalculus.Corrected (Apart BagEq BagStep CanonicalBagStep conventional listener)
open FiniteProgram (commRule heatRule clearRule program predot predot_pFor predot_ground
  channelUnknown dotted_nil)
open Comm (Tm)
open LogicOverTheStep.StepSpan (Succ)
open OneFrame (embed)
open ReflNames (NameLaws nameAction QN QNE nameLaws_heads)
open ReflLocated (atLoc rootLoc childLoc pendingTok doneTok locL locM reflP accC atRule located
  commChild heatChild cool closeRoot closeChild openRoot openChild exists_mem_zip located_finite
  psubst_rootLoc psubst_atLoc_any psubst_pendingTok locatedFrame_name rootState locate
  locatedNoOpen transitions_at_root)
open ReflPacking (psubst_doneTok nameLaws_doneTok_iff)
open ReflLocatedStep (located_cases psubst_childLoc nameLaws_pendingTok_iff nameLaws_childLoc_iff
  res resConf info_known take_reads read_reads taken_row result_label_old made_label result_row
  psubst_pReflect nameLaws_pReflect_iff)
open ReflUniform (predotU predotU_ground pvars_predotU)
open ReflCorrespondence (LocatedRun Splits openRootAt)

/-! ## Universal spine-location invariant and `CleanRepresents` -/

/-- At substitution `σ`, `lbl` reads modulo `NameLaws` as either a `Root` process cell or a cell /
token at a well-formed child spine `childLoc m x p` (`IsLocSpine m`). -/
def RowOnSpine (σ : PSubst) (lbl : Pattern) : Prop :=
  (∃ y, NameLaws (psubst σ lbl) (atLoc y rootLoc)) ∨
  ∃ m x p, IsLocSpine m ∧
    ((∃ y, NameLaws (psubst σ lbl) (atLoc y (psubst σ (childLoc m x p)))) ∨
     (∃ m', NameLaws (psubst σ lbl) (pendingTok (psubst σ (childLoc m x p)) m')) ∨
     (∃ m' c', NameLaws (psubst σ lbl) (doneTok (psubst σ (childLoc m x p)) m' c')))

/-- Every present row of `(label, C)` sits on `Root` or a well-formed child spine at every
solution of `C.equations`. -/
def AllLocatedSpines {O : Type*} (label : O → Pattern) (C : Configuration Pattern O) : Prop :=
  ∀ o ∈ C.present, ∀ σ : PSubst, nameAction.Models σ C.equations → RowOnSpine σ (label o)

section SpineInvariant

variable {O : Type*} [DecidableEq O]

private theorem rowOnSpine_of_pend {σ : PSubst} {lbl l' m' : Pattern}
    (sp : RowOnSpine σ lbl) (reads : NameLaws (pendingTok l' m') (psubst σ lbl)) :
    ∃ m x p, IsLocSpine m ∧ NameLaws l' (psubst σ (childLoc m x p)) := by
  rcases sp with ⟨_, hAt⟩ | ⟨m, x, p, spM, ⟨_, hAt⟩ | ⟨_, hP⟩ | ⟨_, _, hD⟩⟩
  · exact absurd (nameLaws_heads (reads.trans hAt)) (by decide)
  · exact absurd (nameLaws_heads (reads.trans hAt)) (by decide)
  · exact ⟨m, x, p, spM, (nameLaws_pendingTok_iff.mp (reads.trans hP)).1⟩
  · exact absurd (nameLaws_heads (reads.trans hD)) (by decide)

private theorem rowOnSpine_of_done {σ : PSubst} {lbl l' m' c' : Pattern}
    (sp : RowOnSpine σ lbl) (reads : NameLaws (doneTok l' m' c') (psubst σ lbl)) :
    ∃ m x p, IsLocSpine m ∧ NameLaws l' (psubst σ (childLoc m x p)) := by
  rcases sp with ⟨_, hAt⟩ | ⟨m, x, p, spM, ⟨_, hAt⟩ | ⟨_, hP⟩ | ⟨_, _, hD⟩⟩
  · exact absurd (nameLaws_heads (reads.trans hAt)) (by decide)
  · exact absurd (nameLaws_heads (reads.trans hAt)) (by decide)
  · exact absurd (nameLaws_heads (reads.trans hP)) (by decide)
  · exact ⟨m, x, p, spM, (nameLaws_doneTok_iff.mp (reads.trans hD)).1⟩

/-- **`AllLocatedSpines` is unconditionally preserved by every admitted firing of `located`.** -/
theorem allLocatedSpines_preserved {label : O → Pattern} {C : Configuration Pattern O}
    (spines : AllLocatedSpines label C) (g : Firing O QNE located PUnit.unit)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g) :
    AllLocatedSpines (res label C g).label (resConf label C g) := by
  obtain ⟨_, shapes, enabled, -⟩ := (RuleSyntax.admits_iff g).mp admitted
  intro o oPres σ solved
  have known := info_known g solved
  rcases result_row oPres with made | ⟨old, -, -, lblOld⟩
  · obtain ⟨t, inside, lblEq⟩ := made_label admitted made
    rw [lblEq]
    rcases located_cases g.member with rC | rH | rCl | cC | cH | cCl | clR | clC | opR | opC
    · rw [rC] at inside; simp only [atRule, RuleInstance.map, commRule, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl <;>
        exact .inl ⟨_, by simp only [psubst_atLoc_any, psubst_rootLoc]; exact NameLaws.refl _⟩
    · rw [rH] at inside; simp only [atRule, RuleInstance.map, heatRule, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl <;>
        exact .inl ⟨_, by simp only [psubst_atLoc_any, psubst_rootLoc]; exact NameLaws.refl _⟩
    · rw [rCl] at inside; simp [atRule, RuleInstance.map, clearRule] at inside
    · obtain ⟨oP, zP, pP⟩ := taken_row admitted (t := pendingTok locL locM) (by rw [cC]; simp [commChild])
      have rP := take_reads g solved zP; rw [psubst_pendingTok] at rP
      obtain ⟨m, x, p, spM, locEq⟩ := rowOnSpine_of_pend (spines oP pP σ known) rP
      rw [cC] at inside; simp only [commChild, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl
      · exact .inr ⟨m, x, p, spM, .inl ⟨_, by rw [psubst_atLoc_any]; exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨NameLaws.refl _, locEq⟩⟩⟩
      · exact .inr ⟨m, x, p, spM, .inl ⟨_, by rw [psubst_atLoc_any]; exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨NameLaws.refl _, locEq⟩⟩⟩
      · exact .inr ⟨m, x, p, spM, .inr (.inr ⟨_, _, by rw [psubst_doneTok]; exact nameLaws_doneTok_iff.mpr ⟨locEq, NameLaws.refl _, NameLaws.refl _⟩⟩)⟩
    · obtain ⟨oP, zP⟩ := exists_mem_zip shapes.2.2.2.1 (x := pendingTok locL locM) (by rw [cH]; simp [heatChild])
      have pP : oP ∈ C.present := enabled.kept_subset (by simpa [Selection.commit] using (List.of_mem_zip zP).2)
      have rP := read_reads g solved zP; rw [psubst_pendingTok] at rP
      obtain ⟨m, x, p, spM, locEq⟩ := rowOnSpine_of_pend (spines oP pP σ known) rP
      rw [cH] at inside; simp only [heatChild, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl <;>
        exact .inr ⟨m, x, p, spM, .inl ⟨_, by rw [psubst_atLoc_any]; exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨NameLaws.refl _, locEq⟩⟩⟩
    · obtain ⟨oD, zD, pD⟩ := taken_row admitted (t := doneTok locL locM accC) (by rw [cCl]; simp [cool])
      have rD := take_reads g solved zD; rw [psubst_doneTok] at rD
      obtain ⟨m, x, p, spM, locEq⟩ := rowOnSpine_of_done (spines oD pD σ known) rD
      rw [cCl] at inside; simp only [cool, List.mem_singleton] at inside; subst inside
      exact .inr ⟨m, x, p, spM, .inr (.inr ⟨_, _, by rw [psubst_doneTok]; exact nameLaws_doneTok_iff.mpr ⟨locEq, NameLaws.refl _, NameLaws.refl _⟩⟩)⟩
    · rw [clR] at inside; simp only [closeRoot, List.mem_singleton] at inside; subst inside
      exact .inl ⟨_, by simp only [psubst_atLoc_any, psubst_rootLoc]; exact NameLaws.refl _⟩
    · obtain ⟨oP, zP, pP⟩ := taken_row admitted (t := pendingTok locL locM) (by rw [clC]; simp [closeChild])
      have rP := take_reads g solved zP; rw [psubst_pendingTok] at rP
      obtain ⟨m, x, p, spM, locEq⟩ := rowOnSpine_of_pend (spines oP pP σ known) rP
      rw [clC] at inside; simp only [closeChild, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · exact .inr ⟨m, x, p, spM, .inl ⟨_, by rw [psubst_atLoc_any]; exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨NameLaws.refl _, locEq⟩⟩⟩
      · exact .inr ⟨m, x, p, spM, .inr (.inr ⟨_, _, by rw [psubst_doneTok]; exact nameLaws_doneTok_iff.mpr ⟨locEq, NameLaws.refl _, NameLaws.refl _⟩⟩)⟩
    · rw [opR] at inside; simp only [openRoot, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · exact .inr ⟨rootLoc, psubst g.opening channelUnknown, psubst g.opening reflP, .root,
          .inl ⟨_, by simp only [psubst_atLoc_any, psubst_childLoc, psubst_rootLoc]; exact NameLaws.refl _⟩⟩
      · exact .inr ⟨rootLoc, psubst g.opening channelUnknown, psubst g.opening reflP, .root,
          .inr (.inl ⟨_, by simp only [psubst_pendingTok, psubst_childLoc, psubst_rootLoc]; exact NameLaws.refl _⟩)⟩
    · obtain ⟨oP, zP⟩ := exists_mem_zip shapes.2.2.2.1 (x := pendingTok locL locM) (by rw [opC]; simp [openChild])
      have pP : oP ∈ C.present := enabled.kept_subset (by simpa [Selection.commit] using (List.of_mem_zip zP).2)
      have rP := read_reads g solved zP; rw [psubst_pendingTok] at rP
      obtain ⟨m, x, p, spM, locEq⟩ := rowOnSpine_of_pend (spines oP pP σ known) rP
      let m₁ := childLoc m x p
      have spM₁ : IsLocSpine m₁ := .child x p spM
      let x₁ := psubst g.opening channelUnknown
      let p₁ := psubst g.opening reflP
      have chEq : NameLaws (psubst σ (psubst g.opening (childLoc locL channelUnknown reflP)))
          (psubst σ (childLoc m₁ x₁ p₁)) := by
        rw [psubst_childLoc, psubst_childLoc, psubst_childLoc]
        exact nameLaws_childLoc_iff.mpr ⟨locEq, NameLaws.refl _, NameLaws.refl _⟩
      rw [opC] at inside; simp only [openChild, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · exact .inr ⟨m₁, x₁, p₁, spM₁, .inl ⟨_, by rw [psubst_atLoc_any]; exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨NameLaws.refl _, chEq⟩⟩⟩
      · exact .inr ⟨m₁, x₁, p₁, spM₁, .inr (.inl ⟨_, by rw [psubst_pendingTok]; exact nameLaws_pendingTok_iff.mpr ⟨chEq, NameLaws.refl _⟩⟩)⟩
  · rw [lblOld]; exact spines o old σ known

theorem allLocatedSpines_run {label label' : O → Pattern} {C C' : Configuration Pattern O}
    (run : LocatedRun label C label' C') (spines : AllLocatedSpines label C) :
    AllLocatedSpines label' C' := by
  induction run with
  | refl => exact spines
  | step g adm _ ih => exact ih (allLocatedSpines_preserved spines g adm)

theorem noRootTokens_run {label label' : O → Pattern} {C C' : Configuration Pattern O}
    (run : LocatedRun label C label' C') (noTok : NoRootTokens label C) :
    NoRootTokens label' C' := by
  induction run with
  | refl => exact noTok
  | step g adm _ ih => exact ih (noRootTokens_preserved noTok g adm)

/-- Witnessed clean root representation (all child locations `Clean`, `active = []`), parameterized
by `pats` for pattern-instantiation freedom across sequential forward steps. -/
structure CleanRepresentsBy (label : O → Pattern) (C : Configuration Pattern O) (P : Pattern)
    (rootRows : List (O × Pattern)) (pats : List Pattern) : Prop where
  spines : AllLocatedSpines label C
  noRootTok : NoRootTokens label C
  cleanChildren : CleanChildren label C
  rootInv : RootCells label C rootRows
  rootNodes : ∀ q ∈ rootRows, HostedNode q.2
  rootBag : BagEq (rootBagProcess rootRows) P
  freePats : FreeOnPats pats C.equations
  anchPats : ∀ q ∈ pats, ∃ c ∈ rootRows, SpineHasPattern q (predotU c.2)

/-- Existentially packaged clean root representation (`pats = []`). -/
def CleanRepresents (label : O → Pattern) (C : Configuration Pattern O) (P : Pattern) : Prop :=
  ∃ rootRows, CleanRepresentsBy label C P rootRows []

theorem CleanRepresentsBy.presentExact {label : O → Pattern} {C : Configuration Pattern O}
    {P : Pattern} {rootRows : List (O × Pattern)} {pats : List Pattern}
    (rep : CleanRepresentsBy label C P rootRows pats) :
    ∀ o ∈ C.present, o ∈ rootRows.map Prod.fst := by
  obtain ⟨σ₀, s₀⟩ := freeOnPats_consistent rep.freePats
  intro o oPres
  rcases rep.spines o oPres σ₀ s₀ with ⟨y, hAt⟩ | ⟨m, x, p, spM, hChild⟩
  · by_contra notIn; exact rep.rootInv.others o oPres notIn σ₀ s₀ y hAt
  · have cl := rep.cleanChildren m x p spM (Nat.zero_le _) o oPres σ₀ s₀
    rcases hChild with ⟨y, hAt⟩ | ⟨m', hP⟩ | ⟨m', c', hD⟩
    · exact False.elim (cl.2.2 y hAt)
    · exact False.elim (cl.1 m' hP)
    · exact False.elim (cl.2.1 m' c' hD)

/-- Every `CleanRepresentsBy` state inhabits `SystemInvBy StepRel` with `active = []`. -/
theorem CleanRepresentsBy.toSystemInvBy {StepRel : Pattern → Pattern → Prop}
    {label : O → Pattern} {C : Configuration Pattern O} {P : Pattern}
    {rootRows : List (O × Pattern)} {pats : List Pattern}
    (rep : CleanRepresentsBy label C P rootRows pats) :
    SystemInvBy StepRel label C P rootRows [] :=
  ⟨freeOnPats_consistent rep.freePats, rep.noRootTok, rep.rootInv, rep.rootNodes, rep.rootBag,
    fun _ m => absurd m List.not_mem_nil, List.Pairwise.nil,
    fun o oP => .inl (rep.presentExact o oP)⟩

omit [DecidableEq O] in
theorem CleanRepresentsBy.toCleanRepresents {label : O → Pattern} {C : Configuration Pattern O}
    {P : Pattern} {rootRows : List (O × Pattern)} {pats : List Pattern}
    (rep : CleanRepresentsBy label C P rootRows pats) :
    CleanRepresents label C P :=
  ⟨rootRows, rep.spines, rep.noRootTok, rep.cleanChildren, rep.rootInv, rep.rootNodes, rep.rootBag,
    fun _ => let ⟨σ₀, s₀⟩ := freeOnPats_consistent rep.freePats
      ⟨σ₀, s₀, fun _ m => absurd m List.not_mem_nil⟩,
    fun _ m => absurd m List.not_mem_nil⟩

theorem CleanRepresents.toSystemInvN {label : O → Pattern} {C : Configuration Pattern O}
    {P : Pattern} (rep : CleanRepresents label C P) : SystemInvN label C P := by
  obtain ⟨rows, h⟩ := rep; exact ⟨rows, [], h.toSystemInvBy⟩

theorem CleanRepresents.toSystemInvC {label : O → Pattern} {C : Configuration Pattern O}
    {P : Pattern} (rep : CleanRepresents label C P) : SystemInvC label C P := by
  obtain ⟨rows, h⟩ := rep; exact ⟨rows, [], h.toSystemInvBy⟩

end SpineInvariant

/-- **Non-vacuity of encoding (`CleanRepresentsBy`)**: every `HostedNode` process `P` (with any
anchored `pats`) initializes `(encodeLabel P, encodeConf)` in `CleanRepresentsBy`. -/
theorem encode_cleanRepresentsBy {P : Pattern} (hP : HostedNode P) {pats : List Pattern}
    (anch : ∀ q ∈ pats, SpineHasPattern q (predotU P)) :
    CleanRepresentsBy (encodeLabel P) encodeConf P [(0, P)] pats := by
  obtain ⟨noTok, inv, clean, free⟩ := single_root_init P pats
  refine ⟨fun _ _ σ _ => .inl ⟨psubst σ (predotU P), ?_⟩, noTok, clean, inv,
    fun q qM => by obtain rfl := List.mem_singleton.mp qM; exact hP,
    bagEq_pPar_singleton P, free, fun q qM => ⟨(0, P), by simp, anch q qM⟩⟩
  change NameLaws (psubst σ (atLoc (predotU P) rootLoc)) _
  rw [psubst_atLoc_any, psubst_rootLoc]; exact NameLaws.refl _

/-- **Non-vacuity of encoding (`CleanRepresents`, `SystemInvN`, and `SystemInvC`)**. -/
theorem encode_in_relation {P : Pattern} (hP : HostedNode P) :
    CleanRepresents (encodeLabel P) encodeConf P ∧
    SystemInvN (encodeLabel P) encodeConf P ∧
    SystemInvC (encodeLabel P) encodeConf P := by
  have rep := (encode_cleanRepresentsBy hP (pats := []) fun _ m => absurd m List.not_mem_nil).toCleanRepresents
  exact ⟨rep, rep.toSystemInvN, rep.toSystemInvC⟩

/-! ## Forward simulation of hosted actions and structural changes -/

/-- Spine splitting across a list of `(O × Pattern)` root cells. -/
inductive MultiSplits {O : Type*} : List (O × Pattern) → List Pattern → Prop where
  | nil : MultiSplits [] []
  | cons {q : O × Pattern} {rest : List (O × Pattern)} {L₁ L₂ : List Pattern} :
      Splits q.2 L₁ → MultiSplits rest L₂ → MultiSplits (q :: rest) (L₁ ++ L₂)

theorem MultiSplits.of_map_snd {O : Type*} :
    ∀ {rows : List (O × Pattern)} {L : List Pattern}, rows.map Prod.snd = L → MultiSplits rows L
  | [], _, rfl => .nil
  | q :: rest, _, rfl =>
      show MultiSplits (q :: rest) ([q.2] ++ rest.map Prod.snd) from
        .cons (.leaf q.2) (of_map_snd rfl)

/-- Hosted root actions under **Interface N**, together with structural changes.
`COMM` and `REFL` carry their stated side conditions; `equiv` may stutter. -/
inductive HostedRootStepN {O : Type*} :
    List (O × Pattern) → List Pattern → List Pattern → Pattern → Pattern → Prop where
  | equiv {rows : List (O × Pattern)} {pats : List Pattern} {P P' : Pattern} :
      BagEq P P' → HostedRootStepN rows pats pats P P'
  | comm {rows : List (O × Pattern)} {extPats cPre cMid cPost : List Pattern}
      {t u ch A B P P' : Pattern} {bs : Bindings} :
      MultiSplits rows (cPre ++ pFor t ch A :: (cMid ++ pFor u ch B :: cPost)) →
      Step1PrimeComm t ch A u ch B → GroundPrincipal t u bs →
      PlainPatterns (applyDot bs A) → PlainPatterns (applyDot bs B) →
      HostedNode (applyDot bs A) → HostedNode (applyDot bs B) →
      (∀ q ∈ extPats, ∀ v ∈ pvars q, v ∉ pvars t ++ pvars u) →
      (∀ q ∈ extPats, ∃ c ∈ cPre ++ cMid ++ cPost, SpineHasPattern q (predotU c)) →
      BagEq (pPar ((cPre ++ cMid ++ cPost) ++ [applyDot bs A, applyDot bs B])) P' →
      HostedRootStepN rows (t :: u :: extPats) extPats P P'
  | commGround {rows : List (O × Pattern)} {extPats cPre cMid cPost : List Pattern}
      {t u ch A B P P' : Pattern} :
      MultiSplits rows (cPre ++ pFor t ch A :: (cMid ++ pFor u ch B :: cPost)) →
      ExactGroundComm t ch A u ch B → NameLaws (predotU t) (predotU u) →
      (∀ q ∈ extPats, ∃ c ∈ cPre ++ cMid ++ cPost, SpineHasPattern q (predotU c)) →
      BagEq (pPar ((cPre ++ cMid ++ cPost) ++ [A, B])) P' →
      HostedRootStepN rows extPats extPats P P'
  | refl {rows : List (O × Pattern)} {d : ℕ} {extPats cPre cPost : List Pattern}
      {x P_sub R P P' : Pattern} {pair : Pattern × Pattern} {bs : Bindings} :
      MultiSplits rows (cPre ++ pReflect x P_sub :: cPost) →
      HostedChan x → HostedSubStepN d P_sub R pair bs →
      (∀ q ∈ extPats, ∀ v ∈ pvars q, v ∉ pvars pair.1 ++ pvars pair.2) →
      (∀ q ∈ extPats, ∃ c ∈ cPre ++ cPost, SpineHasPattern q (predotU c)) →
      BagEq (pPar (cPre ++ pFor (tProc R) x pZero :: cPost)) P' →
      HostedRootStepN rows (pair.1 :: pair.2 :: extPats) extPats P P'

/-- Hosted root actions under **Interface C**, together with structural changes.
Recursive `REFL` uses `HostedSubStepC` and `listener x R`; `equiv` may stutter. -/
inductive HostedRootStepC {O : Type*} :
    List (O × Pattern) → List Pattern → List Pattern → Pattern → Pattern → Prop where
  | equiv {rows : List (O × Pattern)} {pats : List Pattern} {P P' : Pattern} :
      BagEq P P' → HostedRootStepC rows pats pats P P'
  | comm {rows : List (O × Pattern)} {extPats cPre cMid cPost : List Pattern}
      {t u ch A B P P' : Pattern} {bs : Bindings} :
      MultiSplits rows (cPre ++ pFor t ch A :: (cMid ++ pFor u ch B :: cPost)) →
      Step1PrimeComm t ch A u ch B → GroundPrincipal t u bs →
      PlainPatterns (applyDot bs A) → PlainPatterns (applyDot bs B) →
      HostedNode (applyDot bs A) → HostedNode (applyDot bs B) →
      (∀ q ∈ extPats, ∀ v ∈ pvars q, v ∉ pvars t ++ pvars u) →
      (∀ q ∈ extPats, ∃ c ∈ cPre ++ cMid ++ cPost, SpineHasPattern q (predotU c)) →
      BagEq (pPar ((cPre ++ cMid ++ cPost) ++ [applyDot bs A, applyDot bs B])) P' →
      HostedRootStepC rows (t :: u :: extPats) extPats P P'
  | commGround {rows : List (O × Pattern)} {extPats cPre cMid cPost : List Pattern}
      {t u ch A B P P' : Pattern} :
      MultiSplits rows (cPre ++ pFor t ch A :: (cMid ++ pFor u ch B :: cPost)) →
      ExactGroundComm t ch A u ch B → NameLaws (predotU t) (predotU u) →
      (∀ q ∈ extPats, ∃ c ∈ cPre ++ cMid ++ cPost, SpineHasPattern q (predotU c)) →
      BagEq (pPar ((cPre ++ cMid ++ cPost) ++ [A, B])) P' →
      HostedRootStepC rows extPats extPats P P'
  | refl {rows : List (O × Pattern)} {d : ℕ} {extPats cPre cPost : List Pattern}
      {x P_sub R P P' : Pattern} {pair : Pattern × Pattern} {bs : Bindings} :
      MultiSplits rows (cPre ++ pReflect x P_sub :: cPost) →
      HostedChan x → HostedSubStepC d P_sub R pair bs →
      (∀ q ∈ extPats, ∀ v ∈ pvars q, v ∉ pvars pair.1 ++ pvars pair.2) →
      (∀ q ∈ extPats, ∃ c ∈ cPre ++ cPost, SpineHasPattern q (predotU c)) →
      BagEq (pPar (cPre ++ listener x R :: cPost)) P' →
      HostedRootStepC rows (pair.1 :: pair.2 :: extPats) extPats P P'

section ForwardSimulation

variable {O : Type*} [DecidableEq O]

private theorem splits_hostedNode {P : Pattern} {L : List Pattern} (sp : Splits P L)
    (hP : HostedNode P) : ∀ c ∈ L, HostedNode c := by
  induction sp with
  | leaf P => intro c m; obtain rfl := List.mem_singleton.mp m; exact hP
  | split _ _ ihA ihB =>
      cases hP with
      | par hA hB =>
          intro c m; rcases List.mem_append.mp m with mA | mB
          · exact ihA hA c mA
          · exact ihB hB c mB

omit [DecidableEq O] in
private theorem multiSplits_hostedNode {rows : List (O × Pattern)} {L : List Pattern}
    (ms : MultiSplits rows L) (nodes : ∀ q ∈ rows, HostedNode q.2) :
    ∀ c ∈ L, HostedNode c := by
  induction ms with
  | nil => intro _ m; exact absurd m List.not_mem_nil
  | cons sp _ ih =>
      intro c m; rcases List.mem_append.mp m with m₁ | m₂
      · exact splits_hostedNode sp (nodes _ (List.mem_cons_self ..)) c m₁
      · exact ih (fun q' m' => nodes q' (List.mem_cons_of_mem _ m')) c m₂

theorem cleanChildren_of_rootRule {label : O → Pattern} {C : Configuration Pattern O}
    (clean : CleanChildren label C) {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    {r} (isAt : g.rule = atRule rootLoc r) :
    CleanChildren (res label C g).label (resConf label C g) :=
  cleanAboveDepth_of_subset clean (fun _ s => info_known g s) fun o oP => by
    rcases result_row oP with made | ⟨old, -, -, lblOld⟩
    · obtain ⟨t, inside, lblEq⟩ := made_label admitted made
      rw [isAt] at inside
      simp only [atRule, RuleInstance.map, List.mem_map] at inside
      obtain ⟨body, -, rfl⟩ := inside
      exact .inr ⟨rootLoc, .root, le_rfl, fun σ _ => .inl ⟨psubst σ (psubst g.opening body),
        by rw [lblEq, psubst_atLoc_any, psubst_rootLoc]; exact NameLaws.refl _⟩⟩
    · exact .inl ⟨old, lblOld⟩

private theorem cleanChildren_of_rootHeat_split [Infinite O] {P₀ : Pattern} {L : List Pattern}
    (sp : Splits P₀ L) :
    ∀ (label : O → Pattern) (C : Configuration Pattern O) (pre post : List (O × Pattern))
      (o : O) (pats : List Pattern),
      CleanChildren label C →
      RootCells label C (pre ++ (o, P₀) :: post) →
      FreeOnPats pats C.equations →
      (∀ q ∈ pats, ∃ c ∈ pre ++ (o, P₀) :: post, SpineHasPattern q (predotU c.2)) →
      ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (newCells : List (O × Pattern)),
        LocatedRun label C label' C' ∧
        newCells.map Prod.snd = L ∧
        CleanChildren label' C' ∧
        RootCells label' C' (pre ++ newCells ++ post) ∧
        BagEq (rootBagProcess (pre ++ newCells ++ post))
          (rootBagProcess (pre ++ (o, P₀) :: post)) ∧
        FreeOnPats pats C'.equations ∧
        (∀ q ∈ pats, ∃ c ∈ pre ++ newCells ++ post, SpineHasPattern q (predotU c.2)) := by
  induction sp with
  | leaf P =>
      intro label C pre post o pats clean inv free anch
      exact ⟨label, C, [(o, P)], .refl label C, rfl, clean, by simpa using inv,
        by simpa [rootBagProcess] using BagEq.refl _, free, by simpa using anch⟩
  | @split a b LA LB _ _ ihA ihB =>
      intro label C pre post o pats clean inv free anch
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
        simpa [psubst_atLoc_any, ReflLocated.psubst_par, psubst_rootLoc] using oReads σ₀ known₀
      have admitted := rootHeat_admitted label C o m₁ m₂ oPres m₂ne.symm fresh₁ fresh₂
        known₀ pair₀ opensFreshly
      obtain ⟨inv₁, bag₁, -⟩ := rootCells_heat inv admitted
      obtain ⟨free₁, anch₁⟩ := freeOnPats_rootHeat inv opensFreshly free anch
      have clean₁ := cleanChildren_of_rootRule clean admitted (r := heatRule) rfl
      obtain ⟨label₂, C₂, cellsA, runA, mapA, clean₂, inv₂, bagA, free₂, anch₂⟩ :=
        ihA _ _ pre ((m₂, b) :: post) m₁ pats clean₁ inv₁ free₁ anch₁
      have inv₂' : RootCells label₂ C₂ ((pre ++ cellsA) ++ (m₂, b) :: post) := by
        simpa [List.append_assoc] using inv₂
      have anch₂' : ∀ q ∈ pats, ∃ c ∈ (pre ++ cellsA) ++ (m₂, b) :: post,
          SpineHasPattern q (predotU c.2) := by simpa [List.append_assoc] using anch₂
      obtain ⟨label₃, C₃, cellsB, runB, mapB, clean₃, inv₃, bagB, free₃, anch₃⟩ :=
        ihB label₂ C₂ (pre ++ cellsA) post m₂ pats clean₂ inv₂' free₂ anch₂'
      have bagB' : BagEq (rootBagProcess (pre ++ (cellsA ++ cellsB) ++ post))
          (rootBagProcess (pre ++ cellsA ++ (m₂, b) :: post)) := by
        simpa [rootBagProcess, List.append_assoc] using bagB
      exact ⟨label₃, C₃, cellsA ++ cellsB, .step _ admitted (runA.trans runB),
        by simp [mapA, mapB], clean₃, by simpa [List.append_assoc] using inv₃,
        bagB'.trans (bagA.trans bag₁), free₃, by simpa [List.append_assoc] using anch₃⟩

private theorem multi_root_heating [Infinite O] {rows : List (O × Pattern)} {L : List Pattern}
    (ms : MultiSplits rows L) :
    ∀ (label : O → Pattern) (C : Configuration Pattern O) (pre : List (O × Pattern))
      (pats : List Pattern),
      CleanChildren label C →
      RootCells label C (pre ++ rows) →
      FreeOnPats pats C.equations →
      (∀ q ∈ pats, ∃ c ∈ pre ++ rows, SpineHasPattern q (predotU c.2)) →
      ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (cells : List (O × Pattern)),
        LocatedRun label C label' C' ∧
        cells.map Prod.snd = L ∧
        CleanChildren label' C' ∧
        RootCells label' C' (pre ++ cells) ∧
        BagEq (rootBagProcess (pre ++ cells)) (rootBagProcess (pre ++ rows)) ∧
        FreeOnPats pats C'.equations ∧
        (∀ q ∈ pats, ∃ c ∈ pre ++ cells, SpineHasPattern q (predotU c.2)) := by
  induction ms with
  | nil =>
      intro label C pre pats clean inv free anch
      exact ⟨label, C, [], .refl label C, rfl, clean, inv, BagEq.refl _, free, anch⟩
  | @cons q rest L₁ L₂ sp _ ih =>
      intro label C pre pats clean inv free anch
      obtain ⟨label₁, C₁, cells₁, run₁, map₁, clean₁, inv₁, bag₁, free₁, anch₁⟩ :=
        cleanChildren_of_rootHeat_split sp label C pre rest q.1 pats clean inv free anch
      have inv₁' : RootCells label₁ C₁ ((pre ++ cells₁) ++ rest) := by simpa [List.append_assoc] using inv₁
      have anch₁' : ∀ x ∈ pats, ∃ c ∈ (pre ++ cells₁) ++ rest, SpineHasPattern x (predotU c.2) := by
        simpa [List.append_assoc] using anch₁
      obtain ⟨label₂, C₂, cells₂, run₂, map₂, clean₂, inv₂, bag₂, free₂, anch₂⟩ :=
        ih label₁ C₁ (pre ++ cells₁) pats clean₁ inv₁' free₁ anch₁'
      have bag₂' : BagEq (rootBagProcess (pre ++ (cells₁ ++ cells₂)))
          (rootBagProcess (pre ++ cells₁ ++ rest)) := by
        simpa [rootBagProcess, List.append_assoc] using bag₂
      exact ⟨label₂, C₂, cells₁ ++ cells₂, run₁.trans run₂, by simp [map₁, map₂], clean₂,
        by simpa [List.append_assoc] using inv₂, bag₂'.trans bag₁, free₂,
        by simpa [List.append_assoc] using anch₂⟩

omit [DecidableEq O] in
private theorem split_cells_1 {cells : List (O × Pattern)} {cPre cPost : List Pattern}
    {midP : Pattern} (hMap : cells.map Prod.snd = cPre ++ midP :: cPost) :
    ∃ rPre o rPost, cells = rPre ++ (o, midP) :: rPost ∧
      rPre.map Prod.snd = cPre ∧ rPost.map Prod.snd = cPost := by
  have lenEq : cells.length = (cPre ++ midP :: cPost).length := by
    have h := congrArg List.length hMap; simpa using h
  obtain ⟨rPre, ⟨o, p₀⟩, rPost, rfl, lPre, -⟩ := split_rows_1 lenEq
  simp only [List.map_append, List.map_cons] at hMap
  obtain ⟨eqPre, eqTail⟩ := List.append_inj hMap (by simp [lPre])
  simp only [List.cons.injEq] at eqTail
  obtain ⟨rfl, eqPost⟩ := eqTail
  exact ⟨rPre, o, rPost, rfl, eqPre, eqPost⟩

omit [DecidableEq O] in
private theorem split_cells_2 {cells : List (O × Pattern)} {cPre cMid cPost : List Pattern}
    {p₁ p₂ : Pattern} (hMap : cells.map Prod.snd = cPre ++ p₁ :: (cMid ++ p₂ :: cPost)) :
    ∃ rPre o₁ rMid o₂ rPost,
      cells = rPre ++ (o₁, p₁) :: (rMid ++ (o₂, p₂) :: rPost) ∧
      rPre.map Prod.snd = cPre ∧ rMid.map Prod.snd = cMid ∧ rPost.map Prod.snd = cPost := by
  obtain ⟨rPre, o₁, rTail, rfl, eqPre, eqTail⟩ := split_cells_1 hMap
  obtain ⟨rMid, o₂, rPost, rfl, eqMid, eqPost⟩ := split_cells_1 eqTail
  exact ⟨rPre, o₁, rMid, o₂, rPost, rfl, eqPre, eqMid, eqPost⟩

private theorem forward_comm_step [Infinite O] {label : O → Pattern} {C : Configuration Pattern O}
    {P P' t u ch A B : Pattern} {rootRows : List (O × Pattern)}
    {extPats cPre cMid cPost : List Pattern} {bs : Bindings}
    (rep : CleanRepresentsBy label C P rootRows (t :: u :: extPats))
    (ms : MultiSplits rootRows (cPre ++ pFor t ch A :: (cMid ++ pFor u ch B :: cPost)))
    (s1 : Step1PrimeComm t ch A u ch B) (gp : GroundPrincipal t u bs)
    (plA : PlainPatterns (applyDot bs A)) (plB : PlainPatterns (applyDot bs B))
    (nA : HostedNode (applyDot bs A)) (nB : HostedNode (applyDot bs B))
    (disj : ∀ q ∈ extPats, ∀ v ∈ pvars q, v ∉ pvars t ++ pvars u)
    (anchRest : ∀ q ∈ extPats, ∃ c ∈ cPre ++ cMid ++ cPost, SpineHasPattern q (predotU c))
    (bagOut : BagEq (pPar ((cPre ++ cMid ++ cPost) ++ [applyDot bs A, applyDot bs B])) P') :
    ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (rows' : List (O × Pattern)),
      LocatedRun label C label' C' ∧
      CleanRepresentsBy label' C' P' rows' extPats ∧
      BagStep conventional P P' ∧ CanonicalBagStep conventional P P' := by
  have leafNodes := multiSplits_hostedNode ms rep.rootNodes
  obtain ⟨label₁, C₁, cells, runHeat, mapCells, clean₁, inv₁, bagHeat, free₁, -⟩ :=
    multi_root_heating ms label C [] (t :: u :: extPats) rep.cleanChildren
      (by simpa using rep.rootInv) rep.freePats (by simpa using rep.anchPats)
  have inv₁' : RootCells label₁ C₁ cells := by simpa using inv₁
  have bagHeat' : BagEq (rootBagProcess cells) (rootBagProcess rootRows) := by simpa using bagHeat
  obtain ⟨rPre, f, rMid, s, rPost, rfl, eqPre, eqMid, eqPost⟩ := split_cells_2 mapCells
  obtain ⟨σ₀, k₀, unif₀, -⟩ := freeOnPats_glue_unifier gp.solves disj free₁ (fun _ => none)
  obtain ⟨m₁, fresh₁⟩ := Infinite.exists_notMem_finset C₁.present
  obtain ⟨m₂, fresh₂'⟩ := Infinite.exists_notMem_finset (insert m₁ C₁.present)
  have mDist : m₁ ≠ m₂ := fun e => fresh₂' (Finset.mem_insert.mpr (.inl e.symm))
  have fresh₂ : m₂ ∉ C₁.present := fun m => fresh₂' (Finset.mem_insert.mpr (.inr m))
  obtain ⟨ρ, freshComm⟩ := rootComm_fresh_exists label₁ C₁ f s m₁ m₂
  obtain ⟨adm, inv₂, bStep, cStep⟩ := rootCells_comm_forward inv₁' s1.noBT s1.noBU s1.chanL.1
    s1.noBA s1.noBB plA plB gp s1.convention s1.foA s1.foB s1.groundT s1.groundU s1.canonicalT
    s1.canonicalU mDist fresh₁ fresh₂ k₀ unif₀ freshComm
  have rF : ∀ σ : PSubst, nameAction.Models σ C₁.equations →
      NameLaws (psubst σ (label₁ f))
        (psubst σ (atLoc (pFor t (predot ch) (dotted (pvars t) (predot A))) rootLoc)) := by
    intro σ m; have r := (inv₁'.rows (f, pFor t ch A) (by simp)).2 σ m
    rwa [predotU_pFor_eq_predot_plain s1.noBT s1.chanL.1 s1.noBA, predot_pFor] at r
  have rS : ∀ σ : PSubst, nameAction.Models σ C₁.equations →
      NameLaws (psubst σ (label₁ s))
        (psubst σ (atLoc (pFor u (predot ch) (dotted (pvars u) (predot B))) rootLoc)) := by
    intro σ m; have r := (inv₁'.rows (s, pFor u ch B) (by simp)).2 σ m
    rwa [predotU_pFor_eq_predot_plain s1.noBU s1.chanL.1 s1.noBB, predot_pFor] at r
  have mapRest : (rPre ++ rMid ++ rPost).map Prod.snd = cPre ++ cMid ++ cPost := by
    simp [eqPre, eqMid, eqPost]
  have anchInRest : ∀ q ∈ extPats, ∃ pr ∈ rPre ++ rMid ++ rPost, SpineHasPattern q (predotU pr.2) := by
    intro q qM; obtain ⟨c, cM, hasQ⟩ := anchRest q qM
    obtain ⟨pr, prM, rfl⟩ := List.mem_map.mp (mapRest ▸ cM)
    exact ⟨pr, prM, hasQ⟩
  have restSub : ∀ pr ∈ rPre ++ rMid ++ rPost,
      pr ∈ rPre ++ (f, pFor t ch A) :: (rMid ++ (s, pFor u ch B) :: rPost) := by
    intro pr m; simp only [List.mem_append] at m
    rcases m with (l | m') | r
    · exact by simp [l]
    · exact by simp [m']
    · exact by simp [r]
  have free₂ : FreeOnPats extPats (resConf label₁ C₁ (rootCommAt ρ f s m₁ m₂)).equations :=
    freeOnPats_after_comm_extends gp.solves disj free₁ (fun _ m => info_known _ m)
      (fun _ k unif => rootComm_extends label₁ C₁ t u (predot ch) _ _ f s m₁ m₂ rF rS
        (inv₁'.rows (f, pFor t ch A) (by simp)).1 (inv₁'.rows (s, pFor u ch B) (by simp)).1 freshComm k unif)
      (fun q qM => by
        obtain ⟨pr, prM, hasQ⟩ := anchInRest q qM
        exact ⟨pr.1, (inv₁'.rows pr (restSub pr prM)).1, predotU pr.2, rootLoc,
          (inv₁'.rows pr (restSub pr prM)).2, hasQ⟩)
  let runFull := runHeat.trans (.step _ adm (.refl _ _))
  let outRows := (rPre ++ rMid ++ rPost) ++ [(m₁, applyDot bs A), (m₂, applyDot bs B)]
  have outBagEq : BagEq (rootBagProcess outRows) P' := by
    have eqOut : rootBagProcess outRows =
        pPar ((cPre ++ cMid ++ cPost) ++ [applyDot bs A, applyDot bs B]) := by
      simp [outRows, rootBagProcess, eqPre, eqMid, eqPost]
    exact eqOut ▸ bagOut
  have preEq : BagEq P (rootBagProcess (rPre ++ (f, pFor t ch A) :: (rMid ++ (s, pFor u ch B) :: rPost))) :=
    rep.rootBag.symm.trans bagHeat'.symm
  refine ⟨_, _, outRows, runFull,
    ⟨allLocatedSpines_run runFull rep.spines, noRootTokens_run runFull rep.noRootTok,
     cleanChildren_of_rootRule clean₁ adm (r := commRule) rfl, inv₂, ?_, outBagEq, free₂, ?_⟩,
    .congruence preEq bStep outBagEq, .congruence preEq cStep outBagEq⟩
  · intro pr m; rcases List.mem_append.mp m with inR | inM
    · exact leafNodes pr.2 (by
        have mSnd := List.mem_map_of_mem (f := Prod.snd) (restSub pr inR)
        rwa [mapCells] at mSnd)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at inM
      rcases inM with rfl | rfl
      · exact nA
      · exact nB
  · intro q qM; obtain ⟨pr, prM, hasQ⟩ := anchInRest q qM
    exact ⟨pr, List.mem_append_left _ prM, hasQ⟩

private theorem forward_commGround_step [Infinite O] {label : O → Pattern}
    {C : Configuration Pattern O} {P P' t u ch A B : Pattern} {rootRows : List (O × Pattern)}
    {extPats cPre cMid cPost : List Pattern}
    (rep : CleanRepresentsBy label C P rootRows extPats)
    (ms : MultiSplits rootRows (cPre ++ pFor t ch A :: (cMid ++ pFor u ch B :: cPost)))
    (eg : ExactGroundComm t ch A u ch B) (samePat : NameLaws (predotU t) (predotU u))
    (anchRest : ∀ q ∈ extPats, ∃ c ∈ cPre ++ cMid ++ cPost, SpineHasPattern q (predotU c))
    (bagOut : BagEq (pPar ((cPre ++ cMid ++ cPost) ++ [A, B])) P') :
    ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (rows' : List (O × Pattern)),
      LocatedRun label C label' C' ∧
      CleanRepresentsBy label' C' P' rows' extPats ∧
      BagStep conventional P P' ∧ CanonicalBagStep conventional P P' := by
  have tEqU := eg.exactOnNameLaws samePat; subst tEqU
  have leafNodes := multiSplits_hostedNode ms rep.rootNodes
  obtain ⟨label₁, C₁, cells, runHeat, mapCells, clean₁, inv₁, bagHeat, free₁, -⟩ :=
    multi_root_heating ms label C [] extPats rep.cleanChildren
      (by simpa using rep.rootInv) rep.freePats (by simpa using rep.anchPats)
  have inv₁' : RootCells label₁ C₁ cells := by simpa using inv₁
  have bagHeat' : BagEq (rootBagProcess cells) (rootBagProcess rootRows) := by simpa using bagHeat
  obtain ⟨rPre, f, rMid, s, rPost, rfl, eqPre, eqMid, eqPost⟩ := split_cells_2 mapCells
  obtain ⟨σ₀, k₀⟩ := freeOnPats_consistent free₁
  obtain ⟨m₁, fresh₁⟩ := Infinite.exists_notMem_finset C₁.present
  obtain ⟨m₂, fresh₂'⟩ := Infinite.exists_notMem_finset (insert m₁ C₁.present)
  have mDist : m₁ ≠ m₂ := fun e => fresh₂' (Finset.mem_insert.mpr (.inl e.symm))
  have fresh₂ : m₂ ∉ C₁.present := fun m => fresh₂' (Finset.mem_insert.mpr (.inr m))
  obtain ⟨ρ, freshComm⟩ := rootComm_fresh_exists label₁ C₁ f s m₁ m₂
  obtain ⟨adm, inv₂⟩ := rootCells_comm_ground_forward inv₁' eg.groundT eg.groundT samePat
    eg.chanL.1 mDist fresh₁ fresh₂ k₀ freshComm
  have rF : ∀ σ : PSubst, nameAction.Models σ C₁.equations →
      NameLaws (psubst σ (label₁ f))
        (psubst σ (atLoc (pFor t ch (predotU A)) rootLoc)) := by
    intro σ m; have r := (inv₁'.rows (f, pFor t ch A) (by simp)).2 σ m
    rwa [ReflUniform.predotU_ground_guard eg.groundT eg.chanL.1] at r
  have rS : ∀ σ : PSubst, nameAction.Models σ C₁.equations →
      NameLaws (psubst σ (label₁ s))
        (psubst σ (atLoc (pFor t ch (predotU B)) rootLoc)) := by
    intro σ m; have r := (inv₁'.rows (s, pFor t ch B) (by simp)).2 σ m
    rwa [ReflUniform.predotU_ground_guard eg.groundT eg.chanL.1] at r
  have mapRest : (rPre ++ rMid ++ rPost).map Prod.snd = cPre ++ cMid ++ cPost := by
    simp [eqPre, eqMid, eqPost]
  have anchInRest : ∀ q ∈ extPats, ∃ pr ∈ rPre ++ rMid ++ rPost, SpineHasPattern q (predotU pr.2) := by
    intro q qM; obtain ⟨c, cM, hasQ⟩ := anchRest q qM
    obtain ⟨pr, prM, rfl⟩ := List.mem_map.mp (mapRest ▸ cM)
    exact ⟨pr, prM, hasQ⟩
  have restSub : ∀ pr ∈ rPre ++ rMid ++ rPost,
      pr ∈ rPre ++ (f, pFor t ch A) :: (rMid ++ (s, pFor t ch B) :: rPost) := by
    intro pr m; simp only [List.mem_append] at m
    rcases m with (l | m') | r
    · exact by simp [l]
    · exact by simp [m']
    · exact by simp [r]
  have free₂ : FreeOnPats extPats (resConf label₁ C₁ (rootCommAt ρ f s m₁ m₂)).equations :=
    freeOnPats_of_extends free₁ (fun _ m => info_known _ m)
      (fun τ k => rootComm_extends label₁ C₁ t t ch (predotU A) (predotU B)
        f s m₁ m₂ rF rS (inv₁'.rows (f, pFor t ch A) (by simp)).1
        (inv₁'.rows (s, pFor t ch B) (by simp)).1 freshComm k (NameLaws.refl _))
      (fun q qM => by
        obtain ⟨pr, prM, hasQ⟩ := anchInRest q qM
        exact ⟨pr.1, (inv₁'.rows pr (restSub pr prM)).1, predotU pr.2, rootLoc,
          (inv₁'.rows pr (restSub pr prM)).2, hasQ⟩)
  let runFull := runHeat.trans (.step _ adm (.refl _ _))
  let outRows := (rPre ++ rMid ++ rPost) ++ [(m₁, A), (m₂, B)]
  have outBagEq : BagEq (rootBagProcess outRows) P' := by
    have eqOut : rootBagProcess outRows = pPar ((cPre ++ cMid ++ cPost) ++ [A, B]) := by
      simp [outRows, rootBagProcess, eqPre, eqMid, eqPost]
    exact eqOut ▸ bagOut
  have preEq : BagEq P (rootBagProcess (rPre ++ (f, pFor t ch A) :: (rMid ++ (s, pFor t ch B) :: rPost))) :=
    rep.rootBag.symm.trans bagHeat'.symm
  have gp₀ : GroundPrincipal t t [] :=
    ⟨fun _ m => absurd m List.not_mem_nil,
     fun x m => by rw [eg.groundT, List.append_nil] at m; exact absurd m List.not_mem_nil,
     rfl, fun _ _ x m => by rw [eg.groundT, List.append_nil] at m; exact absurd m List.not_mem_nil⟩
  have conv₀ : Apart t A t B := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro v inT <;> rw [eg.groundT] at inT <;> cases inT
  have eqAD : applyDot [] A = A :=
    (MeTTaOperationsComm.applyDot_eq [] A eg.foA).trans (MeTTaOperationsComm.psubst_none A)
  have eqBD : applyDot [] B = B :=
    (MeTTaOperationsComm.applyDot_eq [] B eg.foB).trans (MeTTaOperationsComm.psubst_none B)
  have bStep : BagStep conventional
      (rootBagProcess (rPre ++ (f, pFor t ch A) :: (rMid ++ (s, pFor t ch B) :: rPost)))
      (rootBagProcess outRows) := by
    simpa [rootBagProcess, outRows, eqPre, eqMid, eqPost, eqAD, eqBD] using
      bagStep_of_pPar_comm (admit := conventional) cPre cMid cPost t t ch A B [] gp₀ conv₀
  have cStep : CanonicalBagStep conventional
      (rootBagProcess (rPre ++ (f, pFor t ch A) :: (rMid ++ (s, pFor t ch B) :: rPost)))
      (rootBagProcess outRows) := by
    simpa [rootBagProcess, outRows, eqPre, eqMid, eqPost, eqAD, eqBD] using
      canonicalBagStep_of_pPar_comm (admit := conventional) cPre cMid cPost t t ch A B [] gp₀ conv₀
  refine ⟨_, _, outRows, runFull,
    ⟨allLocatedSpines_run runFull rep.spines, noRootTokens_run runFull rep.noRootTok,
     cleanChildren_of_rootRule clean₁ adm (r := commRule) rfl, inv₂, ?_, outBagEq, free₂, ?_⟩,
    .congruence preEq bStep outBagEq, .congruence preEq cStep outBagEq⟩
  · intro pr m; rcases List.mem_append.mp m with inR | inM
    · exact leafNodes pr.2 (by
        have mSnd := List.mem_map_of_mem (f := Prod.snd) (restSub pr inR)
        rwa [mapCells] at mSnd)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at inM
      rcases inM with rfl | rfl
      · exact eg.nodeA
      · exact eg.nodeB
  · intro q qM; obtain ⟨pr, prM, hasQ⟩ := anchInRest q qM
    exact ⟨pr, List.mem_append_left _ prM, hasQ⟩

/-- **Forward simulation of hosted actions and structural changes, interface N.**
Every `HostedRootStepN` from `CleanRepresentsBy` is matched by a `LocatedRun` reaching
`CleanRepresentsBy`, and realizes `BagEq P P' ∨ BagStep conventional P P'`. Steps outside
`HostedRootStepN` are not covered. -/
theorem source_step_forward_N [Infinite O] {label : O → Pattern} {C : Configuration Pattern O}
    {P P' : Pattern} {rootRows : List (O × Pattern)} {pats extPats : List Pattern}
    (rep : CleanRepresentsBy label C P rootRows pats)
    (step : HostedRootStepN rootRows pats extPats P P') :
    ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (rows' : List (O × Pattern)),
      LocatedRun label C label' C' ∧
      CleanRepresentsBy label' C' P' rows' extPats ∧
      (BagEq P P' ∨ BagStep conventional P P') := by
  cases step with
  | equiv bEq =>
      exact ⟨label, C, rootRows, .refl label C,
        ⟨rep.spines, rep.noRootTok, rep.cleanChildren, rep.rootInv, rep.rootNodes,
         rep.rootBag.trans bEq, rep.freePats, rep.anchPats⟩, .inl bEq⟩
  | comm ms s1 gp plA plB nA nB disj anchRest bagOut =>
      obtain ⟨l', C', rows', run, rep', bStep, -⟩ :=
        forward_comm_step rep ms s1 gp plA plB nA nB disj anchRest bagOut
      exact ⟨l', C', rows', run, rep', .inr bStep⟩
  | commGround ms eg samePat anchRest bagOut =>
      obtain ⟨l', C', rows', run, rep', bStep, -⟩ :=
        forward_commGround_step rep ms eg samePat anchRest bagOut
      exact ⟨l', C', rows', run, rep', .inr bStep⟩
  | refl ms hX sub disj anchRest bagOut =>
      rename_i d cPre cPost x P_sub R pair bs
      have leafNodes := multiSplits_hostedNode ms rep.rootNodes
      obtain ⟨label₁, C₁, cells, runHeat, mapCells, clean₁, inv₁, bagHeat, free₁, -⟩ :=
        multi_root_heating ms label C [] (pair.1 :: pair.2 :: extPats) rep.cleanChildren
          (by simpa using rep.rootInv) rep.freePats (by simpa using rep.anchPats)
      have inv₁' : RootCells label₁ C₁ cells := by simpa using inv₁
      have bagHeat' : BagEq (rootBagProcess cells) (rootBagProcess rootRows) := by simpa using bagHeat
      obtain ⟨rPre, rOcc, rPost, rfl, eqPre, eqPost⟩ := split_cells_1 mapCells
      have mapRest : (rPre ++ rPost).map Prod.snd = cPre ++ cPost := by simp [eqPre, eqPost]
      have anchInRest : ∀ q ∈ extPats, ∃ pr ∈ rPre ++ rPost, SpineHasPattern q (predotU pr.2) := by
        intro q qM; obtain ⟨c, cM, hasQ⟩ := anchRest q qM
        obtain ⟨pr, prM, rfl⟩ := List.mem_map.mp (mapRest ▸ cM)
        exact ⟨pr, prM, hasQ⟩
      obtain ⟨label₂, C₂, made, runRefl, noTok₂, inv₂, clean₂, free₂, -, bStep⟩ :=
        refl_depth_root_forward_N sub (noRootTokens_run runHeat rep.noRootTok) inv₁' hX.1 clean₁
          disj free₁ anchInRest
      let runFull := runHeat.trans runRefl
      let outRows := rPre ++ (made, pFor (tProc R) x pZero) :: rPost
      have outBagEq : BagEq (rootBagProcess outRows) P' := by
        have eqOut : rootBagProcess outRows = pPar (cPre ++ pFor (tProc R) x pZero :: cPost) := by
          simp [outRows, rootBagProcess, eqPre, eqPost]
        exact eqOut ▸ bagOut
      have preEq : BagEq P (rootBagProcess (rPre ++ (rOcc, pReflect x P_sub) :: rPost)) :=
        rep.rootBag.symm.trans bagHeat'.symm
      refine ⟨label₂, C₂, outRows, runFull,
        ⟨allLocatedSpines_run runFull rep.spines, noTok₂, clean₂, inv₂, ?_, outBagEq, free₂, ?_⟩,
        .inr (.congruence preEq bStep outBagEq)⟩
      · intro pr m; simp only [outRows, List.mem_append, List.mem_cons] at m
        rcases m with inPre | rfl | inPost
        · exact leafNodes pr.2 (by rw [← mapCells]; exact List.mem_map_of_mem (List.mem_append_left _ inPre))
        · exact .guard hX
        · exact leafNodes pr.2 (by rw [← mapCells]; exact List.mem_map_of_mem (List.mem_append_right _ (List.mem_cons_of_mem _ inPost)))
      · intro q qM; obtain ⟨pr, prM, hasQ⟩ := anchInRest q qM
        exact ⟨pr, (List.mem_append.mp prM).elim (List.mem_append_left _)
          (fun r => List.mem_append_right _ (List.mem_cons_of_mem _ r)), hasQ⟩

/-- **Forward simulation of hosted actions and structural changes, interface C.**
Every `HostedRootStepC` from `CleanRepresentsBy` is matched by a `LocatedRun` reaching
`CleanRepresentsBy`, and realizes `BagEq P P' ∨ CanonicalBagStep conventional P P'`. Steps outside
`HostedRootStepC` are not covered. -/
theorem source_step_forward_C [Infinite O] {label : O → Pattern} {C : Configuration Pattern O}
    {P P' : Pattern} {rootRows : List (O × Pattern)} {pats extPats : List Pattern}
    (rep : CleanRepresentsBy label C P rootRows pats)
    (step : HostedRootStepC rootRows pats extPats P P') :
    ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (rows' : List (O × Pattern)),
      LocatedRun label C label' C' ∧
      CleanRepresentsBy label' C' P' rows' extPats ∧
      (BagEq P P' ∨ CanonicalBagStep conventional P P') := by
  cases step with
  | equiv bEq =>
      exact ⟨label, C, rootRows, .refl label C,
        ⟨rep.spines, rep.noRootTok, rep.cleanChildren, rep.rootInv, rep.rootNodes,
         rep.rootBag.trans bEq, rep.freePats, rep.anchPats⟩, .inl bEq⟩
  | comm ms s1 gp plA plB nA nB disj anchRest bagOut =>
      obtain ⟨l', C', rows', run, rep', -, cStep⟩ :=
        forward_comm_step rep ms s1 gp plA plB nA nB disj anchRest bagOut
      exact ⟨l', C', rows', run, rep', .inr cStep⟩
  | commGround ms eg samePat anchRest bagOut =>
      obtain ⟨l', C', rows', run, rep', -, cStep⟩ :=
        forward_commGround_step rep ms eg samePat anchRest bagOut
      exact ⟨l', C', rows', run, rep', .inr cStep⟩
  | refl ms hX sub disj anchRest bagOut =>
      rename_i d cPre cPost x P_sub R pair bs
      have leafNodes := multiSplits_hostedNode ms rep.rootNodes
      obtain ⟨label₁, C₁, cells, runHeat, mapCells, clean₁, inv₁, bagHeat, free₁, -⟩ :=
        multi_root_heating ms label C [] (pair.1 :: pair.2 :: extPats) rep.cleanChildren
          (by simpa using rep.rootInv) rep.freePats (by simpa using rep.anchPats)
      have inv₁' : RootCells label₁ C₁ cells := by simpa using inv₁
      have bagHeat' : BagEq (rootBagProcess cells) (rootBagProcess rootRows) := by simpa using bagHeat
      obtain ⟨rPre, rOcc, rPost, rfl, eqPre, eqPost⟩ := split_cells_1 mapCells
      have mapRest : (rPre ++ rPost).map Prod.snd = cPre ++ cPost := by simp [eqPre, eqPost]
      have anchInRest : ∀ q ∈ extPats, ∃ pr ∈ rPre ++ rPost, SpineHasPattern q (predotU pr.2) := by
        intro q qM; obtain ⟨c, cM, hasQ⟩ := anchRest q qM
        obtain ⟨pr, prM, rfl⟩ := List.mem_map.mp (mapRest ▸ cM)
        exact ⟨pr, prM, hasQ⟩
      obtain ⟨label₂, C₂, made, runRefl, noTok₂, inv₂, clean₂, free₂, cStep⟩ :=
        refl_depth_root_forward_C sub (noRootTokens_run runHeat rep.noRootTok) inv₁' hX.1 clean₁
          disj free₁ anchInRest
      let runFull := runHeat.trans runRefl
      let outRows := rPre ++ (made, listener x R) :: rPost
      have outBagEq : BagEq (rootBagProcess outRows) P' := by
        have eqOut : rootBagProcess outRows = pPar (cPre ++ listener x R :: cPost) := by
          simp [outRows, rootBagProcess, eqPre, eqPost]
        exact eqOut ▸ bagOut
      have preEq : BagEq P (rootBagProcess (rPre ++ (rOcc, pReflect x P_sub) :: rPost)) :=
        rep.rootBag.symm.trans bagHeat'.symm
      refine ⟨label₂, C₂, outRows, runFull,
        ⟨allLocatedSpines_run runFull rep.spines, noTok₂, clean₂, inv₂, ?_, outBagEq, free₂, ?_⟩,
        .inr (.congruence preEq cStep outBagEq)⟩
      · intro pr m; simp only [outRows, List.mem_append, List.mem_cons] at m
        rcases m with inPre | rfl | inPost
        · exact leafNodes pr.2 (by rw [← mapCells]; exact List.mem_map_of_mem (List.mem_append_left _ inPre))
        · exact .guard hX
        · exact leafNodes pr.2 (by rw [← mapCells]; exact List.mem_map_of_mem (List.mem_append_right _ (List.mem_cons_of_mem _ inPost)))
      · intro q qM; obtain ⟨pr, prM, hasQ⟩ := anchInRest q qM
        exact ⟨pr, (List.mem_append.mp prM).elim (List.mem_append_left _)
          (fun r => List.mem_append_right _ (List.mem_cons_of_mem _ r)), hasQ⟩

end ForwardSimulation

/-! ## The hosted correspondence (`N` and `C`): what is proved, not a bisimulation -/

/-- **The hosted correspondence, interface N (named quotes).**
Collects: finiteness of `located`; the encoding of every `HostedNode`; the partition of firings
into `RootVisible` and `Administrative`; at a state with `SystemInvBy` and `BackwardReadyN`, every
admitted firing either keeps the source process (administrative, up to dead locations) or is one
`BagStep conventional`; source soundness along `ReadyLocatedRunN` runs, which assume
`BackwardReadyN` before every firing; and the forward simulation of `HostedRootStepN`
(`source_step_forward_N`). `BackwardReadyN` is not preserved by arbitrary encoded runs, and source
steps outside `HostedRootStepN` are not covered. -/
theorem hosted_correspondence_N (O : Type*) [DecidableEq O] [Infinite O] :
    located.Finite ∧
    (∀ P : Pattern, HostedNode P →
      CleanRepresents (encodeLabel P) encodeConf P ∧ SystemInvN (encodeLabel P) encodeConf P) ∧
    (∀ g : Firing O QNE located PUnit.unit,
      (RootVisible g ∧ ¬ Administrative g) ∨ (Administrative g ∧ ¬ RootVisible g)) ∧
    (∀ {label : O → Pattern} {C : Configuration Pattern O} {P : Pattern}
        {rootRows : List (O × Pattern)} {active : List (ActiveEntry O)},
      SystemInvBy StepRelN label C P rootRows active →
      BackwardReadyN C rootRows active →
      ∀ g : Firing O QNE located PUnit.unit,
        (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g →
        (Administrative g ∧ SystemInvN (res label C g).label (resConf label C g) P) ∨
        (RootVisible g ∧ ∃ P', BagStep conventional P P' ∧
          SystemInvN (res label C g).label (resConf label C g) P')) ∧
    (∀ {label label' : O → Pattern} {C C' : Configuration Pattern O} {P : Pattern},
      ReadyLocatedRunN label C P label' C' →
      ∃ P', Relation.ReflTransGen (BagStep conventional) P P' ∧ SystemInvN label' C' P') ∧
    (∀ {label : O → Pattern} {C : Configuration Pattern O} {P P' : Pattern}
        {rootRows : List (O × Pattern)} {pats extPats : List Pattern},
      CleanRepresentsBy label C P rootRows pats →
      HostedRootStepN rootRows pats extPats P P' →
      ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (rows' : List (O × Pattern)),
        LocatedRun label C label' C' ∧
        CleanRepresentsBy label' C' P' rows' extPats ∧
        (BagEq P P' ∨ BagStep conventional P P')) :=
  ⟨located_finite,
   fun _ hP => ⟨(encode_in_relation hP).1, (encode_in_relation hP).2.1⟩,
   located_firing_partition,
   fun sys ready g adm => located_firing_backward_N sys ready g adm,
   fun run => located_run_backward_N run,
   fun rep st => source_step_forward_N rep st⟩

/-- **The hosted correspondence, interface C (closed canonical quotes, `pvars R = []`).**
Collects: finiteness of `located`; the encoding of every `HostedNode`; the partition of firings;
at a state with `SystemInvBy` and `BackwardReadyC`, every admitted firing either keeps the source
process (administrative, up to dead locations) or is one `CanonicalBagStep conventional`; source
soundness along `ReadyLocatedRunC` runs, which assume `BackwardReadyC` before every firing; and
the forward simulation of `HostedRootStepC` (`source_step_forward_C`). Preservation of
`BackwardReadyC` along arbitrary encoded runs fails, and source steps outside `HostedRootStepC` are not
covered. -/
theorem hosted_correspondence_C (O : Type*) [DecidableEq O] [Infinite O] :
    located.Finite ∧
    (∀ P : Pattern, HostedNode P →
      CleanRepresents (encodeLabel P) encodeConf P ∧ SystemInvC (encodeLabel P) encodeConf P) ∧
    (∀ g : Firing O QNE located PUnit.unit,
      (RootVisible g ∧ ¬ Administrative g) ∨ (Administrative g ∧ ¬ RootVisible g)) ∧
    (∀ {label : O → Pattern} {C : Configuration Pattern O} {P : Pattern}
        {rootRows : List (O × Pattern)} {active : List (ActiveEntry O)},
      SystemInvBy StepRelC label C P rootRows active →
      BackwardReadyC C rootRows active →
      ∀ g : Firing O QNE located PUnit.unit,
        (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g →
        (Administrative g ∧ SystemInvC (res label C g).label (resConf label C g) P) ∨
        (RootVisible g ∧ ∃ P', CanonicalBagStep conventional P P' ∧
          SystemInvC (res label C g).label (resConf label C g) P')) ∧
    (∀ {label label' : O → Pattern} {C C' : Configuration Pattern O} {P : Pattern},
      ReadyLocatedRunC label C P label' C' →
      ∃ P', Relation.ReflTransGen (CanonicalBagStep conventional) P P' ∧ SystemInvC label' C' P') ∧
    (∀ {label : O → Pattern} {C : Configuration Pattern O} {P P' : Pattern}
        {rootRows : List (O × Pattern)} {pats extPats : List Pattern},
      CleanRepresentsBy label C P rootRows pats →
      HostedRootStepC rootRows pats extPats P P' →
      ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (rows' : List (O × Pattern)),
        LocatedRun label C label' C' ∧
        CleanRepresentsBy label' C' P' rows' extPats ∧
        (BagEq P P' ∨ CanonicalBagStep conventional P P')) :=
  ⟨located_finite,
   fun _ hP => ⟨(encode_in_relation hP).1, (encode_in_relation hP).2.2⟩,
   located_firing_partition,
   fun sys ready g adm => located_firing_backward_C sys ready g adm,
   fun run => located_run_backward_C run,
   fun rep st => source_step_forward_C rep st⟩

/-! ## Conservativity on `REFL`-free processes -/

/-- `REFL`-free hosted process nodes (`0`, quoted values `@v`, `par`, and `pFor` — no `pReflect`). -/
inductive NoReflectNode : Pattern → Prop where
  | zero : NoReflectNode pZero
  | quote (v : Pattern) : NoReflectNode (nQuote v)
  | par {a b : Pattern} : NoReflectNode a → NoReflectNode b → NoReflectNode (par a b)
  | guard {t ch A : Pattern} : HostedChan ch → NoReflectNode (pFor t ch A)

theorem NoReflectNode.toHostedNode {P : Pattern} (h : NoReflectNode P) : HostedNode P := by
  induction h with
  | zero => exact .zero
  | quote v => exact .quote v
  | par _ _ ihA ihB => exact .par ihA ihB
  | guard hCh => exact .guard hCh

/-- On any root configuration whose `RootCells` carry `NoReflectNode` terms, `openRoot` is
unconditionally refused. -/
theorem openRoot_refused_of_noReflect {O : Type*} [DecidableEq O] {label : O → Pattern}
    {C : Configuration Pattern O} {rootRows : List (O × Pattern)}
    (inv : RootCells label C rootRows) (noRefl : ∀ q ∈ rootRows, NoReflectNode q.2)
    (g : Firing O QNE located PUnit.unit)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g) :
    g.rule ≠ openRoot := by
  intro opR
  obtain ⟨r, pr, tk, gEq⟩ := eq_openRootAt admitted opR
  rw [gEq] at admitted
  obtain ⟨_, -, enabled, ⟨_, w, solved⟩, -⟩ := (RuleSyntax.admits_iff _).mp admitted
  have known := info_known _ solved
  have rPres : r ∈ C.present := enabled.kept_subset (by simp [openRootAt, Selection.commit])
  have zR : (atLoc (pReflect channelUnknown reflP) rootLoc, r) ∈
      (openRootAt g.opening r pr tk).rule.body.read.zip
        (openRootAt g.opening r pr tk).selection.read := by simp [openRootAt, openRoot]
  have rRead := read_reads _ solved zR
  simp only [psubst_atLoc_any, psubst_pReflect, psubst_rootLoc] at rRead
  have rIn : r ∈ rootRows.map Prod.fst := by
    by_contra notIn; exact inv.others r rPres notIn w known _ rRead.symm
  obtain ⟨⟨r₀, Pr⟩, rMem, eqR⟩ := List.mem_map.mp rIn; subst eqR
  have hR := rRead.trans ((inv.rows _ rMem).2 w known)
  simp only [psubst_atLoc_any, psubst_rootLoc] at hR
  obtain ⟨x, Q, eqP, -⟩ := hostedNode_match_reflect (noRefl _ rMem).toHostedNode
    ((locatedFrame_name.atLoc_iff _ _ _ _).mp hR).1
  have nr := noRefl (r₀, Pr) rMem
  dsimp only at nr
  cases nr <;> simp [pZero, nQuote, par, pPar, pFor, pReflect] at *

/-- **Conservativity on `REFL`-free processes (`↔`)**:
At any `rootState uLabel uC` whose `RootCells` carry `NoReflectNode` terms, every single-firing
transition of `RuleSyntax.step QN O QNE located` coincides **bijectively (`↔`)** with a located
single-firing transition of the 3-rule `FiniteProgram.program` (`commRule`, `heatRule`,
`clearRule`) at `QN`. -/
theorem conservativity_refl_free {O : Type*} [DecidableEq O]
    (uLabel : O → Pattern) (uC : Configuration Pattern O) {rootRows : List (O × Pattern)}
    (inv : RootCells (rootState uLabel uC).label
      ⟨(rootState uLabel uC).knowledge, (rootState uLabel uC).present⟩ rootRows)
    (noRefl : ∀ q ∈ rootRows, NoReflectNode q.2) (s' : State Tm O) :
    Succ (RuleSyntax.step QN O QNE located).toStep (rootState uLabel uC) s' ↔
      ∃ s'' : State Tm O,
        Succ (RuleSyntax.step QN O QNE program).toStep (embed uLabel uC) s'' ∧
        s' = locate rootLoc s'' := by
  have eqEmbed : rootState uLabel uC =
      embed (rootState uLabel uC).label
        ⟨(rootState uLabel uC).knowledge, (rootState uLabel uC).present⟩ := by
    cases uC; rfl
  have iffNoOpen :
      Succ (RuleSyntax.step QN O QNE located).toStep (rootState uLabel uC) s' ↔
        Succ (locatedNoOpen nameAction O) (rootState uLabel uC) s' := by
    constructor
    · rintro ⟨g, adm, rfl⟩
      have adm' : (RuleSyntax.step QN O QNE located).Admits
          (s := embed (rootState uLabel uC).label
            ⟨(rootState uLabel uC).knowledge, (rootState uLabel uC).present⟩) g := by
        rwa [← eqEmbed]
      exact ⟨g, ⟨adm, openRoot_refused_of_noReflect inv noRefl g adm'⟩, rfl⟩
    · rintro ⟨g, ⟨adm, -⟩, rfl⟩; exact ⟨g, adm, rfl⟩
  exact iffNoOpen.trans (transitions_at_root locatedFrame_name uLabel uC s')

/-- Forward `REFL` step returning exact `rows'.map Prod.snd` for multi-step sequential chaining
(**Interface N**). -/
theorem refl_step_forward_list_N {O : Type*} [DecidableEq O] [Infinite O]
    {label : O → Pattern} {C : Configuration Pattern O} {P P' x P_sub R : Pattern}
    {rootRows : List (O × Pattern)} {d : ℕ} {extPats cPre cPost : List Pattern}
    {pair : Pattern × Pattern} {bs : Bindings}
    (rep : CleanRepresentsBy label C P rootRows (pair.1 :: pair.2 :: extPats))
    (ms : MultiSplits rootRows (cPre ++ pReflect x P_sub :: cPost))
    (hX : HostedChan x) (sub : HostedSubStepN d P_sub R pair bs)
    (disj : ∀ q ∈ extPats, ∀ v ∈ pvars q, v ∉ pvars pair.1 ++ pvars pair.2)
    (anchRest : ∀ q ∈ extPats, ∃ c ∈ cPre ++ cPost, SpineHasPattern q (predotU c))
    (bagOut : BagEq (pPar (cPre ++ pFor (tProc R) x pZero :: cPost)) P') :
    ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (rows' : List (O × Pattern)),
      LocatedRun label C label' C' ∧
      rows'.map Prod.snd = cPre ++ pFor (tProc R) x pZero :: cPost ∧
      CleanRepresentsBy label' C' P' rows' extPats ∧
      BagStep conventional P P' := by
  have leafNodes := multiSplits_hostedNode ms rep.rootNodes
  obtain ⟨label₁, C₁, cells, runHeat, mapCells, clean₁, inv₁, bagHeat, free₁, -⟩ :=
    multi_root_heating ms label C [] (pair.1 :: pair.2 :: extPats) rep.cleanChildren
      (by simpa using rep.rootInv) rep.freePats (by simpa using rep.anchPats)
  have inv₁' : RootCells label₁ C₁ cells := by simpa using inv₁
  have bagHeat' : BagEq (rootBagProcess cells) (rootBagProcess rootRows) := by simpa using bagHeat
  obtain ⟨rPre, rOcc, rPost, rfl, eqPre, eqPost⟩ := split_cells_1 mapCells
  have mapRest : (rPre ++ rPost).map Prod.snd = cPre ++ cPost := by simp [eqPre, eqPost]
  have anchInRest : ∀ q ∈ extPats, ∃ pr ∈ rPre ++ rPost, SpineHasPattern q (predotU pr.2) := by
    intro q qM; obtain ⟨c, cM, hasQ⟩ := anchRest q qM
    obtain ⟨pr, prM, rfl⟩ := List.mem_map.mp (mapRest ▸ cM)
    exact ⟨pr, prM, hasQ⟩
  obtain ⟨label₂, C₂, made, runRefl, noTok₂, inv₂, clean₂, free₂, -, bStep⟩ :=
    refl_depth_root_forward_N sub (noRootTokens_run runHeat rep.noRootTok) inv₁' hX.1 clean₁
      disj free₁ anchInRest
  let runFull := runHeat.trans runRefl
  let outRows := rPre ++ (made, pFor (tProc R) x pZero) :: rPost
  have mapOut : outRows.map Prod.snd = cPre ++ pFor (tProc R) x pZero :: cPost := by
    simp [outRows, eqPre, eqPost]
  have outBagEq : BagEq (rootBagProcess outRows) P' := by
    simpa [rootBagProcess, mapOut] using bagOut
  have preEq : BagEq P (rootBagProcess (rPre ++ (rOcc, pReflect x P_sub) :: rPost)) :=
    rep.rootBag.symm.trans bagHeat'.symm
  refine ⟨label₂, C₂, outRows, runFull, mapOut,
    ⟨allLocatedSpines_run runFull rep.spines, noTok₂, clean₂, inv₂, ?_, outBagEq, free₂, ?_⟩,
    .congruence preEq bStep outBagEq⟩
  · intro pr m; simp only [outRows, List.mem_append, List.mem_cons] at m
    rcases m with inPre | rfl | inPost
    · exact leafNodes pr.2 (by rw [← mapCells]; exact List.mem_map_of_mem (List.mem_append_left _ inPre))
    · exact .guard hX
    · exact leafNodes pr.2 (by rw [← mapCells]; exact List.mem_map_of_mem (List.mem_append_right _ (List.mem_cons_of_mem _ inPost)))
  · intro q qM; obtain ⟨pr, prM, hasQ⟩ := anchInRest q qM
    exact ⟨pr, (List.mem_append.mp prM).elim (List.mem_append_left _)
      (fun r => List.mem_append_right _ (List.mem_cons_of_mem _ r)), hasQ⟩

/-- Forward `REFL` step returning exact `rows'.map Prod.snd` for multi-step sequential chaining
(**Interface C**). -/
theorem refl_step_forward_list_C {O : Type*} [DecidableEq O] [Infinite O]
    {label : O → Pattern} {C : Configuration Pattern O} {P P' x P_sub R : Pattern}
    {rootRows : List (O × Pattern)} {d : ℕ} {extPats cPre cPost : List Pattern}
    {pair : Pattern × Pattern} {bs : Bindings}
    (rep : CleanRepresentsBy label C P rootRows (pair.1 :: pair.2 :: extPats))
    (ms : MultiSplits rootRows (cPre ++ pReflect x P_sub :: cPost))
    (hX : HostedChan x) (sub : HostedSubStepC d P_sub R pair bs)
    (disj : ∀ q ∈ extPats, ∀ v ∈ pvars q, v ∉ pvars pair.1 ++ pvars pair.2)
    (anchRest : ∀ q ∈ extPats, ∃ c ∈ cPre ++ cPost, SpineHasPattern q (predotU c))
    (bagOut : BagEq (pPar (cPre ++ listener x R :: cPost)) P') :
    ∃ (label' : O → Pattern) (C' : Configuration Pattern O) (rows' : List (O × Pattern)),
      LocatedRun label C label' C' ∧
      rows'.map Prod.snd = cPre ++ listener x R :: cPost ∧
      CleanRepresentsBy label' C' P' rows' extPats ∧
      CanonicalBagStep conventional P P' := by
  have leafNodes := multiSplits_hostedNode ms rep.rootNodes
  obtain ⟨label₁, C₁, cells, runHeat, mapCells, clean₁, inv₁, bagHeat, free₁, -⟩ :=
    multi_root_heating ms label C [] (pair.1 :: pair.2 :: extPats) rep.cleanChildren
      (by simpa using rep.rootInv) rep.freePats (by simpa using rep.anchPats)
  have inv₁' : RootCells label₁ C₁ cells := by simpa using inv₁
  have bagHeat' : BagEq (rootBagProcess cells) (rootBagProcess rootRows) := by simpa using bagHeat
  obtain ⟨rPre, rOcc, rPost, rfl, eqPre, eqPost⟩ := split_cells_1 mapCells
  have mapRest : (rPre ++ rPost).map Prod.snd = cPre ++ cPost := by simp [eqPre, eqPost]
  have anchInRest : ∀ q ∈ extPats, ∃ pr ∈ rPre ++ rPost, SpineHasPattern q (predotU pr.2) := by
    intro q qM; obtain ⟨c, cM, hasQ⟩ := anchRest q qM
    obtain ⟨pr, prM, rfl⟩ := List.mem_map.mp (mapRest ▸ cM)
    exact ⟨pr, prM, hasQ⟩
  obtain ⟨label₂, C₂, made, runRefl, noTok₂, inv₂, clean₂, free₂, cStep⟩ :=
    refl_depth_root_forward_C sub (noRootTokens_run runHeat rep.noRootTok) inv₁' hX.1 clean₁
      disj free₁ anchInRest
  let runFull := runHeat.trans runRefl
  let outRows := rPre ++ (made, listener x R) :: rPost
  have mapOut : outRows.map Prod.snd = cPre ++ listener x R :: cPost := by
    simp [outRows, eqPre, eqPost]
  have outBagEq : BagEq (rootBagProcess outRows) P' := by
    simpa [rootBagProcess, mapOut] using bagOut
  have preEq : BagEq P (rootBagProcess (rPre ++ (rOcc, pReflect x P_sub) :: rPost)) :=
    rep.rootBag.symm.trans bagHeat'.symm
  refine ⟨label₂, C₂, outRows, runFull, mapOut,
    ⟨allLocatedSpines_run runFull rep.spines, noTok₂, clean₂, inv₂, ?_, outBagEq, free₂, ?_⟩,
    .congruence preEq cStep outBagEq⟩
  · intro pr m; simp only [outRows, List.mem_append, List.mem_cons] at m
    rcases m with inPre | rfl | inPost
    · exact leafNodes pr.2 (by rw [← mapCells]; exact List.mem_map_of_mem (List.mem_append_left _ inPre))
    · exact .guard hX
    · exact leafNodes pr.2 (by rw [← mapCells]; exact List.mem_map_of_mem (List.mem_append_right _ (List.mem_cons_of_mem _ inPost)))
  · intro q qM; obtain ⟨pr, prM, hasQ⟩ := anchInRest q qM
    exact ⟨pr, (List.mem_append.mp prM).elim (List.mem_append_left _)
      (fun r => List.mem_append_right _ (List.mem_cons_of_mem _ r)), hasQ⟩

#print axioms allLocatedSpines_preserved
#print axioms encode_in_relation
#print axioms source_step_forward_N
#print axioms source_step_forward_C
#print axioms hosted_correspondence_N
#print axioms hosted_correspondence_C
#print axioms openRoot_refused_of_noReflect
#print axioms conservativity_refl_free

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem

