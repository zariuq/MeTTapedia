import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Families

/-!
# The tree's driver with delete and inversion: progress by shape on grouped families

A solver of the tree's worklist driver (`familySolver`, a `ContextualDependentWorklist.Solver`) reads the first
equation of the store by its codes (`readFlexData`: no budget, no normalizer) and

* deletes it when both sides are one unknown;
* inverts it, `G := F`, when `F`'s codomain lies below `G`'s, in either orientation;
* is stuck otherwise, in particular when the two codomains are not comparable.

Its rank is the number of equations, and every progress removes one.

**The fragment** (`InFragment`): every declaration of the telescope is a universe family; every equation is a
flex-flex equation of families (`FlexFlex`); and there is a grouping of the unknowns in which the two unknowns of
every equation are in one group and the codomains within a group are comparable. It is the tree's form of the
compatible groups of the codes model, at one domain per equation.

* **Kept by every rule** (`inFragment_delete`, `inFragment_invert`): deletion keeps a sub-store; inversion renames
  `G` to `F` in the other equations, and the grouping is kept because `F` and `G` share a group.
* **Progress by shape** (`familyRound_ne_stuck`): on a nonempty store of the fragment the reader reads the first
  equation (`readFlexData_complete`), and its two codomains are comparable, so a rule fires.
* **Decided** (`family_decided`): on the fragment, the tree's driver reaches, at some budget and at every larger
  one, a principal answer or a certified refutation. The rules never refute (`familyRound_ne_refuted`), so every
  store of the fragment has a principal answer (`principal_of_inFragment`).

Nothing in the rule choice reads a level valuation: the only comparison is `S.R.cumulative`. A comparison that is
not decided either way leaves the solver stuck, and the store is postponed with an exact residual.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentUniverseInjective

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Readers -/

section Readers

/-- Scan a code for the shape of a universe family. -/
def scanFam : {n : Nat} → Tm Head n → Option (List Head × Head)
  | _, .head c => some ([], c)
  | _, .pi (.head p) B => (scanFam B).map fun r => (p :: r.1, r.2)
  | _, _ => none

theorem scanFam_famCode (ps : List Head) (c : Head) : ∀ {n : Nat}, scanFam (famCode ps c : Tm Head n) = some (ps, c) := by
  induction ps with
  | nil => intro n; rfl
  | cons p ps ih => intro n; simp only [famCode_cons, scanFam, ih, Option.map_some]

variable [DecidableEq Head]

/-- **Read a universe family off a code**, checked against the code. -/
def readFam {n : Nat} (t : Tm Head n) : Option (List Head × Head) :=
  match scanFam t with
  | some r => if t = famCode r.1 r.2 then some r else none
  | none => none

theorem readFam_sound {n : Nat} {t : Tm Head n} {r : List Head × Head} (h : readFam t = some r) :
    t = famCode r.1 r.2 := by
  unfold readFam at h
  split at h
  · split_ifs at h with hc
    cases h
    exact hc
  · cases h

theorem readFam_famCode (ps : List Head) (c : Head) {n : Nat} : readFam (famCode ps c : Tm Head n) = some (ps, c) := by
  unfold readFam
  rw [scanFam_famCode]
  simp only [if_true]

/-- **Read an η-long unknown off a code.** -/
def readEta (k : Nat) {n : Nat} (t : Tm Head n) : Option (Fin n) :=
  (List.finRange n).find? fun F => decide (t = etaExp k (.var F))

theorem readEta_sound {k n : Nat} {t : Tm Head n} {F : Fin n} (h : readEta k t = some F) : t = etaExp k (.var F) := by
  unfold readEta at h
  have found := List.find?_some h
  simpa using found

theorem readEta_etaExp (k : Nat) {n : Nat} (F : Fin n) : readEta (Head := Head) k (etaExp k (.var F)) = some F := by
  cases h : readEta (Head := Head) k (etaExp k (.var F)) with
  | none =>
      have absent := (List.find?_eq_none.mp h) F (List.mem_finRange F)
      simp at absent
  | some G =>
      have same := readEta_sound h
      exact congrArg some (Tm.var.inj (etaExp_inj k same)).symm

end Readers

/-! ## Reading a flex-flex equation -/

section Reading

variable {S : Setting Head L} [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]

/-- The data of a flex-flex reading: domains, annotation codomain, the two unknowns, their codomains. -/
structure FlexData (Head : Type) (n : Nat) where
  ps : List Head
  q : Head
  left : Fin n
  right : Fin n
  cl : Head
  cr : Head

/-- **Read a flex-flex equation of families** off its codes. -/
def readFlexData {Θ : Context S.R} (e : Equation (TotalTerm Θ)) : Option (FlexData Head Θ.arity) :=
  (readFam e.1.1.code).bind fun a =>
  (readFam e.2.1.code).bind fun b =>
  (readEta a.1.length e.1.2.code).bind fun F =>
  (readEta a.1.length e.2.2.code).bind fun G =>
  (readFam (Ctx.lookup Θ.raw F)).bind fun dF =>
  (readFam (Ctx.lookup Θ.raw G)).bind fun dG =>
  if b = a ∧ dF.1 = a.1 ∧ dG.1 = a.1 ∧ S.R.isUniverse a.2 ∧ S.R.isUniverse dF.2 ∧ S.R.isUniverse dG.2 ∧
      S.R.cumulative dF.2 a.2 ∧ S.R.cumulative dG.2 a.2 then
    some ⟨a.1, a.2, F, G, dF.2, dG.2⟩
  else none

/-- **The reader reads every flex-flex equation of families.** -/
theorem readFlexData_complete {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexFlex e) :
    readFlexData e = some ⟨v.ps, v.q, v.left, v.right, v.cl, v.cr⟩ := by
  unfold readFlexData
  rw [v.annotation_left, v.annotation_right, readFam_famCode, v.side_left, v.side_right]
  simp [readEta_etaExp, v.declared_left, v.declared_right, readFam_famCode, v.universe_q, v.universe_left,
    v.universe_right, v.below_left, v.below_right]

/-- What a successful reading says. -/
theorem readFlexData_sound {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {d : FlexData Head Θ.arity}
    (h : readFlexData e = some d) :
    e.1.1.code = famCode d.ps d.q ∧ e.2.1.code = famCode d.ps d.q ∧
      e.1.2.code = etaExp d.ps.length (.var d.left) ∧ e.2.2.code = etaExp d.ps.length (.var d.right) ∧
      Ctx.lookup Θ.raw d.left = famCode d.ps d.cl ∧ Ctx.lookup Θ.raw d.right = famCode d.ps d.cr ∧
      S.R.isUniverse d.q ∧ S.R.isUniverse d.cl ∧ S.R.isUniverse d.cr ∧
      S.R.cumulative d.cl d.q ∧ S.R.cumulative d.cr d.q := by
  unfold readFlexData at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, F, hF, G, hG, dF, hdF, dG, hdG, h⟩ := h
  split_ifs at h with hc
  cases h
  obtain ⟨rfl, hdF1, hdG1, hq, hcl, hcr, hbl, hbr⟩ := hc
  refine ⟨readFam_sound ha, readFam_sound hb, readEta_sound hF, readEta_sound hG, ?_, ?_, hq, hcl, hcr, hbl, hbr⟩
  · rw [readFam_sound hdF, hdF1]
  · rw [readFam_sound hdG, hdG1]

/-- The view of a successful reading. -/
def viewOf {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {d : FlexData Head Θ.arity}
    (h : readFlexData e = some d) : FlexFlex e where
  ps := d.ps
  q := d.q
  left := d.left
  right := d.right
  cl := d.cl
  cr := d.cr
  annotation_left := (readFlexData_sound h).1
  annotation_right := (readFlexData_sound h).2.1
  side_left := (readFlexData_sound h).2.2.1
  side_right := (readFlexData_sound h).2.2.2.1
  declared_left := (readFlexData_sound h).2.2.2.2.1
  declared_right := (readFlexData_sound h).2.2.2.2.2.1
  universe_q := (readFlexData_sound h).2.2.2.2.2.2.1
  universe_left := (readFlexData_sound h).2.2.2.2.2.2.2.1
  universe_right := (readFlexData_sound h).2.2.2.2.2.2.2.2.1
  below_left := (readFlexData_sound h).2.2.2.2.2.2.2.2.2.1
  below_right := (readFlexData_sound h).2.2.2.2.2.2.2.2.2.2

end Reading

section Declarations

variable {S : Setting Head L} [DecidableEq Head]

/-- Whether every declaration of a telescope is a universe family, decided. -/
def allFamiliesB (Θ : Context S.R) : Bool :=
  (List.finRange Θ.arity).all fun i => (readFam (Ctx.lookup Θ.raw i)).isSome

theorem allFamilies_of_B {Θ : Context S.R} (h : allFamiliesB Θ = true) : AllFamilies Θ := by
  intro i
  have hi := List.all_eq_true.mp h i (List.mem_finRange i)
  cases hr : readFam (Ctx.lookup Θ.raw i) with
  | none => rw [hr] at hi; cases hi
  | some r => exact ⟨r.1, r.2, readFam_sound hr⟩

theorem allFamiliesB_of {Θ : Context S.R} (all : AllFamilies Θ) : allFamiliesB Θ = true := by
  apply List.all_eq_true.mpr
  intro i _
  obtain ⟨ps, c, hi⟩ := all i
  rw [hi, readFam_famCode]
  rfl

end Declarations

/-! ## Views -/

section Views

variable {S : Setting Head L}

/-- **The reading of an equation is unique.** -/
theorem FlexFlex.unique {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v w : FlexFlex e) :
    v.ps = w.ps ∧ v.left = w.left ∧ v.right = w.right ∧ v.cl = w.cl ∧ v.cr = w.cr := by
  obtain ⟨hps, _⟩ := famCode_inj (v.annotation_left.symm.trans w.annotation_left)
  have hl : v.left = w.left := by
    have same := v.side_left.symm.trans w.side_left
    rw [hps] at same
    exact Tm.var.inj (etaExp_inj _ same)
  have hr : v.right = w.right := by
    have same := v.side_right.symm.trans w.side_right
    rw [hps] at same
    exact Tm.var.inj (etaExp_inj _ same)
  have dl : Ctx.lookup Θ.raw v.left = famCode w.ps w.cl := by rw [hl]; exact w.declared_left
  have dr : Ctx.lookup Θ.raw v.right = famCode w.ps w.cr := by rw [hr]; exact w.declared_right
  exact ⟨hps, hl, hr, (famCode_inj (v.declared_left.symm.trans dl)).2,
    (famCode_inj (v.declared_right.symm.trans dr)).2⟩

/-- The view of the swapped equation. -/
def FlexFlex.swap {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexFlex e) :
    FlexFlex ((e.2, e.1) : Equation (TotalTerm Θ)) where
  ps := v.ps
  q := v.q
  left := v.right
  right := v.left
  cl := v.cr
  cr := v.cl
  annotation_left := v.annotation_right
  annotation_right := v.annotation_left
  side_left := v.side_right
  side_right := v.side_left
  declared_left := v.declared_right
  declared_right := v.declared_left
  universe_q := v.universe_q
  universe_left := v.universe_right
  universe_right := v.universe_left
  below_left := v.below_right
  below_right := v.below_left

theorem solves_swap {Θ Δ : Context S.R} (f : Δ ⟶ Θ) (e : Equation (TotalTerm Θ)) :
    (frames S.levels).Solves f ((e.2, e.1) : Equation (TotalTerm Θ)) ↔ (frames S.levels).Solves f e :=
  ⟨fun h => ((frames S.levels).equivalence Δ).symm h, fun h => ((frames S.levels).equivalence Δ).symm h⟩

/-- Swapping the sides of the first equation keeps the solutions. -/
theorem swap_equivalent {Θ : Context S.R} (e : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ)) :
    (frames S.levels).Equivalent (e :: rest) (((e.2, e.1) : Equation (TotalTerm Θ)) :: rest) := by
  intro Δ f
  constructor
  · intro solved e' member
    rcases List.mem_cons.mp member with rfl | member
    · exact (solves_swap f e).mpr (solved e List.mem_cons_self)
    · exact solved e' (List.mem_cons_of_mem _ member)
  · intro solved e' member
    rcases List.mem_cons.mp member with rfl | member
    · exact (solves_swap f e').mp (solved _ List.mem_cons_self)
    · exact solved e' (List.mem_cons_of_mem _ member)

/-- `G := F` on unknowns. -/
def assignVar {n : Nat} (F G : Fin n) (i : Fin n) : Fin n := if i = G then F else i

theorem assignSub_var {n : Nat} (F G i : Fin n) : assignSub (Head := Head) F G i = .var (assignVar F G i) := by
  unfold assignSub assignVar
  split_ifs <;> rfl

/-- Under `G := F`, a declared family keeps its domains, and its codomain is replaced by one below it. -/
theorem declared_assign (algebra : CumulativeAlgebra S.R) {Θ : Context S.R} {e : Equation (TotalTerm Θ)}
    (v : FlexFlex e) (below : S.R.cumulative v.cl v.cr) {X : Fin Θ.arity} {ps : List Head} {c : Head}
    (hX : Ctx.lookup Θ.raw X = famCode ps c) (hc : S.R.isUniverse c) :
    ∃ c', Ctx.lookup Θ.raw (assignVar v.left v.right X) = famCode ps c' ∧ S.R.isUniverse c' ∧
      ∀ q, S.R.cumulative c q → S.R.cumulative c' q := by
  by_cases h : X = v.right
  · subst h
    obtain ⟨hps, hcr⟩ := famCode_inj (hX.symm.trans v.declared_right)
    refine ⟨v.cl, ?_, v.universe_left, fun q le => algebra.trans below (hcr ▸ le)⟩
    unfold assignVar
    rw [if_pos rfl, v.declared_left, hps]
  · refine ⟨c, ?_, hc, fun _ le => le⟩
    unfold assignVar
    rw [if_neg h]
    exact hX

/-- **The view of an equation, transported along `G := F`.** -/
theorem transport_nonempty (algebra : CumulativeAlgebra S.R) {Θ : Context S.R} {e e' : Equation (TotalTerm Θ)}
    (v : FlexFlex e) (all : AllFamilies Θ) (below : S.R.cumulative v.cl v.cr) (w : FlexFlex e') :
    ∃ t : FlexFlex (((frames S.levels).act
        (assign Θ all v.declared_left v.declared_right v.universe_left v.universe_right below) e'.1,
        (frames S.levels).act
        (assign Θ all v.declared_left v.declared_right v.universe_left v.universe_right below) e'.2) :
          Equation (TotalTerm Θ)),
      t.left = assignVar v.left v.right w.left ∧ t.right = assignVar v.left v.right w.right := by
  obtain ⟨cl', hl', ul', bl'⟩ := declared_assign algebra v below w.declared_left w.universe_left
  obtain ⟨cr', hr', ur', br'⟩ := declared_assign algebra v below w.declared_right w.universe_right
  refine ⟨{
    ps := w.ps
    q := w.q
    left := assignVar v.left v.right w.left
    right := assignVar v.left v.right w.right
    cl := cl'
    cr := cr'
    annotation_left := ?_
    annotation_right := ?_
    side_left := ?_
    side_right := ?_
    declared_left := hl'
    declared_right := hr'
    universe_q := w.universe_q
    universe_left := ul'
    universe_right := ur'
    below_left := bl' _ w.below_left
    below_right := br' _ w.below_right }, rfl, rfl⟩
  · change Presentation.subst (assignSub v.left v.right) e'.1.1.code = _
    rw [w.annotation_left, famCode_subst]
  · change Presentation.subst (assignSub v.left v.right) e'.2.1.code = _
    rw [w.annotation_right, famCode_subst]
  · change Presentation.subst (assignSub v.left v.right) e'.1.2.code = _
    rw [w.side_left, subst_etaExp]
    simp only [Presentation.subst, assignSub_var]
  · change Presentation.subst (assignSub v.left v.right) e'.2.2.code = _
    rw [w.side_right, subst_etaExp]
    simp only [Presentation.subst, assignSub_var]

end Views

/-! ## The fragment -/

section Fragment

variable {S : Setting Head L}

/-- The two unknowns of every equation are in one group. -/
def Grouped {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (group : Fin Θ.arity → Nat) : Prop :=
  ∀ e ∈ problem, ∀ v : FlexFlex e, group v.left = group v.right

/-- Within a group, the codomains of the declared families are comparable. -/
def Comparable (Θ : Context S.R) (group : Fin Θ.arity → Nat) : Prop :=
  ∀ i j : Fin Θ.arity, group i = group j → ∀ (ps ps' : List Head) (c c' : Head),
    Ctx.lookup Θ.raw i = famCode ps c → Ctx.lookup Θ.raw j = famCode ps' c' →
      S.R.cumulative c c' ∨ S.R.cumulative c' c

/-- **The fragment of grouped families.** -/
structure InFragment {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop where
  families : AllFamilies Θ
  shapes : ∀ e ∈ problem, Nonempty (FlexFlex e)
  grouped : ∃ group, Grouped problem group ∧ Comparable Θ group

/-- **Deletion keeps the fragment.** -/
theorem inFragment_delete {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (inside : InFragment (e :: rest)) : InFragment rest := by
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
  exact ⟨inside.families, fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member),
    ⟨group, fun e' member => grouped e' (List.mem_cons_of_mem _ member), comparable⟩⟩

/-- **Inversion keeps the fragment.** -/
theorem inFragment_invert (algebra : CumulativeAlgebra S.R) {Θ : Context S.R} {e : Equation (TotalTerm Θ)}
    (v : FlexFlex e) (all : AllFamilies Θ) (below : S.R.cumulative v.cl v.cr) {rest : EquationStore (TotalTerm Θ)}
    (shapes : ∀ e' ∈ rest, Nonempty (FlexFlex e')) (group : Fin Θ.arity → Nat) (grouped : Grouped rest group)
    (together : group v.left = group v.right) (comparable : Comparable Θ group) :
    InFragment ((frames S.levels).applyStore
      (assign Θ all v.declared_left v.declared_right v.universe_left v.universe_right below) rest) := by
  have keep : ∀ X, group (assignVar v.left v.right X) = group X := by
    intro X
    unfold assignVar
    split_ifs with h
    · rw [h, together]
    · rfl
  refine ⟨all, ?_, ⟨group, ?_, comparable⟩⟩
  · intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := shapes e' inRest
    obtain ⟨t, _, _⟩ := transport_nonempty algebra v all below w
    exact ⟨t⟩
  · intro e'' member u
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := shapes e' inRest
    obtain ⟨t, tl, tr⟩ := transport_nonempty algebra v all below w
    obtain ⟨_, ul, ur, _, _⟩ := FlexFlex.unique u t
    rw [ul, ur, tl, tr, keep, keep]
    exact grouped e' inRest w

end Fragment

/-! ## The solver -/

section Rank

variable {S : Setting Head L}

/-- The rank: the number of equations. -/
def storeRank {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) : Nat × Nat := (problem.length, 0)

theorem below_of_length {Γ Γ' : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {remaining : EquationStore (TotalTerm Γ')} (shorter : remaining.length < problem.length) :
    ContextualDependentWorklist.Below (storeRank remaining) (storeRank problem) :=
  Prod.Lex.left _ _ shorter

end Rank

section Solver

variable {S : Setting Head L} [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **One step on a read equation**: delete, invert in either orientation, or stuck. -/
def stepOf {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ) (v : FlexFlex e)
    (rest : EquationStore (TotalTerm Θ)) : Round S.levels storeRank (e :: rest) :=
  if hsame : v.left = v.right then
    .progress (deleteUpdate v hsame rest) (below_of_length (by
      show rest.length < (e :: rest).length
      simp))
  else if hb : S.R.cumulative v.cl v.cr then
    .progress (invertUpdate facts roots heads algebra rigid complete v all hb rest) (below_of_length (by
      show ((frames S.levels).applyStore _ rest).length < (e :: rest).length
      simp [Frames.applyStore]))
  else if hb' : S.R.cumulative v.cr v.cl then
    .progress ((invertUpdate facts roots heads algebra rigid complete v.swap all hb' rest).rephrase
        (swap_equivalent e rest)) (below_of_length (by
      show ((frames S.levels).applyStore _ rest).length < (e :: rest).length
      simp [Frames.applyStore]))
  else .stuck

/-- **The round of the solver**: read the first equation, then step. -/
def familyRound : {Γ : Context S.R} → (problem : EquationStore (TotalTerm Γ)) → Round S.levels storeRank problem
  | _, [] => .stuck
  | Θ, e :: rest =>
      if hall : allFamiliesB Θ = true then
        match hd : readFlexData e with
        | some _ => stepOf facts roots heads algebra rigid complete (allFamilies_of_B hall) (viewOf hd) rest
        | none => .stuck
      else .stuck

/-- **The tree's driver with delete and inversion.** -/
def familySolver : ContextualDependentWorklist.Solver S.levels where
  rank := storeRank
  round := familyRound facts roots heads algebra rigid complete

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] in
theorem stepOf_ne_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ) (v : FlexFlex e)
    (rest : EquationStore (TotalTerm Θ))
    (decided : v.left = v.right ∨ S.R.cumulative v.cl v.cr ∨ S.R.cumulative v.cr v.cl) :
    stepOf facts roots heads algebra rigid complete all v rest ≠ .stuck := by
  unfold stepOf
  split_ifs with h1 h2 h3
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · rcases decided with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact absurd h h3

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] in
theorem stepOf_ne_refuted {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ) (v : FlexFlex e)
    (rest : EquationStore (TotalTerm Θ)) (absent : ¬ (frames S.levels).Solvable (e :: rest)) :
    stepOf facts roots heads algebra rigid complete all v rest ≠ .refuted absent := by
  unfold stepOf
  split_ifs <;> intro h <;> cases h

/-- **The rules never refute.** -/
theorem familyRound_ne_refuted {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ))
    (absent : ¬ (frames S.levels).Solvable problem) :
    familyRound facts roots heads algebra rigid complete problem ≠ .refuted absent := by
  cases problem with
  | nil => intro h; cases h
  | cons e rest =>
      simp only [familyRound]
      split_ifs with hall
      · split
        · exact stepOf_ne_refuted facts roots heads algebra rigid complete _ _ rest absent
        · intro h; cases h
      · intro h; cases h

/-- **Progress by shape**: on a nonempty store of the fragment, the round is not stuck. -/
theorem familyRound_ne_stuck {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} (inside : InFragment problem)
    (nonempty : problem ≠ []) : familyRound facts roots heads algebra rigid complete problem ≠ .stuck := by
  cases problem with
  | nil => exact absurd rfl nonempty
  | cons e rest =>
      obtain ⟨v⟩ := inside.shapes e List.mem_cons_self
      obtain ⟨group, grouped, comparable⟩ := inside.grouped
      have hall := allFamiliesB_of inside.families
      have hd := readFlexData_complete v
      simp only [familyRound, dif_pos hall]
      split
      · rename_i d hd'
        apply stepOf_ne_stuck
        let w := viewOf hd'
        by_cases same : w.left = w.right
        · exact .inl same
        · exact .inr (comparable w.left w.right (grouped e List.mem_cons_self w) w.ps w.ps w.cl w.cr
            w.declared_left w.declared_right)
      · rename_i hd'
        rw [hd] at hd'
        cases hd'

/-- **The rules keep the fragment.** -/
theorem familyRound_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} {update : Update S.levels problem}
    {smaller : Below (storeRank update.remaining) (storeRank problem)} (inside : InFragment problem)
    (progressed : familyRound facts roots heads algebra rigid complete problem = .progress update smaller) :
    InFragment update.remaining := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      obtain ⟨group, grouped, comparable⟩ := inside.grouped
      have restShapes : ∀ e' ∈ rest, Nonempty (FlexFlex e') :=
        fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member)
      have restGrouped : Grouped rest group := fun e' member => grouped e' (List.mem_cons_of_mem _ member)
      simp only [familyRound] at progressed
      split_ifs at progressed with hall
      split at progressed
      · rename_i d hd
        unfold stepOf at progressed
        split_ifs at progressed with h1 h2 h3
        · cases progressed
          exact inFragment_delete inside
        · cases progressed
          exact inFragment_invert algebra (viewOf hd) (allFamilies_of_B hall) h2 restShapes group restGrouped
            (grouped e List.mem_cons_self _) comparable
        · cases progressed
          exact inFragment_invert algebra (viewOf hd).swap (allFamilies_of_B hall) h3 restShapes group restGrouped
            (grouped e List.mem_cons_self _).symm comparable
      · cases progressed

/-- **The fragment of the solver**: kept by its rounds, never stuck before the store is empty. -/
def familyFragment : ContextualDependentWorklist.Fragment (familySolver facts roots heads algebra rigid complete) where
  holds := InFragment
  stable := fun inside progressed => familyRound_stable facts roots heads algebra rigid complete inside progressed
  decisive := fun inside nonempty => familyRound_ne_stuck facts roots heads algebra rigid complete inside nonempty

include facts roots heads algebra rigid complete in
/-- **Decided by shape**: on the fragment, the tree's driver with delete and inversion reaches, at some budget and
at every larger one, a principal answer or a certified refutation. -/
theorem family_decided {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)} (inside : InFragment original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (familySolver facts roots heads algebra rigid complete) original larger =
          run (familySolver facts roots heads algebra rigid complete) original fuel ∧
        ((∃ state finished, run (familySolver facts roots heads algebra rigid complete) original larger =
              .solved state finished ∧ (frames S.levels).Principal original state.answer) ∨
          (∃ absent, run (familySolver facts roots heads algebra rigid complete) original larger = .refuted absent)) :=
  (familyFragment facts roots heads algebra rigid complete).decided inside

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
/-- A driver whose rounds never refute never reports a refutation. -/
theorem drive_ne_refuted (solver : ContextualDependentWorklist.Solver S.levels)
    (never : ∀ {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) (absent : ¬ (frames S.levels).Solvable problem),
      solver.round problem ≠ .refuted absent) {Γ : Context S.R} {original : EquationStore (TotalTerm Γ)} :
    ∀ (fuel : Nat) (state : Update S.levels original) (absent : ¬ (frames S.levels).Solvable original),
      drive solver fuel state ≠ .refuted absent
  | 0, _, _ => by intro h; cases h
  | fuel + 1, state, absent => by
      rw [drive_succ]
      cases decided : advance solver state with
      | next next => exact drive_ne_refuted solver never fuel next absent
      | done outcome =>
          dsimp only
          intro same
          subst same
          unfold advance at decided
          split at decided
          · cases decided
          · split at decided
            · cases decided
            · rename_i absent' isRefuted
              exact never _ absent' isRefuted
            · cases decided

include facts roots heads algebra rigid complete in
/-- **Every store of the fragment has a principal answer.** -/
theorem principal_of_inFragment {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InFragment original) :
    ∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), (frames S.levels).Principal original answer := by
  obtain ⟨fuel, ends⟩ := family_decided facts roots heads algebra rigid complete inside
  rcases (ends fuel le_rfl).2 with ⟨state, _, _, principal⟩ | ⟨absent, refuted⟩
  · exact ⟨_, _, principal⟩
  · exact absurd refuted (drive_ne_refuted (familySolver facts roots heads algebra rigid complete)
      (fun problem absent => familyRound_ne_refuted facts roots heads algebra rigid complete problem absent)
      fuel _ absent)

end Solver

/-! ## Membership, decided -/

section Membership

variable {S : Setting Head L} [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]

/-- The codomains of all declared families are pairwise comparable, decided. -/
def comparableB (Θ : Context S.R) : Bool :=
  (List.finRange Θ.arity).all fun i => (List.finRange Θ.arity).all fun j =>
    match readFam (Ctx.lookup Θ.raw i), readFam (Ctx.lookup Θ.raw j) with
    | some a, some b => decide (S.R.cumulative a.2 b.2 ∨ S.R.cumulative b.2 a.2)
    | _, _ => true

omit [∀ head, Decidable (S.R.isUniverse head)] in
theorem comparable_of_B {Θ : Context S.R} (h : comparableB Θ = true) : Comparable Θ (fun _ => 0) := by
  intro i j _ ps ps' c c' hi hj
  have hij := List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_finRange i)) j (List.mem_finRange j)
  rw [hi, hj, readFam_famCode, readFam_famCode] at hij
  exact of_decide_eq_true hij

/-- **Membership in the fragment, decided**, with all unknowns in one group. -/
def inFragmentB {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Bool :=
  allFamiliesB Θ && problem.all (fun e => (readFlexData e).isSome) && comparableB Θ

theorem inFragment_of_B {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (h : inFragmentB problem = true) :
    InFragment problem := by
  simp only [inFragmentB, Bool.and_eq_true] at h
  obtain ⟨⟨hall, hshapes⟩, hcomp⟩ := h
  refine ⟨allFamilies_of_B hall, fun e member => ?_, ⟨fun _ => 0, fun _ _ _ => rfl, comparable_of_B hcomp⟩⟩
  have he := List.all_eq_true.mp hshapes e member
  cases hd : readFlexData e with
  | none => rw [hd] at he; cases he
  | some d => exact ⟨viewOf hd⟩

end Membership

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
