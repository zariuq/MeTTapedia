import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.TrueMeet

/-!
# The tree's driver with the true meet: progress by shape on meet groups

A solver of the tree's worklist driver (`meetGroupSolver`) for unary families. It reads the first equation
`λ x. A x ≐ λ x. B x` at `Π (x : U_p). U_q` by its codes (`readFitData`), and

* deletes it when `A` and `B` are one unknown;
* raises `A := λ x. B x` when `B` fits `A`, or `B := λ x. A x` when `A` fits `B` (`raiseContractUpdate`);
* when neither fits and the two **meet**, lowers the unknown with the larger domain to the meet and raises the
  other (`trueMeetUpdate`), in either orientation;
* is stuck otherwise.

**Compatible views** (`Compat`): one fits the other, or they meet, that is one has the smaller domain and the smaller
codomain and the other's domain lies below its codomain. **The fragment** (`InMeetFragment`): every declaration is
a universe family; every equation is a unary flex-flex equation of families (`FitFlex`); and there is a grouping in
which the two unknowns of every equation share a group and, within a group, any two different unknowns have
compatible views. It contains the fragment of fitting groups (`inMeetFragment_of_fit`).

* **The meet keeps compatibility** (`Compat.meet`): an unknown compatible with both meeting views is compatible with
  their meet. By transitivity of cumulativity alone.
* Kept by every rule (`inMeetFragment_delete`, `inMeetFragment_raise`, `inMeetFragment_meet`); **progress by shape**
  (`meetGroupRound_ne_stuck`); decided (`meetGroup_decided`), and every store of the fragment has a principal
  answer (`principal_of_inMeetFragment`).

Nothing in the rule choice reads a level valuation: the comparisons are `S.R.cumulative` only.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Compatible views -/

section Views

variable {R : Rules Head}

/-- **Two unary views `(p, c)` and `(p', c')` are compatible**: the first fits the second, the second fits the first,
the first meets the second (smaller domain and codomain, the second's domain below the first's codomain), or the
second meets the first. -/
def Compat (R : Rules Head) (p c p' c' : Head) : Prop :=
  (R.cumulative p' p ∧ R.cumulative c c') ∨ (R.cumulative p p' ∧ R.cumulative c' c) ∨
    (R.cumulative p p' ∧ R.cumulative c c' ∧ R.cumulative p' c) ∨
    (R.cumulative p' p ∧ R.cumulative c' c ∧ R.cumulative p c')

instance [DecidableRel R.cumulative] (p c p' c' : Head) : Decidable (Compat R p c p' c') := by
  unfold Compat
  infer_instance

theorem Compat.symm {p c p' c' : Head} (h : Compat R p c p' c') : Compat R p' c' p c := by
  rcases h with h | h | h | h
  · exact .inr (.inl h)
  · exact .inl h
  · exact .inr (.inr (.inr h))
  · exact .inr (.inr (.inl h))

/-- **The meet keeps compatibility**: if `Z` is compatible with `A` and with `B`, and `A` meets `B` (so the meet is
`(pB, cA)`), then `Z` is compatible with the meet. -/
theorem Compat.meet (trans : ∀ {u v w : Head}, R.cumulative u v → R.cumulative v w → R.cumulative u w)
    {pZ cZ pA cA pB cB : Head} (za : Compat R pZ cZ pA cA) (zb : Compat R pZ cZ pB cB)
    (dom : R.cumulative pA pB) (cod : R.cumulative cA cB) (cross : R.cumulative pB cA) :
    Compat R pZ cZ pB cA := by
  rcases zb with ⟨b1, _⟩ | ⟨b1, b2⟩ | ⟨b1, _, b3⟩ | ⟨b1, _, _⟩
  · -- `Z` fits `B`
    rcases za with ⟨_, a2⟩ | ⟨a1, a2⟩ | ⟨_, a2, _⟩ | ⟨_, a2, a3⟩
    · exact .inl ⟨b1, a2⟩
    · exact .inr (.inl ⟨trans a1 dom, a2⟩)
    · exact .inl ⟨b1, a2⟩
    · exact .inr (.inr (.inr ⟨b1, a2, a3⟩))
  · -- `B` fits `Z`
    exact .inr (.inl ⟨b1, trans cod b2⟩)
  · -- `Z` meets `B`
    rcases za with ⟨_, a2⟩ | ⟨_, a2⟩ | ⟨_, a2, _⟩ | ⟨_, a2, _⟩
    · exact .inr (.inr (.inl ⟨b1, a2, b3⟩))
    · exact .inr (.inl ⟨b1, a2⟩)
    · exact .inr (.inr (.inl ⟨b1, a2, b3⟩))
    · exact .inr (.inl ⟨b1, a2⟩)
  · -- `B` meets `Z`
    rcases za with ⟨_, a2⟩ | ⟨a1, a2⟩ | ⟨_, a2, _⟩ | ⟨_, a2, a3⟩
    · exact .inl ⟨b1, a2⟩
    · exact .inr (.inr (.inr ⟨b1, a2, trans a1 (trans dom cross)⟩))
    · exact .inl ⟨b1, a2⟩
    · exact .inr (.inr (.inr ⟨b1, a2, a3⟩))

end Views

/-! ## The fragment -/

section Fragment

/-- **Of two different unknowns in one group, the declared unary views are compatible.** -/
def MeetComparable (R : Rules Head) {n : Nat} (Γ : Ctx Head n) (group : Fin n → Nat) : Prop :=
  ∀ i j : Fin n, i ≠ j → group i = group j → ∀ (pi ci pj cj : Head),
    Ctx.lookup Γ i = famCode [pi] ci → Ctx.lookup Γ j = famCode [pj] cj → Compat R pi ci pj cj

/-- **The fragment of meet groups.** -/
structure InMeetFragment {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop where
  families : AllFamilies Θ
  shapes : ∀ e ∈ problem, Nonempty (FitFlex e)
  grouped : ∃ group : Fin Θ.arity → Nat,
    (∀ e ∈ problem, ∀ v : FitFlex e, group v.left = group v.right) ∧ MeetComparable S.R Θ.raw group

/-- **The fragment of fitting groups lies inside.** -/
theorem inMeetFragment_of_fit {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : InFitFragment problem) : InMeetFragment problem := by
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
  refine ⟨inside.families, inside.shapes, ⟨group, grouped, ?_⟩⟩
  intro i j ne same pi ci pj cj di dj
  rcases comparable i j ne same pi ci pj cj di dj with fits | fits
  · exact .inr (.inl ⟨fits.1, fits.2⟩)
  · exact .inl ⟨fits.1, fits.2⟩

theorem inMeetFragment_delete {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (inside : InMeetFragment (e :: rest)) : InMeetFragment rest := by
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
  exact ⟨inside.families, fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member),
    ⟨group, fun e' member => grouped e' (List.mem_cons_of_mem _ member), comparable⟩⟩

variable [DecidableEq Head] [DecidableRel S.R.cumulative] (algebra : CumulativeAlgebra S.R)

/-- **Domain raising keeps the fragment.** -/
theorem inMeetFragment_raise {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e) (all : AllFamilies Θ)
    {rest : EquationStore (TotalTerm Θ)} (shapes : ∀ e' ∈ rest, Nonempty (FitFlex e')) (group : Fin Θ.arity → Nat)
    (grouped : ∀ e' ∈ rest, ∀ w : FitFlex e', group w.left = group w.right) (together : group v.F = group v.G)
    (comparable : MeetComparable S.R Θ.raw group) : InMeetFragment (contractStore algebra v all rest) := by
  have keep : ∀ X, group (raiseVar v.F v.G X) = group X := by
    intro X
    unfold raiseVar
    split_ifs with h
    · rw [h, together]
    · rfl
  refine ⟨all, ?_, ⟨group, ?_, comparable⟩⟩
  · intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := shapes e' inRest
    obtain ⟨t, _, _⟩ := contract_view algebra v all w
    exact ⟨t⟩
  · intro e'' member u
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := shapes e' inRest
    obtain ⟨t, tl, tr⟩ := contract_view algebra v all w
    obtain ⟨ul, ur⟩ := FitFlex.unique u t
    rw [ul, ur, tl, tr, keep, keep]
    exact grouped e' inRest w

omit [DecidableEq Head] [DecidableRel S.R.cumulative] in
include algebra in
/-- **The view of an equation over the lowered telescope**: the same codes and unknowns, the lowered unknown at its
family of the meet. -/
theorem lower_view {Θ : Context S.R} {e e' : Equation (TotalTerm Θ)} (v : FitFlex e) (meets : Meets v)
    (w : FitFlex e') :
    ∃ t : FitFlex (((frames S.levels).act (lowerHom Θ v meets) e'.1, (frames S.levels).act (lowerHom Θ v meets) e'.2) :
        Equation (TotalTerm (lowered Θ v meets))), t.left = w.left ∧ t.right = w.right := by
  have side : ∀ (Z : Fin Θ.arity) (pZ cZ : Head), Ctx.lookup Θ.raw Z = famCode [pZ] cZ → S.R.isUniverse cZ →
      S.R.cumulative cZ w.q → ∃ cZ', Ctx.lookup (setFamAt Θ.raw v.right [v.pr] v.cl) Z = famCode [pZ] cZ' ∧
        S.R.isUniverse cZ' ∧ S.R.cumulative cZ' w.q := by
    intro Z pZ cZ declared hc below
    by_cases hZ : Z = v.right
    · rw [hZ] at declared ⊢
      obtain ⟨hp, hcZ⟩ := famCode_inj (declared.symm.trans v.declared_right)
      refine ⟨v.cl, ?_, v.universe_cl, algebra.trans meets.2.1 (by rw [← hcZ]; exact below)⟩
      rw [lookup_setFamAt_self, (List.cons.inj hp).1]
    · exact ⟨cZ, by rw [lookup_setFamAt_ne Θ.raw v.right Z [v.pr] v.cl hZ]; exact declared, hc, below⟩
  obtain ⟨cl', dl, ul, bl⟩ := side w.left w.pl w.cl w.declared_left w.universe_cl w.codomain_left
  obtain ⟨cr', dr, ur, br⟩ := side w.right w.pr w.cr w.declared_right w.universe_cr w.codomain_right
  exact ⟨{
    p := w.p
    q := w.q
    left := w.left
    right := w.right
    pl := w.pl
    cl := cl'
    pr := w.pr
    cr := cr'
    annotation_left := by
      change Presentation.subst ids e'.1.1.code = famCode [w.p] w.q
      rw [subst_ids]
      exact w.annotation_left
    annotation_right := by
      change Presentation.subst ids e'.2.1.code = famCode [w.p] w.q
      rw [subst_ids]
      exact w.annotation_right
    side_left := by
      change Presentation.subst ids e'.1.2.code = etaExp 1 (.var w.left)
      rw [subst_ids]
      exact w.side_left
    side_right := by
      change Presentation.subst ids e'.2.2.code = etaExp 1 (.var w.right)
      rw [subst_ids]
      exact w.side_right
    declared_left := dl
    declared_right := dr
    universe_p := w.universe_p
    universe_q := w.universe_q
    universe_pl := w.universe_pl
    universe_cl := ul
    universe_pr := w.universe_pr
    universe_cr := ur
    domain_left := w.domain_left
    domain_right := w.domain_right
    codomain_left := bl
    codomain_right := br }, rfl, rfl⟩

omit [DecidableEq Head] [DecidableRel S.R.cumulative] in
include algebra in
/-- **Lowering to the meet keeps compatibility within the groups.** -/
theorem meetComparable_lowered {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) (meets : Meets v)
    (group : Fin Θ.arity → Nat) (together : group v.left = group v.right)
    (comparable : MeetComparable S.R Θ.raw group) :
    MeetComparable S.R (setFamAt Θ.raw v.right [v.pr] v.cl) group := by
  have withMeet : ∀ j : Fin Θ.arity, j ≠ v.right → group j = group v.right → ∀ pj cj : Head,
      Ctx.lookup Θ.raw j = famCode [pj] cj → Compat S.R pj cj v.pr v.cl := by
    intro j ne grp pj cj declared
    by_cases hj : j = v.left
    · rw [hj] at declared
      obtain ⟨hp, hc⟩ := famCode_inj (declared.symm.trans v.declared_left)
      rw [(List.cons.inj hp).1, hc]
      exact .inr (.inl ⟨meets.1, S.levels.cumulative_refl v.universe_cl⟩)
    · have za := comparable j v.left hj (grp.trans together.symm) pj cj v.pl v.cl declared v.declared_left
      have zb := comparable j v.right ne grp pj cj v.pr v.cr declared v.declared_right
      exact Compat.meet algebra.trans za zb meets.1 meets.2.1 meets.2.2
  intro i j ne grp pi ci pj cj di dj
  by_cases hi : i = v.right
  · rw [hi] at di grp ne
    rw [lookup_setFamAt_self] at di
    obtain ⟨hp, hc⟩ := famCode_inj di
    rw [← (List.cons.inj hp).1, ← hc]
    have hj : j ≠ v.right := fun same => ne same.symm
    rw [lookup_setFamAt_ne Θ.raw v.right j [v.pr] v.cl hj] at dj
    exact (withMeet j hj grp.symm pj cj dj).symm
  · rw [lookup_setFamAt_ne Θ.raw v.right i [v.pr] v.cl hi] at di
    by_cases hj : j = v.right
    · rw [hj] at dj grp
      rw [lookup_setFamAt_self] at dj
      obtain ⟨hp, hc⟩ := famCode_inj dj
      rw [← (List.cons.inj hp).1, ← hc]
      exact withMeet i hi grp pi ci di
    · rw [lookup_setFamAt_ne Θ.raw v.right j [v.pr] v.cl hj] at dj
      exact comparable i j ne grp pi ci pj cj di dj

/-- **The true meet keeps the fragment.** -/
theorem inMeetFragment_meet {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) (meets : Meets v)
    (distinct : v.right ≠ v.left) (all : AllFamilies Θ) {rest : EquationStore (TotalTerm Θ)}
    (shapes : ∀ e' ∈ rest, Nonempty (FitFlex e')) (group : Fin Θ.arity → Nat)
    (grouped : ∀ e' ∈ rest, ∀ w : FitFlex e', group w.left = group w.right) (together : group v.left = group v.right)
    (comparable : MeetComparable S.R Θ.raw group) :
    InMeetFragment (contractStore algebra (meetFits v meets distinct) (lowered_families v meets all)
      ((frames S.levels).applyStore (lowerHom Θ v meets) rest)) := by
  refine inMeetFragment_raise algebra (meetFits v meets distinct) (lowered_families v meets all) ?_ group ?_
    together.symm (meetComparable_lowered algebra v meets group together comparable)
  · intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := shapes e' inRest
    obtain ⟨t, _, _⟩ := lower_view algebra v meets w
    exact ⟨t⟩
  · intro e'' member u
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := shapes e' inRest
    obtain ⟨t, tl, tr⟩ := lower_view algebra v meets w
    obtain ⟨ul, ur⟩ := FitFlex.unique u t
    rw [ul, ur, tl, tr]
    exact grouped e' inRest w

end Fragment

/-! ## The solver -/

section Solver

instance {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) [DecidableRel S.R.cumulative] :
    Decidable (Meets v) := by
  unfold Meets
  infer_instance

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **One step on a read equation**: delete, raise in either orientation, meet in either orientation, or stuck. -/
def stepMeetGroup {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ) (v : FitFlex e)
    (rest : EquationStore (TotalTerm Θ)) : Round S.levels storeRank (e :: rest) :=
  if hsame : v.left = v.right then
    .progress (deleteCodes e (v.annotation_left.trans v.annotation_right.symm)
        (by rw [v.side_left, v.side_right, hsame]) rest)
      (below_of_length (by
        show rest.length < (e :: rest).length
        simp))
  else if hb : S.R.cumulative v.pl v.pr ∧ S.R.cumulative v.cr v.cl then
    .progress (raiseContractUpdate algebra facts roots heads rigid complete
        (v.toFits (fun h => hsame h.symm) hb) all rest)
      (below_of_length (by
        show (contractStore algebra _ all rest).length < (e :: rest).length
        simp [contractStore]))
  else if hb' : S.R.cumulative v.pr v.pl ∧ S.R.cumulative v.cl v.cr then
    .progress ((raiseContractUpdate algebra facts roots heads rigid complete
        (v.swap.toFits hsame hb') all rest).rephrase (swap_equivalent e rest))
      (below_of_length (by
        show (contractStore algebra _ all rest).length < (e :: rest).length
        simp [contractStore]))
  else if hm : Meets v then
    .progress (trueMeetUpdate facts roots heads algebra rigid complete v hm (fun h => hsame h.symm) all rest)
      (below_of_length (by
        show (contractStore algebra _ _ ((frames S.levels).applyStore (lowerHom Θ v hm) rest)).length <
          (e :: rest).length
        simp [contractStore, Frames.applyStore]))
  else if hm' : Meets v.swap then
    .progress ((trueMeetUpdate facts roots heads algebra rigid complete v.swap hm' hsame all rest).rephrase
        (swap_equivalent e rest))
      (below_of_length (by
        show (contractStore algebra _ _ ((frames S.levels).applyStore (lowerHom Θ v.swap hm') rest)).length <
          (e :: rest).length
        simp [contractStore, Frames.applyStore]))
  else .stuck

/-- **The round of the solver**: read the first equation, then step. -/
def meetGroupRound : {Γ : Context S.R} → (problem : EquationStore (TotalTerm Γ)) → Round S.levels storeRank problem
  | _, [] => .stuck
  | Θ, e :: rest =>
      if hall : allFamiliesB Θ = true then
        match hd : readFitData e with
        | some _ => stepMeetGroup facts roots heads algebra rigid complete (allFamilies_of_B hall) (viewOfFit hd) rest
        | none => .stuck
      else .stuck

/-- **The tree's driver with delete, domain raising and the true meet.** -/
def meetGroupSolver : ContextualDependentWorklist.Solver S.levels where
  rank := storeRank
  round := meetGroupRound facts roots heads algebra rigid complete

omit [∀ head, Decidable (S.R.isUniverse head)] in
theorem stepMeetGroup_ne_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ)
    (v : FitFlex e) (rest : EquationStore (TotalTerm Θ))
    (decided : v.left = v.right ∨ (S.R.cumulative v.pl v.pr ∧ S.R.cumulative v.cr v.cl) ∨
      (S.R.cumulative v.pr v.pl ∧ S.R.cumulative v.cl v.cr) ∨ Meets v ∨ Meets v.swap) :
    stepMeetGroup facts roots heads algebra rigid complete all v rest ≠ .stuck := by
  unfold stepMeetGroup
  split_ifs with h1 h2 h3 h4 h5
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · rcases decided with h | h | h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact absurd h h3
    · exact absurd h h4
    · exact absurd h h5

omit [∀ head, Decidable (S.R.isUniverse head)] in
theorem stepMeetGroup_ne_refuted {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ)
    (v : FitFlex e) (rest : EquationStore (TotalTerm Θ)) (absent : ¬ (frames S.levels).Solvable (e :: rest)) :
    stepMeetGroup facts roots heads algebra rigid complete all v rest ≠ .refuted absent := by
  unfold stepMeetGroup
  split_ifs <;> intro h <;> cases h

/-- **The rules never refute.** -/
theorem meetGroupRound_ne_refuted {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ))
    (absent : ¬ (frames S.levels).Solvable problem) :
    meetGroupRound facts roots heads algebra rigid complete problem ≠ .refuted absent := by
  cases problem with
  | nil => intro h; cases h
  | cons e rest =>
      simp only [meetGroupRound]
      split_ifs with hall
      · split
        · exact stepMeetGroup_ne_refuted facts roots heads algebra rigid complete _ _ rest absent
        · intro h; cases h
      · intro h; cases h

/-- **Progress by shape**: on a nonempty store of the fragment of meet groups, the round is not stuck. -/
theorem meetGroupRound_ne_stuck {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (inside : InMeetFragment problem) (nonempty : problem ≠ []) :
    meetGroupRound facts roots heads algebra rigid complete problem ≠ .stuck := by
  cases problem with
  | nil => exact absurd rfl nonempty
  | cons e rest =>
      obtain ⟨v⟩ := inside.shapes e List.mem_cons_self
      obtain ⟨group, grouped, comparable⟩ := inside.grouped
      have hall := allFamiliesB_of inside.families
      have hd := readFitData_complete v
      simp only [meetGroupRound, dif_pos hall]
      split
      · rename_i d hd'
        apply stepMeetGroup_ne_stuck
        let w := viewOfFit hd'
        by_cases same : w.left = w.right
        · exact .inl same
        · rcases comparable w.left w.right same (grouped e List.mem_cons_self w) w.pl w.cl w.pr w.cr
            w.declared_left w.declared_right with c | c | c | c
          · exact .inr (.inr (.inl c))
          · exact .inr (.inl c)
          · exact .inr (.inr (.inr (.inl c)))
          · exact .inr (.inr (.inr (.inr c)))
      · rename_i hd'
        rw [hd] at hd'
        cases hd'

/-- **The rules keep the fragment.** -/
theorem meetGroupRound_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (storeRank update.remaining) (storeRank problem)}
    (inside : InMeetFragment problem)
    (progressed : meetGroupRound facts roots heads algebra rigid complete problem = .progress update smaller) :
    InMeetFragment update.remaining := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      obtain ⟨group, grouped, comparable⟩ := inside.grouped
      have restShapes : ∀ e' ∈ rest, Nonempty (FitFlex e') :=
        fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member)
      have restGrouped : ∀ e' ∈ rest, ∀ w : FitFlex e', group w.left = group w.right :=
        fun e' member => grouped e' (List.mem_cons_of_mem _ member)
      simp only [meetGroupRound] at progressed
      split_ifs at progressed with hall
      split at progressed
      · rename_i d hd
        unfold stepMeetGroup at progressed
        split_ifs at progressed with h1 h2 h3 h4 h5
        · cases progressed
          exact inMeetFragment_delete inside
        · cases progressed
          exact inMeetFragment_raise algebra _ (allFamilies_of_B hall) restShapes group restGrouped
            (grouped e List.mem_cons_self _).symm comparable
        · cases progressed
          exact inMeetFragment_raise algebra _ (allFamilies_of_B hall) restShapes group restGrouped
            (grouped e List.mem_cons_self _) comparable
        · cases progressed
          exact inMeetFragment_meet algebra (viewOfFit hd) h4 _ (allFamilies_of_B hall) restShapes group restGrouped
            (grouped e List.mem_cons_self _) comparable
        · cases progressed
          exact inMeetFragment_meet algebra (viewOfFit hd).swap h5 _ (allFamilies_of_B hall) restShapes group
            restGrouped (grouped e List.mem_cons_self _).symm comparable
      · cases progressed

/-- **The fragment of the solver.** -/
def meetGroupFragment :
    ContextualDependentWorklist.Fragment (meetGroupSolver facts roots heads algebra rigid complete) where
  holds := InMeetFragment
  stable := fun inside progressed => meetGroupRound_stable facts roots heads algebra rigid complete inside progressed
  decisive := fun inside nonempty => meetGroupRound_ne_stuck facts roots heads algebra rigid complete inside nonempty

include facts roots heads algebra rigid complete in
/-- **Decided by shape**: on the fragment of meet groups, the tree's driver with delete, domain raising and the true
meet reaches, at some budget and at every larger one, a principal answer or a certified refutation. -/
theorem meetGroup_decided {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InMeetFragment original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (meetGroupSolver facts roots heads algebra rigid complete) original larger =
          run (meetGroupSolver facts roots heads algebra rigid complete) original fuel ∧
        ((∃ state finished, run (meetGroupSolver facts roots heads algebra rigid complete) original larger =
              .solved state finished ∧ (frames S.levels).Principal original state.answer) ∨
          (∃ absent, run (meetGroupSolver facts roots heads algebra rigid complete) original larger =
            .refuted absent)) :=
  (meetGroupFragment facts roots heads algebra rigid complete).decided inside

include facts roots heads algebra rigid complete in
/-- **Every store of the fragment of meet groups has a principal answer.** -/
theorem principal_of_inMeetFragment {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InMeetFragment original) :
    ∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), (frames S.levels).Principal original answer := by
  obtain ⟨fuel, ends⟩ := meetGroup_decided facts roots heads algebra rigid complete inside
  rcases (ends fuel le_rfl).2 with ⟨state, _, _, principal⟩ | ⟨absent, refuted⟩
  · exact ⟨_, _, principal⟩
  · exact absurd refuted (drive_ne_refuted (meetGroupSolver facts roots heads algebra rigid complete)
      (fun problem absent => meetGroupRound_ne_refuted facts roots heads algebra rigid complete problem absent)
      fuel _ absent)

end Solver

/-! ## Membership, decided -/

section Membership

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- Of two different declared unary families, the views are compatible, decided. -/
def meetComparableB {n : Nat} (Γ : Ctx Head n) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    if i = j then true else
    match readFam (Ctx.lookup Γ i), readFam (Ctx.lookup Γ j) with
    | some a, some b =>
        match a.1, b.1 with
        | [pi], [pj] => decide (Compat S.R pi a.2 pj b.2)
        | _, _ => true
    | _, _ => true

omit [∀ head, Decidable (S.R.isUniverse head)] in
theorem meetComparable_of_B {n : Nat} {Γ : Ctx Head n} (h : meetComparableB (S := S) Γ = true) :
    MeetComparable S.R Γ (fun _ => 0) := by
  intro i j ne _ pi ci pj cj hi hj
  have hij := List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_finRange i)) j (List.mem_finRange j)
  rw [if_neg ne, hi, hj, readFam_famCode, readFam_famCode] at hij
  exact of_decide_eq_true hij

/-- **Membership in the fragment of meet groups, decided**, with all unknowns in one group. -/
def inMeetFragmentB {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Bool :=
  allFamiliesB Θ && problem.all (fun e => (readFitData e).isSome) && meetComparableB (S := S) Θ.raw

theorem inMeetFragment_of_B {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (h : inMeetFragmentB problem = true) : InMeetFragment problem := by
  simp only [inMeetFragmentB, Bool.and_eq_true] at h
  obtain ⟨⟨hall, hshapes⟩, hcomp⟩ := h
  refine ⟨allFamilies_of_B hall, fun e member => ?_, ⟨fun _ => 0, fun _ _ _ => rfl, meetComparable_of_B hcomp⟩⟩
  have he := List.all_eq_true.mp hshapes e member
  cases hd : readFitData e with
  | none => rw [hd] at he; cases he
  | some d => exact ⟨viewOfFit hd⟩

end Membership

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
