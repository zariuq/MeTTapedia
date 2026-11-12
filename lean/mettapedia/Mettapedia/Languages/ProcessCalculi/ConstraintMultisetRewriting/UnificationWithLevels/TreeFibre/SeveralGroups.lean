import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.SeveralRules
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MeetGroups

/-!
# Several parameters: progress by shape on meet groups of families

A solver of the tree's driver (`meetGroupSolverK`) for families of several parameters. It reads the first equation
`λ x̄. A x̄ ≐ λ x̄. B x̄` by its codes (`readFlexK`) and deletes it, raises in either orientation where one unknown
fits the other, takes the true meet in either orientation where the two meet, and is stuck otherwise.

**Compatible views** (`CompatK`), on lists of domains compared pointwise: one fits the other, or they meet (one has
the smaller domains and the smaller codomain, and every domain of the other lies below its codomain). **The
fragment** (`InMeetFragmentK`): every declaration is a universe family; every equation is a flex-flex equation of
families with several parameters (`FlexK`); and there is a grouping in which the two unknowns of every equation share
a group and any two different unknowns of a group have compatible views. With one parameter it is the fragment of
meet groups; it contains the fitting groups of several parameters.

* **The meet keeps compatibility** (`CompatK.meet`), by transitivity alone.
* Kept by every rule (`inMeetFragmentK_delete`, `inMeetFragmentK_raise`, `inMeetFragmentK_meet`); **progress by
  shape** (`meetGroupRoundK_ne_stuck`); decided (`meetGroupK_decided`); every store of the fragment has a principal
  answer (`principal_of_inMeetFragmentK`).
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

/-! ## Compatible views with several parameters -/

section Views

variable {R : Rules Head}

/-- **Two views `(p̄, c)` and `(p̄', c')` are compatible**: one fits the other, or one meets the other. -/
def CompatK (R : Rules Head) (ps : List Head) (c : Head) (ps' : List Head) (c' : Head) : Prop :=
  (List.Forall₂ R.cumulative ps' ps ∧ R.cumulative c c') ∨ (List.Forall₂ R.cumulative ps ps' ∧ R.cumulative c' c) ∨
    (List.Forall₂ R.cumulative ps ps' ∧ R.cumulative c c' ∧ ∀ p ∈ ps', R.cumulative p c) ∨
    (List.Forall₂ R.cumulative ps' ps ∧ R.cumulative c' c ∧ ∀ p ∈ ps, R.cumulative p c')

instance [DecidableRel R.cumulative] (ps : List Head) (c : Head) (ps' : List Head) (c' : Head) :
    Decidable (CompatK R ps c ps' c') := by
  unfold CompatK
  infer_instance

instance [∀ head, Decidable (R.isUniverse head)] (ps : List Head) : Decidable (AllUniverses R ps) := by
  unfold AllUniverses
  infer_instance

theorem CompatK.symm {ps : List Head} {c : Head} {ps' : List Head} {c' : Head} (h : CompatK R ps c ps' c') :
    CompatK R ps' c' ps c := by
  rcases h with h | h | h | h
  · exact .inr (.inl h)
  · exact .inl h
  · exact .inr (.inr (.inr h))
  · exact .inr (.inr (.inl h))

/-- **The meet keeps compatibility**: if `Z` is compatible with `A` and with `B`, and `A` meets `B` (so the meet is
`(p̄B, cA)`), then `Z` is compatible with the meet. -/
theorem CompatK.meet (trans : ∀ {u v w : Head}, R.cumulative u v → R.cumulative v w → R.cumulative u w)
    {psZ : List Head} {cZ : Head} {psA : List Head} {cA : Head} {psB : List Head} {cB : Head}
    (za : CompatK R psZ cZ psA cA) (zb : CompatK R psZ cZ psB cB)
    (dom : List.Forall₂ R.cumulative psA psB) (cod : R.cumulative cA cB) (cross : ∀ p ∈ psB, R.cumulative p cA) :
    CompatK R psZ cZ psB cA := by
  rcases zb with ⟨b1, _⟩ | ⟨b1, b2⟩ | ⟨b1, _, b3⟩ | ⟨b1, _, _⟩
  · rcases za with ⟨_, a2⟩ | ⟨a1, a2⟩ | ⟨_, a2, _⟩ | ⟨_, a2, a3⟩
    · exact .inl ⟨b1, a2⟩
    · exact .inr (.inl ⟨forall₂_trans trans a1 dom, a2⟩)
    · exact .inl ⟨b1, a2⟩
    · exact .inr (.inr (.inr ⟨b1, a2, a3⟩))
  · exact .inr (.inl ⟨b1, trans cod b2⟩)
  · rcases za with ⟨_, a2⟩ | ⟨_, a2⟩ | ⟨_, a2, _⟩ | ⟨_, a2, _⟩
    · exact .inr (.inr (.inl ⟨b1, a2, b3⟩))
    · exact .inr (.inl ⟨b1, a2⟩)
    · exact .inr (.inr (.inl ⟨b1, a2, b3⟩))
    · exact .inr (.inl ⟨b1, a2⟩)
  · rcases za with ⟨_, a2⟩ | ⟨a1, a2⟩ | ⟨_, a2, _⟩ | ⟨_, a2, a3⟩
    · exact .inl ⟨b1, a2⟩
    · exact .inr (.inr (.inr ⟨b1, a2, forall₂_below trans (forall₂_trans trans a1 dom) cross⟩))
    · exact .inl ⟨b1, a2⟩
    · exact .inr (.inr (.inr ⟨b1, a2, a3⟩))

end Views

/-! ## The fragment -/

section Fragment

/-- **Of two different unknowns in one group, the declared views are compatible.** -/
def MeetComparableK (R : Rules Head) {n : Nat} (Γ : Ctx Head n) (group : Fin n → Nat) : Prop :=
  ∀ i j : Fin n, i ≠ j → group i = group j → ∀ (psi : List Head) (ci : Head) (psj : List Head) (cj : Head),
    Ctx.lookup Γ i = famCode psi ci → Ctx.lookup Γ j = famCode psj cj → CompatK R psi ci psj cj

/-- **The fragment of meet groups with several parameters.** -/
structure InMeetFragmentK {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop where
  families : AllFamilies Θ
  shapes : ∀ e ∈ problem, Nonempty (FlexK e)
  grouped : ∃ group : Fin Θ.arity → Nat,
    (∀ e ∈ problem, ∀ v : FlexK e, group v.left = group v.right) ∧ MeetComparableK S.R Θ.raw group

theorem inMeetFragmentK_delete {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (inside : InMeetFragmentK (e :: rest)) : InMeetFragmentK rest := by
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
  exact ⟨inside.families, fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member),
    ⟨group, fun e' member => grouped e' (List.mem_cons_of_mem _ member), comparable⟩⟩

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  (algebra : CumulativeAlgebra S.R)

/-- A side `λ ȳ. G ȳ` at a fitting annotation is re-read as `λ ȳ. F ȳ`. -/
theorem contractSideK_reread {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (fits : v.Fits)
    (all : AllFamilies Θ) {side : TotalTerm Θ} {ps' : List Head} {q' : Head} (h : RereadsK v side ps' q') :
    (contractSideK algebra v fits all side).1 = side.1 ∧
      (contractSideK algebra v fits all side).2.code = etaExp ps'.length (.var v.right) := by
  have candidate : readFam side.1.code = some (ps', q') := by rw [h.1, readFam_famCode]
  have same : contractSideK algebra v fits all side = ⟨side.1, rereadTermK algebra v fits side h⟩ := by
    unfold contractSideK
    rw [candidate]
    exact dif_pos h
  have first := congrArg (fun s : TotalTerm Θ => s.1) same
  have second := congrArg (fun s : TotalTerm Θ => s.2.code) same
  exact ⟨first, second⟩

/-- Any other side is instantiated, and keeps its codes when it does not mention `G`. -/
theorem contractSideK_keep {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (fits : v.Fits)
    (all : AllFamilies Θ) {side : TotalTerm Θ} {Z : Fin Θ.arity} {ps' : List Head} {q' : Head}
    (annotation : side.1.code = famCode ps' q') (code : side.2.code = etaExp ps'.length (.var Z)) (ne : Z ≠ v.left) :
    (contractSideK algebra v fits all side).1.code = famCode ps' q' ∧
      (contractSideK algebra v fits all side).2.code = etaExp ps'.length (.var Z) := by
  have notReread : ∀ ps'' q'', ¬ RereadsK v side ps'' q'' := by
    intro ps'' q'' h
    obtain ⟨hps, _⟩ := famCode_inj (h.1.symm.trans annotation)
    have codes := code.symm.trans h.2.1
    rw [hps] at codes
    exact ne (Tm.var.inj (etaExp_inj _ codes))
  rcases contractSideK_cases algebra v fits all side with ⟨ps'', q'', h, _⟩ | same
  · exact absurd h (notReread ps'' q'')
  · rw [same]
    constructor
    · change Presentation.subst (raiseKSub v.psl.length v.right v.left) side.1.code = _
      rw [annotation, famCode_subst]
    · change Presentation.subst (raiseKSub v.psl.length v.right v.left) side.2.code = _
      rw [code, subst_etaExp]
      change etaExp ps'.length (raiseKSub v.psl.length v.right v.left Z) = _
      rw [raiseKSub_ne _ _ _ ne]

/-- **The view of an equation, after domain raising and re-reading.** -/
theorem contract_viewK {Θ : Context S.R} {e e' : Equation (TotalTerm Θ)} (v : FlexK e) (fits : v.Fits)
    (all : AllFamilies Θ) (w : FlexK e') :
    ∃ t : FlexK ((contractSideK algebra v fits all e'.1, contractSideK algebra v fits all e'.2) :
        Equation (TotalTerm Θ)),
      t.left = raiseVar v.right v.left w.left ∧ t.right = raiseVar v.right v.left w.right := by
  have side : ∀ (s : TotalTerm Θ) (Z : Fin Θ.arity) (psZ : List Head) (cZ : Head),
      s.1.code = famCode w.ps w.q → s.2.code = etaExp w.ps.length (.var Z) → Ctx.lookup Θ.raw Z = famCode psZ cZ →
      AllUniverses S.R psZ → S.R.isUniverse cZ → List.Forall₂ S.R.cumulative w.ps psZ → S.R.cumulative cZ w.q →
      ∃ (psZ' : List Head) (cZ' : Head), (contractSideK algebra v fits all s).1.code = famCode w.ps w.q ∧
        (contractSideK algebra v fits all s).2.code = etaExp w.ps.length (.var (raiseVar v.right v.left Z)) ∧
        Ctx.lookup Θ.raw (raiseVar v.right v.left Z) = famCode psZ' cZ' ∧ AllUniverses S.R psZ' ∧
        S.R.isUniverse cZ' ∧ List.Forall₂ S.R.cumulative w.ps psZ' ∧ S.R.cumulative cZ' w.q := by
    intro s Z psZ cZ annotation code declared upsZ ucZ domain codomain
    by_cases hZ : Z = v.left
    · rw [hZ] at declared code
      obtain ⟨hps, hc⟩ := famCode_inj (declared.symm.trans v.declared_left)
      rw [hps] at domain
      rw [hc] at codomain
      have rereads : RereadsK v s w.ps w.q := ⟨annotation, code, w.universes, w.universe_q, domain, codomain⟩
      obtain ⟨same1, same2⟩ := contractSideK_reread algebra v fits all rereads
      refine ⟨v.psr, v.cr, by rw [same1]; exact annotation, ?_, ?_, v.universes_right, v.universe_cr,
        forall₂_trans algebra.trans domain fits.1, algebra.trans fits.2 codomain⟩
      · rw [same2, hZ]
        unfold raiseVar
        rw [if_pos rfl]
      · rw [hZ]
        unfold raiseVar
        rw [if_pos rfl]
        exact v.declared_right
    · obtain ⟨same1, same2⟩ := contractSideK_keep algebra v fits all annotation code hZ
      refine ⟨psZ, cZ, same1, ?_, ?_, upsZ, ucZ, domain, codomain⟩
      · rw [same2]
        unfold raiseVar
        rw [if_neg hZ]
      · unfold raiseVar
        rw [if_neg hZ]
        exact declared
  obtain ⟨psl', cl', a1, s1, d1, upl, ucl, dl, cl⟩ := side e'.1 w.left w.psl w.cl w.annotation_left w.side_left
    w.declared_left w.universes_left w.universe_cl w.domain_left w.codomain_left
  obtain ⟨psr', cr', a2, s2, d2, upr, ucr, dr, cr⟩ := side e'.2 w.right w.psr w.cr w.annotation_right w.side_right
    w.declared_right w.universes_right w.universe_cr w.domain_right w.codomain_right
  exact ⟨{
    ps := w.ps
    q := w.q
    left := raiseVar v.right v.left w.left
    right := raiseVar v.right v.left w.right
    psl := psl'
    cl := cl'
    psr := psr'
    cr := cr'
    annotation_left := a1
    annotation_right := a2
    side_left := s1
    side_right := s2
    declared_left := d1
    declared_right := d2
    universes := w.universes
    universes_left := upl
    universes_right := upr
    universe_q := w.universe_q
    universe_cl := ucl
    universe_cr := ucr
    domain_left := dl
    domain_right := dr
    codomain_left := cl
    codomain_right := cr }, rfl, rfl⟩

/-- **Domain raising keeps the fragment.** -/
theorem inMeetFragmentK_raise {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (fits : v.Fits)
    (all : AllFamilies Θ) {rest : EquationStore (TotalTerm Θ)} (shapes : ∀ e' ∈ rest, Nonempty (FlexK e'))
    (group : Fin Θ.arity → Nat) (grouped : ∀ e' ∈ rest, ∀ w : FlexK e', group w.left = group w.right)
    (together : group v.right = group v.left) (comparable : MeetComparableK S.R Θ.raw group) :
    InMeetFragmentK (contractStoreK algebra v fits all rest) := by
  have keep : ∀ X, group (raiseVar v.right v.left X) = group X := by
    intro X
    unfold raiseVar
    split_ifs with h
    · rw [h, together]
    · rfl
  refine ⟨all, ?_, ⟨group, ?_, comparable⟩⟩
  · intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := shapes e' inRest
    obtain ⟨t, _, _⟩ := contract_viewK algebra v fits all w
    exact ⟨t⟩
  · intro e'' member u
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := shapes e' inRest
    obtain ⟨t, tl, tr⟩ := contract_viewK algebra v fits all w
    obtain ⟨ul, ur⟩ := FlexK.unique u t
    rw [ul, ur, tl, tr, keep, keep]
    exact grouped e' inRest w

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
include algebra in
/-- **The view of an equation over the lowered telescope.** -/
theorem lower_viewK {Θ : Context S.R} {e e' : Equation (TotalTerm Θ)} (v : FlexK e) (meets : v.Meets)
    (w : FlexK e') :
    ∃ t : FlexK (((frames S.levels).act (lowerKHom Θ v meets) e'.1,
        (frames S.levels).act (lowerKHom Θ v meets) e'.2) : Equation (TotalTerm (loweredK Θ v meets))),
      t.left = w.left ∧ t.right = w.right := by
  have side : ∀ (Z : Fin Θ.arity) (psZ : List Head) (cZ : Head), Ctx.lookup Θ.raw Z = famCode psZ cZ →
      S.R.isUniverse cZ → S.R.cumulative cZ w.q → ∃ cZ', Ctx.lookup (setFamAt Θ.raw v.right v.psr v.cl) Z =
        famCode psZ cZ' ∧ S.R.isUniverse cZ' ∧ S.R.cumulative cZ' w.q := by
    intro Z psZ cZ declared hc below
    by_cases hZ : Z = v.right
    · rw [hZ] at declared ⊢
      obtain ⟨hps, hcZ⟩ := famCode_inj (declared.symm.trans v.declared_right)
      refine ⟨v.cl, ?_, v.universe_cl, algebra.trans meets.2.1 (by rw [← hcZ]; exact below)⟩
      rw [lookup_setFamAt_self, hps]
    · exact ⟨cZ, by rw [lookup_setFamAt_ne Θ.raw v.right Z v.psr v.cl hZ]; exact declared, hc, below⟩
  obtain ⟨cl', dl, ul, bl⟩ := side w.left w.psl w.cl w.declared_left w.universe_cl w.codomain_left
  obtain ⟨cr', dr, ur, br⟩ := side w.right w.psr w.cr w.declared_right w.universe_cr w.codomain_right
  exact ⟨{
    ps := w.ps
    q := w.q
    left := w.left
    right := w.right
    psl := w.psl
    cl := cl'
    psr := w.psr
    cr := cr'
    annotation_left := by
      change Presentation.subst ids e'.1.1.code = famCode w.ps w.q
      rw [subst_ids]
      exact w.annotation_left
    annotation_right := by
      change Presentation.subst ids e'.2.1.code = famCode w.ps w.q
      rw [subst_ids]
      exact w.annotation_right
    side_left := by
      change Presentation.subst ids e'.1.2.code = etaExp w.ps.length (.var w.left)
      rw [subst_ids]
      exact w.side_left
    side_right := by
      change Presentation.subst ids e'.2.2.code = etaExp w.ps.length (.var w.right)
      rw [subst_ids]
      exact w.side_right
    declared_left := dl
    declared_right := dr
    universes := w.universes
    universes_left := w.universes_left
    universes_right := w.universes_right
    universe_q := w.universe_q
    universe_cl := ul
    universe_cr := ur
    domain_left := w.domain_left
    domain_right := w.domain_right
    codomain_left := bl
    codomain_right := br }, rfl, rfl⟩

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
include algebra in
/-- **Lowering to the meet keeps compatibility within the groups.** -/
theorem meetComparableK_lowered {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (meets : v.Meets)
    (group : Fin Θ.arity → Nat) (together : group v.left = group v.right)
    (comparable : MeetComparableK S.R Θ.raw group) :
    MeetComparableK S.R (setFamAt Θ.raw v.right v.psr v.cl) group := by
  have withMeet : ∀ j : Fin Θ.arity, j ≠ v.right → group j = group v.right → ∀ (psj : List Head) (cj : Head),
      Ctx.lookup Θ.raw j = famCode psj cj → CompatK S.R psj cj v.psr v.cl := by
    intro j ne grp psj cj declared
    by_cases hj : j = v.left
    · rw [hj] at declared
      obtain ⟨hp, hc⟩ := famCode_inj (declared.symm.trans v.declared_left)
      rw [hp, hc]
      exact .inr (.inl ⟨meets.1, S.levels.cumulative_refl v.universe_cl⟩)
    · have za := comparable j v.left hj (grp.trans together.symm) psj cj v.psl v.cl declared v.declared_left
      have zb := comparable j v.right ne grp psj cj v.psr v.cr declared v.declared_right
      exact CompatK.meet algebra.trans za zb meets.1 meets.2.1 meets.2.2
  intro i j ne grp psi ci psj cj di dj
  by_cases hi : i = v.right
  · rw [hi] at di grp ne
    rw [lookup_setFamAt_self] at di
    obtain ⟨hp, hc⟩ := famCode_inj di
    rw [← hp, ← hc]
    have hj : j ≠ v.right := fun same => ne same.symm
    rw [lookup_setFamAt_ne Θ.raw v.right j v.psr v.cl hj] at dj
    exact (withMeet j hj grp.symm psj cj dj).symm
  · rw [lookup_setFamAt_ne Θ.raw v.right i v.psr v.cl hi] at di
    by_cases hj : j = v.right
    · rw [hj] at dj grp
      rw [lookup_setFamAt_self] at dj
      obtain ⟨hp, hc⟩ := famCode_inj dj
      rw [← hp, ← hc]
      exact withMeet i hi grp psi ci di
    · rw [lookup_setFamAt_ne Θ.raw v.right j v.psr v.cl hj] at dj
      exact comparable i j ne grp psi ci psj cj di dj

/-- **The true meet keeps the fragment.** -/
theorem inMeetFragmentK_meet {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (meets : v.Meets)
    (distinct : v.right ≠ v.left) (all : AllFamilies Θ) {rest : EquationStore (TotalTerm Θ)}
    (shapes : ∀ e' ∈ rest, Nonempty (FlexK e')) (group : Fin Θ.arity → Nat)
    (grouped : ∀ e' ∈ rest, ∀ w : FlexK e', group w.left = group w.right) (together : group v.left = group v.right)
    (comparable : MeetComparableK S.R Θ.raw group) :
    InMeetFragmentK (contractStoreK algebra (meetViewK v meets distinct) (meetViewK_fits v meets distinct)
      (loweredK_families v meets all) ((frames S.levels).applyStore (lowerKHom Θ v meets) rest)) := by
  refine inMeetFragmentK_raise algebra (meetViewK v meets distinct) (meetViewK_fits v meets distinct)
    (loweredK_families v meets all) ?_ group ?_ together.symm (meetComparableK_lowered algebra v meets group together
      comparable)
  · intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := shapes e' inRest
    obtain ⟨t, _, _⟩ := lower_viewK algebra v meets w
    exact ⟨t⟩
  · intro e'' member u
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := shapes e' inRest
    obtain ⟨t, tl, tr⟩ := lower_viewK algebra v meets w
    obtain ⟨ul, ur⟩ := FlexK.unique u t
    rw [ul, ur, tl, tr]
    exact grouped e' inRest w

end Fragment

/-! ## Reading -/

section Reading

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- The data of a flex-flex reading with several parameters. -/
structure FlexKData (Head : Type) (n : Nat) where
  ps : List Head
  q : Head
  left : Fin n
  right : Fin n
  psl : List Head
  cl : Head
  psr : List Head
  cr : Head

/-- **Read a flex-flex equation of families with several parameters** off its codes. -/
def readFlexK {Θ : Context S.R} (e : Equation (TotalTerm Θ)) : Option (FlexKData Head Θ.arity) :=
  (readFam e.1.1.code).bind fun a =>
  (readFam e.2.1.code).bind fun b =>
  (readEta a.1.length e.1.2.code).bind fun A =>
  (readEta a.1.length e.2.2.code).bind fun B =>
  (readFam (Ctx.lookup Θ.raw A)).bind fun dA =>
  (readFam (Ctx.lookup Θ.raw B)).bind fun dB =>
  if b = a ∧ AllUniverses S.R a.1 ∧ AllUniverses S.R dA.1 ∧ AllUniverses S.R dB.1 ∧ S.R.isUniverse a.2 ∧
      S.R.isUniverse dA.2 ∧ S.R.isUniverse dB.2 ∧ List.Forall₂ S.R.cumulative a.1 dA.1 ∧
      List.Forall₂ S.R.cumulative a.1 dB.1 ∧ S.R.cumulative dA.2 a.2 ∧ S.R.cumulative dB.2 a.2 then
    some ⟨a.1, a.2, A, B, dA.1, dA.2, dB.1, dB.2⟩
  else none

/-- **The reader reads every flex-flex equation of families with several parameters.** -/
theorem readFlexK_complete {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) :
    readFlexK e = some ⟨v.ps, v.q, v.left, v.right, v.psl, v.cl, v.psr, v.cr⟩ := by
  unfold readFlexK
  rw [v.annotation_left, v.annotation_right, readFam_famCode, v.side_left, v.side_right]
  simp [-famCode_cons, -famCode_nil, readEta_etaExp, v.declared_left, v.declared_right, readFam_famCode,
    v.universes, v.universes_left, v.universes_right, v.universe_q, v.universe_cl, v.universe_cr, v.domain_left,
    v.domain_right, v.codomain_left, v.codomain_right]

/-- What a successful reading says. -/
theorem readFlexK_sound {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {d : FlexKData Head Θ.arity}
    (h : readFlexK e = some d) :
    e.1.1.code = famCode d.ps d.q ∧ e.2.1.code = famCode d.ps d.q ∧
      e.1.2.code = etaExp d.ps.length (.var d.left) ∧ e.2.2.code = etaExp d.ps.length (.var d.right) ∧
      Ctx.lookup Θ.raw d.left = famCode d.psl d.cl ∧ Ctx.lookup Θ.raw d.right = famCode d.psr d.cr ∧
      AllUniverses S.R d.ps ∧ AllUniverses S.R d.psl ∧ AllUniverses S.R d.psr ∧ S.R.isUniverse d.q ∧
      S.R.isUniverse d.cl ∧ S.R.isUniverse d.cr ∧ List.Forall₂ S.R.cumulative d.ps d.psl ∧
      List.Forall₂ S.R.cumulative d.ps d.psr ∧ S.R.cumulative d.cl d.q ∧ S.R.cumulative d.cr d.q := by
  unfold readFlexK at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, A, hA, B, hB, dA, hdA, dB, hdB, h⟩ := h
  split_ifs at h with hc
  cases h
  obtain ⟨rfl, ua, uA, uB, uq, ucA, ucB, domA, domB, codA, codB⟩ := hc
  exact ⟨readFam_sound ha, readFam_sound hb, readEta_sound hA, readEta_sound hB, readFam_sound hdA,
    readFam_sound hdB, ua, uA, uB, uq, ucA, ucB, domA, domB, codA, codB⟩

/-- The view of a successful reading. -/
def viewOfK {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {d : FlexKData Head Θ.arity} (h : readFlexK e = some d) :
    FlexK e where
  ps := d.ps
  q := d.q
  left := d.left
  right := d.right
  psl := d.psl
  cl := d.cl
  psr := d.psr
  cr := d.cr
  annotation_left := (readFlexK_sound h).1
  annotation_right := (readFlexK_sound h).2.1
  side_left := (readFlexK_sound h).2.2.1
  side_right := (readFlexK_sound h).2.2.2.1
  declared_left := (readFlexK_sound h).2.2.2.2.1
  declared_right := (readFlexK_sound h).2.2.2.2.2.1
  universes := (readFlexK_sound h).2.2.2.2.2.2.1
  universes_left := (readFlexK_sound h).2.2.2.2.2.2.2.1
  universes_right := (readFlexK_sound h).2.2.2.2.2.2.2.2.1
  universe_q := (readFlexK_sound h).2.2.2.2.2.2.2.2.2.1
  universe_cl := (readFlexK_sound h).2.2.2.2.2.2.2.2.2.2.1
  universe_cr := (readFlexK_sound h).2.2.2.2.2.2.2.2.2.2.2.1
  domain_left := (readFlexK_sound h).2.2.2.2.2.2.2.2.2.2.2.2.1
  domain_right := (readFlexK_sound h).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  codomain_left := (readFlexK_sound h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  codomain_right := (readFlexK_sound h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Reading

/-! ## The solver -/

section Solver

instance {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) [DecidableRel S.R.cumulative] :
    Decidable v.Fits := by
  unfold FlexK.Fits
  infer_instance

instance {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) [DecidableRel S.R.cumulative] :
    Decidable v.Meets := by
  unfold FlexK.Meets
  infer_instance

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **One step on a read equation**: delete, raise in either orientation, meet in either orientation, or stuck. -/
def stepMeetGroupK {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ) (v : FlexK e)
    (rest : EquationStore (TotalTerm Θ)) : Round S.levels storeRank (e :: rest) :=
  if hsame : v.left = v.right then
    .progress (deleteCodes e (v.annotation_left.trans v.annotation_right.symm)
        (by rw [v.side_left, v.side_right, hsame]) rest)
      (below_of_length (by
        show rest.length < (e :: rest).length
        simp))
  else if hb : v.Fits then
    .progress (raiseContractKUpdate algebra facts roots heads rigid complete v hb (fun h => hsame h.symm) all rest)
      (below_of_length (by
        show (contractStoreK algebra v hb all rest).length < (e :: rest).length
        simp [contractStoreK]))
  else if hb' : v.swap.Fits then
    .progress ((raiseContractKUpdate algebra facts roots heads rigid complete v.swap hb' hsame all rest).rephrase
        (swap_equivalent e rest))
      (below_of_length (by
        show (contractStoreK algebra v.swap hb' all rest).length < (e :: rest).length
        simp [contractStoreK]))
  else if hm : v.Meets then
    .progress (trueMeetKUpdate facts roots heads algebra rigid complete v hm (fun h => hsame h.symm) all rest)
      (below_of_length (by
        show (contractStoreK algebra _ _ _ ((frames S.levels).applyStore (lowerKHom Θ v hm) rest)).length <
          (e :: rest).length
        simp [contractStoreK, Frames.applyStore]))
  else if hm' : v.swap.Meets then
    .progress ((trueMeetKUpdate facts roots heads algebra rigid complete v.swap hm' hsame all rest).rephrase
        (swap_equivalent e rest))
      (below_of_length (by
        show (contractStoreK algebra _ _ _ ((frames S.levels).applyStore (lowerKHom Θ v.swap hm') rest)).length <
          (e :: rest).length
        simp [contractStoreK, Frames.applyStore]))
  else .stuck

/-- **The round of the solver**: read the first equation, then step. -/
def meetGroupRoundK : {Γ : Context S.R} → (problem : EquationStore (TotalTerm Γ)) → Round S.levels storeRank problem
  | _, [] => .stuck
  | Θ, e :: rest =>
      if hall : allFamiliesB Θ = true then
        match hd : readFlexK e with
        | some _ => stepMeetGroupK facts roots heads algebra rigid complete (allFamilies_of_B hall) (viewOfK hd) rest
        | none => .stuck
      else .stuck

/-- **The tree's driver with delete, domain raising and the true meet, for several parameters.** -/
def meetGroupSolverK : ContextualDependentWorklist.Solver S.levels where
  rank := storeRank
  round := meetGroupRoundK facts roots heads algebra rigid complete

theorem stepMeetGroupK_ne_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ)
    (v : FlexK e) (rest : EquationStore (TotalTerm Θ))
    (decided : v.left = v.right ∨ v.Fits ∨ v.swap.Fits ∨ v.Meets ∨ v.swap.Meets) :
    stepMeetGroupK facts roots heads algebra rigid complete all v rest ≠ .stuck := by
  unfold stepMeetGroupK
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

theorem stepMeetGroupK_ne_refuted {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ)
    (v : FlexK e) (rest : EquationStore (TotalTerm Θ)) (absent : ¬ (frames S.levels).Solvable (e :: rest)) :
    stepMeetGroupK facts roots heads algebra rigid complete all v rest ≠ .refuted absent := by
  unfold stepMeetGroupK
  split_ifs <;> intro h <;> cases h

/-- **The rules never refute.** -/
theorem meetGroupRoundK_ne_refuted {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ))
    (absent : ¬ (frames S.levels).Solvable problem) :
    meetGroupRoundK facts roots heads algebra rigid complete problem ≠ .refuted absent := by
  cases problem with
  | nil => intro h; cases h
  | cons e rest =>
      simp only [meetGroupRoundK]
      split_ifs with hall
      · split
        · exact stepMeetGroupK_ne_refuted facts roots heads algebra rigid complete _ _ rest absent
        · intro h; cases h
      · intro h; cases h

/-- **Progress by shape**: on a nonempty store of the fragment, the round is not stuck. -/
theorem meetGroupRoundK_ne_stuck {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (inside : InMeetFragmentK problem) (nonempty : problem ≠ []) :
    meetGroupRoundK facts roots heads algebra rigid complete problem ≠ .stuck := by
  cases problem with
  | nil => exact absurd rfl nonempty
  | cons e rest =>
      obtain ⟨v⟩ := inside.shapes e List.mem_cons_self
      obtain ⟨group, grouped, comparable⟩ := inside.grouped
      have hall := allFamiliesB_of inside.families
      have hd := readFlexK_complete v
      simp only [meetGroupRoundK, dif_pos hall]
      split
      · rename_i d hd'
        apply stepMeetGroupK_ne_stuck
        let w := viewOfK hd'
        by_cases same : w.left = w.right
        · exact .inl same
        · rcases comparable w.left w.right same (grouped e List.mem_cons_self w) w.psl w.cl w.psr w.cr
            w.declared_left w.declared_right with c | c | c | c
          · exact .inr (.inr (.inl c))
          · exact .inr (.inl c)
          · exact .inr (.inr (.inr (.inl c)))
          · exact .inr (.inr (.inr (.inr c)))
      · rename_i hd'
        rw [hd] at hd'
        cases hd'

/-- **The rules keep the fragment.** -/
theorem meetGroupRoundK_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (storeRank update.remaining) (storeRank problem)}
    (inside : InMeetFragmentK problem)
    (progressed : meetGroupRoundK facts roots heads algebra rigid complete problem = .progress update smaller) :
    InMeetFragmentK update.remaining := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      obtain ⟨group, grouped, comparable⟩ := inside.grouped
      have restShapes : ∀ e' ∈ rest, Nonempty (FlexK e') :=
        fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member)
      have restGrouped : ∀ e' ∈ rest, ∀ w : FlexK e', group w.left = group w.right :=
        fun e' member => grouped e' (List.mem_cons_of_mem _ member)
      simp only [meetGroupRoundK] at progressed
      split_ifs at progressed with hall
      split at progressed
      · rename_i d hd
        unfold stepMeetGroupK at progressed
        split_ifs at progressed with h1 h2 h3 h4 h5
        · cases progressed
          exact inMeetFragmentK_delete inside
        · cases progressed
          exact inMeetFragmentK_raise algebra _ h2 (allFamilies_of_B hall) restShapes group restGrouped
            (grouped e List.mem_cons_self _).symm comparable
        · cases progressed
          exact inMeetFragmentK_raise algebra _ h3 (allFamilies_of_B hall) restShapes group restGrouped
            (grouped e List.mem_cons_self _) comparable
        · cases progressed
          exact inMeetFragmentK_meet algebra (viewOfK hd) h4 _ (allFamilies_of_B hall) restShapes group
            restGrouped (grouped e List.mem_cons_self _) comparable
        · cases progressed
          exact inMeetFragmentK_meet algebra (viewOfK hd).swap h5 _ (allFamilies_of_B hall) restShapes group
            restGrouped (grouped e List.mem_cons_self _).symm comparable
      · cases progressed

/-- **The fragment of the solver.** -/
def meetGroupFragmentK :
    ContextualDependentWorklist.Fragment (meetGroupSolverK facts roots heads algebra rigid complete) where
  holds := InMeetFragmentK
  stable := fun inside progressed => meetGroupRoundK_stable facts roots heads algebra rigid complete inside progressed
  decisive := fun inside nonempty => meetGroupRoundK_ne_stuck facts roots heads algebra rigid complete inside nonempty

include facts roots heads algebra rigid complete in
/-- **Decided by shape, with several parameters**: on the fragment of meet groups, the tree's driver reaches, at some
budget and at every larger one, a principal answer or a certified refutation. -/
theorem meetGroupK_decided {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InMeetFragmentK original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (meetGroupSolverK facts roots heads algebra rigid complete) original larger =
          run (meetGroupSolverK facts roots heads algebra rigid complete) original fuel ∧
        ((∃ state finished, run (meetGroupSolverK facts roots heads algebra rigid complete) original larger =
              .solved state finished ∧ (frames S.levels).Principal original state.answer) ∨
          (∃ absent, run (meetGroupSolverK facts roots heads algebra rigid complete) original larger =
            .refuted absent)) :=
  (meetGroupFragmentK facts roots heads algebra rigid complete).decided inside

include facts roots heads algebra rigid complete in
/-- **Every store of the fragment has a principal answer.** -/
theorem principal_of_inMeetFragmentK {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InMeetFragmentK original) :
    ∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), (frames S.levels).Principal original answer := by
  obtain ⟨fuel, ends⟩ := meetGroupK_decided facts roots heads algebra rigid complete inside
  rcases (ends fuel le_rfl).2 with ⟨state, _, _, principal⟩ | ⟨absent, refuted⟩
  · exact ⟨_, _, principal⟩
  · exact absurd refuted (drive_ne_refuted (meetGroupSolverK facts roots heads algebra rigid complete)
      (fun problem absent => meetGroupRoundK_ne_refuted facts roots heads algebra rigid complete problem absent)
      fuel _ absent)

end Solver

/-! ## Membership, decided -/

section Membership

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- Of two different declared families, the views are compatible, decided. -/
def meetComparableKB {n : Nat} (Γ : Ctx Head n) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    if i = j then true else
    match readFam (Ctx.lookup Γ i), readFam (Ctx.lookup Γ j) with
    | some a, some b => decide (CompatK S.R a.1 a.2 b.1 b.2)
    | _, _ => true

omit [∀ head, Decidable (S.R.isUniverse head)] in
theorem meetComparableK_of_B {n : Nat} {Γ : Ctx Head n} (h : meetComparableKB (S := S) Γ = true) :
    MeetComparableK S.R Γ (fun _ => 0) := by
  intro i j ne _ psi ci psj cj hi hj
  have hij := List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_finRange i)) j (List.mem_finRange j)
  rw [if_neg ne, hi, hj, readFam_famCode, readFam_famCode] at hij
  exact of_decide_eq_true hij

/-- **Membership in the fragment with several parameters, decided**, with all unknowns in one group. -/
def inMeetFragmentKB {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Bool :=
  allFamiliesB Θ && problem.all (fun e => (readFlexK e).isSome) && meetComparableKB (S := S) Θ.raw

theorem inMeetFragmentK_of_B {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (h : inMeetFragmentKB problem = true) : InMeetFragmentK problem := by
  simp only [inMeetFragmentKB, Bool.and_eq_true] at h
  obtain ⟨⟨hall, hshapes⟩, hcomp⟩ := h
  refine ⟨allFamilies_of_B hall, fun e member => ?_, ⟨fun _ => 0, fun _ _ _ => rfl, meetComparableK_of_B hcomp⟩⟩
  have he := List.all_eq_true.mp hshapes e member
  cases hd : readFlexK e with
  | none => rw [hd] at he; cases he
  | some d => exact ⟨viewOfK hd⟩

end Membership

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
