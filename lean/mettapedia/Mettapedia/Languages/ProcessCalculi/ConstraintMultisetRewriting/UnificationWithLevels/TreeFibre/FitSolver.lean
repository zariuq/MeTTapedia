import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.RaiseContract

/-!
# The tree's driver with delete and domain raising: progress by shape where the meet is a declaration

A solver of the tree's worklist driver (`fitSolver`) for unary families. It reads the first equation
`λ x. A x ≐ λ x. B x` at `Π (x : U_p). U_q` by its codes (`readFitData`), and

* deletes it when `A` and `B` are one unknown;
* raises `A := λ x. B x` when `B` fits `A` (it takes `A`'s arguments and returns into `A`'s codomain), or raises
  `B := λ x. A x` when `A` fits `B`, re-reading the other equations (`raiseContractUpdate`);
* is stuck otherwise.

**The fragment** (`InFitFragment`): every declaration is a universe family; every equation is a unary flex-flex
equation of families (`FitFlex`), its annotation's domain below both declared domains and both declared codomains
below its codomain; and there is a grouping in which the two unknowns of every equation share a group and, within a
group, of two different unknowns one fits the other. It is the tree's form of the compatible groups of the codes
model, where the meet of two compatible views is one of them. Two declarations over different domains are allowed:
that is the shape of the cross store, which lies outside only because neither of its unknowns fits the other.

* Kept by every rule (`inFitFragment_delete`, `inFitFragment_raise`); progress by shape (`fitRound_ne_stuck`);
  decided (`fit_decided`), and every store of the fragment has a principal answer (`principal_of_inFitFragment`).
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

/-! ## Unary flex-flex equations of families -/

/-- **A unary flex-flex equation of families**: `λ x. A x ≐ λ x. B x` at `Π (x : U_p). U_q`, with
`A : Π (x : U_{pl}). U_{cl}`, `B : Π (x : U_{pr}). U_{cr}`, `p` below both domains and both codomains below `q`. -/
structure FitFlex {Θ : Context S.R} (e : Equation (TotalTerm Θ)) where
  p : Head
  q : Head
  left : Fin Θ.arity
  right : Fin Θ.arity
  pl : Head
  cl : Head
  pr : Head
  cr : Head
  annotation_left : e.1.1.code = famCode [p] q
  annotation_right : e.2.1.code = famCode [p] q
  side_left : e.1.2.code = etaExp 1 (.var left)
  side_right : e.2.2.code = etaExp 1 (.var right)
  declared_left : Ctx.lookup Θ.raw left = famCode [pl] cl
  declared_right : Ctx.lookup Θ.raw right = famCode [pr] cr
  universe_p : S.R.isUniverse p
  universe_q : S.R.isUniverse q
  universe_pl : S.R.isUniverse pl
  universe_cl : S.R.isUniverse cl
  universe_pr : S.R.isUniverse pr
  universe_cr : S.R.isUniverse cr
  domain_left : S.R.cumulative p pl
  domain_right : S.R.cumulative p pr
  codomain_left : S.R.cumulative cl q
  codomain_right : S.R.cumulative cr q

/-- The view of the swapped equation. -/
def FitFlex.swap {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) :
    FitFlex ((e.2, e.1) : Equation (TotalTerm Θ)) where
  p := v.p
  q := v.q
  left := v.right
  right := v.left
  pl := v.pr
  cl := v.cr
  pr := v.pl
  cr := v.cl
  annotation_left := v.annotation_right
  annotation_right := v.annotation_left
  side_left := v.side_right
  side_right := v.side_left
  declared_left := v.declared_right
  declared_right := v.declared_left
  universe_p := v.universe_p
  universe_q := v.universe_q
  universe_pl := v.universe_pr
  universe_cl := v.universe_cr
  universe_pr := v.universe_pl
  universe_cr := v.universe_cl
  domain_left := v.domain_right
  domain_right := v.domain_left
  codomain_left := v.codomain_right
  codomain_right := v.codomain_left

/-- **The right unknown fits the left**: `A := λ x. B x`. -/
def FitFlex.toFits {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) (ne : v.right ≠ v.left)
    (fits : S.R.cumulative v.pl v.pr ∧ S.R.cumulative v.cr v.cl) : FitsView e where
  p := v.p
  q := v.q
  G := v.left
  F := v.right
  pG := v.pl
  cG := v.cl
  pF := v.pr
  cF := v.cr
  distinct := ne
  annotation_left := v.annotation_left
  annotation_right := v.annotation_right
  side_left := v.side_left
  side_right := v.side_right
  declared_G := v.declared_left
  declared_F := v.declared_right
  universe_p := v.universe_p
  universe_q := v.universe_q
  universe_pG := v.universe_pl
  universe_cG := v.universe_cl
  universe_pF := v.universe_pr
  universe_cF := v.universe_cr
  domain_G := v.domain_left
  domain_F := fits.1
  codomain_F := fits.2
  codomain_G := v.codomain_left

/-- **The reading of a unary equation is unique.** -/
theorem FitFlex.unique {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v w : FitFlex e) :
    v.left = w.left ∧ v.right = w.right := by
  have hl : v.left = w.left := Tm.var.inj (etaExp_inj 1 (v.side_left.symm.trans w.side_left))
  have hr : v.right = w.right := Tm.var.inj (etaExp_inj 1 (v.side_right.symm.trans w.side_right))
  exact ⟨hl, hr⟩

/-! ## Reading -/

section Reading

/-- The element of a one-element list. -/
def single? : List Head → Option Head
  | [p] => some p
  | _ => none

theorem single?_sound {l : List Head} {p : Head} (h : single? l = some p) : l = [p] := by
  cases l with
  | nil => cases h
  | cons a t =>
      cases t with
      | nil =>
          cases h
          rfl
      | cons b t' => cases h

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- The data of a unary flex-flex reading. -/
structure FitData (Head : Type) (n : Nat) where
  p : Head
  q : Head
  left : Fin n
  right : Fin n
  pl : Head
  cl : Head
  pr : Head
  cr : Head

/-- **Read a unary flex-flex equation of families** off its codes. -/
def readFitData {Θ : Context S.R} (e : Equation (TotalTerm Θ)) : Option (FitData Head Θ.arity) :=
  (readFam e.1.1.code).bind fun a =>
  (readFam e.2.1.code).bind fun b =>
  (single? a.1).bind fun p =>
  (readEta 1 e.1.2.code).bind fun A =>
  (readEta 1 e.2.2.code).bind fun B =>
  (readFam (Ctx.lookup Θ.raw A)).bind fun dA =>
  (readFam (Ctx.lookup Θ.raw B)).bind fun dB =>
  (single? dA.1).bind fun pl =>
  (single? dB.1).bind fun pr =>
  if b = a ∧ S.R.isUniverse p ∧ S.R.isUniverse a.2 ∧ S.R.isUniverse pl ∧ S.R.isUniverse dA.2 ∧
      S.R.isUniverse pr ∧ S.R.isUniverse dB.2 ∧ S.R.cumulative p pl ∧ S.R.cumulative p pr ∧
      S.R.cumulative dA.2 a.2 ∧ S.R.cumulative dB.2 a.2 then
    some ⟨p, a.2, A, B, pl, dA.2, pr, dB.2⟩
  else none

/-- **The reader reads every unary flex-flex equation of families.** -/
theorem readFitData_complete {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) :
    readFitData e = some ⟨v.p, v.q, v.left, v.right, v.pl, v.cl, v.pr, v.cr⟩ := by
  unfold readFitData
  rw [v.annotation_left, v.annotation_right, readFam_famCode, v.side_left, v.side_right]
  simp [-famCode_cons, -famCode_nil, single?, readEta_etaExp, v.declared_left, v.declared_right, readFam_famCode,
    v.universe_p, v.universe_q, v.universe_pl, v.universe_cl, v.universe_pr, v.universe_cr, v.domain_left,
    v.domain_right, v.codomain_left, v.codomain_right]

/-- What a successful reading says. -/
theorem readFitData_sound {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {d : FitData Head Θ.arity}
    (h : readFitData e = some d) :
    e.1.1.code = famCode [d.p] d.q ∧ e.2.1.code = famCode [d.p] d.q ∧
      e.1.2.code = etaExp 1 (.var d.left) ∧ e.2.2.code = etaExp 1 (.var d.right) ∧
      Ctx.lookup Θ.raw d.left = famCode [d.pl] d.cl ∧ Ctx.lookup Θ.raw d.right = famCode [d.pr] d.cr ∧
      S.R.isUniverse d.p ∧ S.R.isUniverse d.q ∧ S.R.isUniverse d.pl ∧ S.R.isUniverse d.cl ∧
      S.R.isUniverse d.pr ∧ S.R.isUniverse d.cr ∧ S.R.cumulative d.p d.pl ∧ S.R.cumulative d.p d.pr ∧
      S.R.cumulative d.cl d.q ∧ S.R.cumulative d.cr d.q := by
  unfold readFitData at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, p, hp, A, hA, B, hB, dA, hdA, dB, hdB, pl, hpl, pr, hpr, h⟩ := h
  split_ifs at h with hc
  cases h
  obtain ⟨rfl, up, uq, upl, ucl, upr, ucr, dl, dr, cl, cr⟩ := hc
  have ea := readFam_sound ha
  have eb := readFam_sound hb
  rw [single?_sound hp] at ea eb
  have eA := readFam_sound hdA
  have eB := readFam_sound hdB
  rw [single?_sound hpl] at eA
  rw [single?_sound hpr] at eB
  exact ⟨ea, eb, readEta_sound hA, readEta_sound hB, eA, eB, up, uq, upl, ucl, upr, ucr, dl, dr, cl, cr⟩

/-- The view of a successful reading. -/
def viewOfFit {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {d : FitData Head Θ.arity}
    (h : readFitData e = some d) : FitFlex e where
  p := d.p
  q := d.q
  left := d.left
  right := d.right
  pl := d.pl
  cl := d.cl
  pr := d.pr
  cr := d.cr
  annotation_left := (readFitData_sound h).1
  annotation_right := (readFitData_sound h).2.1
  side_left := (readFitData_sound h).2.2.1
  side_right := (readFitData_sound h).2.2.2.1
  declared_left := (readFitData_sound h).2.2.2.2.1
  declared_right := (readFitData_sound h).2.2.2.2.2.1
  universe_p := (readFitData_sound h).2.2.2.2.2.2.1
  universe_q := (readFitData_sound h).2.2.2.2.2.2.2.1
  universe_pl := (readFitData_sound h).2.2.2.2.2.2.2.2.1
  universe_cl := (readFitData_sound h).2.2.2.2.2.2.2.2.2.1
  universe_pr := (readFitData_sound h).2.2.2.2.2.2.2.2.2.2.1
  universe_cr := (readFitData_sound h).2.2.2.2.2.2.2.2.2.2.2.1
  domain_left := (readFitData_sound h).2.2.2.2.2.2.2.2.2.2.2.2.1
  domain_right := (readFitData_sound h).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  codomain_left := (readFitData_sound h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  codomain_right := (readFitData_sound h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Reading

/-! ## The fragment -/

section Fragment

/-- Of two different unknowns in one group, one fits the other. -/
def FitComparable (Θ : Context S.R) (group : Fin Θ.arity → Nat) : Prop :=
  ∀ i j : Fin Θ.arity, i ≠ j → group i = group j → ∀ (pi ci pj cj : Head),
    Ctx.lookup Θ.raw i = famCode [pi] ci → Ctx.lookup Θ.raw j = famCode [pj] cj →
      (S.R.cumulative pi pj ∧ S.R.cumulative cj ci) ∨ (S.R.cumulative pj pi ∧ S.R.cumulative ci cj)

/-- **The fragment of fitting groups.** -/
structure InFitFragment {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop where
  families : AllFamilies Θ
  shapes : ∀ e ∈ problem, Nonempty (FitFlex e)
  grouped : ∃ group : Fin Θ.arity → Nat,
    (∀ e ∈ problem, ∀ v : FitFlex e, group v.left = group v.right) ∧ FitComparable Θ group

theorem inFitFragment_delete {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (inside : InFitFragment (e :: rest)) : InFitFragment rest := by
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
  exact ⟨inside.families, fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member),
    ⟨group, fun e' member => grouped e' (List.mem_cons_of_mem _ member), comparable⟩⟩

variable [DecidableEq Head] [DecidableRel S.R.cumulative] (algebra : CumulativeAlgebra S.R)

theorem contractSide_eq_reread {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e)
    (all : AllFamilies Θ) {side : TotalTerm Θ} {p' q' : Head} (h : Rereads v side p' q')
    (candidate : unaryCandidate side = some (p', q')) :
    contractSide algebra v all side = ⟨side.1, rereadTerm algebra v side h⟩ := by
  unfold contractSide
  rw [candidate]
  exact dif_pos h

/-- A side `λ y. G y` at a fitting annotation is re-read as `λ y. F y`. -/
theorem contractSide_reread {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e) (all : AllFamilies Θ)
    {side : TotalTerm Θ} {p' q' : Head} (h : Rereads v side p' q') :
    (contractSide algebra v all side).1 = side.1 ∧ (contractSide algebra v all side).2.code = etaExp 1 (.var v.F) := by
  have candidate : unaryCandidate side = some (p', q') := by
    unfold unaryCandidate
    rw [h.1, readFam_famCode]
  have same := contractSide_eq_reread algebra v all h candidate
  have first := congrArg (fun s : TotalTerm Θ => s.1) same
  have second := congrArg (fun s : TotalTerm Θ => s.2.code) same
  exact ⟨first, second⟩

/-- Any other side is instantiated, and keeps its codes when it does not mention `G`. -/
theorem contractSide_keep {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e) (all : AllFamilies Θ)
    {side : TotalTerm Θ} {Z : Fin Θ.arity} {p' q' : Head} (annotation : side.1.code = famCode [p'] q')
    (code : side.2.code = etaExp 1 (.var Z)) (ne : Z ≠ v.G) :
    (contractSide algebra v all side).1.code = famCode [p'] q' ∧
      (contractSide algebra v all side).2.code = etaExp 1 (.var Z) := by
  have notReread : ∀ p'' q'', ¬ Rereads v side p'' q'' := by
    intro p'' q'' h
    exact ne (Tm.var.inj (etaExp_inj 1 (code.symm.trans h.2.1)))
  rcases contractSide_cases algebra v all side with ⟨p'', q'', h, _⟩ | same
  · exact absurd h (notReread p'' q'')
  · rw [same]
    constructor
    · change Presentation.subst (raiseSub v.F v.G) side.1.code = _
      rw [annotation, famCode_subst]
    · change Presentation.subst (raiseSub v.F v.G) side.2.code = _
      rw [code, subst_etaExp]
      change etaExp 1 (raiseSub v.F v.G Z) = _
      rw [raiseSub_ne _ _ ne]

/-- `G := F` on unknowns. -/
def raiseVar {n : Nat} (F G : Fin n) (i : Fin n) : Fin n := if i = G then F else i

/-- **The view of an equation, after domain raising and re-reading.** -/
theorem contract_view {Θ : Context S.R} {e e' : Equation (TotalTerm Θ)} (v : FitsView e) (all : AllFamilies Θ)
    (w : FitFlex e') :
    ∃ t : FitFlex ((contractSide algebra v all e'.1, contractSide algebra v all e'.2) : Equation (TotalTerm Θ)),
      t.left = raiseVar v.F v.G w.left ∧ t.right = raiseVar v.F v.G w.right := by
  -- How each side is read after the step.
  have side : ∀ (s : TotalTerm Θ) (Z : Fin Θ.arity) (pZ cZ : Head),
      s.1.code = famCode [w.p] w.q → s.2.code = etaExp 1 (.var Z) → Ctx.lookup Θ.raw Z = famCode [pZ] cZ →
      S.R.isUniverse pZ → S.R.isUniverse cZ → S.R.cumulative w.p pZ → S.R.cumulative cZ w.q →
      ∃ (pZ' cZ' : Head), (contractSide algebra v all s).1.code = famCode [w.p] w.q ∧
        (contractSide algebra v all s).2.code = etaExp 1 (.var (raiseVar v.F v.G Z)) ∧
        Ctx.lookup Θ.raw (raiseVar v.F v.G Z) = famCode [pZ'] cZ' ∧ S.R.isUniverse pZ' ∧ S.R.isUniverse cZ' ∧
        S.R.cumulative w.p pZ' ∧ S.R.cumulative cZ' w.q := by
    intro s Z pZ cZ annotation code declared upZ ucZ domain codomain
    by_cases hZ : Z = v.G
    · subst hZ
      obtain ⟨hp, hc⟩ := famCode_inj (declared.symm.trans v.declared_G)
      have p_eq : pZ = v.pG := (List.cons.inj hp).1
      subst p_eq
      subst hc
      have rereads : Rereads v s w.p w.q := ⟨annotation, code, domain, codomain⟩
      obtain ⟨same1, same2⟩ := contractSide_reread algebra v all rereads
      refine ⟨v.pF, v.cF, by rw [same1]; exact annotation, ?_, ?_, v.universe_pF, v.universe_cF,
        algebra.trans domain v.domain_F, algebra.trans v.codomain_F codomain⟩
      · rw [same2]
        unfold raiseVar
        rw [if_pos rfl]
      · unfold raiseVar
        rw [if_pos rfl]
        exact v.declared_F
    · obtain ⟨same1, same2⟩ := contractSide_keep algebra v all annotation code hZ
      refine ⟨pZ, cZ, same1, ?_, ?_, upZ, ucZ, domain, codomain⟩
      · rw [same2]
        unfold raiseVar
        rw [if_neg hZ]
      · unfold raiseVar
        rw [if_neg hZ]
        exact declared
  obtain ⟨pl', cl', a1, s1, d1, upl, ucl, dl, cl⟩ := side e'.1 w.left w.pl w.cl w.annotation_left w.side_left
    w.declared_left w.universe_pl w.universe_cl w.domain_left w.codomain_left
  obtain ⟨pr', cr', a2, s2, d2, upr, ucr, dr, cr⟩ := side e'.2 w.right w.pr w.cr w.annotation_right w.side_right
    w.declared_right w.universe_pr w.universe_cr w.domain_right w.codomain_right
  exact ⟨{
    p := w.p
    q := w.q
    left := raiseVar v.F v.G w.left
    right := raiseVar v.F v.G w.right
    pl := pl'
    cl := cl'
    pr := pr'
    cr := cr'
    annotation_left := a1
    annotation_right := a2
    side_left := s1
    side_right := s2
    declared_left := d1
    declared_right := d2
    universe_p := w.universe_p
    universe_q := w.universe_q
    universe_pl := upl
    universe_cl := ucl
    universe_pr := upr
    universe_cr := ucr
    domain_left := dl
    domain_right := dr
    codomain_left := cl
    codomain_right := cr }, rfl, rfl⟩

/-- **Domain raising keeps the fragment.** -/
theorem inFitFragment_raise {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e) (all : AllFamilies Θ)
    {rest : EquationStore (TotalTerm Θ)} (shapes : ∀ e' ∈ rest, Nonempty (FitFlex e')) (group : Fin Θ.arity → Nat)
    (grouped : ∀ e' ∈ rest, ∀ w : FitFlex e', group w.left = group w.right) (together : group v.F = group v.G)
    (comparable : FitComparable Θ group) : InFitFragment (contractStore algebra v all rest) := by
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

end Fragment

/-! ## The solver -/

section Solver

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- Delete an equation whose two sides have the same codes. -/
def deleteCodes {Θ : Context S.R} (e : Equation (TotalTerm Θ)) (sameType : e.1.1.code = e.2.1.code)
    (sameTerm : e.1.2.code = e.2.2.code) (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) where
  target := Θ
  answer := 𝟙 Θ
  remaining := rest
  sound := by
    intro Δ residual solved
    rw [Category.comp_id]
    intro e' member
    rcases List.mem_cons.mp member with rfl | member
    · apply e_of_codes
      · change Presentation.subst residual.substitution e'.1.1.code = Presentation.subst residual.substitution e'.2.1.code
        rw [sameType]
      · change Presentation.subst residual.substitution e'.1.2.code = Presentation.subst residual.substitution e'.2.2.code
        rw [sameTerm]
    · exact solved e' member
  complete := by
    intro Δ solution solved
    refine ⟨solution, fun e' member => solved e' (List.mem_cons_of_mem _ member), fun term => ?_⟩
    rw [Category.comp_id]
    exact ((frames S.levels).equivalence Δ).refl _

/-- **One step on a read equation**: delete, raise in either orientation, or stuck. -/
def stepFit {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ) (v : FitFlex e)
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
  else .stuck

/-- **The round of the solver**: read the first equation, then step. -/
def fitRound : {Γ : Context S.R} → (problem : EquationStore (TotalTerm Γ)) → Round S.levels storeRank problem
  | _, [] => .stuck
  | Θ, e :: rest =>
      if hall : allFamiliesB Θ = true then
        match hd : readFitData e with
        | some _ => stepFit facts roots heads algebra rigid complete (allFamilies_of_B hall) (viewOfFit hd) rest
        | none => .stuck
      else .stuck

/-- **The tree's driver with delete and domain raising.** -/
def fitSolver : ContextualDependentWorklist.Solver S.levels where
  rank := storeRank
  round := fitRound facts roots heads algebra rigid complete

omit [∀ head, Decidable (S.R.isUniverse head)] in
theorem stepFit_ne_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ) (v : FitFlex e)
    (rest : EquationStore (TotalTerm Θ))
    (decided : v.left = v.right ∨ (S.R.cumulative v.pl v.pr ∧ S.R.cumulative v.cr v.cl) ∨
      (S.R.cumulative v.pr v.pl ∧ S.R.cumulative v.cl v.cr)) :
    stepFit facts roots heads algebra rigid complete all v rest ≠ .stuck := by
  unfold stepFit
  split_ifs with h1 h2 h3
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · rcases decided with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact absurd h h3

omit [∀ head, Decidable (S.R.isUniverse head)] in
theorem stepFit_ne_refuted {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ) (v : FitFlex e)
    (rest : EquationStore (TotalTerm Θ)) (absent : ¬ (frames S.levels).Solvable (e :: rest)) :
    stepFit facts roots heads algebra rigid complete all v rest ≠ .refuted absent := by
  unfold stepFit
  split_ifs <;> intro h <;> cases h

/-- **The rules never refute.** -/
theorem fitRound_ne_refuted {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ))
    (absent : ¬ (frames S.levels).Solvable problem) :
    fitRound facts roots heads algebra rigid complete problem ≠ .refuted absent := by
  cases problem with
  | nil => intro h; cases h
  | cons e rest =>
      simp only [fitRound]
      split_ifs with hall
      · split
        · exact stepFit_ne_refuted facts roots heads algebra rigid complete _ _ rest absent
        · intro h; cases h
      · intro h; cases h

/-- **Progress by shape**: on a nonempty store of the fragment, the round is not stuck. -/
theorem fitRound_ne_stuck {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} (inside : InFitFragment problem)
    (nonempty : problem ≠ []) : fitRound facts roots heads algebra rigid complete problem ≠ .stuck := by
  cases problem with
  | nil => exact absurd rfl nonempty
  | cons e rest =>
      obtain ⟨v⟩ := inside.shapes e List.mem_cons_self
      obtain ⟨group, grouped, comparable⟩ := inside.grouped
      have hall := allFamiliesB_of inside.families
      have hd := readFitData_complete v
      simp only [fitRound, dif_pos hall]
      split
      · rename_i d hd'
        apply stepFit_ne_stuck
        let w := viewOfFit hd'
        by_cases same : w.left = w.right
        · exact .inl same
        · exact .inr (comparable w.left w.right same (grouped e List.mem_cons_self w) w.pl w.cl w.pr w.cr
            w.declared_left w.declared_right)
      · rename_i hd'
        rw [hd] at hd'
        cases hd'

/-- **The rules keep the fragment.** -/
theorem fitRound_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (storeRank update.remaining) (storeRank problem)}
    (inside : InFitFragment problem)
    (progressed : fitRound facts roots heads algebra rigid complete problem = .progress update smaller) :
    InFitFragment update.remaining := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      obtain ⟨group, grouped, comparable⟩ := inside.grouped
      have restShapes : ∀ e' ∈ rest, Nonempty (FitFlex e') :=
        fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member)
      have restGrouped : ∀ e' ∈ rest, ∀ w : FitFlex e', group w.left = group w.right :=
        fun e' member => grouped e' (List.mem_cons_of_mem _ member)
      simp only [fitRound] at progressed
      split_ifs at progressed with hall
      split at progressed
      · rename_i d hd
        unfold stepFit at progressed
        split_ifs at progressed with h1 h2 h3
        · cases progressed
          exact inFitFragment_delete inside
        · cases progressed
          exact inFitFragment_raise algebra _ (allFamilies_of_B hall) restShapes group restGrouped
            (grouped e List.mem_cons_self _).symm comparable
        · cases progressed
          exact inFitFragment_raise algebra _ (allFamilies_of_B hall) restShapes group restGrouped
            (grouped e List.mem_cons_self _) comparable
      · cases progressed

/-- **The fragment of the solver.** -/
def fitFragment : ContextualDependentWorklist.Fragment (fitSolver facts roots heads algebra rigid complete) where
  holds := InFitFragment
  stable := fun inside progressed => fitRound_stable facts roots heads algebra rigid complete inside progressed
  decisive := fun inside nonempty => fitRound_ne_stuck facts roots heads algebra rigid complete inside nonempty

include facts roots heads algebra rigid complete in
/-- **Decided by shape**: on the fragment of fitting groups, the tree's driver with delete and domain raising reaches,
at some budget and at every larger one, a principal answer or a certified refutation. -/
theorem fit_decided {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)} (inside : InFitFragment original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (fitSolver facts roots heads algebra rigid complete) original larger =
          run (fitSolver facts roots heads algebra rigid complete) original fuel ∧
        ((∃ state finished, run (fitSolver facts roots heads algebra rigid complete) original larger =
              .solved state finished ∧ (frames S.levels).Principal original state.answer) ∨
          (∃ absent, run (fitSolver facts roots heads algebra rigid complete) original larger = .refuted absent)) :=
  (fitFragment facts roots heads algebra rigid complete).decided inside

include facts roots heads algebra rigid complete in
/-- **Every store of the fragment of fitting groups has a principal answer.** -/
theorem principal_of_inFitFragment {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InFitFragment original) :
    ∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), (frames S.levels).Principal original answer := by
  obtain ⟨fuel, ends⟩ := fit_decided facts roots heads algebra rigid complete inside
  rcases (ends fuel le_rfl).2 with ⟨state, _, _, principal⟩ | ⟨absent, refuted⟩
  · exact ⟨_, _, principal⟩
  · exact absurd refuted (drive_ne_refuted (fitSolver facts roots heads algebra rigid complete)
      (fun problem absent => fitRound_ne_refuted facts roots heads algebra rigid complete problem absent)
      fuel _ absent)

end Solver

/-! ## Membership, decided -/

section Membership

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- Of two different declared unary families, one fits the other, decided. -/
def fitComparableB (Θ : Context S.R) : Bool :=
  (List.finRange Θ.arity).all fun i => (List.finRange Θ.arity).all fun j =>
    if i = j then true else
    match readFam (Ctx.lookup Θ.raw i), readFam (Ctx.lookup Θ.raw j) with
    | some a, some b =>
        match a.1, b.1 with
        | [pi], [pj] => decide ((S.R.cumulative pi pj ∧ S.R.cumulative b.2 a.2) ∨
            (S.R.cumulative pj pi ∧ S.R.cumulative a.2 b.2))
        | _, _ => true
    | _, _ => true

omit [∀ head, Decidable (S.R.isUniverse head)] in
theorem fitComparable_of_B {Θ : Context S.R} (h : fitComparableB Θ = true) : FitComparable Θ (fun _ => 0) := by
  intro i j ne _ pi ci pj cj hi hj
  have hij := List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_finRange i)) j (List.mem_finRange j)
  rw [if_neg ne, hi, hj, readFam_famCode, readFam_famCode] at hij
  exact of_decide_eq_true hij

/-- **Membership in the fragment of fitting groups, decided**, with all unknowns in one group. -/
def inFitFragmentB {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Bool :=
  allFamiliesB Θ && problem.all (fun e => (readFitData e).isSome) && fitComparableB Θ

theorem inFitFragment_of_B {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (h : inFitFragmentB problem = true) : InFitFragment problem := by
  simp only [inFitFragmentB, Bool.and_eq_true] at h
  obtain ⟨⟨hall, hshapes⟩, hcomp⟩ := h
  refine ⟨allFamilies_of_B hall, fun e member => ?_, ⟨fun _ => 0, fun _ _ _ => rfl, fitComparable_of_B hcomp⟩⟩
  have he := List.all_eq_true.mp hshapes e member
  cases hd : readFitData e with
  | none => rw [hd] at he; cases he
  | some d => exact ⟨viewOfFit hd⟩

end Membership

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
