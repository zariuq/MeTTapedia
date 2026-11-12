import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MeetGroups
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbMeet

/-!
# The greatest-lower-bound rule inside a decided fragment

A solver of the tree's worklist driver (`glbGroupSolver`) for unary families, given a function `glb` that returns
greatest lower bounds of universes (`spec`). It reads the first equation `λ x. A x ≐ λ x. B x` at
`Π (x : U_p). U_q` by its codes and applies the rules of meet groups (delete; raise in either orientation; the true
meet in either orientation); when none applies, the greatest-lower-bound rule (`glbMeetUpdate`) at `g = glb cA cB`,
in either orientation, when its conditions hold; it is stuck otherwise.

**Views below each other** (`BelowPair`): comparable domains, each below both codomains. Two views that meet are
below each other (`belowPair_of_meets`). **The fragment** (`InGlbFragment`): every declaration is a universe family;
every equation is a unary flex-flex equation of families; and there is a grouping in which the two unknowns of every
equation share a group and, within a group, any two different unknowns are compatible or below each other
(`GlbCompat`). It contains the fragment of meet groups (`inGlbFragment_of_meet`) and also stores whose codomains are
incomparable, as for two level variables.

* **Lowering to a greatest lower bound keeps the relation** (`GlbCompat.lower`): an unknown compatible with, or
  below, two views is so with both views lowered to a greatest lower bound `g` of their codomains, when both domains
  lie below `g`. By transitivity and the universal property of `g` alone. The true meet is the case `g = cA`
  (`glbComparable_meet`).
* Kept by every rule (`inGlbFragment_delete`, `inGlbFragment_raise`, `inGlbFragment_meet`, `inGlbFragment_glb`).
* **Progress by shape** (`glbGroupRound_ne_stuck`), when every two universes have a greatest lower bound (`total`):
  two different unknowns of a group either are compatible, and a rule of meet groups applies, or are below each
  other, and then both domains lie below `g` and the greatest-lower-bound rule applies.
* Decided (`glbGroup_decided`); every store of the fragment has a principal answer (`principal_of_inGlbFragment`).

Nothing in the rule choice reads a level valuation: the comparisons are `S.R.cumulative` and the function `glb`.
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

/-! ## Views below each other -/

section Views

variable {R : Rules Head}

/-- **Two unary views `(p, c)` and `(p', c')` are below each other**: their domains are comparable, and each domain
lies below both codomains. -/
def BelowPair (R : Rules Head) (p c p' c' : Head) : Prop :=
  (R.cumulative p p' ∨ R.cumulative p' p) ∧ R.cumulative p c ∧ R.cumulative p c' ∧ R.cumulative p' c ∧
    R.cumulative p' c'

instance [DecidableRel R.cumulative] (p c p' c' : Head) : Decidable (BelowPair R p c p' c') := by
  unfold BelowPair
  infer_instance

theorem BelowPair.symm {p c p' c' : Head} (h : BelowPair R p c p' c') : BelowPair R p' c' p c :=
  ⟨h.1.symm, h.2.2.2.2, h.2.2.2.1, h.2.2.1, h.2.1⟩

/-- **Compatible, or below each other.** -/
def GlbCompat (R : Rules Head) (p c p' c' : Head) : Prop := Compat R p c p' c' ∨ BelowPair R p c p' c'

instance [DecidableRel R.cumulative] (p c p' c' : Head) : Decidable (GlbCompat R p c p' c') := by
  unfold GlbCompat
  infer_instance

theorem GlbCompat.symm {p c p' c' : Head} (h : GlbCompat R p c p' c') : GlbCompat R p' c' p c :=
  h.imp Compat.symm BelowPair.symm

/-- Neither compatible way holds, so the views are below each other. -/
theorem below_of_not_compat {p c p' c' : Head} (h : GlbCompat R p c p' c')
    (n1 : ¬ (R.cumulative p p' ∧ R.cumulative c' c)) (n2 : ¬ (R.cumulative p' p ∧ R.cumulative c c'))
    (n3 : ¬ (R.cumulative p p' ∧ R.cumulative c c' ∧ R.cumulative p' c))
    (n4 : ¬ (R.cumulative p' p ∧ R.cumulative c' c ∧ R.cumulative p c')) : BelowPair R p c p' c' := by
  rcases h with (h | h | h | h) | h
  · exact absurd h n2
  · exact absurd h n1
  · exact absurd h n3
  · exact absurd h n4
  · exact h

variable (trans : ∀ {u v w : Head}, R.cumulative u v → R.cumulative v w → R.cumulative u w)

include trans in
/-- **Two views that meet are below each other.** -/
theorem belowPair_of_meets {p c p' c' : Head} (dom : R.cumulative p p') (cod : R.cumulative c c')
    (cross : R.cumulative p' c) : BelowPair R p c p' c' :=
  ⟨Or.inl dom, trans dom cross, trans (trans dom cross) cod, cross, trans cross cod⟩

include trans in
/-- Compatible or below each other is: the first fits the second, the second fits the first, or they are below
each other. -/
theorem GlbCompat.cases {p c p' c' : Head} (h : GlbCompat R p c p' c') :
    (R.cumulative p' p ∧ R.cumulative c c') ∨ (R.cumulative p p' ∧ R.cumulative c' c) ∨ BelowPair R p c p' c' := by
  rcases h with (h | h | ⟨d, k, x⟩ | ⟨d, k, x⟩) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (belowPair_of_meets trans d k x))
  · exact Or.inr (Or.inr (belowPair_of_meets trans d k x).symm)
  · exact Or.inr (Or.inr h)

include trans in
/-- **Lowering two views to a greatest lower bound keeps the relation.** If `Z` is compatible with, or below, `A`
and `B`, `A`'s domain lies below `B`'s, and both domains lie below `g`, a greatest lower bound of the two codomains,
then `Z` is compatible with, or below, `A` and `B` with codomain `g`. -/
theorem GlbCompat.lower (universe_of : ∀ {u v : Head}, R.cumulative u v → R.isUniverse u)
    {pZ cZ pA cA pB cB g : Head} (za : GlbCompat R pZ cZ pA cA) (zb : GlbCompat R pZ cZ pB cB)
    (dom : R.cumulative pA pB) (ga : R.cumulative pA g) (gb : R.cumulative pB g) (la : R.cumulative g cA)
    (lb : R.cumulative g cB)
    (greatest : ∀ u, R.isUniverse u → R.cumulative u cA → R.cumulative u cB → R.cumulative u g) :
    GlbCompat R pZ cZ pA g ∧ GlbCompat R pZ cZ pB g := by
  have belowA : BelowPair R pZ cZ pA cA → R.cumulative pZ g → GlbCompat R pZ cZ pA g :=
    fun h zg => Or.inr ⟨h.1, h.2.1, zg, h.2.2.2.1, ga⟩
  have belowB : BelowPair R pZ cZ pB cB → R.cumulative pZ g → GlbCompat R pZ cZ pB g :=
    fun h zg => Or.inr ⟨h.1, h.2.1, zg, h.2.2.2.1, gb⟩
  rcases GlbCompat.cases trans za with ⟨a1, a2⟩ | ⟨a1, a2⟩ | a
  · -- `Z` fits `A`
    rcases GlbCompat.cases trans zb with ⟨b1, b2⟩ | ⟨b1, b2⟩ | b
    · have zg : R.cumulative cZ g := greatest cZ (universe_of a2) a2 b2
      exact ⟨Or.inl (Or.inl ⟨a1, zg⟩), Or.inl (Or.inl ⟨b1, zg⟩)⟩
    · have zc : R.cumulative pZ cZ := trans b1 (trans gb (trans lb b2))
      exact ⟨Or.inr ⟨Or.inr a1, zc, trans b1 gb, trans a1 zc, ga⟩, Or.inl (Or.inr (Or.inl ⟨b1, trans lb b2⟩))⟩
    · have zg : R.cumulative pZ g := greatest pZ (universe_of b.2.1) (trans b.2.1 a2) b.2.2.1
      exact ⟨Or.inr ⟨Or.inr a1, b.2.1, zg, trans a1 b.2.1, ga⟩, belowB b zg⟩
  · -- `A` fits `Z`
    exact ⟨Or.inl (Or.inr (Or.inl ⟨a1, trans la a2⟩)), Or.inl (Or.inr (Or.inl ⟨trans a1 dom, trans la a2⟩))⟩
  · -- `Z` and `A` below each other
    rcases GlbCompat.cases trans zb with ⟨b1, b2⟩ | ⟨b1, b2⟩ | b
    · have zg : R.cumulative pZ g := greatest pZ (universe_of a.2.1) a.2.2.1 (trans a.2.1 b2)
      exact ⟨belowA a zg, Or.inr ⟨Or.inr b1, a.2.1, zg, trans b1 a.2.1, gb⟩⟩
    · have zg : R.cumulative pZ g := greatest pZ (universe_of a.2.1) a.2.2.1 (trans b1 (trans gb lb))
      exact ⟨belowA a zg, Or.inl (Or.inr (Or.inl ⟨b1, trans lb b2⟩))⟩
    · have zg : R.cumulative pZ g := greatest pZ (universe_of a.2.1) a.2.2.1 b.2.2.1
      exact ⟨belowA a zg, belowB b zg⟩

end Views

/-! ## Groups -/

section Groups

variable {R : Rules Head}

/-- **Of two different unknowns in one group, the declared unary views are compatible or below each other.** -/
def GlbComparable (R : Rules Head) {n : Nat} (Γ : Ctx Head n) (group : Fin n → Nat) : Prop :=
  ∀ i j : Fin n, i ≠ j → group i = group j → ∀ (pi ci pj cj : Head),
    Ctx.lookup Γ i = famCode [pi] ci → Ctx.lookup Γ j = famCode [pj] cj → GlbCompat R pi ci pj cj

theorem glbComparable_of_meetComparable {n : Nat} {Γ : Ctx Head n} {group : Fin n → Nat}
    (h : MeetComparable R Γ group) : GlbComparable R Γ group :=
  fun i j ne same pi ci pj cj di dj => Or.inl (h i j ne same pi ci pj cj di dj)

variable (trans : ∀ {u v w : Head}, R.cumulative u v → R.cumulative v w → R.cumulative u w)

include trans in
/-- **Two unknowns of one group lowered to a greatest lower bound keep the relation within the groups**: `X` and
`Y` declared again at codomain `g`, every other declaration unchanged. -/
theorem glbComparable_lowered (universe_of : ∀ {u v : Head}, R.cumulative u v → R.isUniverse u)
    (refl : ∀ {u : Head}, R.isUniverse u → R.cumulative u u)
    {n : Nat} {Γ Γ' : Ctx Head n} {group : Fin n → Nat} {X Y : Fin n} {pX cX pY cY g : Head}
    (together : group X = group Y) (comparable : GlbComparable R Γ group)
    (hX : Ctx.lookup Γ X = famCode [pX] cX) (hY : Ctx.lookup Γ Y = famCode [pY] cY)
    (newX : Ctx.lookup Γ' X = famCode [pX] g) (newY : Ctx.lookup Γ' Y = famCode [pY] g)
    (others : ∀ Z, Z ≠ X → Z ≠ Y → Ctx.lookup Γ' Z = Ctx.lookup Γ Z)
    (dom : R.cumulative pX pY) (gx : R.cumulative pX g) (gy : R.cumulative pY g) (lx : R.cumulative g cX)
    (ly : R.cumulative g cY)
    (greatest : ∀ u, R.isUniverse u → R.cumulative u cX → R.cumulative u cY → R.cumulative u g) :
    GlbComparable R Γ' group := by
  have pair : GlbCompat R pX g pY g := Or.inl (Or.inr (Or.inl ⟨dom, refl (universe_of lx)⟩))
  have against : ∀ Z, Z ≠ X → Z ≠ Y → group Z = group X → ∀ pZ cZ, Ctx.lookup Γ' Z = famCode [pZ] cZ →
      GlbCompat R pZ cZ pX g ∧ GlbCompat R pZ cZ pY g := by
    intro Z zx zy grp pZ cZ dZ
    rw [others Z zx zy] at dZ
    exact GlbCompat.lower trans universe_of (comparable Z X zx grp pZ cZ pX cX dZ hX)
      (comparable Z Y zy (grp.trans together) pZ cZ pY cY dZ hY) dom gx gy lx ly greatest
  have view : ∀ k : Fin n, ∀ pk ck, Ctx.lookup Γ' k = famCode [pk] ck →
      (k = X ∧ pk = pX ∧ ck = g) ∨ (k = Y ∧ pk = pY ∧ ck = g) ∨
        (k ≠ X ∧ k ≠ Y ∧ Ctx.lookup Γ k = famCode [pk] ck) := by
    intro k pk ck dk
    by_cases kX : k = X
    · rw [kX] at dk
      obtain ⟨hp, hc⟩ := famCode_inj (dk.symm.trans newX)
      exact Or.inl ⟨kX, (List.cons.inj hp).1, hc⟩
    · by_cases kY : k = Y
      · rw [kY] at dk
        obtain ⟨hp, hc⟩ := famCode_inj (dk.symm.trans newY)
        exact Or.inr (Or.inl ⟨kY, (List.cons.inj hp).1, hc⟩)
      · exact Or.inr (Or.inr ⟨kX, kY, (others k kX kY).symm.trans dk⟩)
  intro i j ne grp pi ci pj cj di dj
  rcases view i pi ci di with ⟨iX, hpi, hci⟩ | ⟨iY, hpi, hci⟩ | ⟨iX, iY, di'⟩ <;>
    rcases view j pj cj dj with ⟨jX, hpj, hcj⟩ | ⟨jY, hpj, hcj⟩ | ⟨jX, jY, dj'⟩
  · exact absurd (iX.trans jX.symm) ne
  · rw [hpi, hci, hpj, hcj]
    exact pair
  · rw [hpi, hci]
    exact (against j jX jY (by rw [← grp, iX]) pj cj dj).1.symm
  · rw [hpi, hci, hpj, hcj]
    exact pair.symm
  · exact absurd (iY.trans jY.symm) ne
  · rw [hpi, hci]
    exact (against j jX jY (by rw [← grp, iY, together]) pj cj dj).2.symm
  · rw [hpj, hcj]
    exact (against i iX iY (by rw [grp, jX]) pi ci di).1
  · rw [hpj, hcj]
    exact (against i iX iY (by rw [grp, jY, together]) pi ci di).2
  · exact comparable i j ne grp pi ci pj cj di' dj'

end Groups

/-! ## The fragment -/

section Fragment

/-- **The fragment of groups compatible or below each other.** -/
structure InGlbFragment {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop where
  families : AllFamilies Θ
  shapes : ∀ e ∈ problem, Nonempty (FitFlex e)
  grouped : ∃ group : Fin Θ.arity → Nat,
    (∀ e ∈ problem, ∀ v : FitFlex e, group v.left = group v.right) ∧ GlbComparable S.R Θ.raw group

/-- **The fragment of meet groups lies inside.** -/
theorem inGlbFragment_of_meet {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : InMeetFragment problem) : InGlbFragment problem := by
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
  exact ⟨inside.families, inside.shapes, ⟨group, grouped, glbComparable_of_meetComparable comparable⟩⟩

theorem inGlbFragment_delete {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (inside : InGlbFragment (e :: rest)) : InGlbFragment rest := by
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
  exact ⟨inside.families, fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member),
    ⟨group, fun e' member => grouped e' (List.mem_cons_of_mem _ member), comparable⟩⟩

variable (algebra : CumulativeAlgebra S.R)

include algebra in
/-- **The view of an equation over a telescope with one codomain lowered**: the same codes and unknowns. -/
theorem lowering_view {Θ : Context S.R} (ℓ : CodomainLowering Θ) {e' : Equation (TotalTerm Θ)} (w : FitFlex e') :
    ∃ t : FitFlex (((frames S.levels).act ℓ.hom e'.1, (frames S.levels).act ℓ.hom e'.2) :
        Equation (TotalTerm ℓ.target)), t.left = w.left ∧ t.right = w.right := by
  have side : ∀ (Z : Fin Θ.arity) (pZ cZ : Head), Ctx.lookup Θ.raw Z = famCode [pZ] cZ → S.R.isUniverse cZ →
      S.R.cumulative cZ w.q → ∃ cZ', Ctx.lookup ℓ.target.raw Z = famCode [pZ] cZ' ∧
        S.R.isUniverse cZ' ∧ S.R.cumulative cZ' w.q := by
    intro Z pZ cZ declared hc below
    by_cases hZ : Z = ℓ.index
    · rw [hZ] at declared ⊢
      obtain ⟨hp, hcZ⟩ := famCode_inj (declared.symm.trans ℓ.declared)
      refine ⟨ℓ.lower, ?_, ℓ.universe_lower, algebra.trans ℓ.below (by rw [← hcZ]; exact below)⟩
      rw [ℓ.lookup_self, ← hp]
    · exact ⟨cZ, by rw [ℓ.lookup_ne hZ]; exact declared, hc, below⟩
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

include algebra in
/-- **The true meet keeps the relation within the groups**: the case `g = cA`, with `A` unchanged. -/
theorem glbComparable_meet {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) (meets : Meets v)
    (distinct : v.right ≠ v.left) (group : Fin Θ.arity → Nat) (together : group v.left = group v.right)
    (comparable : GlbComparable S.R Θ.raw group) :
    GlbComparable S.R (setFamAt Θ.raw v.right [v.pr] v.cl) group :=
  glbComparable_lowered algebra.trans (fun h => (S.levels.cumulative_universe h).1) S.levels.cumulative_refl
    together comparable v.declared_left v.declared_right
    ((lookup_setFamAt_ne Θ.raw v.right v.left [v.pr] v.cl (fun same => distinct same.symm)).trans v.declared_left)
    (lookup_setFamAt_self Θ.raw v.right [v.pr] v.cl)
    (fun Z _ zy => lookup_setFamAt_ne Θ.raw v.right Z [v.pr] v.cl zy)
    meets.1 (algebra.trans meets.1 meets.2.2) meets.2.2 (S.levels.cumulative_refl v.universe_cl) meets.2.1
    (fun _ _ below _ => below)

include algebra in
/-- **The greatest-lower-bound rule keeps the relation within the groups**: both unknowns lowered to `g`. -/
theorem glbComparable_glb {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) {g : Head}
    (glbm : GlbMeets v g) (below : BelowPair S.R v.pl v.cl v.pr v.cr) (distinct : v.right ≠ v.left)
    (group : Fin Θ.arity → Nat) (together : group v.left = group v.right)
    (comparable : GlbComparable S.R Θ.raw group) :
    GlbComparable S.R (setFamAt (setFamAt Θ.raw v.left [v.pl] g) v.right [v.pr] g) group :=
  glbComparable_lowered algebra.trans (fun h => (S.levels.cumulative_universe h).1) S.levels.cumulative_refl
    together comparable v.declared_left v.declared_right
    ((lookup_setFamAt_ne _ v.right v.left [v.pr] g (fun same => distinct same.symm)).trans
      (lookup_setFamAt_self Θ.raw v.left [v.pl] g))
    (lookup_setFamAt_self _ v.right [v.pr] g)
    (fun Z zx zy => (lookup_setFamAt_ne _ v.right Z [v.pr] g zy).trans (lookup_setFamAt_ne Θ.raw v.left Z [v.pl] g zx))
    glbm.2.1 (glbm.1.2.2.2 v.pl v.universe_pl below.2.1 below.2.2.1)
    (glbm.1.2.2.2 v.pr v.universe_pr below.2.2.2.1 below.2.2.2.2) glbm.1.2.1 glbm.1.2.2.1 glbm.1.2.2.2

variable [DecidableEq Head] [DecidableRel S.R.cumulative]

/-- **Domain raising keeps the fragment.** -/
theorem inGlbFragment_raise {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e) (all : AllFamilies Θ)
    {rest : EquationStore (TotalTerm Θ)} (shapes : ∀ e' ∈ rest, Nonempty (FitFlex e')) (group : Fin Θ.arity → Nat)
    (grouped : ∀ e' ∈ rest, ∀ w : FitFlex e', group w.left = group w.right) (together : group v.F = group v.G)
    (comparable : GlbComparable S.R Θ.raw group) : InGlbFragment (contractStore algebra v all rest) := by
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

/-- **The true meet keeps the fragment.** -/
theorem inGlbFragment_meet {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) (meets : Meets v)
    (distinct : v.right ≠ v.left) (all : AllFamilies Θ) {rest : EquationStore (TotalTerm Θ)}
    (shapes : ∀ e' ∈ rest, Nonempty (FitFlex e')) (group : Fin Θ.arity → Nat)
    (grouped : ∀ e' ∈ rest, ∀ w : FitFlex e', group w.left = group w.right) (together : group v.left = group v.right)
    (comparable : GlbComparable S.R Θ.raw group) :
    InGlbFragment (contractStore algebra (meetFits v meets distinct) (lowered_families v meets all)
      ((frames S.levels).applyStore (lowerHom Θ v meets) rest)) := by
  refine inGlbFragment_raise algebra (meetFits v meets distinct) (lowered_families v meets all) ?_ group ?_
    together.symm (glbComparable_meet algebra v meets distinct group together comparable)
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

/-- **The greatest-lower-bound rule keeps the fragment.** -/
theorem inGlbFragment_glb {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) {g : Head}
    (glbm : GlbMeets v g) (below : BelowPair S.R v.pl v.cl v.pr v.cr) (distinct : v.right ≠ v.left)
    (all : AllFamilies Θ) {rest : EquationStore (TotalTerm Θ)} (shapes : ∀ e' ∈ rest, Nonempty (FitFlex e'))
    (group : Fin Θ.arity → Nat) (grouped : ∀ e' ∈ rest, ∀ w : FitFlex e', group w.left = group w.right)
    (together : group v.left = group v.right) (comparable : GlbComparable S.R Θ.raw group) :
    InGlbFragment (contractStore algebra (glbFits algebra v glbm distinct)
      ((glbLowerRight v glbm distinct).families ((glbLowerLeft v glbm).families all))
      ((frames S.levels).applyStore (glbLowerRight v glbm distinct).hom
        ((frames S.levels).applyStore (glbLowerLeft v glbm).hom rest))) := by
  have twice : ∀ e'' ∈ (frames S.levels).applyStore (glbLowerRight v glbm distinct).hom
      ((frames S.levels).applyStore (glbLowerLeft v glbm).hom rest),
      ∃ e' ∈ rest, ∃ w : FitFlex e', ∃ t : FitFlex e'', t.left = w.left ∧ t.right = w.right := by
    intro e'' member
    obtain ⟨e₁, member₁, rfl⟩ := List.mem_map.mp member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member₁
    obtain ⟨w⟩ := shapes e' inRest
    obtain ⟨t₁, l₁, r₁⟩ := lowering_view algebra (glbLowerLeft v glbm) w
    obtain ⟨t₂, l₂, r₂⟩ := lowering_view algebra (glbLowerRight v glbm distinct) t₁
    exact ⟨e', inRest, w, t₂, l₂.trans l₁, r₂.trans r₁⟩
  refine inGlbFragment_raise algebra (glbFits algebra v glbm distinct) _ ?_ group ?_ together.symm
    (glbComparable_glb algebra v glbm below distinct group together comparable)
  · intro e'' member
    obtain ⟨_, _, _, t, _, _⟩ := twice e'' member
    exact ⟨t⟩
  · intro e'' member u
    obtain ⟨e', inRest, w, t, tl, tr⟩ := twice e'' member
    obtain ⟨ul, ur⟩ := FitFlex.unique u t
    rw [ul, ur, tl, tr]
    exact grouped e' inRest w

end Fragment

/-! ## The solver -/

section Solver

instance (R : Rules Head) [DecidableEq Head] [DecidableRel R.cumulative] (g p d c : Head) :
    Decidable (LowersTo R g p d c) := by
  unfold LowersTo
  infer_instance

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (glb : Head → Head → Option Head) (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)

/-- **The greatest-lower-bound rule on a read equation**, at `g = glb cA cB`, in either orientation, when its
conditions hold. -/
def glbBranch {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ) (v : FitFlex e)
    (distinct : v.right ≠ v.left) (rest : EquationStore (TotalTerm Θ)) : Round S.levels storeRank (e :: rest) :=
  match hg : glb v.cl v.cr with
  | some g =>
      if hl : S.R.cumulative v.pl v.pr ∧ LowersTo S.R g v.p v.pl v.cl ∧ LowersTo S.R g v.p v.pr v.cr then
        .progress (glbMeetUpdate facts roots heads algebra rigid complete headTypingUnique v
            ⟨spec hg, hl.1, hl.2.1, hl.2.2⟩ distinct all rest)
          (below_of_length (by
            show (contractStore algebra _ _ ((frames S.levels).applyStore _
              ((frames S.levels).applyStore _ rest))).length < (e :: rest).length
            simp [contractStore, Frames.applyStore]))
      else if hr : S.R.cumulative v.pr v.pl ∧ LowersTo S.R g v.p v.pr v.cr ∧ LowersTo S.R g v.p v.pl v.cl then
        .progress ((glbMeetUpdate facts roots heads algebra rigid complete headTypingUnique v.swap
            ⟨(spec hg).symm, hr.1, hr.2.1, hr.2.2⟩ (fun same => distinct same.symm) all rest).rephrase
              (swap_equivalent e rest))
          (below_of_length (by
            show (contractStore algebra _ _ ((frames S.levels).applyStore _
              ((frames S.levels).applyStore _ rest))).length < (e :: rest).length
            simp [contractStore, Frames.applyStore]))
      else .stuck
  | none => .stuck

/-- **One step on a read equation**: delete, raise in either orientation, the true meet in either orientation, the
greatest-lower-bound rule in either orientation, or stuck. -/
def stepGlbGroup {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ) (v : FitFlex e)
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
  else glbBranch facts roots heads algebra rigid complete headTypingUnique glb spec all v (fun h => hsame h.symm) rest

/-- **The round of the solver**: read the first equation, then step. -/
def glbGroupRound : {Γ : Context S.R} → (problem : EquationStore (TotalTerm Γ)) → Round S.levels storeRank problem
  | _, [] => .stuck
  | Θ, e :: rest =>
      if hall : allFamiliesB Θ = true then
        match hd : readFitData e with
        | some _ => stepGlbGroup facts roots heads algebra rigid complete headTypingUnique glb spec
            (allFamilies_of_B hall) (viewOfFit hd) rest
        | none => .stuck
      else .stuck

/-- **The tree's driver with delete, domain raising, the true meet and the greatest-lower-bound rule.** -/
def glbGroupSolver : ContextualDependentWorklist.Solver S.levels where
  rank := storeRank
  round := glbGroupRound facts roots heads algebra rigid complete headTypingUnique glb spec

omit [∀ head, Decidable (S.R.isUniverse head)] in
theorem glbBranch_ne_refuted {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ)
    (v : FitFlex e) (distinct : v.right ≠ v.left) (rest : EquationStore (TotalTerm Θ))
    (absent : ¬ (frames S.levels).Solvable (e :: rest)) :
    glbBranch facts roots heads algebra rigid complete headTypingUnique glb spec all v distinct rest ≠
      .refuted absent := by
  unfold glbBranch
  split
  · split_ifs <;> intro h <;> cases h
  · intro h
    cases h

omit [∀ head, Decidable (S.R.isUniverse head)] in
theorem stepGlbGroup_ne_refuted {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ)
    (v : FitFlex e) (rest : EquationStore (TotalTerm Θ)) (absent : ¬ (frames S.levels).Solvable (e :: rest)) :
    stepGlbGroup facts roots heads algebra rigid complete headTypingUnique glb spec all v rest ≠ .refuted absent := by
  unfold stepGlbGroup
  split_ifs
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · exact glbBranch_ne_refuted facts roots heads algebra rigid complete headTypingUnique glb spec all v _ rest absent

/-- **The rules never refute.** -/
theorem glbGroupRound_ne_refuted {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ))
    (absent : ¬ (frames S.levels).Solvable problem) :
    glbGroupRound facts roots heads algebra rigid complete headTypingUnique glb spec problem ≠ .refuted absent := by
  cases problem with
  | nil => intro h; cases h
  | cons e rest =>
      simp only [glbGroupRound]
      split_ifs with hall
      · split
        · exact stepGlbGroup_ne_refuted facts roots heads algebra rigid complete headTypingUnique glb spec _ _ rest
            absent
        · intro h; cases h
      · intro h; cases h

variable (total : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g)

omit [∀ head, Decidable (S.R.isUniverse head)] in
include total in
/-- **On views below each other the greatest-lower-bound rule applies**: both domains lie below `g`. -/
theorem glbBranch_ne_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ) (v : FitFlex e)
    (distinct : v.right ≠ v.left) (rest : EquationStore (TotalTerm Θ)) (below : BelowPair S.R v.pl v.cl v.pr v.cr) :
    glbBranch facts roots heads algebra rigid complete headTypingUnique glb spec all v distinct rest ≠ .stuck := by
  unfold glbBranch
  split
  · rename_i g hg
    have greatest := (spec hg).2.2.2
    have gl : S.R.cumulative v.pl g := greatest v.pl v.universe_pl below.2.1 below.2.2.1
    have gr : S.R.cumulative v.pr g := greatest v.pr v.universe_pr below.2.2.2.1 below.2.2.2.2
    split_ifs with hl hr
    · intro h; cases h
    · intro h; cases h
    · rcases below.1 with d | d
      · exact (hl ⟨d, Or.inr (Or.inr gl), Or.inr (Or.inr gr)⟩).elim
      · exact (hr ⟨d, Or.inr (Or.inr gr), Or.inr (Or.inr gl)⟩).elim
  · rename_i hg
    obtain ⟨g, found⟩ := total v.universe_cl v.universe_cr
    rw [hg] at found
    cases found

omit [∀ head, Decidable (S.R.isUniverse head)] in
include total in
theorem stepGlbGroup_ne_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ)
    (v : FitFlex e) (rest : EquationStore (TotalTerm Θ))
    (decided : v.left = v.right ∨ GlbCompat S.R v.pl v.cl v.pr v.cr) :
    stepGlbGroup facts roots heads algebra rigid complete headTypingUnique glb spec all v rest ≠ .stuck := by
  unfold stepGlbGroup
  split_ifs with h1 h2 h3 h4 h5
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · rcases decided with same | compat
    · exact absurd same h1
    · exact glbBranch_ne_stuck facts roots heads algebra rigid complete headTypingUnique glb spec total all v _ rest
        (below_of_not_compat compat h2 h3 h4 h5)

include total in
/-- **Progress by shape**: on a nonempty store of the fragment, the round is not stuck. -/
theorem glbGroupRound_ne_stuck {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (inside : InGlbFragment problem) (nonempty : problem ≠ []) :
    glbGroupRound facts roots heads algebra rigid complete headTypingUnique glb spec problem ≠ .stuck := by
  cases problem with
  | nil => exact absurd rfl nonempty
  | cons e rest =>
      obtain ⟨v⟩ := inside.shapes e List.mem_cons_self
      obtain ⟨group, grouped, comparable⟩ := inside.grouped
      have hall := allFamiliesB_of inside.families
      have hd := readFitData_complete v
      simp only [glbGroupRound, dif_pos hall]
      split
      · rename_i d hd'
        apply stepGlbGroup_ne_stuck facts roots heads algebra rigid complete headTypingUnique glb spec total
        let w := viewOfFit hd'
        by_cases same : w.left = w.right
        · exact Or.inl same
        · exact Or.inr (comparable w.left w.right same (grouped e List.mem_cons_self w) w.pl w.cl w.pr w.cr
            w.declared_left w.declared_right)
      · rename_i hd'
        rw [hd] at hd'
        cases hd'

/-- **The rules keep the fragment.** -/
theorem glbGroupRound_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (storeRank update.remaining) (storeRank problem)}
    (inside : InGlbFragment problem)
    (progressed : glbGroupRound facts roots heads algebra rigid complete headTypingUnique glb spec problem =
      .progress update smaller) :
    InGlbFragment update.remaining := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      obtain ⟨group, grouped, comparable⟩ := inside.grouped
      have restShapes : ∀ e' ∈ rest, Nonempty (FitFlex e') :=
        fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member)
      have restGrouped : ∀ e' ∈ rest, ∀ w : FitFlex e', group w.left = group w.right :=
        fun e' member => grouped e' (List.mem_cons_of_mem _ member)
      simp only [glbGroupRound] at progressed
      split_ifs at progressed with hall
      split at progressed
      · rename_i d hd
        unfold stepGlbGroup at progressed
        split_ifs at progressed with h1 h2 h3 h4 h5
        · cases progressed
          exact inGlbFragment_delete inside
        · cases progressed
          exact inGlbFragment_raise algebra _ (allFamilies_of_B hall) restShapes group restGrouped
            (grouped e List.mem_cons_self _).symm comparable
        · cases progressed
          exact inGlbFragment_raise algebra _ (allFamilies_of_B hall) restShapes group restGrouped
            (grouped e List.mem_cons_self _) comparable
        · cases progressed
          exact inGlbFragment_meet algebra (viewOfFit hd) h4 _ (allFamilies_of_B hall) restShapes group restGrouped
            (grouped e List.mem_cons_self _) comparable
        · cases progressed
          exact inGlbFragment_meet algebra (viewOfFit hd).swap h5 _ (allFamilies_of_B hall) restShapes group
            restGrouped (grouped e List.mem_cons_self _).symm comparable
        · have below : BelowPair S.R (viewOfFit hd).pl (viewOfFit hd).cl (viewOfFit hd).pr (viewOfFit hd).cr :=
            below_of_not_compat (comparable _ _ h1 (grouped e List.mem_cons_self _) _ _ _ _
              (viewOfFit hd).declared_left (viewOfFit hd).declared_right) h2 h3 h4 h5
          unfold glbBranch at progressed
          split at progressed
          · split_ifs at progressed with hl hr
            · cases progressed
              exact inGlbFragment_glb algebra (viewOfFit hd) _ below _ (allFamilies_of_B hall) restShapes group
                restGrouped (grouped e List.mem_cons_self _) comparable
            · cases progressed
              exact inGlbFragment_glb algebra (viewOfFit hd).swap _ below.symm _ (allFamilies_of_B hall) restShapes
                group restGrouped (grouped e List.mem_cons_self _).symm comparable
          · cases progressed
      · cases progressed

/-- **The fragment of the solver.** -/
def glbGroupFragment :
    ContextualDependentWorklist.Fragment
      (glbGroupSolver facts roots heads algebra rigid complete headTypingUnique glb spec) where
  holds := InGlbFragment
  stable := fun inside progressed =>
    glbGroupRound_stable facts roots heads algebra rigid complete headTypingUnique glb spec inside progressed
  decisive := fun inside nonempty =>
    glbGroupRound_ne_stuck facts roots heads algebra rigid complete headTypingUnique glb spec total inside nonempty

include total in
/-- **Decided by shape**: on the fragment, the tree's driver with delete, domain raising, the true meet and the
greatest-lower-bound rule reaches, at some budget and at every larger one, a principal answer or a certified
refutation. -/
theorem glbGroup_decided {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InGlbFragment original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (glbGroupSolver facts roots heads algebra rigid complete headTypingUnique glb spec) original larger =
          run (glbGroupSolver facts roots heads algebra rigid complete headTypingUnique glb spec) original fuel ∧
        ((∃ state finished,
              run (glbGroupSolver facts roots heads algebra rigid complete headTypingUnique glb spec) original larger =
                .solved state finished ∧ (frames S.levels).Principal original state.answer) ∨
          (∃ absent,
            run (glbGroupSolver facts roots heads algebra rigid complete headTypingUnique glb spec) original larger =
              .refuted absent)) :=
  (glbGroupFragment facts roots heads algebra rigid complete headTypingUnique glb spec total).decided inside

include facts roots heads algebra rigid complete headTypingUnique spec total in
/-- **Every store of the fragment has a principal answer.** -/
theorem principal_of_inGlbFragment {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InGlbFragment original) :
    ∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), (frames S.levels).Principal original answer := by
  obtain ⟨fuel, ends⟩ :=
    glbGroup_decided facts roots heads algebra rigid complete headTypingUnique glb spec total inside
  rcases (ends fuel le_rfl).2 with ⟨state, _, _, principal⟩ | ⟨absent, refuted⟩
  · exact ⟨_, _, principal⟩
  · exact absurd refuted (drive_ne_refuted
      (glbGroupSolver facts roots heads algebra rigid complete headTypingUnique glb spec)
      (fun problem absent =>
        glbGroupRound_ne_refuted facts roots heads algebra rigid complete headTypingUnique glb spec problem absent)
      fuel _ absent)

end Solver

/-! ## Membership, decided -/

section Membership

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- Of two different declared unary families, the views are compatible or below each other, decided. -/
def glbComparableB {n : Nat} (Γ : Ctx Head n) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    if i = j then true else
    match readFam (Ctx.lookup Γ i), readFam (Ctx.lookup Γ j) with
    | some a, some b =>
        match a.1, b.1 with
        | [pi], [pj] => decide (GlbCompat S.R pi a.2 pj b.2)
        | _, _ => true
    | _, _ => true

omit [∀ head, Decidable (S.R.isUniverse head)] in
theorem glbComparable_of_B {n : Nat} {Γ : Ctx Head n} (h : glbComparableB (S := S) Γ = true) :
    GlbComparable S.R Γ (fun _ => 0) := by
  intro i j ne _ pi ci pj cj hi hj
  have hij := List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_finRange i)) j (List.mem_finRange j)
  rw [if_neg ne, hi, hj, readFam_famCode, readFam_famCode] at hij
  exact of_decide_eq_true hij

/-- **Membership in the fragment, decided**, with all unknowns in one group. -/
def inGlbFragmentB {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Bool :=
  allFamiliesB Θ && problem.all (fun e => (readFitData e).isSome) && glbComparableB (S := S) Θ.raw

theorem inGlbFragment_of_B {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (h : inGlbFragmentB problem = true) : InGlbFragment problem := by
  simp only [inGlbFragmentB, Bool.and_eq_true] at h
  obtain ⟨⟨hall, hshapes⟩, hcomp⟩ := h
  refine ⟨allFamilies_of_B hall, fun e member => ?_, ⟨fun _ => 0, fun _ _ _ => rfl, glbComparable_of_B hcomp⟩⟩
  have he := List.all_eq_true.mp hshapes e member
  cases hd : readFitData e with
  | none => rw [hd] at he; cases he
  | some d => exact ⟨viewOfFit hd⟩

end Membership

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
