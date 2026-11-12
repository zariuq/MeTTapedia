import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentHeadView
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusReadsSigma

/-!
# Every census head has two views, and the rows read by shape

**The opened sides of a census head have views** (`census_views`). The η-long opened sides of an equation with normal
codes and equal annotations are typed (`openNormal_typed`) and normal, so by canonical forms each has a view. The
classification `ContextualDependentHeadView.classify` therefore applies to every census head: a census head is in
one of its seventeen rows, whatever its shape.

**Rows read, stated on the views.**

* `ClashRow`: two neutrals whose heads are fixed under the opening's binders (bound locals or constants) with
  different skeletons: different heads, or eliminations of different shapes. Such a head is refuted by the skeleton
  clash rule (`clashRow_covered`). The rows `headClash` and `shapeClash` of the classification are of this shape
  (`clashRow_of_classify`).
* `SpineRow`: two neutrals of one bound local under applications only, as many on both sides and at least one, or
  under such applications and one more projection, the same on both sides. At a base type as it stands such a head is
  read by the decomposition at every base type (`spineRow_covered`).

**A conditional decision, with the hypothesis on views** (`tower_base_decided_of_rows`). The base family decides every
store of the fragment provided every census head of a constant preparation is read whose two views are in neither row
above and which no other row read covers. Compared with `tower_base_decided_of_uncovered`, the hypothesis hands over
the two views, so a proof of it could proceed by the classification's pattern matching, and it excludes the two rows
by shape; the rows read by the executable readings of formers and pairs are excluded through `CensusCoveredHead`, not
by shape. At the tower the hypothesis fails: the conclusion would decide `crossStore`, solvable and without principal
answer (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). For every store, runs are exact; on
`crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentRank ContextualDependentSpinesMany ContextualDependentCoverageReadersHalf
open ContextualDependentConstantHeads ContextualDependentMillerClosure
open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls
open ContextualDependentAcceptance4
open ContextualDependentHeadView
open ContextualDependentCensus (openNormal)
open ContextualDependentPatternSolver (lamDepth)

section Shapes

variable {Head : Type}

/-- The elimination of a skeleton, from the shape of an elimination. -/
def toElim : ElimShape → Elim
  | .app => .app
  | .fst => .fst
  | .snd => .snd

theorem toElim_injective : Function.Injective toElim := by
  intro first second same
  cases first <;> cases second <;> first | rfl | cases same

/-- Applications only are an application spine. -/
theorem eliminate_apps {n : Nat} : ∀ (arguments : List (Tm Head n)) (head : Tm Head n),
    eliminate head (arguments.map Elimination.app) = appSpine head arguments
  | [], _ => rfl
  | argument :: rest, head => eliminate_apps rest (.app head argument)

theorem fixedSkeleton_apply (depth : Nat) {n : Nat} (elimination : Elimination Head n) (code : Tm Head n) :
    fixedSkeleton depth (elimination.apply code) =
      (fixedSkeleton depth code).map fun s => (s.1, toElim elimination.shape :: s.2) := by
  cases elimination <;> rfl

/-- The skeleton of a head under eliminations. -/
theorem fixedSkeleton_eliminate (depth : Nat) {n : Nat} : ∀ (eliminations : List (Elimination Head n))
    (head : Tm Head n), fixedSkeleton depth (eliminate head eliminations) =
      (fixedSkeleton depth head).map fun s => (s.1, ((shapes eliminations).map toElim).reverse ++ s.2)
  | [], head => by
      cases found : fixedSkeleton depth head <;> simp [eliminate, shapes, found]
  | elimination :: rest, head => by
      rw [eliminate, fixedSkeleton_eliminate depth rest, fixedSkeleton_apply]
      cases fixedSkeleton depth head <;> simp [shapes]

/-- **The skeleton of a neutral view whose head is fixed under `depth` binders**: a bound local or a constant, with
the shapes of its eliminations, outermost first. -/
def rigidSkeleton (depth : Nat) {n : Nat} : View Head n → Option Skeleton
  | .neutral index eliminations =>
      if index.val < depth then some (.local index.val, ((shapes eliminations).map toElim).reverse) else none
  | .constant name eliminations => some (.const name, ((shapes eliminations).map toElim).reverse)
  | .lam _ | .pair _ _ | .refl _ | .pi _ _ | .sigma _ _ | .id _ _ _ | .sort _ => none

theorem fixedSkeleton_code (depth : Nat) {n : Nat} (view : View Head n) :
    fixedSkeleton depth view.code = rigidSkeleton depth view := by
  cases view with
  | neutral index eliminations =>
      simp only [View.code, fixedSkeleton_eliminate, fixedSkeleton, rigidSkeleton]
      split <;> simp
  | constant name eliminations => simp [View.code, fixedSkeleton_eliminate, fixedSkeleton, rigidSkeleton]
  | lam _ | pair _ _ | refl _ | pi _ _ | sigma _ _ | id _ _ _ | sort _ => rfl

/-- **The clash row**: two neutrals with heads fixed under the binders and different skeletons. -/
def ClashRow (depth : Nat) {n : Nat} (left right : View Head n) : Prop :=
  ∃ s s', rigidSkeleton depth left = some s ∧ rigidSkeleton depth right = some s' ∧ s ≠ s'

/-- **The spine row**: two neutrals of one bound local under applications only, as many on both sides and at least
one, or under such applications and one more projection, the same on both sides. -/
def SpineRow (depth : Nat) {n : Nat} (left right : View Head n) : Prop :=
  ∃ (index : Fin n) (as bs : List (Tm Head n)), index.val < depth ∧ as ≠ [] ∧ as.length = bs.length ∧
    ((left = .neutral index (as.map Elimination.app) ∧ right = .neutral index (bs.map Elimination.app)) ∨
      ∃ first : Bool,
        left = .neutral index (as.map Elimination.app ++ [if first then .fst else .snd]) ∧
        right = .neutral index (bs.map Elimination.app ++ [if first then .fst else .snd]))

/-- **The rows `headClash` and `shapeClash` between two bound locals are the clash row.** -/
theorem clashRow_of_classify [DecidableEq Head] {n depth : Nat} {i j : Fin n}
    {left right : List (Elimination Head n)} (rigidLeft : i.val < depth) (rigidRight : j.val < depth)
    (row : classify (openedFlexible depth) (.neutral i left) (.neutral j right) = .headClash ∨
      classify (openedFlexible depth) (.neutral i left) (.neutral j right) = .shapeClash) :
    ClashRow depth (View.neutral i left) (View.neutral j right) := by
  have rigid : openedFlexible depth i = false := by
    simp only [openedFlexible, decide_eq_false_iff_not]
    omega
  refine ⟨(.local i.val, ((shapes left).map toElim).reverse), (.local j.val, ((shapes right).map toElim).reverse),
    by simp [rigidSkeleton, rigidLeft], by simp [rigidSkeleton, rigidRight], fun same => ?_⟩
  obtain ⟨heads, tails⟩ := Prod.mk.inj same
  obtain rfl : i = j := Fin.ext (SpineHead.local.inj heads)
  have sameShapes : shapes left = shapes right :=
    (List.map_injective_iff.mpr toElim_injective) (List.reverse_injective tails)
  simp [classify, rigid, rigidRow, sameShapes] at row

/-- **A skeleton clash of the opened sides is a skeleton clash of the equation**, when both sides and the annotation
have at least the opening's depth of abstractions and Π binders. -/
theorem skeletonClash_of_opened {n d : Nat} {annotation left right : Tm Head n}
    (typeDepth : d ≤ piCount annotation) (leftDepth : d ≤ lamDepth left) (rightDepth : d ≤ lamDepth right)
    (clash : SkeletonClash d (piOpen d annotation) (openNormal d left) (openNormal d right)) :
    SkeletonClash 0 annotation left right := by
  suffices every : ∀ j k, k + j = d →
      SkeletonClash k (piOpen k annotation) (openNormal k left) (openNormal k right) from every d 0 (by omega)
  intro j
  induction j with
  | zero =>
      intro k same
      obtain rfl : k = d := by omega
      exact clash
  | succ j ih =>
      intro k same
      have inner := ih (k + 1) (by omega)
      obtain ⟨D, typeCode⟩ := piOpen_pi (code := annotation) (count := k) (by omega)
      rw [typeCode, openNormal_lam (code := left) (count := k) (by omega),
        openNormal_lam (code := right) (count := k) (by omega)]
      exact .bind inner

end Shapes

section Typed

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **The opened side of a typed code is typed**, over some formed context, when the code has at least the opening's
depth of abstractions. -/
theorem openNormal_typed : ∀ (count : Nat) {n : Nat} {Γ : Ctx Head n} {code type : Tm Head n},
    CtxFormed S.R Γ → TypedEquality.Typed S.R Γ code type → count ≤ lamDepth code →
      ∃ (Δ : Ctx Head (n + count)) (opened : Tm Head (n + count)),
        CtxFormed S.R Δ ∧ TypedEquality.Typed S.R Δ (openNormal count code) opened
  | 0, _, Γ, _, type, formed, typed, _ => ⟨Γ, type, formed, typed⟩
  | count + 1, _, _, code, _, formed, typed, deep => by
      obtain ⟨Δ, opened, formedΔ, typedΔ⟩ := openNormal_typed count formed typed (by omega)
      rw [openNormal_lam (code := code) (count := count) (by omega)] at typedΔ
      obtain ⟨domain, codomain, level, function, isLevel, body, _⟩ := typedΔ.generation
      exact ⟨.snoc Δ domain, codomain, .snoc formedΔ (IsType.pi_parts ⟨level, isLevel, function⟩).1, body⟩

end Typed

/-! ## The tower -/

/-- **The η-long opened sides of an equation with normal codes and equal annotations have views.** -/
theorem census_views {Γ : Context setting.R} (equation : Equation (TotalTerm Γ))
    (normal : ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation)
    (types : TypeEq setting.R Γ.raw equation.1.1.code equation.2.1.code) :
    ∃ left right : View Tower.Head (Γ.arity + piCount equation.1.1.code),
      view? (openNormal (piCount equation.1.1.code) (expandTo (piCount equation.1.1.code) equation.1.2.code)) =
          some left ∧
        view? (openNormal (piCount equation.1.1.code) (expandTo (piCount equation.1.1.code) equation.2.2.code)) =
          some right := by
  have empty := ContextualDependentMillerClosure.computation_empty ContextualDependentPiSpine.Controls.rigid
  obtain ⟨typedLeft, typedRight⟩ := expanded_typed equation types
  obtain ⟨_, _, formedLeft, openedLeft⟩ :=
    openNormal_typed (S := setting) _ Γ.formed typedLeft (lamDepth_expandTo _ _)
  obtain ⟨_, _, formedRight, openedRight⟩ :=
    openNormal_typed (S := setting) _ Γ.formed typedRight (lamDepth_expandTo _ _)
  obtain ⟨left, foundLeft⟩ := view_of_typed_normal (S := setting) TowerModel.facts formedLeft openedLeft
    (ContextualDependentCensus.openNormal_normal empty (normal_expandTo empty _ normal.2.1) _)
  obtain ⟨right, foundRight⟩ := view_of_typed_normal (S := setting) TowerModel.facts formedRight openedRight
    (ContextualDependentCensus.openNormal_normal empty (normal_expandTo empty _ normal.2.2.2) _)
  exact ⟨left, right, foundLeft, foundRight⟩

/-- **A census head in the clash row is in a row read**: the skeleton clash rule refutes it. -/
theorem clashRow_covered {Γ : Context setting.R} {equation : Equation (TotalTerm Γ)}
    {left right : View Tower.Head (Γ.arity + piCount equation.1.1.code)}
    (foundLeft : view? (openNormal (piCount equation.1.1.code)
      (expandTo (piCount equation.1.1.code) equation.1.2.code)) = some left)
    (foundRight : view? (openNormal (piCount equation.1.1.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)) = some right)
    (clash : ClashRow (piCount equation.1.1.code) left right) : CensusCoveredHead equation := by
  obtain ⟨s, s', skeletonLeft, skeletonRight, differ⟩ := clash
  refine .inl (.inl (.inl (.inr (.inr ?_))))
  refine skeletonClash_of_opened le_rfl (lamDepth_expandTo _ _) (lamDepth_expandTo _ _) (.base ?_ ?_ differ)
  · rw [← view?_code foundLeft, fixedSkeleton_code]
    exact skeletonLeft
  · rw [← view?_code foundRight, fixedSkeleton_code]
    exact skeletonRight

/-- **A census head in the spine row at a base type as it stands is in a row read**: the decomposition at every base
type reads it. -/
theorem spineRow_covered {Γ : Context setting.R} {equation : Equation (TotalTerm Γ)}
    {left right : View Tower.Head (Γ.arity + piCount equation.1.1.code)}
    (foundLeft : view? (openNormal (piCount equation.1.1.code)
      (expandTo (piCount equation.1.1.code) equation.1.2.code)) = some left)
    (foundRight : view? (openNormal (piCount equation.1.1.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)) = some right)
    (base : anyBase (piOpen (piCount equation.1.1.code) equation.1.1.code) = true)
    (spines : SpineRow (piCount equation.1.1.code) left right) : CensusCoveredHead equation := by
  obtain ⟨index, as, bs, bound, nonempty, same, shape⟩ := spines
  refine .inl (.inr ?_)
  refine anySpines_of_opened le_rfl (lamDepth_expandTo _ _) (lamDepth_expandTo _ _) ?_
  rw [← view?_code foundLeft, ← view?_code foundRight]
  rcases shape with ⟨rfl, rfl⟩ | ⟨first, rfl, rfl⟩
  · simp only [View.code, eliminate_apps]
    exact .base base bound nonempty same
  · simp only [View.code, eliminate_snoc, eliminate_apps]
    cases first
    · exact .proj (first := false) base bound nonempty same
    · exact .proj (first := true) base bound nonempty same

/-- **Conditional decision for the tower's base family, with the hypothesis on views**: if every census head of a
constant preparation is read whose η-long opened sides have views outside the clash row and, at a base type as it
stands, outside the spine row, and which is outside the rows read, then the family decides every store of the dynamic
pattern fragment, with a principal answer or a certified refutation, constant at every larger budget. At the tower the
hypothesis fails: the conclusion would decide `crossStore`
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`,
`ContextualDependentSweep.Witnesses.acceptance_conclusion_false`). For every store, runs are exact; on `crossStore`
they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_base_decided_of_rows
    (rows : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)},
      PermutedMiller setting.levels problem → problem ≠ [] → ∀ threshold,
        (∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem) →
        ∀ equation ∈ (towerPrepare threshold problem).remaining,
          ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation → CensusHead equation →
          ContextualDependentShortClosure.FragmentSidesMiller equation →
          ∀ left right : View Tower.Head ((towerPrepare threshold problem).target.arity + piCount equation.1.1.code),
            view? (openNormal (piCount equation.1.1.code)
              (expandTo (piCount equation.1.1.code) equation.1.2.code)) = some left →
            view? (openNormal (piCount equation.1.1.code)
              (expandTo (piCount equation.1.1.code) equation.2.2.code)) = some right →
            ¬ ClashRow (piCount equation.1.1.code) left right →
            ¬ (anyBase (piOpen (piCount equation.1.1.code) equation.1.1.code) = true ∧
              SpineRow (piCount equation.1.1.code) left right) →
            ¬ CensusCoveredHead equation → ∃ bound, ∀ larger, bound ≤ larger → TowerBaseReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (baseTower.solver larger) problem larger = run (baseTower.solver budget) problem budget ∧
      ((∃ state finished, run (baseTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (baseTower.solver larger) problem larger = .refuted absent)) :=
  tower_base_decided_of_uncovered
    (fun permuted nonempty threshold constant equation member normal head sides _ uncovered => by
      obtain ⟨left, right, foundLeft, foundRight⟩ := census_views equation normal head.1
      exact rows permuted nonempty threshold constant equation member normal head sides left right foundLeft
        foundRight (fun clash => uncovered (clashRow_covered foundLeft foundRight clash))
        (fun spines => uncovered (spineRow_covered foundLeft foundRight spines.1 spines.2)) uncovered)
    inside

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
