import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPreparedTwins

/-!
# The census half of coverage: distinct rigid heads

`CensusHead` speaks of the normal forms of the two sides opened to the left side's depth `d`. On a census head with
normal codes those are the syntactic openings `openNormal d` (`CensusHead.opened`). The clash reader reads the closed
codes at depth 0 (`HeadClash S.R 0`). The two meet through the opened annotation `piOpen d`: when the right side has at
least `d` abstractions and the annotation at least `d` Π binders, a head clash of the opened sides at the opened
annotation is a head clash of the equation (`headClash_of_opened`), by one `HeadClash.bind` per binder.

**The census kind of distinct rigid heads**, at the depth where both sides and the annotation agree, splits by the
opened annotation and the opened sides:

* distinct skeletons at a rigid base (`tower_underReads_of_skeletons`);
* distinct type kinds at a universe, and reflexivity against a neutral term at an identity type: the other
  constructors of `HeadClash`, covered by `tower_underReads_of_openedClash`.

Each is read by R110's clash row on the prepared store with homogeneous twins from some budget on, so `UnderReads`
holds there (`tower_underReads_of_clash`).

Not every census head of this kind is of these rows. Distinct heads with one skeleton (`fst (g X)` against
`fst (g A)`), heads at a flexible base type, distinct formers of one kind at a universe, and pairs against neutral
terms are read by other readers. A right side with fewer abstractions than the left, or an annotation with more Π
binders than the left side's abstractions, is not read by the clash row at all: `ContextualDependentEtaDepthGap`
gives fragment stores of that shape on which the under-binder round is stuck.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCoverageReadersHalf

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentConstantHeads ContextualDependentDynamicFragment ContextualDependentCensus
open ContextualDependentExecutableJoin

section Opened

variable {Head : Type}

/-- The codomain of a Π type, read under its binder. -/
def piStep {n : Nat} : Tm Head n → Tm Head (n + 1)
  | .pi _ body => body
  | other => Presentation.rename wk other

/-- The annotation read under `count` of its leading Π binders. -/
def piOpen {n : Nat} : (count : Nat) → Tm Head n → Tm Head (n + count)
  | 0, code => code
  | count + 1, code => piStep (piOpen count code)

/-- The body of an abstraction, or the side applied to the fresh local. -/
def openStep {n : Nat} : Tm Head n → Tm Head (n + 1)
  | .lam body => body
  | other => .app (Presentation.rename wk other) (.var 0)

theorem openNormal_succ {n : Nat} (code : Tm Head n) (count : Nat) :
    openNormal (count + 1) code = openStep (openNormal count code) := by
  rw [openNormal]
  generalize openNormal count code = opened
  cases opened <;> rfl

theorem piOpen_piCount {n : Nat} (code : Tm Head n) :
    ∀ count, count ≤ piCount code → piCount (piOpen count code) + count = piCount code
  | 0, _ => rfl
  | count + 1, deep => by
      have inner := piOpen_piCount code count (by omega)
      change piCount (piStep (piOpen count code)) + (count + 1) = piCount code
      generalize piOpen count code = opened at inner ⊢
      cases opened
      case pi D B =>
        simp only [piStep, piCount] at inner ⊢
        omega
      all_goals
        simp only [piCount] at inner
        omega

theorem lamDepth_openNormal {n : Nat} (code : Tm Head n) :
    ∀ count, count ≤ ContextualDependentPatternSolver.lamDepth code →
      ContextualDependentPatternSolver.lamDepth (openNormal count code) + count =
        ContextualDependentPatternSolver.lamDepth code
  | 0, _ => rfl
  | count + 1, deep => by
      have inner := lamDepth_openNormal code count (by omega)
      rw [openNormal_succ]
      generalize openNormal count code = opened at inner ⊢
      cases opened
      case lam body =>
        simp only [openStep, ContextualDependentPatternSolver.lamDepth] at inner ⊢
        omega
      all_goals
        simp only [ContextualDependentPatternSolver.lamDepth] at inner
        omega

/-- Below its Π count, the opened annotation is a Π type whose codomain is the next opening. -/
theorem piOpen_pi {n : Nat} {code : Tm Head n} {count : Nat} (inside : count < piCount code) :
    ∃ D, piOpen count code = .pi D (piOpen (count + 1) code) := by
  have depth := piOpen_piCount code count (by omega)
  change ∃ D, piOpen count code = .pi D (piStep (piOpen count code))
  generalize piOpen count code = opened at depth ⊢
  cases opened
  case pi D B => exact ⟨D, rfl⟩
  all_goals
    simp only [piCount] at depth
    omega

/-- Below its abstraction depth, the opened side is an abstraction whose body is the next opening. -/
theorem openNormal_lam {n : Nat} {code : Tm Head n} {count : Nat}
    (inside : count < ContextualDependentPatternSolver.lamDepth code) :
    openNormal count code = .lam (openNormal (count + 1) code) := by
  have depth := lamDepth_openNormal code count (by omega)
  rw [openNormal_succ]
  generalize openNormal count code = opened at depth ⊢
  cases opened
  case lam body => rfl
  all_goals
    simp only [ContextualDependentPatternSolver.lamDepth] at depth
    omega

/-- **A head clash of the opened sides at the opened annotation is a head clash of the equation**, when both sides
and the annotation have at least the opening's depth of abstractions and Π binders. -/
theorem headClash_of_opened {R : Rules Head} {n d : Nat} {annotation left right : Tm Head n}
    (typeDepth : d ≤ piCount annotation) (leftDepth : d ≤ ContextualDependentPatternSolver.lamDepth left)
    (rightDepth : d ≤ ContextualDependentPatternSolver.lamDepth right)
    (clash : HeadClash R d (piOpen d annotation) (openNormal d left) (openNormal d right)) :
    HeadClash R 0 annotation left right := by
  suffices every : ∀ j k, k + j = d →
      HeadClash R k (piOpen k annotation) (openNormal k left) (openNormal k right) from every d 0 (by omega)
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

/-- **The census kind of the opened normal sides** of a census head with normal sides. -/
theorem CensusHead.opened [DecidableEq Head] {R : Rules Head} (empty : R.computation = RootComputation.empty)
    {Θ : Context R} {equation : Equation (TotalTerm Θ)} (head : CensusHead equation)
    (normalLeft : Normal R equation.1.2.code) (normalRight : Normal R equation.2.2.code) :
    Kind (openedFlexible (ContextualDependentPatternSolver.lamDepth equation.1.2.code))
      (openNormal (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code)
      (openNormal (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code) :=
  head.2 (openCode_star _ _) (openNormal_normal empty normalLeft _) (openCode_star _ _)
    (openNormal_normal empty normalRight _)

end Opened

section Tower

open ContextualDependentPatternFiring.Controls

/-- **The clash reader reads an equation of a constant preparation** whose sides clash at their heads: from some
budget on, R110's first row holds on the prepared store with homogeneous twins. -/
theorem tower_underReads_of_clash {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (clash : HeadClash setting.R 0 equation.1.1.code equation.1.2.code equation.2.2.code) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerUnderReads larger problem := by
  obtain ⟨bound, twins⟩ := tower_twins_keep constant member types (fun A l r => HeadClash setting.R 0 A l r) clash
  exact ⟨bound, fun larger enough => .full (.inl (.inl (.inl (twins larger enough))))⟩

/-- **Distinct rigid heads at the opened annotation are read**: a census head whose right side has at least the left
side's abstractions, whose annotation has at least as many Π binders, and whose opened sides clash at the opened
annotation, is read by the clash reader from some budget on. -/
theorem tower_underReads_of_openedClash {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining) (head : CensusHead equation)
    (typeDepth : ContextualDependentPatternSolver.lamDepth equation.1.2.code ≤ piCount equation.1.1.code)
    (rightDepth : ContextualDependentPatternSolver.lamDepth equation.1.2.code ≤
      ContextualDependentPatternSolver.lamDepth equation.2.2.code)
    (clash : HeadClash setting.R (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
      (piOpen (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.1.code)
      (openNormal (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code)
      (openNormal (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code)) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerUnderReads larger problem :=
  tower_underReads_of_clash constant member head.1 (headClash_of_opened typeDepth le_rfl rightDepth clash)

/-- **Distinct skeletons at a rigid base are read**: the skeleton row of the census kind of distinct rigid heads. -/
theorem tower_underReads_of_skeletons {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining) (head : CensusHead equation)
    (typeDepth : ContextualDependentPatternSolver.lamDepth equation.1.2.code ≤ piCount equation.1.1.code)
    (rightDepth : ContextualDependentPatternSolver.lamDepth equation.1.2.code ≤
      ContextualDependentPatternSolver.lamDepth equation.2.2.code)
    (base : ContextualDependentSpinesMany.rigidBase (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
      (piOpen (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.1.code) = true)
    {s s' : Skeleton}
    (leftSkeleton : fixedSkeleton (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
      (openNormal (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) = some s)
    (rightSkeleton : fixedSkeleton (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
      (openNormal (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code) = some s')
    (differ : s ≠ s') :
    ∃ bound, ∀ larger, bound ≤ larger → TowerUnderReads larger problem :=
  tower_underReads_of_openedClash constant member head typeDepth rightDepth
    (.base base leftSkeleton rightSkeleton differ)

end Tower

end ContextualDependentCoverageReadersHalf
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
