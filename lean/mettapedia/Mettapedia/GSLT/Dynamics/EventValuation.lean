import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.Dynamics.QueryRevision
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Nat

/-!
# Indexed valuations of revision events

Evidence, execution work, latency, energy, and authority can all decorate the
same semantic event graph, but they need not share one total algebra.  This
module attaches the existing GSLT `PartialMonoid` to query/revision events.

The separation is intentional:

* a commuting square is behavioral permission;
* a successful partial merge is resource permission;
* parallelizability requires both.

The partial operation accommodates linear or unavailable capabilities, while
ordinary additive quantities use the total additive instance below.
-/

namespace Mettapedia.GSLT.Dynamics.EventValuation

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics.QueryRevision

universe uGrade uLeft uRight

/-- One algebra-indexed valuation of the revision events of a theory. -/
structure Valuation (theory : Theory) where
  Grade : Type uGrade
  algebra : PartialMonoid Grade
  grade : theory.Revision → Option Grade

namespace Valuation

/-- Combine two independently chosen event valuations.  The resulting grade
retains both components, and a merge succeeds only when both partial algebras
accept it. -/
def prod {theory : Theory}
    (left : Valuation.{uLeft} theory) (right : Valuation.{uRight} theory) :
    Valuation theory where
  Grade := left.Grade × right.Grade
  algebra := left.algebra.prod right.algebra
  grade := fun revision =>
    (left.grade revision).bind fun leftGrade =>
      (right.grade revision).bind fun rightGrade =>
        some (leftGrade, rightGrade)

/-- Fold a chronological event history through its declared partial algebra. -/
def historyGrade {theory : Theory} (valuation : Valuation theory) :
    List theory.Revision → Option valuation.Grade :=
  valuation.algebra.foldOption valuation.grade

@[simp] theorem historyGrade_nil {theory : Theory}
    (valuation : Valuation theory) :
    valuation.historyGrade [] = some valuation.algebra.unit :=
  rfl

@[simp] theorem historyGrade_cons {theory : Theory}
    (valuation : Valuation theory) (revision : theory.Revision)
    (revisions : List theory.Revision) :
    valuation.historyGrade (revision :: revisions) =
      (valuation.grade revision).bind fun head =>
        (valuation.historyGrade revisions).bind fun tail =>
          valuation.algebra.op head tail :=
  rfl

/-- History valuation is compositional under chronological concatenation. -/
theorem historyGrade_append {theory : Theory}
    (valuation : Valuation theory)
    (first second : List theory.Revision) :
    valuation.historyGrade (first ++ second) =
      (valuation.historyGrade first).bind fun left =>
        (valuation.historyGrade second).bind fun right =>
          valuation.algebra.op left right :=
  valuation.algebra.foldOption_append valuation.grade first second

/-- Attempt to combine the grades of two candidate concurrent events. -/
def combine? {theory : Theory} (valuation : Valuation theory)
    (first second : theory.Revision) : Option valuation.Grade := do
  let firstGrade ← valuation.grade first
  let secondGrade ← valuation.grade second
  valuation.algebra.op firstGrade secondGrade

/-- Resource compatibility is successful composition in the selected
valuation algebra. -/
def Compatible {theory : Theory} (valuation : Valuation theory)
    (first second : theory.Revision) : Prop :=
  (valuation.combine? first second).isSome

/-- Strong parallelizability requires a literal semantic square and resource
compatibility. -/
def StronglyParallelizable {theory : Theory} (valuation : Valuation theory)
    (first second : theory.Revision) (source : theory.World) : Prop :=
  theory.StronglyCoexecutible first second source ∧
    valuation.Compatible first second

/-- Observer-relative parallelizability permits distinct internal residuals
when the complete declared query profile agrees. -/
def QueryParallelizable {theory : Theory} (valuation : Valuation theory)
    (first second : theory.Revision) (source : theory.World) : Prop :=
  theory.QueryCoexecutible first second source ∧
    valuation.Compatible first second

/-- Every strong parallelization certificate is also valid at the complete
query profile. -/
theorem stronglyParallelizable_implies_queryParallelizable
    {theory : Theory} {valuation : Valuation theory}
    {first second : theory.Revision} {source : theory.World}
    (parallelizable :
      valuation.StronglyParallelizable first second source) :
    valuation.QueryParallelizable first second source :=
  ⟨theory.stronglyCoexecutible_implies_queryCoexecutible parallelizable.1,
    parallelizable.2⟩

/-- Componentwise compatibility grants compatibility of the product
valuation. -/
theorem prod_compatible {theory : Theory}
    (left : Valuation.{uLeft} theory) (right : Valuation.{uRight} theory)
    (first second : theory.Revision)
    (leftCompatible : left.Compatible first second)
    (rightCompatible : right.Compatible first second) :
    (left.prod right).Compatible first second := by
  cases leftFirst : left.grade first with
  | none => simp [Compatible, combine?, leftFirst] at leftCompatible
  | some leftFirstGrade =>
      cases leftSecond : left.grade second with
      | none =>
          simp [Compatible, combine?, leftFirst, leftSecond] at leftCompatible
      | some leftSecondGrade =>
          cases leftMerge : left.algebra.op leftFirstGrade leftSecondGrade with
          | none =>
              simp [Compatible, combine?, leftFirst, leftSecond, leftMerge]
                at leftCompatible
          | some leftMerged =>
              cases rightFirst : right.grade first with
              | none =>
                  simp [Compatible, combine?, rightFirst] at rightCompatible
              | some rightFirstGrade =>
                  cases rightSecond : right.grade second with
                  | none =>
                      simp [Compatible, combine?, rightFirst, rightSecond]
                        at rightCompatible
                  | some rightSecondGrade =>
                      cases rightMerge :
                          right.algebra.op rightFirstGrade rightSecondGrade with
                      | none =>
                          simp [Compatible, combine?, rightFirst, rightSecond,
                            rightMerge] at rightCompatible
                      | some rightMerged =>
                          simp [Compatible, combine?, prod,
                            Mettapedia.GSLT.PartialMonoid.prod,
                            leftFirst, leftSecond, leftMerge,
                            rightFirst, rightSecond, rightMerge]

end Valuation

/-! ## Total additive valuations -/

/-- Any additive monoid is a total instance of the partial composition
interface. -/
def additivePartialMonoid (Grade : Type uGrade) [AddMonoid Grade] :
    PartialMonoid Grade where
  unit := 0
  op := fun first second => some (first + second)
  unit_op := by simp
  op_unit := by simp
  op_assoc := by simp [add_assoc]

/-- Attach an ordinary additive grade to every event. -/
def additive {theory : Theory} {Grade : Type uGrade} [AddMonoid Grade]
    (grade : theory.Revision → Grade) : Valuation theory where
  Grade := Grade
  algebra := additivePartialMonoid Grade
  grade := fun revision => some (grade revision)

@[simp] theorem additive_combine {theory : Theory}
    {Grade : Type uGrade} [AddMonoid Grade]
    (grade : theory.Revision → Grade) (first second : theory.Revision) :
    (additive grade).combine? first second =
      some (grade first + grade second) :=
  rfl

theorem additive_compatible {theory : Theory}
    {Grade : Type uGrade} [AddMonoid Grade]
    (grade : theory.Revision → Grade) (first second : theory.Revision) :
    (additive grade).Compatible first second := by
  change (some (grade first + grade second)).isSome = true
  rfl

/-- Count revision events without assigning any backend-specific duration or
memory model. -/
def eventCount (theory : Theory) : Valuation theory :=
  additive (Grade := Nat) fun _ => 1

/-! ## Certified backend-specific parallel admission -/

/-- A backend may conservatively select a subset of query-preserving,
resource-compatible event pairs for parallel execution.  Backends share the
same semantic theory; they may differ in valuation and admitted plan set. -/
structure ParallelBackend (theory : Theory) where
  valuation : Valuation.{uGrade} theory
  Admits : theory.Revision → theory.Revision → theory.World → Prop
  sound : ∀ {first second source}, Admits first second source →
    valuation.QueryParallelizable first second source

namespace ParallelBackend

/-- Backend admission is always sound for the declared query profile. -/
theorem admitted_queryCoexecutible {theory : Theory}
    (backend : ParallelBackend.{uGrade} theory)
    {first second : theory.Revision} {source : theory.World}
    (admitted : backend.Admits first second source) :
    theory.QueryCoexecutible first second source :=
  (backend.sound admitted).1

/-- One backend has at least the parallel-plan inventory of another when it
admits every pair admitted by the other. -/
def Subsumes {theory : Theory}
    (more less : ParallelBackend.{uGrade} theory) : Prop :=
  ∀ {first second source}, less.Admits first second source →
    more.Admits first second source

end ParallelBackend

/-! ## Separating canary: behavior is not resource authority -/

namespace Canary

/-- Two no-op events commute semantically.  This deliberately tiny theory is
only a separating model for the resource obligation. -/
def noOpTheory : Theory where
  World := Unit
  Revision := Bool
  Query := Unit
  Observation := Unit
  Step := fun _ source target => target = source
  query := fun _ _ => ()

/-- Every pair of no-op events forms a literal semantic square. -/
def noOpSquare (first second : Bool) :
    noOpTheory.StrongSquare first second () where
  afterFirst := ()
  afterSecond := ()
  joined := ()
  firstFromSource := rfl
  secondFromSource := rfl
  secondAfterFirst := rfl
  firstAfterSecond := rfl

/-- `true` means an event claims one exclusive token.  Two claims cannot be
merged even when their state transitions commute. -/
def exclusiveClaimAlgebra : PartialMonoid Bool where
  unit := false
  op := fun first second =>
    if first && second then none else some (first || second)
  unit_op := by intro value; cases value <;> rfl
  op_unit := by intro value; cases value <;> rfl
  op_assoc := by
    intro first second third
    cases first <;> cases second <;> cases third <;> rfl

/-- Both no-op events claim the same exclusive resource class. -/
def exclusiveValuation : Valuation noOpTheory where
  Grade := Bool
  algebra := exclusiveClaimAlgebra
  grade := fun _ => some true

theorem exclusive_events_not_compatible (first second : Bool) :
    ¬ exclusiveValuation.Compatible first second := by
  simp [Valuation.Compatible, Valuation.combine?, exclusiveValuation,
    exclusiveClaimAlgebra]

/-- Behavioral commutation alone does not grant parallel resource authority. -/
theorem semantic_commutation_does_not_imply_resource_compatibility
    (first second : Bool) :
    noOpTheory.StronglyCoexecutible first second () ∧
      ¬ exclusiveValuation.Compatible first second :=
  ⟨⟨noOpSquare first second⟩,
    exclusive_events_not_compatible first second⟩

/-- Ordinary additive work accounting accepts the same commuting events. -/
def workValuation : Valuation noOpTheory :=
  eventCount noOpTheory

theorem work_events_parallelizable (first second : Bool) :
    workValuation.StronglyParallelizable first second () :=
  ⟨⟨noOpSquare first second⟩,
    additive_compatible (theory := noOpTheory) (Grade := Nat)
      (fun _ => 1) first second⟩

@[simp] theorem two_event_work_grade (first second : Bool) :
    workValuation.historyGrade [first, second] = some (2 : Nat) :=
  rfl

/-- A backend that admits every pair in the no-op theory. -/
def allPairsBackend : ParallelBackend noOpTheory where
  valuation := workValuation
  Admits := fun _ _ _ => True
  sound := by
    intro first second source _
    cases source
    exact work_events_parallelizable first second |>
      Valuation.stronglyParallelizable_implies_queryParallelizable

/-- A sound but conservative backend that admits only equal event classes. -/
def sameClassBackend : ParallelBackend noOpTheory where
  valuation := workValuation
  Admits := fun first second _ => first = second
  sound := by
    intro first second source _
    cases source
    exact work_events_parallelizable first second |>
      Valuation.stronglyParallelizable_implies_queryParallelizable

theorem allPairs_subsumes_sameClass :
    allPairsBackend.Subsumes sameClassBackend := by
  intro first second source _
  trivial

/-- A backend may serialize a behaviorally and resource-compatible pair; its
plan inventory is an implementation capability, not the language meaning. -/
theorem conservative_backend_rejects_commuting_pair :
    noOpTheory.QueryCoexecutible true false () ∧
      workValuation.Compatible true false ∧
      allPairsBackend.Admits true false () ∧
      ¬ sameClassBackend.Admits true false () := by
  exact
    ⟨noOpTheory.stronglyCoexecutible_implies_queryCoexecutible
        ⟨noOpSquare true false⟩,
      additive_compatible (theory := noOpTheory) (Grade := Nat)
        (fun _ => 1) true false,
      trivial,
      by simp [sameClassBackend]⟩

end Canary

end Mettapedia.GSLT.Dynamics.EventValuation
