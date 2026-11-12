import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.DependentFibre
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.AbsenceNotCompositional
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CanonicalFirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullControls

/-!
# Four permanent acceptance tests

Each test is a law that a stronger theorem might be tempted to state, written as a proposition over
the tree's own objects, together with its refutation by a fixed witness and the weaker law that
does hold there. A theorem that claims more than the weaker law must exclude the witness by an
explicit hypothesis.

1. **A solvable store with no principal answer** (`principalLaw_fails`). On the dependent fibre,
   `crossStore` (`λx. X x ≐ λx. Y x` over `X : U0 → U0, Y : U1 → U1`) is in the dynamic pattern
   fragment and solvable, and has no principal answer. What holds: every exact solver that stops on
   it stops postponed, with an exact nonempty residual (`principal_test_postponed`).
2. **Absence against framing** (`frameLaw_fails`). On the first-order step, admission is not
   preserved by putting a store beside the configuration, even when the made identities are new to
   it and its knowledge is trivial: `spawn` (make `T` where `U` is absent) is admitted at the empty
   store and refused beside `U`. What holds: positive admission is monotone, and absence-guarded
   admission survives exactly when the added store has no match (`frame_test_graded`).
3. **Pairwise compatibility without a joint wave** (`waveLaw_fails`). On the first-order step, the
   tells `X ≐ Y`, `X ≐ 1`, `Y ≐ 2` are independent in pairs at the empty configuration, and no run
   fires all three in any order.
4. **Solvable without being inhabited** (`inhabitationLaw_fails`). On the dependent fibre, `x ≐ x`
   over `x : Ground` is solvable and has no closed solution. On the dependent full step itself, the
   firing that makes `x : X`, `g : Ground` and tells `(x : X) ≐ (g : Ground)` is admitted, and its
   information has no closed solution (`admitted_not_closed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ProgrammingOnTheStep.AcceptanceTests

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

/-! ## 1. A solvable store with no principal answer -/

section Principal

open ContextualDependentSweep.Witnesses ContextualDependentDynamicFragment

/-- The package of the cross store: the cumulative tower. -/
abbrev crossSetting := ContextualDependentPatternFiring.Controls.setting

/-- **The tempting law**: every solvable store of the dependent fibre has a principal answer. -/
def PrincipalLaw : Prop :=
  ∀ {Γ : Context crossSetting.R} (K : EquationStore (TotalTerm Γ)),
    (frames crossSetting.levels).Solvable K →
      ∃ (Δ : Context crossSetting.R) (σ : Δ ⟶ Γ), (frames crossSetting.levels).Principal K σ

/-- **Test 1**: the law fails at `crossStore`, a store of the dynamic pattern fragment. -/
theorem principalLaw_fails : InFragmentStore crossStore ∧ ¬ PrincipalLaw := by
  refine ⟨fragment_without_principal_answer.1, fun law => ?_⟩
  obtain ⟨_, σ, principal⟩ := law crossStore fragment_without_principal_answer.2.1
  exact fragment_without_principal_answer.2.2 σ principal

/-- **What holds at the test**: an exact solver that stops on `crossStore` stops postponed, with a
nonempty residual that keeps every solution, and is never refuted. -/
theorem principal_test_postponed (P : UnificationWithLevels.Solver (frames crossSetting.levels))
    {m : Context crossSetting.R} {σ : m ⟶ ctxCross} {R : EquationStore (TotalTerm m)}
    (run : P.Reaches crossStore m σ R) :
    R ≠ [] ∧ (∀ r : UnificationWithLevels.Reason, ¬ P.Refutes R r) ∧
      UnificationWithLevels.Exact (frames crossSetting.levels) crossStore σ R :=
  UnificationWithLevels.DependentFibre.cross_postponed P run

end Principal

/-! ## 2. Absence against framing -/

section Framing

open NamesOnTheStep NamesOnTheStep.IssuingControls NullsOnTheStep NullsOnTheStep.Composition

/-- **The tempting law (the frame rule)**: an admitted firing stays admitted beside any store whose
occurrences its made identities avoid and whose knowledge is trivial. -/
def FrameLaw : Prop :=
  ∀ (C D : Conf) (f : Fir), base.Admits (s := C) f → (∀ o ∈ f.selection.made, o ∉ D.present) →
    (∀ e ∈ D.equations, e.1 = e.2) → base.Admits (s := union C D) f

/-- **Test 2**: the frame rule fails for the absence-guarded `spawn` beside the store `U`. -/
theorem frameLaw_fails : ¬ FrameLaw := by
  intro law
  have onUnion := law Separations.emptyS.1 Separations.onlyU.1 Separations.spawnAt.1
    Separations.spawn_admitted.1 (by decide) (by decide)
  have clear := (guarded_union_iff (D := Separations.onlyU.1) (f := Separations.spawnAt.1) rfl rfl
    Separations.spawn_admitted.1 (by decide) (by decide)).mp onUnion
  exact clear (factU, 0) (by decide) rfl

/-- **What holds at the test**: the frame rule holds for take, read, make and tell admission, and an
absence-guarded firing survives framing exactly when the frame has no match. -/
theorem frame_test_graded {C D : Conf} {f : Fir} {p : Expr}
    (freshInD : ∀ o ∈ f.selection.made, o ∉ D.present) (knowledgeD : ∀ e ∈ D.equations, e.1 = e.2)
    (noQueries : f.queries = []) (admitted : base.Admits (s := C) f) :
    (f.rule.checks = [] → base.Admits (s := union C D) f) ∧
      (f.rule.checks = [.absent p] →
        (base.Admits (s := union C D) f ↔ (Check.absent p).Holds ground () Prod.fst D.present)) :=
  ⟨fun noChecks => positive_monotone noChecks noQueries admitted freshInD knowledgeD,
    fun guard => guarded_union_iff guard noQueries admitted freshInD knowledgeD⟩

end Framing

/-! ## 3. Pairwise compatibility without a joint wave -/

section Wave

open AnnotatedRuns AnnotatedRuns.CanonicalControls
open ConstraintMultisetRewriting.Controls (A)
open AnnotatedRuns.Controls (label)
open AnnotatedRuns.RoundControls (tellSame tellOne tellTwo empty)

/-- **The tempting law**: three firings independent in pairs at a configuration run together, in
some order. -/
def WaveLaw : Prop :=
  ∀ C f g h, (firstOrderTransport A label).Independent C f g →
    (firstOrderTransport A label).Independent C f h → (firstOrderTransport A label).Independent C g h →
      ∃ r : (firstOrder A label).Run C, (r.word.map Sigma.snd).Perm [f, g, h]

/-- **Test 3**: the law fails at the hollow cube `X ≐ Y`, `X ≐ 1`, `Y ≐ 2`. -/
theorem waveLaw_fails : ¬ WaveLaw := by
  intro law
  obtain ⟨⟨one, two, three⟩, never⟩ := hollow_cube_never_round
  obtain ⟨r, perm⟩ := law empty tellSame tellOne tellTwo one two three
  exact never r perm

end Wave

/-! ## 4. Solvable without being inhabited -/

section Inhabitation

open ContextualDependentClosedBoundary ContextualDependentClosedBoundary.Controls

/-- The package of the point store: the cumulative tower. -/
abbrev towerSetting := ContextualDependentEtaLong.Controls.setting

/-- **The tempting law**: a solvable store of the dependent fibre has a closed solution. -/
def InhabitationLaw : Prop :=
  ∀ {Γ : Context towerSetting.R} (K : EquationStore (TotalTerm Γ)),
    (frames towerSetting.levels).Solvable K → ClosedSolvable (S := towerSetting) K

/-- **Test 4**: the law fails at `x ≐ x` over `x : Ground`. -/
theorem inhabitationLaw_fails : ¬ InhabitationLaw :=
  fun law => point_not_closedSolvable (law pointStore point_solvable)

/-- The newest variable of `X : U0, x : X, g : Ground` has type `Ground`. -/
theorem triple_newest_ground (σ : empty Tower.rules ⟶ DependentFull.Controls.triple) :
    Typed Tower.rules Ctx.nil (σ.substitution 0) DependentFull.Controls.ground := σ.typed (0 : Fin 3)

/-- **Test 4 on the dependent full step**: the step admits a firing whose information has no closed
solution. The firing makes the helpers `x : X`, `g : Ground` and tells `(x : X) ≐ (g : Ground)`; a
closed solution would give `g` a closed value of type `Ground`. -/
theorem admitted_not_closed :
    (DependentFull.step DependentFull.Controls.setting.levels Nat).Admits DependentFull.Controls.refinedFiring ∧
      ¬ ClosedSolvable (S := DependentFull.Controls.setting) DependentFull.Controls.refinedFiring.information :=
  ⟨DependentFull.Controls.refined_admitted, fun ⟨σ, _⟩ => ground_uninhabited (triple_newest_ground σ)⟩

end Inhabitation

end ProgrammingOnTheStep.AcceptanceTests

#print axioms ProgrammingOnTheStep.AcceptanceTests.principalLaw_fails
#print axioms ProgrammingOnTheStep.AcceptanceTests.principal_test_postponed
#print axioms ProgrammingOnTheStep.AcceptanceTests.frameLaw_fails
#print axioms ProgrammingOnTheStep.AcceptanceTests.frame_test_graded
#print axioms ProgrammingOnTheStep.AcceptanceTests.waveLaw_fails
#print axioms ProgrammingOnTheStep.AcceptanceTests.inhabitationLaw_fails
#print axioms ProgrammingOnTheStep.AcceptanceTests.admitted_not_closed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
