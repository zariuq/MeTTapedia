import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullCount
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullFibreControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Transport

/-!
# Counting through the join: controls

The package and the state are R91's (`DependentFull.FibreControls`): two unary metavariables `m, n`,
one present row `1 : n(x)`. The firing takes row `1` with the pattern `m(x)`; its problem is
`m(x) ≐ n(x)`, answered with η by the endomorphism `m, n ↦ λx. m x`.

* **Positive** (`count_one_admitted`): with the check "exactly one present row equals `m(x)`" the firing
  is admitted by the first-order step, and its translation, with R91's counting query, by the dependent
  full step: at every solution the row `n(x)` equals `m(x)`.
* **Negative** (`count_two_refused`): with "exactly two" it is refused on both sides; only one row is
  present.

The extensions the join needs decided, the problem with `m(x) ≐ n(x)` added again, have the same
solutions as the problem, so the same principal answer (`Frames.Principal.of_equivalent`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

theorem Frames.Principal.of_equivalent {Obj : Type*} {Tm : Obj → Type*} {Hom : Obj → Obj → Type*}
    {X : Frames Tm Hom} {a m : Obj} {K K' : EquationStore (Tm a)} {answer : Hom a m}
    (principal : X.Principal K answer) (same : X.Equivalent K K') : X.Principal K' answer :=
  ⟨(same m answer).mp principal.sound, fun b f solved => principal.factors b f ((same b f).mpr solved)⟩

namespace DependentFull.CountControls

open _root_.CategoryTheory
open Mettapedia.OSLF
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentEtaLong Translation
open ContextualDependentFibre ContextualDependentFibre.Controls
open DependentFull.FibreControls

/-- The pattern `m(x)`. -/
abbrev mOcc : Obs (pairFrame star) := occurrence (pairFrame star) (mIdx star)

/-- Take row `1` with the pattern `m(x)`, and check that exactly `number` present rows equal `m(x)`. -/
def countFiring (number : Nat) :
    AnnotatedRuns.Firing (Obs (pairFrame star))
      (Binding.ContextualFamily.Assignment (S := pointSig) (pairFrame star).get (pairFrame star).get) Nat :=
  ⟨⟨[mOcc], [], [], [.count mOcc number], []⟩, [], ⟨[1], [], []⟩⟩

theorem countFiring_problem (number : Nat) :
    (countFiring number).selection.problem label (countFiring number).rule start = patternStore star := rfl

theorem decided (number : Nat) :
    EndoDecided (S := setting) facts roots heads church names realization
      ((countFiring number).selection.problem label (countFiring number).rule start) := by
  rw [countFiring_problem]
  exact .inl ⟨_, endo_principal⟩

theorem extension_equivalent :
    (frames setting.levels).Equivalent (Ψ.store (patternStore star))
      (Ψ.store (patternStore star ++ [(mOcc, label 1)])) :=
  Frames.equivalent_of_mem_iff fun e => by
    simp only [FrameMap.store, List.map_append, List.mem_append, List.map_cons, List.map_nil,
      List.mem_singleton, patternStore]
    constructor
    · exact fun same => .inl same
    · rintro (same | same)
      · exact same
      · exact same

theorem decidedExtensions (number : Nat) :
    ∀ c ∈ (countFiring number).rule.checks, ∀ o ∈ start.present,
      EndoDecided (S := setting) facts roots heads church names realization
        ((countFiring number).selection.problem label (countFiring number).rule start ++ [(c.pattern, label o)]) := by
  intro c member o present
  obtain rfl := List.mem_singleton.mp member
  obtain rfl : o = 1 := Finset.mem_singleton.mp present
  rw [countFiring_problem]
  exact .inl ⟨_, endo_principal.of_equivalent extension_equivalent⟩

/-- At every endomorphic solution of the problem, the one present row equals `m(x)`. -/
theorem matches_one {σ : Binding.ContextualFamily.Assignment (S := pointSig) (pairFrame star).get
      (pairFrame star).get}
    (solved : (action (pairFrame star)).Models σ (patternStore star)) :
    Check.matches (action (pairFrame star)) σ label start.present mOcc = {1} := by
  ext o
  rw [SubstitutionAction.mem_matches]
  constructor
  · rintro ⟨present, -⟩
    exact present
  · intro present
    obtain rfl : o = 1 := Finset.mem_singleton.mp present
    exact ⟨present, solved _ (List.mem_singleton_self _)⟩

theorem firstOrder_iff (number : Nat) :
    (AnnotatedRuns.firstOrder (action (pairFrame star)) label).Admits (s := start) (countFiring number) ↔
      number = 1 := by
  rw [firstOrder_admits_iff_count label start (countFiring number) rfl]
  constructor
  · rintro ⟨-, -, ⟨σ, solved⟩, checks⟩
    have counted := checks _ (List.mem_singleton_self _) σ solved
    change (Check.matches (action (pairFrame star)) σ label start.present mOcc).card = number at counted
    rw [matches_one solved, Finset.card_singleton] at counted
    exact counted.symm
  · rintro rfl
    refine ⟨⟨by decide, by decide, rfl, rfl, rfl⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨endoCollapse, endoCollapse_solves⟩, ?_⟩
    · intro o member
      obtain rfl := List.mem_singleton.mp member
      exact Finset.mem_singleton_self 1
    · intro o member
      cases member
    · intro o _ readToo
      cases readToo
    · intro o member
      cases member
    · intro c member σ solved
      obtain rfl := List.mem_singleton.mp member
      change (Check.matches (action (pairFrame star)) σ label start.present mOcc).card = 1
      rw [matches_one solved]
      exact Finset.card_singleton 1

/-- **Counting through the join, positive**: exactly one row is counted on both sides. -/
theorem count_one_admitted :
    (AnnotatedRuns.firstOrder (action (pairFrame star)) label).Admits (s := start) (countFiring 1) ∧
      (step setting.levels Nat).Admits
        (s := translateState (S := setting) facts roots heads church names realization label start)
        (translateFiring (S := setting) facts roots heads church names realization label start (countFiring 1)) :=
  ⟨(firstOrder_iff 1).mpr rfl,
    ((admits_translate_iff_count (S := setting) facts roots heads algebra complete rigid church names realization
      sortInjective point_closed @operatorInjective label start (countFiring 1) rfl (decided 1)
      (decidedExtensions 1)).mp ((firstOrder_iff 1).mpr rfl)).2⟩

/-- **Counting through the join, negative**: "exactly two" is refused on both sides. -/
theorem count_two_refused :
    ¬ (AnnotatedRuns.firstOrder (action (pairFrame star)) label).Admits (s := start) (countFiring 2) ∧
      ¬ (step setting.levels Nat).Admits
        (s := translateState (S := setting) facts roots heads church names realization label start)
        (translateFiring (S := setting) facts roots heads church names realization label start (countFiring 2)) := by
  have firstOrder : ¬ (AnnotatedRuns.firstOrder (action (pairFrame star)) label).Admits (s := start)
      (countFiring 2) := fun admitted => absurd ((firstOrder_iff 2).mp admitted) (by decide)
  refine ⟨firstOrder, fun admitted => firstOrder ?_⟩
  refine (admits_translate_iff_count (S := setting) facts roots heads algebra complete rigid church names realization
    sortInjective point_closed @operatorInjective label start (countFiring 2) rfl (decided 2)
    (decidedExtensions 2)).mpr ⟨rfl, admitted⟩

end DependentFull.CountControls

#print axioms Frames.Principal.of_equivalent
#print axioms DependentFull.CountControls.decidedExtensions
#print axioms DependentFull.CountControls.firstOrder_iff
#print axioms DependentFull.CountControls.count_one_admitted
#print axioms DependentFull.CountControls.count_two_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
