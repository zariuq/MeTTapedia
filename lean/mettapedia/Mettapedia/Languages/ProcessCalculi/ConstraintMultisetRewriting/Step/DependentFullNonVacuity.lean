import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullPointPackage
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullNonVacuityStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullFibreControls

/-!
# The fibre join is not vacuous: actual runs of the full solver

In the point package, with every hypothesis of `fibre_admission_transfer_of_full` discharged
(`DependentFull.PointPackage`), the actual full solver is run by the kernel on two translated
pattern stores.

**The solved case.** On the translated pattern equation `λx. m x ≐ λx. n x` the solver commits
(`pattern_commit`). The run's answer is principal (`pattern_solved`), lands at a translated telescope
of one metavariable (`pattern_answer_arity`, `pattern_in_fibre`), and reads back as a second-order
principal answer (`pattern_second_order`). The second-order take firing that takes the row `n(x)` with
the pattern `m(x)` has exactly this store as its information (`take_information`). The join applies
to it with its decision hypothesis discharged by the run (`take_transfer`), and the firing is
admitted on both sides (`solved_case_nonvacuous`): by the frame-local second-order step, with a
solution built by hand, and on the translated data, with solvability read off the run.

**The refuted case.** On `λxy. F x ≐ λxy. y` the solver returns a certified refutation
(`outside_refuted`). The take firing with this information is refused on both sides
(`refuted_case_refused`); on the second-order side unsolvability is also proved directly, by cases on
the image of `F` (`outside_unsolvable_direct`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull.NonVacuity

open _root_.CategoryTheory
open Mettapedia.OSLF
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open ContextualDependentFibre ContextualDependentFibre.Controls Translation
open PointPackage
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)

/-- Observations of the point signature at a list frame. -/
abbrev Obs : List (Binding.MetaArity pointSig) → Type :=
  fun M => Binding.ContextualFamily.Observation pointSig M.get

/-- The frame-local second-order step at the list frames of the point signature. -/
abbrev second : Step.Standard (listFrames pointSig) Nat (EquationStep.State Obs Nat) (fun s => EquationStep.Firing Obs s) :=
  EquationStep.step (listFrames pointSig) Nat

/-- A dependent principal answer at some telescope that equals a translated one gives one at the
translated telescope. -/
theorem landing {M N : List (Binding.MetaArity pointSig)} {K : EquationStore (Obs M)}
    {T : Context setting.R} (answer : T ⟶ Ψ.obj M) (same : T = Ψ.obj N)
    (principal : (frames setting.levels).Principal (Ψ.store K) answer) :
    ∃ τ : Ψ.obj N ⟶ Ψ.obj M, (frames setting.levels).Principal (Ψ.store K) τ := by
  subst same
  exact ⟨answer, principal⟩

/-! ## The solved case: `m(x) ≐ n(x)` -/

/-- **The actual full solver commits on the translated pattern store**, evaluated by the kernel. -/
theorem pattern_commit :
    (ContextualDependentWorklist.run full (Ψ.store (patternStore star)) 2).readout = .commit := by
  decide +kernel

/-- **Its answer lands at a telescope of one metavariable.** -/
theorem pattern_answer_arity :
    (ContextualDependentWorklist.run full (Ψ.store (patternStore star)) 2).state?.map
      (fun state => state.target.arity) = some 1 := by
  decide +kernel

theorem pattern_decided :
    (ContextualDependentWorklist.run full (Ψ.store (patternStore star)) 2).Decided := by
  generalize computed : ContextualDependentWorklist.run full (Ψ.store (patternStore star)) 2 = outcome
  have committed := pattern_commit
  rw [computed] at committed
  cases outcome with
  | solved _ _ => trivial
  | refuted _ => cases committed
  | stuck _ => cases committed
  | cutoff _ => cases committed

/-- **The run solves the store with a principal answer.** -/
theorem pattern_solved :
    ∃ state finished, ContextualDependentWorklist.run full (Ψ.store (patternStore star)) 2 = .solved state finished ∧
      (frames setting.levels).Principal (Ψ.store (patternStore star)) state.answer := by
  generalize computed : ContextualDependentWorklist.run full (Ψ.store (patternStore star)) 2 = outcome
  have committed := pattern_commit
  rw [computed] at committed
  cases outcome with
  | solved state finished =>
      exact ⟨state, finished, rfl, ContextualDependentWorklist.drive_solved_principal full computed⟩
  | refuted _ => cases committed
  | stuck _ => cases committed
  | cutoff _ => cases committed

/-- **The solved half of the join's domain is inhabited**: the run's principal answer lands at a
translated telescope. -/
theorem pattern_in_fibre :
    ∃ (N : List (Binding.MetaArity pointSig)) (τ : Ψ.obj N ⟶ Ψ.obj (pairFrame star)),
      (frames setting.levels).Principal (Ψ.store (patternStore star)) τ := by
  generalize computed : ContextualDependentWorklist.run full (Ψ.store (patternStore star)) 2 = outcome
  have committed := pattern_commit
  rw [computed] at committed
  cases outcome with
  | solved state finished =>
      obtain ⟨N, same⟩ := drive_solved_target _
        (full_keeps_translated (S := setting) facts roots heads church names realization rigid complete algebra
          declared choices reducer (fun _ => none) point_normalizes certifyNormal headTypingUnique 16)
        2 _ (translated_obj (S := setting) facts roots heads church names realization _) computed
      obtain ⟨τ, principal⟩ := landing state.answer same
        (ContextualDependentWorklist.drive_solved_principal full computed)
      exact ⟨N, τ, principal⟩
  | refuted _ => cases committed
  | stuck _ => cases committed
  | cutoff _ => cases committed

/-- **The run's answer reads back as a second-order principal answer** of `m(x) ≐ n(x)`. -/
theorem pattern_second_order :
    ∃ (N : List (Binding.MetaArity pointSig))
      (σ : Binding.ContextualFamily.Assignment (S := pointSig) (pairFrame star).get N.get),
      (listFrames pointSig).Principal (a := pairFrame star) (m := N) (patternStore star) σ ∧
        (frames setting.levels).Principal (Ψ.store (patternStore star)) (Ψ.hom σ) := by
  obtain ⟨N, τ, principal⟩ := pattern_in_fibre
  obtain ⟨σ, _, translated, second⟩ := point_answer_in_fibre principal
  exact ⟨N, σ, second, translated⟩

/-! ### The take firing -/

/-- Labels: the row `1` is `n(x)`; every other row is `m(x)`. -/
def label (o : Nat) : Obs (pairFrame star) :=
  if o = 1 then occurrence (pairFrame star) (nIdx star) else occurrence (pairFrame star) (mIdx star)

/-- One present row, `1 : n(x)`, and empty knowledge. -/
def start : EquationStep.State Obs Nat := ⟨pairFrame star, [], {1}, label⟩

/-- Take the row `1` with the pattern `m(x)`. -/
def takeFiring : EquationStep.Firing Obs start :=
  ⟨[1], [], [occurrence (pairFrame star) (mIdx star)], [], [], [], []⟩

/-- **Its information is the pattern store.** -/
theorem take_information : second.information takeFiring = patternStore star := rfl

/-- The run on the firing's own translated information. -/
theorem take_decided :
    (ContextualDependentWorklist.run (fullAt 16) (Ψ.store (second.information takeFiring)) 2).Decided :=
  pattern_decided

/-- **The join at this firing, with its decision hypothesis discharged by the run.** -/
theorem take_transfer :
    second.Admits takeFiring ↔ second.Shapes takeFiring ∧
      Enabled (fun _ : Nat => ()) (second.present start) ((second.selection takeFiring).commit (T := Unit)) ∧
      (frames setting.levels).Solvable (Ψ.store (second.information takeFiring)) ∧
      (frames setting.levels).Entails (Ψ.store (second.information takeFiring))
        (fun _ g => (frames setting.levels).Models g (Ψ.store takeFiring.guards)) :=
  fibre_admission_transfer_of_full (S := setting) facts roots heads church names realization rigid complete
    algebra declared choices reducer (fun _ => none) point_normalizes certifyNormal headTypingUnique
    sortInjective point_closed @operatorInjective second.toStep (fun f => f.guards) (fun _ _ _ => Iff.rfl)
    takeFiring 16 2 take_decided

theorem take_shapes : second.Shapes takeFiring := ⟨by decide, by decide, rfl, rfl⟩

theorem take_enabled :
    Enabled (fun _ : Nat => ()) (second.present start) ((second.selection takeFiring).commit (T := Unit)) := by
  refine (EquationStep.enabled_iff takeFiring).mpr ⟨?_, ?_, ?_, ?_⟩
  · intro o member
    simp only [takeFiring, List.mem_singleton] at member
    subst member
    simp [start]
  · intro o member
    cases member
  · intro o _ readToo
    cases readToo
  · intro o member
    cases member

/-- **Admitted by the second-order step**, with the hand-built solution `m, n ↦ m(x)`. -/
theorem take_admitted_second_order : second.Admits takeFiring :=
  (EquationStep.admits_iff takeFiring).mpr ⟨take_shapes, take_enabled,
    ⟨pairFrame star, FibreControls.endoCollapse, FibreControls.endoCollapse_solves⟩,
    fun _ _ _ e member => by cases member⟩

/-- **Admitted on the translated data**, with solvability read off the solver's run. -/
theorem take_admitted_translated :
    (frames setting.levels).Solvable (Ψ.store (second.information takeFiring)) ∧
      (frames setting.levels).Entails (Ψ.store (second.information takeFiring))
        (fun _ g => (frames setting.levels).Models g (Ψ.store takeFiring.guards)) := by
  obtain ⟨state, _, _, principal⟩ := pattern_solved
  exact ⟨principal.solvable, fun _ _ _ e member => by cases member⟩

/-- **Non-vacuity of the solved case.** The actual full solver commits on the translated information
of a concrete second-order firing; the join applies to it with every hypothesis discharged; and the
firing is admitted on both sides. -/
theorem solved_case_nonvacuous :
    (ContextualDependentWorklist.run full (Ψ.store (second.information takeFiring)) 2).readout = .commit ∧
      (second.Admits takeFiring ↔ second.Shapes takeFiring ∧
        Enabled (fun _ : Nat => ()) (second.present start) ((second.selection takeFiring).commit (T := Unit)) ∧
        (frames setting.levels).Solvable (Ψ.store (second.information takeFiring)) ∧
        (frames setting.levels).Entails (Ψ.store (second.information takeFiring))
          (fun _ g => (frames setting.levels).Models g (Ψ.store takeFiring.guards))) ∧
      second.Admits takeFiring ∧
      (frames setting.levels).Solvable (Ψ.store (second.information takeFiring)) ∧
      (frames setting.levels).Entails (Ψ.store (second.information takeFiring))
        (fun _ g => (frames setting.levels).Models g (Ψ.store takeFiring.guards)) :=
  ⟨pattern_commit, take_transfer, take_admitted_second_order, take_admitted_translated⟩

/-! ## The refuted case: `F(x) ≐ y` -/

/-- One unary metavariable `F`. -/
abbrev single : List (Binding.MetaArity pointSig) := unaryFrame star

/-- `F(x)` under `x y`, with `y` the newest bound variable. -/
def outsideLeft : Obs single :=
  ⟨[star, star], star, .op (.inr (.mk ⟨0, Nat.zero_lt_one⟩)) (.cons (.var (.succ .zero)) .nil)⟩

/-- `y` under `x y`. -/
def outsideRight : Obs single := ⟨[star, star], star, .var .zero⟩

/-- The store `F(x) ≐ y`: the right side uses a variable `F` cannot see. -/
def outsideStore : EquationStore (Obs single) := [(outsideLeft, outsideRight)]

/-- **The actual full solver refutes the translated store**, evaluated by the kernel. -/
theorem outside_refuted :
    (ContextualDependentWorklist.run full (Ψ.store outsideStore) 2).readout = .refuted := by
  decide +kernel

theorem outside_unsolvable : ¬ (frames setting.levels).Solvable (Ψ.store outsideStore) :=
  ContextualDependentWorklist.Outcome.readout_eq_refuted outside_refuted

/-- Labels: the row `1` is `y`; every other row is `F(x)`. -/
def outsideLabel (o : Nat) : Obs single := if o = 1 then outsideRight else outsideLeft

def outsideStart : EquationStep.State Obs Nat := ⟨single, [], {1}, outsideLabel⟩

/-- Take the row `1 : y` with the pattern `F(x)`. -/
def outsideFiring : EquationStep.Firing Obs outsideStart := ⟨[1], [], [outsideLeft], [], [], [], []⟩

theorem outside_information : second.information outsideFiring = outsideStore := rfl

theorem outside_decided :
    (ContextualDependentWorklist.run (fullAt 16) (Ψ.store (second.information outsideFiring)) 2).Decided := by
  generalize computed : ContextualDependentWorklist.run (fullAt 16) (Ψ.store (second.information outsideFiring))
    2 = outcome
  have refuted := outside_refuted
  rw [show ContextualDependentWorklist.run full (Ψ.store outsideStore) 2 = outcome from computed] at refuted
  cases outcome with
  | refuted _ => trivial
  | solved _ _ => cases refuted
  | stuck _ => cases refuted
  | cutoff _ => cases refuted

/-- **The refuted case**: the join applies with its hypothesis discharged by the run, and the firing
is refused on both sides. -/
theorem refuted_case_refused :
    (ContextualDependentWorklist.run full (Ψ.store (second.information outsideFiring)) 2).readout = .refuted ∧
      ¬ second.Admits outsideFiring ∧
      ¬ (frames setting.levels).Solvable (Ψ.store (second.information outsideFiring)) := by
  have transfer := fibre_admission_transfer_of_full (S := setting) facts roots heads church names realization
    rigid complete algebra declared choices reducer (fun _ => none) point_normalizes certifyNormal
    headTypingUnique sortInjective point_closed @operatorInjective second.toStep (fun f => f.guards)
    (fun _ _ _ => Iff.rfl) outsideFiring 16 2 outside_decided
  exact ⟨outside_refuted, fun admitted => outside_unsolvable (transfer.mp admitted).2.2.1, outside_unsolvable⟩

/-- A term over one parameter, with the parameter sent to the older of two variables, is never the
newer one. -/
theorem bind_ne_newest {T : Binding.Signature} {s : T.Srt} (sub : Binding.Sub T [s] [s, s])
    (first : sub s .zero = .var (.succ .zero)) :
    ∀ t : Binding.Term T [s] s, Binding.bind sub t ≠ .var .zero
  | .var v, same => by
      match v with
      | .zero =>
          change sub s .zero = .var .zero at same
          rw [first] at same
          cases same
  | .op _ _, same => by cases same

/-- **Direct second-order check**: no assignment solves `F(x) ≐ y`. -/
theorem outside_unsolvable_direct : ¬ (listFrames pointSig).Solvable outsideStore := by
  rintro ⟨N, σ, solved⟩
  have equation := solved _ (List.mem_singleton_self _)
  change Binding.ContextualFamily.instantiateObservation σ outsideLeft =
    Binding.ContextualFamily.instantiateObservation σ outsideRight at equation
  have terms := Binding.ContextualFamily.observe_injective (S := pointSig) (source := N.get)
    (Γ := [star, star]) (sort := star) equation
  exact bind_ne_newest _ rfl _ terms

end DependentFull.NonVacuity

#print axioms DependentFull.NonVacuity.pattern_commit
#print axioms DependentFull.NonVacuity.pattern_answer_arity
#print axioms DependentFull.NonVacuity.pattern_solved
#print axioms DependentFull.NonVacuity.pattern_in_fibre
#print axioms DependentFull.NonVacuity.pattern_second_order
#print axioms DependentFull.NonVacuity.take_information
#print axioms DependentFull.NonVacuity.take_transfer
#print axioms DependentFull.NonVacuity.take_admitted_second_order
#print axioms DependentFull.NonVacuity.take_admitted_translated
#print axioms DependentFull.NonVacuity.solved_case_nonvacuous
#print axioms DependentFull.NonVacuity.outside_refuted
#print axioms DependentFull.NonVacuity.refuted_case_refused
#print axioms DependentFull.NonVacuity.outside_unsolvable_direct

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
