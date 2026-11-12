import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreWeight
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreTraceControls
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Controls for weights on the first-order step

* `firstOrder_respects`, `firstOrder_keeps`: on the first-order step every weight of firings
  respects the transport and is kept by placement, so tensors weigh products there.
* `account_eq_prod_sites`: the weight of a first-order run is the product of the weights of its
  firing word.
* **Interchange is commutativity, and no more** (`weights_and_the_counting_interchange`). For the
  two runs of `interchange_fails_for_counting`, which are not one trace, the free monoid weight
  (the firing word itself) tells the two sides apart, and every commutative weight gives them the
  same value. A commutative weight cannot see the order that the counting grade sees.
* **Placement must keep the weights** (`a_weight_that_reads_the_state`). The weight "number of
  present occurrences" is not kept by placement, and the tensor of the reading run with the empty
  run beside the occurrence `9` does not weigh the product of the weights.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.WeightControls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open AnnotatedRuns (Firing firstOrder firstOrderTransport)
open FirstOrderNativeRuns
open KnowledgeTensorFirstOrder
open KnowledgeTensorFirstOrderControls (plain one)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.Controls

universe uT uS uO uM

section FirstOrder

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-- **First-order weights respect the transport**: moved firings are the firings themselves, and
alike firings are equal. -/
theorem firstOrder_respects (A : SubstitutionAction T S) (label : O → T) {M : Type uM} [Monoid M]
    (w : Firing T S O → M) :
    RespectsTransport (P := (firstOrder A label).toStep) (fun _ f => w f) (firstOrderTransport A label) :=
  ⟨fun _ _ => rfl, fun same => congrArg w same⟩

/-- **Placement keeps first-order weights**: the placed candidate is the firing itself. -/
theorem firstOrder_keeps (A : SubstitutionAction T S) (label : O → T) {M : Type uM} [Monoid M]
    (w : Firing T S O → M) :
    KeepsWeights (contextualRunInterpretation A label) (fun _ f => w f) :=
  fun _ _ => rfl

/-- The weight of a first-order run is the product of the weights of its firing word. -/
theorem account_eq_prod_sites (A : SubstitutionAction T S) (label : O → T) {M : Type uM} [Monoid M]
    (w : Firing T S O → M) :
    ∀ {C : Configuration T O} (run : (firstOrder A label).toStep.Run C),
      run.account (fun _ f => w f) = ((sites A label run).map w).prod
  | _, .nil _ => rfl
  | _, .cons f _ rest => by
      show w f * rest.account (fun _ f => w f) = (w f :: (sites A label rest).map w).prod
      rw [List.prod_cons, account_eq_prod_sites A label w rest]

end FirstOrder

/-! ## Interchange is commutativity, and no more -/

/-- The free monoid weight: a firing weighs itself, so a run weighs its firing word. -/
def wordWeight : Firing Nat Unit Nat → FreeMonoid (Firing Nat Unit Nat) := FreeMonoid.of

theorem cut_side_word :
    sites plain five (cutOfTensors (contextualRunInterpretation plain five) (contextualFlip plain five)
      beforePlan afterPlan) = [adds, removes, counts 1] :=
  sites_sequentialTensor plain five beforePlan afterPlan

theorem tensor_side_word :
    sites plain five (wholePlan.realize (contextualRunInterpretation plain five)
      (contextualFlip plain five)).execution = [counts 1, adds, removes] :=
  tensor_sites plain five wholePlan

/-- **Interchange is commutativity, and no more.** On the two sides of the counting control, which
are not one trace, the free monoid weight differs and every commutative weight agrees. -/
theorem weights_and_the_counting_interchange :
    (cutOfTensors (contextualRunInterpretation plain five) (contextualFlip plain five)
        beforePlan afterPlan).account (fun _ f => wordWeight f) ≠
      (wholePlan.realize (contextualRunInterpretation plain five)
        (contextualFlip plain five)).execution.account (fun _ f => wordWeight f) ∧
    ∀ {M : Type} [CommMonoid M] (w : Firing Nat Unit Nat → M),
      (cutOfTensors (contextualRunInterpretation plain five) (contextualFlip plain five)
          beforePlan afterPlan).account (fun _ f => w f) =
        (wholePlan.realize (contextualRunInterpretation plain five)
          (contextualFlip plain five)).execution.account (fun _ f => w f) := by
  refine ⟨fun same => ?_, fun w => ?_⟩
  · rw [account_eq_prod_sites plain five, account_eq_prod_sites plain five, cut_side_word,
      tensor_side_word] at same
    have words := congrArg FreeMonoid.toList same
    change [adds, removes, counts 1] = [counts 1, adds, removes] at words
    exact counts_ne_adds (List.cons.inj words).1.symm
  · exact interchange_weights (contextualRunInterpretation plain five)
      (firstOrder_respects plain five w) (firstOrder_keeps plain five w) (contextualFlip plain five)
      beforePlan afterPlan wholePlan

/-- And the two sides are not one trace: the order a commutative weight forgets is real. -/
theorem the_sides_are_not_one_trace :
    ¬ InterchangeAt (contextualRunInterpretation plain five) (contextualFlip plain five)
      beforePlan afterPlan wholePlan :=
  interchange_fails_for_counting

/-! ## Placement must keep the weights -/

/-- A weight that reads the state: the number of present occurrences where the firing fires. -/
def crowd : (C : Configuration Nat Nat) → Firing Nat Unit Nat → ℕ := fun C _ => C.present.card

/-- The reading run beside the occurrence `9`, with the empty run on the other side. -/
def readsBesideNine : (contextualRunInterpretation plain id).TensorPlan (contextualFlip plain id)
    PUnit.unit readsRun (.nil nine) where
  leftPlan :=
    .cons (I := contextualRunInterpretation plain id) (left := one) (right := nine)
      (place := PUnit.unit) reads_frames_nine reads_is_admitted_beside_nine (.nil _)
  rightPlan := .nil _

/-- The state-reading weight is not kept by placement. -/
theorem crowd_is_not_kept : ¬ KeepsWeights (contextualRunInterpretation plain id) crowd := by
  intro keeps
  have same := keeps (left := one) (right := nine) PUnit.unit reads
  have counted : ((AnnotatedRuns.tensor one nine).present).card = (one.present).card := same
  exact absurd counted (by decide)

/-- **Placement must keep the weights.** With the state-reading weight, the tensor of the reading
run and the empty run does not weigh the product of their weights. -/
theorem a_weight_that_reads_the_state :
    (readsBesideNine.realize (contextualRunInterpretation plain id) (contextualFlip plain id)).execution.account
        crowd ≠ readsRun.account crowd * (Step.Run.nil (P := (firstOrder plain id).toStep) nine).account crowd := by
  decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.WeightControls
