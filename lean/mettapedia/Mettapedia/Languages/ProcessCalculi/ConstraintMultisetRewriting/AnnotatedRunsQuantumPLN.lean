import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsQuantum

/-!
# A quantum reading of PLN: truth values as readouts, revision for records, deduction against
interference

## Truth values as readouts of amplitude collections

* A proposition reads two families of branches, those that end in `yes` and those that end in
  `no`. Its strength is the Born probability of `yes` in the record-respecting readout
  (`readoutStrength`), and its evidence weight is the total readout (`readoutWeight`).
* With one end state per region this is the Born probability of the coherent sums, R33's
  `bornProbability` (`readoutStrength_of_one_end`).

## Revision survives for recorded evidence

* **Exact for records** (`revision_of_recorded`): when no end state of one family is an end state
  of the other, the readouts add, so the strength of the union is the weight-averaged strength:
  PLN revision with the Born weights as evidence.
* **Not for unrecorded evidence** (`revision_fails_unrecorded`): two halves, each with a `yes`
  path and a `no` path, ending in shared states. Each half reads `1/2`; revising them gives `1/2`;
  their union reads `0`, because the `yes` paths `1` and `-1` cancel. Recorded, the same union
  reads `1/2` (`revision_holds_recorded`).

## Deduction on Born readouts against the coherent computation

* A Mach–Zehnder interferometer: a photon from `A` takes the upper arm `B` or the lower arm `¬B`
  with amplitude `1` each; the upper arm reaches the detectors `C` and `D` with amplitudes `1` and
  `1`, the lower arm with `1` and `-1`.
* With the arm recorded, the Born readouts are `P(B|A) = P(C|B) = P(B) = P(C) = 1/2`, consistent
  with a classical joint distribution in which `C` is independent of `A` given `B` and given `¬B`,
  and PLN's deduction formula gives `P(C|A) = 1/2` (`deduction_on_born_readouts`), which is the
  recorded readout (`recorded_detector_C`).
* With the arm unrecorded, the two routes to each detector interfere: `C` reads `1` and `D` reads
  `0` (`coherent_detector_C`). **Deduction disagrees with the coherent computation**
  (`deduction_fails_under_interference`): the coherent readout is not a mixture over the arms, and
  the difference is the cross term of the two routes to `C` over the total weight.
-/

set_option autoImplicit false

open scoped QuadraticAlgebra

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace AmplitudeRuns

namespace QuantumPLN

open Mettapedia.Algebra.RationalComplexAmplitude (Amplitude born)
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction (simpleDeductionStrengthFormula
  conditionalProbabilityConsistency)

/-! ## Truth values as readouts -/

section Readouts

variable {ι : Type*} {E : Type*} [DecidableEq E]

/-- **The evidence weight of a proposition**: the total record-respecting readout of its `yes`
and `no` families. -/
def readoutWeight (ends : ι → E) (amp : ι → Amplitude) (yes no : Finset ι) : ℚ :=
  endReadout ends amp yes + endReadout ends amp no

/-- **The strength of a proposition**: the Born probability of `yes` in the record-respecting
readout. -/
def readoutStrength (ends : ι → E) (amp : ι → Amplitude) (yes no : Finset ι) : ℚ :=
  endReadout ends amp yes / readoutWeight ends amp yes no

/-- **With one end per region, the strength is R33's Born probability** of the coherent sums. -/
theorem readoutStrength_of_one_end (ends : ι → E) (amp : ι → Amplitude) {yes no : Finset ι}
    {e f : E} (yesNonempty : yes.Nonempty) (noNonempty : no.Nonempty)
    (yesShared : ∀ b ∈ yes, ends b = e) (noShared : ∀ b ∈ no, ends b = f) :
    readoutStrength ends amp yes no =
      bornProbability (∑ b ∈ yes, amp b) (∑ b ∈ no, amp b) := by
  unfold readoutStrength readoutWeight bornProbability
  rw [endReadout_of_one_end amp yesNonempty yesShared, endReadout_of_one_end amp noNonempty noShared]

theorem mul_div_self_of_ne {a b : ℚ} (nonzero : a ≠ 0) : a * (b / a) = b := by
  field_simp

/-- **Revision survives for recorded evidence.** When the end states of the two families are
disjoint, the strength of their union is the weight-averaged strength of the two. -/
theorem revision_of_recorded [DecidableEq ι] (ends : ι → E) (amp : ι → Amplitude)
    {yes₁ yes₂ no₁ no₂ : Finset ι}
    (apartYes : Disjoint (yes₁.image ends) (yes₂.image ends))
    (apartNo : Disjoint (no₁.image ends) (no₂.image ends))
    (weighted₁ : readoutWeight ends amp yes₁ no₁ ≠ 0)
    (weighted₂ : readoutWeight ends amp yes₂ no₂ ≠ 0) :
    readoutStrength ends amp (yes₁ ∪ yes₂) (no₁ ∪ no₂) =
      (readoutWeight ends amp yes₁ no₁ * readoutStrength ends amp yes₁ no₁ +
          readoutWeight ends amp yes₂ no₂ * readoutStrength ends amp yes₂ no₂) /
        (readoutWeight ends amp yes₁ no₁ + readoutWeight ends amp yes₂ no₂) := by
  unfold readoutStrength
  rw [mul_div_self_of_ne weighted₁, mul_div_self_of_ne weighted₂]
  unfold readoutWeight
  rw [endReadout_union_of_disjoint_ends ends amp apartYes,
    endReadout_union_of_disjoint_ends ends amp apartNo]
  congr 1
  ring

/-- The readout of one branch is its Born weight. -/
theorem endReadout_singleton (ends : ι → E) (amp : ι → Amplitude) (b : ι) :
    endReadout ends amp {b} = born (amp b) := by
  rw [endReadout_of_one_end amp (Finset.singleton_nonempty b) (e := ends b)
    (fun b' member => by rw [Finset.mem_singleton.mp member]), Finset.sum_singleton]

end Readouts

/-! ## Revision does not survive for unrecorded evidence -/

section Halves

/-- The paths of two halves: half `h` has a `yes` path `(h, true)` and a `no` path `(h, false)`.
The `yes` paths carry `1` and `-1`; the `no` paths carry `1`. -/
def halfPath : Bool × Bool → Amplitude
  | (true, true) => 1
  | (false, true) => -1
  | (_, false) => 1

/-- Unrecorded: a path ends in its region alone; nothing records its half. -/
def unrecordedEnd (path : Bool × Bool) : Bool := path.2

/-- Each half reads `1/2`, with evidence weight `2`. -/
theorem half_strengths :
    readoutStrength unrecordedEnd halfPath {(true, true)} {(true, false)} = 1 / 2 ∧
      readoutStrength unrecordedEnd halfPath {(false, true)} {(false, false)} = 1 / 2 ∧
      readoutWeight unrecordedEnd halfPath {(true, true)} {(true, false)} = 2 ∧
      readoutWeight unrecordedEnd halfPath {(false, true)} {(false, false)} = 2 := by
  simp only [readoutStrength, readoutWeight, endReadout_singleton, halfPath, born_one, born_neg]
  norm_num

/-- **Revision fails for unrecorded evidence.** The two halves read `1/2` each and revise to
`1/2`; their union reads `0`, because the `yes` paths cancel and the `no` paths reinforce. -/
theorem revision_fails_unrecorded :
    (2 * (1 / 2 : ℚ) + 2 * (1 / 2)) / (2 + 2) = 1 / 2 ∧
      readoutStrength unrecordedEnd halfPath ({(true, true)} ∪ {(false, true)})
        ({(true, false)} ∪ {(false, false)}) = 0 := by
  refine ⟨by norm_num, ?_⟩
  have yesSum : endReadout unrecordedEnd halfPath ({(true, true)} ∪ {(false, true)}) = 0 := by
    rw [endReadout_of_one_end halfPath (e := true) ⟨(true, true), by simp⟩
      (fun path member => by
        simp only [Finset.mem_union, Finset.mem_singleton] at member
        rcases member with rfl | rfl <;> rfl),
      Finset.sum_union (by simp), Finset.sum_singleton, Finset.sum_singleton]
    simp [halfPath]
  unfold readoutStrength
  rw [yesSum, zero_div]

/-- Recorded: a path ends in a state that keeps its half. -/
def recordedEnd (path : Bool × Bool) : Bool × Bool := path

/-- **Recorded, the same union revises exactly**: it reads `1/2`, the revision of the halves. -/
theorem revision_holds_recorded :
    readoutStrength recordedEnd halfPath ({(true, true)} ∪ {(false, true)})
      ({(true, false)} ∪ {(false, false)}) = 1 / 2 := by
  rw [revision_of_recorded recordedEnd halfPath (by simp [recordedEnd]) (by simp [recordedEnd])
    (by simp [readoutWeight, endReadout_singleton, halfPath])
    (by simp [readoutWeight, endReadout_singleton, halfPath, born_neg])]
  simp only [readoutStrength, readoutWeight, endReadout_singleton, halfPath, born_one, born_neg]
  norm_num

end Halves

/-! ## Deduction against interference -/

section Interferometer

/-- **The routes of the interferometer**: arm `true` is `B`, arm `false` is `¬B`; detector `true`
is `C`, detector `false` is `D`. The amplitude of a route is the product of the amplitude `1` of
its arm and the amplitude of the arm to the detector. -/
def route : Bool → Bool → Amplitude
  | true, _ => 1
  | false, true => 1
  | false, false => -1

/-- With the arm unrecorded, both routes to a detector end at that detector. -/
def detectorOnly (_ : Bool) : Unit := ()

/-- **The coherent readout of a detector**: its two routes, unrecorded. -/
def coherentDetector (detector : Bool) : ℚ :=
  endReadout detectorOnly (fun arm => route arm detector) Finset.univ

/-- **The recorded readout of a detector**: its two routes, with the arm recorded. -/
def recordedDetector (detector : Bool) : ℚ :=
  endReadout id (fun arm => route arm detector) Finset.univ

theorem coherentDetector_eq (detector : Bool) :
    coherentDetector detector = born (route true detector + route false detector) := by
  unfold coherentDetector
  rw [endReadout_of_one_end _ Finset.univ_nonempty (e := ()) (fun _ _ => rfl), Fintype.sum_bool]

theorem recordedDetector_eq (detector : Bool) :
    recordedDetector detector = born (route true detector) + born (route false detector) := by
  unfold recordedDetector
  rw [endReadout_of_injOn _ (Function.injective_id.injOn), classicalWeight, Fintype.sum_bool]

/-- **The arm unrecorded, `C` reads `1` and `D` reads `0`.** -/
theorem coherent_detector_C :
    coherentDetector true / (coherentDetector true + coherentDetector false) = 1 ∧
      coherentDetector false = 0 := by
  rw [coherentDetector_eq, coherentDetector_eq]
  simp only [route, add_neg_cancel, born_zero, add_zero]
  rw [born_double, born_one]
  norm_num

/-- **The arm recorded, `C` reads `1/2`.** -/
theorem recorded_detector_C :
    recordedDetector true / (recordedDetector true + recordedDetector false) = 1 / 2 := by
  rw [recordedDetector_eq, recordedDetector_eq]
  simp only [route, born_one, born_neg]
  norm_num

/-- **The Born readouts with the arm recorded**: `P(B|A) = P(C|B) = 1/2`, and the marginals of
`B` and `C` among the photons from `A` are `1/2`. -/
theorem born_readouts :
    bornProbability 1 1 = 1 / 2 ∧ bornProbability (route true true) (route true false) = 1 / 2 ∧
      bornProbability (route false true) (route false false) = 1 / 2 ∧
      recordedDetector true / (recordedDetector true + recordedDetector false) = 1 / 2 := by
  refine ⟨?_, ?_, ?_, recorded_detector_C⟩ <;>
    simp only [bornProbability, route, born_one, born_neg] <;> norm_num

/-- The consistency conditions of PLN deduction hold for the recorded readouts. -/
theorem readouts_consistent :
    conditionalProbabilityConsistency 1 (1 / 2) (1 / 2) ∧
      conditionalProbabilityConsistency (1 / 2) (1 / 2) (1 / 2) :=
  ⟨⟨by norm_num, max_le (by norm_num) (by norm_num), le_min (by norm_num) (by norm_num)⟩,
    ⟨by norm_num, max_le (by norm_num) (by norm_num), le_min (by norm_num) (by norm_num)⟩⟩

/-- **PLN deduction on the Born readouts** gives `P(C|A) = 1/2`. -/
theorem deduction_on_born_readouts :
    simpleDeductionStrengthFormula 1 (1 / 2) (1 / 2) (1 / 2) (1 / 2) = 1 / 2 := by
  unfold simpleDeductionStrengthFormula
  rw [if_neg (not_not.mpr readouts_consistent), if_neg (by norm_num)]
  norm_num

/-- **Deduction disagrees with the coherent computation under interference.** On the Born readouts
of the recorded interferometer, PLN deduction gives `1/2`, which is the recorded readout of `C`;
the coherent readout of `C` is `1`. The difference is the cross term of the two routes to `C`,
`interference 1 1 = 2`, over the total weight `4`. -/
theorem deduction_fails_under_interference :
    simpleDeductionStrengthFormula 1 (1 / 2) (1 / 2) (1 / 2) (1 / 2) =
        ((recordedDetector true / (recordedDetector true + recordedDetector false) : ℚ) : ℝ) ∧
      simpleDeductionStrengthFormula 1 (1 / 2) (1 / 2) (1 / 2) (1 / 2) ≠
        ((coherentDetector true / (coherentDetector true + coherentDetector false) : ℚ) : ℝ) ∧
      coherentDetector true / (coherentDetector true + coherentDetector false) -
          recordedDetector true / (recordedDetector true + recordedDetector false) =
        interference (route true true) (route false true) /
          (coherentDetector true + coherentDetector false) := by
  have deduced := deduction_on_born_readouts
  have recorded := recorded_detector_C
  have coherent := coherent_detector_C
  refine ⟨?_, ?_, ?_⟩
  · rw [deduced, recorded]
    norm_num
  · rw [deduced, coherent.1]
    norm_num
  · rw [coherent.1, recorded, coherentDetector_eq, coherentDetector_eq]
    simp only [route, add_neg_cancel, born_zero, add_zero]
    rw [born_double, born_one]
    norm_num [interference]

end Interferometer

end QuantumPLN

end AmplitudeRuns

open AmplitudeRuns.QuantumPLN

#print axioms readoutStrength_of_one_end
#print axioms mul_div_self_of_ne
#print axioms revision_of_recorded
#print axioms endReadout_singleton
#print axioms half_strengths
#print axioms revision_fails_unrecorded
#print axioms revision_holds_recorded
#print axioms coherentDetector_eq
#print axioms recordedDetector_eq
#print axioms coherent_detector_C
#print axioms recorded_detector_C
#print axioms born_readouts
#print axioms readouts_consistent
#print axioms deduction_on_born_readouts
#print axioms deduction_fails_under_interference

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
