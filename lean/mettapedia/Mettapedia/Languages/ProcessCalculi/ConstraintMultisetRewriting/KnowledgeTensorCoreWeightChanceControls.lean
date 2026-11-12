import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreWeightChance
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreControls

/-!
# Controls: runs of the first-order step in random surroundings

Surroundings are sets of facts of a finite type, each fact an occurrence with that number.

* **Absence.** The run of `unlessNine` (no `9`, makes `7`) at the occurrence `5` is an
  absence-only run along the surroundings, with forbidden set `{7, 9}`
  (`unless_nine_absence_along`): the label it forbids and the identity it makes. It survives with
  chance `(1 - p 7) (1 - p 9)` (`unless_nine_survival`).
* **An admitted count is graded like absence.** `counts 1`, admitted at the occurrence `0`, is
  placed beside a surrounding exactly when the surrounding adds no occurrence labelled `5`
  (`counts_one_absence_along`): its local count is already exact, and a surrounding only adds.
* **A candidate count is graded by counting.** `counts 2` is not admitted at `0`
  (`counts_two_not_admitted`), and as a candidate it is placed exactly when the surrounding adds
  one occurrence (`counts_two_candidate`), with the chance of the coefficient of `X`
  (`counts_two_candidate_measure`). Its grade is neither down- nor up-closed
  (`counts_two_candidate_is_not_monotone`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.ChanceControls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Logic.LinearLogic.KnowledgeTensorWeight
open AnnotatedRuns (Firing firstOrder firstOrderTransport)
open FirstOrderNativeRuns
open KnowledgeTensorFirstOrderControls (plain one unlessNine makeSeven)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.Controls

/-! ## Absence -/

/-- The surrounding of the facts `S`: the occurrences with their numbers. -/
def surroundingOf (S : Finset (Fin 10)) : Configuration Nat Nat := ⟨[], S.map Fin.valEmbedding⟩

theorem mem_surroundingOf {S : Finset (Fin 10)} {o : ℕ} :
    o ∈ (surroundingOf S).present ↔ ∃ a ∈ S, a.val = o := by
  simp [surroundingOf]

/-- The one-firing grade of `unlessNine` beside a surrounding: neither the fact `7` nor `9`. -/
theorem unless_nine_graded (S : Finset (Fin 10)) :
    ((contextualRunInterpretation plain id).domain (left := one) (right := surroundingOf S)
        PUnit.unit unlessNineFiring ∧
      (contextualRunInterpretation plain id).check (left := one) (right := surroundingOf S)
        PUnit.unit unlessNineFiring) ↔
    Disjoint S {7, 9} := by
  have solved : plain.Models ()
      (makeSeven.problem id unlessNine (AnnotatedRuns.tensor one (surroundingOf S))) := by
    intro equation member
    cases member
  rw [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
  constructor
  · rintro ⟨_, fresh, _, guards, _⟩
    refine ⟨fun seven => ?_, fun nine => ?_⟩
    · have inside : (7 : ℕ) ∈ (surroundingOf S).present := mem_surroundingOf.mpr ⟨7, seven, rfl⟩
      exact Finset.disjoint_left.mp fresh (by decide) inside
    · have inside : (9 : ℕ) ∈ one.present ∪ (surroundingOf S).present :=
        Finset.mem_union_right _ (mem_surroundingOf.mpr ⟨9, nine, rfl⟩)
      exact guards (Check.absent 9) (List.mem_singleton_self _) () solved 9 inside rfl
  · rintro ⟨seven, nine⟩
    refine ⟨?_, ?_, ⟨(), solved⟩, ?_, ?_⟩
    · show Disjoint ([] : List ℕ).toFinset (surroundingOf S).present
      simp
    · show Disjoint ([7] : List ℕ).toFinset (surroundingOf S).present
      rw [Finset.disjoint_left]
      intro o made inside
      have isSeven : o = 7 := by simpa using made
      subst isSeven
      obtain ⟨a, member, value⟩ := mem_surroundingOf.mp inside
      have same : a = 7 := Fin.ext value
      exact seven (same ▸ member)
    · intro check member σ _
      obtain rfl := List.mem_singleton.mp member
      intro o inside matched
      have nineIs : (9 : ℕ) = o := matched
      subst nineIs
      rcases Finset.mem_union.mp inside with five | around
      · exact absurd five (by decide)
      · obtain ⟨a, member, value⟩ := mem_surroundingOf.mp around
        have same : a = 9 := Fin.ext value
        exact nine (same ▸ member)
    · intro query member
      cases member

/-- **The run of `unlessNine` is absence-only along the surroundings**, with forbidden set
`{7, 9}`: the label it forbids and the identity it makes. -/
theorem unless_nine_absence_along :
    AbsenceAlong (contextualRunInterpretation plain id) surroundingOf (fun _ => PUnit.unit)
      unlessNineRun {7, 9} := by
  have shape : ({7, 9} : Finset (Fin 10)) = {7, 9} ∪ ∅ := (Finset.union_empty _).symm
  rw [shape]
  exact AbsenceAlong.cons unless_nine_graded (AbsenceAlong.nil _)

/-- **Its survival chance** is `(1 - p 7) (1 - p 9)`. -/
theorem unless_nine_survival (p : Fin 10 → ℝ) :
    measure p (fun S => (contextualRunInterpretation plain id).Checks (left := one)
      (right := surroundingOf S) PUnit.unit unlessNineRun) = (1 - p 7) * (1 - p 9) := by
  rw [AbsenceAlong.survival (contextualRunInterpretation plain id) surroundingOf p
    unless_nine_absence_along, Finset.prod_pair (by decide)]

/-! ## Counting: admitted counts and candidate counts -/

/-- The facts `Fin 4`, each the occurrence one above its number: never the occurrence `0`. -/
def shifted : Fin 4 ↪ ℕ := ⟨fun a => a.val + 1, fun a b same => Fin.ext (by simpa using same)⟩

/-- The surrounding of the facts `S` beside the occurrence `0`. -/
def aroundZero (S : Finset (Fin 4)) : Configuration Nat Nat := ⟨[], S.map shifted⟩

theorem card_beside_zero (S : Finset (Fin 4)) :
    (zero.present ∪ (aroundZero S).present).card = S.card + 1 := by
  have apart : Disjoint zero.present (aroundZero S).present := by
    rw [Finset.disjoint_left]
    intro o inZero inS
    have isZero : o = 0 := Finset.mem_singleton.mp inZero
    obtain ⟨a, _, value⟩ := Finset.mem_map.mp inS
    have shiftedValue : a.val + 1 = o := value
    omega
  rw [Finset.card_union_of_disjoint apart]
  show ({0} : Finset ℕ).card + (S.map shifted).card = S.card + 1
  rw [Finset.card_map, Finset.card_singleton, add_comm]

/-- The one-firing grade of `counts number` at the occurrence `0`: the surrounding brings the count
to `number`. -/
theorem counts_graded (number : ℕ) (S : Finset (Fin 4)) :
    ((contextualRunInterpretation plain five).domain (left := zero) (right := aroundZero S)
        PUnit.unit (counts number) ∧
      (contextualRunInterpretation plain five).check (left := zero) (right := aroundZero S)
        PUnit.unit (counts number)) ↔
    S.card + 1 = number := by
  have solved : plain.Models ()
      ((counts number).selection.problem five (counts number).rule
        (AnnotatedRuns.tensor zero (aroundZero S))) := by
    intro equation member
    cases member
  constructor
  · rintro ⟨_, _, _, guards, _⟩
    have counted : (Check.matches plain () five (zero.present ∪ (aroundZero S).present) 5).card =
        number := guards (Check.count 5 number) (List.mem_singleton_self _) () solved
    rw [all_match, card_beside_zero] at counted
    exact counted
  · intro size
    refine ⟨?_, ?_, ⟨(), solved⟩, ?_, ?_⟩
    · show Disjoint ([] : List ℕ).toFinset (aroundZero S).present
      simp
    · show Disjoint ([] : List ℕ).toFinset (aroundZero S).present
      simp
    · intro check member σ _
      obtain rfl := List.mem_singleton.mp member
      show (Check.matches plain σ five (zero.present ∪ (aroundZero S).present) 5).card = number
      rw [all_match, card_beside_zero]
      exact size
    · intro query member
      cases member

theorem disjoint_univ_iff {S : Finset (Fin 4)} : Disjoint S Finset.univ ↔ S.card = 0 := by
  rw [Finset.card_eq_zero]
  constructor
  · intro apart
    exact Finset.eq_empty_of_forall_notMem fun a member =>
      Finset.disjoint_left.mp apart member (Finset.mem_univ a)
  · rintro rfl
    exact Finset.disjoint_empty_left _

/-- The run of `counts 1`, admitted at the occurrence `0`. -/
def countsOneRun : (firstOrder plain five).toStep.Run zero :=
  .cons (counts 1) counts_one_admitted (.nil _)

/-- **An admitted count is graded like absence**: `counts 1` at the occurrence `0` survives a
surrounding exactly when it adds no fact, every fact being labelled `5`. -/
theorem counts_one_absence_along :
    AbsenceAlong (contextualRunInterpretation plain five) aroundZero (fun _ => PUnit.unit)
      countsOneRun Finset.univ := by
  have shape : (Finset.univ : Finset (Fin 4)) = Finset.univ ∪ ∅ := (Finset.union_empty _).symm
  rw [shape]
  refine AbsenceAlong.cons (fun S => (counts_graded 1 S).trans ?_) (AbsenceAlong.nil _)
  rw [disjoint_univ_iff]
  constructor <;> intro size <;> omega

/-- `counts 2` is not admitted at the occurrence `0`. -/
theorem counts_two_not_admitted : ¬ (counts 2).Valid plain five zero :=
  a_count_is_enabled_by_its_context.2.1

/-- **A candidate count is graded by counting**: `counts 2` at `0` is placed exactly when the
surrounding adds one fact. -/
theorem counts_two_candidate (S : Finset (Fin 4)) :
    ((contextualRunInterpretation plain five).domain (left := zero) (right := aroundZero S)
        PUnit.unit (counts 2) ∧
      (contextualRunInterpretation plain five).check (left := zero) (right := aroundZero S)
        PUnit.unit (counts 2)) ↔
    (S ∩ Finset.univ).card = 1 := by
  rw [counts_graded 2 S, Finset.inter_univ]
  constructor <;> intro size <;> omega

/-- Its chance is the coefficient of `X` in `∏_a (1 - p a + p a X)`. -/
theorem counts_two_candidate_measure (p : Fin 4 → ℝ) :
    measure p (fun S =>
      (contextualRunInterpretation plain five).domain (left := zero) (right := aroundZero S)
          PUnit.unit (counts 2) ∧
        (contextualRunInterpretation plain five).check (left := zero) (right := aroundZero S)
          PUnit.unit (counts 2)) =
      (∏ a ∈ Finset.univ, (Polynomial.C (1 - p a) + Polynomial.C (p a) * Polynomial.X)).coeff 1 :=
  candidate_count_measure (contextualRunInterpretation plain five) aroundZero p
    (place := fun _ => PUnit.unit) counts_two_candidate

/-- **The candidate's grade is neither down- nor up-closed**: it accepts one fact and refuses
none and two. -/
theorem counts_two_candidate_is_not_monotone :
    ¬ ((contextualRunInterpretation plain five).domain (left := zero) (right := aroundZero ∅)
        PUnit.unit (counts 2) ∧
      (contextualRunInterpretation plain five).check (left := zero) (right := aroundZero ∅)
        PUnit.unit (counts 2)) ∧
    ((contextualRunInterpretation plain five).domain (left := zero) (right := aroundZero {0})
        PUnit.unit (counts 2) ∧
      (contextualRunInterpretation plain five).check (left := zero) (right := aroundZero {0})
        PUnit.unit (counts 2)) ∧
    ¬ ((contextualRunInterpretation plain five).domain (left := zero) (right := aroundZero {0, 1})
        PUnit.unit (counts 2) ∧
      (contextualRunInterpretation plain five).check (left := zero) (right := aroundZero {0, 1})
        PUnit.unit (counts 2)) := by
  rw [counts_graded 2 ∅, counts_graded 2 {0}, counts_graded 2 {0, 1}]
  decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.ChanceControls
