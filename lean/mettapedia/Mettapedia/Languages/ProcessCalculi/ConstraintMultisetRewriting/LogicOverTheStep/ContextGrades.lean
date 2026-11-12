import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.AbsenceNotCompositional
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.TransitionMaps

/-!
# Context grades: which predicates and modalities survive an added store

On the first-order step over ground terms (`base`), a **context change** puts a store beside the
current one (`beside`, the union of stores of `NullsOnTheStep.Composition`). Predicates are
reindexed along it by `pb`. Context changes compose: the empty store is the identity
(`beside_empty`) and adding two stores is adding their union (`beside_union`).

**The grade of a predicate** is the set of stores beside which it survives (`Grade`), that is, where
`φ ≤ pb (beside D) φ` (`grade_iff_le`). Grades are closed under conjunction, disjunction and union of
contexts (`grade_and`, `grade_or`, `grade_union`).

## Which predicates survive

* **Positive predicates survive every context**: presence of a label (`present_grade`) and counts
  from below (`countAtLeast_grade`).
* **Absence survives exactly where the added store lacks the pattern** (`absent_grade_iff`).
* **Exact counts survive exactly beside the stores without the pattern** (`count_grade_iff`, from
  `count_grade_of_absent`; the count zero is absence, `count_zero_grade_iff`).

## Which firings and modalities survive

* **The grade of a firing** whose checks are absences is the conjunction of their grades
  (`absences_union_iff`, generalizing `Composition.guarded_union_iff` from one absence to any list).
* **Possibility through a positive firing survives** every fresh context with trivial knowledge
  (`positive_possible_beside`).
* **Absence invalidated by an added context, modally** (`absence_invalidated_beside`): on the
  four-rule theory of `NullsOnTheStep.Separations`, a successor is possible at the empty store
  (`spawn` makes `T` where `U` is absent) and impossible beside the store holding `U`.
* **Successor necessity does not survive an added context, even with no absence anywhere**
  (`successorBox_not_kept`): "no successor" holds of the store holding `U` and fails beside the store
  holding `T`, where `drop` fires.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ContextGrades

open Mettapedia.OSLF.Framework.DerivedModalities
open FragmentsOfTheStep.TransitionMaps
open NamesOnTheStep NamesOnTheStep.IssuingControls
open NullsOnTheStep NullsOnTheStep.Composition

/-! ## Context changes -/

/-- **Putting a store beside**: the context change. -/
def beside (D : Conf) (C : Conf) : Conf := union C D

/-- The empty context. -/
def emptyContext : Conf := ⟨[], ∅⟩

/-- **The empty context is the identity change.** -/
theorem beside_empty (C : Conf) : beside emptyContext C = C := by
  cases C
  simp [beside, union, emptyContext]

/-- **Adding two stores is adding their union.** -/
theorem beside_union (D E C : Conf) : beside (union D E) C = beside E (beside D C) := by
  simp [beside, union, List.append_assoc, Finset.union_assoc]

/-- **The grade of a predicate**: the stores beside which it survives. -/
def Grade (φ : Conf → Prop) (D : Conf) : Prop := ∀ C, φ C → φ (beside D C)

/-- The grade is where the predicate lies below its reindexing along the context. -/
theorem grade_iff_le (φ : Conf → Prop) (D : Conf) : Grade φ D ↔ φ ≤ pb (beside D) φ := by
  constructor
  · intro grade C holds
    exact grade C holds
  · intro le C holds
    exact le C holds

theorem grade_and {φ ψ : Conf → Prop} {D : Conf} (first : Grade φ D) (second : Grade ψ D) :
    Grade (fun C => φ C ∧ ψ C) D :=
  fun C holds => ⟨first C holds.1, second C holds.2⟩

theorem grade_or {φ ψ : Conf → Prop} {D : Conf} (first : Grade φ D) (second : Grade ψ D) :
    Grade (fun C => φ C ∨ ψ C) D :=
  fun C holds => holds.elim (fun h => Or.inl (first C h)) (fun h => Or.inr (second C h))

/-- **Grades are closed under the union of contexts.** -/
theorem grade_union {φ : Conf → Prop} {D E : Conf} (first : Grade φ D) (second : Grade φ E) :
    Grade φ (union D E) := by
  intro C holds
  rw [beside_union]
  exact second _ (first C holds)

theorem grade_empty (φ : Conf → Prop) : Grade φ emptyContext := by
  intro C holds
  rw [beside_empty]
  exact holds

/-! ## Which predicates survive -/

/-- Some occurrence is labelled `p`. -/
def Present (p : Expr) (C : Conf) : Prop := ∃ o ∈ C.present, o.1 = p

/-- No occurrence is labelled `p`. -/
def Absent (p : Expr) (C : Conf) : Prop := (Check.absent p).Holds ground () Prod.fst C.present

/-- Exactly `n` occurrences are labelled `p`. -/
def CountIs (p : Expr) (n : ℕ) (C : Conf) : Prop :=
  (Check.count p n).Holds ground () Prod.fst C.present

/-- At least `n` occurrences are labelled `p`. -/
def CountAtLeast (p : Expr) (n : ℕ) (C : Conf) : Prop :=
  n ≤ (Check.«matches» ground () Prod.fst C.present p).card

/-- **Presence survives every context.** -/
theorem present_grade (p : Expr) (D : Conf) : Grade (Present p) D := by
  rintro C ⟨o, member, labelled⟩
  exact ⟨o, Finset.mem_union_left _ member, labelled⟩

/-- **Counts from below survive every context.** -/
theorem countAtLeast_grade (p : Expr) (n : ℕ) (D : Conf) : Grade (CountAtLeast p n) D := by
  intro C atLeast
  refine le_trans atLeast (Finset.card_le_card ?_)
  intro o member
  simp only [Check.«matches», Finset.mem_filter, beside, union, Finset.mem_union] at member ⊢
  exact ⟨Or.inl member.1, member.2⟩

/-- **The grade of absence is exactly the stores without the pattern.** -/
theorem absent_grade_iff (p : Expr) (D : Conf) : Grade (Absent p) D ↔ Absent p D := by
  constructor
  · intro grade
    have onUnion := grade emptyContext (fun o member => by simp [emptyContext] at member)
    exact (absent_union_iff.mp onUnion).2
  · intro onD C onC
    exact absent_union_iff.mpr ⟨onC, onD⟩

/-- **Exact counts survive beside every store without the pattern.** -/
theorem count_grade_of_absent {p : Expr} {D : Conf} (clear : Absent p D) (n : ℕ) :
    Grade (CountIs p n) D := by
  intro C counted
  show (Check.«matches» ground () Prod.fst (C.present ∪ D.present) p).card = n
  have same : Check.«matches» ground () Prod.fst (C.present ∪ D.present) p =
      Check.«matches» ground () Prod.fst C.present p := by
    ext o
    simp only [Check.«matches», Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨inC | inD, matched⟩
      · exact ⟨inC, matched⟩
      · exact absurd matched (clear o inD)
    · rintro ⟨inC, matched⟩
      exact ⟨Or.inl inC, matched⟩
  rw [same]
  exact counted

/-- The count zero is absence. -/
theorem countIs_zero_iff (p : Expr) (C : Conf) : CountIs p 0 C ↔ Absent p C := by
  constructor
  · intro zero o member matched
    have empty : Check.«matches» ground () Prod.fst C.present p = ∅ := Finset.card_eq_zero.mp zero
    have inside : o ∈ Check.«matches» ground () Prod.fst C.present p := by
      simp only [Check.«matches», Finset.mem_filter]
      exact ⟨member, matched⟩
    rw [empty] at inside
    simp at inside
  · intro clear
    show (Check.«matches» ground () Prod.fst C.present p).card = 0
    rw [Finset.card_eq_zero]
    ext o
    simp only [Check.«matches», Finset.mem_filter]
    constructor
    · rintro ⟨member, matched⟩
      exact absurd matched (clear o member)
    · intro inEmpty
      simp at inEmpty

/-- **For the count zero the grade is exact.** -/
theorem count_zero_grade_iff (p : Expr) (D : Conf) : Grade (CountIs p 0) D ↔ Absent p D := by
  have same : CountIs p 0 = Absent p := funext fun C => propext (countIs_zero_iff p C)
  rw [same]
  exact absent_grade_iff p D

/-- **The grade of every exact count is exactly the stores without the pattern**: beside a store
holding an occurrence of `p`, a store with `n` fresh occurrences of `p` counts more than `n`. -/
theorem count_grade_iff (p : Expr) (n : ℕ) (D : Conf) : Grade (CountIs p n) D ↔ Absent p D := by
  refine ⟨fun grade => ?_, fun clear => count_grade_of_absent clear n⟩
  intro o member labelled
  have isP : p = o.1 := labelled
  let C : Conf := ⟨[], (Finset.range n).image (fun k => (p, k + o.2 + 1))⟩
  have allP : ∀ q ∈ C.present, q.1 = p := by
    intro q inside
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp inside
    rfl
  have fresh : o ∉ C.present := by
    intro inside
    obtain ⟨k, _, same⟩ := Finset.mem_image.mp inside
    have later : k + o.2 + 1 = o.2 := congrArg Prod.snd same
    omega
  have matchesC : Check.«matches» ground () Prod.fst C.present p = C.present := by
    ext q
    simp only [Check.«matches», Finset.mem_filter]
    constructor
    · exact fun inside => inside.1
    · intro inside
      exact ⟨inside, (allP q inside).symm⟩
  have cardC : C.present.card = n := by
    show ((Finset.range n).image (fun k => (p, k + o.2 + 1))).card = n
    rw [Finset.card_image_of_injective _ (fun a b same => by simpa using congrArg Prod.snd same),
      Finset.card_range]
  have counted : CountIs p n C := by
    show (Check.«matches» ground () Prod.fst C.present p).card = n
    rw [matchesC, cardC]
  have more : (Check.«matches» ground () Prod.fst (C.present ∪ D.present) p).card = n :=
    grade C counted
  have strict : C.present ⊂ Check.«matches» ground () Prod.fst (C.present ∪ D.present) p := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨o, ?_, fresh⟩
      simp only [Check.«matches», Finset.mem_filter, Finset.mem_union]
      exact ⟨Or.inr member, isP⟩
    · intro q inside
      simp only [Check.«matches», Finset.mem_filter, Finset.mem_union]
      exact ⟨Or.inl inside, (allP q inside).symm⟩
  have grows := Finset.card_lt_card strict
  omega

/-! ## Which firings and modalities survive -/

/-- Every check of an admitted first-order firing holds at the store it fires from. -/
theorem check_holds {C : Conf} {f : Fir} (admitted : base.Admits (s := C) f) {c : Check Expr}
    (member : c ∈ f.rule.checks) : c.Holds ground () Prod.fst C.present := by
  have valid : f.Valid ground Prod.fst C := admitted
  obtain ⟨u, solved⟩ := valid.firing.consistent
  exact valid.firing.checks c member u solved

/-- **The grade of a firing is the conjunction of its absence grades.** -/
theorem absences_union_iff {C D : Conf} {f : Fir} {ps : List Expr}
    (checks : f.rule.checks = ps.map Check.absent) (noQueries : f.queries = [])
    (admitted : base.Admits (s := C) f)
    (freshInD : ∀ o ∈ f.selection.made, o ∉ D.present) (knowledgeD : ∀ e ∈ D.equations, e.1 = e.2) :
    base.Admits (s := union C D) f ↔ ∀ p ∈ ps, Absent p D := by
  constructor
  · intro onUnion p member
    have holds := check_holds onUnion (c := .absent p) (by rw [checks]; exact List.mem_map_of_mem member)
    exact (absent_union_iff.mp holds).2
  · intro onD
    refine valid_union admitted freshInD knowledgeD ?_ noQueries
    intro c member
    rw [checks] at member
    obtain ⟨p, inPs, rfl⟩ := List.mem_map.mp member
    exact absent_union_iff.mpr
      ⟨check_holds admitted (by rw [checks]; exact List.mem_map_of_mem inPs), onD p inPs⟩

/-- The successors of the first-order step. -/
def baseSucc (C C' : Conf) : Prop := ∃ (f : Fir) (a : base.Admits (s := C) f), base.result (s := C) f a = C'

/-- **Possibility through a positive firing survives** every fresh context with trivial
knowledge. -/
theorem positive_possible_beside {C D : Conf} {f : Fir} (noChecks : f.rule.checks = [])
    (noQueries : f.queries = []) (admitted : base.Admits (s := C) f)
    (freshInD : ∀ o ∈ f.selection.made, o ∉ D.present) (knowledgeD : ∀ e ∈ D.equations, e.1 = e.2) :
    derivedDiamond (span baseSucc) (fun _ => True) (beside D C) :=
  (diamond_iff _ _ _).mpr
    ⟨_, ⟨f, positive_monotone noChecks noQueries admitted freshInD knowledgeD, rfl⟩, trivial⟩

/-- The successors of the four-rule theory, with its ledger. -/
def spSucc (s s' : Conf × Set ℕ) : Prop :=
  ∃ (f : Fir × List ℕ) (a : Separations.sp.Admits (s := s) f), Separations.sp.result (s := s) f a = s'

/-- Putting a store, with its ledger, beside. -/
def besideL (D : Conf × Set ℕ) (s : Conf × Set ℕ) : Conf × Set ℕ := (union s.1 D.1, s.2 ∪ D.2)

theorem besideL_onlyU_emptyS : besideL Separations.onlyU Separations.emptyS = Separations.onlyU := by
  simp [besideL, union, Separations.onlyU, Separations.emptyS]

/-- **Absence invalidated by an added context, modally.** At the empty store a successor is
possible (`spawn` makes `T` where `U` is absent); beside the store holding `U` none is. -/
theorem absence_invalidated_beside :
    derivedDiamond (span spSucc) (fun _ => True) Separations.emptyS ∧
      ¬ derivedDiamond (span spSucc) (fun _ => True) (besideL Separations.onlyU Separations.emptyS) := by
  refine ⟨(diamond_iff _ _ _).mpr ⟨_, ⟨Separations.spawnAt, Separations.spawn_admitted, rfl⟩, trivial⟩,
    ?_⟩
  rw [besideL_onlyU_emptyS]
  intro possible
  obtain ⟨_, ⟨f, a, _⟩, _⟩ := (diamond_iff _ _ _).mp possible
  exact Separations.onlyU_no_successor f a

/-- **Successor necessity does not survive an added context, even with no absence anywhere**:
"no successor" holds of the store holding `U`, and beside the store holding `T` the firing of
`drop` appears. -/
theorem successorBox_not_kept :
    derivedForwardBox (span spSucc) (fun _ => False) Separations.onlyU ∧
      ¬ derivedForwardBox (span spSucc) (fun _ => False)
        (besideL Separations.onlyT Separations.onlyU) := by
  refine ⟨(forwardBox_iff _ _ _).mpr fun s' succ => ?_, fun never => ?_⟩
  · obtain ⟨f, a, _⟩ := succ
    exact Separations.onlyU_no_successor f a
  · have admitted : Separations.sp.Admits (s := besideL Separations.onlyT Separations.onlyU)
        Separations.dropAt :=
      admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
        ⟨Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    exact (forwardBox_iff _ _ _).mp never _ ⟨_, admitted, rfl⟩

#print axioms beside_empty
#print axioms beside_union
#print axioms grade_iff_le
#print axioms grade_union
#print axioms present_grade
#print axioms countAtLeast_grade
#print axioms absent_grade_iff
#print axioms count_grade_of_absent
#print axioms count_zero_grade_iff
#print axioms count_grade_iff
#print axioms absences_union_iff
#print axioms positive_possible_beside
#print axioms absence_invalidated_beside
#print axioms successorBox_not_kept

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ContextGrades
