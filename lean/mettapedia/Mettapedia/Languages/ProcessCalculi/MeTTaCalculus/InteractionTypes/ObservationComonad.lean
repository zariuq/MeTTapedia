import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ChannelAddressing

/-!
# Observation rights as a graded comonad

Restriction to held names (`OccurrenceCommits.restrict`) is deflationary, idempotent and graded by
rights under meet. On the poset of stores those are the laws of a graded comonad, but in a poset
every diagram commutes, so calling it a graded comonad adds nothing to the factorization lemmas it
is used through. This module gives the structure that does carry content.

## The graded comonad

Grades are rights (`N → Bool`), combined by union, with no rights as the unit. `Graded r X` is a
value of `X` together with a store whose occurrences all lie at names in `r`: what an observer with
rights `r` sees, beside its input. This is the coeffect form of the product comonad.

* `extract : Graded none X → X` forgets an empty view;
* `duplicate : Graded (r ∪ s) X → Graded r (Graded s X)` splits a view into the views of `r` and
  `s`;
* `gmap` acts on the value, and `regrade` widens the grade.

The laws hold on the nose, with one regrading at the input where the grades differ only by the
monoid laws (`gmap_id`, `gmap_comp`, `extract_duplicate`, `gmap_extract_duplicate`,
`duplicate_assoc`, `duplicate_natural`). Unlike the restriction family on the poset of stores,
this category is not thin: its maps are functions on views.

## What it buys: grades are exactly non-interference, and every observer has a support

A map out of `Graded r Unit`, read on whole stores through restriction, is an **observer of grade
`r`**. The grade is a semantic property of the observer:

* **Factorization** (`ofGrade_iff_factors`): an observer `f` of stores is of grade `r` (stores that
  agree at the names of `r` look alike to it) exactly when it factors through the view of `r`.
* **Weakening and composition** (`OfGrade.mono`, `OfGrade.comp`): grades may be widened, and an
  observer that combines a grade-`r` observation with a grade-`s` one has grade `r ∪ s`: the
  coKleisli composition of the graded comonad.
* **Grades are closed under meet** (`OfGrade.inf`): if an observer depends only on the names of
  `r` and only on the names of `s`, it depends only on the names of both. Over finitely many names,
  every observer has a **least grade**, its support (`exists_least_grade`), as finitely supported
  elements of a nominal set have a least support.
* **Processes**: the run of a list of commits scoped to rights `r` is an observer of grade `r`,
  both in which runs execute and in the held part of where they end (`run_ofGrade`), which is the
  non-interference theorem of channel addressing read as a typing.
* **A pattern-addressed reader has the wrong grade** (`Controls.wildcard_not_ofGrade`): the absence
  of messages at every name is not of the grade of the one name its reader holds. Renaming-invariance
  of names would not exclude it; grades do.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v w x y

variable {O : Type u} [DecidableEq O] {R : Type v} {N : Type w}

/-! ## Grades -/

/-- The union of two grades. -/
def gradeUnion (r s : N → Bool) : N → Bool := fun n => r n || s n

/-- The meet of two grades. -/
def gradeMeet (r s : N → Bool) : N → Bool := fun n => r n && s n

/-- The empty grade. -/
def noRights : N → Bool := fun _ => false

/-- One grade lies within another. -/
def GradeLE (r s : N → Bool) : Prop := ∀ n, r n = true → s n = true

section Views

variable (label : O → R) (loc : R → N)

/-- A store lies within a grade: its occurrences are at names of the grade. -/
def Within (r : N → Bool) (S : Finset O) : Prop := ∀ o ∈ S, r (loc (label o)) = true

/-- **The graded functor**: a value beside a view of grade `r`. -/
def Graded (r : N → Bool) (X : Type x) : Type (max u x) :=
  {p : Finset O × X // Within label loc r p.1}

variable {label loc}

omit [DecidableEq O] in
theorem within_restrict (r : N → Bool) (S : Finset O) : Within label loc r (restrict label loc r S) :=
  fun _ member => (mem_restrict.mp member).2

omit [DecidableEq O] in
theorem restrict_of_within {r : N → Bool} {S : Finset O} (within : Within label loc r S) :
    restrict label loc r S = S := by
  ext o
  simp only [mem_restrict, and_iff_left_iff_imp]
  exact within o

omit [DecidableEq O] in
theorem Within.mono {r s : N → Bool} (le : GradeLE r s) {S : Finset O} (within : Within label loc r S) :
    Within label loc s S := fun o member => le _ (within o member)

variable {X : Type x} {Y : Type y} {Z : Type y}

/-- The action on values. -/
def gmap {r : N → Bool} (f : X → Y) (g : Graded label loc r X) : Graded label loc r Y :=
  ⟨(g.val.1, f g.val.2), g.property⟩

/-- **The counit**: an empty view is forgotten. -/
def extract (g : Graded label loc noRights X) : X := g.val.2

/-- **The comultiplication**: a view of `r ∪ s` splits into a view of `r` and a view of `s`. -/
def duplicate {r s : N → Bool} (g : Graded label loc (gradeUnion r s) X) :
    Graded label loc r (Graded label loc s X) :=
  ⟨(restrict label loc r g.val.1, ⟨(restrict label loc s g.val.1, g.val.2), within_restrict s _⟩),
    within_restrict r _⟩

/-- **Widening a grade.** -/
def regrade {r s : N → Bool} (le : GradeLE r s) (g : Graded label loc r X) : Graded label loc s X :=
  ⟨g.val, g.property.mono le⟩

omit [DecidableEq O] in
theorem gmap_id {r : N → Bool} (g : Graded label loc r X) : gmap id g = g := rfl

omit [DecidableEq O] in
theorem gmap_comp {r : N → Bool} (f : X → Y) (h : Y → Z) (g : Graded label loc r X) :
    gmap (h ∘ f) g = gmap h (gmap f g) := rfl

theorem le_union_left (r s : N → Bool) : GradeLE r (gradeUnion r s) := fun n h => by
  simp [gradeUnion, h]

theorem le_union_right (r s : N → Bool) : GradeLE s (gradeUnion r s) := fun n h => by
  simp [gradeUnion, h]

omit [DecidableEq O] in
/-- **Counit law, right**: splitting off an empty view and forgetting it gives back the view. -/
theorem extract_duplicate {r : N → Bool} (g : Graded label loc r X) :
    extract (duplicate (r := noRights) (s := r) (regrade (le_union_right noRights r) g)) = g := by
  apply Subtype.ext
  simp only [extract, duplicate, regrade]
  rw [restrict_of_within g.property]

omit [DecidableEq O] in
/-- **Counit law, left**: splitting off an empty inner view and forgetting it gives back the view. -/
theorem gmap_extract_duplicate {r : N → Bool} (g : Graded label loc r X) :
    gmap extract (duplicate (r := r) (s := noRights) (regrade (le_union_left r noRights) g)) = g := by
  apply Subtype.ext
  simp only [gmap, extract, duplicate, regrade]
  rw [restrict_of_within g.property]

/-- The two groupings of three grades lie within each other. -/
theorem union_assoc_le (r s t : N → Bool) :
    GradeLE (gradeUnion r (gradeUnion s t)) (gradeUnion (gradeUnion r s) t) := fun n h => by
  simp only [gradeUnion, Bool.or_eq_true] at h ⊢
  tauto

omit [DecidableEq O] in
/-- **Coassociativity**: splitting `r ∪ (s ∪ t)` as `r`, then `s ∪ t` as `s` and `t`, is splitting
`(r ∪ s) ∪ t` as `r ∪ s` and `t`, then `r ∪ s` as `r` and `s`. -/
theorem duplicate_assoc {r s t : N → Bool} (g : Graded label loc (gradeUnion r (gradeUnion s t)) X) :
    gmap (duplicate (r := s) (s := t)) (duplicate (r := r) (s := gradeUnion s t) g) =
      duplicate (r := r) (s := s)
        (duplicate (r := gradeUnion r s) (s := t) (regrade (union_assoc_le r s t) g)) := by
  have inner : ∀ (a b : N → Bool), GradeLE a b → ∀ S : Finset O,
      restrict label loc a (restrict label loc b S) = restrict label loc a S := by
    intro a b le S
    rw [restrict_restrict]
    congr 1
    funext n
    cases ha : a n <;> simp [ha, le n]
  apply Subtype.ext
  simp only [gmap, duplicate, regrade, inner r (gradeUnion r s) (le_union_left r s),
    inner s (gradeUnion s t) (le_union_left s t), inner s (gradeUnion r s) (le_union_right r s),
    inner t (gradeUnion s t) (le_union_right s t)]

omit [DecidableEq O] in
/-- **Naturality** of the comultiplication. -/
theorem duplicate_natural {r s : N → Bool} (f : X → Y) (g : Graded label loc (gradeUnion r s) X) :
    duplicate (gmap f g) = gmap (gmap f) (duplicate g) := rfl

end Views

/-! ## Observers and their grades -/

section Observers

variable {label : O → R} {loc : R → N} {Y : Type y}

/-- **An observer of grade `r`**: stores that agree at the names of `r` look alike to it. -/
def OfGrade (label : O → R) (loc : R → N) (r : N → Bool) (f : Finset O → Y) : Prop :=
  ∀ S S', restrict label loc r S = restrict label loc r S' → f S = f S'

/-- The view of grade `r` of a whole store. -/
def view (r : N → Bool) (S : Finset O) : Graded label loc r Unit :=
  ⟨(restrict label loc r S, ()), within_restrict r S⟩

omit [DecidableEq O] in
/-- **Factorization**: an observer has grade `r` exactly when it is a map out of the views of
grade `r`, read through restriction. -/
theorem ofGrade_iff_factors {r : N → Bool} {f : Finset O → Y} :
    OfGrade label loc r f ↔ ∃ k : Graded label loc r Unit → Y, ∀ S, f S = k (view r S) := by
  constructor
  · intro grade
    refine ⟨fun g => f g.val.1, fun S => ?_⟩
    apply grade
    simp only [view]
    rw [restrict_idem]
  · rintro ⟨k, factors⟩ S S' agree
    rw [factors, factors]
    simp only [view, agree]

omit [DecidableEq O] in
/-- **Weakening**: a grade may be widened. -/
theorem OfGrade.mono {r s : N → Bool} (le : GradeLE r s) {f : Finset O → Y}
    (grade : OfGrade label loc r f) : OfGrade label loc s f := by
  intro S S' agree
  apply grade
  have narrow : ∀ T : Finset O, restrict label loc r (restrict label loc s T) = restrict label loc r T := by
    intro T
    rw [restrict_restrict]
    congr 1
    funext n
    cases hr : r n <;> simp [hr, le n]
  rw [← narrow S, agree, narrow]

omit [DecidableEq O] in
/-- **Composition**: combining an observation of grade `r` with one of grade `s` has grade
`r ∪ s`. -/
theorem OfGrade.comp {Z : Type y} {r s : N → Bool} {f : Finset O → Y}
    {g : Finset O → Y → Z} (gradeF : OfGrade label loc r f)
    (gradeG : ∀ yv, OfGrade label loc s (fun S => g S yv)) :
    OfGrade label loc (gradeUnion r s) (fun S => g S (f S)) := by
  intro S S' agree
  have restrictR : restrict label loc r S = restrict label loc r S' := by
    have := congrArg (restrict label loc r) agree
    rwa [restrict_restrict, restrict_restrict,
      show (fun n => r n && gradeUnion r s n) = r from funext fun n => by
        cases h : r n <;> simp [gradeUnion, h]] at this
  have restrictS : restrict label loc s S = restrict label loc s S' := by
    have := congrArg (restrict label loc s) agree
    rwa [restrict_restrict, restrict_restrict,
      show (fun n => s n && gradeUnion r s n) = s from funext fun n => by
        cases h : s n <;> simp [gradeUnion, h]] at this
  show g S (f S) = g S' (f S')
  rw [gradeF S S' restrictR]
  exact gradeG (f S') S S' restrictS

/-- **Grades are closed under meet**: an observer that depends only on the names of `r` and only on
the names of `s` depends only on the names of both. -/
theorem OfGrade.inf {r s : N → Bool} {f : Finset O → Y} (gradeR : OfGrade label loc r f)
    (gradeS : OfGrade label loc s f) : OfGrade label loc (gradeMeet r s) f := by
  intro S S' agree
  -- A store that agrees with `S` at `r` and with `S'` at `s`.
  let mixed := restrict label loc r S ∪ restrict label loc (fun n => !r n) S'
  have atR : restrict label loc r mixed = restrict label loc r S := by
    ext o
    simp only [mixed, mem_restrict, Finset.mem_union]
    constructor
    · rintro ⟨⟨inS, _⟩ | ⟨_, notR⟩, isR⟩
      · exact ⟨inS, isR⟩
      · simp [isR] at notR
    · rintro ⟨inS, isR⟩
      exact ⟨Or.inl ⟨inS, isR⟩, isR⟩
  have atS : restrict label loc s mixed = restrict label loc s S' := by
    ext o
    have pointwise := congrArg (fun T => o ∈ T) agree
    simp only [mem_restrict, gradeMeet, Bool.and_eq_true] at pointwise
    simp only [mixed, mem_restrict, Finset.mem_union, Bool.not_eq_true']
    constructor
    · rintro ⟨⟨inS, isR⟩ | ⟨inS', _⟩, isS⟩
      · exact ⟨(pointwise.mp ⟨inS, isR, isS⟩).1, isS⟩
      · exact ⟨inS', isS⟩
    · rintro ⟨inS', isS⟩
      cases hr : r (loc (label o))
      · exact ⟨Or.inr ⟨inS', rfl⟩, isS⟩
      · exact ⟨Or.inl ⟨(pointwise.mpr ⟨inS', hr, isS⟩).1, rfl⟩, isS⟩
  rw [← gradeR mixed S atR, gradeS mixed S' atS]

omit [DecidableEq O] in
/-- Every observer has the grade of all names. -/
theorem ofGrade_top (f : Finset O → Y) : OfGrade label loc (fun _ => true) f := by
  intro S S' agree
  rw [restrict_top, restrict_top] at agree
  rw [agree]

/-- **The least grade**: over finitely many names, the grades of an observer have a least element,
its support. -/
theorem exists_least_grade [Fintype N] [DecidableEq N] (f : Finset O → Y) :
    ∃ r, OfGrade label loc r f ∧ ∀ s, OfGrade label loc s f → GradeLE r s := by
  classical
  let grades : Finset (N → Bool) := Finset.univ.filter fun r => OfGrade label loc r f
  let least : N → Bool := fun n => decide (∀ r ∈ grades, r n = true)
  have closed : ∀ T : Finset (N → Bool), (∀ r ∈ T, OfGrade label loc r f) →
      OfGrade label loc (fun n => decide (∀ r ∈ T, r n = true)) f := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro _
        simpa using ofGrade_top (label := label) (loc := loc) f
    | insert r T notIn ih =>
        intro all
        have rest := ih fun s member => all s (Finset.mem_insert_of_mem member)
        have both := OfGrade.inf (all r (Finset.mem_insert_self r T)) rest
        have same : gradeMeet r (fun n => decide (∀ s ∈ T, s n = true)) =
            fun n => decide (∀ s ∈ insert r T, s n = true) := by
          funext n
          simp [gradeMeet]
        rw [same] at both
        exact both
  refine ⟨least, closed grades fun r member => (Finset.mem_filter.mp member).2, fun s grade n held => ?_⟩
  have := of_decide_eq_true held
  exact this s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, grade⟩)

/-- **Runs of scoped commits are observers of their grade**: which runs execute, and the held part
of where they end, depend only on the store at the held names. -/
theorem run_ofGrade {r : N → Bool} {run : List (Commit O R)}
    (inScope : ∀ e ∈ run, Scoped label loc r e) :
    OfGrade label loc r (fun S => (Executable label S run, restrict label loc r (fireList S run))) := by
  intro S S' agree
  obtain ⟨sameRun, sameEnd⟩ := noninterference inScope agree
  show (_, _) = (_, _)
  rw [propext sameRun, sameEnd]

end Observers

/-! ## Controls -/

namespace Controls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Controls

/-- The absence of messages at every name, as an observer. -/
def anywhereAbsent (S : Finset ℕ) : Prop := AbsenceHolds chanLabel anywhere S

/-- The absence of messages at name `0`, as an observer. -/
def zeroAbsent (S : Finset ℕ) : Prop := AbsenceHolds chanLabel atZero S

/-- **A pattern-addressed reader has the wrong grade**: the absence of messages anywhere is not an
observer of the grade of name `0`. -/
theorem wildcard_not_ofGrade : ¬ OfGrade chanLabel Prod.fst holdsZero anywhereAbsent := by
  intro grade
  obtain ⟨agree, -, -, emptyAbsent, notAbsent⟩ := wildcard_breaks_noninterference
  have := grade ∅ {51} agree
  unfold anywhereAbsent at this
  rw [this] at emptyAbsent
  exact notAbsent emptyAbsent

/-- **The scoped reader has the grade of its name.** -/
theorem scoped_ofGrade : OfGrade chanLabel Prod.fst holdsZero zeroAbsent := by
  intro S S' agree
  unfold zeroAbsent
  rw [absenceHolds_iff, absenceHolds_iff]
  apply propext
  have inside : ∀ r, atZero r = true → holdsZero r.1 = true := by
    intro r h
    simp only [atZero, Bool.and_eq_true, beq_iff_eq] at h
    simp [holdsZero, h.1]
  constructor
  · intro none o inS'
    cases isZero : atZero (chanLabel o)
    · rfl
    · have inRestrict : o ∈ restrict chanLabel Prod.fst holdsZero S' :=
        mem_restrict.mpr ⟨inS', inside _ isZero⟩
      rw [← agree] at inRestrict
      have := none o (mem_restrict.mp inRestrict).1
      rw [isZero] at this
      exact absurd this (by decide)
  · intro none o inS
    cases isZero : atZero (chanLabel o)
    · rfl
    · have inRestrict : o ∈ restrict chanLabel Prod.fst holdsZero S :=
        mem_restrict.mpr ⟨inS, inside _ isZero⟩
      rw [agree] at inRestrict
      have := none o (mem_restrict.mp inRestrict).1
      rw [isZero] at this
      exact absurd this (by decide)

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes
