import Mettapedia.Computability.RegularLanguages.ClassExpressions

/-!
# Exact equality of finite interval classes

A canonical list contains valid, ascending maximal intervals: consecutive
components neither overlap nor touch. Equality of these lists is equivalent to
independently specified pointwise membership. Normalization therefore gives an
exact decision procedure, including for composed class expressions with explicit
complement domains. These laws concern interval algorithms, not unchecked C
allocations, pointer bounds, or a general GSLT equation solver.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.CanonicalClasses

open IntervalClasses

/-- Components are valid and separated by at least one absent point. -/
def Canonical : List Interval → Prop
  | [] => True
  | head :: rest =>
      head.Valid ∧ (∀ next ∈ rest, head.high + 1 < next.low) ∧ Canonical rest

theorem canonical_valid (ranges : List Interval) (canonical : Canonical ranges) :
    Valid ranges := by
  induction ranges with
  | nil => simp [Valid]
  | cons head rest ih =>
      intro range member
      rcases List.mem_cons.mp member with equal | member
      · subst range
        exact canonical.1
      · exact ih canonical.2.2 range member

theorem head_low_le_member (head : Interval) (rest : List Interval)
    (canonical : Canonical (head :: rest)) (point : Nat)
    (present : Contains (head :: rest) point) : head.low ≤ point := by
  rcases contains_cons head rest point |>.mp present with present | present
  · exact present.1
  · obtain ⟨range, member, present⟩ := present
    have separated := canonical.2.1 range member
    have valid := canonical.1
    simp only [Interval.Valid, Interval.Contains] at valid present
    omega

theorem tail_member_above_head (head : Interval) (rest : List Interval)
    (canonical : Canonical (head :: rest)) (point : Nat)
    (present : Contains rest point) : head.high + 1 < point := by
  obtain ⟨range, member, present⟩ := present
  have separated := canonical.2.1 range member
  simp only [Interval.Contains] at present
  omega

theorem head_successor_absent (head : Interval) (rest : List Interval)
    (canonical : Canonical (head :: rest)) :
    ¬ Contains (head :: rest) (head.high + 1) := by
  intro present
  rcases (contains_cons _ _ _).mp present with present | present
  · simp only [Interval.Contains] at present
    omega
  · have impossible := tail_member_above_head head rest canonical _ present
    omega

/-- Independent membership determines every endpoint of a maximal run. -/
theorem canonical_unique (left right : List Interval)
    (hl : Canonical left) (hr : Canonical right)
    (same : ∀ point, Contains left point ↔ Contains right point) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head rest =>
          have present : Contains (head :: rest) head.low :=
            (contains_cons _ _ _).mpr (Or.inl ⟨le_rfl, hr.1⟩)
          exact False.elim (contains_nil _ ((same _).mpr present))
  | cons head rest ih =>
      cases right with
      | nil =>
          have present : Contains (head :: rest) head.low :=
            (contains_cons _ _ _).mpr (Or.inl ⟨le_rfl, hl.1⟩)
          exact False.elim (contains_nil _ ((same _).mp present))
      | cons other tail =>
          have atLeft : Contains (head :: rest) head.low :=
            (contains_cons _ _ _).mpr (Or.inl ⟨le_rfl, hl.1⟩)
          have atRight : Contains (other :: tail) other.low :=
            (contains_cons _ _ _).mpr (Or.inl ⟨le_rfl, hr.1⟩)
          have lower := head_low_le_member other tail hr _ ((same _).mp atLeft)
          have upper := head_low_le_member head rest hl _ ((same _).mpr atRight)
          have lowEqual : head.low = other.low := by omega
          have highEqual : head.high = other.high := by
            apply Nat.le_antisymm
            · by_contra notLe
              have present : Contains (head :: rest) (other.high + 1) := by
                apply (contains_cons _ _ _).mpr
                left
                have valid := hr.1
                simp only [Interval.Valid, Interval.Contains] at valid ⊢
                omega
              exact head_successor_absent other tail hr ((same _).mp present)
            · by_contra notLe
              have present : Contains (other :: tail) (head.high + 1) := by
                apply (contains_cons _ _ _).mpr
                left
                have valid := hl.1
                simp only [Interval.Valid, Interval.Contains] at valid ⊢
                omega
              exact head_successor_absent head rest hl ((same _).mpr present)
          have headEqual : head = other := by
            cases head
            cases other
            simp_all
          subst other
          congr 1
          apply ih tail hl.2.2 hr.2.2
          intro point
          by_cases inHead : head.Contains point
          · have notLeft : ¬ Contains rest point := by
              intro present
              have separated := tail_member_above_head head rest hl point present
              simp only [Interval.Contains] at inHead
              omega
            have notRight : ¬ Contains tail point := by
              intro present
              have separated := tail_member_above_head head tail hr point present
              simp only [Interval.Contains] at inHead
              omega
            simp [notLeft, notRight]
          · simpa only [contains_cons, inHead, false_or] using same point

theorem insert_canonical (range : Interval) (ranges : List Interval)
    (validRange : range.Valid) (canonical : Canonical ranges) :
    Canonical (IntervalClasses.insert range ranges) := by
  induction ranges generalizing range with
  | nil => exact ⟨validRange, by simp, trivial⟩
  | cons head rest ih =>
      have headValid := canonical.1
      have restValid := canonical_valid rest canonical.2.2
      have hullValid : (hull range head).Valid := by
        simp only [hull, Interval.Valid, min_def, max_def]
        split_ifs <;> simp_all [Interval.Valid] <;> omega
      simp only [IntervalClasses.insert]
      split_ifs with before after
      · refine ⟨validRange, ?_, canonical⟩
        intro next member
        rcases List.mem_cons.mp member with equal | member
        · subst next
          exact before
        · have separated := canonical.2.1 next member
          simp only [Interval.Valid] at headValid
          omega
      · refine ⟨headValid, ?_, ih range validRange canonical.2.2⟩
        intro next member
        have nextValid := insert_valid range rest validRange restValid next member
        have present : Contains (IntervalClasses.insert range rest) next.low :=
          ⟨next, member, le_rfl, nextValid⟩
        rcases (insert_contains range rest validRange restValid _).mp present
            with inRange | inRest
        · simp only [Interval.Contains] at inRange
          omega
        · exact tail_member_above_head head rest canonical _ inRest
      · exact ih (hull range head) hullValid canonical.2.2

theorem normalize_canonical (ranges : List Interval) (valid : Valid ranges) :
    Canonical (normalize ranges) := by
  induction ranges with
  | nil => trivial
  | cons head rest ih =>
      exact insert_canonical head (normalize rest) (valid head (by simp))
        (ih fun range member => valid range (by simp [member]))

/-- List equality is an exact membership decision after normalization. -/
theorem normal_forms_equal_iff (left right : List Interval)
    (hl : Valid left) (hr : Valid right) :
    normalize left = normalize right ↔
      ∀ point, Contains left point ↔ Contains right point := by
  constructor
  · intro equal point
    rw [← normalize_contains left hl point, ← normalize_contains right hr point, equal]
  · intro same
    apply canonical_unique _ _ (normalize_canonical left hl) (normalize_canonical right hr)
    intro point
    rw [normalize_contains left hl point, normalize_contains right hr point]
    exact same point

theorem normalize_idempotent (ranges : List Interval) (valid : Valid ranges) :
    normalize (normalize ranges) = normalize ranges := by
  apply canonical_unique _ _
    (normalize_canonical _ (normalize_valid ranges valid)) (normalize_canonical ranges valid)
  exact normalize_contains _ (normalize_valid ranges valid)

theorem canonical_normalize_eq (ranges : List Interval) (canonical : Canonical ranges) :
    normalize ranges = ranges := by
  have valid := canonical_valid ranges canonical
  exact canonical_unique _ _ (normalize_canonical ranges valid) canonical
    (normalize_contains ranges valid)

/-- A universe tag remains part of a class value even for the empty class. -/
structure ScopedValue (Domain : Type) where
  domain : Domain
  ranges : List Interval
  deriving DecidableEq, Repr

def SameScopedMeaning {Domain : Type} (left right : ScopedValue Domain) : Prop :=
  left.domain = right.domain ∧ ∀ point, Contains left.ranges point ↔ Contains right.ranges point

theorem scoped_values_equal_iff {Domain : Type} (left right : ScopedValue Domain)
    (hl : Canonical left.ranges) (hr : Canonical right.ranges) :
    left = right ↔ SameScopedMeaning left right := by
  constructor
  · intro equal
    subst right
    exact ⟨rfl, fun _ => Iff.rfl⟩
  · rintro ⟨sameDomain, samePoints⟩
    have sameRanges := canonical_unique left.ranges right.ranges hl hr samePoints
    cases left
    cases right
    simp_all

/-- Composed expressions have exact canonical representatives, even where
their unnormalized difference operation leaves touching components. -/
def normalForm (expression : ClassExpressions.Expr) : List Interval :=
  normalize (ClassExpressions.compile expression)

theorem expression_normal_forms_equal_iff (left right : ClassExpressions.Expr)
    (hl : ClassExpressions.WellFormed left) (hr : ClassExpressions.WellFormed right) :
    normalForm left = normalForm right ↔
      ∀ point, ClassExpressions.Denote left point ↔ ClassExpressions.Denote right point := by
  rw [normalForm, normalForm,
    normal_forms_equal_iff _ _ (ClassExpressions.compile_valid left hl)
      (ClassExpressions.compile_valid right hr)]
  simp only [ClassExpressions.compile_contains left hl, ClassExpressions.compile_contains right hr]

def equivalent (left right : ClassExpressions.Expr) : Bool :=
  decide (normalForm left = normalForm right)

theorem equivalent_correct (left right : ClassExpressions.Expr)
    (hl : ClassExpressions.WellFormed left) (hr : ClassExpressions.WellFormed right) :
    equivalent left right = true ↔
      ∀ point, ClassExpressions.Denote left point ↔ ClassExpressions.Denote right point := by
  rw [equivalent, decide_eq_true_eq, expression_normal_forms_equal_iff left right hl hr]

theorem union_commutes (left right : ClassExpressions.Expr)
    (hl : ClassExpressions.WellFormed left) (hr : ClassExpressions.WellFormed right) :
    normalForm (.union left right) = normalForm (.union right left) := by
  apply (expression_normal_forms_equal_iff (.union left right) (.union right left)
    ⟨hl, hr⟩ ⟨hr, hl⟩).mpr
  intro point
  exact or_comm

theorem union_associates (first second third : ClassExpressions.Expr)
    (ha : ClassExpressions.WellFormed first) (hb : ClassExpressions.WellFormed second)
    (hc : ClassExpressions.WellFormed third) :
    normalForm (.union (.union first second) third) =
      normalForm (.union first (.union second third)) := by
  apply (expression_normal_forms_equal_iff (.union (.union first second) third)
    (.union first (.union second third)) ⟨⟨ha, hb⟩, hc⟩ ⟨ha, hb, hc⟩).mpr
  intro point
  exact or_assoc

theorem union_idempotent (expression : ClassExpressions.Expr)
    (wellFormed : ClassExpressions.WellFormed expression) :
    normalForm (.union expression expression) = normalForm expression := by
  apply (expression_normal_forms_equal_iff (.union expression expression) expression
    ⟨wellFormed, wellFormed⟩ wellFormed).mpr
  intro point
  simp [ClassExpressions.Denote]

theorem intersection_commutes (left right : ClassExpressions.Expr)
    (hl : ClassExpressions.WellFormed left) (hr : ClassExpressions.WellFormed right) :
    normalForm (.intersection left right) = normalForm (.intersection right left) := by
  apply (expression_normal_forms_equal_iff (.intersection left right) (.intersection right left)
    ⟨hl, hr⟩ ⟨hr, hl⟩).mpr
  intro point
  exact and_comm

theorem intersection_idempotent (expression : ClassExpressions.Expr)
    (wellFormed : ClassExpressions.WellFormed expression) :
    normalForm (.intersection expression expression) = normalForm expression := by
  apply (expression_normal_forms_equal_iff (.intersection expression expression) expression
    ⟨wellFormed, wellFormed⟩ wellFormed).mpr
  intro point
  simp [ClassExpressions.Denote]

theorem intersection_distributes (first second third : ClassExpressions.Expr)
    (ha : ClassExpressions.WellFormed first) (hb : ClassExpressions.WellFormed second)
    (hc : ClassExpressions.WellFormed third) :
    normalForm (.intersection first (.union second third)) =
      normalForm (.union (.intersection first second) (.intersection first third)) := by
  apply (expression_normal_forms_equal_iff (.intersection first (.union second third))
    (.union (.intersection first second) (.intersection first third))
    ⟨ha, hb, hc⟩ ⟨⟨ha, hb⟩, ha, hc⟩).mpr
  intro point
  simp only [ClassExpressions.Denote]
  tauto

theorem union_absorbs (left right : ClassExpressions.Expr)
    (hl : ClassExpressions.WellFormed left) (hr : ClassExpressions.WellFormed right) :
    normalForm (.union left (.intersection left right)) = normalForm left := by
  apply (expression_normal_forms_equal_iff (.union left (.intersection left right)) left
    ⟨hl, hl, hr⟩ hl).mpr
  intro point
  simp only [ClassExpressions.Denote]
  tauto

theorem complement_union (domain : List Interval) (left right : ClassExpressions.Expr)
    (hu : Valid domain) (hl : ClassExpressions.WellFormed left)
    (hr : ClassExpressions.WellFormed right) :
    normalForm (.complement domain (.union left right)) =
      normalForm (.intersection (.complement domain left) (.complement domain right)) := by
  apply (expression_normal_forms_equal_iff (.complement domain (.union left right))
    (.intersection (.complement domain left) (.complement domain right))
    ⟨hu, hl, hr⟩ ⟨⟨hu, hl⟩, hu, hr⟩).mpr
  intro point
  simp only [ClassExpressions.Denote]
  tauto

theorem complement_intersection (domain : List Interval)
    (left right : ClassExpressions.Expr) (hu : Valid domain)
    (hl : ClassExpressions.WellFormed left) (hr : ClassExpressions.WellFormed right) :
    normalForm (.complement domain (.intersection left right)) =
      normalForm (.union (.complement domain left) (.complement domain right)) := by
  apply (expression_normal_forms_equal_iff (.complement domain (.intersection left right))
    (.union (.complement domain left) (.complement domain right))
    ⟨hu, hl, hr⟩ ⟨⟨hu, hl⟩, hu, hr⟩).mpr
  intro point
  simp only [ClassExpressions.Denote]
  tauto

/-- Involution requires containment in the declared universe. Without it the
second complement is a projection, not the original class. -/
theorem complement_involution (domain : List Interval) (expression : ClassExpressions.Expr)
    (hu : Valid domain) (he : ClassExpressions.WellFormed expression)
    (contained : ∀ point, ClassExpressions.Denote expression point → Contains domain point) :
    normalForm (.complement domain (.complement domain expression)) = normalForm expression := by
  apply (expression_normal_forms_equal_iff (.complement domain (.complement domain expression))
    expression ⟨hu, hu, he⟩ he).mpr
  intro point
  simp only [ClassExpressions.Denote]
  constructor
  · tauto
  · intro present
    exact ⟨contained point present, by tauto⟩

theorem unequal_has_witness (left right : ClassExpressions.Expr)
    (hl : ClassExpressions.WellFormed left) (hr : ClassExpressions.WellFormed right)
    (different : normalForm left ≠ normalForm right) :
    ∃ point, ¬ (ClassExpressions.Denote left point ↔ ClassExpressions.Denote right point) := by
  have notSame : ¬ ∀ point,
      ClassExpressions.Denote left point ↔ ClassExpressions.Denote right point :=
    fun same => different ((expression_normal_forms_equal_iff left right hl hr).mpr same)
  exact not_forall.mp notSame

/-! Independent positive and negative controls. Equal cardinality is not
equal membership; an undeclared gap or a changed complement domain matters. -/

example : equivalent (.leaf [⟨0, 3⟩, ⟨4, 7⟩]) (.leaf [⟨0, 7⟩]) = true := by decide +kernel
example : equivalent (.leaf [⟨0, 3⟩, ⟨5, 7⟩]) (.leaf [⟨0, 7⟩]) = false := by decide +kernel
example : equivalent (.leaf [⟨0, 1⟩]) (.leaf [⟨2, 3⟩]) = false := by decide +kernel
example : equivalent (.complement codePoints (.leaf []))
    (.complement scalars (.leaf [])) = false := by decide +kernel
example : equivalent (.difference (.leaf [⟨0, 20⟩]) (.leaf [⟨7, 9⟩]))
    (.union (.leaf [⟨0, 6⟩]) (.leaf [⟨10, 20⟩])) = true := by decide +kernel
example : ¬ SameScopedMeaning (ScopedValue.mk false []) (ScopedValue.mk true []) := by
  rintro ⟨impossible, _⟩
  cases impossible

#print axioms canonical_unique
#print axioms insert_canonical
#print axioms normalize_canonical
#print axioms normal_forms_equal_iff
#print axioms normalize_idempotent
#print axioms canonical_normalize_eq
#print axioms scoped_values_equal_iff
#print axioms expression_normal_forms_equal_iff
#print axioms equivalent_correct
#print axioms union_commutes
#print axioms union_associates
#print axioms union_idempotent
#print axioms intersection_commutes
#print axioms intersection_idempotent
#print axioms intersection_distributes
#print axioms union_absorbs
#print axioms complement_union
#print axioms complement_intersection
#print axioms complement_involution
#print axioms unequal_has_witness

end Mettapedia.Computability.RegularLanguages.CanonicalClasses
