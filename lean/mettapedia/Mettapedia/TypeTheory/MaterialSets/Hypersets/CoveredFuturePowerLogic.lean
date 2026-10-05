import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerFunctor

/-!
# Constructive bounded logic of small-covered future powers

Empty predicates, binary union, intersection and bounded separation have
constructed small covers. Separation uses actual proposition-valued receipt
subtypes at the original bound. Implication tests every actual later argument
and morphism; bounding this predicate gives the relative Heyting adjunction
inside any covered predicate.

No enumeration is selected from its existence proof. Full proposition-valued
separation is used explicitly. Arbitrary small-index union, fixed-bound
Collection and indexed finality are not consequences of these finite and
bounded constructions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerLogic

open CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor

universe u v
variable {D : Type u} [Category.{u} D] {A : D ⥤ Type v} {point : D}

def bottom (A : D ⥤ Type v) (point : D) : Predicate A point where
  holds _ := False
  closed _ impossible := impossible.elim

def bottomEnumeration (A : D ⥤ Type v) (point : D) : Enumeration (bottom A point) where
  Carrier _ := PEmpty.{u + 1}
  value _ receipt := receipt.elim
  covered _ _ := ⟨fun impossible => impossible.elim, fun ⟨receipt, _⟩ => receipt.elim⟩

def bottomPower (A : D ⥤ Type v) (point : D) : Power A point :=
  ⟨bottom A point, ⟨bottomEnumeration A point⟩⟩

def disjunction (first second : Predicate A point) : Predicate A point where
  holds argument := first.holds argument ∨ second.holds argument
  closed move available := available.elim
    (fun holds => Or.inl (first.closed move holds))
    (fun holds => Or.inr (second.closed move holds))

def conjunction (first second : Predicate A point) : Predicate A point where
  holds argument := first.holds argument ∧ second.holds argument
  closed move available := ⟨first.closed move available.1, second.closed move available.2⟩

def disjunctionEnumeration {first second : Predicate A point}
    (left : Enumeration first) (right : Enumeration second) :
    Enumeration (disjunction first second) where
  Carrier future := left.Carrier future ⊕ right.Carrier future
  value future := Sum.elim (left.value future) (right.value future)
  covered future argument := by
    constructor
    · intro available
      cases available with
      | inl holds =>
          obtain ⟨receipt, same⟩ := (left.covered future argument).mp holds
          exact ⟨Sum.inl receipt, same⟩
      | inr holds =>
          obtain ⟨receipt, same⟩ := (right.covered future argument).mp holds
          exact ⟨Sum.inr receipt, same⟩
    · rintro ⟨receipt, same⟩
      cases receipt with
      | inl receipt => exact Or.inl ((left.covered future argument).mpr ⟨receipt, same⟩)
      | inr receipt => exact Or.inr ((right.covered future argument).mpr ⟨receipt, same⟩)

/-- Filtering actual small receipts constructs bounded separation for every
stable proposition, without enumerating the larger ambient argument type. -/
def conjunctionEnumeration {first : Predicate A point} (enumeration : Enumeration first)
    (second : Predicate A point) : Enumeration (conjunction first second) where
  Carrier future := {receipt : enumeration.Carrier future //
    second.holds ⟨future, enumeration.value future receipt⟩}
  value future receipt := enumeration.value future receipt.val
  covered future argument := by
    constructor
    · rintro ⟨firstTruth, secondTruth⟩
      obtain ⟨receipt, same⟩ := (enumeration.covered future argument).mp firstTruth
      refine ⟨⟨receipt, ?_⟩, same⟩
      rw [same]
      exact secondTruth
    · rintro ⟨receipt, same⟩
      refine ⟨(enumeration.covered future argument).mpr ⟨receipt.val, same⟩, ?_⟩
      have secondTruth := receipt.property
      rw [same] at secondTruth
      exact secondTruth

def joinPower (first second : Power A point) : Power A point :=
  ⟨disjunction first.val second.val, by
    obtain ⟨left⟩ := first.property
    obtain ⟨right⟩ := second.property
    exact ⟨disjunctionEnumeration left right⟩⟩

def separatePower (bound : Power A point) (predicate : Predicate A point) : Power A point :=
  ⟨conjunction bound.val predicate, by
    obtain ⟨enumeration⟩ := bound.property
    exact ⟨conjunctionEnumeration enumeration predicate⟩⟩

def meetPower (first second : Power A point) : Power A point :=
  separatePower first second.val

theorem meet_first (first second : Power A point) : Included (meetPower first second).val first.val :=
  fun _ truth => truth.1

theorem meet_second (first second : Power A point) : Included (meetPower first second).val second.val :=
  fun _ truth => truth.2

theorem join_left (first second : Power A point) : Included first.val (joinPower first second).val :=
  fun _ truth => Or.inl truth

theorem join_right (first second : Power A point) : Included second.val (joinPower first second).val :=
  fun _ truth => Or.inr truth

theorem join_le_iff (first second upper : Power A point) :
    Included (joinPower first second).val upper.val ↔
      Included first.val upper.val ∧ Included second.val upper.val := by
  constructor
  · intro included
    exact ⟨fun argument truth => included argument (Or.inl truth),
      fun argument truth => included argument (Or.inr truth)⟩
  · rintro ⟨left, right⟩ argument truth
    exact truth.elim (left argument) (right argument)

theorem le_meet_iff (lower first second : Power A point) :
    Included lower.val (meetPower first second).val ↔
      Included lower.val first.val ∧ Included lower.val second.val := by
  constructor
  · intro included
    exact ⟨fun argument truth => (included argument truth).1,
      fun argument truth => (included argument truth).2⟩
  · rintro ⟨left, right⟩ argument truth
    exact ⟨left argument truth, right argument truth⟩

theorem join_comm (first second : Power A point) : joinPower first second = joinPower second first := by
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  exact Or.comm

theorem meet_comm (first second : Power A point) : meetPower first second = meetPower second first := by
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  exact And.comm

theorem meet_distributes_join (first second third : Power A point) :
    meetPower first (joinPower second third) =
      joinPower (meetPower first second) (meetPower first third) := by
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  constructor
  · rintro ⟨bound, available⟩
    exact available.elim (fun left => Or.inl ⟨bound, left⟩) (fun right => Or.inr ⟨bound, right⟩)
  · intro available
    exact available.elim (fun left => ⟨left.1, Or.inl left.2⟩)
      (fun right => ⟨right.1, Or.inr right.2⟩)

/-- Relative implication observes all later actual arrows and arguments.
Pointwise host implication alone need not be restriction-stable. -/
def implication (first second : Predicate A point) : Predicate A point where
  holds argument := ∀ {later : Arguments A point} (_move : argument ⟶ later),
    first.holds later → second.holds later
  closed earlier available := by
    intro later move truth
    exact available (earlier ≫ move) truth

def implicationPower (bound : Power A point) (first second : Predicate A point) : Power A point :=
  separatePower bound (implication first second)

theorem implicationPower_bounded (bound : Power A point) (first second : Predicate A point) :
    Included (implicationPower bound first second).val bound.val := fun _ truth => truth.1

/-- The actual constructed bounded implication is right adjoint to meet
inside the covered bound. The proof uses stability of the lower predicate. -/
theorem relative_implication_adjunction (bound first second third : Power A point)
    (inside : Included first.val bound.val) :
    Included (meetPower first second).val third.val ↔
      Included first.val (implicationPower bound second.val third.val).val := by
  constructor
  · intro valid argument truth
    refine ⟨inside argument truth, ?_⟩
    intro later move admitted
    exact valid later ⟨first.val.closed move truth, admitted⟩
  · intro valid argument truth
    exact (valid argument truth.1).2 (𝟙 argument) truth.2

theorem joinPower_restrict {first second : D} (step : first ⟶ second)
    (left right : Power A first) :
    restrictPower A step (joinPower left right) =
      joinPower (restrictPower A step left) (restrictPower A step right) := by
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  exact Iff.rfl

theorem separatePower_restrict {first second : D} (step : first ⟶ second)
    (bound : Power A first) (predicate : Predicate A first) :
    restrictPower A step (separatePower bound predicate) =
      separatePower (restrictPower A step bound) (restrict A step predicate) := by
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  exact Iff.rfl

/-- Every continuation of a precomposed future has the constructed lifted
future. This proves preservation of implication under actual restriction. -/
theorem implication_restrict {first second : D} (step : first ⟶ second)
    (left right : Predicate A first) :
    restrict A step (implication left right) =
      implication (restrict A step left) (restrict A step right) := by
  apply Predicate.ext
  intro argument
  constructor
  · intro valid later move truth
    exact valid ((futurePrecompose A step).map move) truth
  · intro valid later move truth
    let lifted : Arguments A second :=
      ⟨⟨later.1.1, argument.1.2 ≫ move.1.1⟩, later.2⟩
    let liftedMove : argument ⟶ lifted := ⟨⟨move.1.1, rfl⟩, move.2⟩
    have same : ((futurePrecompose A step).obj lifted) = later := by
      refine Sigma.ext ?_ (HEq.rfl)
      refine PowerClassPresheafBaseChange.Future.objects_ext
        (first := ((futurePrecompose A step).obj lifted).1) (second := later.1) rfl ?_
      exact heq_of_eq ((Category.assoc step argument.1.2 move.1.1).symm.trans move.1.2)
    have liftedTruth : (restrict A step left).holds lifted := by
      change left.holds ((futurePrecompose A step).obj lifted)
      rw [same]
      exact truth
    have result := valid liftedMove liftedTruth
    change right.holds ((futurePrecompose A step).obj lifted) at result
    rw [same] at result
    exact result

theorem implicationPower_restrict {first second : D} (step : first ⟶ second)
    (bound : Power A first) (left right : Predicate A first) :
    restrictPower A step (implicationPower bound left right) =
      implicationPower (restrictPower A step bound) (restrict A step left) (restrict A step right) := by
  change restrictPower A step (separatePower bound (implication left right)) = _
  rw [separatePower_restrict, implication_restrict]
  rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerLogic
