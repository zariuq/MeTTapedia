import Mettapedia.OSLF.StructuralModal.SeparatingConjunction

/-!
# Admissible equations, and the descent they buy

The separating conjunction quantifies over decompositions rather than recursing
through them, so it says what a split is without saying how to find one.  A
procedure that searched for a split would descend: pick a representative, break
it into parts, and repeat on the parts.  Three conditions on an equation theory
are what makes that terminate, and they are the source material's:

1. **Every class has a lean representative** — so the descent has somewhere to
   start, and starts on a term that carries the parts it appears to carry
   rather than padding.
2. **Leanness is hereditary, with a strictly decreasing measure** — so the parts
   of a lean composition are themselves lean, and smaller, and the descent
   terminates.
3. **The theory relates only terms of the same sort** — so a change of
   representative cannot leave the sort the descent is working in.

This module states them, proves the induction principle they buy, relates them
to the connective, and gives a presentation that meets all three together with
the witnesses that show the conditions are not vacuous there.

**What is not claimed.**  A decision procedure for the connective is not built.
The three conditions are what such a procedure would consume -- a starting
representative, a terminating recursion, and a sort that does not move -- and
each is proved to do its job here.  Turning them into a procedure needs one more
thing this module does not supply: that a split of a lean representative is
recoverable from a split of *its* element list, which is a property of a
particular equation theory rather than of admissibility.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.StructuralModal.AdmissibleEquations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.StructuralModal.SeparatingConjunction

/-- **Admissible equations.**  An equation theory on the terms of a carrier,
with a notion of lean representative and a measure, meeting the three
conditions a descent along decompositions needs. -/
structure Admissible (equiv : Pattern → Pattern → Prop) (kind : CollType)
    (sortedAt : Pattern → String → Prop) where
  /-- The terms the theory is about.  A theory is a theory of a presentation's
  terms, not of every pattern, and asking for a representative outside the
  carrier is asking for something no presentation supplies. -/
  Carrier : Pattern → Prop
  /-- The lean terms: the representatives the descent works on. -/
  IsLean : Pattern → Prop
  /-- The measure the descent strictly decreases. -/
  measure : Pattern → Nat
  /-- A lean term is a term of the carrier. -/
  leanInCarrier : ∀ term, IsLean term → Carrier term
  /-- **Every class has a lean representative.** -/
  leanRepresentative : ∀ term, Carrier term →
    ∃ representative, equiv term representative ∧ IsLean representative
  /-- **Leanness is hereditary, with a strictly decreasing measure.** -/
  hereditary : ∀ elements : List Pattern,
    IsLean (.collection kind elements none) →
      ∀ element ∈ elements,
        IsLean element ∧
          measure element < measure (.collection kind elements none)
  /-- **The theory relates only terms of the same sort.** -/
  sortRespecting : ∀ {left right : Pattern}, equiv left right →
    ∀ category : String, sortedAt left category ↔ sortedAt right category

namespace Admissible

variable {equiv : Pattern → Pattern → Prop} {kind : CollType}
  {sortedAt : Pattern → String → Prop}

/-- **The descent terminates.**  Anything provable of a lean term from its
parts is provable of every lean term.  This is what the second condition buys,
and it is the shape a decision procedure for the connective would recurse
along. -/
theorem leanInduction (admissible : Admissible equiv kind sortedAt)
    {motive : Pattern → Prop}
    (step : ∀ term, admissible.IsLean term →
      (∀ elements : List Pattern, term = .collection kind elements none →
        ∀ element ∈ elements, motive element) →
      motive term) :
    ∀ term, admissible.IsLean term → motive term := by
  have key : ∀ bound term, admissible.measure term ≤ bound →
      admissible.IsLean term → motive term := by
    intro bound
    induction bound with
    | zero =>
        intro term bounded isLean
        refine step term isLean ?_
        intro elements shape element member
        obtain ⟨-, smaller⟩ := admissible.hereditary elements (shape ▸ isLean) element member
        rw [← shape] at smaller
        omega
    | succ previous inductionHypothesis =>
        intro term bounded isLean
        refine step term isLean ?_
        intro elements shape element member
        obtain ⟨elementLean, smaller⟩ :=
          admissible.hereditary elements (shape ▸ isLean) element member
        rw [← shape] at smaller
        exact inductionHypothesis element (by omega) elementLean
  exact fun term isLean => key (admissible.measure term) term le_rfl isLean

/-- **A split is a split of a lean representative.**  So the descent has
something to descend on: the search can move to the representative without
losing the split. -/
theorem sepConj_at_lean (admissible : Admissible equiv kind sortedAt)
    (symm : ∀ {a b : Pattern}, equiv a b → equiv b a)
    (trans : ∀ {a b c : Pattern}, equiv a b → equiv b c → equiv a c)
    {left right : Pattern → Prop} {term : Pattern}
    (carrier : admissible.Carrier term)
    (split : SepConj equiv kind left right term) :
    ∃ representative, equiv term representative ∧ admissible.IsLean representative ∧
      SepConj equiv kind left right representative := by
  obtain ⟨representative, equivalent, isLean⟩ :=
    admissible.leanRepresentative term carrier
  obtain ⟨leftElements, rightElements, decomposition, holdsLeft, holdsRight⟩ := split
  exact ⟨representative, equivalent, isLean,
    leftElements, rightElements, trans (symm equivalent) decomposition,
    holdsLeft, holdsRight⟩

/-- **And a split never crosses a sort.**  The decomposition a split exhibits
sits at the same sorts as the term it decomposes. -/
theorem sepConj_sort (admissible : Admissible equiv kind sortedAt)
    {left right : Pattern → Prop} {term : Pattern}
    (split : SepConj equiv kind left right term) :
    ∃ leftElements rightElements : List Pattern,
      left (.collection kind leftElements none) ∧
        right (.collection kind rightElements none) ∧
        ∀ category : String,
          sortedAt term category ↔
            sortedAt (.collection kind (leftElements ++ rightElements) none) category := by
  obtain ⟨leftElements, rightElements, decomposition, holdsLeft, holdsRight⟩ := split
  exact ⟨leftElements, rightElements, holdsLeft, holdsRight,
    admissible.sortRespecting decomposition⟩

/-- **The measure is load-bearing, and the condition is not vacuous.**  In any
admissible theory a lean one-element composition is strictly larger than its
element, so a theory with a constant measure has no lean one-element
compositions at all. -/
theorem measure_lt_of_lean_singleton (admissible : Admissible equiv kind sortedAt)
    {element : Pattern}
    (isLean : admissible.IsLean (.collection kind [element] none)) :
    admissible.measure element <
      admissible.measure (.collection kind [element] none) :=
  (admissible.hereditary [element] isLean element (by simp)).2

end Admissible

/-! ## A presentation that meets all three

Compositions of atoms, with one law: a unit part may be dropped.  Lean means
carrying no unit, the measure counts parts, and the sort is membership of the
carrier.  All three conditions are discharged, and the witnesses at the end show
none of them is vacuous here -- there is a carrier term that is not lean, and
its lean representative is a different term. -/

namespace UnitPadding

/-- The unit part. -/
def unit : Pattern := .apply "Stop" []

/-- An atom of the presentation. -/
def IsAtom (term : Pattern) : Prop := ∃ label : String, term = .apply label []

/-- The terms the theory is about: atoms, and compositions of atoms. -/
def Carrier (term : Pattern) : Prop :=
  IsAtom term ∨
    ∃ elements : List Pattern,
      term = .collection .hashBag elements none ∧ ∀ element ∈ elements, IsAtom element

/-- The one law, as the equivalence it generates: the same term, or two
compositions with the same non-unit parts in the same order. -/
def Equiv (left right : Pattern) : Prop :=
  left = right ∨
    ∃ leftElements rightElements : List Pattern,
      left = .collection .hashBag leftElements none ∧
        right = .collection .hashBag rightElements none ∧
        leftElements.filter (fun element => element != unit)
          = rightElements.filter (fun element => element != unit)

theorem equiv_refl (term : Pattern) : Equiv term term := Or.inl rfl

theorem equiv_symm {left right : Pattern} (equivalent : Equiv left right) :
    Equiv right left := by
  rcases equivalent with rfl | ⟨leftElements, rightElements, leftShape, rightShape, same⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨rightElements, leftElements, rightShape, leftShape, same.symm⟩

theorem equiv_trans {left middle right : Pattern}
    (first : Equiv left middle) (second : Equiv middle right) : Equiv left right := by
  rcases first with rfl | ⟨leftElements, middleElements, leftShape, middleShape, firstSame⟩
  · exact second
  · rcases second with rfl | ⟨middleElements', rightElements, middleShape', rightShape, secondSame⟩
    · exact Or.inr ⟨leftElements, middleElements, leftShape, middleShape, firstSame⟩
    · rw [middleShape] at middleShape'
      have elementsEq : middleElements = middleElements' := by
        simpa using middleShape'
      exact Or.inr ⟨leftElements, rightElements, leftShape, rightShape,
        firstSame.trans (elementsEq ▸ secondSame)⟩

/-- Lean: a composition carrying no unit, or an atom. -/
def IsLean (term : Pattern) : Prop :=
  IsAtom term ∨
    ∃ elements : List Pattern,
      term = .collection .hashBag elements none ∧
        unit ∉ elements ∧ ∀ element ∈ elements, IsAtom element

/-- The measure: how many parts a composition carries.  An atom carries none. -/
def measure : Pattern → Nat
  | .collection _ elements _ => elements.length + 1
  | _ => 0

/-- Membership of the carrier, as the presentation's one sort. -/
def sortedAt (term : Pattern) (category : String) : Prop :=
  category = "Proc" ∧ Carrier term

theorem carrier_of_filter_eq {leftElements rightElements : List Pattern}
    (same : leftElements.filter (fun element => element != unit)
      = rightElements.filter (fun element => element != unit))
    (atoms : ∀ element ∈ leftElements, IsAtom element) :
    ∀ element ∈ rightElements, IsAtom element := by
  intro element member
  by_cases isUnit : element = unit
  · exact ⟨"Stop", by rw [isUnit, unit]⟩
  · have inFiltered : element ∈ rightElements.filter (fun e => e != unit) :=
      List.mem_filter.mpr ⟨member, by simpa using isUnit⟩
    rw [← same] at inFiltered
    exact atoms element (List.mem_of_mem_filter inFiltered)

/-- **The three conditions, met.** -/
def admissible : Admissible Equiv .hashBag sortedAt where
  Carrier := Carrier
  IsLean := IsLean
  measure := measure
  leanInCarrier := by
    rintro term (atom | ⟨elements, shape, -, atoms⟩)
    · exact Or.inl atom
    · exact Or.inr ⟨elements, shape, atoms⟩
  leanRepresentative := by
    rintro term (atom | ⟨elements, rfl, atoms⟩)
    · exact ⟨term, Or.inl rfl, Or.inl atom⟩
    · refine ⟨.collection .hashBag (elements.filter (fun e => e != unit)) none,
        Or.inr ⟨elements, elements.filter (fun e => e != unit), rfl, rfl, ?_⟩,
        Or.inr ⟨elements.filter (fun e => e != unit), rfl, ?_, ?_⟩⟩
      · simp [List.filter_filter]
      · intro member
        simpa using (List.mem_filter.mp member).2
      · intro element member
        exact atoms element (List.mem_of_mem_filter member)
  hereditary := by
    rintro elements (atom | ⟨elements', shape, noUnit, atoms⟩) element member
    · exact absurd atom (by rintro ⟨label, shape⟩; exact Pattern.noConfusion shape)
    · have elementsEq : elements' = elements := by simpa using shape.symm
      subst elementsEq
      refine ⟨Or.inl (atoms element member), ?_⟩
      obtain ⟨label, rfl⟩ := atoms element member
      simp [measure]
  sortRespecting := by
    rintro left right (rfl | ⟨leftElements, rightElements, rfl, rfl, same⟩) category
    · exact Iff.rfl
    · constructor
      · rintro ⟨rfl, (atom | ⟨elements, shape, atoms⟩)⟩
        · exact absurd atom (by rintro ⟨label, shape⟩; exact Pattern.noConfusion shape)
        · have elementsEq : elements = leftElements := by simpa using shape.symm
          subst elementsEq
          exact ⟨rfl, Or.inr ⟨rightElements, rfl, carrier_of_filter_eq same atoms⟩⟩
      · rintro ⟨rfl, (atom | ⟨elements, shape, atoms⟩)⟩
        · exact absurd atom (by rintro ⟨label, shape⟩; exact Pattern.noConfusion shape)
        · have elementsEq : elements = rightElements := by simpa using shape.symm
          subst elementsEq
          exact ⟨rfl, Or.inr ⟨leftElements, rfl, carrier_of_filter_eq same.symm atoms⟩⟩

/-! ### The conditions are not vacuous here -/

/-- A padded composition is a term of the carrier. -/
theorem padded_carrier : Carrier (.collection .hashBag [unit] none) :=
  Or.inr ⟨[unit], rfl, by rintro element member; simp at member; exact ⟨"Stop", by rw [member, unit]⟩⟩

/-- **And it is not lean**, so leanness is a real restriction. -/
theorem padded_not_lean : ¬ IsLean (.collection .hashBag [unit] none) := by
  rintro (atom | ⟨elements, shape, noUnit, -⟩)
  · exact absurd atom (by rintro ⟨label, shape⟩; exact Pattern.noConfusion shape)
  · have elementsEq : elements = [unit] := by simpa using shape.symm
    subst elementsEq
    exact noUnit (by simp)

/-- **Its lean representative is a different term**, so the first condition is
doing work rather than returning what it was given. -/
theorem padded_representative :
    Equiv (.collection .hashBag [unit] none) (.collection .hashBag [] none) ∧
      IsLean (.collection .hashBag [] none) ∧
      (.collection .hashBag [unit] none : Pattern) ≠ .collection .hashBag [] none :=
  ⟨Or.inr ⟨[unit], [], rfl, rfl, by simp [unit]⟩,
    Or.inr ⟨[], rfl, by simp, by simp⟩,
    by simp⟩

/-- **And the measure strictly decreases into the parts**, at a lean
composition of two atoms. -/
theorem measure_decreases :
    measure (.apply "A" []) <
      measure (.collection .hashBag [.apply "A" [], .apply "B" []] none) := by
  simp [measure]

end UnitPadding

end Mettapedia.OSLF.StructuralModal.AdmissibleEquations
