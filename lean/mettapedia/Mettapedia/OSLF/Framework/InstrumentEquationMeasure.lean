import Mettapedia.OSLF.Framework.PartialStructuralObservers

/-!
# Least constructor count for closed first-order equation classes

The measure is the least actual constructor count in a class of the
independently generated constructor congruence. A class has an attaining
representative by well-ordering of the natural numbers. Replacing one child
by a smaller equivalent term earns hereditary leanness and strict descent;
these are not supplied admissibility fields.

The signature has one sort and finite constructor arities. No binding,
quotation or arbitrary contextual operational correspondence is asserted.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentEquations

open InstrumentObservations
open scoped BigOperators

universe u

variable {Symbols : Type u} {arity : Symbols → Nat}

def constructorCount : Tree Symbols arity → Nat
  | .node _constructor arguments => 1 + ∑ position, constructorCount (arguments position)

theorem constructorCount_positive (term : Tree Symbols arity) :
    0 < constructorCount term := by
  cases term with
  | node constructor arguments => simp only [constructorCount]; omega

theorem constructorCount_child_lt (constructor : Symbols)
    (arguments : Fin (arity constructor) → Tree Symbols arity)
    (position : Fin (arity constructor)) :
    constructorCount (arguments position) < constructorCount (.node constructor arguments) := by
  have bounded : constructorCount (arguments position) ≤
      ∑ index, constructorCount (arguments index) :=
    Finset.single_le_sum (f := fun index => constructorCount (arguments index))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ position)
  simp only [constructorCount]
  omega

abbrev TermClass (generators : Tree Symbols arity → Tree Symbols arity → Prop) :=
  Quotient (equationSetoid generators)

def classOf (generators : Tree Symbols arity → Tree Symbols arity → Prop)
    (term : Tree Symbols arity) : TermClass generators := Quotient.mk _ term

theorem classOf_eq_iff (generators : Tree Symbols arity → Tree Symbols arity → Prop)
    (first second : Tree Symbols arity) :
    classOf generators first = classOf generators second ↔ Equation generators first second :=
  ⟨fun same => Quotient.exact same, fun equation => Quotient.sound equation⟩

variable (generators : Tree Symbols arity → Tree Symbols arity → Prop)

def CountAttained (value : TermClass generators) (count : Nat) : Prop :=
  ∃ term : Tree Symbols arity, classOf generators term = value ∧ constructorCount term = count

theorem countAttained_exists (value : TermClass generators) :
    ∃ count, CountAttained generators value count := by
  refine Quotient.inductionOn value ?_
  intro term
  exact ⟨constructorCount term, term, rfl, rfl⟩

def measure (value : TermClass generators) : Nat := by
  classical
  exact Nat.find (countAttained_exists generators value)

theorem measure_attained (value : TermClass generators) :
    CountAttained generators value (measure generators value) := by
  classical
  exact Nat.find_spec (countAttained_exists generators value)

theorem measure_le_count (value : TermClass generators) (term : Tree Symbols arity)
    (represents : classOf generators term = value) :
    measure generators value ≤ constructorCount term := by
  classical
  exact Nat.find_min' (countAttained_exists generators value) ⟨term, represents, rfl⟩

theorem measure_positive (value : TermClass generators) : 0 < measure generators value := by
  obtain ⟨term, _, counted⟩ := measure_attained generators value
  rw [← counted]
  exact constructorCount_positive term

def IsLean (term : Tree Symbols arity) : Prop :=
  constructorCount term = measure generators (classOf generators term)

theorem lean_representative (value : TermClass generators) :
    ∃ term : Tree Symbols arity, classOf generators term = value ∧ IsLean generators term := by
  obtain ⟨term, represents, counted⟩ := measure_attained generators value
  refine ⟨term, represents, ?_⟩
  exact counted.trans (congrArg (measure generators) represents).symm

theorem measure_equation {first second : Tree Symbols arity}
    (equation : Equation generators first second) :
    measure generators (classOf generators first) =
      measure generators (classOf generators second) :=
  congrArg (measure generators) (Quotient.sound equation)

theorem isLean_iff_le_all (term : Tree Symbols arity) :
    IsLean generators term ↔ ∀ other, Equation generators term other →
      constructorCount term ≤ constructorCount other := by
  constructor
  · intro lean other equation
    rw [lean, measure_equation generators equation]
    exact measure_le_count generators _ other rfl
  · intro least
    obtain ⟨other, represents, counted⟩ := measure_attained generators (classOf generators term)
    apply le_antisymm
    · rw [← counted]
      exact least other (Quotient.exact represents.symm)
    · exact measure_le_count generators _ term rfl

theorem equivalent_child_replacement (constructor : Symbols)
    (arguments : Fin (arity constructor) → Tree Symbols arity)
    (position : Fin (arity constructor)) (replacement : Tree Symbols arity)
    (equation : Equation generators (arguments position) replacement) :
    Equation generators (.node constructor arguments)
      (.node constructor (Function.update arguments position replacement)) := by
  classical
  apply Equation.congruence
  intro index
  by_cases same : index = position
  · subst index
    simpa using equation
  · simpa [Function.update_of_ne same] using Equation.refl (generators := generators) (arguments index)

theorem smaller_child_replacement (constructor : Symbols)
    (arguments : Fin (arity constructor) → Tree Symbols arity)
    (position : Fin (arity constructor)) (replacement : Tree Symbols arity)
    (smaller : constructorCount replacement < constructorCount (arguments position)) :
    constructorCount (.node constructor (Function.update arguments position replacement)) <
      constructorCount (.node constructor arguments) := by
  classical
  have sumSmaller :
      (∑ index, constructorCount (Function.update arguments position replacement index)) <
        ∑ index, constructorCount (arguments index) := by
    apply Finset.sum_lt_sum
    · intro index _
      by_cases same : index = position
      · subst index
        simpa using Nat.le_of_lt smaller
      · simp [Function.update_of_ne same]
    · exact ⟨position, Finset.mem_univ _, by simpa using smaller⟩
  simpa only [constructorCount] using Nat.add_lt_add_left sumSmaller 1

theorem lean_children (constructor : Symbols)
    (arguments : Fin (arity constructor) → Tree Symbols arity)
    (lean : IsLean generators (.node constructor arguments))
    (position : Fin (arity constructor)) : IsLean generators (arguments position) := by
  classical
  apply (isLean_iff_le_all generators (arguments position)).2
  intro replacement equation
  by_contra notBounded
  have smaller : constructorCount replacement < constructorCount (arguments position) := by omega
  have wholeEquation := equivalent_child_replacement generators constructor arguments position
    replacement equation
  have wholeSmaller := smaller_child_replacement constructor arguments position replacement smaller
  have wholeBounded := (isLean_iff_le_all generators _).1 lean _ wholeEquation
  omega

theorem lean_child_descent (constructor : Symbols)
    (arguments : Fin (arity constructor) → Tree Symbols arity)
    (lean : IsLean generators (.node constructor arguments))
    (position : Fin (arity constructor)) :
    IsLean generators (arguments position) ∧
      measure generators (classOf generators (arguments position)) <
        measure generators (classOf generators (.node constructor arguments)) := by
  have childLean := lean_children generators constructor arguments lean position
  refine ⟨childLean, ?_⟩
  rw [← childLean, ← lean]
  exact constructorCount_child_lt constructor arguments position

end Mettapedia.OSLF.Framework.InstrumentEquations
