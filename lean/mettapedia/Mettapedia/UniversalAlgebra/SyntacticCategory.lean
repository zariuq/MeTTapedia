import Mathlib.CategoryTheory.Category.Basic
import Mettapedia.UniversalAlgebra.BoundedTerm
import Mettapedia.UniversalAlgebra.EquationSystemInterpretation
import Mettapedia.UniversalAlgebra.FreeModelInvariance

/-!
# The finite-context syntactic category of an equation system

Objects are finite variable contexts.  A raw arrow `n → m` is an `m`-tuple
of terms using only variables below `n`.  Arrows are raw tuples modulo
pointwise generated equational consequence, and composition is simultaneous
substitution.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

open CategoryTheory

universe u

variable {S : Signature.{u}}

/-- An `output`-tuple of terms in an `input`-variable context. -/
@[ext] structure BoundedTermTuple (S : Signature.{u})
    (input output : Nat) : Type u where
  component : Fin output → Term.Bounded S input

namespace BoundedTermTuple

variable (system : EquationSystem S)

/-- Pointwise generated consequence between bounded term tuples. -/
def Equivalent {input output : Nat}
    (left right : BoundedTermTuple S input output) : Prop :=
  ∀ position, EquationalConsequence system
    ((left.component position).1, (right.component position).1)

/-- Pointwise consequence is a setoid on bounded term tuples. -/
def consequenceSetoid (input output : Nat) :
    Setoid (BoundedTermTuple S input output) where
  r := Equivalent system
  iseqv := ⟨
    fun tuple position =>
      EquationalConsequence.refl system (tuple.component position).1,
    fun {_left _right} equivalent position =>
      EquationalConsequence.symm (equivalent position),
    fun {_first _second _third} firstSecond secondThird position =>
      EquationalConsequence.trans (firstSecond position)
        (secondThird position)⟩

/-- The identity tuple consists of its context variables. -/
def identity (size : Nat) : BoundedTermTuple S size size where
  component position := ⟨.var position.val, position.isLt⟩

/-- Extend a bounded tuple to a total simultaneous substitution. -/
def substitution {input output : Nat}
    (tuple : BoundedTermTuple S input output) : Nat → Term S :=
  Term.finSubstitution (fun position => (tuple.component position).1)

@[simp] theorem substitution_apply {input output : Nat}
    (tuple : BoundedTermTuple S input output) (position : Fin output) :
    substitution tuple position.val = (tuple.component position).1 :=
  Term.finSubstitution_apply _ position

/-- Composition of tuples is simultaneous substitution. -/
def comp {first second third : Nat}
    (earlier : BoundedTermTuple S first second)
    (later : BoundedTermTuple S second third) :
    BoundedTermTuple S first third where
  component position :=
    ⟨(later.component position).1.subst (substitution earlier),
      Term.variablesBelow_subst (later.component position).2
        (substitution earlier) (by
          intro index below
          simp only [substitution, Term.finSubstitution, below, dite_true]
          exact (earlier.component ⟨index, below⟩).2)⟩

/-- Composition respects pointwise consequence in both arguments. -/
theorem comp_equivalent {first second third : Nat}
    {earlier earlier' : BoundedTermTuple S first second}
    {later later' : BoundedTermTuple S second third}
    (earlierEquivalent : Equivalent system earlier earlier')
    (laterEquivalent : Equivalent system later later') :
    Equivalent system (comp earlier later) (comp earlier' later') := by
  intro position
  have changeArguments : EquationalConsequence system
      ((later.component position).1.subst (substitution earlier),
        (later.component position).1.subst (substitution earlier')) := by
    apply EquationalConsequence.substitution_congr
    intro index
    by_cases below : index < second
    · simp only [substitution, Term.finSubstitution, below, dite_true]
      exact earlierEquivalent ⟨index, below⟩
    · simp only [substitution, Term.finSubstitution, below, dite_false]
      exact EquationalConsequence.refl system (.var index)
  have changeTemplate := EquationalConsequence.subst
    (laterEquivalent position) (substitution earlier')
  exact EquationalConsequence.trans changeArguments changeTemplate

/-- Left identity holds already for raw tuples. -/
theorem identity_comp {input output : Nat}
    (tuple : BoundedTermTuple S input output) :
    comp (identity input) tuple = tuple := by
  ext position
  calc
    (tuple.component position).1.subst (substitution (identity input)) =
        (tuple.component position).1.subst Term.var :=
      Term.subst_eq_of_variablesBelow (tuple.component position).2 _ _
        (by
          intro index below
          simp only [substitution, Term.finSubstitution, below, dite_true,
            identity])
    _ = (tuple.component position).1 := Term.subst_variables _

/-- Right identity holds already for raw tuples. -/
theorem comp_identity {input output : Nat}
    (tuple : BoundedTermTuple S input output) :
    comp tuple (identity output) = tuple := by
  ext position
  simp only [comp, identity, Term.subst_var, substitution_apply]

/-- Tuple substitution is associative already at the raw syntax level. -/
theorem comp_assoc {first second third fourth : Nat}
    (firstSecond : BoundedTermTuple S first second)
    (secondThird : BoundedTermTuple S second third)
    (thirdFourth : BoundedTermTuple S third fourth) :
    comp (comp firstSecond secondThird) thirdFourth =
      comp firstSecond (comp secondThird thirdFourth) := by
  ext position
  simp only [comp, Term.subst_subst]
  apply Term.subst_eq_of_variablesBelow
    (thirdFourth.component position).2
  intro index below
  simp only [substitution, Term.finSubstitution, below, dite_true]

end BoundedTermTuple

/-- The finite-context syntactic category's objects.  The equation system is
retained in the type so categories belonging to different theories cannot be
silently mixed. -/
def SyntacticCategory (_system : EquationSystem S) := Nat

namespace SyntacticCategory

variable (system : EquationSystem S)

/-- Regard a finite context size as an object of the syntactic category. -/
abbrev object (size : Nat) : SyntacticCategory system := size

/-- Recover the number of variables in a finite-context object. -/
abbrev objectSize (context : SyntacticCategory system) : Nat := context

/-- Quotient arrows of the syntactic category. -/
abbrev Hom (input output : Nat) :=
  Quotient (BoundedTermTuple.consequenceSetoid system input output)

/-- Pass a raw bounded tuple to its syntactic arrow class. -/
def mk {input output : Nat} (tuple : BoundedTermTuple S input output) :
    Hom system input output :=
  Quotient.mk (BoundedTermTuple.consequenceSetoid system input output) tuple

/-- Equality of displayed arrows is exactly pointwise generated consequence. -/
theorem mk_eq_iff {input output : Nat}
    (left right : BoundedTermTuple S input output) :
    mk system left = mk system right ↔
      BoundedTermTuple.Equivalent system left right := by
  change Quotient.mk (BoundedTermTuple.consequenceSetoid system input output)
      left = Quotient.mk
        (BoundedTermTuple.consequenceSetoid system input output) right ↔ _
  exact Quotient.eq_iff_equiv

/-- Quotient composition induced by raw tuple substitution. -/
def comp {first second third : Nat} :
    Hom system first second → Hom system second third →
      Hom system first third :=
  Quotient.lift₂
    (fun earlier later =>
      mk system (BoundedTermTuple.comp earlier later))
    (by
      intro earlier earlier' later later' earlierEquivalent laterEquivalent
      apply (mk_eq_iff system _ _).mpr
      exact BoundedTermTuple.comp_equivalent system earlierEquivalent
        laterEquivalent)

instance category : CategoryTheory.Category (SyntacticCategory system) where
  Hom input output :=
    Hom system (objectSize system input) (objectSize system output)
  id size := mk system (BoundedTermTuple.identity (objectSize system size))
  comp earlier later := comp system earlier later
  id_comp arrow := by
    induction arrow using Quotient.inductionOn with
    | _ tuple =>
        apply (mk_eq_iff system _ _).mpr
        rw [BoundedTermTuple.identity_comp]
        exact (BoundedTermTuple.consequenceSetoid system _ _).refl tuple
  comp_id arrow := by
    induction arrow using Quotient.inductionOn with
    | _ tuple =>
        apply (mk_eq_iff system _ _).mpr
        rw [BoundedTermTuple.comp_identity]
        exact (BoundedTermTuple.consequenceSetoid system _ _).refl tuple
  assoc firstSecond secondThird thirdFourth := by
    induction firstSecond using Quotient.inductionOn with
    | _ firstSecond =>
      induction secondThird using Quotient.inductionOn with
      | _ secondThird =>
        induction thirdFourth using Quotient.inductionOn with
        | _ thirdFourth =>
          apply (mk_eq_iff system _ _).mpr
          rw [BoundedTermTuple.comp_assoc]
          exact (BoundedTermTuple.consequenceSetoid system _ _).refl _

/-- A bounded term as a one-output arrow. -/
def termArrow {input : Nat} (term : Term.Bounded S input) :
    object system input ⟶ object system 1 :=
  mk system ⟨fun _position => term⟩

/-- Generated equational consequence is exactly equality of the corresponding
one-output arrows in the syntactic category. -/
theorem termArrow_eq_iff {input : Nat} (left right : Term.Bounded S input) :
    termArrow system left = termArrow system right ↔
      EquationalConsequence system (left.1, right.1) := by
  unfold termArrow
  rw [mk_eq_iff]
  constructor
  · intro equivalent
    have position : Fin (objectSize system (object system 1)) :=
      ⟨0, by simp [objectSize, object]⟩
    exact equivalent position
  · intro consequence _position
    exact consequence

end SyntacticCategory

end Mettapedia.UniversalAlgebra
