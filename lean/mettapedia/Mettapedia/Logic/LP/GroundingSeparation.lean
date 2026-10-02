import Mettapedia.Logic.LP.Semantics

/-!
# Groundings separate distinct terms

When a signature has two distinct ground terms, two terms with the same
ground instance under every grounding are the same term.  So the free
(Herbrand) interpretation of terms validates no equation except identities:
an equational law that is to be used for rewriting needs a model that is not
free.

The hypothesis is needed.  With a single ground term every two terms have the
same ground instances.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP

variable {σ : LPSignature}

namespace GroundTerm

/-- The size of a ground term, as a term. -/
def size (term : GroundTerm σ) : ℕ := term.toTerm.size

theorem size_argument_lt {symbol : σ.functionSymbols}
    (arguments : Fin (σ.functionArity symbol) → GroundTerm σ)
    (position : Fin (σ.functionArity symbol)) :
    (arguments position).size < (GroundTerm.app symbol arguments).size :=
  Term.size_subterm (ts := fun index => (arguments index).toTerm) position

end GroundTerm

namespace Grounding

/-- The grounding that sends every variable to one ground term. -/
def constant (value : GroundTerm σ) : Grounding σ := fun _ => value

/-- A term is a variable, or it has the same ground instance under every
grounding, or each constant grounding makes it larger than its value. -/
theorem variable_or_closed_or_grows (term : Term σ) :
    (∃ name, term = .var name) ∨
      (∀ first second : Grounding σ, first.groundTerm term = second.groundTerm term) ∨
      (∀ value : GroundTerm σ, value.size < ((constant value).groundTerm term).size) := by
  induction term with
  | var name => exact Or.inl ⟨name, rfl⟩
  | const symbol => exact Or.inr (Or.inl fun _ _ => rfl)
  | app symbol arguments ih =>
      refine Or.inr ?_
      by_cases closed : ∀ position, ∀ first second : Grounding σ,
          first.groundTerm (arguments position) = second.groundTerm (arguments position)
      · refine Or.inl fun first second => ?_
        simp only [groundTerm]
        exact congrArg (GroundTerm.app symbol) (funext fun position => closed position first second)
      · refine Or.inr fun value => ?_
        obtain ⟨position, open_⟩ := not_forall.mp closed
        have below : value.size ≤ ((constant value).groundTerm (arguments position)).size := by
          rcases ih position with ⟨name, shape⟩ | same | grows
          · rw [shape]
            exact Nat.le_refl _
          · exact absurd same open_
          · exact Nat.le_of_lt (grows value)
        exact Nat.lt_of_le_of_lt below
          (GroundTerm.size_argument_lt
            (fun index => (constant value).groundTerm (arguments index)) position)

/-- A variable and a term that is not a variable have different ground
instances under some grounding. -/
theorem variable_separated {first second : GroundTerm σ} (different : first ≠ second)
    (name : σ.vars) {term : Term σ} (notVariable : ∀ other, term ≠ .var other)
    (same : ∀ grounding : Grounding σ, grounding name = grounding.groundTerm term) : False := by
  rcases variable_or_closed_or_grows term with ⟨other, shape⟩ | closed | grows
  · exact notVariable other shape
  · exact different ((same (constant first)).trans
      ((closed (constant first) (constant second)).trans (same (constant second)).symm))
  · have larger := grows first
    rw [← same (constant first)] at larger
    exact Nat.lt_irrefl _ larger

/-- **Groundings separate distinct terms.**  In a signature with two distinct
ground terms, terms with the same ground instance under every grounding are
equal. -/
theorem eq_of_groundTerm_eq {first second : GroundTerm σ} (different : first ≠ second) :
    ∀ {left right : Term σ},
      (∀ grounding : Grounding σ, grounding.groundTerm left = grounding.groundTerm right) →
        left = right := by
  intro left
  induction left with
  | var name =>
      intro right same
      cases right with
      | var other =>
          by_contra distinct
          have names : name ≠ other := fun equal => distinct (congrArg Term.var equal)
          classical
          have image := same fun queried => if queried = name then first else second
          simp only [groundTerm, if_true, if_neg (Ne.symm names)] at image
          exact different image
      | const symbol =>
          exact (variable_separated different name (fun _ shape => by cases shape) same).elim
      | app symbol arguments =>
          exact (variable_separated different name (fun _ shape => by cases shape) same).elim
  | const symbol =>
      intro right same
      cases right with
      | var other =>
          exact (variable_separated different other (fun _ shape => by cases shape)
            fun grounding => (same grounding).symm).elim
      | const otherSymbol =>
          have image := same (constant first)
          simp only [groundTerm, GroundTerm.const.injEq] at image
          rw [image]
      | app otherSymbol arguments =>
          have image := same (constant first)
          simp only [groundTerm] at image
          cases image
  | app symbol arguments ih =>
      intro right same
      cases right with
      | var other =>
          exact (variable_separated different other (fun _ shape => by cases shape)
            fun grounding => (same grounding).symm).elim
      | const otherSymbol =>
          have image := same (constant first)
          simp only [groundTerm] at image
          cases image
      | app otherSymbol otherArguments =>
          have image := same (constant first)
          simp only [groundTerm, GroundTerm.app.injEq] at image
          obtain ⟨rfl, -⟩ := image
          have pointwise : arguments = otherArguments := by
            funext position
            refine ih position fun grounding => ?_
            have image := same grounding
            simp only [groundTerm, GroundTerm.app.injEq, heq_eq_eq, true_and] at image
            exact congrFun image position
          rw [pointwise]

/-- The hypothesis of two distinct ground terms is needed: when all ground
terms are equal, every two terms have the same ground instances. -/
theorem groundTerm_eq_of_subsingleton [Subsingleton (GroundTerm σ)] (left right : Term σ)
    (grounding : Grounding σ) : grounding.groundTerm left = grounding.groundTerm right :=
  Subsingleton.elim _ _

end Grounding

namespace GroundingSeparationControls

/-- One constant, one variable and no function symbol: a single ground term. -/
abbrev single : LPSignature where
  constants := Unit
  vars := Unit
  relationSymbols := Empty
  relationArity := fun symbol => symbol.elim
  functionSymbols := Empty
  functionArity := fun symbol => symbol.elim

instance : Subsingleton (GroundTerm single) where
  allEq := by
    intro left right
    cases left with
    | const first =>
        cases right with
        | const second => rfl
        | app symbol arguments => exact symbol.elim
    | app symbol arguments => exact symbol.elim

/-- With a single ground term, the variable and the constant are different
terms with the same ground instances. -/
theorem variable_and_constant_not_separated :
    (Term.var () : Term single) ≠ Term.const () ∧
      ∀ grounding : Grounding single,
        grounding.groundTerm (.var ()) = grounding.groundTerm (.const ()) :=
  ⟨fun same => (by cases same),
    fun grounding => Grounding.groundTerm_eq_of_subsingleton _ _ grounding⟩

/-- Two constants: the variable and a constant are separated. -/
abbrev pair : LPSignature where
  constants := Bool
  vars := Unit
  relationSymbols := Empty
  relationArity := fun symbol => symbol.elim
  functionSymbols := Empty
  functionArity := fun symbol => symbol.elim

theorem variable_and_constant_separated :
    ¬ ∀ grounding : Grounding pair,
        grounding.groundTerm (.var ()) = grounding.groundTerm (.const true) := by
  intro same
  have equal : (Term.var () : Term pair) = Term.const true :=
    Grounding.eq_of_groundTerm_eq (first := GroundTerm.const true)
      (second := GroundTerm.const false)
      (fun identical => absurd (GroundTerm.const.inj identical) (by decide)) same
  cases equal

end GroundingSeparationControls

end Mettapedia.Logic.LP
