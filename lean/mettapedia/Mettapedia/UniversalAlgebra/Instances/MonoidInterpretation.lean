import Mettapedia.UniversalAlgebra.EquationSystemInterpretation
import Mettapedia.UniversalAlgebra.InterpretabilityOrder
import Mettapedia.UniversalAlgebra.Instances.MonoidConsequenceInvariance
import Mettapedia.UniversalAlgebra.NIK.Interpretation

/-!
# Interpretation controls for monoid equation systems

The monoid equations interpret canonically in their commutative extension.
A redundant extension interprets in both directions.  In contrast, the
identity operation map cannot interpret the commutative extension back in the
monoid equations, because commutativity fails in a free noncommutative monoid.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.Monoid

open Mettapedia.UniversalAlgebra

namespace Term

/-- The ordered variable-occurrence word of a monoid term. -/
def variableWord : Term signature → List Nat
  | .var index => [index]
  | .op .mul arguments =>
      variableWord (arguments ⟨0, by decide⟩) ++
        variableWord (arguments ⟨1, by decide⟩)
  | .op .one _arguments => []

/-- Evaluating a monoid term in a free monoid replaces each variable
occurrence in its ordered word by the valuation word. -/
theorem toList_evaluate_freeMonoid {Generator : Type}
    (valuation : Nat → FreeMonoid Generator) : ∀ term : Term signature,
    FreeMonoid.toList
        (term.evaluate (mathlibModel (FreeMonoid Generator)) valuation) =
      (variableWord term).flatMap (fun index =>
        FreeMonoid.toList (valuation index))
  | .var _index => by
      simp only [Term.evaluate, variableWord, List.flatMap_singleton]
  | .op .mul arguments => by
      simp only [Term.evaluate, mathlibModel, FreeMonoid.toList_mul,
        variableWord, List.flatMap_append]
      congr 1
      · exact toList_evaluate_freeMonoid valuation (arguments ⟨0, by decide⟩)
      · exact toList_evaluate_freeMonoid valuation (arguments ⟨1, by decide⟩)
  | .op .one _arguments => rfl

/-- Every entry of the occurrence word is a variable occurrence of the term
and therefore obeys any declared finite variable bound. -/
theorem variableWord_mem_lt {bound : Nat} {term : Term signature}
    (bounded : term.VariablesBelow bound) {index : Nat}
    (member : index ∈ variableWord term) : index < bound := by
  induction term with
  | var variableIndex =>
      simp only [variableWord, List.mem_singleton] at member
      subst index
      change variableIndex < bound at bounded
      exact bounded
  | op operation arguments ih =>
      cases operation with
      | mul =>
          simp only [variableWord, List.mem_append] at member
          rcases member with member | member
          · exact ih ⟨0, by decide⟩ (bounded ⟨0, by decide⟩) member
          · exact ih ⟨1, by decide⟩ (bounded ⟨1, by decide⟩) member
      | one =>
          simp only [variableWord, List.not_mem_nil] at member

/-- A term with no available variables has an empty occurrence word. -/
theorem variableWord_eq_nil_of_variablesBelow_zero {term : Term signature}
    (bounded : term.VariablesBelow 0) : variableWord term = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro index member
  exact Nat.not_lt_zero index (variableWord_mem_lt bounded member)

/-- Direct bounded evaluation in a free monoid is the occurrence word with
the supplied finite argument words substituted. -/
theorem toList_evaluateBelow_freeMonoid {Generator : Type} {bound : Nat}
    (arguments : Fin bound → FreeMonoid Generator)
    (term : Term signature) (bounded : term.VariablesBelow bound) :
    FreeMonoid.toList
        (term.evaluateBelow (mathlibModel (FreeMonoid Generator)) arguments
          bounded) =
      (variableWord term).flatMap (fun index =>
        if below : index < bound
        then FreeMonoid.toList (arguments ⟨index, below⟩)
        else []) := by
  rw [Term.evaluateBelow_eq_evaluate
    (mathlibModel (FreeMonoid Generator)) arguments
    (fun index => if below : index < bound then arguments ⟨index, below⟩
      else 1)
    (by intro index below; simp only [below, dite_true])]
  rw [toList_evaluate_freeMonoid]
  apply List.flatMap_congr
  intro index _member
  by_cases below : index < bound
  · simp only [below, dite_true]
  · simp only [below, dite_false, FreeMonoid.toList_one]

theorem swappedSingletons_ne {word : List Nat} (nonempty : word ≠ [])
    (belowTwo : ∀ index ∈ word, index < 2) :
    word.flatMap (fun index => if index = 0 then [false] else [true]) ≠
      word.flatMap (fun index => if index = 0 then [true] else [false]) := by
  cases word with
  | nil => exact (nonempty rfl).elim
  | cons head tail =>
      have headBelow : head < 2 := belowTwo head (by simp)
      have headCases : head = 0 ∨ head = 1 := by omega
      rcases headCases with rfl | rfl <;> simp

end Term

namespace Signature.Interpretation

/-- The binary operation induced by a monoid-signature interpretation in the
free Boolean monoid. -/
def freeBoolMul
    (interpretation : Signature.Interpretation signature signature)
    (left right : FreeMonoid Bool) : FreeMonoid Bool :=
  (interpretation.operation .mul).1.evaluateBelow
    (mathlibModel (FreeMonoid Bool))
    (fun position => if position.val = 0 then left else right)
    (interpretation.operation .mul).2

/-- The nullary operation induced by a monoid-signature interpretation in the
free Boolean monoid. -/
def freeBoolOne
    (interpretation : Signature.Interpretation signature signature) :
    FreeMonoid Bool :=
  (interpretation.operation .one).1.evaluateBelow
    (mathlibModel (FreeMonoid Bool)) Fin.elim0
    (interpretation.operation .one).2

@[simp] theorem evaluate_mul_reduct
    (interpretation : Signature.Interpretation signature signature)
    (valuation : Nat → FreeMonoid Bool) (left right : Term signature) :
    (mul left right).evaluate
        ((mathlibModel (FreeMonoid Bool)).reduct interpretation) valuation =
      freeBoolMul interpretation
        (left.evaluate
          ((mathlibModel (FreeMonoid Bool)).reduct interpretation) valuation)
        (right.evaluate
          ((mathlibModel (FreeMonoid Bool)).reduct interpretation) valuation) :=
  by
    unfold mul freeBoolMul Model.reduct
    simp only [Term.evaluate]
    congr 2
    funext position
    by_cases first : position.val = 0 <;> simp [first]

@[simp] theorem evaluate_one_reduct
    (interpretation : Signature.Interpretation signature signature)
    (valuation : Nat → FreeMonoid Bool) :
    one.evaluate
        ((mathlibModel (FreeMonoid Bool)).reduct interpretation) valuation =
      freeBoolOne interpretation := by
  unfold one freeBoolOne Model.reduct
  simp only [Term.evaluate]
  congr 2
  funext position
  exact Fin.elim0 position

/-- The interpreted multiplication's free word is obtained by replacing
formal variables zero and one in its operation template. -/
theorem toList_freeBoolMul
    (interpretation : Signature.Interpretation signature signature)
    (left right : FreeMonoid Bool) :
    FreeMonoid.toList (freeBoolMul interpretation left right) =
      (Term.variableWord (interpretation.operation .mul).1).flatMap
        (fun index =>
          if _below : index < 2
          then FreeMonoid.toList
            (if index = 0 then left else right)
          else []) := by
  exact Term.toList_evaluateBelow_freeMonoid
    (fun position => if position.val = 0 then left else right)
    (interpretation.operation .mul).1
    (interpretation.operation .mul).2

/-- A nullary interpreted monoid term has no variable occurrences and hence
evaluates to the native free-monoid unit. -/
theorem toList_freeBoolOne
    (interpretation : Signature.Interpretation signature signature) :
    FreeMonoid.toList (freeBoolOne interpretation) = [] := by
  rw [freeBoolOne, Term.toList_evaluateBelow_freeMonoid]
  rw [Term.variableWord_eq_nil_of_variablesBelow_zero
    (interpretation.operation .one).2]
  rfl

end Signature.Interpretation

/-- The identity operation map interprets the monoid equations in their
commutative extension. -/
def interpretationInCommutative :
    EquationSystem.Interpretation equationSystem
      commutativeEquationSystem where
  symbols := Signature.Interpretation.id signature
  axiom_consequence equation member := by
    simpa only [Equation.translate_id] using
      consequence_lifts_to_commutative
        (EquationalConsequence.of_mem member)

/-- Positive control: the commutative extension is at least as expressive as
the monoid system under algebraic interpretation. -/
theorem monoid_isInterpretableIn_commutative :
    equationSystem.IsInterpretableIn commutativeEquationSystem :=
  ⟨interpretationInCommutative⟩

/-- The redundant extension and the original monoid equations interpret one
another through their shared symbols. -/
theorem derivedExtension_mutuallyInterpretable :
    derivedExtension.IsInterpretableIn equationSystem ∧
      equationSystem.IsInterpretableIn derivedExtension :=
  ⟨⟨EquationSystem.Interpretation.ofSameConsequences
      derivedExtension_sameConsequences⟩,
    ⟨EquationSystem.Interpretation.ofSameConsequences
      derivedExtension_sameConsequences.symm⟩⟩

/-- Commutativity is not generated by the ordinary monoid equations. -/
theorem commutativity_not_consequence :
    ¬ EquationalConsequence equationSystem (mul x y, mul y x) := by
  intro derivation
  have result := consequence_holds_in_monoid derivation (FreeMonoid Bool)
    (fun index => if index = 0 then FreeMonoid.ofList [false]
      else FreeMonoid.ofList [true])
  have listResult := congrArg FreeMonoid.toList result
  simp [x, y] at listResult

/-- Negative control: no interpretation with the canonical identity symbol
map sends the commutative equations back into the monoid equations. -/
theorem no_identitySymbol_interpretation_of_commutative_in_monoid :
    ¬ ∃ interpretation : EquationSystem.Interpretation
        commutativeEquationSystem equationSystem,
      interpretation.symbols = Signature.Interpretation.id signature := by
  rintro ⟨interpretation, symbolsIdentity⟩
  have commutativityMember : (mul x y, mul y x) ∈
      commutativeEquationSystem := by
    change (mul x y, mul y x) ∈
      equationSystem.equations ++ [(mul x y, mul y x)]
    exact List.mem_append_right _ (by simp)
  have translated := interpretation.axiom_consequence _ commutativityMember
  rw [symbolsIdentity] at translated
  apply commutativity_not_consequence
  simpa only [Equation.translate_id] using translated

/-- Strong negative control: the commutative-monoid equations have no
algebraic interpretation at all in the ordinary monoid equations.  Any binary
monoid term is an ordered word in its arguments; a nonempty word cannot equal
the word obtained by swapping every occurrence of variables zero and one. -/
theorem commutative_not_interpretableIn_monoid :
    ¬ commutativeEquationSystem.IsInterpretableIn equationSystem := by
  rintro ⟨interpretation⟩
  let targetModel : Model signature (FreeMonoid Bool) :=
    mathlibModel (FreeMonoid Bool)
  have targetSatisfies : targetModel.Satisfies equationSystem :=
    mathlibModel_satisfies (FreeMonoid Bool)
  have sourceSatisfies :
      (targetModel.reduct interpretation.symbols).Satisfies
        commutativeEquationSystem :=
    interpretation.reduct_satisfies targetModel targetSatisfies

  have leftUnitMember : (mul one x, x) ∈ commutativeEquationSystem := by
    change (mul one x, x) ∈
      equationSystem.equations ++ [(mul x y, mul y x)]
    exact List.mem_append_left _ (by simp [equationSystem])
  let generator : FreeMonoid Bool := FreeMonoid.of false
  let unitValuation : Nat → FreeMonoid Bool :=
    fun index => if index = 0 then generator else 1
  have unitEquality :=
    sourceSatisfies (mul one x, x) leftUnitMember unitValuation
  have unitLaw :
      Signature.Interpretation.freeBoolMul interpretation.symbols
          (Signature.Interpretation.freeBoolOne interpretation.symbols)
          generator = generator := by
    simpa only [Signature.Interpretation.evaluate_mul_reduct,
      Signature.Interpretation.evaluate_one_reduct, x, Term.evaluate,
      targetModel, unitValuation, if_pos] using unitEquality

  let multiplicationTemplate := (interpretation.symbols.operation .mul).1
  have multiplicationBounded : multiplicationTemplate.VariablesBelow 2 :=
    (interpretation.symbols.operation .mul).2
  have multiplicationWordNonempty :
      Term.variableWord multiplicationTemplate ≠ [] := by
    intro wordEmpty
    have listLaw := congrArg FreeMonoid.toList unitLaw
    have multiplicationListEmpty :
        FreeMonoid.toList
            (Signature.Interpretation.freeBoolMul interpretation.symbols
              (Signature.Interpretation.freeBoolOne interpretation.symbols)
              generator) = [] := by
      rw [Signature.Interpretation.toList_freeBoolMul, wordEmpty]
      rfl
    rw [multiplicationListEmpty] at listLaw
    simp [generator] at listLaw

  have commutativityMember : (mul x y, mul y x) ∈
      commutativeEquationSystem := by
    change (mul x y, mul y x) ∈
      equationSystem.equations ++ [(mul x y, mul y x)]
    exact List.mem_append_right _ (by simp)
  let commutativityValuation : Nat → FreeMonoid Bool :=
    fun index => if index = 0 then FreeMonoid.of false
      else FreeMonoid.of true
  have commutativityEquality := sourceSatisfies
    (mul x y, mul y x) commutativityMember commutativityValuation
  have commutativityLaw :
      Signature.Interpretation.freeBoolMul interpretation.symbols
          (FreeMonoid.of false) (FreeMonoid.of true) =
        Signature.Interpretation.freeBoolMul interpretation.symbols
          (FreeMonoid.of true) (FreeMonoid.of false) := by
    simpa only [Signature.Interpretation.evaluate_mul_reduct,
      x, y, Term.evaluate, targetModel, commutativityValuation, if_pos, if_neg,
      Nat.one_ne_zero, if_false] using commutativityEquality

  have leftWord :
      FreeMonoid.toList
          (Signature.Interpretation.freeBoolMul interpretation.symbols
            (FreeMonoid.of false) (FreeMonoid.of true)) =
        (Term.variableWord multiplicationTemplate).flatMap
          (fun index => if index = 0 then [false] else [true]) := by
    rw [Signature.Interpretation.toList_freeBoolMul]
    apply List.flatMap_congr
    intro index member
    have below := Term.variableWord_mem_lt multiplicationBounded member
    simp only [below, dite_true]
    by_cases zero : index = 0 <;> simp [zero]
  have rightWord :
      FreeMonoid.toList
          (Signature.Interpretation.freeBoolMul interpretation.symbols
            (FreeMonoid.of true) (FreeMonoid.of false)) =
        (Term.variableWord multiplicationTemplate).flatMap
          (fun index => if index = 0 then [true] else [false]) := by
    rw [Signature.Interpretation.toList_freeBoolMul]
    apply List.flatMap_congr
    intro index member
    have below := Term.variableWord_mem_lt multiplicationBounded member
    simp only [below, dite_true]
    by_cases zero : index = 0 <;> simp [zero]

  apply Term.swappedSingletons_ne multiplicationWordNonempty
    (fun index member => Term.variableWord_mem_lt multiplicationBounded member)
  exact leftWord.symm.trans
    ((congrArg FreeMonoid.toList commutativityLaw).trans rightWord)

/-- The commutative extension is strictly above the monoid equations in the
algebraic-interpretability preorder. -/
theorem monoid_strictlyBelow_commutative :
    EquationSystem.InterpretabilityOrder.of equationSystem <
      EquationSystem.InterpretabilityOrder.of commutativeEquationSystem := by
  constructor
  · exact monoid_isInterpretableIn_commutative
  · exact commutative_not_interpretableIn_monoid

/-- The canonical monoid interpretation gives a semantic simulation between
the corresponding NIK theory objects. -/
theorem commutativeNIK_semanticallySimulates_monoidNIK :
    Mettapedia.Logic.TheorySimulation.SemanticallySimulates
      (NIK.theoryObject commutativeEquationSystem)
      (NIK.theoryObject equationSystem) :=
  NIK.semanticallySimulates interpretationInCommutative

end Mettapedia.UniversalAlgebra.Monoid
