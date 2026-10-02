import Mettapedia.GSLT.Dynamics.ResumptionOperationTheory
import Mathlib.Algebra.Category.ModuleCat.Semi
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic

/-!
# Linear interpretations of weighted finite operations

Finite weighted operations act on valuations by taking the sum of their
ordered contributions. This is a functor from the occurrence-sensitive
writer/list operation theory to Mathlib's semimodule category when scalars
commute. Identity, substitution, projections and products are preserved.

The ordered evaluation and substitution laws need only a semiring. Scalar
linearity is an additional commutative-scalar qualification; it is not imposed
on ordered matrix or tensor coefficients. Aggregation is not faithful: it can
forget physical multiplicity, including contributions that cancel.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.WeightedLinearInterpretation

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.FiniteOperationTheory
open WeightedResumption

variable {Answer Other : Type} {R : Type} [Semiring R]

def evaluate : Contributions Answer R → (Answer → R) → R
  | [], _ => 0
  | (answer, coefficient) :: rest, valuation =>
      coefficient * valuation answer + evaluate rest valuation

theorem evaluate_reindex (answers : Contributions Answer R) (readout : Answer → Other)
    (valuation : Other → R) :
    evaluate (answers.map fun answer => (readout answer.1, answer.2)) valuation =
      evaluate answers (fun answer => valuation (readout answer)) := by
  induction answers with
  | nil => rfl
  | cons head rest ih => rcases head with ⟨answer, coefficient⟩; simp [evaluate, ih]

theorem evaluate_append (left right : Contributions Answer R) (valuation : Answer → R) :
    evaluate (left ++ right) valuation = evaluate left valuation + evaluate right valuation := by
  induction left with
  | nil => simp [evaluate]
  | cons head rest ih => rcases head with ⟨answer, coefficient⟩; simp [evaluate, ih, add_assoc]

theorem evaluate_scale_left (coefficient : R) (answers : Contributions Answer R)
    (valuation : Answer → R) :
    evaluate (answers.map fun answer => (answer.1, coefficient * answer.2)) valuation =
      coefficient * evaluate answers valuation := by
  induction answers with
  | nil => simp [evaluate]
  | cons head rest ih =>
      rcases head with ⟨answer, factor⟩
      simp [evaluate, ih, mul_add, mul_assoc]

theorem evaluate_sequence (answers : Contributions Answer R)
    (next : Answer → Contributions Other R) (valuation : Other → R) :
    evaluate (sequence answers next) valuation =
      evaluate answers (fun answer => evaluate (next answer) valuation) := by
  induction answers with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨answer, coefficient⟩
      rw [sequence_cons, evaluate_append, evaluate_scale_left, ih]
      rfl

theorem evaluate_as_total (answers : Contributions Answer R) (valuation : Answer → R) :
    evaluate answers valuation =
      total (answers.map fun answer => (answer.1, answer.2 * valuation answer.1)) := by
  induction answers with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨answer, coefficient⟩
      simpa [evaluate, total, SemiringTraversal.weightSum] using
        congrArg (fun value => coefficient * valuation answer + value) ih

theorem evaluate_ofFn {n : Nat} (answers : Fin n → Answer × R) (valuation : Answer → R) :
    evaluate (List.ofFn answers) valuation = ∑ index, (answers index).2 * valuation (answers index).1 := by
  rw [evaluate_as_total]
  simp [total, SemiringTraversal.weightSum, List.map_ofFn, List.sum_ofFn]

theorem evaluate_add (answers : Contributions Answer R) (left right : Answer → R) :
    evaluate answers (left + right) = evaluate answers left + evaluate answers right := by
  induction answers with
  | nil => simp [evaluate]
  | cons head rest ih =>
      rcases head with ⟨answer, coefficient⟩
      simp [evaluate, ih, mul_add, add_assoc, add_left_comm]

section CommutativeScalars

variable {S : Type} [CommSemiring S]

def linearFunctional (answers : Contributions Answer S) : (Answer → S) →ₗ[S] S where
  toFun := evaluate answers
  map_add' := evaluate_add answers
  map_smul' := by
    intro coefficient valuation
    induction answers with
    | nil => simp [evaluate]
    | cons head rest ih =>
        rcases head with ⟨answer, factor⟩
        simp [evaluate, ih, smul_eq_mul, mul_add, mul_left_comm]

abbrev WeightedTheory (S : Type) [Monoid S] := Theory (WriterT S List)

def operationLinearMap {n m : WeightedTheory S} (operation : n ⟶ m) :
    (Fin n → S) →ₗ[S] (Fin m → S) where
  toFun valuation index := evaluate (terms operation index).run valuation
  map_add' left right := by funext index; exact evaluate_add _ _ _
  map_smul' coefficient valuation := by
    funext index
    exact (linearFunctional (terms operation index).run).map_smul coefficient valuation

def linearInterpretation : WeightedTheory S ⥤ SemimoduleCat S where
  obj n := SemimoduleCat.of S (Fin n → S)
  map operation := SemimoduleCat.ofHom (operationLinearMap operation)
  map_id n := by
    apply SemimoduleCat.Hom.ext
    apply LinearMap.ext
    intro valuation
    funext index
    change evaluate [(index, (1 : S))] valuation = valuation index
    simp [evaluate]
  map_comp first second := by
    apply SemimoduleCat.Hom.ext
    apply LinearMap.ext
    intro valuation
    funext index
    change evaluate ((terms second index >>= terms first).run) valuation = _
    rw [ResumptionCategory.writer_bind, evaluate_sequence]
    rfl

theorem substitution_linear {n m k : WeightedTheory S} (first : n ⟶ m) (second : m ⟶ k) :
    operationLinearMap (first ≫ second) =
      (operationLinearMap second).comp (operationLinearMap first) := by
  apply LinearMap.ext
  intro valuation
  funext index
  change evaluate ((terms second index >>= terms first).run) valuation = _
  rw [ResumptionCategory.writer_bind, evaluate_sequence]
  rfl

theorem first_projection_linear (n m : Nat) (valuation : Fin (n + m) → S) (index : Fin n) :
    operationLinearMap (firstProjection (M := WriterT S List) n m) valuation index =
      valuation (index.castAdd m) := by
  simp [operationLinearMap, firstProjection, evaluate]

theorem second_projection_linear (n m : Nat) (valuation : Fin (n + m) → S) (index : Fin m) :
    operationLinearMap (secondProjection (M := WriterT S List) n m) valuation index =
      valuation (index.natAdd n) := by
  simp [operationLinearMap, secondProjection, evaluate]

theorem tuple_linear {n : WeightedTheory S} {m k : Nat}
    (first : n ⟶ object (WriterT S List) m) (second : n ⟶ object (WriterT S List) k)
    (valuation : Fin n → S) :
    operationLinearMap (tuple first second) valuation =
      Fin.addCases (operationLinearMap first valuation) (operationLinearMap second valuation) := by
  funext index
  refine Fin.addCases ?_ ?_ index <;> intro index <;>
    simp [operationLinearMap, tuple]

/-- Every linear operation on finite valuations has an explicit weighted
operation representative. Zero coefficients remain physical occurrences in
this representative. -/
def canonicalOperation {n m : Nat} (linear : (Fin n → S) →ₗ[S] (Fin m → S)) :
    object (WriterT S List) n ⟶ object (WriterT S List) m :=
  ofTerms fun output => WriterT.mk (List.ofFn fun input =>
    (input, linear (Pi.single input 1) output))

theorem canonicalOperation_exact {n m : Nat} (linear : (Fin n → S) →ₗ[S] (Fin m → S)) :
    operationLinearMap (canonicalOperation linear) = linear := by
  apply LinearMap.ext
  intro valuation
  funext output
  change evaluate (List.ofFn fun input => (input, linear (Pi.single input 1) output)) valuation = _
  rw [evaluate_ofFn]
  conv_rhs => rw [pi_eq_sum_univ' valuation]
  simp [map_sum, map_smul, Finset.sum_apply, smul_eq_mul, mul_comm]

theorem operationLinearMap_surjective (n m : Nat) :
    Function.Surjective (operationLinearMap (n := object (WriterT S List) n)
      (m := object (WriterT S List) m)) :=
  fun linear => ⟨canonicalOperation linear, canonicalOperation_exact linear⟩

end CommutativeScalars

theorem duplicate_contributions_linear_control (valuation : Unit → Nat) :
    evaluate [((), 2), ((), 3)] valuation = evaluate [((), 5)] valuation := by
  simp [evaluate, ← add_mul]

theorem aggregation_forgets_occurrences :
    ([((), 2), ((), 3)] : Contributions Unit Nat) ≠ [((), 5)] ∧
      linearFunctional ([((), 2), ((), 3)] : Contributions Unit Nat) =
        linearFunctional [((), 5)] := by
  constructor
  · decide +kernel
  · apply LinearMap.ext
    intro valuation
    exact duplicate_contributions_linear_control valuation

end Mettapedia.GSLT.Dynamics.WeightedLinearInterpretation
