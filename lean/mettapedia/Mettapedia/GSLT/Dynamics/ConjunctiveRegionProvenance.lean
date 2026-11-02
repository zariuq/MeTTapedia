import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Occurrence provenance for arbitrary finite conjunctive regions

Each factor has an arity-typed ground row carrier and a pattern whose cells
are constants or scoped variables. The variable type can include a frame;
the model never identifies variables merely by printed name. A full valuation
must satisfy every repeated occurrence of a variable in a factor.

The reference enumerates one physical row occurrence per factor in authored
order. Annotation interpretation sums the products of these witness lists.
An independent factorized evaluator multiplies per-factor sums and agrees for
any finite conjunction, cyclic queries included. This is a per-assignment
semantic law, not an assignment-enumeration algorithm or a join cost bound.

The polynomial interpretation retains occurrence tokens. Counts and other
commutative-semiring views commute with evaluation. Ordered witness streams,
absence tests and probabilities are not interchangeable with those views.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ConjunctiveRegionProvenance

universe u v w x y

inductive Cell (Var : Type u) (Value : Type v) where
  | constant (value : Value)
  | variable (name : Var)
  deriving DecidableEq

def Cell.eval {Var : Type u} {Value : Type v} (environment : Var → Value) : Cell Var Value → Value
  | .constant value => value
  | .variable name => environment name

structure Factor (Var : Type u) (Value : Type v) (Id : Type w) where
  arity : Nat
  pattern : Fin arity → Cell Var Value
  rows : List (Id × (Fin arity → Value))

namespace Factor

variable {Var : Type u} {Value : Type v} {Id : Type w} [DecidableEq Value]

def acceptsRow (environment : Var → Value) (factor : Factor Var Value Id)
    (row : Id × (Fin factor.arity → Value)) : Bool :=
  decide (∀ column, row.2 column = (factor.pattern column).eval environment)

theorem acceptsRow_iff (environment : Var → Value) (factor : Factor Var Value Id)
    (row : Id × (Fin factor.arity → Value)) : factor.acceptsRow environment row = true ↔
    ∀ column, row.2 column = (factor.pattern column).eval environment := by simp [acceptsRow]

def occurrences (environment : Var → Value) (factor : Factor Var Value Id) : List Id :=
  (factor.rows.filter (factor.acceptsRow environment)).map Prod.fst

theorem mem_occurrences (environment : Var → Value) (factor : Factor Var Value Id) (id : Id) :
    id ∈ factor.occurrences environment ↔
      ∃ row ∈ factor.rows, row.1 = id ∧ ∀ column,
        row.2 column = (factor.pattern column).eval environment := by
  simp only [occurrences, List.mem_map, List.mem_filter, acceptsRow_iff]
  constructor
  · rintro ⟨row, ⟨present, matched⟩, same⟩
    exact ⟨row, present, same, matched⟩
  · rintro ⟨row, present, same, matched⟩
    exact ⟨row, ⟨present, matched⟩, same⟩

end Factor

variable {Var : Type u} {Value : Type v} {Id : Type w} [DecidableEq Value]

/-- The nested-loop reference retains each complete ordered witness. A row
token may occur twice when the source uses that row in two read positions. -/
def witnesses (environment : Var → Value) : List (Factor Var Value Id) → List (List Id)
  | [] => [[]]
  | factor :: rest => (factor.occurrences environment).flatMap fun occurrence =>
      (witnesses environment rest).map (occurrence :: ·)

def interpretation {K : Type x} [CommSemiring K] (tag : Id → K) (paths : List (List Id)) : K :=
  (paths.map fun path => (path.map tag).prod).sum

/-- The target does not construct the Cartesian product of witness lists. -/
def factorized {K : Type x} [CommSemiring K] (tag : Id → K) (environment : Var → Value)
    (factors : List (Factor Var Value Id)) : K :=
  (factors.map fun factor => ((factor.occurrences environment).map tag).sum).prod

private theorem interpretation_prepend {K : Type x} [CommSemiring K]
    (tag : Id → K) (occurrence : Id) (paths : List (List Id)) :
    interpretation tag (paths.map (occurrence :: ·)) = tag occurrence * interpretation tag paths := by
  simp only [interpretation, List.map_map, Function.comp_def, List.map_cons, List.prod_cons]
  rw [List.sum_map_mul_left]

private theorem interpretation_flatMap {K : Type x} [CommSemiring K] (tag : Id → K)
    (occurrences : List Id) (paths : List (List Id)) :
    interpretation tag (occurrences.flatMap fun occurrence => paths.map (occurrence :: ·)) =
      (occurrences.map tag).sum * interpretation tag paths := by
  induction occurrences with
  | nil => simp [interpretation]
  | cons occurrence rest ih =>
      have append (first second : List (List Id)) :
          interpretation tag (first ++ second) = interpretation tag first + interpretation tag second := by
        simp [interpretation, List.sum_append]
      rw [List.flatMap_cons, append, interpretation_prepend, ih]
      simp [add_mul]

/-- Arbitrary finite conjunctions, not just paths or binary joins, satisfy
the factorization law at every complete valuation. -/
theorem factorized_exact {K : Type x} [CommSemiring K] (tag : Id → K)
    (environment : Var → Value) (factors : List (Factor Var Value Id)) :
    factorized tag environment factors = interpretation tag (witnesses environment factors) := by
  induction factors with
  | nil => simp [factorized, witnesses, interpretation]
  | cons factor rest ih =>
      simp only [factorized, List.map_cons, List.prod_cons] at ih ⊢
      rw [witnesses, interpretation_flatMap, ← ih]

theorem interpretation_map {K : Type x} {L : Type y} [CommSemiring K] [CommSemiring L]
    (hom : K →+* L) (tag : Id → K) (paths : List (List Id)) :
    hom (interpretation tag paths) = interpretation (fun id => hom (tag id)) paths := by
  simp [interpretation, map_list_sum, map_list_prod, List.map_map, Function.comp_def]

theorem factorized_map {K : Type x} {L : Type y} [CommSemiring K] [CommSemiring L]
    (hom : K →+* L) (tag : Id → K) (environment : Var → Value)
    (factors : List (Factor Var Value Id)) :
    hom (factorized tag environment factors) = factorized (fun id => hom (tag id)) environment factors := by
  rw [factorized_exact, interpretation_map, factorized_exact]

noncomputable def provenance (environment : Var → Value) (factors : List (Factor Var Value Id)) :
    MvPolynomial Id Nat := interpretation MvPolynomial.X (witnesses environment factors)

/-- Universal occurrence annotations specialize by the unique polynomial
evaluation map. This does not grant independence to repeated event labels. -/
theorem provenance_specializes {K : Type*} [CommSemiring K] (tag : Id → K)
    (environment : Var → Value) (factors : List (Factor Var Value Id)) :
    (MvPolynomial.eval₂Hom (Nat.castRingHom K) tag) (provenance environment factors) =
      factorized tag environment factors := by
  unfold provenance
  rw [interpretation_map, factorized_exact]
  simp

theorem counting_preserves_witness_multiplicity (environment : Var → Value)
    (factors : List (Factor Var Value Id)) :
    factorized (fun _ => (1 : Nat)) environment factors = (witnesses environment factors).length := by
  rw [factorized_exact]
  simp [interpretation]

theorem factor_order_preserves_semiring_value {K : Type x} [CommSemiring K] (tag : Id → K)
    (environment : Var → Value) {first second : List (Factor Var Value Id)}
    (reordered : first.Perm second) :
    factorized tag environment first = factorized tag environment second :=
  (reordered.map _).prod_eq

namespace Controls

theorem empty_conjunction_has_one_empty_witness :
    witnesses (Id := Nat) (fun (_ : Nat) => (7 : Nat)) [] = [[]] ∧
      factorized (fun (_ : Nat) => (1 : Nat)) (fun (_ : Nat) => (7 : Nat)) [] = 1 := by decide

def nullary : Factor Nat Nat Nat :=
  ⟨0, Fin.elim0, [(4, Fin.elim0), (5, Fin.elim0)]⟩

theorem nullary_facts_still_have_multiplicity :
    witnesses (fun (_ : Nat) => (7 : Nat)) [nullary] = [[4], [5]] := by decide

def duplicateValues : Factor Nat Nat Nat :=
  ⟨1, fun _ => .variable 0, [(10, fun _ => 7), (20, fun _ => 7)]⟩

theorem equal_values_have_distinct_witnesses :
    witnesses (fun _ => 7) [duplicateValues] = [[10], [20]] := by decide

theorem self_join_keeps_aliased_reads :
    witnesses (fun _ => 7) [duplicateValues, duplicateValues] =
      [[10, 10], [10, 20], [20, 10], [20, 20]] := by decide

theorem self_join_count_is_four :
    factorized (fun _ => (1 : Nat)) (fun _ => 7) [duplicateValues, duplicateValues] = 4 := by decide

def repeatedVariable : Factor Nat Nat Nat :=
  ⟨2, fun _ => .variable 0, [(30, fun column => if column = 0 then 1 else 2)]⟩

def separateVariables : Factor Nat Nat Nat :=
  ⟨2, fun column => .variable column.val, repeatedVariable.rows⟩

theorem correlation_cannot_be_dropped :
    witnesses (fun name => if name = 0 then 1 else 2) [repeatedVariable] = [] ∧
      witnesses (fun name => if name = 0 then 1 else 2) [separateVariables] = [[30]] := by decide

theorem provenance_keeps_physical_tokens :
    provenance (fun _ => 7) [duplicateValues] =
      MvPolynomial.X 10 + MvPolynomial.X 20 := by
  unfold provenance
  rw [equal_values_have_distinct_witnesses]
  simp [interpretation]

theorem factorization_is_not_ordered_witness_equality :
    ([10, 20] : List Nat) ≠ [20, 10] ∧
      ([10, 20] : List Nat).Perm [20, 10] := by
  exact ⟨by decide, List.Perm.swap ..⟩

end Controls

#print axioms factorized_exact
#print axioms provenance_specializes
#print axioms counting_preserves_witness_multiplicity
#print axioms factor_order_preserves_semiring_value

end Mettapedia.GSLT.Dynamics.ConjunctiveRegionProvenance
