import Mettapedia.GSLT.Dynamics.ResumptionAlgebra
import Mettapedia.GSLT.Dynamics.SemiringTraversal

/-!
# Algebra-valued handlers of free resumptions

Each authorized response occurrence carries a coefficient. Alternative
occurrences remain in a list, including zero-coefficient occurrences. A
declared readout may subsequently combine them. Sequencing multiplies in
execution order; multiplication is not assumed commutative.

The handler respects substitution and algebra homomorphisms. Those are proved
laws of the free construction, not additional axioms on a native evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.WeightedResumption

open ResumptionAlgebra

universe uOp uResponse uAnswer uOther uValue

variable {Operation : Type uOp} {Response : Operation → Type uResponse}
  {Answer : Type uAnswer} {Other : Type uOther} {V : Type uValue}

/-- Ordered, occurrence-sensitive contributions; aggregation is a later readout. -/
abbrev Contributions (Answer : Type uAnswer) (V : Type uValue) := List (Answer × V)

def sequence [Mul V] (answers : Contributions Answer V)
    (next : Answer → Contributions Other V) : Contributions Other V :=
  answers.flatMap fun first =>
    (next first.1).map fun second => (second.1, first.2 * second.2)

@[simp] theorem sequence_nil [Mul V] (next : Answer → Contributions Other V) :
    sequence [] next = [] := rfl

@[simp] theorem sequence_cons [Mul V] (first : Answer × V)
    (rest : Contributions Answer V) (next : Answer → Contributions Other V) :
    sequence (first :: rest) next =
      (next first.1).map (fun second => (second.1, first.2 * second.2)) ++
        sequence rest next := rfl

theorem sequence_append [Mul V] (left right : Contributions Answer V)
    (next : Answer → Contributions Other V) :
    sequence (left ++ right) next = sequence left next ++ sequence right next := by
  simp [sequence, List.flatMap_append]

/-- Erasure forgets coefficients but retains every authorized occurrence. -/
def eraseCoefficients (answers : Contributions Answer V) : List Answer := answers.map Prod.fst

theorem eraseCoefficients_sequence [Mul V] (answers : Contributions Answer V)
    (next : Answer → Contributions Other V) :
    eraseCoefficients (sequence answers next) =
      (eraseCoefficients answers).flatMap (fun answer => eraseCoefficients (next answer)) := by
  simp [eraseCoefficients, sequence, List.map_flatMap, List.flatMap_map, List.map_map,
    Function.comp_def]

@[simp] theorem sequence_return [Monoid V] (answer : Answer)
    (next : Answer → Contributions Other V) :
    sequence [(answer, 1)] next = next answer := by
  simp [sequence]

@[simp] theorem sequence_pure [Monoid V] (answers : Contributions Answer V) :
    sequence answers (fun answer => [(answer, 1)]) = answers := by
  simp [sequence]

/-- Reindex answers without identifying physical occurrences or coefficients. -/
theorem sequence_map [Monoid V] (answers : Contributions Answer V) (readout : Answer → Other) :
    sequence answers (fun answer => [(readout answer, 1)]) =
      answers.map (fun answer => (readout answer.1, answer.2)) := by
  induction answers with
  | nil => rfl
  | cons answer rest ih => simp [sequence_cons, ih]

theorem sequence_assoc [Semigroup V] {Final : Type*}
    (answers : Contributions Answer V) (first : Answer → Contributions Other V)
    (second : Other → Contributions Final V) :
    sequence (sequence answers first) second =
      sequence answers (fun answer => sequence (first answer) second) := by
  induction answers with
  | nil => rfl
  | cons head rest ih =>
      simp only [sequence_cons, sequence_append, ih]
      congr 1
      simp only [sequence, List.flatMap_map, List.map_flatMap, List.map_map]
      apply List.flatMap_congr
      intro item member
      apply List.map_congr_left
      intro final present
      simp only [Function.comp_apply, mul_assoc]

/-- The operation algebra for a response catalogue with authored coefficients. -/
def operationAlgebra [Mul V]
    (responses : (operation : Operation) → Contributions (Response operation) V)
    (operation : Operation) (next : Response operation → Contributions Answer V) :
    Contributions Answer V := sequence (responses operation) next

/-- Interpret returns and operations through the existing free fold. -/
def interpret [Monoid V]
    (responses : (operation : Operation) → Contributions (Response operation) V) :
    Computation Operation Response Answer → Contributions Answer V :=
  fold (fun answer => [(answer, 1)]) (operationAlgebra responses)

@[simp] theorem interpret_pure [Monoid V]
    (responses : (operation : Operation) → Contributions (Response operation) V)
    (answer : Answer) : interpret responses (pure answer) = [(answer, 1)] := rfl

@[simp] theorem interpret_perform [Monoid V]
    (responses : (operation : Operation) → Contributions (Response operation) V)
    (operation : Operation)
    (next : Response operation → Computation Operation Response Answer) :
    interpret responses (perform operation next) =
      sequence (responses operation) (fun response => interpret responses (next response)) := rfl

/-- Ordered coefficient multiplication is compatible with free sequencing. -/
theorem interpret_bind [Monoid V]
    (responses : (operation : Operation) → Contributions (Response operation) V)
    (computation : Computation Operation Response Answer)
    (next : Answer → Computation Operation Response Other) :
    interpret responses (bind computation next) =
      sequence (interpret responses computation) (fun answer => interpret responses (next answer)) := by
  induction computation with
  | mk shape continuation ih =>
      cases shape with
      | inl answer =>
          change interpret responses (next answer) =
            sequence [(answer, 1)] (fun result => interpret responses (next result))
          exact (sequence_return (V := V) answer
            (fun result => interpret responses (next result))).symm
      | inr operation =>
          change sequence (responses operation)
              (fun response => interpret responses (bind (continuation response) next)) =
            sequence (sequence (responses operation)
              (fun response => interpret responses (continuation response)))
              (fun answer => interpret responses (next answer))
          rw [sequence_assoc]
          exact congrArg (sequence (responses operation)) (funext ih)

theorem interpret_map [Monoid V]
    (responses : (operation : Operation) → Contributions (Response operation) V)
    (computation : Computation Operation Response Answer) (readout : Answer → Other) :
    interpret responses (bind computation (fun answer => pure (readout answer))) =
      (interpret responses computation).map (fun answer => (readout answer.1, answer.2)) := by
  rw [interpret_bind]
  simp only [interpret_pure]
  exact sequence_map _ _

/-- Resuming a cut substitutes its residual interpretations, in the same order. -/
theorem interpret_unfold_add [Monoid V] {State : Type*}
    (responses : (operation : Operation) → Contributions (Response operation) V)
    (observe : State → View Operation Response Answer State)
    (first second : Nat) (state : State) :
    interpret responses (unfold observe (first + second) state) =
      sequence (interpret responses (unfold observe first state))
        (fun leaf => interpret responses (resume observe second leaf)) := by
  rw [unfold_add, interpret_bind]

def mapCoefficients {W : Type*} (change : V → W)
    (answers : Contributions Answer V) : Contributions Answer W :=
  answers.map fun answer => (answer.1, change answer.2)

theorem mapCoefficients_sequence {W : Type*} [Mul V] [Mul W]
    (change : V → W) (multiplies : ∀ left right, change (left * right) = change left * change right)
    (answers : Contributions Answer V) (next : Answer → Contributions Other V) :
    mapCoefficients change (sequence answers next) =
      sequence (mapCoefficients change answers) (fun answer => mapCoefficients change (next answer)) := by
  simp only [mapCoefficients, sequence, List.map_flatMap, List.flatMap_map, List.map_map]
  apply List.flatMap_congr
  intro item member
  apply List.map_congr_left
  intro final present
  simp only [Function.comp_apply, multiplies]

/-- Change of coefficients is natural exactly when unit and multiplication
are preserved; additive readouts impose their own extra law. -/
theorem interpret_mapCoefficients {W : Type*} [Monoid V] [Monoid W]
    (change : V →* W)
    (responses : (operation : Operation) → Contributions (Response operation) V)
    (computation : Computation Operation Response Answer) :
    mapCoefficients change (interpret responses computation) =
      interpret (fun operation => mapCoefficients change (responses operation)) computation := by
  apply fold_fusion (onReturn := fun answer => [(answer, (1 : V))])
    (onOperation := operationAlgebra responses)
    (onTarget := operationAlgebra (fun operation => mapCoefficients change (responses operation)))
    (readout := mapCoefficients change) ?_ computation |>.trans ?_
  · intro operation next
    exact mapCoefficients_sequence change change.map_mul (responses operation) next
  · apply congrArg (fun returns => fold returns
        (operationAlgebra (fun operation => mapCoefficients change (responses operation))) computation)
    funext answer
    simp [mapCoefficients]

/-- The additive readout reuses the existing traversal aggregate. -/
def total [AddCommMonoid V] (answers : Contributions Answer V) : V :=
  SemiringTraversal.weightSum Prod.snd answers

theorem total_append [AddCommMonoid V] (left right : Contributions Answer V) :
    total (left ++ right) = total left + total right :=
  SemiringTraversal.weightSum_append _ _ _

theorem total_permutation [AddCommMonoid V] {left right : Contributions Answer V}
    (same : left.Perm right) : total left = total right :=
  SemiringTraversal.weightSum_perm _ same

/-- Additive readout commutes with an additive change of coefficients. This
extra law is independent of the multiplicative handler law. -/
theorem total_mapCoefficients {W : Type*} [AddCommMonoid V] [AddCommMonoid W]
    (change : V →+ W) (answers : Contributions Answer V) :
    total (mapCoefficients change answers) = change (total answers) := by
  induction answers with
  | nil => simp [total, mapCoefficients, SemiringTraversal.weightSum]
  | cons answer rest ih =>
      simpa [total, mapCoefficients, SemiringTraversal.weightSum, map_add] using
        congrArg (fun result => change answer.2 + result) ih

theorem total_scale_left [Semiring V] (coefficient : V)
    (answers : Contributions Answer V) :
    total (answers.map (fun answer => (answer.1, coefficient * answer.2))) =
      coefficient * total answers := by
  simp only [total, SemiringTraversal.weightSum, List.map_map, Function.comp_def]
  exact SemiringTraversal.weightSum_mul_left Prod.snd coefficient answers

/-- The aggregate of a sequential computation is the sum of its ordered
products. No commutativity of multiplication is used. -/
theorem total_sequence [Semiring V] (answers : Contributions Answer V)
    (next : Answer → Contributions Other V) :
    total (sequence answers next) =
      SemiringTraversal.weightSum (fun answer => answer.2 * total (next answer.1)) answers := by
  induction answers with
  | nil => rfl
  | cons answer rest ih =>
      rw [sequence_cons, total_append, total_scale_left, ih]
      rfl

end Mettapedia.GSLT.Dynamics.WeightedResumption
