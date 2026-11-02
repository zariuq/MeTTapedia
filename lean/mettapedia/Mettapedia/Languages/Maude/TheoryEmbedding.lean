import Mettapedia.Languages.Maude.HookedEquivalence

/-! Inclusion of sorted declarations and authored equations. The embedding
transports the actual conditional derivation, including every premise, into
the enlarged imported theory. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude

theorem HasSort.of_operator_subset {first second : Signature}
    (included : ∀ declaration ∈ first.operators, declaration ∈ second.operators)
    {context : VariableContext} {source : Term} {sort : String}
    (typed : HasSort first context source sort) : HasSort second context source sort := by
  refine HasSort.rec
    (motive_1 := fun source sort _ => HasSort second context source sort)
    (motive_2 := fun sources sorts _ => List.Forall₂ (HasSort second context) sources sorts)
    ?_ ?_ ?_ ?_ typed
  · intro _ _ found
    exact .var found
  · intro declaration _ member _ ih
    exact .app (included declaration member) ih
  · exact .nil
  · intro _ _ _ _ _ _ firstIH restIH
    exact .cons firstIH restIH

def ArgumentContext.mapSignature {first second : Signature}
    (included : ∀ declaration ∈ first.operators, declaration ∈ second.operators)
    {context : VariableContext} {hole result : String}
    (frame : ArgumentContext first context hole result) : ArgumentContext second context hole result where
  declaration := frame.declaration
  declared := included _ frame.declared
  beforeSorts := frame.beforeSorts
  afterSorts := frame.afterSorts
  before := frame.before
  after := frame.after
  argumentSorts := frame.argumentSorts
  resultSort := frame.resultSort
  beforeTyped := frame.beforeTyped.imp (fun _ _ typed => typed.of_operator_subset included)
  afterTyped := frame.afterTyped.imp (fun _ _ typed => typed.of_operator_subset included)

theorem AlgebraStep.mapSignature {first second : Signature}
    (included : ∀ declaration ∈ first.operators, declaration ∈ second.operators)
    {context : VariableContext} {sort : String} {source target : Term}
    (step : AlgebraStep first context sort source target) : AlgebraStep second context sort source target := by
  refine ⟨?_, step.source_sorted.of_operator_subset included, step.target_sorted.of_operator_subset included⟩
  cases step.schema with
  | associative member active => exact .associative (included _ member) active
  | commutative member active => exact .commutative (included _ member) active
  | leftUnit member active => exact .leftUnit (included _ member) active
  | rightUnit member active => exact .rightUnit (included _ member) active

structure TheoryEmbedding (source target : Theory) : Prop where
  operators : ∀ declaration ∈ source.signature.operators, declaration ∈ target.signature.operators
  equations : ∀ row ∈ source.equations, row ∈ target.equations
  checked : ∀ row ∈ source.equations, row.check source.signature = true → row.check target.signature = true

theorem TheoryEmbedding.equivalent {first second : Theory} (embedding : TheoryEmbedding first second)
    {context : VariableContext} {sort : String} {source target : Term}
    (equivalent : Equivalent first context sort source target) (hook : EquationHook) :
    HookedEquivalent second hook context sort source target := by
  refine Equivalent.rec
    (motive_1 := fun sort source target _ => HookedEquivalent second hook context sort source target)
    (motive_2 := fun assignment conditions _ => HookedConditions second hook context assignment conditions)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ equivalent
  · intro _ _ typed
    exact .refl (typed.of_operator_subset embedding.operators)
  · intro _ _ _ _ ih
    exact .symm ih
  · intro _ _ _ _ _ _ firstIH lastIH
    exact .trans firstIH lastIH
  · intro _ _ frame _ _ _ ih
    exact .argument (frame.mapSignature embedding.operators) ih
  · intro _ _ _ step
    exact .algebra (step.mapSignature embedding.operators)
  · intro row _ replacement member checked left right typed _ conditions
    exact .equation replacement (embedding.equations row member) (embedding.checked row member checked)
      (left.of_operator_subset embedding.operators) (right.of_operator_subset embedding.operators)
      (fun name sort found => (typed name sort found).of_operator_subset embedding.operators) conditions
  · intro assignment
    exact .nil assignment
  · intro _ _ _ _ _ _ firstIH lastIH
    exact .cons firstIH lastIH

theorem TheoryEmbedding.ordinary {first second : Theory} (embedding : TheoryEmbedding first second)
    {context : VariableContext} {sort : String} {source target : Term}
    (equivalent : Equivalent first context sort source target) : Equivalent second context sort source target :=
  (embedding.equivalent equivalent (fun _ _ _ _ => False)).toOrdinary

end Mettapedia.Languages.Maude
