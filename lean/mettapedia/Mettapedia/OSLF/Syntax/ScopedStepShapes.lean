import Mettapedia.OSLF.Syntax.ScopedStepConstructorFrame

/-!
# Scoped rule shapes separated from recursive evidence

The shape of an admissible authored step records the two endpoints and the
matching assignment but does not contain an oracle result or a recursive
proof. Filling that shape with a selected oracle occurrence is a separate
operation. This separation is required before building a fixed polynomial
whose recursive positions can be interpreted in different rule algebras.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedStepShapes

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.Binding.ScopedStepConstructorFrame

/-- An admissible recursive premise independently of the algebra that will
provide evidence for its child judgment. The child's context is the exact
premise-local binder extension of the caller's ambient context. -/
structure StepShape (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient index localDepth : Nat) (source target : Pattern)
    (initial final : Assignment) where
  childSource : Pattern
  childTarget : Pattern
  instantiated : instantiateAt? rule spec ambient (.premise index 0 0)
    [] localDepth initial source = some childSource
  sourceScoped : childSource.isWellScopedAt (localDepth + ambient) = true
  targetScoped : childTarget.isWellScopedAt (localDepth + ambient) = true
  matched : final ∈ matchAt rule spec ambient (.premise index 0 1)
    [] localDepth initial target childTarget

/-- The recursive judgment requested by a shape is independent of any
particular witness or oracle enumeration. -/
def StepShape.childJudgment {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient index localDepth : Nat} {source target : Pattern}
    {initial final : Assignment}
    (shape : StepShape rule spec ambient index localDepth
      source target initial final) : Nat × Pattern × Pattern :=
  (localDepth + ambient, shape.childSource, shape.childTarget)

/-- Filling a fixed shape selects a particular occurrence of a recursive
result. Equal endpoints at different ordinals remain different selections. -/
structure StepSelection {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient index localDepth : Nat} {source target : Pattern}
    {initial final : Assignment} {Evidence : Type}
    (oracle : StepOracle Evidence)
    (shape : StepShape rule spec ambient index localDepth
      source target initial final) where
  evidence : Evidence
  ordinal : Nat
  selected : ((evidence, shape.childTarget), ordinal) ∈
    (oracle (localDepth + ambient) shape.childSource).zipIdx

/-- Forget recursive evidence while retaining the admitted rule shape and
its exact child context. -/
def shapeOfAdmitted {Evidence : Type}
    {oracle : StepOracle Evidence} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient index localDepth : Nat}
    {source target : Pattern} {initial final : Assignment}
    {event : PremiseEvent Evidence} {child : ChildRequest Evidence}
    (admitted : AdmittedChild oracle rule spec ambient index localDepth
      source target initial final event child) :
    StepShape rule spec ambient index localDepth
      source target initial final := by
  rcases child with ⟨childAmbient, childSource, childTarget,
    ordinal, evidence⟩
  rcases admitted with ⟨context, instantiated, sourceScoped,
    _, targetScoped, matched, _⟩
  dsimp at context instantiated sourceScoped targetScoped matched
  subst childAmbient
  exact ⟨childSource, childTarget, instantiated,
    sourceScoped, targetScoped, matched⟩

/-- The executable scoped step is exactly an oracle-independent admissible
shape filled by one selected recursive result. -/
theorem mem_stepResults_iff_shape_selection {Evidence : Type}
    (oracle : StepOracle Evidence) (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient index localDepth : Nat)
    (source target : Pattern) (initial final : Assignment)
    (event : PremiseEvent Evidence) :
    (event, final) ∈ stepResults oracle rule spec ambient index localDepth
      source target initial ↔
      ∃ (shape : StepShape rule spec ambient index localDepth
          source target initial final)
        (selection : StepSelection oracle shape),
        event = .step index selection.ordinal selection.evidence := by
  constructor
  · intro result
    obtain ⟨child, valid⟩ :=
      (mem_stepResults_iff oracle rule spec ambient index localDepth
        source target initial final event).mp result
    rcases child with ⟨childAmbient, childSource, childTarget,
      ordinal, evidence⟩
    rcases valid with ⟨context, instantiated, sourceScoped,
      selected, targetScoped, matched, eventEq⟩
    dsimp at context instantiated sourceScoped selected targetScoped matched eventEq
    subst childAmbient
    let shape : StepShape rule spec ambient index localDepth
        source target initial final :=
      ⟨childSource, childTarget, instantiated,
        sourceScoped, targetScoped, matched⟩
    exact ⟨shape, ⟨evidence, ordinal, selected⟩, eventEq⟩
  · rintro ⟨shape, selection, eventEq⟩
    rcases selection with ⟨evidence, ordinal, selected⟩
    let child : ChildRequest Evidence :=
      ⟨localDepth + ambient, shape.childSource, shape.childTarget,
        ordinal, evidence⟩
    exact (mem_stepResults_iff oracle rule spec ambient index localDepth
      source target initial final event).mpr
        ⟨child, rfl, shape.instantiated, shape.sourceScoped,
          selected, shape.targetScoped, shape.matched, eventEq⟩

/-- An admissible shape can be filled by two distinct occurrences with the
same evidence and endpoint. Forgetting the selected ordinal therefore cannot
serve as a proof that execution histories are identified. -/
theorem duplicate_selections_distinct {Evidence : Type}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient index localDepth : Nat} {source target : Pattern}
    {initial final : Assignment}
    (shape : StepShape rule spec ambient index localDepth
      source target initial final) (evidence : Evidence) :
    ∃ (oracle : StepOracle Evidence)
      (first second : StepSelection oracle shape),
      first.ordinal = 0 ∧ second.ordinal = 1 ∧ first ≠ second := by
  let oracle : StepOracle Evidence :=
    fun _ _ => [(evidence, shape.childTarget),
      (evidence, shape.childTarget)]
  have firstSelected : ((evidence, shape.childTarget), 0) ∈
      (oracle (localDepth + ambient) shape.childSource).zipIdx := by
    simp [oracle, List.zipIdx]
  have secondSelected : ((evidence, shape.childTarget), 1) ∈
      (oracle (localDepth + ambient) shape.childSource).zipIdx := by
    simp [oracle, List.zipIdx]
  let first : StepSelection oracle shape :=
    ⟨evidence, 0, firstSelected⟩
  let second : StepSelection oracle shape :=
    ⟨evidence, 1, secondSelected⟩
  refine ⟨oracle, first, second, rfl, rfl, ?_⟩
  intro equal
  have ordinalEq := congrArg StepSelection.ordinal equal
  have contradiction : (0 : Nat) = 1 := ordinalEq
  exact Nat.zero_ne_one contradiction

end Mettapedia.OSLF.Binding.ScopedStepShapes
