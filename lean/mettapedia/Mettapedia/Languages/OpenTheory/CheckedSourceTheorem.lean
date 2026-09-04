import Mettapedia.Languages.OpenTheory.NominalProvenanceBoundary

/-!
# Checked source representatives for OpenTheory theorem state

The primitive replay layer uses alpha-canonical terms and finite hypothesis
sets.  Definition provenance additionally observes named source terms.  This
module relates the two views without replacing either one.

It first constructs source-backed sequents and theorems, then proves an exact
commuting square for constant-definition checking.  Type-operator definitions
and the remaining named primitive operations are later closure obligations.
-/

namespace Mettapedia.Languages.OpenTheory

namespace CheckedSourceTerm

/-- Canonicalization preserves the displayed type definitionally. -/
@[simp] theorem canonical_ty (term : CheckedSourceTerm) :
    term.canonical.ty = term.ty := rfl

/-- Checking the retained source of a checked term returns its canonical
projection. -/
@[simp] theorem source_check (term : CheckedSourceTerm) :
    term.source.check = some term.canonical := by
  rw [SourceTerm.check_eq_some_iff]
  rfl

/-- A checked source occurrence of a constant. -/
def ofConstant (constant : Const) (ty : Ty) : CheckedSourceTerm :=
  ⟨.const constant ty, ty, by simp [SourceTerm.inferType]⟩

/-- Retaining a named constant occurrence does not alter its canonical term. -/
@[simp] theorem ofConstant_canonical (constant : Const) (ty : Ty) :
    (ofConstant constant ty).canonical = CanonicalTerm.constant constant ty := by
  apply CanonicalTerm.ext_term
  simp [ofConstant, canonical, CanonicalTerm.constant]

/-- A checked named application when its function type is already known. -/
def applyFunction (function argument : CheckedSourceTerm) (codomain : Ty)
    (functionType :
      function.ty.destFunction? = some (argument.ty, codomain)) :
    CheckedSourceTerm :=
  ⟨.app function.source argument.source, codomain, by
    simp [SourceTerm.inferType, function.checked, argument.checked,
      functionType]⟩

/-- Named application commutes exactly with alpha-canonical projection. -/
theorem applyFunction_canonical
    (function argument : CheckedSourceTerm) (codomain : Ty)
    (functionType :
      function.ty.destFunction? = some (argument.ty, codomain)) :
    (applyFunction function argument codomain functionType).canonical =
      CanonicalTerm.applicationOfFunction function.canonical
        argument.canonical codomain functionType := by
  apply CanonicalTerm.ext_term
  simp [applyFunction, canonical, CanonicalTerm.applicationOfFunction]

/-- Primitive equality on retained named representatives. -/
def equalityOfSameType (left right : CheckedSourceTerm)
    (sameType : left.ty = right.ty) : CheckedSourceTerm :=
  ⟨.app
      (.app (.const Const.equality (Ty.equality left.ty)) left.source)
      right.source,
    Ty.bool,
    by
      have rightChecked : right.source.inferType = some left.ty := by
        simpa [sameType] using right.checked
      simp [SourceTerm.inferType, Ty.equality, Ty.function,
        TypeOp.function, Ty.destFunction?, left.checked, rightChecked]⟩

/-- Named equality commutes exactly with alpha-canonical projection. -/
theorem equalityOfSameType_canonical
    (left right : CheckedSourceTerm) (sameType : left.ty = right.ty) :
    (equalityOfSameType left right sameType).canonical =
      CanonicalTerm.equalityOfSameType left.canonical right.canonical
        sameType := by
  apply CanonicalTerm.ext_term
  simp [equalityOfSameType, canonical,
    CanonicalTerm.equalityOfSameType, CanonicalTerm.equalityDB]

end CheckedSourceTerm

/-- Named representatives of a sequent, with duplicate alpha classes rejected
before conversion to the canonical finite hypothesis set. -/
structure CheckedSourceSequent where
  hypotheses : List CheckedSourceTerm
  conclusion : CheckedSourceTerm
  hypothesesNodup : (hypotheses.map CheckedSourceTerm.canonical).Nodup

namespace CheckedSourceSequent

/-- Alpha-canonical projection of a checked source sequent. -/
def canonical (sequent : CheckedSourceSequent) : Sequent :=
  ⟨(sequent.hypotheses.map CheckedSourceTerm.canonical).toFinset,
    sequent.conclusion.canonical⟩

/-- A source sequent with no hypotheses. -/
def empty (conclusion : CheckedSourceTerm) : CheckedSourceSequent :=
  ⟨[], conclusion, by simp⟩

/-- The existing duplicate-rejecting ingress accepts exactly this retained
hypothesis list and returns its canonical projection. -/
theorem ingress (sequent : CheckedSourceSequent) :
    Sequent.ofObjectTerms?
        (sequent.hypotheses.map CheckedSourceTerm.canonical)
        sequent.conclusion.canonical =
      some sequent.canonical := by
  simp [Sequent.ofObjectTerms?, sequent.hypothesesNodup, canonical]

end CheckedSourceSequent

/-- A theorem's named current sequent together with its exact canonical theorem
state.  Axiom tags are already alpha-extensional in the canonical state. -/
structure CheckedSourceTheorem where
  sourceSequent : CheckedSourceSequent
  canonical : Theorem
  sequent_eq : canonical.sequent = sourceSequent.canonical

namespace CheckedSourceTheorem

/-- A source-backed theorem with empty axiom provenance and no hypotheses. -/
def emptyResult (conclusion : CheckedSourceTerm) : CheckedSourceTheorem :=
  { sourceSequent := .empty conclusion
    canonical := Theorem.emptyResult ∅ conclusion.canonical
    sequent_eq := rfl }

/-- A source-backed axiom result. -/
def axiomResult (sourceSequent : CheckedSourceSequent)
    (currentBool : sourceSequent.canonical.IsBool) : CheckedSourceTheorem :=
  { sourceSequent := sourceSequent
    canonical := Theorem.axiomResult sourceSequent.canonical currentBool
    sequent_eq := rfl }

/-- A source-backed binary result once the named output sequent has been
constructed by the selected rule. -/
def unionResult (left right : CheckedSourceTheorem)
    (sourceSequent : CheckedSourceSequent) : CheckedSourceTheorem :=
  { sourceSequent := sourceSequent
    canonical := Theorem.unionResult left.canonical right.canonical
      sourceSequent.canonical.hyp sourceSequent.canonical.concl
    sequent_eq := rfl }

end CheckedSourceTheorem

/-- The source-backed result of one constant definition. -/
structure CheckedConstantDefinitionResult where
  constant : Const
  definitionTheorem : CheckedSourceTheorem

namespace CheckedConstantDefinitionResult

/-- Forget named theorem representatives while retaining the exact canonical
definition result. -/
def canonical (result : CheckedConstantDefinitionResult) :
    ConstantDefinitionResult :=
  ⟨result.constant, result.definitionTheorem.canonical⟩

end CheckedConstantDefinitionResult

/-- Construct a source-backed constant definition from an already checked
source term. -/
def makeCheckedConstantDefinition (name : Name)
    (definition : CheckedSourceTerm) : CheckedConstantDefinitionResult :=
  let constant : Const := .mk name (.defined definition.source)
  let constantTerm := CheckedSourceTerm.ofConstant constant definition.ty
  let equality := CheckedSourceTerm.equalityOfSameType constantTerm definition rfl
  ⟨constant, CheckedSourceTheorem.emptyResult equality⟩

/-- The source-backed construction projects to the existing canonical
constant-definition construction exactly. -/
theorem makeCheckedConstantDefinition_canonical
    (name : Name) (definition : CheckedSourceTerm) :
    (makeCheckedConstantDefinition name definition).canonical =
      makeConstantDefinition name definition.source definition.canonical := by
  let constant : Const := .mk name (.defined definition.source)
  let constantTerm := CheckedSourceTerm.ofConstant constant definition.ty
  have equalityProjection :=
    CheckedSourceTerm.equalityOfSameType_canonical
      constantTerm definition rfl
  simpa [makeCheckedConstantDefinition,
    CheckedConstantDefinitionResult.canonical,
    CheckedSourceTheorem.emptyResult, CheckedSourceSequent.empty,
    makeConstantDefinition, constant, constantTerm] using
      congrArg
        (fun equality : CanonicalTerm =>
          (⟨constant, Theorem.emptyResult ∅ equality⟩ :
            ConstantDefinitionResult))
        equalityProjection

/-- Execute the constant-definition side conditions while retaining the named
source representative. -/
def checkCheckedConstantDefinition (name : Name)
    (definition : CheckedSourceTerm) :
    Option CheckedConstantDefinitionResult :=
  if definition.canonical.term.hasNoFreeVariables then
    if definition.canonical.term.typeVariables ⊆
        definition.canonical.ty.typeVariables then
      some (makeCheckedConstantDefinition name definition)
    else
      none
  else
    none

/-- Source-backed constant checking succeeds exactly on the independent pinned
side conditions. -/
theorem checkCheckedConstantDefinition_isSome_iff
    (name : Name) (definition : CheckedSourceTerm) :
    (checkCheckedConstantDefinition name definition).isSome = true ↔
      definition.canonical.term.HasNoFreeVariables ∧
        definition.canonical.term.typeVariables ⊆
          definition.canonical.ty.typeVariables := by
  change (checkCheckedConstantDefinition name definition).isSome = true ↔
    definition.canonical.term.HasNoFreeVariables ∧
      definition.canonical.term.typeVariables ⊆ definition.ty.typeVariables
  by_cases closed : definition.canonical.term.hasNoFreeVariables = true
  · by_cases typeVariables :
        definition.canonical.term.typeVariables ⊆
          definition.ty.typeVariables
    · simp [checkCheckedConstantDefinition, closed, typeVariables,
        (DBTerm.hasNoFreeVariables_eq_true_iff _).mp closed]
    · simp [checkCheckedConstantDefinition, closed, typeVariables]
  · have notClosed :
        ¬ definition.canonical.term.HasNoFreeVariables := by
      intro structurallyClosed
      exact closed
        ((DBTerm.hasNoFreeVariables_eq_true_iff _).mpr structurallyClosed)
    simp [checkCheckedConstantDefinition, closed, notClosed]

/-- Forgetting retained source evidence commutes with constant-definition
checking on every checked input. -/
theorem checkCheckedConstantDefinition_commutes
    (name : Name) (definition : CheckedSourceTerm) :
    (checkCheckedConstantDefinition name definition).map
        CheckedConstantDefinitionResult.canonical =
      checkConstantDefinition name definition.source := by
  unfold checkCheckedConstantDefinition checkConstantDefinition
  rw [CheckedSourceTerm.source_check]
  by_cases closed : definition.canonical.term.hasNoFreeVariables = true
  · by_cases typeVariables :
        definition.canonical.term.typeVariables ⊆
          definition.ty.typeVariables
    · simp [closed, typeVariables,
        makeCheckedConstantDefinition_canonical]
    · simp [closed, typeVariables]
  · simp [closed]

end Mettapedia.Languages.OpenTheory
