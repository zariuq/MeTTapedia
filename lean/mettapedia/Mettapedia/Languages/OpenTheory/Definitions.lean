import Mettapedia.Languages.OpenTheory.Binding
import Mettapedia.Languages.OpenTheory.CoreRules

/-!
# OpenTheory definitional extensions

This module formalizes the constant-definition and type-operator-definition
boundary of OpenTheory revision
`f555adbf6f3ca52ef6a9c5ca35d0316e53a289c1`.

Definitions are deliberately not classified as primitive theorem inferences.
They introduce provenance-bearing symbols after checking syntactic side
conditions and produce the corresponding definitional theorems.  The theorems
below establish exact admission and provenance properties.  They do not call
this operation conservative: semantic model extension or syntactic elimination
is a separate theorem obligation.
-/

namespace Mettapedia.Languages.OpenTheory

/-! ## Type-variable support -/

namespace Ty

mutual
  /-- The type-variable names occurring in an OpenTheory type. -/
  def typeVariables : Ty → Finset Name
    | .var name => {name}
    | .op _ arguments => typeVariablesList arguments

  /-- Type-variable support of a list of OpenTheory types. -/
  def typeVariablesList : List Ty → Finset Name
    | [] => ∅
    | ty :: tys => typeVariables ty ∪ typeVariablesList tys
end

end Ty

namespace DBTerm

/-- Type-variable names in the displayed type annotations of a canonical term.
Symbol provenance is opaque, matching `Term.typeVars` in the pinned source. -/
def typeVariables : DBTerm → Finset Name
  | .const _ ty => ty.typeVariables
  | .free sourceVar => sourceVar.ty.typeVariables
  | .bound _ => ∅
  | .app function argument =>
      typeVariables function ∪ typeVariables argument
  | .abs domain body => domain.typeVariables ∪ typeVariables body
termination_by term => sizeOf term

/-- Structural absence of free term variables. -/
inductive HasNoFreeVariables : DBTerm → Prop where
  | const : HasNoFreeVariables (.const constant ty)
  | bound : HasNoFreeVariables (.bound index)
  | app : HasNoFreeVariables function → HasNoFreeVariables argument →
      HasNoFreeVariables (.app function argument)
  | abs : HasNoFreeVariables body → HasNoFreeVariables (.abs domain body)

/-- Executable recognition of terms with no free term variables. -/
def hasNoFreeVariables : DBTerm → Bool
  | .const _ _ => true
  | .free _ => false
  | .bound _ => true
  | .app function argument =>
      hasNoFreeVariables function && hasNoFreeVariables argument
  | .abs _ body => hasNoFreeVariables body
termination_by term => sizeOf term

/-- Executable closedness is exactly structural absence of free variables. -/
@[simp] theorem hasNoFreeVariables_eq_true_iff (term : DBTerm) :
    term.hasNoFreeVariables = true ↔ term.HasNoFreeVariables := by
  induction term with
  | const constant ty =>
      simp [hasNoFreeVariables, HasNoFreeVariables.const]
  | free sourceVar =>
      constructor
      · simp [hasNoFreeVariables]
      · intro impossible
        cases impossible
  | bound index =>
      simp [hasNoFreeVariables, HasNoFreeVariables.bound]
  | app function argument functionIH argumentIH =>
      constructor
      · intro accepted
        rw [hasNoFreeVariables, Bool.and_eq_true, functionIH, argumentIH]
          at accepted
        exact .app accepted.1 accepted.2
      · intro closed
        cases closed with
        | app functionClosed argumentClosed =>
            simp [hasNoFreeVariables, functionIH, argumentIH,
              functionClosed, argumentClosed]
  | abs domain body bodyIH =>
      constructor
      · intro accepted
        simp only [hasNoFreeVariables, bodyIH] at accepted
        exact .abs accepted
      · intro closed
        cases closed with
        | abs bodyClosed => simpa [hasNoFreeVariables, bodyIH]

end DBTerm

namespace CanonicalTerm

/-- A checked occurrence of a constant at one displayed type. -/
def constant (constant : Const) (ty : Ty) : CanonicalTerm :=
  ⟨.const constant ty, ty, by simp [DBTerm.inferType]⟩

/-- A checked occurrence of one exact typed free variable. -/
def free (sourceVar : SourceVar) : CanonicalTerm :=
  ⟨.free sourceVar, sourceVar.ty, by simp [DBTerm.inferType]⟩

/-- Typed application when the function-space decomposition is already
known. -/
def applicationOfFunction (function argument : CanonicalTerm)
    (codomain : Ty)
    (functionType :
      function.ty.destFunction? = some (argument.ty, codomain)) :
    CanonicalTerm :=
  ⟨.app function.term argument.term, codomain, by
    simp [DBTerm.inferType, function.checked, argument.checked, functionType]⟩

/-- The total application constructor has the independent application graph. -/
theorem applicationOfFunction_semantics
    (function argument : CanonicalTerm) (codomain : Ty)
    (functionType :
      function.ty.destFunction? = some (argument.ty, codomain)) :
    ApplicationSemantics function argument
      (applicationOfFunction function argument codomain functionType) := by
  exact ⟨argument.ty, codomain, functionType, rfl, rfl⟩

/-- Decompose a canonical application and recheck both immediate subterms. -/
def destApplication? (whole : CanonicalTerm) :
    Option (CanonicalTerm × CanonicalTerm) :=
  match whole.term with
  | .app function argument => do
      let checkedFunction ← ofDB? function
      let checkedArgument ← ofDB? argument
      pure (checkedFunction, checkedArgument)
  | _ => none

/-- Canonical application decomposition is exact. -/
theorem destApplication?_eq_some_iff
    (whole function argument : CanonicalTerm) :
    whole.destApplication? = some (function, argument) ↔
      ApplicationSemantics function argument whole := by
  constructor
  · intro accepted
    unfold destApplication? at accepted
    cases shape : whole.term with
    | const constant ty => simp [shape] at accepted
    | free sourceVar => simp [shape] at accepted
    | bound index => simp [shape] at accepted
    | abs domain body => simp [shape] at accepted
    | app functionDB argumentDB =>
        simp only [shape] at accepted
        cases functionCheck : ofDB? functionDB with
        | none => simp [functionCheck] at accepted
        | some checkedFunction =>
            cases argumentCheck : ofDB? argumentDB with
            | none => simp [functionCheck, argumentCheck] at accepted
            | some checkedArgument =>
                simp [functionCheck, argumentCheck] at accepted
                rcases accepted with ⟨functionEq, argumentEq⟩
                subst checkedFunction
                subst checkedArgument
                have functionTerm :=
                  (ofDB?_eq_some_iff functionDB function).mp functionCheck
                have argumentTerm :=
                  (ofDB?_eq_some_iff argumentDB argument).mp argumentCheck
                have wholeChecked := whole.checked
                rw [shape, ← functionTerm, ← argumentTerm] at wholeChecked
                simp only [DBTerm.inferType, function.checked,
                  argument.checked] at wholeChecked
                cases functionShape : function.ty.destFunction? with
                | none => simp [functionShape] at wholeChecked
                | some pair =>
                    rcases pair with ⟨domain, codomain⟩
                    by_cases sameDomain : Ty.same domain argument.ty = true
                    · simp [functionShape, sameDomain] at wholeChecked
                      refine ⟨domain, codomain, functionShape,
                        (Ty.same_eq_true_iff domain argument.ty).mp sameDomain,
                        ?_⟩
                      simp [shape, functionTerm, argumentTerm]
                    · simp [functionShape, sameDomain] at wholeChecked
  · rintro ⟨domain, codomain, functionType, domainEq, shape⟩
    unfold destApplication?
    rw [shape]
    simp [ofDB?_term]

/-- The codomain displayed by an application view is the result's canonical
type. -/
theorem ApplicationSemantics.functionType
    {function argument result : CanonicalTerm}
    (application : ApplicationSemantics function argument result) :
    function.ty.destFunction? = some (argument.ty, result.ty) := by
  have accepted :=
    (apply?_eq_some_iff function argument result).mpr application
  unfold apply? at accepted
  split at accepted
  · rename_i domain codomain functionType
    split at accepted
    · rename_i sameDomain
      have resultEq := Option.some.inj accepted
      have domainEq : domain = argument.ty :=
        (Ty.same_eq_true_iff domain argument.ty).mp sameDomain
      have codomainEq : codomain = result.ty := by
        exact congrArg CanonicalTerm.ty resultEq
      simpa [domainEq, codomainEq] using functionType
    · contradiction
  · contradiction

/-- Primitive equality for two already checked terms with propositionally
equal types. -/
def equalityOfSameType (left right : CanonicalTerm)
    (sameType : left.ty = right.ty) : CanonicalTerm :=
  ⟨equalityDB left.ty left.term right.term, Ty.bool, by
    have rightChecked : right.term.inferType [] = some left.ty := by
      simpa [sameType] using right.checked
    simp [equalityDB, Ty.equality, Ty.function, TypeOp.function,
      Ty.destFunction?, DBTerm.inferType, left.checked, rightChecked]⟩

/-- The total same-type constructor has the independent equality graph. -/
theorem equalityOfSameType_semantics
    (left right : CanonicalTerm) (sameType : left.ty = right.ty) :
    EqualityConstructionSemantics left right
      (equalityOfSameType left right sameType) := by
  exact ⟨sameType, rfl⟩

end CanonicalTerm

/-- Checking named syntax yields a chosen canonical term exactly when erasing
binder names gives that term's de Bruijn tree.  The displayed type is then
forced by the canonical term's checkedness proof. -/
theorem SourceTerm.check_eq_some_iff
    (source : SourceTerm) (canonical : CanonicalTerm) :
    source.check = some canonical ↔ source.toDB [] = canonical.term := by
  constructor
  · intro accepted
    change
      (match checked : (source.toDB []).inferType [] with
      | some ty => some ⟨source.toDB [], ty, checked⟩
      | none => none) = some canonical at accepted
    split at accepted
    · exact congrArg CanonicalTerm.term (Option.some.inj accepted)
    · contradiction
  · intro shape
    change
      (match checked : (source.toDB []).inferType [] with
      | some ty => some ⟨source.toDB [], ty, checked⟩
      | none => none) = some canonical
    rw [shape]
    split
    · rename_i inferred checked
      have typeEquality : inferred = canonical.ty :=
        Option.some.inj (checked.symm.trans canonical.checked)
      subst inferred
      apply congrArg some
      apply CanonicalTerm.ext_term
      rfl
    · rename_i rejected
      have impossible := rejected.symm.trans canonical.checked
      contradiction

/-! ## Constant definitions -/

/-- The symbol and theorem produced by one admitted constant definition. -/
structure ConstantDefinitionResult where
  constant : Const
  definitionTheorem : Theorem

/-- Independent side conditions for a constant definition. -/
def ConstantDefinitionAdmissible (sourceDefinition : SourceTerm) : Prop :=
  ∃ definition : CanonicalTerm,
    sourceDefinition.check = some definition ∧
      definition.term.HasNoFreeVariables ∧
      definition.term.typeVariables ⊆ definition.ty.typeVariables

/-- Construct the exact provenance-bearing symbol and definitional theorem
once the checked source term is known. -/
def makeConstantDefinition (name : Name) (sourceDefinition : SourceTerm)
    (definition : CanonicalTerm) : ConstantDefinitionResult :=
  let constant : Const := .mk name (.defined sourceDefinition)
  let constantTerm := CanonicalTerm.constant constant definition.ty
  let equality :=
    CanonicalTerm.equalityOfSameType constantTerm definition rfl
  ⟨constant, Theorem.emptyResult ∅ equality⟩

/-- Execute the constant-definition side conditions and construct its result. -/
def checkConstantDefinition (name : Name)
    (sourceDefinition : SourceTerm) : Option ConstantDefinitionResult :=
  match sourceDefinition.check with
  | none => none
  | some definition =>
      if definition.term.hasNoFreeVariables then
        if definition.term.typeVariables ⊆ definition.ty.typeVariables then
          some (makeConstantDefinition name sourceDefinition definition)
        else
          none
      else
        none

/-- The executable constant-definition gate succeeds exactly on the source
side conditions of the pinned kernel. -/
theorem checkConstantDefinition_isSome_iff
    (name : Name) (sourceDefinition : SourceTerm) :
    (checkConstantDefinition name sourceDefinition).isSome = true ↔
      ConstantDefinitionAdmissible sourceDefinition := by
  cases sourceCheck : sourceDefinition.check with
  | none =>
      constructor
      · simp [checkConstantDefinition, sourceCheck]
      · rintro ⟨candidate, checked, _, _⟩
        rw [sourceCheck] at checked
        contradiction
  | some definition =>
      by_cases closed : definition.term.hasNoFreeVariables = true
      · by_cases typeVariables :
            definition.term.typeVariables ⊆ definition.ty.typeVariables
        · constructor
          · intro _
            exact ⟨definition, sourceCheck,
              (DBTerm.hasNoFreeVariables_eq_true_iff definition.term).mp closed,
              typeVariables⟩
          · intro _
            simp [checkConstantDefinition, sourceCheck, closed, typeVariables]
        · constructor
          · intro impossible
            simp [checkConstantDefinition, sourceCheck, closed, typeVariables]
              at impossible
          · rintro ⟨candidate, checked, _, candidateTypeVariables⟩
            have candidateEq : candidate = definition :=
              Option.some.inj (checked.symm.trans sourceCheck)
            subst candidate
            exact False.elim (typeVariables candidateTypeVariables)
      · constructor
        · intro impossible
          simp [checkConstantDefinition, sourceCheck, closed] at impossible
        · rintro ⟨candidate, checked, candidateClosed, _⟩
          have candidateEq : candidate = definition :=
            Option.some.inj (checked.symm.trans sourceCheck)
          subst candidate
          exact False.elim
            (closed
              ((DBTerm.hasNoFreeVariables_eq_true_iff definition.term).mpr
                candidateClosed))

/-- Every accepted constant definition has the exact symbol provenance and an
axiom-free, hypothesis-free equality theorem. -/
theorem checkConstantDefinition_result
    {name : Name} {sourceDefinition : SourceTerm}
    {result : ConstantDefinitionResult}
    (accepted : checkConstantDefinition name sourceDefinition = some result) :
    ∃ definition equality,
      sourceDefinition.check = some definition ∧
      definition.term.HasNoFreeVariables ∧
      definition.term.typeVariables ⊆ definition.ty.typeVariables ∧
      result.constant = .mk name (.defined sourceDefinition) ∧
      CanonicalTerm.EqualityConstructionSemantics
        (CanonicalTerm.constant result.constant definition.ty)
        definition equality ∧
      HasParts result.definitionTheorem ∅ ∅ equality := by
  unfold checkConstantDefinition at accepted
  split at accepted
  · contradiction
  · rename_i definition sourceCheck
    split at accepted
    · rename_i closed
      split at accepted
      · rename_i typeVariables
        have resultEq := Option.some.inj accepted
        subst result
        simp only [makeConstantDefinition]
        refine ⟨definition,
          CanonicalTerm.equalityOfSameType
            (CanonicalTerm.constant
              (.mk name (.defined sourceDefinition)) definition.ty)
            definition rfl,
          sourceCheck,
          (DBTerm.hasNoFreeVariables_eq_true_iff definition.term).mp closed,
          typeVariables, True.intro, ?_, ?_⟩
        · let constantTerm :=
            CanonicalTerm.constant
              (.mk name (.defined sourceDefinition)) definition.ty
          have sameType : constantTerm.ty = definition.ty := rfl
          exact CanonicalTerm.equalityOfSameType_semantics
            constantTerm definition sameType
        · exact ⟨rfl, rfl, rfl⟩
      · contradiction
    · contradiction

/-- Constant definitions add no primitive axiom provenance. -/
theorem checkConstantDefinition_axioms_empty
    {name : Name} {sourceDefinition : SourceTerm}
    {result : ConstantDefinitionResult}
    (accepted : checkConstantDefinition name sourceDefinition = some result) :
    result.definitionTheorem.axioms = ∅ := by
  obtain ⟨_, _, _, _, _, _, _, parts⟩ :=
    checkConstantDefinition_result accepted
  exact parts.1

/-! ## Type-operator definitions -/

/-- All source data needed by one OpenTheory type-operator definition.  The
nominal predicate is retained separately because canonical theorem state has
erased binder names, while symbol provenance has not. -/
structure TypeOperatorDefinitionRequest where
  typeName : Name
  abstractionName : Name
  representationName : Name
  typeVariables : List Name
  predicateSource : SourceTerm
  existence : Theorem

/-- The new type operator, its two representation constants, and the two
definitional theorems returned by `defineTypeOp`. -/
structure TypeOperatorDefinitionResult where
  typeOperator : TypeOp
  abstractionConstant : Const
  representationConstant : Const
  abstractionRepresentationTheorem : Theorem
  representationAbstractionTheorem : Theorem

/-- Independent admission conditions for the pinned type-definition rule. -/
def TypeOperatorDefinitionAdmissible
    (request : TypeOperatorDefinitionRequest) : Prop :=
  ∃ predicate witness,
    CanonicalTerm.ApplicationSemantics predicate witness
        request.existence.sequent.concl ∧
      request.predicateSource.check = some predicate ∧
      request.existence.sequent.hyp = ∅ ∧
      request.existence.sequent.concl.IsBool ∧
      predicate.term.HasNoFreeVariables ∧
      request.typeVariables.Nodup ∧
      request.typeVariables.toFinset = predicate.term.typeVariables

/-- Construct the exact outputs after the application view and Boolean result
type have been established.  The remaining admission conditions restrict when
this construction may be invoked but do not affect its output. -/
def makeTypeOperatorDefinition
    (request : TypeOperatorDefinitionRequest)
    (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness
      request.existence.sequent.concl)
    (conclusionBool : request.existence.sequent.concl.IsBool) :
    TypeOperatorDefinitionResult :=
  let typeOperator : TypeOp :=
    .mk request.typeName
      (.defined request.predicateSource request.typeVariables)
  let abstractType : Ty :=
    .op typeOperator (request.typeVariables.map Ty.var)
  let representationType := witness.ty
  let abstractionConstant : Const :=
    .mk request.abstractionName (.abstraction typeOperator)
  let representationConstant : Const :=
    .mk request.representationName (.representation typeOperator)
  let abstractionTerm :=
    CanonicalTerm.constant abstractionConstant
      (.function representationType abstractType)
  let representationTerm :=
    CanonicalTerm.constant representationConstant
      (.function abstractType representationType)
  have predicateType :
      predicate.ty.destFunction? = some (representationType, Ty.bool) := by
    have functionType := application.functionType
    rw [conclusionBool] at functionType
    exact functionType
  let abstractVariable : SourceVar :=
    ⟨Name.global "a", abstractType⟩
  let abstractVariableTerm := CanonicalTerm.free abstractVariable
  let representedAbstract :=
    CanonicalTerm.applicationOfFunction representationTerm
      abstractVariableTerm representationType
      (Ty.destFunction?_function abstractType representationType)
  let abstractedRepresentation :=
    CanonicalTerm.applicationOfFunction abstractionTerm
      representedAbstract abstractType
      (Ty.destFunction?_function representationType abstractType)
  let abstractionRepresentationLeft :=
    abstractedRepresentation.abstractFree abstractVariable
  let abstractionRepresentationRight :=
    abstractVariableTerm.abstractFree abstractVariable
  let abstractionRepresentationEquality :=
    CanonicalTerm.equalityOfSameType abstractionRepresentationLeft
      abstractionRepresentationRight rfl
  let abstractionRepresentationTheorem : Theorem :=
    { axioms := request.existence.axioms
      axiomsBoolean := request.existence.axiomsBoolean
      sequent :=
        ⟨request.existence.sequent.hyp,
          abstractionRepresentationEquality⟩ }
  let representationVariable : SourceVar :=
    ⟨Name.global "r", representationType⟩
  let representationVariableTerm := CanonicalTerm.free representationVariable
  let abstractedRepresentationVariable :=
    CanonicalTerm.applicationOfFunction abstractionTerm
      representationVariableTerm abstractType
      (Ty.destFunction?_function representationType abstractType)
  let representedAbstraction :=
    CanonicalTerm.applicationOfFunction representationTerm
      abstractedRepresentationVariable representationType
      (Ty.destFunction?_function abstractType representationType)
  let representationRoundTripEquality :=
    CanonicalTerm.equalityOfSameType representedAbstraction
      representationVariableTerm rfl
  let representationAbstractionLeft :=
    representationRoundTripEquality.abstractFree representationVariable
  let predicateApplication :=
    CanonicalTerm.applicationOfFunction predicate representationVariableTerm
      Ty.bool predicateType
  let representationAbstractionRight :=
    predicateApplication.abstractFree representationVariable
  let representationAbstractionEquality :=
    CanonicalTerm.equalityOfSameType representationAbstractionLeft
      representationAbstractionRight rfl
  let representationAbstractionTheorem : Theorem :=
    { axioms := request.existence.axioms
      axiomsBoolean := request.existence.axiomsBoolean
      sequent :=
        ⟨request.existence.sequent.hyp,
          representationAbstractionEquality⟩ }
  { typeOperator := typeOperator
    abstractionConstant := abstractionConstant
    representationConstant := representationConstant
    abstractionRepresentationTheorem :=
      abstractionRepresentationTheorem
    representationAbstractionTheorem := representationAbstractionTheorem }

/-- The construction uses exact OpenTheory provenance constructors and
preserves the existence theorem's complete axiom provenance. -/
theorem makeTypeOperatorDefinition_provenance
    (request : TypeOperatorDefinitionRequest)
    (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness
      request.existence.sequent.concl)
    (conclusionBool : request.existence.sequent.concl.IsBool) :
    let result := makeTypeOperatorDefinition request predicate witness
      application conclusionBool
    result.typeOperator =
        .mk request.typeName
          (.defined request.predicateSource request.typeVariables) ∧
      result.abstractionConstant =
        .mk request.abstractionName (.abstraction result.typeOperator) ∧
      result.representationConstant =
        .mk request.representationName (.representation result.typeOperator) ∧
      result.abstractionRepresentationTheorem.axioms =
        request.existence.axioms ∧
      result.representationAbstractionTheorem.axioms =
        request.existence.axioms := by
  simp [makeTypeOperatorDefinition]

/-- Both type-definition theorems retain the exact hypothesis set of the
existence theorem; admitted requests therefore make both empty. -/
theorem makeTypeOperatorDefinition_hypotheses
    (request : TypeOperatorDefinitionRequest)
    (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness
      request.existence.sequent.concl)
    (conclusionBool : request.existence.sequent.concl.IsBool) :
    let result := makeTypeOperatorDefinition request predicate witness
      application conclusionBool
    result.abstractionRepresentationTheorem.sequent.hyp =
        request.existence.sequent.hyp ∧
      result.representationAbstractionTheorem.sequent.hyp =
        request.existence.sequent.hyp := by
  simp [makeTypeOperatorDefinition]

/-- Check all non-application side conditions once the existence conclusion
has been decomposed. -/
def checkTypeOperatorDefinitionFromApplication
    (request : TypeOperatorDefinitionRequest)
    (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness
      request.existence.sequent.concl) : Option TypeOperatorDefinitionResult :=
  if _sourceChecked : request.predicateSource.check = some predicate then
    if _hypothesesEmpty : request.existence.sequent.hyp = ∅ then
      if conclusionBool : request.existence.sequent.concl.isBoolB = true then
        if predicate.term.hasNoFreeVariables then
          if request.typeVariables.Nodup then
            if request.typeVariables.toFinset = predicate.term.typeVariables then
              some (makeTypeOperatorDefinition request predicate witness
                application
                ((CanonicalTerm.isBoolB_eq_true_iff _).mp conclusionBool))
            else
              none
          else
            none
        else
          none
      else
        none
    else
      none
  else
    none

/-- The post-decomposition checker is exact for all remaining source side
conditions. -/
theorem checkTypeOperatorDefinitionFromApplication_isSome_iff
    (request : TypeOperatorDefinitionRequest)
    (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness
      request.existence.sequent.concl) :
    (checkTypeOperatorDefinitionFromApplication request predicate witness
      application).isSome = true ↔
      request.predicateSource.check = some predicate ∧
      request.existence.sequent.hyp = ∅ ∧
      request.existence.sequent.concl.IsBool ∧
      predicate.term.HasNoFreeVariables ∧
      request.typeVariables.Nodup ∧
      request.typeVariables.toFinset = predicate.term.typeVariables := by
  by_cases sourceChecked : request.predicateSource.check = some predicate
  · by_cases hypothesesEmpty : request.existence.sequent.hyp = ∅
    · by_cases conclusionBool :
          request.existence.sequent.concl.isBoolB = true
      · by_cases predicateClosed : predicate.term.hasNoFreeVariables = true
        · by_cases variablesNodup : request.typeVariables.Nodup
          · by_cases variablesExact :
                request.typeVariables.toFinset = predicate.term.typeVariables
            · constructor
              · intro _
                exact ⟨sourceChecked, hypothesesEmpty,
                  (CanonicalTerm.isBoolB_eq_true_iff _).mp conclusionBool,
                  (DBTerm.hasNoFreeVariables_eq_true_iff _).mp predicateClosed,
                  variablesNodup, variablesExact⟩
              · intro _
                simp [checkTypeOperatorDefinitionFromApplication,
                  sourceChecked, hypothesesEmpty, conclusionBool,
                  predicateClosed, variablesNodup, variablesExact]
            · constructor
              · intro impossible
                simp [checkTypeOperatorDefinitionFromApplication,
                  sourceChecked, hypothesesEmpty, conclusionBool,
                  predicateClosed, variablesNodup, variablesExact] at impossible
              · rintro ⟨_, _, _, _, _, exactVariables⟩
                exact False.elim (variablesExact exactVariables)
          · constructor
            · intro impossible
              simp [checkTypeOperatorDefinitionFromApplication,
                sourceChecked, hypothesesEmpty, conclusionBool,
                predicateClosed, variablesNodup] at impossible
            · rintro ⟨_, _, _, _, nodup, _⟩
              exact False.elim (variablesNodup nodup)
        · constructor
          · intro impossible
            simp [checkTypeOperatorDefinitionFromApplication,
              sourceChecked, hypothesesEmpty, conclusionBool,
              predicateClosed] at impossible
          · rintro ⟨_, _, _, closed, _, _⟩
            exact False.elim
              (predicateClosed
                ((DBTerm.hasNoFreeVariables_eq_true_iff _).mpr closed))
      · constructor
        · intro impossible
          simp [checkTypeOperatorDefinitionFromApplication,
            sourceChecked, hypothesesEmpty, conclusionBool] at impossible
        · rintro ⟨_, _, bool, _, _, _⟩
          exact False.elim
            (conclusionBool
              ((CanonicalTerm.isBoolB_eq_true_iff _).mpr bool))
    · constructor
      · intro impossible
        simp [checkTypeOperatorDefinitionFromApplication,
          sourceChecked, hypothesesEmpty] at impossible
      · rintro ⟨_, empty, _, _, _, _⟩
        exact False.elim (hypothesesEmpty empty)
  · constructor
    · intro impossible
      simp [checkTypeOperatorDefinitionFromApplication, sourceChecked]
        at impossible
    · rintro ⟨checked, _, _, _, _, _⟩
      exact False.elim (sourceChecked checked)

/-- A proof-relevant canonical view of an application. -/
structure CanonicalTerm.ApplicationView (whole : CanonicalTerm) where
  function : CanonicalTerm
  argument : CanonicalTerm
  semantics : CanonicalTerm.ApplicationSemantics function argument whole

/-- Recover a proof-relevant application view when the canonical term has one. -/
def CanonicalTerm.applicationView? (whole : CanonicalTerm) :
    Option (CanonicalTerm.ApplicationView whole) :=
  match applicationView : whole.destApplication? with
  | none => none
  | some (function, argument) =>
      some
        ⟨function, argument,
          (CanonicalTerm.destApplication?_eq_some_iff _ _ _).mp
            applicationView⟩

/-- Attaching application evidence does not change whether decomposition
succeeds. -/
theorem CanonicalTerm.applicationView?_isSome_eq
    (whole : CanonicalTerm) :
  whole.applicationView?.isSome = whole.destApplication?.isSome := by
  rw [CanonicalTerm.applicationView?.eq_1]
  split
  · rename_i noApplication
    exact (congrArg Option.isSome noApplication).symm
  · rename_i pair application
    exact (congrArg Option.isSome application).symm

/-- Execute the complete pinned type-operator-definition gate. -/
def checkTypeOperatorDefinition (request : TypeOperatorDefinitionRequest) :
    Option TypeOperatorDefinitionResult :=
  match request.existence.sequent.concl.applicationView? with
  | none => none
  | some view =>
      checkTypeOperatorDefinitionFromApplication request view.function
        view.argument view.semantics

/-- Executable type-operator definition succeeds exactly for the pinned
definition side conditions. -/
theorem checkTypeOperatorDefinition_isSome_iff
    (request : TypeOperatorDefinitionRequest) :
    (checkTypeOperatorDefinition request).isSome = true ↔
      TypeOperatorDefinitionAdmissible request := by
  cases applicationView :
      request.existence.sequent.concl.applicationView? with
  | none =>
    constructor
    · simp [checkTypeOperatorDefinition, applicationView]
    · intro admissible
      rcases admissible with ⟨predicate, witness, application, _⟩
      have destinationView :=
        (CanonicalTerm.destApplication?_eq_some_iff _ _ _).mpr application
      have existsView :
          request.existence.sequent.concl.applicationView?.isSome = true := by
        rw [CanonicalTerm.applicationView?_isSome_eq, destinationView]
        rfl
      rw [applicationView] at existsView
      contradiction
  | some view =>
    simp only [checkTypeOperatorDefinition, applicationView]
    rw [checkTypeOperatorDefinitionFromApplication_isSome_iff]
    constructor
    · rintro ⟨sourceChecked, hypothesesEmpty, conclusionBool,
        predicateClosed, variablesNodup, variablesExact⟩
      exact ⟨view.function, view.argument, view.semantics,
        sourceChecked, hypothesesEmpty, conclusionBool, predicateClosed,
        variablesNodup, variablesExact⟩
    · rintro ⟨otherPredicate, otherWitness, otherApplication,
        sourceChecked, hypothesesEmpty, conclusionBool, predicateClosed,
        variablesNodup, variablesExact⟩
      have otherPairView :=
        (CanonicalTerm.destApplication?_eq_some_iff _ _ _).mpr
          otherApplication
      have selectedPairView :=
        (CanonicalTerm.destApplication?_eq_some_iff _ _ _).mpr view.semantics
      have pairEquality :
          (otherPredicate, otherWitness) = (view.function, view.argument) :=
        Option.some.inj (otherPairView.symm.trans selectedPairView)
      have predicateEquality : otherPredicate = view.function :=
        congrArg Prod.fst pairEquality
      subst otherPredicate
      exact ⟨sourceChecked, hypothesesEmpty, conclusionBool,
        predicateClosed, variablesNodup, variablesExact⟩

/-- Accepted type definitions preserve all existing axiom provenance and add
no new axiom tag. -/
theorem checkTypeOperatorDefinition_preserves_axioms
    {request : TypeOperatorDefinitionRequest}
    {result : TypeOperatorDefinitionResult}
    (accepted : checkTypeOperatorDefinition request = some result) :
    result.abstractionRepresentationTheorem.axioms =
        request.existence.axioms ∧
      result.representationAbstractionTheorem.axioms =
        request.existence.axioms := by
  cases applicationView :
      request.existence.sequent.concl.applicationView? with
  | none =>
    simp [checkTypeOperatorDefinition, applicationView] at accepted
  | some view =>
    simp only [checkTypeOperatorDefinition, applicationView] at accepted
    unfold checkTypeOperatorDefinitionFromApplication at accepted
    repeat' split at accepted <;> try contradiction
    rename_i sourceChecked hypothesesEmpty conclusionBoolB predicateClosed
      variablesNodup variablesExact
    have resultEquality := Option.some.inj accepted
    subst result
    exact (makeTypeOperatorDefinition_provenance request view.function
      view.argument view.semantics
      ((CanonicalTerm.isBoolB_eq_true_iff _).mp conclusionBoolB)).2.2.2

end Mettapedia.Languages.OpenTheory
