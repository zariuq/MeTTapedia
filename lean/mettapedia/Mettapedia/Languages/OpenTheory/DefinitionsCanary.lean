import Mettapedia.Languages.OpenTheory.Definitions

/-!
# Positive and adversarial controls for OpenTheory definitions

These controls exercise the exact source-side definition gates.  They do not
postulate a HOL axiom bundle and do not treat definitional output as a semantic
conservativity proof.
-/

namespace Mettapedia.Languages.OpenTheory.DefinitionCanary

open Mettapedia.Languages.OpenTheory

/-! ## Constant definitions -/

def booleanValue : Const := .mk (Name.global "booleanValue") .undefined

def closedBooleanSource : SourceTerm :=
  .const booleanValue Ty.bool

def closedBooleanCanonical : CanonicalTerm :=
  CanonicalTerm.constant booleanValue Ty.bool

theorem closedBooleanSource_checked :
    closedBooleanSource.check = some closedBooleanCanonical := by
  rw [SourceTerm.check_eq_some_iff]
  simp [closedBooleanSource, closedBooleanCanonical,
    CanonicalTerm.constant, SourceTerm.toDB]

/-- A closed monomorphic term is admitted as a constant definition. -/
theorem closedBooleanSource_admitted :
    (checkConstantDefinition (Name.global "definedBoolean")
      closedBooleanSource).isSome = true := by
  rw [checkConstantDefinition_isSome_iff]
  refine ⟨closedBooleanCanonical, closedBooleanSource_checked,
    .const, ?_⟩
  simp [closedBooleanCanonical, CanonicalTerm.constant,
    DBTerm.typeVariables, Ty.typeVariables, Ty.typeVariablesList, Ty.bool]

def freeIndividual : SourceTerm :=
  .var (Name.global "x") Examples.individual

def freeIndividualCanonical : CanonicalTerm :=
  CanonicalTerm.free ⟨Name.global "x", Examples.individual⟩

theorem freeIndividual_checked :
    freeIndividual.check = some freeIndividualCanonical := by
  rw [SourceTerm.check_eq_some_iff]
  simp [freeIndividual, freeIndividualCanonical, CanonicalTerm.free,
    SourceTerm.toDB, boundIndex]

/-- A free term variable blocks constant definition. -/
theorem freeIndividual_rejected :
    checkConstantDefinition (Name.global "bad") freeIndividual = none := by
  cases accepted :
      checkConstantDefinition (Name.global "bad") freeIndividual with
  | none => rfl
  | some result =>
      exfalso
      have admissible : ConstantDefinitionAdmissible freeIndividual :=
        (checkConstantDefinition_isSome_iff
          (Name.global "bad") freeIndividual).mp (by simp [accepted])
      obtain ⟨candidate, checked, closed, _⟩ := admissible
      have candidateEquality : candidate = freeIndividualCanonical :=
        Option.some.inj (checked.symm.trans freeIndividual_checked)
      rw [candidateEquality] at closed
      cases closed

/-! ## Type-operator definitions -/

def predicateConstant : Const :=
  .mk (Name.global "predicate") .undefined

def witnessConstant : Const :=
  .mk (Name.global "witness") .undefined

def predicateSource : SourceTerm :=
  .const predicateConstant (.function Examples.individual Ty.bool)

def predicate : CanonicalTerm :=
  CanonicalTerm.constant predicateConstant
    (.function Examples.individual Ty.bool)

theorem predicateSource_checked :
    predicateSource.check = some predicate := by
  rw [SourceTerm.check_eq_some_iff]
  simp [predicateSource, predicate, CanonicalTerm.constant,
    SourceTerm.toDB]

def witness : CanonicalTerm :=
  CanonicalTerm.constant witnessConstant Examples.individual

def predicateWitness : CanonicalTerm :=
  CanonicalTerm.applicationOfFunction predicate witness Ty.bool
    (Ty.destFunction?_function Examples.individual Ty.bool)

def existence : Theorem := Theorem.emptyResult ∅ predicateWitness

def validTypeRequest : TypeOperatorDefinitionRequest :=
  { typeName := Name.global "selected"
    abstractionName := Name.global "absSelected"
    representationName := Name.global "repSelected"
    typeVariables := []
    predicateSource := predicateSource
    existence := existence }

/-- A hypothesis-free existence theorem for a closed predicate is admitted. -/
theorem validTypeRequest_admitted :
    (checkTypeOperatorDefinition validTypeRequest).isSome = true := by
  rw [checkTypeOperatorDefinition_isSome_iff]
  refine ⟨predicate, witness,
    CanonicalTerm.applicationOfFunction_semantics predicate witness Ty.bool
      (Ty.destFunction?_function Examples.individual Ty.bool),
    predicateSource_checked, rfl, rfl, .const, List.nodup_nil, ?_⟩
  simp [validTypeRequest, predicate, CanonicalTerm.constant,
    DBTerm.typeVariables, Ty.function, TypeOp.function,
    Ty.typeVariables, Ty.typeVariablesList, Examples.individual, Ty.bool]

def otherPredicateConstant : Const :=
  .mk (Name.global "otherPredicate") .undefined

def otherPredicateSource : SourceTerm :=
  .const otherPredicateConstant (.function Examples.individual Ty.bool)

def otherPredicate : CanonicalTerm :=
  CanonicalTerm.constant otherPredicateConstant
    (.function Examples.individual Ty.bool)

theorem otherPredicateSource_checked :
    otherPredicateSource.check = some otherPredicate := by
  rw [SourceTerm.check_eq_some_iff]
  simp [otherPredicateSource, otherPredicate, CanonicalTerm.constant,
    SourceTerm.toDB]

def mismatchedPredicateRequest : TypeOperatorDefinitionRequest :=
  { validTypeRequest with predicateSource := otherPredicateSource }

/-- The nominal predicate stored in type-operator provenance must check to the
predicate used by the existence theorem; equal types alone are insufficient. -/
theorem mismatchedPredicateRequest_rejected :
    checkTypeOperatorDefinition mismatchedPredicateRequest = none := by
  cases accepted : checkTypeOperatorDefinition mismatchedPredicateRequest with
  | none => rfl
  | some result =>
      exfalso
      have admissible :
          TypeOperatorDefinitionAdmissible mismatchedPredicateRequest :=
        (checkTypeOperatorDefinition_isSome_iff
          mismatchedPredicateRequest).mp (by simp [accepted])
      obtain ⟨candidate, selectedWitness, application, checked, _⟩ :=
        admissible
      have selectedView :=
        (CanonicalTerm.destApplication?_eq_some_iff _ _ _).mpr application
      have intendedApplication :=
        CanonicalTerm.applicationOfFunction_semantics predicate witness Ty.bool
          (Ty.destFunction?_function Examples.individual Ty.bool)
      have intendedView :=
        (CanonicalTerm.destApplication?_eq_some_iff _ _ _).mpr
          intendedApplication
      have pairEquality :
          (candidate, selectedWitness) = (predicate, witness) :=
        Option.some.inj (selectedView.symm.trans intendedView)
      have candidateIsPredicate : candidate = predicate :=
        congrArg Prod.fst pairEquality
      have candidateIsOther : candidate = otherPredicate :=
        Option.some.inj (checked.symm.trans otherPredicateSource_checked)
      have predicateEquality : predicate = otherPredicate :=
        candidateIsPredicate.symm.trans candidateIsOther
      have termEquality := congrArg CanonicalTerm.term predicateEquality
      simp [predicate, otherPredicate, CanonicalTerm.constant,
        predicateConstant, otherPredicateConstant, Name.global] at termEquality

def hypothesisBearingExistence : Theorem :=
  Theorem.emptyResult {SequentExamples.boolVariable "assumption"}
    predicateWitness

def hypothesisBearingRequest : TypeOperatorDefinitionRequest :=
  { validTypeRequest with existence := hypothesisBearingExistence }

/-- An existence theorem with hypotheses cannot define a type operator. -/
theorem hypothesisBearingRequest_rejected :
    checkTypeOperatorDefinition hypothesisBearingRequest = none := by
  cases accepted : checkTypeOperatorDefinition hypothesisBearingRequest with
  | none => rfl
  | some result =>
      exfalso
      have admissible :
          TypeOperatorDefinitionAdmissible hypothesisBearingRequest :=
        (checkTypeOperatorDefinition_isSome_iff
          hypothesisBearingRequest).mp (by simp [accepted])
      obtain ⟨_, _, _, _, hypothesesEmpty, _⟩ := admissible
      have impossible :
          SequentExamples.boolVariable "assumption" ∈
            (∅ : Finset CanonicalTerm) := by
        rw [← hypothesesEmpty]
        simp [hypothesisBearingRequest, hypothesisBearingExistence,
          Theorem.emptyResult]
      simp at impossible

def openPredicateSource : SourceTerm :=
  .var (Name.global "p") (.function Examples.individual Ty.bool)

def openPredicate : CanonicalTerm :=
  CanonicalTerm.free
    ⟨Name.global "p", .function Examples.individual Ty.bool⟩

theorem openPredicateSource_checked :
    openPredicateSource.check = some openPredicate := by
  rw [SourceTerm.check_eq_some_iff]
  simp [openPredicateSource, openPredicate, CanonicalTerm.free,
    SourceTerm.toDB, boundIndex]

def openPredicateWitness : CanonicalTerm :=
  CanonicalTerm.applicationOfFunction openPredicate witness Ty.bool
    (Ty.destFunction?_function Examples.individual Ty.bool)

def openPredicateRequest : TypeOperatorDefinitionRequest :=
  { validTypeRequest with
    predicateSource := openPredicateSource
    existence := Theorem.emptyResult ∅ openPredicateWitness }

/-- A free predicate variable is rejected even when the existence conclusion
is otherwise a well-typed Boolean application. -/
theorem openPredicateRequest_rejected :
    checkTypeOperatorDefinition openPredicateRequest = none := by
  cases accepted : checkTypeOperatorDefinition openPredicateRequest with
  | none => rfl
  | some result =>
      exfalso
      have admissible :
          TypeOperatorDefinitionAdmissible openPredicateRequest :=
        (checkTypeOperatorDefinition_isSome_iff
          openPredicateRequest).mp (by simp [accepted])
      obtain ⟨candidate, _, _, checked, _, _, closed, _⟩ := admissible
      have candidateEquality : candidate = openPredicate :=
        Option.some.inj (checked.symm.trans openPredicateSource_checked)
      rw [candidateEquality] at closed
      cases closed

def typeVariable : Name := Name.global "A"

def polymorphicPredicateConstant : Const :=
  .mk (Name.global "polymorphicPredicate") .undefined

def polymorphicWitnessConstant : Const :=
  .mk (Name.global "polymorphicWitness") .undefined

def polymorphicPredicateSource : SourceTerm :=
  .const polymorphicPredicateConstant (.function (.var typeVariable) Ty.bool)

def polymorphicPredicate : CanonicalTerm :=
  CanonicalTerm.constant polymorphicPredicateConstant
    (.function (.var typeVariable) Ty.bool)

def polymorphicWitness : CanonicalTerm :=
  CanonicalTerm.constant polymorphicWitnessConstant (.var typeVariable)

def polymorphicExistence : Theorem :=
  Theorem.emptyResult ∅
    (CanonicalTerm.applicationOfFunction polymorphicPredicate
      polymorphicWitness Ty.bool
      (Ty.destFunction?_function (.var typeVariable) Ty.bool))

def duplicateTypeVariablesRequest : TypeOperatorDefinitionRequest :=
  { typeName := Name.global "duplicate"
    abstractionName := Name.global "absDuplicate"
    representationName := Name.global "repDuplicate"
    typeVariables := [typeVariable, typeVariable]
    predicateSource := polymorphicPredicateSource
    existence := polymorphicExistence }

/-- Listing the right support twice still rejects: the source list is an
ordered arity declaration and must contain each variable precisely once. -/
theorem duplicateTypeVariablesRequest_rejected :
    checkTypeOperatorDefinition duplicateTypeVariablesRequest = none := by
  cases accepted :
      checkTypeOperatorDefinition duplicateTypeVariablesRequest with
  | none => rfl
  | some result =>
      exfalso
      have admissible :
          TypeOperatorDefinitionAdmissible duplicateTypeVariablesRequest :=
        (checkTypeOperatorDefinition_isSome_iff
          duplicateTypeVariablesRequest).mp (by simp [accepted])
      obtain ⟨_, _, _, _, _, _, _, variablesNodup, _⟩ := admissible
      have duplicated :
          ¬ duplicateTypeVariablesRequest.typeVariables.Nodup := by
        simp [duplicateTypeVariablesRequest]
      exact duplicated variablesNodup

end Mettapedia.Languages.OpenTheory.DefinitionCanary
