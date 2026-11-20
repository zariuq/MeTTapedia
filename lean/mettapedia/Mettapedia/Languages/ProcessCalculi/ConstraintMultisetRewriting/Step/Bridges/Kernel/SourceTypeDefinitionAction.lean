import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.SourceDefinitionAction

/-!
# Actual type-definition witnesses under a source name action

Predicate syntax, the typed existence application, its hypotheses and axiom
dependencies all move together. This preserves the shared type-definition
admission conditions. The source adapter additionally requires fresh names
and its chosen parameter ordering; these are not inferred from arity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceTypeDefinitionAction

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open SourceNameAction SourceSignatureAction SourceBindingAction SourceDefinitionAction

def BoolFixed (names : Names) : Prop := names.operators (Name.global "bool") = Name.global "bool"

theorem boolean_type (names : Names) (fixed : BoolFixed names) : mapType names Ty.bool = Ty.bool := by
  simp only [Ty.bool, TypeOp.bool, mapType, mapOperator, mapOperatorOrigin, mapTypes]
  rw [fixed]

theorem boolean_term (names : Names) (functionFixed : FunctionFixed names) (booleanFixed : BoolFixed names)
    (term : CanonicalTerm) : (mapCanonical names functionFixed term).IsBool ↔ term.IsBool := by
  change mapType names term.ty = Ty.bool ↔ term.ty = Ty.bool
  constructor
  · intro equal
    exact type_injective names (equal.trans (boolean_type names booleanFixed).symm)
  · intro equal
    rw [equal]
    exact boolean_type names booleanFixed

def mapSequent (names : Names) (fixed : FunctionFixed names) (sequent : Sequent) : Sequent :=
  ⟨sequent.hyp.image (mapCanonical names fixed), mapCanonical names fixed sequent.concl⟩

theorem sequent_boolean (names : Names) (fixed : FunctionFixed names) (booleanFixed : BoolFixed names)
    (sequent : Sequent) (valid : sequent.IsBool) : (mapSequent names fixed sequent).IsBool := by
  refine ⟨(boolean_term names fixed booleanFixed _).mpr valid.1, ?_⟩
  intro hypothesis member
  obtain ⟨original, present, rfl⟩ := Finset.mem_image.mp member
  exact (boolean_term names fixed booleanFixed original).mpr (valid.2 original present)

def mapTheorem (names : Names) (fixed : FunctionFixed names) (booleanFixed : BoolFixed names)
    (fact : Theorem) : Theorem where
  axioms := fact.axioms.image (mapSequent names fixed)
  axiomsBoolean := by
    intro sequent member
    obtain ⟨original, present, rfl⟩ := Finset.mem_image.mp member
    exact sequent_boolean names fixed booleanFixed original (fact.axiomsBoolean original present)
  sequent := mapSequent names fixed fact.sequent

def mapRequest (names : Names) (fixed : FunctionFixed names) (booleanFixed : BoolFixed names)
    (request : TypeOperatorDefinitionRequest) : TypeOperatorDefinitionRequest where
  typeName := names.operators request.typeName
  abstractionName := names.constants request.abstractionName
  representationName := names.constants request.representationName
  typeVariables := request.typeVariables.map names.parameters
  predicateSource := mapTerm names request.predicateSource
  existence := mapTheorem names fixed booleanFixed request.existence

theorem application_preserved (names : Names) (fixed : FunctionFixed names)
    {function argument result : CanonicalTerm}
    (application : CanonicalTerm.ApplicationSemantics function argument result) :
    CanonicalTerm.ApplicationSemantics (mapCanonical names fixed function)
      (mapCanonical names fixed argument) (mapCanonical names fixed result) := by
  obtain ⟨domain, codomain, arrow, argumentType, resultShape⟩ := application
  refine ⟨mapType names domain, mapType names codomain, ?_, congrArg (mapType names) argumentType, ?_⟩
  · change (mapType names function.ty).destFunction? = _
    rw [function_view names fixed, arrow]
    rfl
  · change mapDB names result.term = .app (mapDB names function.term) (mapDB names argument.term)
    rw [resultShape]
    rfl

theorem admissible (names : Names) (fixed : FunctionFixed names) (booleanFixed : BoolFixed names)
    (request : TypeOperatorDefinitionRequest) (admitted : TypeOperatorDefinitionAdmissible request) :
    TypeOperatorDefinitionAdmissible (mapRequest names fixed booleanFixed request) := by
  obtain ⟨predicate, witness, application, predicateChecked, noHypotheses, boolean, closed,
    distinct, support⟩ := admitted
  refine ⟨mapCanonical names fixed predicate, mapCanonical names fixed witness,
    application_preserved names fixed application, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (mapTerm names request.predicateSource).check = _
    rw [check_action names fixed, predicateChecked]
    rfl
  · change request.existence.sequent.hyp.image (mapCanonical names fixed) = ∅
    rw [noHypotheses, Finset.image_empty]
  · exact (boolean_term names fixed booleanFixed _).mpr boolean
  · exact (closedness names predicate.term).mpr closed
  · exact distinct.map names.parameters.injective
  · change (request.typeVariables.map names.parameters).toFinset =
      (mapDB names predicate.term).typeVariables
    rw [List.toFinset_map, term_parameters, support]

theorem names_fresh (names : Names) (fixed : FunctionFixed names) (booleanFixed : BoolFixed names)
    (context : NameContext) (request : TypeOperatorDefinitionRequest) :
    TypeNamesFresh (mapNameContext names context) (mapRequest names fixed booleanFixed request) ↔
      TypeNamesFresh context request := by
  unfold TypeNamesFresh
  change (mapDeclaredName names (.typeOperator request.typeName) ∉ mapNameContext names context ∧
    mapDeclaredName names (.constant request.abstractionName) ∉ mapNameContext names context ∧
    mapDeclaredName names (.constant request.representationName) ∉ mapNameContext names context ∧
    names.constants request.abstractionName ≠ names.constants request.representationName) ↔ _
  simp only [declared_member]
  constructor
  · rintro ⟨typeFresh, abstractionFresh, representationFresh, distinct⟩
    exact ⟨typeFresh, abstractionFresh, representationFresh,
      fun same => distinct (congrArg names.constants same)⟩
  · rintro ⟨typeFresh, abstractionFresh, representationFresh, distinct⟩
    exact ⟨typeFresh, abstractionFresh, representationFresh,
      fun same => distinct (names.constants.injective same)⟩

/-- The actual source gate is preserved once its independently testable
ordering condition has been supplied for the renamed predicate. -/
theorem gate_forward (names : Names) (fixed : FunctionFixed names) (booleanFixed : BoolFixed names)
    (context : NameContext) (request : TypeOperatorDefinitionRequest)
    (accepted : (admitType context request).isSome = true)
    (ordered : request.typeVariables.map names.parameters =
      sortedParameters (mapTerm names request.predicateSource)) :
    (admitType (mapNameContext names context) (mapRequest names fixed booleanFixed request)).isSome = true := by
  obtain ⟨fresh, actual, _⟩ := (admitType_isSome_iff context request).mp accepted
  exact (admitType_isSome_iff _ _).mpr
    ⟨(names_fresh names fixed booleanFixed context request).mpr fresh,
      admissible names fixed booleanFixed request actual, ordered⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceTypeDefinitionAction
