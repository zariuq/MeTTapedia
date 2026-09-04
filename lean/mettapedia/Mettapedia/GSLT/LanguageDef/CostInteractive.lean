import Mettapedia.GSLT.LanguageDef.CostInteractionClosure

/-!
# Interactive closure of the generic Cost presentation

The generated whole-redex Cost language is returned to the existing
interactive hierarchy by selecting declarations from that exact validated
language.  The wrapped carrier, binary contact constructor, and funded rewrite
are not copied into a neighboring presentation.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open StructuralMorphism

namespace CIGSLT

/-- The generated wrapped carrier, selected from the exact Cost language. -/
def costWholeInteractingSort (source : CIGSLT) :
    DeclaredSort source.costWholePresentation :=
  ⟨TypeDecl.plain costWrappedSortName, by
    change List.Mem (TypeDecl.plain costWrappedSortName)
      source.costCoreLanguage.types
    apply List.mem_append_left
    simp [ContinuationRetypingPlan.generatedLanguage,
      ContinuationRetypingPlan.generatedTypes]⟩

/-- The generated binary contact, selected from the exact Cost language. -/
def costWholeContactConstructor (source : CIGSLT) :
    DeclaredConstructor source.costWholePresentation :=
  ⟨costContactConstructor, by
    change List.Mem costContactConstructor source.costCoreLanguage.terms
    apply List.mem_append_right
    simp [costCoreConstructors]⟩

/-- The generated funded interaction, selected from the exact Cost language. -/
def costWholeDeclaredRewrite (source : CIGSLT) :
    DeclaredRewrite source.costWholePresentation :=
  ⟨source.costWholeRedexRewrite, by
    change List.Mem source.costWholeRedexRewrite
      [source.costWholeRedexRewrite]
    exact List.mem_cons_self⟩

/-- The generic Cost presentation is interactive at its generated wrapped
carrier.  Binary contact is representation data; the singleton authored
rewrite remains the only reduction authority. -/
def costWholeInteractivePresentation (source : CIGSLT) :
    InteractivePresentation where
  presentation := source.costWholePresentation
  interactingSort := source.costWholeInteractingSort
  contactConstructor := source.costWholeContactConstructor
  interactionRewrite := source.costWholeDeclaredRewrite
  contactRepresentation := .binary
  representsContact := by
    rfl
  interactionHeaded := by
    change InteractionHeaded .binary costContactConstructor
      source.costWholeRedexSource
    rw [source.costWholeRedexSource_eq]
    rfl

@[simp]
theorem costBaseEquationDecl_left_freeFvarNames (equation : Equation) :
    (costBaseEquationDecl equation).left.freeFvarNames =
      equation.left.freeFvarNames.map costSourceSchemaName := by
  simp [costBaseEquationDecl, mapEquationSchemaNames, costBaseEquation,
    mapEquation, StructuralMorphism.mapPattern_freeFvarNames]

@[simp]
theorem costBaseEquationDecl_right_freeFvarNames (equation : Equation) :
    (costBaseEquationDecl equation).right.freeFvarNames =
      equation.right.freeFvarNames.map costSourceSchemaName := by
  simp [costBaseEquationDecl, mapEquationSchemaNames, costBaseEquation,
    mapEquation, StructuralMorphism.mapPattern_freeFvarNames]

@[simp]
theorem costWrappedEquationDecl_left_freeFvarNames (source : CIGSLT)
    (equation : Equation) :
    (costWrappedEquationDecl source.theory equation).left.freeFvarNames =
      equation.left.freeFvarNames.map costSourceSchemaName := by
  simp [costWrappedEquationDecl, mapEquationSchemaNames,
    costWrappedEquation, mapEquation,
    StructuralMorphism.mapPattern_freeFvarNames]

@[simp]
theorem costWrappedEquationDecl_right_freeFvarNames (source : CIGSLT)
    (equation : Equation) :
    (costWrappedEquationDecl source.theory equation).right.freeFvarNames =
      equation.right.freeFvarNames.map costSourceSchemaName := by
  simp [costWrappedEquationDecl, mapEquationSchemaNames,
    costWrappedEquation, mapEquation,
    StructuralMorphism.mapPattern_freeFvarNames]

/-- The exact source language's admitted execution profile exposes its
ordered-flow component independently of structural and relation-mode
validation. -/
theorem sourceExecutionFlowErrors_eq_nil (source : CIGSLT) :
    source.theory.presentation.presentation.language.executionFlowErrors
        source.theory.executionProfile.relationModes = [] := by
  have admitted := source.theory.executionProfile.admitted.admitted
  rw [source.theory.executionProfile.exactLanguage] at admitted
  unfold LanguageDef.executionAdmissionErrors at admitted
  simp only [List.append_eq_nil_iff] at admitted
  exact admitted.2

/-- Every generated static Cost equation remains premise-free. -/
theorem costStaticEquation_premises_eq_nil (source : CIGSLT)
    (equation : Equation) (membership : equation ∈ source.costStaticEquations) :
    equation.premises = [] := by
  rw [costStaticEquations] at membership
  rcases List.mem_append.mp membership with base | wrapped
  · rcases List.mem_map.mp base with
      ⟨sourceEquation, sourceMembership, rfl⟩
    simpa using congrArg
      (List.map (mapPremiseSchemaNames costSourceSchemaName ∘
        mapPremise costBaseStaticSymbols))
      (source.equationsRetypable sourceEquation sourceMembership).premiseFree
  · rcases List.mem_map.mp wrapped with
      ⟨sourceEquation, sourceMembership, rfl⟩
    simpa using congrArg
      (List.map (mapPremiseSchemaNames costSourceSchemaName ∘
        mapPremise (costWrappedStaticSymbols source.theory)))
      (source.equationsRetypable sourceEquation sourceMembership).premiseFree

/-- Structural validation of the source equation supplies the forward
metavariable inclusion for both generated Cost fibers. -/
theorem costStaticEquation_rightFvar_mem_left (source : CIGSLT)
    (equation : Equation) (membership : equation ∈ source.costStaticEquations)
    (name : String) (rightMembership : name ∈ equation.right.freeFvarNames) :
    name ∈ equation.left.freeFvarNames := by
  rw [costStaticEquations] at membership
  rcases List.mem_append.mp membership with base | wrapped
  · rcases List.mem_map.mp base with
      ⟨sourceEquation, sourceMembership, rfl⟩
    rw [costBaseEquationDecl_right_freeFvarNames] at rightMembership
    rcases List.mem_map.mp rightMembership with
      ⟨sourceName, sourceRightMembership, rfl⟩
    rw [costBaseEquationDecl_left_freeFvarNames]
    apply List.mem_map.mpr
    exact ⟨sourceName,
      by simpa [patternFvarNames_nil] using
        rightFvar_mem_left_of_validatedEquation_noPremises
          source.theory.presentation.presentation.language
          source.theory.presentation.presentation.valid sourceEquation
          sourceMembership
          (source.equationsRetypable sourceEquation sourceMembership).premiseFree
          sourceName (by simpa [patternFvarNames_nil] using
            sourceRightMembership), rfl⟩
  · rcases List.mem_map.mp wrapped with
      ⟨sourceEquation, sourceMembership, rfl⟩
    rw [costWrappedEquationDecl_right_freeFvarNames] at rightMembership
    rcases List.mem_map.mp rightMembership with
      ⟨sourceName, sourceRightMembership, rfl⟩
    rw [costWrappedEquationDecl_left_freeFvarNames]
    apply List.mem_map.mpr
    exact ⟨sourceName,
      by simpa [patternFvarNames_nil] using
        rightFvar_mem_left_of_validatedEquation_noPremises
          source.theory.presentation.presentation.language
          source.theory.presentation.presentation.valid sourceEquation
          sourceMembership
          (source.equationsRetypable sourceEquation sourceMembership).premiseFree
          sourceName (by simpa [patternFvarNames_nil] using
            sourceRightMembership), rfl⟩

/-- Reverse source flow supplies the converse metavariable inclusion, which
is necessary because authored equations execute in both orientations. -/
theorem costStaticEquation_leftFvar_mem_right (source : CIGSLT)
    (equation : Equation) (membership : equation ∈ source.costStaticEquations)
    (name : String) (leftMembership : name ∈ equation.left.freeFvarNames) :
    name ∈ equation.right.freeFvarNames := by
  rw [costStaticEquations] at membership
  rcases List.mem_append.mp membership with base | wrapped
  · rcases List.mem_map.mp base with
      ⟨sourceEquation, sourceMembership, rfl⟩
    rw [costBaseEquationDecl_left_freeFvarNames] at leftMembership
    rcases List.mem_map.mp leftMembership with
      ⟨sourceName, sourceLeftMembership, rfl⟩
    rw [costBaseEquationDecl_right_freeFvarNames]
    apply List.mem_map.mpr
    exact ⟨sourceName,
      LanguageDef.equation_leftFvar_mem_right_of_executionFlowErrors_eq_nil
        source.theory.presentation.presentation.language
        source.theory.executionProfile.relationModes
        source.sourceExecutionFlowErrors_eq_nil sourceEquation
        sourceMembership
        (source.equationsRetypable sourceEquation sourceMembership).premiseFree
        sourceName sourceLeftMembership, rfl⟩
  · rcases List.mem_map.mp wrapped with
      ⟨sourceEquation, sourceMembership, rfl⟩
    rw [costWrappedEquationDecl_left_freeFvarNames] at leftMembership
    rcases List.mem_map.mp leftMembership with
      ⟨sourceName, sourceLeftMembership, rfl⟩
    rw [costWrappedEquationDecl_right_freeFvarNames]
    apply List.mem_map.mpr
    exact ⟨sourceName,
      LanguageDef.equation_leftFvar_mem_right_of_executionFlowErrors_eq_nil
        source.theory.presentation.presentation.language
        source.theory.executionProfile.relationModes
        source.sourceExecutionFlowErrors_eq_nil sourceEquation
        sourceMembership
        (source.equationsRetypable sourceEquation sourceMembership).premiseFree
        sourceName sourceLeftMembership, rfl⟩

theorem costWholeLanguage_executionFlowErrors_eq_nil (source : CIGSLT) :
    source.costWholeLanguage.executionFlowErrors [] = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_premiseFree_withEquations
  · intro rule membership
    simp only [costWholeLanguage_rewrites, List.mem_singleton] at membership
    subst rule
    rfl
  · intro rule membership name nameMembership
    simp only [costWholeLanguage_rewrites, List.mem_singleton] at membership
    subst rule
    have bound := source.costWholeRedex_rightFvar_mem_left name
      (by simpa [costWholeRedexRewrite, patternFvarNames_nil] using
        nameMembership)
    simpa [costWholeRedexRewrite, patternFvarNames_nil] using bound
  · exact source.costStaticEquation_premises_eq_nil
  · exact source.costStaticEquation_rightFvar_mem_left
  · exact source.costStaticEquation_leftFvar_mem_right

/-- The generated interaction has no external relation premises and passes
the existing ordered execution-flow gate. -/
theorem costWholeLanguage_executionAdmissionErrors_eq_nil
    (source : CIGSLT) :
    source.costWholeLanguage.executionAdmissionErrors [] = [] := by
  exact LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes
    source.costWholeLanguage source.costWholeLanguage_validate
      source.costWholeLanguage_executionFlowErrors_eq_nil

/-- Empty relation modes are the exact execution profile of the generated
premise-free Cost interaction. -/
def costWholeExecutionProfile (source : CIGSLT) :
    ExecutionProfile source.costWholePresentation where
  relationModes := []
  admitted :=
    { lang := source.costWholeLanguage
      admitted := source.costWholeLanguage_executionAdmissionErrors_eq_nil }
  exactLanguage := rfl

/-- The generic Cost interaction as an iGSLT over the exact generated
presentation. -/
def costIGSLT (source : CIGSLT) : IGSLT where
  presentation := source.costWholeInteractivePresentation
  executionProfile := source.costWholeExecutionProfile

end CIGSLT

end Mettapedia.GSLT.LanguageDef
