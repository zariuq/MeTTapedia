import Mettapedia.GSLT.LanguageDef.ConstructorFragmentTyping
import Mettapedia.GSLT.LanguageDef.CostStaticTyping
import Mettapedia.GSLT.LanguageDef.Cost.FiniteStatic

/-!
# Static typing for an arbitrary finite continuation profile

Both generated static colours transport the exact nonprincipal constructor
fragment of the authored profile. Declaration witnesses retain the sorting
of bare collections. This generic layer has no concrete instance imports.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax StructuralMorphism WellSorted

namespace ContinuationDecorationProfile
variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

/-- Additional slots still belong to the selected principal declarations. -/
theorem selectedParameter_eq_false_of_nonprincipal
    (profile : ContinuationDecorationProfile cut) (constructor : GrammarRule)
    (notProgram : constructor ≠ cut.program.constructor.1)
    (notEnvironment : constructor ≠ cut.environment.constructor.1) (index : Nat) :
    profile.selectedParameter constructor index = false := by
  simp [selectedParameter, isSelectedContinuation, notProgram, notEnvironment]

/-- No parameter is positionally retyped in a nonprincipal base row. -/
theorem baseConstructor_params_eq_map_of_nonprincipal
    (profile : ContinuationDecorationProfile cut) (constructor : GrammarRule)
    (notProgram : constructor ≠ cut.program.constructor.1)
    (notEnvironment : constructor ≠ cut.environment.constructor.1) :
    (profile.baseConstructor constructor).params =
      constructor.params.map (mapTermParam costBaseStaticSymbols) := by
  apply List.ext_getElem
  · simp [baseConstructor]
  · intro index leftBound rightBound
    rw [baseConstructor_parameter _ _ _ (by simpa [baseConstructor] using leftBound)]
    simp [List.getElem_map, baseParameter,
      profile.selectedParameter_eq_false_of_nonprincipal constructor notProgram notEnvironment]

/-- Row transport is derived from the actual closure inventory, including
bare collection declarations whose labels are absent from raw patterns. -/
theorem staticRows (profile : ContinuationDecorationProfile cut)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (color : CostStaticColor) (rule : GrammarRule)
    (member : rule ∈ theory.presentation.presentation.language.terms)
    (supported : rule.label ∈ profile.wrappedLabels) :
    ∃ targetRule ∈ profile.generatedLanguage.terms,
      targetRule.label = (color.symbolsOf theory).constructor rule.label ∧
      targetRule.category = (color.symbolsOf theory).sort rule.category ∧
      targetRule.params = rule.params.map (mapTermParam (color.symbolsOf theory)) := by
  let authored : DeclaredConstructor theory.presentation.presentation := ⟨rule, member⟩
  have included : authored ∈ profile.constructorClosure :=
    (profile.mem_wrappedLabels_iff authored).mp supported
  have excluded := nonprincipal authored included
  cases color with
  | base =>
      refine ⟨profile.baseConstructor rule, profile.baseConstructor_mem rule member,
        rfl, rfl, ?_⟩
      exact profile.baseConstructor_params_eq_map_of_nonprincipal rule
        (fun same => excluded.1 (Subtype.ext same))
        (fun same => excluded.2 (Subtype.ext same))
  | wrapped =>
      refine ⟨costWrappedConstructor (theory := theory) rule,
        profile.wrappedConstructor_mem authored included, rfl, rfl, ?_⟩
      simp [costWrappedConstructor, CostStaticColor.symbolsOf]

/-- Uniform static transport into the actual finite generated signature. -/
theorem mapStatic_hasType_generated (profile : ContinuationDecorationProfile cut)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasTypeWithConstructors theory.presentation.presentation.language
      (· ∈ profile.wrappedLabels) free bound pattern type) :
    HasType profile.generatedLanguage (free.map (color.symbolsOf theory))
      (bound.map (mapTypeExpr (color.symbolsOf theory)))
      (mapPattern (color.symbolsOf theory) pattern) (mapTypeExpr (color.symbolsOf theory) type) :=
  typed.mapRows (color.symbolsOf theory) (profile.staticRows nonprincipal color)

/-- The same derivation lives in the generated Cost language with its
apparatus, source equations, and selected funded rule. -/
theorem mapStatic_hasType (profile : ContinuationDecorationProfile cut)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasTypeWithConstructors theory.presentation.presentation.language
      (· ∈ profile.wrappedLabels) free bound pattern type) :
    HasType profile.costWholeLanguage (free.map (color.symbolsOf theory))
      (bound.map (mapTypeExpr (color.symbolsOf theory)))
      (mapPattern (color.symbolsOf theory) pattern) (mapTypeExpr (color.symbolsOf theory) type) :=
  (profile.mapStatic_hasType_generated nonprincipal color typed).weakenTerms
    profile.generatedTerms_mem_costWhole

/-- The old two-slot domain supplies the inventory condition constructively. -/
theorem ofRetypingPlan_nonprincipal (plan : ContinuationRetypingPlan cut) :
    ∀ constructor ∈ (ofRetypingPlan plan).constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor :=
  fun constructor included => (plan.mem_wrappedConstructors_iff constructor).mp included

/-- Specialization preserves the exact old language and static action. -/
theorem ofRetypingPlan_mapStatic_hasType (source : CIGSLT) (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasTypeWithConstructors source.theory.presentation.presentation.language
      (· ∈ source.continuationRetyping.wrappedLabels) free bound pattern type) :
    HasType source.costWholeLanguage (free.map (color.symbols source))
      (bound.map (mapTypeExpr (color.symbols source)))
      (mapPattern (color.symbols source) pattern) (mapTypeExpr (color.symbols source) type) := by
  simpa only [ofRetypingPlan_costWholeLanguage, CostStaticColor.symbols_eq_symbolsOf] using
    (ofRetypingPlan source.continuationRetyping).mapStatic_hasType
      (ofRetypingPlan_nonprincipal source.continuationRetyping) color typed

/-- A principal introduction cannot be smuggled into the uniform static
fragment by retaining its label alone. -/
theorem principal_labels_excluded (profile : ContinuationDecorationProfile cut)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor) :
    cut.program.constructor.1.label ∉ profile.wrappedLabels ∧
      cut.environment.constructor.1.label ∉ profile.wrappedLabels := by
  constructor
  · intro supported
    exact (nonprincipal cut.program.constructor
      ((profile.mem_wrappedLabels_iff _).mp supported)).1 rfl
  · intro supported
    exact (nonprincipal cut.environment.constructor
      ((profile.mem_wrappedLabels_iff _).mp supported)).2 rfl

end ContinuationDecorationProfile

end Mettapedia.GSLT.LanguageDef
