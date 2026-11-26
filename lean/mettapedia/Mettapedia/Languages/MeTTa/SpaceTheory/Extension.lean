import Mettapedia.Languages.MeTTa.SpaceTheory.Presentation
import Mettapedia.GSLT.LanguageDef.EquationSimulation

/-!
# When a space extends its base theory

Extension includes the original grammar, equations and directed rewrites.
It is a structural map between validated presentations, not a promise
that the new definitions cannot distinguish previously inert terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.Extension

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.LanguageDef
open EquationSemantics EquationSimulation
open LiveModuleEdits (Order)
open Presentation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- The inclusion does not choose a presentation-dependent numbering or
change spelling. It retains every authored declaration of the base. -/
def includeBase (core : ValidatedLanguageDef) (order : Order)
    (parts : List Contribution) (valid : (assemble order core.language parts).validate = []) :
    StructuralMorphism core ⟨assemble order core.language parts, valid⟩ where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration member := by
    rw [mapTypeDecl_id]
    exact member
  mapsTerms constructorDecl member := by
    rw [mapGrammarRule_id]
    exact member
  mapsEquations equation member := by
    rw [mapEquation_id]
    exact List.mem_append_left _ member
  mapsRewrites rewrite member := by
    rw [mapRewriteRule_id]
    cases order
    · exact List.mem_append_right _ member
    · exact List.mem_append_left _ member

theorem snapshot_extends (core : ValidatedLanguageDef) (order : Order) (atoms : List Atom)
    {localTheory : PresentedSpace} (presented : present order core.language atoms = some localTheory)
    (valid : localTheory.language.validate = []) :
    ∃ inclusion : StructuralMorphism core ⟨localTheory.language, valid⟩,
      inclusion.symbols = LanguageDefSymbolMap.id := by
  obtain ⟨language, built, rfl⟩ := Option.map_eq_some_iff.mp presented
  obtain ⟨parts, _, rfl⟩ := Option.map_eq_some_iff.mp built
  exact ⟨includeBase core order parts valid, rfl⟩

/-- Includes all of the base's steps modulo its equations, even when
the base has conditional rewrites and derived collection laws.
The default premise evaluator has no additional external relations. -/
theorem base_steps_in_snapshot (core : ValidatedLanguageDef) (order : Order) (atoms : List Atom)
    {localTheory : PresentedSpace} (presented : present order core.language atoms = some localTheory)
    (valid : localTheory.language.validate = []) {input output : Pattern}
    (source : StepModuloEquations (engineBasePremises RelationEnv.empty) core.language input output) :
    (localTheory.theory (engineBasePremises RelationEnv.empty)).Step input output := by
  obtain ⟨inclusion, symbols⟩ := snapshot_extends core order atoms presented valid
  have builtIn : inclusion.symbols.relation "eq" = "eq" := by rw [symbols]; rfl
  have units : FixesDeclaredUnits inclusion.symbols core.language := by
    rw [symbols]
    intro _ _ _ _ _ _
    rfl
  have mapped := stepModuloEquations_map_default inclusion builtIn units source
  change StepModuloEquations (engineBasePremises RelationEnv.empty) localTheory.language input output
  simpa only [symbols, mapPattern_id] using mapped

end Mettapedia.Languages.MeTTa.SpaceTheory.Extension
