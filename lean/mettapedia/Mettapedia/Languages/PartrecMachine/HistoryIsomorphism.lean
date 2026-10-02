import Mettapedia.Languages.PartrecMachine.HistoryContinued
import Mettapedia.GSLT.LanguageDef.Continued.EffectiveIsomorphism

/-!
# No theory isomorphic to the history theory has an effective section

The history theory has no effective section.  The same holds of every
interactive theory isomorphic to it: an effective section of an isomorphic
theory would decide the static equivalence of the history theory along the
computable family of probes, which is the halting problem.

So the failure is a property of the theory up to isomorphism and not of one
presentation of it: no interactive theory with an effective section, and in
particular no effectively continued one, is isomorphic to the history theory.

The isomorphisms considered keep the name of the built-in equality relation,
which belongs to the evaluator and not to either theory.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.Languages.PartrecMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSimulation

/-- The history machine declares no collection algebra. -/
theorem historyMachine_no_algebra : historyMachine.hasAlgebraDeclarations = false := by
  decide

/-- A theory with a map of declarations into the history theory declares no
collection algebra either: declaration transport preserves the presence of
algebra metadata. Every symbol map therefore fixes its declared units. -/
theorem fixesDeclaredUnits_of_morphism {theory : IGSLT} (morphism : theory ⟶ historyTheory)
    (symbols : LanguageDefSymbolMap) :
    FixesDeclaredUnits symbols theory.presentation.presentation.language := by
  intro rule membership algebra declared
  have mapped : mapGrammarRule morphism.structural.structural.symbols rule ∈
      historyMachine.terms := morphism.structural.structural.mapsTerms rule membership
  have absent := List.any_eq_false.mp historyMachine_no_algebra _ mapped
  have transported : (mapGrammarRule morphism.structural.structural.symbols rule).algebra? =
      some (StructuralMorphism.mapCollectionAlgebra
        morphism.structural.structural.symbols.constructor algebra) := by
    simp only [mapGrammarRule, declared, Option.map_some]
  rw [transported] at absent
  simp at absent

/-- **No theory isomorphic to the history theory has an effective
section.** -/
theorem no_effective_section_of_iso (theory : IGSLT) (iso : theory ≅ historyTheory)
    (relationFixesEq : iso.hom.structural.structural.symbols.relation "eq" = "eq")
    (canonical : ComputableCanonicalSection theory) : ¬ canonical.Effective :=
  fun effective => equivalence_not_computable
    (IGSLT.computablePred_of_iso iso relationFixesEq
      (fixesDeclaredUnits_of_morphism iso.hom _)
      (fixesDeclaredUnits_of_no_algebra _ historyMachine_no_algebra) effective
      computable_code_nowProbe computable_code_flagProbe)

/-- **No effectively continued theory is isomorphic to the history theory.**
The witness for an undecidable static equivalence lies outside the essential
image of the effectively continued theories, and not only outside their
image. -/
theorem not_effectivelyContinued_of_iso (theory : IGSLT) (iso : theory ≅ historyTheory)
    (relationFixesEq : iso.hom.structural.structural.symbols.relation "eq" = "eq") :
    ¬ IsEffectivelyContinued theory :=
  fun ⟨continued, effective⟩ =>
    no_effective_section_of_iso theory iso relationFixesEq continued.canonical effective

/-- The history theory itself, by the identity isomorphism. -/
theorem history_not_effectivelyContinued_by_iso : ¬ IsEffectivelyContinued historyTheory :=
  not_effectivelyContinued_of_iso historyTheory (Iso.refl historyTheory) rfl

end Mettapedia.Languages.PartrecMachine
