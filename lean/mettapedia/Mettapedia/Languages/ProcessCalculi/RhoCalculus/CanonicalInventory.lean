import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalSupport
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous

/-!
# Declaration inventories for the existing rho canonicalizer

This inventory concerns rows of one authored `LanguageDef`. It permits extra
process constructors with ordinary parameters, as required by synchronous
output, while retaining the exact quote, drop, unit, and parallel rows. It
contains no normalization or iteration closure assumption.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open CanonicalSupport

/-- The four static rows and the shapes of all other declarations used by
rho normalization. Additional process constructors may contain binders. -/
structure CanonicalInventory (language : LanguageDef) where
  shared : ∀ index : Fin 4, rhoCalc.terms[index.val] ∈ language.terms
  rows : ∀ rule ∈ language.terms, rule ∈ rhoCalc.terms ∨
    (rule.label ≠ "NQuote" ∧ rule.label ≠ "PDrop" ∧ rule.category = "Proc" ∧
      ¬ UsesBareCollection rule ∧ ParametersCanonicalizable rule.params)

namespace CanonicalInventory
variable {language : LanguageDef}

/-- The original asynchronous language inhabits the same declaration domain. -/
theorem asynchronous : CanonicalInventory rhoCalc where
  shared := fun _ => List.getElem_mem _
  rows := fun _ member => Or.inl member

/-- Synchronous output is an additional ordinary process constructor; its
three arguments all have authored Name or Proc result types. -/
theorem synchronous : CanonicalInventory Synchronous.rhoSyncCalc where
  shared := by
    intro index
    fin_cases index <;> simp [Synchronous.rhoSyncCalc]
  rows := by
    intro rule member
    simp only [Synchronous.rhoSyncCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact Or.inl (List.getElem_mem _) | skip
    right
    refine ⟨by decide, by decide, rfl, ?_, ?_⟩
    · simp [UsesBareCollection, Synchronous.rhoSyncOutputRule]
    · simp [ParametersCanonicalizable, Synchronous.rhoSyncOutputRule, parameterType?]
      exact ⟨trivial, trivial⟩

theorem quote_row (inventory : CanonicalInventory language)
    {rule : GrammarRule} (member : rule ∈ language.terms) (label : rule.label = "NQuote") :
    rule = rhoCalc.terms[2] := by
  rcases inventory.rows rule member with source | extra
  · simp [rhoCalc] at source
    rcases source with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [rhoCalc]
  · exact False.elim (extra.1 label)

theorem drop_row (inventory : CanonicalInventory language)
    {rule : GrammarRule} (member : rule ∈ language.terms) (label : rule.label = "PDrop") :
    rule = rhoCalc.terms[1] := by
  rcases inventory.rows rule member with source | extra
  · simp [rhoCalc] at source
    rcases source with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [rhoCalc]
  · exact False.elim (extra.2.1 label)

theorem name_row (inventory : CanonicalInventory language)
    {rule : GrammarRule} (member : rule ∈ language.terms) (category : rule.category = "Name") :
    rule = rhoCalc.terms[2] := by
  rcases inventory.rows rule member with source | extra
  · simp [rhoCalc] at source
    rcases source with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [rhoCalc]
  · simp [extra.2.2.1] at category

theorem collection_row (inventory : CanonicalInventory language)
    {rule : GrammarRule} (member : rule ∈ language.terms) (bare : UsesBareCollection rule) :
    rule = rhoCalc.terms[3] := by
  rcases inventory.rows rule member with source | extra
  · simp [rhoCalc] at source
    rcases source with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [rhoCalc, UsesBareCollection, TypeExpr.proc, TypeExpr.name, TypeExpr.baseType]
  · exact False.elim (extra.2.2.2.1 bare)

theorem parameters (inventory : CanonicalInventory language)
    {rule : GrammarRule} (member : rule ∈ language.terms) (notBare : ¬ UsesBareCollection rule) :
    ParametersCanonicalizable rule.params := by
  rcases inventory.rows rule member with source | extra
  · exact rhoRule_parametersCanonicalizable source notBare
  · exact extra.2.2.2.2

end CanonicalInventory
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
