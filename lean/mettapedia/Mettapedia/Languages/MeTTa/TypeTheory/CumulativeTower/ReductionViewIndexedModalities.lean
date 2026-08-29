import Mettapedia.Languages.MeTTa.Prime.NucleusDerivedModalTyping

/-!
# Modal typing is indexed by an operational reduction view

An authored language determines its sorts and constructor crossings, but it
does not by itself determine which sort carries reduction.  OSLF's derived
modal classification takes that reduction sort as an explicit parameter.

This module packages the parameter as a typed operational view and proves the
consequence on the current Prime presentation.  The same language and the same
quote/drop arrows have different derived modal roles under Process and Atom
views.  Therefore residency and syntax cannot silently choose a firing
discipline: a space or evaluator must supply the operational view it uses.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace ReductionViewIndexedModalities

open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.DerivedTyping
open Mettapedia.Languages.MeTTa.Prime

/-- A reduction carrier selected from the sorts of one authored language. -/
structure ReductionView
    (language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef) where
  carrier : LangSort language

namespace ReductionView

def role {language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (view : ReductionView language) {domain codomain : LangSort language}
    (arrow : SortArrow language domain codomain) : ConstructorRole :=
  classifyArrow language view.carrier.val arrow

/-- A quoting observation forces the arrow's domain to be the selected
reduction carrier. -/
theorem role_eq_quoting_iff
    {language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (view : ReductionView language) {domain codomain : LangSort language}
    (arrow : SortArrow language domain codomain) :
    view.role arrow = .quoting ↔ domain.val = view.carrier.val :=
  classifyArrow_eq_quoting_iff language view.carrier.val arrow

/-- Reflection likewise depends on the selected carrier, with the usual
domain-side exclusion. -/
theorem role_eq_reflecting_iff
    {language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (view : ReductionView language) {domain codomain : LangSort language}
    (arrow : SortArrow language domain codomain) :
    view.role arrow = .reflecting ↔
      domain.val ≠ view.carrier.val ∧ codomain.val = view.carrier.val :=
  classifyArrow_eq_reflecting_iff language view.carrier.val arrow

end ReductionView

namespace PrimeCanary

open NucleusDerivedModalTyping

/-- The current evaluator-oriented reading: authored rewrites produce
`Process`. -/
def processView : ReductionView
    Mettapedia.Languages.MeTTa.Prime.LanguageDef.language where
  carrier := processSortObj

/-- The atom-reduction reading needed for quote/drop to derive rho-like
modalities. -/
def atomView : ReductionView
    Mettapedia.Languages.MeTTa.Prime.LanguageDef.language where
  carrier := atomSort

theorem quote_neutral_in_process_view :
    processView.role quoteArrow = .neutral :=
  quote_is_neutral

theorem drop_neutral_in_process_view :
    processView.role dropArrow = .neutral :=
  drop_is_neutral

theorem quote_quoting_in_atom_view :
    atomView.role quoteArrow = .quoting :=
  quote_is_quoting_if_atoms_reduce

theorem drop_reflecting_in_atom_view :
    atomView.role dropArrow = .reflecting :=
  drop_is_reflecting_if_atoms_reduce

/-- No constructor-only readout can assign quote one view-independent modal
role: the two lawful reduction views disagree on the same arrow. -/
theorem quote_has_no_view_independent_role :
    ¬ ∃ role : ConstructorRole,
      processView.role quoteArrow = role ∧
      atomView.role quoteArrow = role := by
  rintro ⟨role, processRole, atomRole⟩
  rw [quote_neutral_in_process_view] at processRole
  rw [quote_quoting_in_atom_view] at atomRole
  exact ConstructorRole.noConfusion (processRole.trans atomRole.symm)

/-- Positive/negative canary: changing only the operational view changes both
derived modal readings while leaving the language and arrows fixed. -/
theorem same_language_distinct_modal_readouts :
    processView.role quoteArrow = .neutral ∧
    atomView.role quoteArrow = .quoting ∧
    processView.role dropArrow = .neutral ∧
    atomView.role dropArrow = .reflecting :=
  ⟨quote_neutral_in_process_view, quote_quoting_in_atom_view,
    drop_neutral_in_process_view, drop_reflecting_in_atom_view⟩

end PrimeCanary

#print axioms ReductionView.role_eq_quoting_iff
#print axioms ReductionView.role_eq_reflecting_iff
#print axioms PrimeCanary.quote_has_no_view_independent_role
#print axioms PrimeCanary.same_language_distinct_modal_readouts

end ReductionViewIndexedModalities
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
