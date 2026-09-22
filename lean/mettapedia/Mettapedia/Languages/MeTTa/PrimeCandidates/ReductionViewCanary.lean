import Mettapedia.OSLF.Framework.ReductionViewIndexedModalities
import Mettapedia.Languages.MeTTa.PrimeCandidates.NucleusDerivedModalTyping

/-!
# Reduction-view canary for the nucleus candidate presentation

The same nucleus language and quote/drop arrows have different derived modal
roles under Process and Atom views.  The classification is therefore indexed
by the selected reduction carrier, not fixed by the language's constructor
crossings alone.  These facts concern this presentation; they do not select a
reduction carrier or an activation discipline for other languages or spaces.
-/


open Mettapedia.OSLF.Framework
set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.ReductionViewCanary

open Mettapedia.OSLF.Framework.DerivedTyping
open Mettapedia.OSLF.Framework.ReductionViewIndexedModalities
open NucleusDerivedModalTyping

/-- The evaluator-oriented reading of the nucleus: authored rewrites produce
`Process`. -/
def processView : ReductionView
    Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.language where
  carrier := processSortObj

/-- The atom-reduction reading needed for the nucleus quote/drop arrows to
derive rho-like modalities. -/
def atomView : ReductionView
    Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.language where
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

#print axioms quote_has_no_view_independent_role
#print axioms same_language_distinct_modal_readouts

end Mettapedia.Languages.MeTTa.PrimeCandidates.ReductionViewCanary
