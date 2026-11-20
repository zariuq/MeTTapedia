import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.FreshNamespaces

/-!
# A finite protected prefix for an application store

Only shared values, captured arguments and source knowledge constrain the
caller namespace. The private terms inside a schematic datum do not. A bound
on this finite support makes independently paired openings genuinely fresh
even when the source contains unresolved shared unknowns.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)

universe uOcc
variable {O : Type uOcc}

noncomputable def sourceSupport (s : Store O) : Finset Nat :=
  (context s).toFinset.biUnion Term.freeVars

noncomputable def sourceBound (s : Store O) : Nat := (sourceSupport s).sup id + 1

theorem context_below (s : Store O) (term : Tm) (inside : term ∈ context s)
    (name : Nat) (occurs : name ∈ term.freeVars) : name < sourceBound s := by
  have supported : name ∈ sourceSupport s :=
    Finset.mem_biUnion.mpr ⟨term, List.mem_toFinset.mpr inside, occurs⟩
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id) supported)

theorem mentioned_in_context (s : Store O) (term : Tm) (mentioned : s.scope.Mentions term) :
    term ∈ context s := by
  rw [State.scope_mentions_iff] at mentioned
  rcases mentioned with left | right | ⟨o, present, inside⟩
  · exact List.mem_append_left _ (List.mem_append_left _ left)
  · exact List.mem_append_left _ (List.mem_append_right _ right)
  · apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨o, Finset.mem_toList.mpr present, inside⟩

theorem mentioned_below (s : Store O) (term : Tm) (mentioned : s.scope.Mentions term)
    (name : Nat) (occurs : name ∈ term.freeVars) : name < sourceBound s :=
  context_below s term (mentioned_in_context s term mentioned) name occurs

theorem ambient_in_context (s : Store O) (o : O) (present : o ∈ s.present)
    (term : Tm) (inside : term ∈ (s.label o).ambientTerms) : term ∈ context s :=
  mentioned_in_context s term ((State.scope_mentions_iff s term).mpr (Or.inr (Or.inr ⟨o, present, inside⟩)))

#print axioms context_below
#print axioms mentioned_below
#print axioms ambient_in_context

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
