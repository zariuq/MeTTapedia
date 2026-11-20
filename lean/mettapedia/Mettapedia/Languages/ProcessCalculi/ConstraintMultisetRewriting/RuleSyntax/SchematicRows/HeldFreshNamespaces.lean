import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.FreshNamespaces
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Step
import Mettapedia.Logic.LP.TermEquality

/-!
# Fresh first-order openings in a state holding rule occurrences

The retained support includes both ordinary data and every held closure's
captured arguments. Its finite bound licenses independently opened materializers
and consumers even when caller unknowns remain unresolved. Private code terms
are not mistaken for ambient unknowns merely because a rule is stored.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldFreshNamespaces

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open RuleOccurrences

universe uOcc uR uC uZ
variable {signature : LPSignature} {O : Type uOcc} {R : Type uR} {C : Type uC} {Z : Type uZ}

abbrev X := frames (FirstOrder.action signature)
abbrev E := ext (FirstOrder.action signature)

noncomputable def sourceTerms (s : RState (Terms (Term signature)) O R C Z) : List (Term signature) :=
  s.knowledge.map Prod.fst ++ s.knowledge.map Prod.snd ++ s.present.toList.map s.label ++
    s.rules.toList.flatMap (fun held => (s.held held).args)

theorem mentioned_in_sourceTerms (s : RState (Terms (Term signature)) O R C Z) (term : Term signature)
    (mentioned : s.Mentions term) : term ∈ sourceTerms s := by
  rcases mentioned with (left | right | ⟨o, present, labelled⟩) | ⟨held, present, argument⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ left))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ right))
  · exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨o, Finset.mem_toList.mpr present, labelled⟩))
  · exact List.mem_append_right _
      (List.mem_flatMap.mpr ⟨held, Finset.mem_toList.mpr present, argument⟩)

variable [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]

noncomputable def support (s : RState (Terms (Term signature)) O R C Z) : Finset signature.vars :=
  (sourceTerms s).toFinset.biUnion Term.freeVars

noncomputable def bound (slots : signature.vars ≃ Nat) (s : RState (Terms (Term signature)) O R C Z) : Nat :=
  (support s).sup slots + 1

theorem mentioned_below (slots : signature.vars ≃ Nat) (s : RState (Terms (Term signature)) O R C Z)
    (term : Term signature) (mentioned : s.Mentions term) (name : signature.vars) (occurs : name ∈ term.freeVars) :
    slots name < bound slots s := by
  have inside : name ∈ support s := Finset.mem_biUnion.mpr
    ⟨term, List.mem_toFinset.mpr (mentioned_in_sourceTerms s term mentioned), occurs⟩
  exact Nat.lt_succ_of_le (Finset.le_sup (f := fun name => slots name) inside)

theorem firing_fresh (slots : signature.vars ≃ Nat) {codes : Codes (Terms (Term signature)) C Z}
    {s : RState (Terms (Term signature)) O R C Z} (f : RFiring O R E codes s) (index : Nat)
    (opened : f.opening = FreshNamespaces.opening slots (bound slots s) index) : f.Fresh X := by
  intro target caller locals
  cases target
  let requested : Nat → Subst signature := fun _ => locals
  let assignment := FreshNamespaces.combine slots (bound slots s) caller requested
  refine ⟨assignment, ?_, ?_⟩
  · intro term mentioned
    change assignment.applyTerm ((Subst.id signature).applyTerm term) = caller.applyTerm term
    rw [Subst.applyTerm_id]
    exact FreshNamespaces.source_agrees slots (bound slots s) caller requested term
      (mentioned_below slots s term mentioned)
  · intro term _
    change assignment.applyTerm (f.opening.applyTerm term) = locals.applyTerm term
    rw [opened]
    exact FreshNamespaces.combine_opening slots (bound slots s) caller requested index term

#print axioms mentioned_below
#print axioms firing_fresh

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldFreshNamespaces
