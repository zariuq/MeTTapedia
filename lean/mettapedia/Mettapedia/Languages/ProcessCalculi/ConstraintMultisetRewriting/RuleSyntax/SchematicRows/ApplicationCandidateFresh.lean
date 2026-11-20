import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationCandidate

/-!
# The application candidate satisfies actual joint freshness

The finite source-support bound reserves every retained caller coordinate.
Three separate paired namespaces supply the rule and the two datum openings.
Filtering out shared data removes unused scope members, never merges the two
schematic selections, and retains the existing joint-freshness predicate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open JointFirings

universe uOcc
variable {O : Type uOcc}

theorem candidate_fresh (judgmentTag arrowTag : Nat) (s : Store O) (major minor made : O) :
    (candidate judgmentTag arrowTag (sourceBound s) s major minor made).Fresh X := by
  rcases s with ⟨frame, knowledge, present, label⟩
  cases frame
  let source : Store O := ⟨PUnit.unit, knowledge, present, label⟩
  let family := candidateScopes judgmentTag arrowTag (sourceBound source) source major minor made
  have distinct : (family.map Prod.fst).Nodup :=
    candidateScopes_distinct judgmentTag arrowTag (sourceBound source) source major minor made
  have opened : ∀ entry ∈ family,
      entry.2.opening = FreshNamespaces.opening (Equiv.refl Nat) (sourceBound source) entry.1 :=
    candidateScopes_openings judgmentTag arrowTag (sourceBound source) source major minor made
  have below : ∀ term,
      (⟨PUnit.unit, source.scope.knowledge, source.scope.present, source.scope.label⟩ :
        RuleSyntax.State RowTerms Tm).Mentions term →
      ∀ name ∈ term.freeVars, (Equiv.refl Nat) name < sourceBound source := by
    intro term mentioned name occurs
    exact mentioned_below source term mentioned name occurs
  have fresh := FreshNamespaces.fresh (Equiv.refl Nat) (sourceBound source)
    source.scope.knowledge source.scope.present source.scope.label family distinct opened below
  change Bag.Fresh X source.scope
    (⟨PUnit.unit, (candidate judgmentTag arrowTag (sourceBound source) source major minor made).scopeBag.members⟩ :
      Bag Tm E (Set.univ : RuleSyntax.Program RowTerms) PUnit.unit)
  rw [← candidateScopes_members]
  exact fresh

#print axioms candidate_fresh

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
