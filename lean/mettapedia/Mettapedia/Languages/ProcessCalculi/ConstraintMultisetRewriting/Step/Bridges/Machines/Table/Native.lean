import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Evaluator

/-!
# Computed successors and actual root-rule firings

The executable matcher/table evaluator is sound and complete for the actual
schematic step at every state that reads as the supplied row. A failed scan
means that this finite, range-restricted table admits no firing there.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table

open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic
open RuleSyntax.Machines

variable (schemas : List Schema)
  (closed : ∀ schema ∈ schemas, ∀ name ∈ unknowns schema.2, name ∈ unknowns schema.1)

include closed

theorem successor_iff_firing {state : SState Nat} {row result : Expr} (reads : ReadsBag state {row}) :
    result ∈ successors schemas row ↔
      ∃ firing : RuleSyntax.Firing Nat E {r | r ∈ rootRules schemas} state.frame,
        ∃ admitted : (schematicStep Nat (rootRules schemas)).Admits firing,
          ReadsBag ((schematicStep Nat (rootRules schemas)).result firing admitted) {result} := by
  constructor
  · intro member
    exact firing_of_rootStep closed reads ((mem_successors_iff schemas closed row result).mp member)
  · rintro ⟨firing, admitted, observed⟩
    obtain ⟨made, rooted, actual⟩ := rootStep_of_firing closed reads firing admitted
    have sameBag : ({made} : Multiset Expr) = {result} :=
      readsAs_unique actual.readsAs.1 actual.readsAs.2 observed.readsAs.2
    have same := Multiset.singleton_inj.mp sameBag
    subst made
    exact (mem_successors_iff schemas closed row result).mpr rooted

theorem no_successors_iff_no_firing {state : SState Nat} {row : Expr} (reads : ReadsBag state {row}) :
    successors schemas row = [] ↔
      ∀ firing : RuleSyntax.Firing Nat E {r | r ∈ rootRules schemas} state.frame,
        ¬ (schematicStep Nat (rootRules schemas)).Admits firing := by
  constructor
  · intro empty firing admitted
    obtain ⟨result, rooted, _⟩ := rootStep_of_firing closed reads firing admitted
    exact (successors_empty_iff schemas closed row).mp empty ⟨result, rooted⟩
  · intro none
    apply (successors_empty_iff schemas closed row).mpr
    rintro ⟨result, rooted⟩
    obtain ⟨firing, admitted, _⟩ := firing_of_rootStep closed reads rooted
    exact none firing admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.successor_iff_firing
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.no_successors_iff_no_firing
