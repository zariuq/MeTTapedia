import Mettapedia.OSLF.Syntax.CanonicalConditionalRuleFrames
import Mettapedia.OSLF.Syntax.RhoAuthoredDropProfile

/-!
# The authored rho Drop profile in the conditional-rule polynomial

The same canonical language that runs the Chapter 7 Drop rule supplies a
constructor tree for that firing. Its COMM-only predecessor has no such tree
at any finite depth. These controls compare the new source-level polynomial
with the actual executable and least relational semantics.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoCanonicalConditionalRuleFrames

open Mettapedia.OSLF.Binding.CanonicalConditionalRuleFrames
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSchema.Authored
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

/-- The actual authored Drop firing inhabits the new proof-relevant tree
family at one contextual layer. -/
theorem authored_drop_has_tree :
    Nonempty ((authoredPresentation
      (engineBasePremises RelationEnv.empty) rhoCalcWithDrop).Derivation ()
        (1, dropQuotedZero, zero)) := by
  exact (mem_rewriteAt_iff_derivation
    (engineBasePremises RelationEnv.empty) rhoCalcWithDrop
    1 dropQuotedZero zero).mp authored_drop_fires

/-- The previous authored rho core cannot derive Drop at any depth, even
though the enlarged profile can. This is a negative operational control,
not a claim that the two presentations have different term carriers. -/
theorem authored_core_has_no_drop_tree (fuel : Nat) :
    ¬ Nonempty ((authoredPresentation
      (engineBasePremises RelationEnv.empty) rhoCalc).Derivation ()
        (fuel, dropQuotedZero, zero)) := by
  intro tree
  apply authored_comm_only_never_drops zero
  exact (derivation_nonempty_iff_step
    (engineBasePremises RelationEnv.empty) rhoCalc dropQuotedZero zero).mp
      ⟨fuel, tree⟩

/-- The profile inclusion is strict at the level of retained operational
trees, just as it is strict for the existing step relation. -/
theorem authored_drop_profile_is_strict :
    Nonempty ((authoredPresentation
      (engineBasePremises RelationEnv.empty) rhoCalcWithDrop).Derivation ()
        (1, dropQuotedZero, zero)) ∧
    ∀ fuel, ¬ Nonempty ((authoredPresentation
      (engineBasePremises RelationEnv.empty) rhoCalc).Derivation ()
        (fuel, dropQuotedZero, zero)) :=
  ⟨authored_drop_has_tree, authored_core_has_no_drop_tree⟩

/-- Put the real Drop redex inside the authored parallel collection. -/
def parallelDrop : Pattern :=
  .collection .hashBag [dropQuotedZero] none

def parallelZero : Pattern :=
  .collection .hashBag [zero] none

/-- ParCong consumes the Drop firing as a recursive premise. The actual
interpreter needs two contextual layers for this example. -/
theorem parCong_over_drop_fires :
    parallelZero ∈ reducts rhoCalcWithDrop 2 parallelDrop := by
  decide +kernel

/-- The same authored execution has a retained two-layer constructor tree. -/
theorem parCong_over_drop_has_tree :
    Nonempty ((authoredPresentation
      (engineBasePremises RelationEnv.empty) rhoCalcWithDrop).Derivation ()
        (2, parallelDrop, parallelZero)) := by
  exact (mem_rewriteAt_iff_derivation
    (engineBasePremises RelationEnv.empty) rhoCalcWithDrop
    2 parallelDrop parallelZero).mp parCong_over_drop_fires

/-- A single layer cannot discharge the ParCong premise. -/
theorem parCong_over_drop_needs_recursive_layer :
    ¬ Nonempty ((authoredPresentation
      (engineBasePremises RelationEnv.empty) rhoCalcWithDrop).Derivation ()
        (1, parallelDrop, parallelZero)) := by
  intro tree
  have member := (mem_rewriteAt_iff_derivation
    (engineBasePremises RelationEnv.empty) rhoCalcWithDrop
    1 parallelDrop parallelZero).mpr tree
  have noReducts : reducts rhoCalcWithDrop 1 parallelDrop = [] := by
    decide +kernel
  change parallelZero ∈ reducts rhoCalcWithDrop 1 parallelDrop at member
  rw [noReducts] at member
  exact List.not_mem_nil member

#print axioms authored_drop_has_tree
#print axioms authored_core_has_no_drop_tree
#print axioms authored_drop_profile_is_strict
#print axioms parCong_over_drop_has_tree
#print axioms parCong_over_drop_needs_recursive_layer

end Mettapedia.OSLF.Binding.RhoCanonicalConditionalRuleFrames
