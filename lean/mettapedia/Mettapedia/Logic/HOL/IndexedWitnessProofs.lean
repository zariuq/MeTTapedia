import Mettapedia.Logic.HOL.IndexedPredicateInduction
import Mettapedia.Logic.HOL.CurriedGuardProgramProofs
import Mettapedia.Logic.HOL.ConstantExpansionProofsFree

/-!+# Retaining an index while adding membership and motive evidence

An existential root witness is transformed in its own scope. The family
predicate is arbitrary, so a shared certificate can later be instantiated
with the actual least predicate without rebuilding its logical derivation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedWitnessProofs

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    {space index : Ty Base} {assumptions : List (Formula Const Γ)}
    (family : Term Const Γ (space ⇒ .prop))
    (root property : Term Const Γ (space ⇒ index ⇒ .prop))
    (point : Term Const Γ space)
    (evidence : Formula Const (index :: Γ))

def rootWitness : Formula Const Γ :=
  .ex (.and evidence (.app (.app (weaken root) (weaken point)) (.var .vz)))

def indexedWitness : Formula Const Γ :=
  .ex (.and evidence
    (.and (.app (.app (weaken (CurriedGuardProgramProofs.conjunctionProgram family root)) (weaken point)) (.var .vz))
      (.app (.app (weaken property) (weaken point)) (.var .vz))))

def consume
    (member : ProofSyntax Const assumptions (.app family point))
    (lifted : ProofSyntax Const assumptions (.app (IndexedPredicateInduction.lift root property) point))
    (witness : ProofSyntax Const assumptions (rootWitness root point evidence)) :
    ProofSyntax Const assumptions (indexedWitness family root property point evidence) := by
  apply ProofSyntax.impE (ContextualTrinity.exImp ?_) witness
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let antecedent := Term.and evidence (.app (.app (weaken root) (weaken point)) (.var .vz))
  let localAssumptions := antecedent :: weakenHyps assumptions
  let present : ProofSyntax Const localAssumptions antecedent := .hyp 0
  let localMember := (ProofSyntax.rename Rename.weaken member).prepend antecedent
  have localLift : ProofSyntax Const localAssumptions
      (.app (IndexedPredicateInduction.lift (weaken root) (weaken property)) (weaken point)) := by
    apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.rename Rename.weaken lifted).prepend antecedent)
    simp only [HOL.rename, IndexedPredicateInduction.rename_lift, weaken]
  let memberProof := ProofSyntax.impE (ProofSyntax.eqPropER
    (CurriedGuardProgramProofs.conjunctionProgram_beta (weaken family) (weaken root) (weaken point) (.var .vz)))
    (ProofSyntax.andI localMember (ProofSyntax.andER present))
  let motiveProof := IndexedPredicateInduction.eliminate (weaken root) (weaken property)
    (weaken point) (.var .vz) localLift (ProofSyntax.andER present)
  apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.andI (ProofSyntax.andEL present)
    (ProofSyntax.andI memberProof motiveProof))
  simp only [weaken, ← subst_ofRename, CurriedGuardProgramProofs.subst_conjunctionProgram]

theorem consume_free
    (member : ProofSyntax Const assumptions (.app family point))
    (lifted : ProofSyntax Const assumptions (.app (IndexedPredicateInduction.lift root property) point))
    (witness : ProofSyntax Const assumptions (rootWitness root point evidence))
    (memberFree : member.FunctionExtensionalityFree) (liftedFree : lifted.FunctionExtensionalityFree)
    (witnessFree : witness.FunctionExtensionalityFree) :
    (consume family root property point evidence member lifted witness).FunctionExtensionalityFree := by
  unfold consume
  refine ⟨?_, witnessFree⟩
  apply (ContextualTrinity.exImp_free _).mpr
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  refine ⟨trivial, ⟨?_, ?_⟩⟩
  · refine ⟨CurriedGuardProgramProofs.conjunctionProgram_beta_free _ _ _ _, ?_, trivial⟩
    apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr memberFree
  · apply IndexedPredicateInduction.eliminate_free
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr liftedFree
    · trivial

#print axioms consume
#print axioms consume_free

end Mettapedia.Logic.HOL.IndexedWitnessProofs
