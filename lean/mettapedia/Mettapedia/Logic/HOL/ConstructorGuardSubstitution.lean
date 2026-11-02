import Mettapedia.Logic.HOL.ConstructorShapeDataGuard

/-!
# Substitution of retained constructor-row implications

A row implication remains available after an earlier typed substitution.
Later substitutions compose with that substitution, and the original
hypothesis occurrences are transported through an explicit equality of
the substituted premise lists. Both endpoint casts retain the original
callback's proof tree.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.ConstructorPrograms.RowImplication

open FiniteConstructorEncoding

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ Ω : Ctx Base}
  {premises : List (Formula Const Γ)} {inventory : ConstructorPrograms Const Γ}
  {conditions : ConstructorDataPredicates.Conditions Const Γ inventory.fields}

def substitute (refine : RowImplication premises inventory conditions)
    (earlier : Subst Const Γ Ξ) :
    RowImplication (premises.map (HOL.subst earlier)) (inventory.subst earlier)
      (fun occurrence => HOL.subst earlier (conditions occurrence)) := by
  intro Ω later assumptions transport occurrence arguments allowed
  have sourceLists : (premises.map (HOL.subst earlier)).map (HOL.subst later) =
      premises.map (HOL.subst (Subst.comp later earlier)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro formula _
    exact HOL.subst_comp later earlier formula
  let originalOccurrences : ProofSyntax.OccurrenceMap
      (premises.map (HOL.subst (Subst.comp later earlier))) assumptions :=
    sourceLists ▸ transport
  have originalAllowed : ProofSyntax Const assumptions
      (applyArguments _ (HOL.subst (Subst.comp later earlier) (inventory.allowed occurrence)) arguments) :=
    .castIndices rfl
      (congrArg (fun predicate => applyArguments _ predicate arguments)
        (HOL.subst_comp later earlier (inventory.allowed occurrence))) allowed
  have result := refine (Subst.comp later earlier) originalOccurrences occurrence arguments originalAllowed
  exact .castIndices rfl
    (congrArg (fun predicate => applyArguments _ predicate arguments)
      (HOL.subst_comp later earlier (conditions occurrence)).symm) result

theorem substitute_free (refine : RowImplication premises inventory conditions)
    (refineFree : RowImplication.Free refine) (earlier : Subst Const Γ Ξ) :
    RowImplication.Free (substitute refine earlier) := by
  intro Ω later assumptions transport occurrence arguments allowed allowedFree
  unfold substitute
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply refineFree
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr allowedFree

def reindexPremises (refine : RowImplication premises inventory conditions)
    {newPremises : List (Formula Const Γ)}
    (indices : ProofSyntax.OccurrenceMap premises newPremises) :
    RowImplication newPremises inventory conditions := by
  intro Ω images assumptions transport occurrence arguments allowed
  let shifted := indices.map (HOL.subst images)
  let originalOccurrences : ProofSyntax.OccurrenceMap (premises.map (HOL.subst images)) assumptions :=
    { index := fun index => transport.index (shifted.index index)
      get_eq := fun index => (transport.get_eq (shifted.index index)).trans (shifted.get_eq index) }
  exact refine images originalOccurrences occurrence arguments allowed

theorem reindexPremises_free (refine : RowImplication premises inventory conditions)
    (refineFree : RowImplication.Free refine)
    {newPremises : List (Formula Const Γ)}
    (indices : ProofSyntax.OccurrenceMap premises newPremises) :
    RowImplication.Free (reindexPremises refine indices) := by
  intro Ω images assumptions transport occurrence arguments allowed allowedFree
  exact refineFree images _ occurrence arguments allowed allowedFree

#print axioms substitute
#print axioms substitute_free
#print axioms reindexPremises
#print axioms reindexPremises_free

end Mettapedia.Logic.HOL.IndexedConstructorGuards.ConstructorPrograms.RowImplication
