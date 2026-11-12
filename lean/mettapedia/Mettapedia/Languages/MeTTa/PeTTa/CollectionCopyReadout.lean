import Mettapedia.Languages.MeTTa.PeTTa.EagerDFS
import Mettapedia.Languages.ProcessCalculi.MORK.AtomRenamingApart
import Mettapedia.Languages.ProcessCalculi.MORK.VariantReadout

/-!
# Canonical readout of the independent source collection-copy contract

Every accepted copy retains its value/associated-syntax sharing. Separately
copied answer occurrences have a joint observation determined by their source
variants, rather than by the concrete fresh-name allocator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.CollectionCopyReadout

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (atomFreeVars)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (renameTypeVars)
open EagerDFS

theorem type_variables (term : Atom) : TypeSubst.typeVars term = atomFreeVars term := by
  induction term using Atom.rec
      (motive_2 := fun terms => TypeSubst.typeVarsList terms = atomFreeVars.atomFreeVarsList terms) with
  | symbol | var | grounded => rfl
  | expression terms ih => exact ih
  | nil => rfl
  | cons term terms head tail =>
      simp only [TypeSubst.typeVarsList,atomFreeVars.atomFreeVarsList,head,tail]

theorem type_renaming (names : String → String) (term : Atom) :
    renameTypeVars names term = AtomRenaming.rename names term := by
  induction term using Atom.rec
      (motive_2 := fun terms => terms.map (renameTypeVars names) = AtomRenaming.rename.list names terms) with
  | symbol | var | grounded => simp only [renameTypeVars,AtomRenaming.rename]
  | expression terms ih => simpa only [renameTypeVars,AtomRenaming.rename] using congrArg Atom.expression ih
  | nil => rfl
  | cons term terms head tail => simp only [List.map_cons,AtomRenaming.rename.list,head,tail]

theorem tuple_variables (terms : List Atom) :
    EagerDFS.Destination.ClauseChoice.names terms = atomFreeVars (.expression terms) := by
  induction terms with
  | nil => rfl
  | cons first rest ih =>
      change TypeSubst.typeVars first ++ EagerDFS.Destination.ClauseChoice.names rest =
        atomFreeVars first ++ atomFreeVars (.expression rest)
      rw [type_variables,ih]

theorem isCopy_tuple_variant (protectedNames : Finset String) (value : Atom) (associated : List Atom)
    (copied : Atom × List Atom) (source : Collection.IsCopy protectedNames value associated copied) :
    AtomRenaming.Variant (.expression (value :: associated)) (.expression (copied.1 :: copied.2)) := by
  obtain ⟨names,injective,fresh,head,tail⟩ := source
  apply (VariantReadout.normalize_equal_iff_variant _ _).mp
  have renamed : .expression (copied.1 :: copied.2) =
      AtomRenaming.rename names (.expression (value :: associated)) := by
    rw [head,tail]
    rw [← type_renaming names (.expression (value :: associated))]
    simp only [renameTypeVars,List.map_cons]
  rw [renamed]
  apply (VariantReadout.normalize_rename _ names _).symm
  intro first firstIn second secondIn same
  apply injective _ _ same
  · simpa only [Set.mem_ofPred_eq,tuple_variables] using firstIn
  · simpa only [Set.mem_ofPred_eq,tuple_variables] using secondIn

theorem isCopy_value_variant (protectedNames : Finset String) (value : Atom) (associated : List Atom)
    (copied : Atom × List Atom) (source : Collection.IsCopy protectedNames value associated copied) :
    AtomRenaming.Variant value copied.1 := by
  obtain ⟨forward,backward,changed,recovered⟩ := isCopy_tuple_variant protectedNames value associated copied source
  exact ⟨forward,backward,(List.cons.inj (Atom.expression.inj changed)).1,
    (List.cons.inj (Atom.expression.inj recovered)).1⟩

theorem copies_values_separated (protectedNames : Finset String) (source copied : List (Atom × List Atom))
    (copies : Collection.Copies protectedNames source copied) :
    (copied.map Prod.fst).Pairwise AtomRenaming.Apart := by
  apply List.pairwise_iff_getElem.mpr
  intro first second firstBound secondBound earlier
  simp only [List.getElem_map]
  intro name present
  simpa only [type_variables] using copies.2.2 first second (by simpa using firstBound) (by simpa using secondBound)
    (Nat.ne_of_lt earlier) name (by simpa only [type_variables] using present)

theorem copies_values_variant (protectedNames : Finset String) (source copied : List (Atom × List Atom))
    (copies : Collection.Copies protectedNames source copied) :
    List.Forall₂ AtomRenaming.Variant (source.map Prod.fst) (copied.map Prod.fst) := by
  apply List.forall₂_iff_get.mpr
  refine ⟨by simpa using copies.1.symm,?_⟩
  intro index before after
  simp only [List.get_eq_getElem,List.getElem_map]
  exact isCopy_value_variant _ _ _ _ (copies.2.1 index (by simpa using before) (by simpa using after))

/-- Both collectors copy their corresponding source values. Their concrete
allocation names may differ; occurrence order and joint sharing do not. -/
theorem copied_joint_observations (firstProtected secondProtected : Finset String)
    (firstSource secondSource firstCopied secondCopied : List (Atom × List Atom))
    (corresponding : List.Forall₂ AtomRenaming.Variant (firstSource.map Prod.fst) (secondSource.map Prod.fst))
    (firstCopies : Collection.Copies firstProtected firstSource firstCopied)
    (secondCopies : Collection.Copies secondProtected secondSource secondCopied) :
    VariantReadout.joint (firstCopied.map Prod.fst) = VariantReadout.joint (secondCopied.map Prod.fst) := by
  have left := AtomRenaming.variants_symm (copies_values_variant firstProtected firstSource firstCopied firstCopies)
  have right := copies_values_variant secondProtected secondSource secondCopied secondCopies
  have joint := AtomRenaming.joint_variant_of_separated
    (AtomRenaming.variants_trans left (AtomRenaming.variants_trans corresponding right))
    (copies_values_separated firstProtected firstSource firstCopied firstCopies)
    (copies_values_separated secondProtected secondSource secondCopied secondCopies)
  exact (VariantReadout.joint_equal_iff_variant _ _).mpr joint

end Mettapedia.Languages.MeTTa.PeTTa.CollectionCopyReadout
