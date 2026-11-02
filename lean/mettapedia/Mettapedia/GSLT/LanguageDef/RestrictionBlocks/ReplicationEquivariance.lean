import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationCanonFacts

/-!
# Renaming a term renames its canonical block

The canonical block of a renamed object term whose restrictions bind is the canonical form of its canonical block
renamed outside (`canonP_rename`): a constructor's arguments are read from their canonical blocks, a restriction
closes, a bag joins and a replication collects its molecules, and each of these commutes with renaming once the
canonical form is taken. Exchanging two restrictions keeps the canonical form (`normal_exchange`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)

variable {block : ReplicationBlock}

/-! ## Similar blocks by an order of the restrictions -/

theorem SimilarR.of_order {first second : Prenex} (countEq : first.count = second.count)
    {order : List Nat} (isOrder : IsOrder first.count order)
    (permutation : (first.components.map (rename (Prenex.permute first.count order))).Perm second.components) :
    SimilarR block first second :=
  ⟨countEq, order, _, isOrder, List.forall₂_same.mpr fun component _ => AlikeR.refl component, permutation⟩

theorem SimilarR.of_eq {first second : Prenex} (equal : first = second) : SimilarR block first second := by
  subst equal
  exact SimilarR.of_order rfl (order := List.range first.count) (List.Perm.refl _)
    (by rw [map_rename_permute_range])

/-- **Exchanging two restrictions on blocks**: the two closed blocks are similar, by exchanging the two
restrictions when both are used, and equal otherwise. -/
theorem exchange_blockR (form : Prenex) :
    SimilarR block form.close.close (form.renameOuter swapInner).close.close := by
  obtain ⟨count, components⟩ := form
  simp only [Prenex.renameOuter, liftIndex_swapInner]
  have swapInner' : (components.map (rename (swapAt count))).any (mentions count) =
      components.any (mentions (count + 1)) :=
    any_mentions_rename fun _ _ original _ => by simp only [swapAt]; split_ifs <;> omega
  have swapOuter' : (components.map (rename (swapAt count))).any (mentions (count + 1)) =
      components.any (mentions count) :=
    any_mentions_rename fun _ _ original _ => by simp only [swapAt]; split_ifs <;> omega
  by_cases inner : components.any (mentions count) = true <;>
    by_cases outer : components.any (mentions (count + 1)) = true
  · -- both restrictions are used: exchange them
    rw [close_of_used (form := ⟨count, components⟩) inner,
      close_of_used (form := Prenex.restrict ⟨count, components⟩) outer,
      close_of_used (form := ⟨count, components.map (rename (swapAt count))⟩) (swapInner'.trans outer),
      close_of_used (form := Prenex.restrict ⟨count, components.map (rename (swapAt count))⟩)
        (swapOuter'.trans inner)]
    refine SimilarR.of_order rfl (order := List.range count ++ [count + 1, count]) ?_ ?_
    · show (List.range count ++ [count + 1, count]).Perm (List.range (count + 2))
      rw [show count + 2 = count + 1 + 1 by omega, List.range_succ, List.range_succ, List.append_assoc]
      exact List.Perm.append_left _ (.swap _ _ _)
    · have same : Prenex.permute (count + 1 + 1) (List.range count ++ [count + 1, count]) = swapAt count := by
        funext index
        have length : (List.range count ++ [count + 1, count]).length = count + 1 + 1 := by simp
        by_cases inside : index < count + 1 + 1
        · rw [permute_of_lt length inside]
          by_cases low : index < count
          · have value : (List.range count ++ [count + 1, count])[index]'(by simp; omega) = index := by
              rw [List.getElem_append_left (by simpa using low)]
              simp
            rw [value]
            simp only [swapAt]
            split_ifs <;> omega
          · have : index = count ∨ index = count + 1 := by omega
            rcases this with rfl | rfl <;> simp [swapAt]
        · rw [permute_of_ge _ inside]
          simp only [swapAt]
          split_ifs <;> omega
      simp only [Prenex.restrict, same]
      exact .refl _
  · -- the inner restriction is used, the outer one is garbage
    have outer' : components.any (mentions (count + 1)) = false := by simpa using outer
    have swappedInner : (components.map (rename (swapAt count))).any (mentions count) = false :=
      swapInner'.trans outer'
    have unusedOuter := unused_of_any outer'
    have unusedSwapped := unused_of_any swappedInner
    have dropped : ((components.map (rename (swapAt count))).map (rename (dropIndex count))).any (mentions count) =
        true := by
      rw [any_mentions_rename (target := count + 1) fun component member original free => by
        have different : original ≠ count := fun equal => unusedSwapped component member (equal ▸ free)
        simp only [dropIndex]
        split_ifs <;> omega]
      exact swapOuter'.trans inner
    rw [close_of_used (form := ⟨count, components⟩) inner,
      close_of_unused (form := Prenex.restrict ⟨count, components⟩) outer',
      close_of_unused (form := ⟨count, components.map (rename (swapAt count))⟩) swappedInner,
      close_of_used (form := ⟨count, (components.map (rename (swapAt count))).map (rename (dropIndex count))⟩)
        dropped]
    refine SimilarR.of_eq ?_
    simp only [Prenex.restrict, List.map_map, Prenex.mk.injEq, true_and]
    refine List.map_congr_left fun component member => ?_
    simp only [Function.comp, rename_comp]
    apply rename_congr
    intro index free
    have different : index ≠ count + 1 := fun equal => unusedOuter component member (equal ▸ free)
    simp only [Function.comp, dropIndex, swapAt]
    split_ifs <;> omega
  · -- the inner restriction is garbage, the outer one is used
    have inner' : components.any (mentions count) = false := by simpa using inner
    have swappedOuter : (components.map (rename (swapAt count))).any (mentions (count + 1)) = false :=
      swapOuter'.trans inner'
    have unusedInner := unused_of_any inner'
    have dropped : (components.map (rename (dropIndex count))).any (mentions count) = true := by
      rw [any_mentions_rename (target := count + 1) fun component member original free => by
        have different : original ≠ count := fun equal => unusedInner component member (equal ▸ free)
        simp only [dropIndex]
        split_ifs <;> omega]
      exact outer
    rw [close_of_unused (form := ⟨count, components⟩) inner',
      close_of_used (form := ⟨count, components.map (rename (dropIndex count))⟩) dropped,
      close_of_used (form := ⟨count, components.map (rename (swapAt count))⟩) (swapInner'.trans outer),
      close_of_unused (form := Prenex.restrict ⟨count, components.map (rename (swapAt count))⟩) swappedOuter]
    refine SimilarR.of_eq ?_
    simp only [Prenex.restrict, List.map_map, Prenex.mk.injEq, true_and]
    refine List.map_congr_left fun component member => ?_
    simp only [Function.comp, rename_comp]
    apply rename_congr
    intro index free
    have different : index ≠ count := fun equal => unusedInner component member (equal ▸ free)
    simp only [Function.comp, dropIndex, swapAt]
    split_ifs <;> omega
  · -- both restrictions are garbage
    have inner' : components.any (mentions count) = false := by simpa using inner
    have outer' : components.any (mentions (count + 1)) = false := by simpa using outer
    have unusedInner := unused_of_any inner'
    have unusedOuter := unused_of_any outer'
    have swappedInner : (components.map (rename (swapAt count))).any (mentions count) = false :=
      swapInner'.trans outer'
    have unusedSwapped := unused_of_any swappedInner
    have dropped : (components.map (rename (dropIndex count))).any (mentions count) = false := by
      rw [any_mentions_rename (target := count + 1) fun component member original free => by
        have different : original ≠ count := fun equal => unusedInner component member (equal ▸ free)
        simp only [dropIndex]
        split_ifs <;> omega]
      exact outer'
    have droppedSwapped :
        ((components.map (rename (swapAt count))).map (rename (dropIndex count))).any (mentions count) = false := by
      rw [any_mentions_rename (target := count + 1) fun component member original free => by
        have different : original ≠ count := fun equal => unusedSwapped component member (equal ▸ free)
        simp only [dropIndex]
        split_ifs <;> omega]
      exact swapOuter'.trans inner'
    rw [close_of_unused (form := ⟨count, components⟩) inner',
      close_of_unused (form := ⟨count, components.map (rename (dropIndex count))⟩) dropped,
      close_of_unused (form := ⟨count, components.map (rename (swapAt count))⟩) swappedInner,
      close_of_unused (form := ⟨count, (components.map (rename (swapAt count))).map (rename (dropIndex count))⟩)
        droppedSwapped]
    refine SimilarR.of_eq ?_
    simp only [List.map_map, Prenex.mk.injEq, true_and]
    refine List.map_congr_left fun component member => ?_
    simp only [Function.comp, rename_comp]
    apply rename_congr
    intro index free
    have different : index ≠ count := fun equal => unusedInner component member (equal ▸ free)
    have different' : index ≠ count + 1 := fun equal => unusedOuter component member (equal ▸ free)
    simp only [Function.comp, dropIndex, swapAt]
    split_ifs <;> omega

/-! ## Blocks side by side, renamed outside -/

theorem foldr_par_renameOuter (relabel : Nat → Nat) : ∀ (forms : List Prenex),
    (forms.foldr Prenex.par Prenex.nil).renameOuter relabel =
      (forms.map (Prenex.renameOuter relabel)).foldr Prenex.par Prenex.nil
  | [] => nil_renameOuter relabel
  | form :: forms => by
      rw [List.foldr_cons, par_renameOuter, foldr_par_renameOuter relabel forms, List.map_cons, List.foldr_cons]

/-- The argument a constructor reads from an object argument's canonical block: a named multiset's as a multiset,
any other as the block's pattern. -/
def objectArgument (block : ReplicationBlock) (label : String) (form : Prenex) : Pattern :=
  if label ∈ block.multisets then multisetOf block.toBlock form else Prenex.toPattern block.toBlock form

theorem argumentOf_eq_objectArgument {label : String} {argument : Pattern} {form : Prenex}
    (object : isObjectPattern argument = true) :
    argumentOf block label argument form = objectArgument block label form :=
  argumentOf_object object

/-- **A renamed canonical block's pattern reads as the canonical form of the block renamed outside.** -/
theorem canonicalOf_rename_toPattern {form : Prenex} (atomic : form.Atomic block.toBlock) (used : form.Used)
    (relabel : Nat → Nat) :
    canonicalOf block (rename relabel (Prenex.toPattern block.toBlock form)) =
      Prenex.toPattern block.toBlock (normal block (form.renameOuter relabel)) := by
  unfold canonicalOf
  rw [decompose_renameOuter, decompose_toPattern atomic used]

/-- **A renamed argument read from a canonical block reads as the argument of the block renamed outside.** -/
theorem partOf_rename_objectArgument {label : String} {form : Prenex} (notRestrict : label ≠ block.restrict)
    (atomic : form.Atomic block.toBlock) (used : form.Used) (relabel : Nat → Nat) :
    partOf block label (rename relabel (objectArgument block label form)) =
      objectArgument block label (normal block (form.renameOuter relabel)) := by
  unfold partOf objectArgument
  rw [if_neg notRestrict]
  split_ifs with listed
  · obtain ⟨elements, bagIs⟩ := multisetOf_shape block.toBlock form
    have renamedIs : rename relabel (multisetOf block.toBlock form) =
        .collection .hashBag (elements.map (rename relabel)) none := by
      rw [bagIs, rename_collection]
    rw [multisetPart_other (argument := rename relabel (multisetOf block.toBlock form))
      (fun kind elements' rest equal => by rw [renamedIs] at equal; cases equal)
      (fun body replacement equal => by rw [renamedIs] at equal; cases equal),
      decompose_renameOuter, decompose_multisetOf atomic used]
  · exact canonicalOf_rename_toPattern atomic used relabel

/-- A canonical block other than inaction has a component. -/
theorem components_ne_nil_of_used {form : Prenex} (used : form.Used) (notNil : form ≠ Prenex.nil) :
    form.components ≠ [] := by
  intro empty
  obtain ⟨count, components⟩ := form
  simp only at empty
  subst empty
  cases count with
  | zero => exact notNil rfl
  | succ count =>
      obtain ⟨component, member, _⟩ := used 0 (Nat.succ_pos _)
      simp at member

/-- A pattern renamed is an abstraction exactly when the pattern is. -/
theorem rename_notLambda_iff {relabel : Nat → Nat} {pattern : Pattern} :
    (∀ binder body, rename relabel pattern ≠ .lambda binder body) ↔ ∀ binder body, pattern ≠ .lambda binder body := by
  refine ⟨fun renamed binder body equal => ?_, rename_notLambda⟩
  subst equal
  exact renamed binder _ (rename_lambda relabel binder body)

section Equivariance

variable (multisetFresh : block.replicate ∉ block.multisets) (fresh : block.replicate ∉ block.emptyUnits)
  (restrictFresh : block.replicate ≠ block.restrict)

include fresh restrictFresh

omit multisetFresh in
/-- **Exchanging two restrictions keeps the canonical form.** -/
theorem normal_exchange {form : Prenex} (atomic : form.Atomic block.toBlock) :
    normal block form.close.close = normal block (form.renameOuter swapInner).close.close :=
  normal_similar_all fresh restrictFresh (exchange_blockR form) (close_atomic (close_atomic atomic))
    (close_atomic (close_atomic (renameOuter_atomic atomic swapInner)))

omit multisetFresh in
/-- **A block with a component keeps one in its canonical form.** -/
theorem normal_components_ne_nil {form : Prenex} (atomic : form.Atomic block.toBlock)
    (nonempty : form.components ≠ []) : (normal block form).components ≠ [] := by
  rw [← normal_prune fresh restrictFresh form atomic]
  have prunedAtomic := prune_atomic atomic
  have prunedUsed := used_prune form
  have bundle := bundle_all fresh restrictFresh (size (Prenex.toPattern block.toBlock form.prune) + 1)
  have kept := bundle.nonEmpty (Prenex.toPattern block.toBlock form.prune) (Nat.lt_succ_self _)
  rw [decompose_toPattern prunedAtomic prunedUsed] at kept
  exact kept (by simpa [Prenex.prune] using nonempty)

omit multisetFresh in
/-- **Canonical blocks side by side read through their canonical forms.** -/
theorem normal_foldr_normal : ∀ (forms : List Prenex), (∀ form ∈ forms, form.Atomic block.toBlock) →
    normal block ((forms.map (normal block)).foldr Prenex.par Prenex.nil) =
      normal block (forms.foldr Prenex.par Prenex.nil)
  | [], _ => rfl
  | form :: forms, atomic => by
      have formAtomic := atomic form List.mem_cons_self
      have restAtomic : ∀ other ∈ forms, other.Atomic block.toBlock := fun other member =>
        atomic other (List.mem_cons_of_mem _ member)
      have mappedAtomic : ((forms.map (normal block)).foldr Prenex.par Prenex.nil).Atomic block.toBlock :=
        foldr_par_atomic _ fun other member => by
          obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
          exact normal_atomic fresh restrictFresh (restAtomic original inOriginal)
      have foldAtomic := foldr_par_atomic forms restAtomic
      rw [List.map_cons, List.foldr_cons, List.foldr_cons,
        normal_par_normal_left fresh restrictFresh formAtomic mappedAtomic,
        ← normal_par_normal_right fresh restrictFresh formAtomic mappedAtomic,
        normal_foldr_normal forms restAtomic,
        normal_par_normal_right fresh restrictFresh formAtomic foldAtomic]

omit multisetFresh in
/-- A component that is its own block, renamed outside, reads as the renamed component read again. -/
theorem normal_atom_renameOuter {component : Pattern}
    (atomic : decompose block.toBlock component = Prenex.atom component) (relabel : Nat → Nat) :
    normal block ((Prenex.atom component).renameOuter relabel) =
      Prenex.atom (recanon block (rename relabel component)) := by
  rw [atom_renameOuter, normal_atom fresh restrictFresh (atomic_rename atomic relabel)]

omit multisetFresh fresh restrictFresh in
/-- **Any other application is one component, its arguments read from their canonical blocks.** -/
theorem canonP_atomCase {label : String} {arguments : List Pattern}
    (object : ∀ argument ∈ arguments, isObjectPattern argument = true) (notRestrict : label ≠ block.restrict)
    (notUnit : ¬ (label = block.unit ∧ arguments = []))
    (notReplicated : ∀ argument, (∀ binder body, argument ≠ .lambda binder body) →
      ¬ (label = block.replicate ∧ arguments = [argument]))
    (notEmpty : ∀ argument, (∀ binder body, argument ≠ .lambda binder body) → arguments = [argument] →
      label ∈ block.emptyUnits → canonP block argument ≠ Prenex.nil) :
    canonP block (.apply label arguments) =
      Prenex.atom (.apply label (arguments.map fun argument => objectArgument block label (canonP block argument))) := by
  rw [canonP_apply notUnit (fun _ _ equal => notRestrict equal.1) notReplicated notEmpty, canonsP_eq_map,
    zipWith_map_self _ _ _ _ fun argument member => argumentOf_eq_objectArgument (object argument member)]

omit multisetFresh fresh restrictFresh in
/-- A renamed list of arguments is one argument exactly when the list is. -/
theorem map_rename_eq_singleton {relabel : Nat → Nat} {arguments : List Pattern} {argument : Pattern}
    (equal : arguments.map (rename relabel) = [argument]) :
    ∃ original, arguments = [original] ∧ rename relabel original = argument := by
  match arguments, equal with
  | [original], equal =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at equal
      exact ⟨original, rfl, equal⟩

include multisetFresh in
/-- **Renaming an object term whose restrictions bind renames its canonical block**, up to the canonical form; and so
for the body of an abstraction. -/
theorem canonP_rename_and (pattern : Pattern) :
    (isObjectPattern pattern = true → restrictionsBind block.toBlock pattern = true → ∀ relabel,
      Function.Injective relabel →
        canonP block (rename relabel pattern) = normal block ((canonP block pattern).renameOuter relabel)) ∧
      ∀ binder body, pattern = .lambda binder body → isObjectPattern body = true →
        restrictionsBind block.toBlock body = true → ∀ relabel, Function.Injective relabel →
          canonP block (rename relabel body) = normal block ((canonP block body).renameOuter relabel) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      refine ⟨fun _ _ relabel _ => ?_, fun _ _ equal => by cases equal⟩
      have atomIs : ∀ index', canonP block (.bvar index') = Prenex.atom (.bvar index') := fun _ => by simp [canonP]
      rw [rename_bvar, atomIs, atomIs, normal_atom_renameOuter fresh restrictFresh (decompose_bvar index), rename_bvar,
        recanon_bvar]
  | hfvar name =>
      refine ⟨fun _ _ relabel _ => ?_, fun _ _ equal => by cases equal⟩
      have atomIs : canonP block (.fvar name) = Prenex.atom (.fvar name) := by simp [canonP]
      rw [rename_fvar, atomIs, normal_atom_renameOuter fresh restrictFresh (decompose_fvar name), rename_fvar,
        recanon_fvar]
  | hsubst body replacement _ _ =>
      exact ⟨fun object _ => by simp [isObjectPattern] at object, fun _ _ equal => by cases equal⟩
  | hlambda binder body recurse =>
      refine ⟨fun object binds relabel injective => ?_, fun binder' body' equal => by cases equal; exact recurse.1⟩
      have bodyObject : isObjectPattern body = true := by simpa [isObjectPattern] using object
      have bodyBinds : restrictionsBind block.toBlock body = true := by simpa [restrictionsBind] using binds
      have facts := canonFacts fresh restrictFresh bodyObject bodyBinds
      rw [rename_lambda, canonP_lambda, canonP_lambda,
        recurse.1 bodyObject bodyBinds _ (liftIndex_injective injective 1),
        normal_atom_renameOuter fresh restrictFresh (decompose_lambda binder _), rename_lambda, recanon_lambda,
        canonicalOf_rename_toPattern facts.atomic facts.used]
  | hmultiLambda arity binders body recurse =>
      refine ⟨fun object binds relabel injective => ?_, fun _ _ equal => by cases equal⟩
      have bodyObject : isObjectPattern body = true := by simpa [isObjectPattern] using object
      have bodyBinds : restrictionsBind block.toBlock body = true := by simpa [restrictionsBind] using binds
      have facts := canonFacts fresh restrictFresh bodyObject bodyBinds
      have atomIs : ∀ inner, canonP block (.multiLambda arity binders inner) =
          Prenex.atom (.multiLambda arity binders (Prenex.toPattern block.toBlock (canonP block inner))) := fun _ => by
        simp [canonP]
      rw [rename_multiLambda, atomIs, atomIs,
        recurse.1 bodyObject bodyBinds _ (liftIndex_injective injective arity),
        normal_atom_renameOuter fresh restrictFresh (decompose_multiLambda arity binders _), rename_multiLambda,
        recanon_multiLambda, canonicalOf_rename_toPattern facts.atomic facts.used]
  | hcollection kind elements rest recurse =>
      refine ⟨fun object binds relabel injective => ?_, fun _ _ equal => by cases equal⟩
      simp only [isObjectPattern, isObjectPatternList_eq_all, Bool.and_eq_true, List.all_eq_true] at object
      simp only [restrictionsBind, restrictionsBindList_eq_all, List.all_eq_true] at binds
      obtain ⟨closed, objects⟩ := object
      have renamed : ∀ element ∈ elements, canonP block (rename relabel element) =
          normal block ((canonP block element).renameOuter relabel) := fun element member =>
        (recurse element member).1 (objects element member) (binds element member) relabel injective
      have facts : ∀ element ∈ elements, CanonFacts block element := fun element member =>
        canonFacts fresh restrictFresh (objects element member) (binds element member)
      have listIs : ((elements.map (rename relabel)).map (canonP block)).map (Prenex.toPattern block.toBlock) =
          (((elements.map (canonP block)).map (Prenex.toPattern block.toBlock)).map (rename relabel)).map
            (canonicalOf block) := by
        simp only [List.map_map]
        exact List.map_congr_left fun element member => by
          simp only [Function.comp_apply]
          rw [renamed element member,
            canonicalOf_rename_toPattern (facts element member).atomic (facts element member).used]
      cases rest with
      | some name => simp at closed
      | none =>
          rw [rename_collection]
          cases kind with
          | hashBag =>
              have mapIs : (elements.map (rename relabel)).map (canonP block) =
                  ((elements.map (canonP block)).map (Prenex.renameOuter relabel)).map (normal block) := by
                simp only [List.map_map]
                exact List.map_congr_left fun element member => renamed element member
              have atomicAll : ∀ form ∈ (elements.map (canonP block)).map (Prenex.renameOuter relabel),
                  form.Atomic block.toBlock := by
                intro form member
                simp only [List.map_map, List.mem_map] at member
                obtain ⟨element, inElements, rfl⟩ := member
                exact renameOuter_atomic (facts element inElements).atomic relabel
              have foldAtomic : ((elements.map (canonP block)).foldr Prenex.par Prenex.nil).Atomic block.toBlock :=
                foldr_par_atomic _ fun form member => by
                  obtain ⟨element, inElements, rfl⟩ := List.mem_map.mp member
                  exact (facts element inElements).atomic
              rw [canonP_bag, canonP_bag, canonsP_eq_map, canonsP_eq_map, mapIs,
                normal_foldr_normal fresh restrictFresh _ atomicAll, ← foldr_par_renameOuter,
                normal_renameOuter_normal fresh restrictFresh foldAtomic injective]
          | hashSet =>
              have atomIs : ∀ list : List Pattern, canonP block (.collection .hashSet list none) =
                  Prenex.atom (.collection .hashSet ((list.map (canonP block)).map (Prenex.toPattern block.toBlock))
                    none) := fun list => by
                simp [canonP, canonsP_eq_map]
              rw [atomIs, atomIs, normal_atom_renameOuter fresh restrictFresh (decompose_atom (by simp)
                (fun _ _ equal => by cases equal) (fun _ equal => by cases equal) (fun _ _ equal => by cases equal)),
                rename_collection, recanon_collection, listIs]
          | vec =>
              have atomIs : ∀ list : List Pattern, canonP block (.collection .vec list none) =
                  Prenex.atom (.collection .vec ((list.map (canonP block)).map (Prenex.toPattern block.toBlock))
                    none) := fun list => by
                simp [canonP, canonsP_eq_map]
              rw [atomIs, atomIs, normal_atom_renameOuter fresh restrictFresh (decompose_atom (by simp)
                (fun _ _ equal => by cases equal) (fun _ equal => by cases equal) (fun _ _ equal => by cases equal)),
                rename_collection, recanon_collection, listIs]
  | happly label arguments recurse =>
      refine ⟨fun object binds relabel injective => ?_, fun _ _ equal => by cases equal⟩
      have wholeFacts := canonFacts fresh restrictFresh object binds
      simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_eq_true] at object
      simp only [restrictionsBind, restrictionsBindList_eq_all, Bool.and_eq_true, List.all_eq_true] at binds
      obtain ⟨bindsHere, bindsBelow⟩ := binds
      have renamed : ∀ argument ∈ arguments, canonP block (rename relabel argument) =
          normal block ((canonP block argument).renameOuter relabel) := fun argument member =>
        (recurse argument member).1 (object argument member) (bindsBelow argument member) relabel injective
      have facts : ∀ argument ∈ arguments, CanonFacts block argument := fun argument member =>
        canonFacts fresh restrictFresh (object argument member) (bindsBelow argument member)
      rw [rename_apply]
      by_cases isRestriction : ∃ binder body, label = block.restrict ∧ arguments = [.lambda binder body]
      · -- a restriction closes its body's canonical block, and closing commutes with renaming
        obtain ⟨binder, body, rfl, rfl⟩ := isRestriction
        have lambdaObject := object _ List.mem_cons_self
        have bodyObject : isObjectPattern body = true := by simpa [isObjectPattern] using lambdaObject
        have bodyBinds : restrictionsBind block.toBlock body = true := by
          simpa [restrictionsBind] using bindsBelow _ List.mem_cons_self
        have bodyFacts := canonFacts fresh restrictFresh bodyObject bodyBinds
        have bodyRenamed := (recurse _ List.mem_cons_self).2 binder body rfl bodyObject bodyBinds (liftIndex 1 relabel)
          (liftIndex_injective injective 1)
        rw [List.map_singleton, rename_lambda, canonP_restrict, canonP_restrict, bodyRenamed,
          normal_close_normal fresh restrictFresh (renameOuter_atomic bodyFacts.atomic _), close_renameOuter,
          normal_renameOuter_normal fresh restrictFresh (close_atomic bodyFacts.atomic) injective]
      have notRestrict : label ≠ block.restrict := by
        intro same
        have notLambda : ∀ binder body, arguments ≠ [.lambda binder body] := fun binder body equal =>
          isRestriction ⟨binder, body, same, equal⟩
        rw [bindsAt_other notLambda, same] at bindsHere
        simp at bindsHere
      by_cases isUnit : label = block.unit ∧ arguments = []
      · obtain ⟨rfl, rfl⟩ := isUnit
        rw [List.map_nil, canonP_unit, nil_renameOuter, normal_nil]
      by_cases isReplicate : ∃ argument, (∀ binder body, argument ≠ .lambda binder body) ∧
          label = block.replicate ∧ arguments = [argument]
      · -- a replication collects its molecules, and collecting commutes with renaming
        obtain ⟨argument, notLambda, rfl, rfl⟩ := isReplicate
        have argumentFacts := facts argument List.mem_cons_self
        have entriesAtomic : (Prenex.mk 0 (replicatedOf block (canonicalOf block) (canonP block argument))).Atomic
            block.toBlock := fun component member =>
          replicated_atomic fresh restrictFresh (replicatedOf_replicated component member)
        rw [List.map_singleton, canonP_replicate (rename_notLambda notLambda), canonP_replicate notLambda,
          renamed argument List.mem_cons_self,
          normal_replicatedOf_normal multisetFresh fresh restrictFresh (renameOuter_atomic argumentFacts.atomic relabel),
          normal_replicatedOf_renameOuter multisetFresh fresh restrictFresh argumentFacts.atomic injective,
          normal_renameOuter_normal fresh restrictFresh entriesAtomic injective]
      by_cases isEmpty : ∃ argument, (∀ binder body, argument ≠ .lambda binder body) ∧ arguments = [argument] ∧
          label ∈ block.emptyUnits ∧ canonP block argument = Prenex.nil
      · -- an empty named multiset stays inaction
        obtain ⟨argument, notLambda, rfl, listed, empty⟩ := isEmpty
        have notReplicate : label ≠ block.replicate := fun same => fresh (same ▸ listed)
        have renamedEmpty : canonP block (rename relabel argument) = Prenex.nil := by
          rw [renamed argument List.mem_cons_self, empty, nil_renameOuter, normal_nil]
        rw [List.map_singleton, canonP_empty listed notReplicate (rename_notLambda notLambda) renamedEmpty,
          canonP_empty listed notReplicate notLambda empty, nil_renameOuter, normal_nil]
      -- any other application is one component, its arguments read from canonical blocks renamed outside
      have notReplicated : ∀ argument, (∀ binder body, argument ≠ .lambda binder body) →
          ¬ (label = block.replicate ∧ arguments = [argument]) := fun argument notLambda equal =>
        isReplicate ⟨argument, notLambda, equal.1, equal.2⟩
      have notEmpty : ∀ argument, (∀ binder body, argument ≠ .lambda binder body) → arguments = [argument] →
          label ∈ block.emptyUnits → canonP block argument ≠ Prenex.nil := fun argument notLambda equal listed empty =>
        isEmpty ⟨argument, notLambda, equal, listed, empty⟩
      have atomIs := canonP_atomCase object notRestrict isUnit notReplicated notEmpty
      have renamedObject : ∀ argument ∈ arguments.map (rename relabel), isObjectPattern argument = true := by
        intro argument member
        obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
        rw [isObjectPattern_rename]
        exact object original inOriginal
      have renamedAtomIs := canonP_atomCase (block := block) (label := label)
        (arguments := arguments.map (rename relabel)) renamedObject notRestrict
        (fun equal => isUnit ⟨equal.1, List.map_eq_nil_iff.mp equal.2⟩)
        (fun argument notLambda equal => by
          obtain ⟨original, rfl, rfl⟩ := map_rename_eq_singleton equal.2
          exact notReplicated original (rename_notLambda_iff.mp notLambda) ⟨equal.1, rfl⟩)
        (fun argument notLambda equal listed nil => by
          obtain ⟨original, rfl, rfl⟩ := map_rename_eq_singleton equal
          have originalFacts := facts original List.mem_cons_self
          have notNil := notEmpty original (rename_notLambda_iff.mp notLambda) rfl listed
          have components := components_ne_nil_of_used originalFacts.used notNil
          have renamedComponents : ((canonP block original).renameOuter relabel).components ≠ [] := by
            simpa [Prenex.renameOuter] using components
          have kept := normal_components_ne_nil fresh restrictFresh
            (renameOuter_atomic originalFacts.atomic relabel) renamedComponents
          rw [renamed original List.mem_cons_self] at nil
          rw [nil] at kept
          exact kept rfl)
      have componentAtomic : decompose block.toBlock (.apply label (arguments.map fun argument =>
          objectArgument block label (canonP block argument))) = Prenex.atom (.apply label (arguments.map
            fun argument => objectArgument block label (canonP block argument))) := by
        have atoms := wholeFacts.atomic
        rw [atomIs] at atoms
        exact atoms _ (List.mem_singleton_self _)
      have listIs : (arguments.map (rename relabel)).map (fun argument =>
            objectArgument block label (canonP block argument)) =
          ((arguments.map fun argument => objectArgument block label (canonP block argument)).map
            (rename relabel)).map (partOf block label) := by
        simp only [List.map_map]
        exact List.map_congr_left fun argument member => by
          simp only [Function.comp_apply]
          rw [renamed argument member, partOf_rename_objectArgument notRestrict (facts argument member).atomic
            (facts argument member).used]
      rw [renamedAtomIs, atomIs, normal_atom_renameOuter fresh restrictFresh componentAtomic, rename_apply,
        recanon_apply, listIs]

include multisetFresh in
/-- **Renaming an object term whose restrictions bind renames its canonical block**, up to the canonical form. -/
theorem canonP_rename {pattern : Pattern} (object : isObjectPattern pattern = true)
    (binds : restrictionsBind block.toBlock pattern = true) {relabel : Nat → Nat} (injective : Function.Injective relabel) :
    canonP block (rename relabel pattern) = normal block ((canonP block pattern).renameOuter relabel) :=
  (canonP_rename_and multisetFresh fresh restrictFresh pattern).1 object binds relabel injective

end Equivariance

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
