import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationReference
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationSoundness
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationCompleteness

/-!
# Chains of laws through object terms, with replication

A raw law of replication matches a bag without reading the matched term's tail, so a chain of laws between object
terms may pass through terms with an open tail. Reading every term of a chain through its object reading
(`closeTails`) gives a chain between the same object ends that passes through object terms only
(`objectChain_of_sortedEquiv`):

- closing tails keeps typing (`HasType.closeTails`), and keeps each shape of a law, its tails closed
  (`LawShape.closeTailed`);
- a shape with closed tails, between typed object terms, is a law instance, or two (`shape_objectChain`): the laws of
  replication read raw, the laws of the blocks read through their declarations, the laws of the bag derived; at the
  argument of a named multiset only a reordering of the bag can stand.

The argument reads only the shapes of a language's laws (`ObjectShapes`), so it serves any language whose laws have
shapes with these properties: the replication theory's (`lawShapes`), or that theory with more laws.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList HasType ArgumentsHaveTypes
  ElementsHaveType FreeTypeContext MatchesParameterRepresentation)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationContextStep EquationEquiv)

/-! ## Typing survives closing tails -/

theorem matchesParameterRepresentation_closeTails (parameter : TermParam) (argument : Pattern)
    (represented : MatchesParameterRepresentation parameter argument) :
    MatchesParameterRepresentation parameter (closeTails argument) := by
  cases parameter <;> cases argument <;> simp_all [closeTails]
  all_goals first
    | trivial
    | (rename_i binders _; cases binders <;> simp_all [MatchesParameterRepresentation])

mutual
  /-- **Closing tails keeps typing**: the type of a collection does not read its tail. -/
  theorem _root_.Mettapedia.GSLT.LanguageDef.WellSorted.HasType.closeTails {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr} (typed : HasType language free bound pattern type) :
      HasType language free bound (RestrictionBlocks.closeTails pattern) type := by
    cases typed with
    | bvar present => exact .bvar present
    | fvar present => exact .fvar present
    | constructor member notBare argumentsTyped =>
        rw [RestrictionBlocks.closeTails, closeTailsList_eq_map]
        exact .constructor member notBare argumentsTyped.closeTails
    | lambda bodyTyped =>
        rw [RestrictionBlocks.closeTails]
        exact .lambda bodyTyped.closeTails
    | multiLambda bodyTyped =>
        rw [RestrictionBlocks.closeTails]
        exact .multiLambda bodyTyped.closeTails
    | subst bodyTyped replacementTyped =>
        rw [RestrictionBlocks.closeTails]
        exact .subst bodyTyped.closeTails replacementTyped.closeTails
    | collection elementsTyped =>
        rw [RestrictionBlocks.closeTails, closeTailsList_eq_map]
        exact .collection elementsTyped.closeTails
    | collectionConstructor member shape elementsTyped =>
        rw [RestrictionBlocks.closeTails, closeTailsList_eq_map]
        exact .collectionConstructor member shape elementsTyped.closeTails

  theorem _root_.Mettapedia.GSLT.LanguageDef.WellSorted.ArgumentsHaveTypes.closeTails {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound arguments parameters) :
      ArgumentsHaveTypes language free bound (arguments.map RestrictionBlocks.closeTails) parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation parameterType argumentTyped rest =>
        exact .cons (matchesParameterRepresentation_closeTails _ _ representation) parameterType
          argumentTyped.closeTails rest.closeTails

  theorem _root_.Mettapedia.GSLT.LanguageDef.WellSorted.ElementsHaveType.closeTails {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
      {elements : List Pattern} {type : TypeExpr} (typed : ElementsHaveType language free bound elements type) :
      ElementsHaveType language free bound (elements.map RestrictionBlocks.closeTails) type := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped rest => exact .cons elementTyped.closeTails rest.closeTails
end

/-! ## Closing tails keeps each shape -/

section Shapes

variable {block : ReplicationBlock}

theorem closeTails_replicate (process : Pattern) :
    closeTails (.apply block.replicate [process]) = .apply block.replicate [closeTails process] := by
  simp [closeTails_apply]

/-- **Closing tails keeps each shape**, its tails closed. -/
theorem LawShape.closeTailed {source target : Pattern} (shape : LawShape block source target) :
    LawShape block (closeTails source) (closeTails target) := by
  cases shape with
  | restrictionNil binder =>
      simp only [closeTails_apply, closeTails_lambda, List.map_cons, List.map_nil]
      exact .restrictionNil binder
  | exchange outerBinder innerBinder body =>
      simp only [closeTails_apply, closeTails_lambda, List.map_cons, List.map_nil, closeTails_rename]
      exact .exchange outerBinder innerBinder _
  | @extrusion members selected inside binder body chosen =>
      simp only [closeTails_apply, closeTails_lambda, closeTails_collection, List.map_cons, List.map_nil]
      have inside' : selected < (members.map closeTails).length := by simpa using inside
      have chosen' : (members.map closeTails)[selected] = .apply block.restrict [.lambda binder (closeTails body)] := by
        rw [List.getElem_map, chosen]
        simp [closeTails_apply, closeTails_lambda]
      have shape := LawShape.extrusion (block := block) inside' chosen'
      rw [map_eraseIdx, List.map_map] at shape
      have commute : closeTails ∘ liftBVars 0 1 = liftBVars 0 1 ∘ closeTails := funext closeTails_lift
      rw [List.map_map, commute]
      exact shape
  | @extrusionReverse binder members selected inside originals erased =>
      simp only [closeTails_apply, closeTails_lambda, closeTails_collection, List.map_cons, List.map_nil]
      have inside' : selected < (members.map closeTails).length := by simpa using inside
      have erased' : (members.map closeTails).eraseIdx selected = (originals.map closeTails).map (liftBVars 0 1) := by
        rw [map_eraseIdx, erased, List.map_map, List.map_map]
        exact List.map_congr_left fun original _ => closeTails_lift original
      have shape := LawShape.extrusionReverse (block := block) (binder := binder) inside' erased'
      simpa only [List.getElem_map] using shape
  | @emptyUnit label listed binder =>
      simp only [closeTails_apply, closeTails_lambda, closeTails_collection, List.map_cons, List.map_nil]
      exact .emptyUnit listed binder
  | unfold process rest =>
      simp only [closeTails_collection, List.map_cons, List.map_nil, closeTails_replicate]
      exact .unfold _ none
  | unfoldSwap process rest =>
      simp only [closeTails_collection, List.map_cons, List.map_nil, closeTails_replicate]
      exact .unfoldSwap _ none
  | replicationNil =>
      simp only [closeTails_apply, List.map_cons, List.map_nil]
      exact .replicationNil
  | twice process =>
      simp only [closeTails_replicate]
      exact .twice _
  | par first second rest swapped =>
      cases swapped <;>
        simp only [closeTails_replicate, closeTails_collection, List.map_cons, List.map_nil, Bool.false_eq_true,
          if_false, if_true] <;>
        first
          | exact .par (closeTails first) (closeTails second) none false
          | exact .par (closeTails first) (closeTails second) none true
  | parReverse first second rest swapped =>
      cases swapped <;>
        simp only [closeTails_replicate, closeTails_collection, List.map_cons, List.map_nil, Bool.false_eq_true,
          if_false, if_true] <;>
        first
          | exact .parReverse (closeTails first) (closeTails second) none false
          | exact .parReverse (closeTails first) (closeTails second) none true
  | idempotent process rest =>
      simp only [closeTails_collection, List.map_cons, List.map_nil, closeTails_replicate]
      exact .idempotent _ none
  | bagPerm permutation =>
      simp only [closeTails_collection]
      exact .bagPerm (permutation.map _)
  | flatten pre inner post =>
      simp only [closeTails_collection, List.map_append, List.map_cons]
      exact .flatten _ _ _
  | singleton notLambda =>
      simp only [closeTails_collection, List.map_cons, List.map_nil]
      exact .singleton (closeTails_notLambda notLambda)
  | unitElim pre post =>
      simp only [closeTails_collection, List.map_append, List.map_cons, closeTails_apply, List.map_nil]
      exact .unitElim _ _
  | emptyBag =>
      simp only [closeTails_collection, closeTails_apply, List.map_nil]
      exact .emptyBag

end Shapes

/-! ## Chains through object terms -/

open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationInstance DerivedInstance equationContextStep_fill
  readsRaw_of_none declaredInstanceAt_of_applyEquationAt)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

/-- **A chain of laws through object terms** of a type. -/
def ObjectChain (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr) (type : TypeExpr) :
    Pattern → Pattern → Prop :=
  Relation.EqvGen fun first second =>
    SortedStep language free bound type first second ∧ isObjectPattern first = true ∧ isObjectPattern second = true

namespace ObjectChain

variable {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr}

theorem toSortedEquiv {first second : Pattern} (chain : ObjectChain language free bound type first second) :
    SortedEquiv language free bound type first second :=
  Relation.EqvGen.mono (fun _ _ step => step.1) _ _ chain

theorem ofInstance {first second : Pattern}
    (witness : EquationInstance (engineBasePremises RelationEnv.empty) language first second)
    (firstTyped : HasType language free bound first type) (secondTyped : HasType language free bound second type)
    (firstObject : isObjectPattern first = true) (secondObject : isObjectPattern second = true) :
    ObjectChain language free bound type first second :=
  .rel _ _ ⟨⟨.inContext .hole (.inl witness), firstTyped, secondTyped⟩, firstObject, secondObject⟩

theorem ofDerived {first second : Pattern} (witness : DerivedInstance language first second)
    (firstTyped : HasType language free bound first type) (secondTyped : HasType language free bound second type)
    (firstObject : isObjectPattern first = true) (secondObject : isObjectPattern second = true) :
    ObjectChain language free bound type first second :=
  .rel _ _ ⟨⟨.inContext .hole (.inr witness), firstTyped, secondTyped⟩, firstObject, secondObject⟩

/-- **A context of the right type carries a chain through object terms**, when it keeps object terms object
terms. -/
theorem fill {holeBound : List TypeExpr} {holeType : TypeExpr} (context : OneHoleContext)
    (rebuild : ∀ filling, HasType language free holeBound filling holeType →
      HasType language free bound (context.fill filling) type)
    (objects : ∀ filling, isObjectPattern filling = true → isObjectPattern (context.fill filling) = true)
    {first second : Pattern} (chain : ObjectChain language free holeBound holeType first second) :
    ObjectChain language free bound type (context.fill first) (context.fill second) := by
  induction chain with
  | rel _ _ step =>
      exact .rel _ _ ⟨⟨equationContextStep_fill context step.1.step, rebuild _ step.1.firstTyped,
        rebuild _ step.1.secondTyped⟩, objects _ step.2.1, objects _ step.2.2⟩
  | refl => exact .refl _
  | symm _ _ _ recurse => exact .symm _ _ recurse
  | trans _ _ _ _ _ left right => exact .trans _ _ _ left right

end ObjectChain

/-! ## A shape between object terms is a chain through object terms -/

section Language

variable {language : LanguageDef} {block : ReplicationBlock}

open Mettapedia.OSLF.MeTTaIL.Match (matchPattern matchArgs mergeBindings matchBag applyBindings)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff)

section Signature

variable [replication : ReplicationSignature language block]

omit [ReplicationSignature language block] in
/-- An object collection has no tail. -/
theorem collection_tail_none {kind : CollType} {elements : List Pattern} {tail : Option String}
    (object : isObjectPattern (.collection kind elements tail) = true) : tail = none := by
  simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_iff_eq_none] at object
  exact object.1

include replication in
/-- **A shape between typed object terms of a base sort is a chain through object terms**: one instance of a law, or
a reordering and an instance. -/
theorem shape_objectChain_base {free : FreeTypeContext} {bound : List TypeExpr} {sort : String}
    {source target : Pattern} (shape : LawShape block source target)
    (sourceTyped : HasType language free bound source (.base sort))
    (targetTyped : HasType language free bound target (.base sort))
    (sourceObject : isObjectPattern source = true) (targetObject : isObjectPattern target = true) :
    ObjectChain language free bound (.base sort) source target := by
  have signature := replication.toBlockSignature
  cases shape with
  | restrictionNil binder =>
      exact .ofInstance ⟨0, .forward (initialBindings := []) (finalBindings := []) signature.nil_mem
        (readsRaw_of_none rfl) (by simp [restrictionNilOf, matchPattern, matchArgs, mergeBindings]) (.nil _)
        (by simp [restrictionNilOf, applyBindings])⟩ sourceTyped targetTyped sourceObject targetObject
  | exchange outerBinder innerBinder body =>
      obtain ⟨outerBody, -, rfl⟩ := signature.restriction_typed sourceTyped
      obtain ⟨bodyTyped, -, rfl⟩ := signature.restriction_typed outerBody
      obtain ⟨swappedOuter, -, -⟩ := signature.restriction_typed targetTyped
      obtain ⟨swappedTyped, -, -⟩ := signature.restriction_typed swappedOuter
      have wellScoped : body.isWellScopedAt (2 + bound.length) = true := by
        have := Mettapedia.GSLT.LanguageDef.WellSorted.HasType.isWellScopedAt bodyTyped
        simp only [List.length_cons] at this
        rwa [show 2 + bound.length = bound.length + 1 + 1 by omega]
      have swappedScoped : (rename swapInner body).isWellScopedAt (2 + bound.length) = true := by
        have := Mettapedia.GSLT.LanguageDef.WellSorted.HasType.isWellScopedAt swappedTyped
        simp only [List.length_cons] at this
        rwa [show 2 + bound.length = bound.length + 1 + 1 by omega]
      exact .ofInstance ⟨0, .declared (orientation := .forward) (ambient := bound.length) signature.exchange_mem rfl
        (declaredInstanceAt_of_applyEquationAt (exchange_instance wellScoped swappedScoped))⟩
        sourceTyped targetTyped sourceObject targetObject
  | @extrusion members selected inside binder body chosen =>
      obtain ⟨-, -, membersTyped⟩ := signature.bag_members sourceTyped
      have chosenTyped := elementsHaveType_iff.mp membersTyped _ (List.getElem_mem inside)
      rw [chosen] at chosenTyped
      obtain ⟨bodyTyped, -, rfl⟩ := signature.restriction_typed chosenTyped
      have bodyScoped : body.isWellScopedAt (1 + bound.length) = true := by
        simpa [Nat.add_comm] using Mettapedia.GSLT.LanguageDef.WellSorted.HasType.isWellScopedAt bodyTyped
      have membersScoped := Mettapedia.GSLT.LanguageDef.WellSorted.HasType.isWellScopedAt sourceTyped
      have othersScoped : (Pattern.collection .hashBag (members.eraseIdx selected) none).isWellScopedAt
          bound.length = true := by
        simp only [Pattern.isWellScopedAt,
          Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff] at membersScoped ⊢
        exact fun member inside' => membersScoped member (List.mem_of_mem_eraseIdx inside')
      exact .ofInstance ⟨0, .declared (orientation := .forward) (ambient := bound.length) signature.extrusion_mem rfl
        (declaredInstanceAt_of_applyEquationAt
          (extrusion_instance_at inside chosen bodyScoped othersScoped membersScoped))⟩
        sourceTyped targetTyped sourceObject targetObject
  | @extrusionReverse binder members selected inside originals erased =>
      obtain ⟨bagTyped, -, rfl⟩ := signature.restriction_typed sourceTyped
      obtain ⟨-, -, membersTyped⟩ := signature.bag_members bagTyped
      have permutation := perm_getElem_eraseIdx members selected inside
      rw [erased] at permutation
      have selectedTyped := elementsHaveType_iff.mp membersTyped _ (List.getElem_mem inside)
      have middleMembers : ∀ member ∈ members[selected] :: originals.map (liftBVars 0 1),
          HasType language free (.base block.name :: bound) member (.base block.proc) := fun member inside' =>
        elementsHaveType_iff.mp membersTyped member (permutation.symm.subset inside')
      have middleBag := signature.bag_typed (rest := none) (elementsHaveType_iff.mpr middleMembers)
      have middleTyped := signature.restrict_typed middleBag
      obtain ⟨-, sortIs, -⟩ := signature.restriction_typed sourceTyped
      cases sortIs
      have bagObject : isObjectPattern (.collection .hashBag members none) = true := by
        simpa [isObjectPattern, isObjectPatternList] using sourceObject
      have middleBagObject : isObjectPattern
          (.collection .hashBag (members[selected] :: originals.map (liftBVars 0 1)) none) = true := by
        simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_none, true_and] at bagObject ⊢
        rw [Mettapedia.GSLT.LanguageDef.BagNormalForm.isObjectPatternList_iff] at bagObject ⊢
        exact fun member inside' => bagObject member (permutation.symm.subset inside')
      have middleObject : isObjectPattern (.apply block.restrict [.lambda none
          (.collection .hashBag (members[selected] :: originals.map (liftBVars 0 1)) none)]) = true := by
        simpa [isObjectPattern, isObjectPatternList] using middleBagObject
      -- reorder inside the restriction
      have reordered : ObjectChain language free bound (.base block.proc) (.apply block.restrict [.lambda none
          (.collection .hashBag members none)]) (.apply block.restrict [.lambda none
            (.collection .hashBag (members[selected] :: originals.map (liftBVars 0 1)) none)]) := by
        have inside' := ObjectChain.ofDerived (language := language) (free := free) (bound := .base block.name :: bound)
          (type := .base block.proc)
          (Mettapedia.GSLT.LanguageDef.EquationSemantics.DerivedInstance.bagPerm_of_sorted ⟨free, _, bagTyped⟩ permutation)
          bagTyped middleBag bagObject middleBagObject
        have filled := ObjectChain.fill (bound := bound) (type := .base block.proc)
          (.apply block.restrict [] (.lambda none .hole) []) (fun _ typed => signature.restrict_typed typed)
          (fun _ object => by simpa [OneHoleContext.fill, isObjectPattern, isObjectPatternList] using object) inside'
        simpa [OneHoleContext.fill] using filled
      -- the extrusion, read backward
      have selectedRestricted := elementsHaveType_iff.mp (signature.bag_members targetTyped).2.2 _ List.mem_cons_self
      obtain ⟨selectedBody, -, -⟩ := signature.restriction_typed selectedRestricted
      have selectedScoped : members[selected].isWellScopedAt (1 + bound.length) = true := by
        simpa [Nat.add_comm] using Mettapedia.GSLT.LanguageDef.WellSorted.HasType.isWellScopedAt selectedBody
      have originalsScoped : (Pattern.collection .hashBag originals none).isWellScopedAt bound.length = true := by
        have targetScoped := Mettapedia.GSLT.LanguageDef.WellSorted.HasType.isWellScopedAt targetTyped
        simp only [Pattern.isWellScopedAt,
          Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff] at targetScoped ⊢
        exact fun member inside' => targetScoped member (List.mem_cons_of_mem _ inside')
      have extruded := ObjectChain.ofInstance (language := language) (free := free) (bound := bound)
        (type := .base block.proc)
        ⟨0, .declared (orientation := .forward) (ambient := bound.length) signature.extrusion_mem rfl
          (declaredInstanceAt_of_applyEquationAt (extrusion_instance selectedScoped originalsScoped))⟩
        targetTyped middleTyped targetObject middleObject
      exact .trans _ _ _ reordered (.symm _ _ extruded)
  | @emptyUnit label listed binder =>
      obtain ⟨-, -, rfl⟩ := signature.restriction_typed targetTyped
      exact .ofInstance ⟨0, .declared (orientation := .forward) (ambient := bound.length)
        (signature.emptyUnit_mem listed) rfl (declaredInstanceAt_of_applyEquationAt emptyUnit_instance)⟩
        sourceTyped targetTyped sourceObject targetObject
  | unfold process rest =>
      cases collection_tail_none sourceObject
      exact .symm _ _ (ObjectChain.ofInstance ⟨0, .forward (initialBindings := [("P", process)])
        (finalBindings := [("P", process)]) (ReplicationSignature.unfold_mem (block := block)) (readsRaw_of_none rfl)
        (by simp [replicationUnfoldOf, matchPattern, matchArgs, mergeBindings]) (.nil _)
        (by simp [replicationUnfoldOf, applyBindings])⟩ targetTyped sourceTyped targetObject sourceObject)
  | unfoldSwap process rest =>
      cases collection_tail_none sourceObject
      obtain ⟨-, sortIs, membersTyped⟩ := signature.bag_members sourceTyped
      subst sortIs
      have swapped : [Pattern.apply block.replicate [process], process].Perm [process, .apply block.replicate [process]] :=
        List.Perm.swap _ _ []
      have middleTyped := signature.bag_typed (rest := none) (elementsHaveType_iff.mpr fun member inside' =>
        elementsHaveType_iff.mp membersTyped member (swapped.symm.subset inside'))
      have middleObject : isObjectPattern (.collection .hashBag [process, .apply block.replicate [process]] none) =
          true := by
        simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at sourceObject ⊢
        exact ⟨sourceObject.1, sourceObject.2.2, sourceObject.2.1⟩
      have reordered := ObjectChain.ofDerived (language := language) (free := free) (bound := bound)
        (Mettapedia.GSLT.LanguageDef.EquationSemantics.DerivedInstance.bagPerm_of_sorted ⟨free, bound, sourceTyped⟩
          swapped) sourceTyped middleTyped sourceObject middleObject
      exact .trans _ _ _ reordered (.symm _ _ (ObjectChain.ofInstance ⟨0, .forward (initialBindings := [("P", process)])
        (finalBindings := [("P", process)]) (ReplicationSignature.unfold_mem (block := block)) (readsRaw_of_none rfl)
        (by simp [replicationUnfoldOf, matchPattern, matchArgs, mergeBindings]) (.nil _)
        (by simp [replicationUnfoldOf, applyBindings])⟩ targetTyped middleTyped targetObject middleObject))
  | replicationNil =>
      exact .ofInstance ⟨0, .forward (initialBindings := []) (finalBindings := [])
        (ReplicationSignature.nil_mem (block := block)) (readsRaw_of_none rfl)
        (by simp [replicationNilOf, matchPattern, matchArgs, mergeBindings]) (.nil _)
        (by simp [replicationNilOf, applyBindings])⟩ sourceTyped targetTyped sourceObject targetObject
  | twice process =>
      exact .ofInstance ⟨0, .forward (initialBindings := [("P", process)]) (finalBindings := [("P", process)])
        (ReplicationSignature.twice_mem (block := block)) (readsRaw_of_none rfl)
        (by simp [replicationTwiceOf, matchPattern, matchArgs, mergeBindings]) (.nil _)
        (by simp [replicationTwiceOf, applyBindings])⟩ sourceTyped targetTyped sourceObject targetObject
  | par first second rest swapped =>
      have tailNone : rest = none := by
        simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at sourceObject
        exact Option.isNone_iff_eq_none.mp sourceObject.1
      subst tailNone
      cases swapped <;>
      exact .ofInstance ⟨0, .forward (initialBindings := [("Q", second), ("P", first)])
        (finalBindings := [("Q", second), ("P", first)]) (ReplicationSignature.par_mem (block := block))
        (readsRaw_of_none rfl)
        (by simp [replicationParOf, matchPattern, matchArgs, mergeBindings, matchBag]) (.nil _)
        (by simp [replicationParOf, applyBindings])⟩ sourceTyped targetTyped sourceObject targetObject
  | parReverse first second rest swapped =>
      cases collection_tail_none sourceObject
      cases swapped <;>
      exact .ofInstance ⟨0, .reverse (initialBindings := [("Q", second), ("P", first)])
        (finalBindings := [("Q", second), ("P", first)]) (ReplicationSignature.par_mem (block := block))
        (readsRaw_of_none rfl)
        (by simp [replicationParOf, matchPattern, matchArgs, mergeBindings, matchBag]) (.nil _)
        (by simp [replicationParOf, applyBindings])⟩ sourceTyped targetTyped sourceObject targetObject
  | idempotent process rest =>
      cases collection_tail_none sourceObject
      exact .ofInstance ⟨0, .forward (initialBindings := [("P", process)]) (finalBindings := [("P", process)])
        (ReplicationSignature.idempotent_mem (block := block)) (readsRaw_of_none rfl)
        (by simp [replicationIdempotentOf, matchPattern, matchArgs, mergeBindings, matchBag]) (.nil _)
        (by simp [replicationIdempotentOf, applyBindings])⟩ sourceTyped targetTyped sourceObject targetObject
  | bagPerm permutation =>
      exact .ofDerived (Mettapedia.GSLT.LanguageDef.EquationSemantics.DerivedInstance.bagPerm_of_sorted
        ⟨free, bound, sourceTyped⟩ permutation) sourceTyped targetTyped sourceObject targetObject
  | flatten pre inner post =>
      obtain ⟨-, sortIs, -⟩ := signature.bag_members sourceTyped
      subst sortIs
      exact .ofDerived (signature.flatten sourceTyped) sourceTyped targetTyped sourceObject targetObject
  | singleton notLambda =>
      obtain ⟨-, sortIs, membersTyped⟩ := signature.bag_members sourceTyped
      subst sortIs
      exact .ofDerived (signature.singleton (elementsHaveType_iff.mp membersTyped _ List.mem_cons_self))
        sourceTyped targetTyped sourceObject targetObject
  | unitElim pre post =>
      obtain ⟨-, sortIs, -⟩ := signature.bag_members sourceTyped
      subst sortIs
      exact .ofDerived (signature.unitElim sourceTyped) sourceTyped targetTyped sourceObject targetObject
  | emptyBag =>
      exact .ofDerived signature.emptyUnit sourceTyped targetTyped sourceObject targetObject

include replication in
/-- **At the argument of a named multiset only a reordering of the bag stands**: every other shape has an
application on one side, or a member of the process sort among members of another. -/
theorem shape_objectChain_multiset {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {type : TypeExpr} (multiset : MultisetType language block.toBlock type) {source target : Pattern}
    (shape : LawShape block source target) (sourceTyped : HasType language free bound source type)
    (targetTyped : HasType language free bound target type) (sourceObject : isObjectPattern source = true)
    (targetObject : isObjectPattern target = true) :
    ObjectChain language free bound type source target := by
  have signature := replication.toBlockSignature
  obtain ⟨sort, other, rfl, rule, member, parameter, parameterMember, occurs⟩ := multiset
  have membersTyped : ∀ {elements : List Pattern},
      HasType language free bound (.collection .hashBag elements none) (.collection .hashBag (.base sort)) →
      ∀ element ∈ elements, HasType language free bound element (.base sort) := by
    intro elements typed element inside
    rcases Mettapedia.GSLT.LanguageDef.WellSorted.hasType_collection_inversion typed with
      ⟨elementType, typeIs, elementsTyped⟩ | ⟨_, _, _, _, _, typeIs, _⟩
    · simp only [TypeExpr.collection.injEq, true_and] at typeIs
      subst typeIs
      exact elementsHaveType_iff.mp elementsTyped element inside
    · cases typeIs
  have notProcess : ∀ {label : String} {arguments : List Pattern},
      HasType language free bound (.apply label arguments) (.base sort) →
      (label = block.restrict ∨ label = block.unit) → False := by
    intro label arguments typed isBlock
    obtain ⟨rule', member', labelIs, -, typeIs, -⟩ := Mettapedia.GSLT.LanguageDef.WellSorted.hasType_apply_inversion typed
    simp only [TypeExpr.base.injEq] at typeIs
    rcases isBlock with rfl | rfl
    · exact other (typeIs.trans (signature.restrictShape rule' member' labelIs.symm).1)
    · exact other (typeIs.trans (signature.unitShape rule' member' labelIs.symm))
  cases shape with
  | restrictionNil => exact (apply_not_collection sourceTyped).elim
  | exchange => exact (apply_not_collection sourceTyped).elim
  | @extrusion members selected inside binder body chosen =>
      have selectedTyped := membersTyped sourceTyped _ (List.getElem_mem inside)
      rw [chosen] at selectedTyped
      exact (notProcess selectedTyped (.inl rfl)).elim
  | extrusionReverse => exact (apply_not_collection sourceTyped).elim
  | emptyUnit => exact (apply_not_collection sourceTyped).elim
  | unfold => exact (apply_not_collection targetTyped).elim
  | unfoldSwap => exact (apply_not_collection targetTyped).elim
  | replicationNil => exact (apply_not_collection sourceTyped).elim
  | twice => exact (apply_not_collection sourceTyped).elim
  | par => exact (apply_not_collection sourceTyped).elim
  | parReverse => exact (apply_not_collection targetTyped).elim
  | idempotent => exact (apply_not_collection targetTyped).elim
  | bagPerm permutation =>
      exact .ofDerived (.bagPerm member ⟨parameter, parameterMember, .base sort, occurs, free, bound, sourceTyped⟩
        permutation) sourceTyped targetTyped sourceObject targetObject
  | flatten pre inner post =>
      have innerTyped := membersTyped sourceTyped (.collection .hashBag inner none) (by simp)
      exact absurd (signature.bag_members innerTyped).2.1 other
  | singleton notLambda =>
      obtain ⟨kind', elements, rest, rfl⟩ := collection_of_typed context targetTyped targetObject
      have elementTyped := membersTyped sourceTyped _ (List.mem_singleton_self _)
      exact absurd (signature.bag_members elementTyped).2.1 other
  | unitElim pre post =>
      have unitTyped := membersTyped sourceTyped (.apply block.unit []) (by simp)
      exact (notProcess unitTyped (.inr rfl)).elim
  | emptyBag => exact (apply_not_collection targetTyped).elim

include replication in
/-- **A shape between typed object terms at a hole is a chain through object terms.** -/
theorem shape_objectChain {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {type : TypeExpr} (hole : HoleType language block.toBlock type) {source target : Pattern}
    (shape : LawShape block source target) (sourceTyped : HasType language free bound source type)
    (targetTyped : HasType language free bound target type) (sourceObject : isObjectPattern source = true)
    (targetObject : isObjectPattern target = true) :
    ObjectChain language free bound type source target := by
  rcases hole with ⟨sort, rfl⟩ | multiset
  · exact shape_objectChain_base shape sourceTyped targetTyped sourceObject targetObject
  · exact shape_objectChain_multiset context multiset shape sourceTyped targetTyped sourceObject targetObject

/-! ## The object reading of a chain -/

open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationGenerator)

/-- **Shapes of a language's laws that read through object terms**: every generator of the static theory relates its
two terms by a shape, one way or the other; a shape keeps pending substitutions, has no abstraction on either side,
keeps its shape with its tails closed, and between typed object terms at a hole is a chain through object terms. -/
structure ObjectShapes (language : LanguageDef) (block : ReplicationBlock) (Shape : Pattern → Pattern → Prop) :
    Prop where
  generator : ∀ {base : BasePremiseEvaluator} {source target : Pattern},
    EquationGenerator base language source target → Shape source target ∨ Shape target source
  sameSubst : ∀ {source target : Pattern}, Shape source target → substFree source = substFree target
  notLambda : ∀ {source target : Pattern}, Shape source target →
    (∀ binder body, source ≠ .lambda binder body) ∨ ∀ binder body, target ≠ .lambda binder body
  closeTailed : ∀ {source target : Pattern}, Shape source target → Shape (closeTails source) (closeTails target)
  chain : ∀ {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern},
    BaseContext free bound → HoleType language block.toBlock type → Shape source target →
    HasType language free bound source type → HasType language free bound target type →
    isObjectPattern source = true → isObjectPattern target = true → ObjectChain language free bound type source target

namespace ObjectShapes

variable {Shape : Pattern → Pattern → Prop}

omit [ReplicationSignature language block] in
/-- **A law in a context keeps pending substitutions.** -/
theorem substFree_step (shapes : ObjectShapes language block Shape) {base : BasePremiseEvaluator}
    {first second : Pattern} (step : EquationContextStep base language first second) :
    substFree first = substFree second := by
  cases step with
  | inContext context generator =>
      rcases shapes.generator generator with shape | shape
      · exact substFree_fill context (shapes.sameSubst shape)
      · exact substFree_fill context (shapes.sameSubst shape).symm

omit [ReplicationSignature language block] in
/-- **A chain of laws keeps pending substitutions.** -/
theorem substFree_chain (shapes : ObjectShapes language block Shape) {base : BasePremiseEvaluator}
    {first second : Pattern} (equivalent : EquationEquiv base language first second) :
    substFree first = substFree second := by
  induction equivalent with
  | rel _ _ step => exact shapes.substFree_step step
  | refl => rfl
  | symm _ _ _ same => exact same.symm
  | trans _ _ _ _ _ left right => exact left.trans right

include replication in
/-- **The object reading of a shape in a context is a chain through object terms**, when the context's filling with
the shape's side has no pending substitution and both fillings have a sort. -/
theorem shape_fill_objectChain (shapes : ObjectShapes language block Shape) {free : FreeTypeContext}
    {bound : List TypeExpr} (context : BaseContext free bound) {sort : String} (stepContext : OneHoleContext)
    {redex contractum : Pattern} (shape : Shape redex contractum ∨ Shape contractum redex)
    (firstTyped : HasType language free bound (stepContext.fill redex) (.base sort))
    (secondTyped : HasType language free bound (stepContext.fill contractum) (.base sort))
    (free' : substFree (stepContext.fill redex) = true) :
    ObjectChain language free bound (.base sort) (closeTails (stepContext.fill redex))
      (closeTails (stepContext.fill contractum)) := by
  have sameFree : substFree (stepContext.fill redex) = substFree (stepContext.fill contractum) := by
    rcases shape with shape | shape
    · exact substFree_fill stepContext (shapes.sameSubst shape)
    · exact substFree_fill stepContext (shapes.sameSubst shape).symm
  have oneNotLambda : (∀ binder body, redex ≠ .lambda binder body) ∨
      ∀ binder body, contractum ≠ .lambda binder body := by
    rcases shape with shape | shape
    · exact shapes.notLambda shape
    · exact (shapes.notLambda shape).symm
  have firstClosed := firstTyped.closeTails
  have secondClosed := secondTyped.closeTails
  have firstObject : isObjectPattern (closeTails (stepContext.fill redex)) = true := by
    rw [isObject_closeTails]; exact free'
  have secondObject : isObjectPattern (closeTails (stepContext.fill contractum)) = true := by
    rw [isObject_closeTails, ← sameFree]; exact free'
  rw [closeTails_fill] at firstClosed secondClosed firstObject secondObject ⊢
  rw [closeTails_fill]
  obtain ⟨holeBound, holeType, holeContext, holeKind, redexTyped, contractumTyped, rebuild⟩ :
      ∃ holeBound holeType, BaseContext free holeBound ∧ HoleType language block.toBlock holeType ∧
        HasType language free holeBound (closeTails redex) holeType ∧
        HasType language free holeBound (closeTails contractum) holeType ∧
        ∀ replacement, HasType language free holeBound replacement holeType →
          HasType language free bound ((closeContext stepContext).fill replacement) (.base sort) := by
    rcases oneNotLambda with notLambda | notLambda
    · exact fill_typed_pair (block := block.toBlock) _ context firstClosed secondClosed (.inl ⟨sort, rfl⟩)
        firstObject secondObject (closeTails_notLambda notLambda)
    · obtain ⟨holeBound, holeType, holeContext, holeKind, contractumTyped, redexTyped, rebuild⟩ :=
        fill_typed_pair (block := block.toBlock) _ context secondClosed firstClosed (.inl ⟨sort, rfl⟩)
          secondObject firstObject (closeTails_notLambda notLambda)
      exact ⟨holeBound, holeType, holeContext, holeKind, redexTyped, contractumTyped, rebuild⟩
  have redexObject := isObject_of_fill _ firstObject
  have contractumObject := isObject_of_fill _ secondObject
  have objects : ∀ filling, isObjectPattern filling = true →
      isObjectPattern ((closeContext stepContext).fill filling) = true := fun filling object => by
    rw [isObject_fill_congr (object.trans redexObject.symm) (closeContext stepContext)]
    exact firstObject
  rcases shape with shape | shape
  · exact ObjectChain.fill _ rebuild objects (shapes.chain holeContext holeKind (shapes.closeTailed shape) redexTyped
      contractumTyped redexObject contractumObject)
  · exact ObjectChain.fill _ rebuild objects (.symm _ _ (shapes.chain holeContext holeKind (shapes.closeTailed shape)
      contractumTyped redexTyped contractumObject redexObject))

include replication in
/-- **The object reading of a step is a chain through object terms**, when the step's terms have no pending
substitution. -/
theorem step_objectChain (shapes : ObjectShapes language block Shape) {free : FreeTypeContext}
    {bound : List TypeExpr} (context : BaseContext free bound) {sort : String} {first second : Pattern}
    (step : SortedStep language free bound (.base sort) first second) (free' : substFree first = true) :
    ObjectChain language free bound (.base sort) (closeTails first) (closeTails second) := by
  obtain ⟨stepped, firstTyped, secondTyped⟩ := step
  cases stepped with
  | @inContext stepContext redex contractum generator =>
      exact shapes.shape_fill_objectChain context stepContext (shapes.generator generator) firstTyped secondTyped free'

include replication in
/-- **The object reading of a chain of laws through terms of a sort is a chain through object terms**, when its
terms have no pending substitution: a chain between object terms passes through object terms only. -/
theorem objectChain_of_sortedEquiv (shapes : ObjectShapes language block Shape) {free : FreeTypeContext}
    {bound : List TypeExpr} (context : BaseContext free bound) {sort : String} {first second : Pattern}
    (equivalent : SortedEquiv language free bound (.base sort) first second) :
    substFree first = true → ObjectChain language free bound (.base sort) (closeTails first) (closeTails second) := by
  induction equivalent with
  | rel _ _ step => exact shapes.step_objectChain context step
  | refl => exact fun _ => .refl _
  | symm _ _ chain recurse =>
      intro free'
      have keeps := shapes.substFree_chain (SortedEquiv.toEquationEquiv chain)
      exact .symm _ _ (recurse (keeps ▸ free'))
  | trans _ _ _ left _ leftRecurse rightRecurse =>
      intro free'
      have keeps := shapes.substFree_chain (SortedEquiv.toEquationEquiv left)
      exact .trans _ _ _ (leftRecurse free') (rightRecurse (keeps ▸ free'))

include replication in
/-- **A chain of laws through terms of a sort between object terms is a chain through object terms.** -/
theorem objectChain_of_objects (shapes : ObjectShapes language block Shape) {free : FreeTypeContext}
    {bound : List TypeExpr} (context : BaseContext free bound) {sort : String} {first second : Pattern}
    (equivalent : SortedEquiv language free bound (.base sort) first second)
    (firstObject : isObjectPattern first = true) (secondObject : isObjectPattern second = true) :
    ObjectChain language free bound (.base sort) first second := by
  have chain := shapes.objectChain_of_sortedEquiv context equivalent (substFree_of_object firstObject)
  rwa [closeTails_of_object _ firstObject, closeTails_of_object _ secondObject] at chain

end ObjectShapes

end Signature

variable [laws : ReplicationLanguage language block]

include laws in
/-- **The shapes of the replication theory's laws read through object terms.** -/
theorem lawShapes : ObjectShapes language block (LawShape block) where
  generator generator := generator_lawShape (block := block) generator
  sameSubst shape := (shape.keeps_of (language := language)).sameSubst
  notLambda shape := .inl (shape.keeps_of (language := language)).sourceNotLambda
  closeTailed shape := shape.closeTailed
  chain context hole shape := shape_objectChain context hole shape

include laws in
/-- **The object reading of a step is a chain through object terms**, when the step's terms have no pending
substitution. -/
theorem step_objectChain {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {sort : String} {first second : Pattern} (step : SortedStep language free bound (.base sort) first second)
    (free' : substFree first = true) :
    ObjectChain language free bound (.base sort) (closeTails first) (closeTails second) :=
  (lawShapes (block := block)).step_objectChain context step free'

include laws in
/-- **The object reading of a chain of laws through terms of a sort is a chain through object terms**, when its
terms have no pending substitution: a chain between object terms passes through object terms only. -/
theorem objectChain_of_sortedEquiv {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {sort : String} {first second : Pattern}
    (equivalent : SortedEquiv language free bound (.base sort) first second) :
    substFree first = true → ObjectChain language free bound (.base sort) (closeTails first) (closeTails second) :=
  (lawShapes (block := block)).objectChain_of_sortedEquiv context equivalent

include laws in
/-- **Equivalent object terms of a sort are related by a chain through object terms.** -/
theorem objectChain_of_equationEquiv {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {first second : Pattern} {sort : String} (firstTyped : HasType language free bound first (.base sort))
    (secondTyped : HasType language free bound second (.base sort)) (firstObject : isObjectPattern first = true)
    (secondObject : isObjectPattern second = true) {base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator}
    (equivalent : EquationEquiv base language first second) :
    ObjectChain language free bound (.base sort) first second := by
  have chain := objectChain_of_sortedEquiv (block := block) context
    (sortedEquiv_of_equationEquiv_replication (block := block) context firstTyped secondTyped firstObject
      secondObject equivalent) (substFree_of_object firstObject)
  rwa [closeTails_of_object _ firstObject, closeTails_of_object _ secondObject] at chain

end Language

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
