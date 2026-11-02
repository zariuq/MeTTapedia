import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationLawShapes

/-!
# The canonical form with replication is complete

Equivalent object terms of a calculus with restriction and replication, their restrictions binding, have one
canonical form (`canonR_complete`), so the static theory, the laws of replication among them, is decided by the
canonical form on object terms of a sort (`equationEquiv_iff_canonR_eq`).

A chain of laws may pass through terms that are not object terms: a law of replication read raw matches a bag
without reading its tail. Along a chain, terms keep their pending substitutions and their binding restrictions, and
their object readings keep one canonical block (`equationEquiv_keeps`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList HasType FreeTypeContext
  hasType_apply_inversion hasType_collection_inversion ArgumentsHaveTypes MatchesParameterRepresentation
  matchesParameterRepresentation_abstractionNamed_iff)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationGenerator EquationInstance EquationInstanceAt
  DeclaredInstanceAt DerivedInstance EquationContextStep EquationEquiv extendClosed_closedRoot readsRaw)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator PremisesAt engineBasePremises)
open Mettapedia.OSLF.MeTTaIL.Match (matchPattern applyBindings)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

variable {block : ReplicationBlock}

/-! ## What a context keeps of its filling -/

theorem substFree_of_fill (context : OneHoleContext) {filling : Pattern}
    (free : substFree (context.fill filling) = true) : substFree filling = true := by
  induction context with
  | hole => exact free
  | apply label before inner after recurse =>
      simp only [OneHoleContext.fill, substFree_apply, List.all_append, List.all_cons, Bool.and_eq_true] at free
      exact recurse free.2.1
  | lambda binder inner recurse => exact recurse free
  | multiLambda arity binders inner recurse => exact recurse free
  | substBody inner replacement _ => simp [OneHoleContext.fill, substFree] at free
  | substReplacement body inner _ => simp [OneHoleContext.fill, substFree] at free
  | collection kind before inner after rest recurse =>
      simp only [OneHoleContext.fill, substFree_collection, List.all_append, List.all_cons, Bool.and_eq_true] at free
      exact recurse free.2.1

theorem restrictionsBind_of_fill (base : Block) (context : OneHoleContext) {filling : Pattern}
    (binds : restrictionsBind base (context.fill filling) = true) : restrictionsBind base filling = true := by
  induction context with
  | hole => exact binds
  | apply label before inner after recurse =>
      simp only [OneHoleContext.fill, restrictionsBind_apply, List.all_append, List.all_cons,
        Bool.and_eq_true] at binds
      exact recurse binds.2.2.1
  | lambda binder inner recurse => exact recurse binds
  | multiLambda arity binders inner recurse => exact recurse binds
  | substBody inner replacement recurse =>
      simp only [OneHoleContext.fill, restrictionsBind, Bool.and_eq_true] at binds
      exact recurse binds.1
  | substReplacement body inner recurse =>
      simp only [OneHoleContext.fill, restrictionsBind, Bool.and_eq_true] at binds
      exact recurse binds.2
  | collection kind before inner after rest recurse =>
      simp only [OneHoleContext.fill, restrictionsBind_collection, List.all_append, List.all_cons,
        Bool.and_eq_true] at binds
      exact recurse binds.2.1

section Language

variable {language : LanguageDef} [laws : ReplicationLanguage language block]

include laws in
/-- **Every generator of the static theory keeps the object reading's canonical block.** -/
theorem generator_keeps {base : BasePremiseEvaluator} {source target : Pattern}
    (generator : EquationGenerator base language source target) : Keeps block source target :=
  (generator_lawShape generator).elim (fun shape => shape.keeps_of (language := language))
    (fun shape => (shape.keeps_of (language := language)).symm)

/-! ## Along a chain of laws -/

/-- **A context keeps what its filling keeps**: pending substitutions, binding restrictions and the object reading's
canonical block. -/
theorem keeps_fill (context : OneHoleContext) {redex contractum : Pattern} (keeps : Keeps block redex contractum) :
    substFree (context.fill redex) = substFree (context.fill contractum) ∧
      restrictionsBind block.toBlock (context.fill redex) = restrictionsBind block.toBlock (context.fill contractum) ∧
      (substFree (context.fill redex) = true → restrictionsBind block.toBlock (context.fill redex) = true →
        canonP block (closeTails (context.fill redex)) = canonP block (closeTails (context.fill contractum))) := by
  refine ⟨substFree_fill context keeps.sameSubst, (restrictionsBind_fill block.toBlock context keeps.sameBinds
    (LambdaAlike.of_notLambda keeps.sourceNotLambda keeps.targetNotLambda)).1, fun free binds => ?_⟩
  have fills : Fills block (closeTails redex) (closeTails contractum) :=
    ⟨keeps.canon (substFree_of_fill context free) (restrictionsBind_of_fill block.toBlock context binds),
      .inl ⟨closeTails_notLambda keeps.sourceNotLambda, closeTails_notLambda keeps.targetNotLambda⟩⟩
  have firstObject : isObjectPattern ((closeContext context).fill (closeTails redex)) = true := by
    rw [← closeTails_fill, isObject_closeTails]
    exact free
  have secondObject : isObjectPattern ((closeContext context).fill (closeTails contractum)) = true := by
    rw [← closeTails_fill, isObject_closeTails, ← substFree_fill context keeps.sameSubst]
    exact free
  rw [closeTails_fill, closeTails_fill]
  exact (fills_context (closeContext context) fills firstObject secondObject).1

include laws in
/-- **One step of the static theory** keeps pending substitutions, binding restrictions and the object reading's
canonical block. -/
theorem step_keeps {base : BasePremiseEvaluator} {first second : Pattern}
    (step : EquationContextStep base language first second) :
    substFree first = substFree second ∧
      restrictionsBind block.toBlock first = restrictionsBind block.toBlock second ∧
      (substFree first = true → restrictionsBind block.toBlock first = true →
        canonP block (closeTails first) = canonP block (closeTails second)) := by
  cases step with
  | @inContext context redex contractum generator => exact keeps_fill context (generator_keeps generator)

include laws in
/-- **Along a chain of laws**, terms keep their pending substitutions and their binding restrictions, and their
object readings keep one canonical block. -/
theorem equationEquiv_keeps {base : BasePremiseEvaluator} {first second : Pattern}
    (equivalent : EquationEquiv base language first second) :
    substFree first = substFree second ∧
      restrictionsBind block.toBlock first = restrictionsBind block.toBlock second ∧
      (substFree first = true → restrictionsBind block.toBlock first = true →
        canonP block (closeTails first) = canonP block (closeTails second)) := by
  induction equivalent with
  | rel _ _ step => exact step_keeps step
  | refl => exact ⟨rfl, rfl, fun _ _ => rfl⟩
  | symm _ _ _ recurse =>
      obtain ⟨sameFree, sameBinds, canon⟩ := recurse
      exact ⟨sameFree.symm, sameBinds.symm, fun free binds =>
        (canon (sameFree.trans free) (sameBinds.trans binds)).symm⟩
  | trans _ _ _ _ _ first second =>
      obtain ⟨firstFree, firstBinds, firstCanon⟩ := first
      obtain ⟨secondFree, secondBinds, secondCanon⟩ := second
      exact ⟨firstFree.trans secondFree, firstBinds.trans secondBinds, fun free binds =>
        (firstCanon free binds).trans (secondCanon (firstFree.symm.trans free) (firstBinds.symm.trans binds))⟩

/-! ## Completeness -/

include laws in
/-- **The canonical form with replication is complete**: equivalent object terms whose restrictions bind have one
canonical form. -/
theorem canonR_complete {base : BasePremiseEvaluator} {first second : Pattern}
    (firstObject : isObjectPattern first = true) (secondObject : isObjectPattern second = true)
    (binds : restrictionsBind block.toBlock first = true) (equivalent : EquationEquiv base language first second) :
    canonR block first = canonR block second := by
  have canon := (equationEquiv_keeps equivalent).2.2 (substFree_of_object firstObject) binds
  rw [closeTails_of_object first firstObject, closeTails_of_object second secondObject] at canon
  unfold canonR
  rw [canon]

/-- The arguments of a typed constructor are typed. -/
theorem argumentsHaveTypes_mem {free : FreeTypeContext} {bound : List TypeExpr} :
    ∀ {arguments : List Pattern} {parameters : List TermParam},
      ArgumentsHaveTypes language free bound arguments parameters →
        ∀ argument ∈ arguments, ∃ type, HasType language free bound argument type
  | [], _, _ => fun _ member => by simp at member
  | argument :: arguments, _ :: _, typed => by
      cases typed with
      | cons _ _ argumentTyped rest =>
          intro other member
          rcases List.mem_cons.mp member with rfl | inRest
          · exact ⟨_, argumentTyped⟩
          · exact argumentsHaveTypes_mem rest other inRest

include laws in
/-- **The restrictions of a typed term bind**: the restriction takes one abstraction. -/
theorem restrictionsBind_of_typed {free : FreeTypeContext} (pattern : Pattern) :
    ∀ {bound : List TypeExpr} {type : TypeExpr}, HasType language free bound pattern type →
      restrictionsBind block.toBlock pattern = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _ _ _; rfl
  | hfvar name => intro _ _ _; rfl
  | happly label arguments recurse =>
      intro bound type typed
      obtain ⟨rule, member, labelIs, -, -, argumentsTyped⟩ := hasType_apply_inversion typed
      rw [restrictionsBind_apply, Bool.and_eq_true, List.all_eq_true]
      refine ⟨?_, fun argument inArguments => ?_⟩
      · by_cases isRestrict : label = block.restrict
        · obtain ⟨-, body, params⟩ := laws.restrictShape rule member (labelIs.symm.trans isRestrict)
          rw [params] at argumentsTyped
          cases argumentsTyped with
          | cons representation _ _ rest =>
              cases rest
              obtain ⟨inner, rfl⟩ := (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp representation
              rfl
        · exact bindsAt_of_ne isRestrict arguments
      · obtain ⟨argumentType, argumentTyped⟩ := argumentsHaveTypes_mem argumentsTyped argument inArguments
        exact recurse argument inArguments argumentTyped
  | hlambda binder body recurse =>
      intro bound type typed
      cases typed with
      | lambda inner => exact recurse inner
  | hmultiLambda arity binders body recurse =>
      intro bound type typed
      cases typed with
      | multiLambda inner => exact recurse inner
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro bound type typed
      cases typed with
      | subst bodyTyped replacementTyped =>
          simp only [restrictionsBind, Bool.and_eq_true]
          exact ⟨bodyRecurse bodyTyped, replacementRecurse replacementTyped⟩
  | hcollection kind elements rest recurse =>
      intro bound type typed
      rw [restrictionsBind_collection, List.all_eq_true]
      intro element inElements
      rcases hasType_collection_inversion typed with ⟨_, _, elementsTyped⟩ | ⟨_, _, _, _, _, _, elementsTyped⟩
      · exact recurse element inElements (elementsHaveType_iff.mp elementsTyped element inElements)
      · exact recurse element inElements (elementsHaveType_iff.mp elementsTyped element inElements)

include laws in
/-- **The static theory with replication is decided by the canonical form** on object terms of a sort. -/
theorem equationEquiv_iff_canonR_eq {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {first second : Pattern} {sort : String} (firstTyped : HasType language free bound first (.base sort))
    (secondTyped : HasType language free bound second (.base sort)) (firstObject : isObjectPattern first = true)
    (secondObject : isObjectPattern second = true) :
    EquationEquiv (engineBasePremises RelationEnv.empty) language first second ↔
      canonR block first = canonR block second := by
  refine ⟨canonR_complete firstObject secondObject (restrictionsBind_of_typed (block := block) first firstTyped),
    fun equal => ?_⟩
  have firstChain := (canonR_sound (block := block) context firstTyped).2
  have secondChain := (canonR_sound (block := block) context secondTyped).2
  rw [equal] at firstChain
  exact SortedEquiv.toEquationEquiv (Relation.EqvGen.trans _ _ _ firstChain (Relation.EqvGen.symm _ _ secondChain))

include laws in
/-- **Equivalent object terms of a sort are related by a chain of laws through terms of that sort**, the laws of
replication among them. -/
theorem sortedEquiv_of_equationEquiv_replication {free : FreeTypeContext} {bound : List TypeExpr}
    (context : BaseContext free bound) {first second : Pattern} {sort : String}
    (firstTyped : HasType language free bound first (.base sort))
    (secondTyped : HasType language free bound second (.base sort)) (firstObject : isObjectPattern first = true)
    (secondObject : isObjectPattern second = true) {base : BasePremiseEvaluator}
    (equivalent : EquationEquiv base language first second) :
    SortedEquiv language free bound (.base sort) first second := by
  have equal := canonR_complete firstObject secondObject (restrictionsBind_of_typed (block := block) first firstTyped)
    equivalent
  have firstChain := (canonR_sound (block := block) context firstTyped).2
  have secondChain := (canonR_sound (block := block) context secondTyped).2
  rw [equal] at firstChain
  exact .trans _ _ _ firstChain (.symm _ _ secondChain)

end Language

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
