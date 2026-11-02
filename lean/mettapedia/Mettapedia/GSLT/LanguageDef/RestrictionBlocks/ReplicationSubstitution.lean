import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationCompleteness
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Closing

/-!
# Substitution in calculi with replication

The static theory of a calculus with restriction and replication is closed under substitution of terms that are no
abstractions. A substitution keeps every shape of a law (`LawShape.substituted`) and passes a context with its
assignment lifted at the hole, so along a chain of laws the substituted ends keep their pending substitutions, their
binding restrictions and one canonical block of their object readings (`equationEquiv_substitute_keeps`), whatever
terms the chain passes through. On object terms of a sort the canonical form decides the theory, so equivalent
object terms stay equivalent under a substitution of object terms of their variables' sorts
(`equationEquiv_substitute_replication`); in particular, continuations stay equivalent once a datum is received
(`sortedEquiv_instantiate_replication`). Closing a free name into a new innermost variable keeps every shape too, so
the theory is closed under binding a free name (`equationEquiv_close_replication`), as a named translation binds one.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (Assignment substitute lift single
  substitute_single_eq_instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.Substitution (instantiateBVar closeFVar liftBVars)
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern HasType FreeTypeContext)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationContextStep EquationEquiv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator engineBasePremises)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

variable {block : ReplicationBlock}

/-- The assignment reaching a hole is the assignment lifted past the context's binders. -/
theorem NoAbstractions.atHole {assignment : Assignment} (plain : NoAbstractions assignment) :
    ∀ context : OneHoleContext, NoAbstractions (ContextSubstitution.atHole assignment context)
  | .hole => plain
  | .apply _ _ inner _ => plain.atHole inner
  | .lambda _ inner => (plain.lift 1).atHole inner
  | .multiLambda arity _ inner => (plain.lift arity).atHole inner
  | .substBody inner _ => (plain.lift 1).atHole inner
  | .substReplacement _ inner => plain.atHole inner
  | .collection _ _ inner _ _ => plain.atHole inner

/-- A name, or any term that is no abstraction, received for the first variable. -/
theorem NoAbstractions.single {datum : Pattern} (notLambda : ∀ binder body, datum ≠ .lambda binder body) :
    NoAbstractions (single datum) := by
  intro index binder body
  cases index with
  | zero => exact notLambda binder body
  | succ index => exact fun same => Pattern.noConfusion same

section Language

variable {language : LanguageDef} [laws : ReplicationLanguage language block]

include laws in
/-- **A substitution keeps what one step keeps**: pending substitutions, binding restrictions and the object reading's
canonical block of the substituted ends. -/
theorem step_substitute_keeps (assignment : Assignment) (plain : NoAbstractions assignment)
    {base : BasePremiseEvaluator} {first second : Pattern} (step : EquationContextStep base language first second) :
    substFree (substitute assignment first) = substFree (substitute assignment second) ∧
      restrictionsBind block.toBlock (substitute assignment first) =
        restrictionsBind block.toBlock (substitute assignment second) ∧
      (substFree (substitute assignment first) = true →
        restrictionsBind block.toBlock (substitute assignment first) = true →
        canonP block (closeTails (substitute assignment first)) =
          canonP block (closeTails (substitute assignment second))) := by
  cases step with
  | @inContext context redex contractum generator =>
      rw [ContextSubstitution.substitute_fill, ContextSubstitution.substitute_fill]
      have plainAt := plain.atHole context
      rcases generator_lawShape (block := block) generator with shape | shape
      · exact keeps_fill _ ((shape.substituted _ plainAt).keeps_of (language := language))
      · exact keeps_fill _ ((shape.substituted _ plainAt).keeps_of (language := language)).symm

include laws in
/-- **Along a chain of laws, a substitution keeps** the pending substitutions, the binding restrictions and the object
reading's canonical block of the substituted ends. -/
theorem equationEquiv_substitute_keeps (assignment : Assignment) (plain : NoAbstractions assignment)
    {base : BasePremiseEvaluator} {first second : Pattern} (equivalent : EquationEquiv base language first second) :
    substFree (substitute assignment first) = substFree (substitute assignment second) ∧
      restrictionsBind block.toBlock (substitute assignment first) =
        restrictionsBind block.toBlock (substitute assignment second) ∧
      (substFree (substitute assignment first) = true →
        restrictionsBind block.toBlock (substitute assignment first) = true →
        canonP block (closeTails (substitute assignment first)) =
          canonP block (closeTails (substitute assignment second))) := by
  induction equivalent with
  | rel _ _ step => exact step_substitute_keeps assignment plain step
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

include laws in
/-- **The static theory with replication is closed under substitution**: equivalent object terms of a sort stay
equivalent once object terms of their variables' sorts, none an abstraction, are substituted for the variables. -/
theorem equationEquiv_substitute_replication {free : FreeTypeContext} {bound target : List TypeExpr}
    (targetContext : BaseContext free target) {assignment : Assignment}
    (assigned : SortedAssignment language free bound target assignment) (plain : NoAbstractions assignment)
    {first second : Pattern} {sort : String} (firstTyped : HasType language free bound first (.base sort))
    (secondTyped : HasType language free bound second (.base sort)) (firstObject : isObjectPattern first = true)
    (secondObject : isObjectPattern second = true) {base : BasePremiseEvaluator}
    (equivalent : EquationEquiv base language first second) :
    EquationEquiv (engineBasePremises RelationEnv.empty) language (substitute assignment first)
      (substitute assignment second) := by
  have firstTyped' := HasType.substituteBoundOnSupport firstTyped assignment
    (fun index type _ lookup => assigned.typed index type lookup)
  have secondTyped' := HasType.substituteBoundOnSupport secondTyped assignment
    (fun index type _ lookup => assigned.typed index type lookup)
  have firstObject' := isObject_substitute _ assigned.objects firstObject
  have secondObject' := isObject_substitute _ assigned.objects secondObject
  have canon := (equationEquiv_substitute_keeps (block := block) assignment plain equivalent).2.2
    (substFree_of_object firstObject') (restrictionsBind_of_typed (block := block) _ firstTyped')
  rw [closeTails_of_object _ firstObject', closeTails_of_object _ secondObject'] at canon
  refine (equationEquiv_iff_canonR_eq (block := block) targetContext firstTyped' secondTyped' firstObject'
    secondObject').mpr ?_
  unfold canonR
  rw [canon]

include laws in
/-- **Equivalent continuations stay equivalent once a datum is received**, in a calculus with replication. -/
theorem sortedEquiv_instantiate_replication {free : FreeTypeContext} {bound : List TypeExpr}
    (context : BaseContext free bound) {datum first second : Pattern} {sort datumSort : String}
    (datumTyped : HasType language free bound datum (.base datumSort)) (datumObject : isObjectPattern datum = true)
    (firstTyped : HasType language free (.base datumSort :: bound) first (.base sort))
    (secondTyped : HasType language free (.base datumSort :: bound) second (.base sort))
    (firstObject : isObjectPattern first = true) (secondObject : isObjectPattern second = true)
    {base : BasePremiseEvaluator} (equivalent : EquationEquiv base language first second) :
    EquationEquiv (engineBasePremises RelationEnv.empty) language (instantiateBVar datum first)
      (instantiateBVar datum second) := by
  have notLambda : ∀ binder body, datum ≠ .lambda binder body := by
    intro binder body same
    subst same
    cases datumTyped
  rw [← substitute_single_eq_instantiateBVar, ← substitute_single_eq_instantiateBVar]
  exact equationEquiv_substitute_replication (block := block) context (single_assignment datumTyped datumObject)
    (NoAbstractions.single notLambda) firstTyped secondTyped firstObject secondObject equivalent

/-! ## Binding a free name -/

omit [ReplicationLanguage language block] in
theorem close_replicate (name : String) (level : Nat) (process : Pattern) :
    closeFVar level name (.apply block.replicate [process]) = .apply block.replicate [closeFVar level name process] := by
  simp [closeFVar]

omit [ReplicationLanguage language block] in
/-- Closing a name makes no abstraction of a term that is none. -/
theorem closeFVar_notLambda (name : String) (level : Nat) {pattern : Pattern}
    (notLambda : ∀ binder body, pattern ≠ .lambda binder body) :
    ∀ binder body, closeFVar level name pattern ≠ .lambda binder body := by
  intro binder body same
  cases pattern with
  | lambda binder' body' => exact notLambda binder' body' rfl
  | fvar other =>
      simp only [closeFVar] at same
      split at same <;> cases same
  | bvar => simp [closeFVar] at same
  | apply => simp [closeFVar] at same
  | multiLambda => simp [closeFVar] at same
  | subst => simp [closeFVar] at same
  | collection => simp [closeFVar] at same

omit [ReplicationLanguage language block] in
/-- **Closing a free name keeps each shape**, a level deeper under each binder of the shape. -/
theorem LawShape.closed (name : String) (level : Nat) {source target : Pattern} (shape : LawShape block source target) :
    LawShape block (closeFVar level name source) (closeFVar level name target) := by
  cases shape with
  | restrictionNil binder =>
      rw [close_restriction (block := block.toBlock), close_inaction (block := block.toBlock),
        close_inaction (block := block.toBlock)]
      exact .restrictionNil binder
  | exchange outerBinder innerBinder body =>
      rw [close_restriction (block := block.toBlock), close_restriction (block := block.toBlock),
        close_restriction (block := block.toBlock), close_restriction (block := block.toBlock),
        ← rename_closeFVar name body (level + 1 + 1) swapInner (by simp [swapInner])]
      exact .exchange outerBinder innerBinder _
  | @extrusion members selected inside binder body chosen =>
      rw [close_bag, close_restriction (block := block.toBlock), close_bag, List.map_cons, List.map_map]
      have inside' : selected < (members.map (closeFVar level name)).length := by simpa using inside
      have chosen' : (members.map (closeFVar level name))[selected] =
          .apply block.restrict [.lambda binder (closeFVar (level + 1) name body)] := by
        rw [List.getElem_map]
        simp only [chosen, close_restriction (block := block.toBlock)]
      have shape := LawShape.extrusion (block := block) inside' chosen'
      rw [map_eraseIdx, List.map_map] at shape
      have commute : closeFVar (level + 1) name ∘ liftBVars 0 1 = liftBVars 0 1 ∘ closeFVar level name :=
        funext fun pattern => closeFVar_liftBVars name pattern level 0 (Nat.zero_le _)
      rw [commute]
      exact shape
  | @extrusionReverse binder members selected inside originals erased =>
      rw [close_restriction (block := block.toBlock), close_bag, close_bag, List.map_cons,
        close_restriction (block := block.toBlock)]
      have inside' : selected < (members.map (closeFVar (level + 1) name)).length := by simpa using inside
      have erased' : (members.map (closeFVar (level + 1) name)).eraseIdx selected =
          (originals.map (closeFVar level name)).map (liftBVars 0 1) := by
        rw [map_eraseIdx, erased, List.map_map, List.map_map]
        exact List.map_congr_left fun original _ => closeFVar_liftBVars name original level 0 (Nat.zero_le _)
      have shape := LawShape.extrusionReverse (block := block) (binder := binder) inside' erased'
      simpa only [List.getElem_map] using shape
  | @emptyUnit label listed binder =>
      rw [close_emptyMultiset, close_restriction (block := block.toBlock), close_inaction (block := block.toBlock)]
      exact .emptyUnit listed binder
  | unfold process rest =>
      simp only [close_bag, List.map_cons, List.map_nil, close_replicate]
      exact .unfold _ rest
  | unfoldSwap process rest =>
      simp only [close_bag, List.map_cons, List.map_nil, close_replicate]
      exact .unfoldSwap _ rest
  | replicationNil =>
      simp only [close_replicate, close_inaction (block := block.toBlock)]
      exact .replicationNil
  | twice process =>
      simp only [close_replicate]
      exact .twice _
  | par first second rest swapped =>
      cases swapped <;>
        simp only [close_replicate, close_bag, List.map_cons, List.map_nil, Bool.false_eq_true, if_false,
          if_true] <;>
        first
          | exact .par (closeFVar level name first) (closeFVar level name second) rest false
          | exact .par (closeFVar level name first) (closeFVar level name second) rest true
  | parReverse first second rest swapped =>
      cases swapped <;>
        simp only [close_replicate, close_bag, List.map_cons, List.map_nil, Bool.false_eq_true, if_false,
          if_true] <;>
        first
          | exact .parReverse (closeFVar level name first) (closeFVar level name second) rest false
          | exact .parReverse (closeFVar level name first) (closeFVar level name second) rest true
  | idempotent process rest =>
      simp only [close_bag, List.map_cons, List.map_nil, close_replicate]
      exact .idempotent _ rest
  | bagPerm permutation =>
      rw [close_bag, close_bag]
      exact .bagPerm (permutation.map _)
  | flatten pre inner post =>
      rw [close_bag, close_bag, List.map_append, List.map_cons, close_bag, List.map_append, List.map_append]
      exact .flatten _ _ _
  | singleton notLambda =>
      rw [close_bag, List.map_cons, List.map_nil]
      exact .singleton (closeFVar_notLambda name level notLambda)
  | unitElim pre post =>
      rw [close_bag, close_bag, List.map_append, List.map_cons, close_inaction (block := block.toBlock),
        List.map_append]
      exact .unitElim _ _
  | emptyBag =>
      rw [close_bag, close_inaction (block := block.toBlock), List.map_nil]
      exact .emptyBag

include laws in
/-- **Binding a free name keeps what one step keeps.** -/
theorem step_close_keeps (name : String) (level : Nat) {base : BasePremiseEvaluator} {first second : Pattern}
    (step : EquationContextStep base language first second) :
    substFree (closeFVar level name first) = substFree (closeFVar level name second) ∧
      restrictionsBind block.toBlock (closeFVar level name first) =
        restrictionsBind block.toBlock (closeFVar level name second) ∧
      (substFree (closeFVar level name first) = true →
        restrictionsBind block.toBlock (closeFVar level name first) = true →
        canonP block (closeTails (closeFVar level name first)) =
          canonP block (closeTails (closeFVar level name second))) := by
  cases step with
  | @inContext context redex contractum generator =>
      rw [OneHoleContext.closeFVar_fill, OneHoleContext.closeFVar_fill]
      rcases generator_lawShape (block := block) generator with shape | shape
      · exact keeps_fill _ ((shape.closed name _).keeps_of (language := language))
      · exact keeps_fill _ ((shape.closed name _).keeps_of (language := language)).symm

include laws in
/-- **Along a chain of laws, binding a free name keeps** what the chain keeps. -/
theorem equationEquiv_close_keeps (name : String) (level : Nat) {base : BasePremiseEvaluator} {first second : Pattern}
    (equivalent : EquationEquiv base language first second) :
    substFree (closeFVar level name first) = substFree (closeFVar level name second) ∧
      restrictionsBind block.toBlock (closeFVar level name first) =
        restrictionsBind block.toBlock (closeFVar level name second) ∧
      (substFree (closeFVar level name first) = true →
        restrictionsBind block.toBlock (closeFVar level name first) = true →
        canonP block (closeTails (closeFVar level name first)) =
          canonP block (closeTails (closeFVar level name second))) := by
  induction equivalent with
  | rel _ _ step => exact step_close_keeps name level step
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

include laws in
/-- **The static theory with replication is closed under binding a free name**: equivalent object terms of a sort
stay equivalent once a free name of a base sort becomes a new innermost bound variable. -/
theorem equationEquiv_close_replication {free : FreeTypeContext} {bound : List TypeExpr}
    (context : BaseContext free bound) {name nameSort : String} (lookup : free name = some (.base nameSort))
    {first second : Pattern} {sort : String} (firstTyped : HasType language free bound first (.base sort))
    (secondTyped : HasType language free bound second (.base sort)) (firstObject : isObjectPattern first = true)
    (secondObject : isObjectPattern second = true) {base : BasePremiseEvaluator}
    (equivalent : EquationEquiv base language first second) :
    EquationEquiv (engineBasePremises RelationEnv.empty) language (closeFVar bound.length name first)
      (closeFVar bound.length name second) := by
  have firstTyped' := firstTyped.closeFVar name (.base nameSort) lookup
  have secondTyped' := secondTyped.closeFVar name (.base nameSort) lookup
  have firstObject' : isObjectPattern (closeFVar bound.length name first) = true := by
    rw [isObject_closeFVar]; exact firstObject
  have secondObject' : isObjectPattern (closeFVar bound.length name second) = true := by
    rw [isObject_closeFVar]; exact secondObject
  have canon := (equationEquiv_close_keeps (block := block) name bound.length equivalent).2.2
    (substFree_of_object firstObject') (restrictionsBind_of_typed (block := block) _ firstTyped')
  rw [closeTails_of_object _ firstObject', closeTails_of_object _ secondObject'] at canon
  refine (equationEquiv_iff_canonR_eq (block := block) (context.snoc nameSort) firstTyped' secondTyped'
    firstObject' secondObject').mpr ?_
  unfold canonR
  rw [canon]

end Language

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
