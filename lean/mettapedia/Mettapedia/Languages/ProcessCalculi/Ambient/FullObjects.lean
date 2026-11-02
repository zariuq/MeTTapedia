import Mettapedia.Languages.ProcessCalculi.Ambient.FullEquivalences

/-!
# Chains of ambient laws through object processes

The shapes of the ambient calculus's laws (`AmbShape`) read through object terms (`ambientShapes`): the shapes of its
blocks with replication do, and the boundary law relates an ambient over a restriction to the restriction over the
ambient, keeping pending substitutions and its shape with tails closed, and between typed object processes it is one
instance of the law. So a chain of laws between object processes passes through object processes only
(`ambient_objectChain`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Full

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc coreSignature commTerms capRule)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern hasType_apply_inversion)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (ProcEquiv BaseContext HoleType ObjectChain ObjectShapes LawShape
  closeTails closeTailsList substFree substFreeList closeTails_rename substFree_rename liftBVars_eq_rename
  shape_objectChain restrict_typed)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (declaredInstanceAt_of_applyEquationAt)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType amb_inv)

theorem closeTails_lift (pattern : Pattern) : closeTails (liftBVars 0 1 pattern) = liftBVars 0 1 (closeTails pattern) := by
  rw [liftBVars_eq_rename, closeTails_rename, ← liftBVars_eq_rename]

theorem substFree_lift (pattern : Pattern) : substFree (liftBVars 0 1 pattern) = substFree pattern := by
  rw [liftBVars_eq_rename, substFree_rename]

/-- **Every constructor but those of capability terms makes processes**: names are variables only. -/
theorem apply_type {free : FreeTypeContext} {bound : List TypeExpr} {label : String} {arguments : List Pattern}
    {type : TypeExpr} (notCap : label ∉ ["CapIn", "CapOut", "CapOpen", "CapEps", "CapPath"])
    (typed : HasType ambientCoreCalc free bound (.apply label arguments) type) : type = procType := by
  obtain ⟨rule, member, rfl, -, typeIs, -⟩ := hasType_apply_inversion typed
  rw [typeIs]
  simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> first | rfl | simp at notCap

/-- **The boundary law between typed object processes is one instance of it.** -/
theorem boundary_objectChain {free : FreeTypeContext} {bound : List TypeExpr} {name body : Pattern}
    (nameTyped : HasType ambientCoreCalc free bound name nameType)
    (bodyTyped : HasType ambientCoreCalc free (nameType :: bound) body procType)
    (sourceObject : isObjectPattern (.apply "AAmb" [name, .apply "ANu" [.lambda none body]]) = true)
    (targetObject : isObjectPattern (.apply "ANu" [.lambda none (.apply "AAmb" [liftBVars 0 1 name, body])]) = true) :
    ObjectChain ambientCoreCalc free bound procType (.apply "AAmb" [name, .apply "ANu" [.lambda none body]])
      (.apply "ANu" [.lambda none (.apply "AAmb" [liftBVars 0 1 name, body])]) := by
  have nameScoped : name.isWellScopedAt bound.length = true := nameTyped.isWellScopedAt
  have bodyScoped : body.isWellScopedAt (1 + bound.length) = true := by
    simpa [Nat.add_comm] using bodyTyped.isWellScopedAt
  have liftedTyped : HasType ambientCoreCalc free (nameType :: bound) (liftBVars 0 1 name) nameType := by
    simpa using Mettapedia.GSLT.LanguageDef.RestrictionBlocks.lift_typed (language := ambientCoreCalc)
      (inner := []) (inserted := [nameType]) (outer := bound) nameTyped
  have member : ambientBoundary ∈ ambientCoreCalc.equations := List.mem_append_right _ (List.mem_singleton_self _)
  exact ObjectChain.ofInstance ⟨0, .declared (orientation := .forward) (ambient := bound.length) member rfl
    (declaredInstanceAt_of_applyEquationAt (boundary_instance nameScoped bodyScoped))⟩
    (amb_typed nameTyped (restrict_typed (block := ambientBlock) bodyTyped))
    (restrict_typed (block := ambientBlock) (amb_typed liftedTyped bodyTyped)) sourceObject targetObject

/-- **A shape keeps its shape with its tails closed.** -/
theorem AmbShape.closeTailed {source target : Pattern} (shape : AmbShape source target) :
    AmbShape (closeTails source) (closeTails target) := by
  cases shape with
  | law shape => exact .law shape.closeTailed
  | boundary name binder body =>
      have closed := AmbShape.boundary (closeTails name) binder (closeTails body)
      rw [← closeTails_lift] at closed
      simpa [closeTails, closeTailsList] using closed
  | boundaryReverse name binder body =>
      have closed := AmbShape.boundaryReverse (closeTails name) binder (closeTails body)
      rw [← closeTails_lift] at closed
      simpa [closeTails, closeTailsList] using closed

/-- **A shape keeps pending substitutions.** -/
theorem AmbShape.sameSubst {source target : Pattern} (shape : AmbShape source target) :
    substFree source = substFree target := by
  cases shape with
  | law shape => exact (shape.keeps (by decide) (by decide) (by decide) (by decide) (by decide)).sameSubst
  | boundary name binder body =>
      simp only [substFree, substFreeList, substFree_lift, Bool.and_true]
  | boundaryReverse name binder body =>
      simp only [substFree, substFreeList, substFree_lift, Bool.and_true]

/-- **A shape between typed object terms at a hole is a chain through object terms.** -/
theorem AmbShape.objectChain {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {type : TypeExpr} (hole : HoleType ambientCoreCalc ambientRepBlock.toBlock type) {source target : Pattern}
    (shape : AmbShape source target) (sourceTyped : HasType ambientCoreCalc free bound source type)
    (targetTyped : HasType ambientCoreCalc free bound target type) (sourceObject : isObjectPattern source = true)
    (targetObject : isObjectPattern target = true) :
    ObjectChain ambientCoreCalc free bound type source target := by
  cases shape with
  | law shape => exact shape_objectChain context hole shape sourceTyped targetTyped sourceObject targetObject
  | boundary name binder body =>
      obtain rfl := apply_type (by simp) sourceTyped
      obtain ⟨nameTyped, restrictionTyped⟩ := amb_inv sourceTyped
      obtain ⟨bodyTyped, -, rfl⟩ := coreSignature.restriction_typed restrictionTyped
      exact boundary_objectChain nameTyped bodyTyped sourceObject targetObject
  | boundaryReverse name binder body =>
      obtain rfl := apply_type (by simp) sourceTyped
      obtain ⟨-, -, rfl⟩ := coreSignature.restriction_typed sourceTyped
      obtain ⟨nameTyped, restrictionTyped⟩ := amb_inv targetTyped
      obtain ⟨bodyTyped, -, -⟩ := coreSignature.restriction_typed restrictionTyped
      exact .symm _ _ (boundary_objectChain nameTyped bodyTyped targetObject sourceObject)

/-- **The shapes of the ambient calculus's laws read through object terms.** -/
theorem ambientShapes : ObjectShapes ambientCoreCalc ambientRepBlock AmbShape where
  generator generator := ambient_generator_shape generator
  sameSubst shape := shape.sameSubst
  notLambda shape := .inl shape.notLambda.1
  closeTailed shape := shape.closeTailed
  chain context hole shape := shape.objectChain context hole

/-- **A chain of ambient laws between object processes passes through object processes only.** -/
theorem ambient_objectChain {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {first second : Pattern} (equivalent : ProcEquiv ambientCoreCalc ambientBlock free bound first second)
    (firstObject : isObjectPattern first = true) (secondObject : isObjectPattern second = true) :
    ObjectChain ambientCoreCalc free bound procType first second :=
  ambientShapes.objectChain_of_objects context equivalent firstObject secondObject

end Mettapedia.Languages.ProcessCalculi.Ambient.Full
