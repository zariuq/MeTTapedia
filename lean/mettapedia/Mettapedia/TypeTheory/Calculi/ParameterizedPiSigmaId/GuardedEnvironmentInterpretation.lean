import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.GuardedApplicationSpines
import Mettapedia.Logic.HOL.PredicateContextInstantiation

/-!
# Retained source proofs in independently represented target contexts

Source typing remains in its original guarded context. A typed HOL
substitution may interpret that context in a target of another size. Actual
proofs of the variable guards and closed root occurrences earn the target
membership proof. Existential elimination opens a fresh guarded value only
inside its continuation; no global witness is selected.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading

open Mettapedia.Logic
open Presentation TypedEquality.Annotated HOL.PredicateContexts
universe u v
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}
    {R : Rules Head} {P : ChurchRules R} {lex : LexicalReading Head Base Const}
    {Γ Ξ : HOL.Ctx Base} {roots : List (HOL.ClosedFormula Const)}
    {target : List (HOL.Formula Const Ξ)}

namespace GuardedContext

private def rootImages (images : HOL.Subst Const Γ Ξ)
    (rootProofs : HOL.ProofSyntax.HypothesisSubstitution (assumptions roots Ξ) target) :
    HOL.ProofSyntax.HypothesisSubstitution ((assumptions roots Γ).map (HOL.subst images)) target :=
  fun occurrence => by
    let chosen : Fin (assumptions roots Ξ).length := occurrence.cast (by simp [assumptions])
    apply HOL.ProofSyntax.castIndices rfl ?_ (rootProofs chosen)
    simp only [assumptions, List.get_eq_getElem, List.getElem_map, chosen, Fin.val_cast,
      HOL.subst_weakenCtx]

private theorem rootImages_free (images : HOL.Subst Const Γ Ξ)
    (rootProofs : HOL.ProofSyntax.HypothesisSubstitution (assumptions roots Ξ) target)
    (free : ∀ occurrence, (rootProofs occurrence).FunctionExtensionalityFree) :
    ∀ occurrence, (rootImages images rootProofs occurrence).FunctionExtensionalityFree := by
  intro occurrence
  simpa only [rootImages, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using
    free (occurrence.cast (by simp [assumptions]))

def realizeProof (context : GuardedContext P lex Γ) (images : HOL.Subst Const Γ Ξ)
    (guards : context.telescope.Realizes images target)
    (rootProofs : HOL.ProofSyntax.HypothesisSubstitution (assumptions roots Ξ) target)
    {formula : HOL.Formula Const Γ}
    (proof : HOL.ProofSyntax Const (context.hypotheses roots) formula) :
    HOL.ProofSyntax Const target (HOL.subst images formula) := by
  let supplied := HOL.ProofSyntax.HypothesisSubstitution.append
    ((assumptions roots Γ).map (HOL.subst images))
    (context.telescope.hypotheses.map (HOL.subst images)) target
    (rootImages images rootProofs) guards.hypotheses
  apply HOL.ProofSyntax.substituteHypothesesCached supplied
  exact HOL.ProofSyntax.castIndices List.map_append rfl (proof.subst images)

theorem realizeProof_free (context : GuardedContext P lex Γ) (images : HOL.Subst Const Γ Ξ)
    (guards : context.telescope.Realizes images target)
    (rootProofs : HOL.ProofSyntax.HypothesisSubstitution (assumptions roots Ξ) target)
    {formula : HOL.Formula Const Γ}
    (proof : HOL.ProofSyntax Const (context.hypotheses roots) formula)
    (guardsFree : ∀ {type} (index : HOL.Var Γ type), (guards index).FunctionExtensionalityFree)
    (rootsFree : ∀ occurrence, (rootProofs occurrence).FunctionExtensionalityFree)
    (proofFree : proof.FunctionExtensionalityFree) :
    (context.realizeProof images guards rootProofs proof).FunctionExtensionalityFree := by
  unfold realizeProof
  rw [HOL.ProofSyntax.substituteHypothesesCached_eq]
  apply HOL.ProofSyntax.substituteHypotheses_free
  · simpa only [HOL.ProofSyntax.functionExtensionalityFree_castIndices,
      HOL.ProofSyntax.functionExtensionalityFree_subst] using proofFree
  · exact HOL.ProofSyntax.HypothesisSubstitution.append_free _ _ _ _ _
      (rootImages_free images rootProofs rootsFree) (Telescope.Realizes.hypotheses_free guards guardsFree)

private def weakenRoots {carrier : HOL.Ty Base}
    (rootProofs : HOL.ProofSyntax.HypothesisSubstitution (assumptions roots Ξ) target)
    (guard : HOL.Formula Const (carrier :: Ξ)) :
    HOL.ProofSyntax.HypothesisSubstitution (assumptions roots (carrier :: Ξ))
      (guard :: HOL.weakenHyps target) := fun occurrence => by
  let chosen : Fin (assumptions roots Ξ).length := occurrence.cast (by simp [assumptions])
  apply HOL.ProofSyntax.castIndices rfl ?_ ((rootProofs chosen).renameShared HOL.Rename.weaken |>.prepend guard)
  simp only [assumptions, List.get_eq_getElem, List.getElem_map, chosen, Fin.val_cast,
    HOL.weakenCtx_cons, HOL.weaken]

private theorem weakenRoots_free {carrier : HOL.Ty Base}
    (rootProofs : HOL.ProofSyntax.HypothesisSubstitution (assumptions roots Ξ) target)
    (guard : HOL.Formula Const (carrier :: Ξ))
    (free : ∀ occurrence, (rootProofs occurrence).FunctionExtensionalityFree) :
    ∀ occurrence, (weakenRoots rootProofs guard occurrence).FunctionExtensionalityFree := by
  intro occurrence
  simpa only [weakenRoots, HOL.ProofSyntax.prepend, HOL.ProofSyntax.renameShared_eq, HOL.ProofSyntax.functionExtensionalityFree_castIndices,
    HOL.ProofSyntax.functionExtensionalityFree_mono, HOL.ProofSyntax.functionExtensionalityFree_rename] using
    free (occurrence.cast (by simp [assumptions]))

def eliminateWitness (context : GuardedContext P lex Γ) (images : HOL.Subst Const Γ Ξ)
    (guards : context.telescope.Realizes images target)
    (rootProofs : HOL.ProofSyntax.HypothesisSubstitution (assumptions roots Ξ) target)
    {sourceType : CTm Head Γ.length} {carrier : HOL.Ty Base}
    (predicate : HOL.Term Const Γ (.arr carrier .prop)) (reading : Reads lex sourceType predicate)
    (formed : CIsType P context.source sourceType)
    (present : HOL.ProofSyntax Const target
      (.ex (.app (HOL.weaken (HOL.subst images predicate)) (.var .vz))))
    {goal : HOL.Formula Const Γ}
    (continuation : HOL.ProofSyntax Const ((context.snoc predicate reading formed).hypotheses roots) (HOL.weaken goal)) :
    HOL.ProofSyntax Const target (HOL.subst images goal) := by
  let guard := HOL.Term.app (HOL.weaken (HOL.subst images predicate)) (.var .vz)
  have body := (context.snoc predicate reading formed).realizeProof (HOL.Subst.lift images)
    (guards.liftUnderGuard predicate) (weakenRoots rootProofs guard) continuation
  exact .exE present (HOL.ProofSyntax.castIndices rfl (HOL.subst_weaken images goal) body)

theorem eliminateWitness_free (context : GuardedContext P lex Γ) (images : HOL.Subst Const Γ Ξ)
    (guards : context.telescope.Realizes images target)
    (rootProofs : HOL.ProofSyntax.HypothesisSubstitution (assumptions roots Ξ) target)
    {sourceType : CTm Head Γ.length} {carrier : HOL.Ty Base}
    (predicate : HOL.Term Const Γ (.arr carrier .prop)) (reading : Reads lex sourceType predicate)
    (formed : CIsType P context.source sourceType)
    (present : HOL.ProofSyntax Const target (.ex (.app (HOL.weaken (HOL.subst images predicate)) (.var .vz))))
    {goal : HOL.Formula Const Γ}
    (continuation : HOL.ProofSyntax Const ((context.snoc predicate reading formed).hypotheses roots) (HOL.weaken goal))
    (guardsFree : ∀ {type} (index : HOL.Var Γ type), (guards index).FunctionExtensionalityFree)
    (rootsFree : ∀ occurrence, (rootProofs occurrence).FunctionExtensionalityFree)
    (presentFree : present.FunctionExtensionalityFree) (continuationFree : continuation.FunctionExtensionalityFree) :
    (context.eliminateWitness images guards rootProofs predicate reading formed present continuation).FunctionExtensionalityFree := by
  unfold eliminateWitness
  constructor
  · exact presentFree
  · apply (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact realizeProof_free _ _ _ _ continuation
      (Telescope.Realizes.liftUnderGuard_free guards predicate guardsFree)
      (weakenRoots_free rootProofs _ rootsFree) continuationFree

end GuardedContext

namespace GuardedRealizer

def realize {context : GuardedContext P lex Γ} {source type : CTm Head Γ.length} {carrier : HOL.Ty Base}
    (value : GuardedRealizer roots context source type carrier) (images : HOL.Subst Const Γ Ξ)
    (guards : context.telescope.Realizes images target)
    (rootProofs : HOL.ProofSyntax.HypothesisSubstitution (assumptions roots Ξ) target) :
    HOL.ProofSyntax Const target (.app (HOL.subst images value.predicate) (HOL.subst images value.term)) :=
  context.realizeProof images guards rootProofs value.member

theorem realize_free {context : GuardedContext P lex Γ} {source type : CTm Head Γ.length} {carrier : HOL.Ty Base}
    (value : GuardedRealizer roots context source type carrier) (images : HOL.Subst Const Γ Ξ)
    (guards : context.telescope.Realizes images target)
    (rootProofs : HOL.ProofSyntax.HypothesisSubstitution (assumptions roots Ξ) target)
    (guardsFree : ∀ {type} (index : HOL.Var Γ type), (guards index).FunctionExtensionalityFree)
    (rootsFree : ∀ occurrence, (rootProofs occurrence).FunctionExtensionalityFree) (valueFree : value.Free) :
    (value.realize images guards rootProofs).FunctionExtensionalityFree :=
  context.realizeProof_free images guards rootProofs value.member guardsFree rootsFree valueFree

end GuardedRealizer

#print axioms GuardedContext.realizeProof_free
#print axioms GuardedContext.eliminateWitness_free
#print axioms GuardedRealizer.realize_free

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
