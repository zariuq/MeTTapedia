import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.GuardedEnvironmentInterpretation

/-!
# Binding represented values in the original guarded source context

A source binder remains typed in its original context. Its target value may
be a native expression in a context of another size. The actual membership
proof extends the guard assignment, so a retained source continuation can
use that value without inventing target DTT syntax or a source substitution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading.GuardedContext

open Mettapedia.Logic
open Presentation TypedEquality.Annotated HOL.PredicateContexts
universe u v
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}
    {R : Rules Head} {P : ChurchRules R} {lex : LexicalReading Head Base Const}
    {Γ Ξ : HOL.Ctx Base} {roots : List (HOL.ClosedFormula Const)}
    {target : List (HOL.Formula Const Ξ)}

def bindValue (context : GuardedContext P lex Γ) (images : HOL.Subst Const Γ Ξ)
    (guards : context.telescope.Realizes images target)
    (rootProofs : HOL.ProofSyntax.HypothesisSubstitution (assumptions roots Ξ) target)
    {sourceType : CTm Head Γ.length} {carrier : HOL.Ty Base}
    (predicate : HOL.Term Const Γ (.arr carrier .prop)) (reading : Reads lex sourceType predicate)
    (formed : CIsType P context.source sourceType) (value : HOL.Term Const Ξ carrier)
    (member : HOL.ProofSyntax Const target (.app (HOL.subst images predicate) value))
    {goal : HOL.Formula Const (carrier :: Γ)}
    (continuation : HOL.ProofSyntax Const ((context.snoc predicate reading formed).hypotheses roots) goal) :
    HOL.ProofSyntax Const target (HOL.subst (HOL.Subst.cons value images) goal) :=
  (context.snoc predicate reading formed).realizeProof (HOL.Subst.cons value images)
    (guards.cons predicate value member) rootProofs continuation

theorem bindValue_free (context : GuardedContext P lex Γ) (images : HOL.Subst Const Γ Ξ)
    (guards : context.telescope.Realizes images target)
    (rootProofs : HOL.ProofSyntax.HypothesisSubstitution (assumptions roots Ξ) target)
    {sourceType : CTm Head Γ.length} {carrier : HOL.Ty Base}
    (predicate : HOL.Term Const Γ (.arr carrier .prop)) (reading : Reads lex sourceType predicate)
    (formed : CIsType P context.source sourceType) (value : HOL.Term Const Ξ carrier)
    (member : HOL.ProofSyntax Const target (.app (HOL.subst images predicate) value))
    {goal : HOL.Formula Const (carrier :: Γ)}
    (continuation : HOL.ProofSyntax Const ((context.snoc predicate reading formed).hypotheses roots) goal)
    (guardsFree : ∀ {type} (index : HOL.Var Γ type), (guards index).FunctionExtensionalityFree)
    (rootsFree : ∀ occurrence, (rootProofs occurrence).FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree) (continuationFree : continuation.FunctionExtensionalityFree) :
    (context.bindValue images guards rootProofs predicate reading formed value member continuation).FunctionExtensionalityFree :=
  realizeProof_free _ _ _ _ continuation
    (Telescope.Realizes.cons_free guards predicate value member guardsFree memberFree) rootsFree continuationFree

#print axioms bindValue_free

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading.GuardedContext
