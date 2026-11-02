import Mettapedia.Logic.HOL.ContextualInductionSchema
import Mettapedia.Logic.HOL.IndexedConstructorRowClauses

/-!
# Closing original-row clauses into the guarded constructor method

The payload condition is the actual strengthened child condition, including
inactive padding. Original-field clauses for that condition give the exact
closed method consumed by indexed induction. The clauses remain obligations
on the source methods; no arbitrary-condition method is substituted for them.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    (signature : Contextual Const Γ)
    (predicate : Term Const Γ (signature.space ⇒ .prop))
    (children : Term Const Γ (signature.number ⇒ signature.space))

theorem childPredicate_subst (images : Subst Const Γ Ξ) :
    HOL.subst images (signature.childPredicate predicate children) =
      (signature.subst images).childPredicate (HOL.subst images predicate) (HOL.subst images children) := by
  have under {type bound : Ty Base} (term : Term Const Γ type) :
      HOL.subst (Subst.lift (σ := bound) images) (HOL.subst (Subst.ofRename Rename.weaken) term) =
        HOL.subst (Subst.ofRename (Rename.weaken (σ := bound))) (HOL.subst images term) := by
    rw [subst_ofRename, subst_ofRename]
    exact subst_weaken images term
  simp only [childPredicate, HOL.subst, subst_childConditions, Contextual.subst,
    subst_weaken, Subst.lift]
  unfold childConditions
  simp only [under]

end Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms

open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    {constructors : ConstructorPrograms Const Γ} (positions : PositionPrograms constructors)
    {space : Ty Base} (bottom : Term Const Γ space)
    (construct : Term Const Γ
      (constructors.number ⇒ payloadType constructors.fields ⇒ (constructors.number ⇒ space) ⇒ space))
    (property : Term Const Γ (space ⇒ constructors.index ⇒ .prop))

def strengthened : Term Const Γ (space ⇒ .prop) :=
  PredicateFixedPoint.intersection (positions.contextual bottom construct).least
    (IndexedPredicateInduction.lift (constructors.rootProgram construct) property)

def methodScope : Subst Const Γ (positions.contextual bottom construct).constructorContext :=
  Subst.ofRename (positions.contextual bottom construct).constructorRenaming

def methodRow (occurrence : Fin constructors.fields.length) :
    Formula Const (positions.contextual bottom construct).constructorContext :=
  let signature := positions.contextual bottom construct
  let images : Subst Const Γ signature.constructorContext := positions.methodScope bottom construct
  (constructors.subst images).rowClause (HOL.subst images construct) signature.constructorChildren
    (signature.constructorScope.childPredicate
      (weaken (weaken (weaken (positions.strengthened bottom construct property)))) signature.constructorChildren)
    (weaken (weaken (weaken property))) occurrence

variable {assumptions : List (Formula Const Γ)}

def methodFromRows
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (clauses : ∀ occurrence, ProofSyntax Const
      (weakenHyps (σ := constructors.number ⇒ space)
        (weakenHyps (σ := payloadType constructors.fields) (weakenHyps (σ := constructors.number) assumptions)))
      (positions.methodRow bottom construct property occurrence)) :
    ProofSyntax Const assumptions ((positions.contextual bottom construct).closedMethod
      (positions.strengthened bottom construct property)
      (IndexedPredicateInduction.lift (constructors.rootProgram construct) property)) := by
  let signature := positions.contextual bottom construct
  let images : Subst Const Γ signature.constructorContext := positions.methodScope bottom construct
  let predicate := positions.strengthened bottom construct property
  let condition := signature.constructorScope.childPredicate
    (weaken (weaken (weaken predicate))) signature.constructorChildren
  let childHyp := signature.constructorScope.childConditions
    (weaken (weaken (weaken predicate))) signature.constructorPayload signature.constructorChildren
  let shapeHyp := signature.constructorScope.shapeAt signature.constructorTag signature.constructorPayload
  apply signature.closeMethod
  apply positions.constructorMethod_of_cases bottom construct predicate property injectivity
  exact (constructors.subst images).casesOfClauses (HOL.subst images construct) signature.constructorChildren
    condition (weaken (weaken (weaken property)))
    (fun occurrence => ((clauses occurrence).prepend childHyp).prepend shapeHyp)

theorem methodFromRows_free
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (clauses : ∀ occurrence, ProofSyntax Const
      (weakenHyps (σ := constructors.number ⇒ space)
        (weakenHyps (σ := payloadType constructors.fields) (weakenHyps (σ := constructors.number) assumptions)))
      (positions.methodRow bottom construct property occurrence))
    (injectivityFree : injectivity.FunctionExtensionalityFree)
    (clausesFree : ∀ occurrence, (clauses occurrence).FunctionExtensionalityFree) :
    (positions.methodFromRows bottom construct property injectivity clauses).FunctionExtensionalityFree := by
  unfold methodFromRows
  apply RecursiveSpacePredicate.Contextual.closeMethod_free
  apply constructorMethod_of_cases_free
  · exact injectivityFree
  · apply ConstructorPrograms.casesOfClauses_free
    intro occurrence
    apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    exact clausesFree occurrence

def inductionFromRows
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (clauses : ∀ occurrence, ProofSyntax Const
      (weakenHyps (σ := constructors.number ⇒ space)
        (weakenHyps (σ := payloadType constructors.fields) (weakenHyps (σ := constructors.number) assumptions)))
      (positions.methodRow bottom construct property occurrence))
    (point : Term Const Γ space) (index : Term Const Γ constructors.index)
    (member : ProofSyntax Const assumptions
      (.app (.app ((positions.contextual bottom construct).memberProgram (constructors.rootProgram construct)) point) index)) :
    ProofSyntax Const assumptions (.app (.app property point) index) :=
  (positions.contextual bottom construct).indexedFromClosedMethod (constructors.rootProgram construct) property point index
    (positions.methodFromRows bottom construct property injectivity clauses) member

theorem inductionFromRows_free
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (clauses : ∀ occurrence, ProofSyntax Const
      (weakenHyps (σ := constructors.number ⇒ space)
        (weakenHyps (σ := payloadType constructors.fields) (weakenHyps (σ := constructors.number) assumptions)))
      (positions.methodRow bottom construct property occurrence))
    (point : Term Const Γ space) (index : Term Const Γ constructors.index)
    (member : ProofSyntax Const assumptions
      (.app (.app ((positions.contextual bottom construct).memberProgram (constructors.rootProgram construct)) point) index))
    (injectivityFree : injectivity.FunctionExtensionalityFree)
    (clausesFree : ∀ occurrence, (clauses occurrence).FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree) :
    (positions.inductionFromRows bottom construct property injectivity clauses point index member).FunctionExtensionalityFree :=
  (positions.contextual bottom construct).indexedFromClosedMethod_free _ _ _ _ _ _
    (positions.methodFromRows_free bottom construct property injectivity clauses injectivityFree clausesFree) memberFree

#print axioms RecursiveSpacePredicate.Contextual.childPredicate_beta_free
#print axioms methodFromRows
#print axioms methodFromRows_free
#print axioms inductionFromRows_free

end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
