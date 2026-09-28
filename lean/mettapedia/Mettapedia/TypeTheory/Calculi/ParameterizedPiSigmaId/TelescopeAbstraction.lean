import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedSubstitution

/-!
# Dependent telescope abstraction and checked application

Closing an equation must preserve the dependent domains of its actual context.
Abstracting that context produces a closed term and product type; applying
the abstraction through a typed context morphism recovers the simultaneous
substitution, both by typing and by directed beta computation.

These raw typing laws do not assert context or declaration formation. An
admission authority must earn those separately. The computation theorem uses
no universe-head equality, declared equation, symmetry, or conversion oracle.
-/

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TelescopeAbstraction

def closeTerm : (context : Ctx Head n) → Tm Head n → Tm Head 0
  | .nil, term => term
  | .snoc prior _, term => closeTerm prior (.lam term)

def closeType : (context : Ctx Head n) → Tm Head n → Tm Head 0
  | .nil, type => type
  | .snoc prior domain, type => closeType prior (.pi domain type)

/-- Apply arguments in lexical telescope order, not de Bruijn index order. -/
def applyClosed : (context : Ctx Head n) → Sub Head n m → Tm Head m → Tm Head m
  | .nil, _, function => function
  | .snoc prior _, sigma, function =>
      .app (applyClosed prior (fun index => sigma index.succ) function) (sigma 0)

theorem close_typed {R : Rules Head} {context : Ctx Head n}
    {term type : Tm Head n} (typing : HasType R context term type) :
    HasType R .nil (closeTerm context term) (closeType context type) := by
  induction context with
  | nil => exact typing
  | snoc prior domain ih => exact ih (.lamIntro typing)

theorem subst_empty (sigma : Sub Head 0 m) (term : Tm Head 0) :
    subst sigma term = liftClosed term := by
  change subst sigma term = rename Fin.elim0 term
  rw [← subst_renSub (rho := Fin.elim0)]
  apply subst_ext
  intro index
  exact Fin.elim0 index

theorem liftClosed_zero (term : Tm Head 0) :
    (liftClosed term : Tm Head 0) = term := by
  change rename Fin.elim0 term = term
  have emptyRenaming : (Fin.elim0 : Ren 0 0) = idRen := by
    funext index
    exact Fin.elim0 index
  rw [emptyRenaming, rename_id]

theorem subst_open (sigma : Sub Head (n + 1) m)
    (body : Tm Head (n + 1)) :
    inst0 (sigma 0) (subst (liftSub (fun index => sigma index.succ)) body) =
      subst sigma body := by
  rw [← subst_consSub, consSub_eta]

theorem subst_prior (sigma : Sub Head (n + 1) m) (term : Tm Head n) :
    subst sigma (rename wk term) = subst (fun index => sigma index.succ) term := by
  rw [subst_rename]
  rfl

theorem CtxMor.prior {R : Rules Head} {prior : Ctx Head n}
    {domain : Tm Head n} {target : Ctx Head m} {sigma : Sub Head (n + 1) m}
    (typed : Presentation.CtxMor R (.snoc prior domain) target sigma) :
    Presentation.CtxMor R prior target (fun index => sigma index.succ) := by
  intro index
  simpa only [Ctx.lookup_snoc_succ, subst_prior] using typed index.succ

/-- A function checked at the closed product type can be applied to every
argument supplied by the same typed context morphism. -/
theorem applyClosed_typed {R : Rules Head} {context : Ctx Head n}
    {target : Ctx Head m} {sigma : Sub Head n m} {type : Tm Head n}
    {function : Tm Head m}
    (typed : Presentation.CtxMor R context target sigma)
    (functionTyping : HasType R target function (liftClosed (closeType context type))) :
    HasType R target (applyClosed context sigma function) (subst sigma type) := by
  induction context with
  | nil => simpa only [applyClosed, closeType, subst_empty] using functionTyping
  | snoc prior domain ih =>
      have functionTyped := ih (CtxMor.prior typed) functionTyping
      have argumentTyped := typed 0
      simp only [Ctx.lookup_snoc_zero, subst_prior] at argumentTyped
      have application := HasType.appElim functionTyped argumentTyped
      simpa only [applyClosed, subst, subst_open] using application

/-- Pure beta/projection computation, excluding head equality and all
declaration-specific root equations. -/
abbrev BetaSteps (source target : Tm Head n) : Prop :=
  Relation.ReflTransGen (StepCore (RootComputation.empty : RootComputation Head)
    (fun _ _ => False)) source target

/-- The closed abstraction executes to the actual substituted open term.
No equality between independent implementations is assumed. -/
theorem applyClosed_beta (context : Ctx Head n) (sigma : Sub Head n m)
    (term : Tm Head n) :
    BetaSteps (applyClosed context sigma (liftClosed (closeTerm context term)))
      (subst sigma term) := by
  induction context with
  | nil => simpa only [applyClosed, closeTerm, subst_empty] using
      (Relation.ReflTransGen.refl (a := liftClosed term))
  | snoc prior domain ih =>
      have earlier := ih (sigma := fun index => sigma index.succ) (term := .lam term)
      have underApplication := earlier.lift
        (fun function : Tm Head m => Tm.app function (sigma 0))
        (fun _ _ step => StepCore.congAppFun step)
      refine Relation.ReflTransGen.tail underApplication ?_
      simpa only [subst, subst_open] using
        (StepCore.betaPi (root := (RootComputation.empty : RootComputation Head))
          (headEq := fun _ _ => False)
          (subst (liftSub (fun index => sigma index.succ)) term) (sigma 0))

/-- Substituting the target context transports the result through the same
composite morphism, without a separate equation-specific operation. -/
theorem applyClosed_subst (context : Ctx Head n) (sigma : Sub Head n m)
    (tau : Sub Head m k) (function : Tm Head m) :
    subst tau (applyClosed context sigma function) =
      applyClosed context (subComp tau sigma) (subst tau function) := by
  induction context with
  | nil => rfl
  | snoc prior domain ih =>
      simp only [applyClosed, subst, ih, subComp]
      rfl

theorem applyClosed_composite_beta (context : Ctx Head n) (sigma : Sub Head n m)
    (tau : Sub Head m k) (term : Tm Head n) :
    BetaSteps
      (subst tau (applyClosed context sigma (liftClosed (closeTerm context term))))
      (subst tau (subst sigma term)) := by
  simpa only [applyClosed_subst, subst_liftClosed, subst_subComp] using
    (applyClosed_beta context (subComp tau sigma) term)

#print axioms close_typed
#print axioms applyClosed_typed
#print axioms applyClosed_beta
#print axioms applyClosed_subst
#print axioms applyClosed_composite_beta

end TelescopeAbstraction
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
