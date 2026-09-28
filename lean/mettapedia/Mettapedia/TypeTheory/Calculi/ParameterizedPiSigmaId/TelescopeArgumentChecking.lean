import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TelescopeAbstraction

/-!
# Checking dependent arguments before simultaneous instantiation

An assignment found by matching is not a typed substitution. This executable
fold checks arguments in telescope order. Each expected domain is instantiated
with the already assigned earlier arguments, not with an independent type map.

The primitive operation checks supplied evidence. A false result means that
this evidence was not accepted; it is not a refutation of the typing claim.
Context and declaration formation remain separate admission obligations.
Accepted arguments supply the existing context morphism, which transports the
equation's actual body and displayed type and composes with later substitutions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TelescopeArgumentChecking

variable {Head Evidence : Type} {n m k : Nat}

/-- Earlier telescope arguments are checked first. The newest argument's
domain is computed using exactly that earlier assignment. -/
def checkArguments
    (check : Tm Head m → Tm Head m → Evidence → Bool) :
    {n : Nat} → Ctx Head n → Sub Head n m → (Fin n → Evidence) → Bool
  | _, .nil, _, _ => true
  | _, .snoc prior domain, sigma, evidence =>
      checkArguments check prior (fun index => sigma index.succ)
        (fun index => evidence index.succ) &&
      check (sigma 0) (subst (fun index => sigma index.succ) domain)
        (evidence 0)

@[simp] theorem checkArguments_cons
    (check : Tm Head m → Tm Head m → Evidence → Bool)
    (prior : Ctx Head n) (domain : Tm Head n) (sigma : Sub Head n m)
    (argument : Tm Head m) (earlier : Fin n → Evidence) (newest : Evidence) :
    checkArguments check (.snoc prior domain) (consSub argument sigma)
        (Fin.cases newest earlier) =
      (checkArguments check prior sigma earlier &&
        check argument (subst sigma domain) newest) :=
  rfl

/-- The dependent fold checks precisely the domains displayed by lookup in
the original telescope. Weakening introduces no extra argument dependency. -/
theorem checkArguments_eq_true_iff
    (check : Tm Head m → Tm Head m → Evidence → Bool)
    (context : Ctx Head n) (sigma : Sub Head n m) (evidence : Fin n → Evidence) :
    checkArguments check context sigma evidence = true ↔
      ∀ index, check (sigma index) (subst sigma (Ctx.lookup context index))
        (evidence index) = true := by
  induction context with
  | nil =>
      constructor
      · intro _ index
        exact Fin.elim0 index
      · intro _
        rfl
  | snoc prior domain inductionHypothesis =>
      have weakening (body : Tm Head _) :
          subst sigma (rename wk body) =
            subst (fun index => sigma index.succ) body := by
        exact subst_rename sigma wk body
      simp only [checkArguments, Bool.and_eq_true, inductionHypothesis]
      constructor
      · rintro ⟨earlier, newest⟩ index
        refine Fin.cases ?_ ?_ index
        · simpa only [Ctx.lookup_snoc_zero, weakening] using newest
        · intro index
          simpa only [Ctx.lookup_snoc_succ, weakening] using earlier index
      · intro all
        constructor
        · intro index
          simpa only [Ctx.lookup_snoc_succ, weakening] using all index.succ
        · simpa only [Ctx.lookup_snoc_zero, weakening] using all 0

/-- Primitive evidence checks, rather than raw matching, earn every component
of the typed simultaneous substitution. -/
theorem checkArguments_sound
    {R : Rules Head} {target : Ctx Head m}
    (check : Tm Head m → Tm Head m → Evidence → Bool)
    (checkSound : ∀ argument domain evidence,
      check argument domain evidence = true → HasType R target argument domain)
    {context : Ctx Head n} {sigma : Sub Head n m} {evidence : Fin n → Evidence}
    (accepted : checkArguments check context sigma evidence = true) :
    Presentation.CtxMor R context target sigma := by
  induction context with
  | nil =>
      intro index
      exact Fin.elim0 index
  | snoc prior domain inductionHypothesis =>
      have components :
          checkArguments check prior (fun index => sigma index.succ)
              (fun index => evidence index.succ) = true ∧
            check (sigma 0) (subst (fun index => sigma index.succ) domain)
              (evidence 0) = true := by
        simpa only [checkArguments, Bool.and_eq_true] using accepted
      have earlier := inductionHypothesis components.1
      have newest := checkSound _ _ _ components.2
      simpa only [consSub_eta] using
        (Presentation.CtxMor.extend earlier newest)

/-- Both checked equation endpoints retain the same instantiated displayed type.
The typing of the target instance is derived, not an admission assumption. -/
theorem checked_endpoints
    {R : Rules Head} {target : Ctx Head m}
    (check : Tm Head m → Tm Head m → Evidence → Bool)
    (checkSound : ∀ argument domain evidence,
      check argument domain evidence = true → HasType R target argument domain)
    {context : Ctx Head n} {sigma : Sub Head n m} {evidence : Fin n → Evidence}
    {left right type : Tm Head n}
    (leftTyping : HasType R context left type)
    (rightTyping : HasType R context right type)
    (accepted : checkArguments check context sigma evidence = true) :
    HasType R target (subst sigma left) (subst sigma type) ∧
      HasType R target (subst sigma right) (subst sigma type) := by
  have typed := checkArguments_sound check checkSound accepted
  exact ⟨leftTyping.substitute typed, rightTyping.substitute typed⟩

/-- Checked arguments also justify the actual closed application and its pure
directed beta path to the substituted body. No head-equality oracle is used. -/
theorem checked_application_beta
    {R : Rules Head} {target : Ctx Head m}
    (check : Tm Head m → Tm Head m → Evidence → Bool)
    (checkSound : ∀ argument domain evidence,
      check argument domain evidence = true → HasType R target argument domain)
    {context : Ctx Head n} {sigma : Sub Head n m} {evidence : Fin n → Evidence}
    {body type : Tm Head n}
    (bodyTyping : HasType R context body type)
    (accepted : checkArguments check context sigma evidence = true) :
    HasType R target
        (TelescopeAbstraction.applyClosed context sigma
          (liftClosed (TelescopeAbstraction.closeTerm context body)))
        (subst sigma type) ∧
      HasType R target (subst sigma body) (subst sigma type) ∧
      TelescopeAbstraction.BetaSteps
        (TelescopeAbstraction.applyClosed context sigma
          (liftClosed (TelescopeAbstraction.closeTerm context body)))
        (subst sigma body) := by
  have typed := checkArguments_sound check checkSound accepted
  have emptyTyped : Presentation.CtxMor R (.nil : Ctx Head 0) target
      (renSub Fin.elim0) := by
    intro index
    exact Fin.elim0 index
  have functionTyping : HasType R target
      (liftClosed (TelescopeAbstraction.closeTerm context body))
      (liftClosed (TelescopeAbstraction.closeType context type)) := by
    simpa only [subst_renSub, liftClosed] using
      (TelescopeAbstraction.close_typed bodyTyping).substitute emptyTyped
  exact ⟨TelescopeAbstraction.applyClosed_typed typed functionTyping,
    bodyTyping.substitute typed,
    TelescopeAbstraction.applyClosed_beta context sigma body⟩

/-- A later typed context change transports the accepted instance through the
existing composite substitution, without independently rebuilding its type. -/
theorem checked_instance_composes
    {R : Rules Head} {target : Ctx Head m} {destination : Ctx Head k}
    (check : Tm Head m → Tm Head m → Evidence → Bool)
    (checkSound : ∀ argument domain evidence,
      check argument domain evidence = true → HasType R target argument domain)
    {context : Ctx Head n} {sigma : Sub Head n m} {evidence : Fin n → Evidence}
    {tau : Sub Head m k} {body type : Tm Head n}
    (bodyTyping : HasType R context body type)
    (accepted : checkArguments check context sigma evidence = true)
    (later : Presentation.CtxMor R target destination tau) :
    HasType R destination (subst (subComp tau sigma) body)
      (subst (subComp tau sigma) type) := by
  exact bodyTyping.substitute
    ((checkArguments_sound check checkSound accepted).comp later)

#print axioms checkArguments_eq_true_iff
#print axioms checkArguments_sound
#print axioms checked_endpoints
#print axioms checked_application_beta
#print axioms checked_instance_composes

end TelescopeArgumentChecking
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
