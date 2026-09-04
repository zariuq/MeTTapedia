import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.TypedSubstitution

/-!
# Typed beta subject reduction

The cumulative-tower presentation already provides simultaneous substitution
and proves that every well-typed term remains well typed after a typed context
substitution.  This module extracts the dependent beta instance of that
generic theorem.

The result is deliberately independent of any wire encoding or inference
checker.  It is the intrinsic typed boundary that an authored beta rule must
preserve when transported into a checked presentation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation

variable {Head : Type} {n : Nat}

/-- Opening the newest variable with a well-typed argument preserves the
dependent type of the body. -/
theorem HasType.instantiateNewest
    {R : Rules Head} {Gamma : Ctx Head n}
    {domain : Tm Head n} {body bodyType : Tm Head (n + 1)}
    {argument : Tm Head n}
    (bodyTyping : HasType R (.snoc Gamma domain) body bodyType)
    (argumentTyping : HasType R Gamma argument domain) :
    HasType R Gamma (inst0 argument body) (inst0 argument bodyType) := by
  have typedIdentityArgument :
      HasType R Gamma argument (subst ids domain) := by
    simpa only [subst_ids] using argumentTyping
  have extensionTyped :
      CtxMor R (.snoc Gamma domain) Gamma (consSub argument ids) :=
    CtxMor.extend (CtxMor.identity R Gamma) typedIdentityArgument
  have instantiated := bodyTyping.substitute extensionTyped
  have pairedIdentityIsOpening :
      consSub argument ids = subst0 argument := by
    funext index
    refine Fin.cases ?_ ?_ index
    · rfl
    · intro prior
      rfl
  rw [pairedIdentityIsOpening] at instantiated
  exact instantiated

/-- A dependent beta redex is well typed at the instantiated codomain. -/
theorem HasType.betaSource
    {R : Rules Head} {Gamma : Ctx Head n}
    {domain : Tm Head n} {body bodyType : Tm Head (n + 1)}
    {argument : Tm Head n}
    (bodyTyping : HasType R (.snoc Gamma domain) body bodyType)
    (argumentTyping : HasType R Gamma argument domain) :
    HasType R Gamma (.app (.lam body) argument)
      (inst0 argument bodyType) :=
  .appElim (.lamIntro bodyTyping) argumentTyping

/-- The contractum of a well-typed dependent beta redex has the same
instantiated type.  This is the root beta subject-reduction theorem. -/
theorem HasType.betaTarget
    {R : Rules Head} {Gamma : Ctx Head n}
    {domain : Tm Head n} {body bodyType : Tm Head (n + 1)}
    {argument : Tm Head n}
    (bodyTyping : HasType R (.snoc Gamma domain) body bodyType)
    (argumentTyping : HasType R Gamma argument domain) :
    HasType R Gamma (inst0 argument body) (inst0 argument bodyType) :=
  bodyTyping.instantiateNewest argumentTyping

/-- The raw beta step and both typed endpoints are constructed from the same
body and argument evidence.  No untyped reduction receipt can manufacture
either typing derivation. -/
theorem HasType.typedBeta
    {R : Rules Head} {Gamma : Ctx Head n}
    {domain : Tm Head n} {body bodyType : Tm Head (n + 1)}
    {argument : Tm Head n}
    (bodyTyping : HasType R (.snoc Gamma domain) body bodyType)
    (argumentTyping : HasType R Gamma argument domain) :
    StepCore R.computation R.headEq
        (.app (.lam body) argument) (inst0 argument body) ∧
      HasType R Gamma (.app (.lam body) argument)
        (inst0 argument bodyType) ∧
      HasType R Gamma (inst0 argument body)
        (inst0 argument bodyType) := by
  exact
    ⟨.betaPi body argument,
      bodyTyping.betaSource argumentTyping,
      bodyTyping.betaTarget argumentTyping⟩

/-! ## Negative boundary

An untyped beta step exists for every raw body and argument.  The theorem
above therefore requires the two typing premises explicitly; the raw step
alone is intentionally not an admission interface for typed computation.
-/

example {R : Rules Head} {body : Tm Head 1} {argument : Tm Head 0} :
    StepCore R.computation R.headEq
      (.app (.lam body) argument) (inst0 argument body) :=
  .betaPi body argument

/-! ## Axiom audit -/

#print axioms HasType.instantiateNewest
#print axioms HasType.betaSource
#print axioms HasType.betaTarget
#print axioms HasType.typedBeta

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
