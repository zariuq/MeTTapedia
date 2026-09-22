import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TelescopeArgumentChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRegularity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveTelescopeSpine

/-!
# Formed dependent programs and retained certificate return

The same argument-checking fold earns formation-sensitive substitutions when
its primitive evidence semantics is formation-sensitive. Source and target
context formation are retained separately; neither is inferred from matching.

Closing a formed telescope also requires universe joins. That capability is
an explicit theorem parameter, not another field of the language definition.
The cumulative tower supplies it by its actual maximum-level join rule.

Checked projections close to actual lambda programs, execute by directed beta
steps, and return the value certified by the retained input tree. The returned
tree can be rechecked in the unchanged target context. This is not compulsory
second checking, unrestricted reflection, or verification of the C loaders.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationCheckedTelescopePrograms

open FormationSensitive TelescopeAbstraction TelescopeArgumentChecking

variable {Head Evidence : Type} {R : Rules Head} {n m : Nat}

/-- Closure forms all products in the original telescope order. -/
theorem close_formed
    (joins : ∀ {u v}, R.isUniverse u → R.isUniverse v →
      ∃ w, R.isUniverse w ∧ R.join u v w)
    {context : Ctx Head n} (contextFormation : ContextFormation R context)
    {type : Tm Head n} {u : Head}
    (formed : Typing R context type (.head u)) (isUniverse : R.isUniverse u) :
    ∃ v, R.isUniverse v ∧ Typing R .nil (closeType context type) (.head v) := by
  induction contextFormation generalizing u with
  | nil => exact ⟨u, isUniverse, formed⟩
  | @snoc n prior domain domainUniverse priorFormation domainFormation domainIsUniverse ih =>
      obtain ⟨v, isV, joined⟩ := joins domainIsUniverse isUniverse
      exact ih (.piForm domainFormation domainIsUniverse formed isUniverse joined) isV

/-- Every lambda introduction retains the formation of its actual product.
Raw lambda typing alone cannot establish this theorem. -/
theorem close_typed
    (universes : UniverseRegularity R)
    (joins : ∀ {u v}, R.isUniverse u → R.isUniverse v →
      ∃ w, R.isUniverse w ∧ R.join u v w)
    {context : Ctx Head n} (contextFormation : ContextFormation R context)
    {body type : Tm Head n} (typing : Typing R context body type) :
    Typing R .nil (closeTerm context body) (closeType context type) := by
  induction contextFormation with
  | nil => exact typing
  | @snoc n prior domain domainUniverse priorFormation domainFormation domainIsUniverse ih =>
      have current : ContextFormation R (.snoc prior domain) :=
        .snoc priorFormation domainFormation domainIsUniverse
      obtain ⟨v, isV, typeFormation⟩ := typing.regularity universes current
      obtain ⟨w, isW, joined⟩ := joins domainIsUniverse isV
      exact ih (.lamIntro
        (.piForm domainFormation domainIsUniverse typeFormation isV joined) isW typing)

/-- Accepted certificates earn the existing refined context morphism. -/
theorem checked_substitution
    {target : Ctx Head m}
    (check : Tm Head m → Tm Head m → Evidence → Bool)
    (checkSound : ∀ argument domain evidence,
      check argument domain evidence = true → Typing R target argument domain)
    {context : Ctx Head n} {sigma : Sub Head n m} {evidence : Fin n → Evidence}
    (accepted : checkArguments check context sigma evidence = true) :
    FormationSensitive.CtxMor R context target sigma := by
  intro index
  exact checkSound _ _ _
    ((checkArguments_eq_true_iff check context sigma evidence).1 accepted index)

/-- The very same checked argument assignment types the actual application. -/
theorem apply_typed
    {context : Ctx Head n} {target : Ctx Head m}
    {sigma : Sub Head n m} {type : Tm Head n} {function : Tm Head m}
    (typed : FormationSensitive.CtxMor R context target sigma)
    (functionTyping : Typing R target function (liftClosed (closeType context type))) :
    Typing R target (applyClosed context sigma function) (subst sigma type) := by
  induction context with
  | nil => simpa only [applyClosed, closeType, subst_empty] using functionTyping
  | snoc prior domain ih =>
      have earlier := ih typed.dropNewest functionTyping
      have newest := typed 0
      simp only [Ctx.lookup_snoc_zero, subst_prior] at newest
      simpa only [applyClosed, subst, subst_open] using (Typing.appElim earlier newest)

/-- The formed closed abstraction can be placed in any target context by
the existing empty-source substitution, with no new declaration or carrier. -/
theorem close_into_target
    (universes : UniverseRegularity R)
    (joins : ∀ {u v}, R.isUniverse u → R.isUniverse v →
      ∃ w, R.isUniverse w ∧ R.join u v w)
    {context : Ctx Head n} {body type : Tm Head n}
    (source : Judgment R context body type) {target : Ctx Head m} :
    Typing R target (liftClosed (closeTerm context body))
      (liftClosed (closeType context type)) := by
  have emptyTyped : FormationSensitive.CtxMor R (.nil : Ctx Head 0) target
      (renSub Fin.elim0) := by
    intro index
    exact Fin.elim0 index
  simpa only [subst_renSub, liftClosed] using
    (close_typed universes joins source.context source.typing).substitute emptyTyped

/-- Formed source evidence closes, applies, and computes without changing
the body, its displayed type, or the supplied simultaneous substitution. -/
theorem checked_program
    (universes : UniverseRegularity R)
    (joins : ∀ {u v}, R.isUniverse u → R.isUniverse v →
      ∃ w, R.isUniverse w ∧ R.join u v w)
    {target : Ctx Head m} (targetFormation : ContextFormation R target)
    (check : Tm Head m → Tm Head m → Evidence → Bool)
    (checkSound : ∀ argument domain evidence,
      check argument domain evidence = true → Typing R target argument domain)
    {context : Ctx Head n} {sigma : Sub Head n m} {evidence : Fin n → Evidence}
    {body type : Tm Head n} (source : Judgment R context body type)
    (accepted : checkArguments check context sigma evidence = true) :
    Judgment R target
        (applyClosed context sigma (liftClosed (closeTerm context body)))
        (subst sigma type) ∧
      Judgment R target (subst sigma body) (subst sigma type) ∧
      BetaSteps (applyClosed context sigma (liftClosed (closeTerm context body)))
        (subst sigma body) := by
  have typed := checked_substitution check checkSound accepted
  have lifted := close_into_target universes joins source (target := target)
  exact ⟨⟨targetFormation, apply_typed typed lifted⟩,
    source.substitute targetFormation typed, applyClosed_beta context sigma body⟩

/-- Math-to-program-to-math for arbitrary dependent projections: the
returned value has the exact type and certificate of the chosen argument. -/
theorem checked_projection_loop
    (universes : UniverseRegularity R)
    (joins : ∀ {u v}, R.isUniverse u → R.isUniverse v →
      ∃ w, R.isUniverse w ∧ R.join u v w)
    {context : Ctx Head n} (sourceFormation : ContextFormation R context)
    {target : Ctx Head m} (targetFormation : ContextFormation R target)
    (check : Tm Head m → Tm Head m → Evidence → Bool)
    (checkSound : ∀ argument domain evidence,
      check argument domain evidence = true → Typing R target argument domain)
    {sigma : Sub Head n m} {evidence : Fin n → Evidence}
    (accepted : checkArguments check context sigma evidence = true) (index : Fin n) :
    Judgment R target
        (applyClosed context sigma (liftClosed (closeTerm context (.var index))))
        (subst sigma (Ctx.lookup context index)) ∧
      Judgment R target (sigma index) (subst sigma (Ctx.lookup context index)) ∧
      BetaSteps
        (applyClosed context sigma (liftClosed (closeTerm context (.var index))))
        (sigma index) ∧
      check (sigma index) (subst sigma (Ctx.lookup context index)) (evidence index) = true := by
  have source : Judgment R context (.var index) (Ctx.lookup context index) :=
    ⟨sourceFormation, .var index⟩
  obtain ⟨program, result, execution⟩ :=
    checked_program universes joins targetFormation check checkSound source accepted
  exact ⟨program, result, execution,
    (checkArguments_eq_true_iff check context sigma evidence).1 accepted index⟩

/-- Feed an actually typed program result into the next invocation. Its
typing is earned by the first invocation, not assumed from a raw certificate
for an unreduced term. The same original tree certifies the final value. -/
theorem checked_return_then_consume
    (universes : UniverseRegularity R)
    (joins : ∀ {u v}, R.isUniverse u → R.isUniverse v →
      ∃ w, R.isUniverse w ∧ R.join u v w)
    {prior : Ctx Head n} {domain : Tm Head n}
    (sourceFormation : ContextFormation R (.snoc prior domain))
    {target : Ctx Head m} (targetFormation : ContextFormation R target)
    (check : Tm Head m → Tm Head m → Evidence → Bool)
    (checkSound : ∀ argument domain evidence,
      check argument domain evidence = true → Typing R target argument domain)
    {sigma : Sub Head (n + 1) m} {evidence : Fin (n + 1) → Evidence}
    (accepted : checkArguments check (.snoc prior domain) sigma evidence = true) :
    let function := liftClosed (closeTerm (.snoc prior domain) (.var 0))
    let returned := applyClosed (.snoc prior domain) sigma function
    let feedback := consSub returned (fun index => sigma index.succ)
    Judgment R target (applyClosed (.snoc prior domain) feedback function)
        (subst sigma (Ctx.lookup (.snoc prior domain) 0)) ∧
      BetaSteps (applyClosed (.snoc prior domain) feedback function) (sigma 0) ∧
      check (sigma 0) (subst sigma (Ctx.lookup (.snoc prior domain) 0)) (evidence 0) = true := by
  dsimp only
  obtain ⟨first, _, firstSteps, retained⟩ :=
    checked_projection_loop universes joins sourceFormation targetFormation check checkSound accepted 0
  have initial := checked_substitution check checkSound accepted
  have returnedTyping : Typing R target
      (applyClosed (.snoc prior domain) sigma
        (liftClosed (closeTerm (.snoc prior domain) (.var 0))))
      (subst (fun index => sigma index.succ) domain) := by
    simpa only [Ctx.lookup_snoc_zero, subst_prior] using first.typing
  have feedback := initial.dropNewest.extend returnedTyping
  have function := close_into_target universes joins
    (⟨sourceFormation, Typing.var 0⟩ : Judgment R (.snoc prior domain) (.var 0)
      (Ctx.lookup (.snoc prior domain) 0)) (target := target)
  have second := apply_typed feedback function
  have secondSteps := applyClosed_beta (.snoc prior domain)
    (consSub
      (applyClosed (.snoc prior domain) sigma
        (liftClosed (closeTerm (.snoc prior domain) (.var 0))))
      (fun index => sigma index.succ)) (.var 0)
  refine ⟨⟨targetFormation, ?_⟩, secondSteps.trans firstSteps, retained⟩
  simpa only [Ctx.lookup_snoc_zero, subst_prior, consSub_succ] using second

#print axioms close_formed
#print axioms close_typed
#print axioms checked_substitution
#print axioms apply_typed
#print axioms close_into_target
#print axioms checked_program
#print axioms checked_projection_loop
#print axioms checked_return_then_consume

end FormationCheckedTelescopePrograms
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
