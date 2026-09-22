import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveJudgmentReplay
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplaySubstitution

/-!
# Executable formation evidence from structural typing replay

Formation evidence is read from the supplied finite typing and context trees.
The operations reuse certificate renaming and substitution, including their
conversion payloads. They do not search for a derivation or select a witness
from propositional completeness.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay

variable {Head : Type} {ConversionCode : Nat → Type}

def Code.piFormation : {n : Nat} → Code Head ConversionCode n →
    Option (Head × Head × Code Head ConversionCode n × Code Head ConversionCode (n + 1))
  | _, .piForm u v domain body => some (u, v, domain, body)
  | _, .cumul _ source => source.piFormation
  | _, .convert _ _ source _ _ => source.piFormation
  | _, _ => none

def Code.sigmaFormation : {n : Nat} → Code Head ConversionCode n →
    Option (Head × Head × Code Head ConversionCode n × Code Head ConversionCode (n + 1))
  | _, .sigmaForm u v domain body => some (u, v, domain, body)
  | _, .cumul _ source => source.sigmaFormation
  | _, .convert _ _ source _ _ => source.sigmaFormation
  | _, _ => none

variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)] [∀ u v, Decidable (R.cumulative u v)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)

theorem Code.piFormation_checked {n : Nat} (code : Code Head ConversionCode n) :
    ∀ {context : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)} {type : Tm Head n},
      check R conversionCheck context (.pi A B) type code = true →
      ∃ u v domain body, code.piFormation = some (u, v, domain, body) ∧
        R.isUniverse u ∧ R.isUniverse v ∧
        check R conversionCheck context A (.head u) domain = true ∧
        check R conversionCheck (.snoc context A) B (.head v) body = true := by
  induction code with
  | piForm u v domain body _ _ =>
      intro context A B type accepted
      cases type <;> simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      exact ⟨u, v, domain, body, rfl, accepted.1.1.1.1, accepted.1.1.1.2, accepted.1.2, accepted.2⟩
  | cumul u source ih =>
      intro context A B type accepted
      cases type <;> simp only [check, Bool.and_eq_true, Bool.false_eq_true] at accepted
      exact ih accepted.1
  | convert sourceType u source formation conversion ih _ =>
      intro context A B type accepted
      simp only [check, Bool.and_eq_true] at accepted
      exact ih accepted.1.1.2
  | _ =>
      intros context A B type accepted
      cases type <;> simp only [check, Bool.false_eq_true] at accepted

theorem Code.sigmaFormation_checked {n : Nat} (code : Code Head ConversionCode n) :
    ∀ {context : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)} {type : Tm Head n},
      check R conversionCheck context (.sigma A B) type code = true →
      ∃ u v domain body, code.sigmaFormation = some (u, v, domain, body) ∧
        R.isUniverse u ∧ R.isUniverse v ∧
        check R conversionCheck context A (.head u) domain = true ∧
        check R conversionCheck (.snoc context A) B (.head v) body = true := by
  induction code with
  | sigmaForm u v domain body _ _ =>
      intro context A B type accepted
      cases type <;> simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      exact ⟨u, v, domain, body, rfl, accepted.1.1.1.1, accepted.1.1.1.2, accepted.1.2, accepted.2⟩
  | cumul u source ih =>
      intro context A B type accepted
      cases type <;> simp only [check, Bool.and_eq_true, Bool.false_eq_true] at accepted
      exact ih accepted.1
  | convert sourceType u source formation conversion ih _ =>
      intro context A B type accepted
      simp only [check, Bool.and_eq_true] at accepted
      exact ih accepted.1.1.2
  | _ =>
      intros context A B type accepted
      cases type <;> simp only [check, Bool.false_eq_true] at accepted

variable (renameConversion : {n m : Nat} → Ren n m → ConversionCode n → ConversionCode m)
variable (renamePreserves : ∀ {n m} (ρ : Ren n m) (code : ConversionCode n)
  {left right : Tm Head n}, conversionCheck code left right = true →
    conversionCheck (renameConversion ρ code) (Presentation.rename ρ left) (Presentation.rename ρ right) = true)

def ContextCode.lookupFormation : {n : Nat} → ContextCode Head ConversionCode n →
    Fin n → Head × Code Head ConversionCode n
  | _, .nil, index => Fin.elim0 index
  | _, .snoc prior u formation, index =>
      Fin.cases (u, formation.rename renameConversion wk)
        (fun index => let result := prior.lookupFormation index
                      (result.1, result.2.rename renameConversion wk)) index

include renamePreserves in
theorem ContextCode.lookupFormation_checked {n : Nat} (code : ContextCode Head ConversionCode n) :
    ∀ {context : Ctx Head n}, checkContext R conversionCheck context code = true →
      ∀ index : Fin n,
        R.isUniverse (code.lookupFormation renameConversion index).1 ∧
        check R conversionCheck context (Ctx.lookup context index)
          (.head (code.lookupFormation renameConversion index).1)
          (code.lookupFormation renameConversion index).2 = true := by
  induction code with
  | nil => intro context accepted index; exact Fin.elim0 index
  | snoc prior u formation ih =>
      intro context accepted index
      cases context with
      | snoc context A =>
          simp only [checkContext, Bool.and_eq_true, decide_eq_true_eq] at accepted
          refine Fin.cases ?_ (fun index => ?_) index
          · refine ⟨accepted.1.2, ?_⟩
            exact check_rename renameConversion R conversionCheck renamePreserves formation
              accepted.2 (fun _ => rfl)
          · obtain ⟨isUniverse, checked⟩ := ih accepted.1.1 index
            refine ⟨isUniverse, ?_⟩
            exact check_rename renameConversion R conversionCheck renamePreserves _
              checked (fun _ => rfl)

variable (substituteConversion : {n m : Nat} → Sub Head n m → ConversionCode n → ConversionCode m)
variable (substitutePreserves : ∀ {n m} (σ : Sub Head n m) (code : ConversionCode n)
  {left right : Tm Head n}, conversionCheck code left right = true →
    conversionCheck (substituteConversion σ code) (subst σ left) (subst σ right) = true)

def Code.instantiateFormation {n : Nat} (body : Tm Head (n + 1)) (level : Head)
    (argument : Tm Head n) (formation : Code Head ConversionCode (n + 1))
    (argumentCode : Code Head ConversionCode n) : Code Head ConversionCode n :=
  Code.instantiate renameConversion substituteConversion body (.head level) argument formation argumentCode

include renamePreserves substitutePreserves in
theorem Code.instantiateFormation_checked {n : Nat} {context : Ctx Head n}
    {A : Tm Head n} {body : Tm Head (n + 1)} {level : Head} {argument : Tm Head n}
    {argumentCode : Code Head ConversionCode n} {formation : Code Head ConversionCode (n + 1)}
    (formed : check R conversionCheck (.snoc context A) body (.head level) formation = true)
    (argumentChecked : check R conversionCheck context argument A argumentCode = true) :
    check R conversionCheck context (inst0 argument body) (.head level)
      (formation.instantiateFormation renameConversion substituteConversion body level argument argumentCode) = true := by
  exact Code.instantiate_checked renameConversion substituteConversion R conversionCheck
    renamePreserves substitutePreserves formed argumentChecked

/-- Recover a finite certificate for the displayed result type. Malformed
inputs may fail; every accepted judgment is covered by `resultFormation_checked`. -/
def Code.resultFormation
    (renameConversion : {n m : Nat} → Ren n m → ConversionCode n → ConversionCode m)
    (substituteConversion : {n m : Nat} → Sub Head n m → ConversionCode n → ConversionCode m)
    (universeSuccessor : Head → Head) : {n : Nat} → Code Head ConversionCode n →
      ContextCode Head ConversionCode n → Tm Head n → Tm Head n →
      Option (Head × Code Head ConversionCode n)
  | _, .headType, _, _, .head u => some (universeSuccessor u, .headType)
  | _, .var, context, .var index, _ => some (context.lookupFormation renameConversion index)
  | _, .const u formation, _, _, _ => some (u, formation.rename renameConversion Fin.elim0)
  | _, .piForm _ _ _ _, _, _, .head u => some (universeSuccessor u, .headType)
  | _, .sigmaForm _ _ _ _, _, _, .head u => some (universeSuccessor u, .headType)
  | _, .lamIntro u formation _, _, _, _ => some (u, formation)
  | _, .appElim A B function argument, context, .app f a, _ => do
      let (_, formedFunction) ← function.resultFormation renameConversion substituteConversion
        universeSuccessor context f (.pi A B)
      let (_, v, _, formedBody) ← formedFunction.piFormation
      return (v, formedBody.instantiateFormation renameConversion substituteConversion B v a argument)
  | _, .pairIntro u formation _ _, _, _, _ => some (u, formation)
  | _, .fstElim B pair, context, .fst p, type => do
      let (_, formedPair) ← pair.resultFormation renameConversion substituteConversion
        universeSuccessor context p (.sigma type B)
      let (u, _, formedDomain, _) ← formedPair.sigmaFormation
      return (u, formedDomain)
  | _, .sndElim A B pair, context, .snd p, _ => do
      let (_, formedPair) ← pair.resultFormation renameConversion substituteConversion
        universeSuccessor context p (.sigma A B)
      let (_, v, _, formedBody) ← formedPair.sigmaFormation
      return (v, formedBody.instantiateFormation renameConversion substituteConversion
        B v (.fst p) (.fstElim B pair))
  | _, .idForm _ _ _ _, _, _, .head u => some (universeSuccessor u, .headType)
  | _, .reflIntro A term, context, .refl a, _ => do
      let (u, formation) ← term.resultFormation renameConversion substituteConversion
        universeSuccessor context a A
      return (u, .idForm u formation term term)
  | _, .cumul _ _, _, _, .head u => some (universeSuccessor u, .headType)
  | _, .convert _ u _ formation _, _, _, _ => some (u, formation)
  | _, _, _, _, _ => none

variable (universeSuccessor : Head → Head)
variable (universes : FormationSensitive.UniverseRegularity R)
variable (successorQualified : ∀ u, R.isUniverse u →
  R.isUniverse (universeSuccessor u) ∧ R.headTyping u (universeSuccessor u))

include successorQualified in
private theorem successor_checked {n : Nat} (context : Ctx Head n) (u : Head)
    (isUniverse : R.isUniverse u) :
    R.isUniverse (universeSuccessor u) ∧
      check R conversionCheck context (.head u) (.head (universeSuccessor u)) .headType = true := by
  obtain ⟨isNext, typed⟩ := successorQualified u isUniverse
  exact ⟨isNext, by simpa only [check, decide_eq_true_eq] using typed⟩

include renamePreserves substitutePreserves universes successorQualified in
/-- Every accepted tree computes an accepted formation certificate for its
displayed result type. The output is pinned by the extraction equation. -/
theorem Code.resultFormation_checked {n : Nat} (code : Code Head ConversionCode n) :
    ∀ {context : Ctx Head n} {subject type : Tm Head n}
      (contextCode : ContextCode Head ConversionCode n),
      checkContext R conversionCheck context contextCode = true →
      check R conversionCheck context subject type code = true →
      ∃ u formation,
        code.resultFormation renameConversion substituteConversion universeSuccessor
          contextCode subject type = some (u, formation) ∧
        R.isUniverse u ∧ check R conversionCheck context type (.head u) formation = true := by
  induction code with
  | headType =>
      intro context subject type contextCode contextAccepted accepted
      cases subject <;> cases type <;>
        simp only [check, decide_eq_true_eq, Bool.false_eq_true] at accepted
      exact ⟨_, _, rfl, successor_checked R conversionCheck universeSuccessor successorQualified
        context _ (universes.head_target accepted)⟩
  | var =>
      intro context subject type contextCode contextAccepted accepted
      cases subject <;> simp only [check, decide_eq_true_eq, Bool.false_eq_true] at accepted
      subst type
      exact ⟨_, _, rfl, contextCode.lookupFormation_checked R conversionCheck
        renameConversion renamePreserves contextAccepted _⟩
  | const u formation ih =>
      intro context subject type contextCode contextAccepted accepted
      cases subject <;> simp only [check, Bool.false_eq_true] at accepted
      rename_i name
      cases known : R.constantType name with
      | none => simp only [known, Bool.false_eq_true] at accepted
      | some declared =>
          simp only [known, Bool.and_eq_true, decide_eq_true_eq] at accepted
          obtain ⟨⟨isU, formed⟩, same⟩ := accepted
          subst type
          refine ⟨u, _, rfl, isU, ?_⟩
          exact check_rename renameConversion R conversionCheck renamePreserves formation
            formed (fun index => Fin.elim0 index)
  | piForm u v domain body ihDomain ihBody =>
      intro context subject type contextCode contextAccepted accepted
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      exact ⟨_, _, rfl, successor_checked R conversionCheck universeSuccessor successorQualified
        context _ (universes.join_target accepted.1.1.2)⟩
  | sigmaForm u v domain body ihDomain ihBody =>
      intro context subject type contextCode contextAccepted accepted
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      exact ⟨_, _, rfl, successor_checked R conversionCheck universeSuccessor successorQualified
        context _ (universes.join_target accepted.1.1.2)⟩
  | lamIntro u formation body ihFormation ihBody =>
      intro context subject type contextCode contextAccepted accepted
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      exact ⟨u, formation, rfl, accepted.1.1, accepted.1.2⟩
  | appElim A B function argument ihFunction ihArgument =>
      intro context subject type contextCode contextAccepted accepted
      cases subject <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      rename_i f a
      obtain ⟨⟨functionChecked, argumentChecked⟩, same⟩ := accepted
      subst type
      obtain ⟨u, formedFunction, computed, isU, functionFormed⟩ :=
        ihFunction contextCode contextAccepted functionChecked
      obtain ⟨v, w, domain, body, parts, isV, isW, domainChecked, bodyChecked⟩ :=
        formedFunction.piFormation_checked R conversionCheck functionFormed
      refine ⟨w, _, ?_, isW,
        Code.instantiateFormation_checked R conversionCheck renameConversion renamePreserves
          substituteConversion substitutePreserves bodyChecked argumentChecked⟩
      simp [resultFormation, computed, parts]
  | pairIntro u formation first second ihFormation ihFirst ihSecond =>
      intro context subject type contextCode contextAccepted accepted
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      exact ⟨u, formation, rfl, accepted.1.1.1, accepted.1.1.2⟩
  | fstElim B pair ihPair =>
      intro context subject type contextCode contextAccepted accepted
      cases subject <;> simp only [check, Bool.false_eq_true] at accepted
      obtain ⟨u, formedPair, computed, isU, pairFormed⟩ :=
        ihPair contextCode contextAccepted accepted
      obtain ⟨v, w, domain, body, parts, isV, isW, domainChecked, bodyChecked⟩ :=
        formedPair.sigmaFormation_checked R conversionCheck pairFormed
      refine ⟨v, domain, ?_, isV, domainChecked⟩
      simp [resultFormation, computed, parts]
  | sndElim A B pair ihPair =>
      intro context subject type contextCode contextAccepted accepted
      cases subject <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨pairChecked, same⟩ := accepted
      subst type
      obtain ⟨u, formedPair, computed, isU, pairFormed⟩ :=
        ihPair contextCode contextAccepted pairChecked
      obtain ⟨v, w, domain, body, parts, isV, isW, domainChecked, bodyChecked⟩ :=
        formedPair.sigmaFormation_checked R conversionCheck pairFormed
      refine ⟨w, _, ?_, isW,
        Code.instantiateFormation_checked R conversionCheck renameConversion renamePreserves
          substituteConversion substitutePreserves bodyChecked (show
            check R conversionCheck context (.fst _) A (.fstElim B pair) = true from pairChecked)⟩
      simp [resultFormation, computed, parts]
  | idForm u formation left right ihFormation ihLeft ihRight =>
      intro context subject type contextCode contextAccepted accepted
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      rcases accepted with ⟨⟨⟨⟨isU, formed⟩, leftChecked⟩, rightChecked⟩, rfl⟩
      exact ⟨_, _, rfl, successor_checked R conversionCheck universeSuccessor successorQualified
        context _ isU⟩
  | reflIntro A term ihTerm =>
      intro context subject type contextCode contextAccepted accepted
      cases subject <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨termChecked, same⟩ := accepted
      subst type
      obtain ⟨u, formation, computed, isU, formed⟩ := ihTerm contextCode contextAccepted termChecked
      refine ⟨u, .idForm u formation term term, ?_, isU, ?_⟩
      · simp [resultFormation, computed]
      · simp only [check, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨⟨⟨isU, formed⟩, termChecked⟩, termChecked⟩, True.intro⟩
  | cumul u term ih =>
      intro context subject type contextCode contextAccepted accepted
      cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      exact ⟨_, _, rfl, successor_checked R conversionCheck universeSuccessor successorQualified
        context _ (universes.cumulative_target accepted.2)⟩
  | convert sourceType u source formation conversion ihSource ihFormation =>
      intro context subject type contextCode contextAccepted accepted
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at accepted
      exact ⟨u, formation, rfl, accepted.1.1.1, accepted.1.2⟩

/-- Build evidence for an unreduced lambda application from its argument and
body evidence. Domains are taken from the argument's displayed type; formation
is computed from both input trees. This is not inference from an erased term. -/
def Code.applyLambda (universeJoin : Head → Head → Head) {n : Nat}
    (contextCode : ContextCode Head ConversionCode n)
    (argument A : Tm Head n) (body B : Tm Head (n + 1))
    (argumentCode : Code Head ConversionCode n)
    (bodyCode : Code Head ConversionCode (n + 1)) :
    Option (Code Head ConversionCode n) := do
  let (u, domain) ← argumentCode.resultFormation renameConversion substituteConversion
    universeSuccessor contextCode argument A
  let (v, codomain) ← bodyCode.resultFormation renameConversion substituteConversion
    universeSuccessor (.snoc contextCode u domain) body B
  return .appElim A B (.lamIntro (universeJoin u v) (.piForm u v domain codomain) bodyCode)
    argumentCode

include renamePreserves substitutePreserves universes successorQualified in
/-- Accepted premises yield a computed certificate for the original redex,
with the actual dependent result type, without replacing the redex by its reduct. -/
theorem Code.applyLambda_checked (universeJoin : Head → Head → Head)
    (joinQualified : ∀ u v, R.isUniverse u → R.isUniverse v → R.join u v (universeJoin u v))
    {n : Nat} {context : Ctx Head n} {argument A : Tm Head n}
    {body B : Tm Head (n + 1)} {contextCode : ContextCode Head ConversionCode n}
    {argumentCode : Code Head ConversionCode n} {bodyCode : Code Head ConversionCode (n + 1)}
    (contextAccepted : checkContext R conversionCheck context contextCode = true)
    (argumentAccepted : check R conversionCheck context argument A argumentCode = true)
    (bodyAccepted : check R conversionCheck (.snoc context A) body B bodyCode = true) :
    ∃ code, Code.applyLambda renameConversion substituteConversion universeSuccessor universeJoin
      contextCode argument A body B argumentCode bodyCode = some code ∧
      check R conversionCheck context (.app (.lam body) argument) (inst0 argument B) code = true := by
  obtain ⟨u, domain, domainComputed, isU, domainChecked⟩ := Code.resultFormation_checked
    R conversionCheck renameConversion renamePreserves substituteConversion substitutePreserves
    universeSuccessor universes successorQualified argumentCode contextCode contextAccepted argumentAccepted
  have extended : checkContext R conversionCheck (.snoc context A)
      (.snoc contextCode u domain) = true := by
    simp [checkContext, contextAccepted, isU, domainChecked]
  obtain ⟨v, codomain, codomainComputed, isV, codomainChecked⟩ := Code.resultFormation_checked
    R conversionCheck renameConversion renamePreserves substituteConversion substitutePreserves
    universeSuccessor universes successorQualified bodyCode _ extended bodyAccepted
  have joined := joinQualified u v isU isV
  refine ⟨.appElim A B (.lamIntro (universeJoin u v)
    (.piForm u v domain codomain) bodyCode) argumentCode, ?_, ?_⟩
  · simp [applyLambda, domainComputed, codomainComputed]
  · simp [check, isU, isV, joined, universes.join_target joined,
      domainChecked, codomainChecked, bodyAccepted, argumentAccepted]

/-- Constant-family checking can propagate an expected type backwards across
an application. The argument still has to check, even if the body ignores it. -/
theorem Code.appConstantFamily_checked {n : Nat} {context : Ctx Head n}
    {function argument A B : Tm Head n}
    {functionCode argumentCode : Code Head ConversionCode n}
    (functionAccepted : check R conversionCheck context function
      (.pi A (Presentation.rename wk B)) functionCode = true)
    (argumentAccepted : check R conversionCheck context argument A argumentCode = true) :
    check R conversionCheck context (.app function argument) B
      (.appElim A (Presentation.rename wk B) functionCode argumentCode) = true := by
  simp [check, inst0_rename_wk, functionAccepted, argumentAccepted]

#print axioms Code.applyLambda_checked
#print axioms Code.appConstantFamily_checked
#print axioms Code.piFormation_checked
#print axioms Code.sigmaFormation_checked
#print axioms ContextCode.lookupFormation_checked
#print axioms Code.instantiateFormation_checked
#print axioms Code.resultFormation_checked

end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
