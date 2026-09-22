import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationCheckedTelescopePrograms

/-!
# Inspectable structural evidence replay on the existing native syntax

The executable checker below reconstructs existing formation-sensitive typing
from a supplied finite evidence tree. It does not infer proof authority from a
search result, add language fields, or provide a semantic-equality oracle.
Lambda and pair evidence retain formation; application and second projection
check the type obtained by substituting the actual argument or projection.

The primitive decisions concern the selected rule package itself. Conversion
uses a supplied finite-code checker, separately qualified against the actual
conversion relation. Context formation remains a separate boundary here;
rejecting one supplied tree does not refute general native typing.
This is a reference evidence replay, not an exported C checking certificate or
a verification of the C declaration environment and normalization routines.

`Code` enumerates structural typing rules, not every declared connective.
The `const` and `appElim` cases replay declared eliminators, including the
native dependent J of `NativeIndexedFamilies`; its iota rule is checked by
the supplied conversion-code instance. Formation extraction from these
trees computes evidence for the displayed type, not typing evidence from
an unannotated or erased result.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay

open FormationSensitive TelescopeArgumentChecking

variable {Head : Type} {ConversionCode : Nat → Type}

/-- The structural-only replay profile has no conversion evidence. -/
abbrev NoConversion (_ : Nat) := Empty

def noConversionCheck {n : Nat} (code : NoConversion n)
    (_left _right : Tm Head n) : Bool := nomatch code

theorem noConversionSound (R : Rules Head) {n : Nat} {code : NoConversion n}
    {left right : Tm Head n} (_accepted : noConversionCheck code left right = true) :
    Conv R.headEq left right R.computation := nomatch code

/-- Finite inspectable evidence. Indices and child binders use the same scope
as native terms; annotations expose the premises that checking must earn. -/
inductive Code (Head : Type) (ConversionCode : Nat → Type) : Nat → Type where
  | headType {n : Nat} : Code Head ConversionCode n
  | var {n : Nat} : Code Head ConversionCode n
  | const {n : Nat} (levelHead : Head) (formation : Code Head ConversionCode 0) : Code Head ConversionCode n
  | piForm {n : Nat} (domainUniverse bodyUniverse : Head)
      (domain : Code Head ConversionCode n) (body : Code Head ConversionCode (n + 1)) : Code Head ConversionCode n
  | sigmaForm {n : Nat} (domainUniverse bodyUniverse : Head)
      (domain : Code Head ConversionCode n) (body : Code Head ConversionCode (n + 1)) : Code Head ConversionCode n
  | lamIntro {n : Nat} (levelHead : Head) (formation : Code Head ConversionCode n)
      (body : Code Head ConversionCode (n + 1)) : Code Head ConversionCode n
  | appElim {n : Nat} (domain : Tm Head n) (body : Tm Head (n + 1))
      (function argument : Code Head ConversionCode n) : Code Head ConversionCode n
  | pairIntro {n : Nat} (levelHead : Head) (formation first second : Code Head ConversionCode n) : Code Head ConversionCode n
  | fstElim {n : Nat} (body : Tm Head (n + 1)) (pair : Code Head ConversionCode n) : Code Head ConversionCode n
  | sndElim {n : Nat} (domain : Tm Head n) (body : Tm Head (n + 1))
      (pair : Code Head ConversionCode n) : Code Head ConversionCode n
  | idForm {n : Nat} (levelHead : Head) (formation left right : Code Head ConversionCode n) : Code Head ConversionCode n
  | reflIntro {n : Nat} (type : Tm Head n) (term : Code Head ConversionCode n) : Code Head ConversionCode n
  | cumul {n : Nat} (sourceUniverse : Head) (term : Code Head ConversionCode n) : Code Head ConversionCode n
  | convert {n : Nat} (sourceType : Tm Head n) (levelHead : Head)
      (source formation : Code Head ConversionCode n)
      (conversion : ConversionCode n) : Code Head ConversionCode n

/-- Change the finite conversion encoding without changing the authored
typing-rule tree, its annotations, or any binder scopes. -/
def Code.mapConversion {OtherCode : Nat → Type}
    (mapCode : {n : Nat} → ConversionCode n → OtherCode n) :
    {n : Nat} → Code Head ConversionCode n → Code Head OtherCode n
  | _, .headType => .headType
  | _, .var => .var
  | _, .const u formation => .const u (formation.mapConversion mapCode)
  | _, .piForm u v domain body =>
      .piForm u v (domain.mapConversion mapCode) (body.mapConversion mapCode)
  | _, .sigmaForm u v domain body =>
      .sigmaForm u v (domain.mapConversion mapCode) (body.mapConversion mapCode)
  | _, .lamIntro u formation body =>
      .lamIntro u (formation.mapConversion mapCode) (body.mapConversion mapCode)
  | _, .appElim A B function argument =>
      .appElim A B (function.mapConversion mapCode) (argument.mapConversion mapCode)
  | _, .pairIntro u formation first second =>
      .pairIntro u (formation.mapConversion mapCode) (first.mapConversion mapCode)
        (second.mapConversion mapCode)
  | _, .fstElim B pair => .fstElim B (pair.mapConversion mapCode)
  | _, .sndElim A B pair => .sndElim A B (pair.mapConversion mapCode)
  | _, .idForm u formation left right =>
      .idForm u (formation.mapConversion mapCode) (left.mapConversion mapCode)
        (right.mapConversion mapCode)
  | _, .reflIntro A term => .reflIntro A (term.mapConversion mapCode)
  | _, .cumul u term => .cumul u (term.mapConversion mapCode)
  | _, .convert A u source formation conversion =>
      .convert A u (source.mapConversion mapCode) (formation.mapConversion mapCode)
        (mapCode conversion)

@[simp] theorem Code.mapConversion_id {n : Nat} (code : Code Head ConversionCode n) :
    code.mapConversion (fun value => value) = code := by
  induction code <;> simp_all only [mapConversion]

theorem Code.mapConversion_comp {OtherCode FinalCode : Nat → Type}
    (first : {n : Nat} → ConversionCode n → OtherCode n)
    (second : {n : Nat} → OtherCode n → FinalCode n)
    {n : Nat} (code : Code Head ConversionCode n) :
    (code.mapConversion first).mapConversion second =
      code.mapConversion (fun value => second (first value)) := by
  induction code <;> simp_all only [mapConversion]

variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)]
variable [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)]
variable [∀ u v, Decidable (R.cumulative u v)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)

/-- Replay the supplied tree against the actual context, subject, and type.
The equality tests are syntax equality, not native or semantic conversion. -/
def check {n : Nat} (context : Ctx Head n) (subject type : Tm Head n) :
    Code Head ConversionCode n → Bool
  | .headType => match subject, type with
      | .head h, .head u => decide (R.headTyping h u)
      | _, _ => false
  | .var => match subject with
      | .var index => decide (type = Ctx.lookup context index)
      | _ => false
  | .const levelHead formation => match subject with
      | .const name => match R.constantType name with
          | none => false
          | some declared => decide (R.isUniverse levelHead) &&
              check .nil declared (.head levelHead) formation &&
              decide (type = liftClosed declared)
      | _ => false
  | .piForm u v domain body => match subject, type with
      | .pi A B, .head w => decide (R.isUniverse u) && decide (R.isUniverse v) &&
          decide (R.join u v w) && check context A (.head u) domain &&
          check (.snoc context A) B (.head v) body
      | _, _ => false
  | .sigmaForm u v domain body => match subject, type with
      | .sigma A B, .head w => decide (R.isUniverse u) && decide (R.isUniverse v) &&
          decide (R.join u v w) && check context A (.head u) domain &&
          check (.snoc context A) B (.head v) body
      | _, _ => false
  | .lamIntro levelHead formation body => match subject, type with
      | .lam term, .pi A B => decide (R.isUniverse levelHead) &&
          check context (.pi A B) (.head levelHead) formation &&
          check (.snoc context A) term B body
      | _, _ => false
  | .appElim A B function argument => match subject with
      | .app g a => check context g (.pi A B) function &&
          check context a A argument && decide (type = inst0 a B)
      | _ => false
  | .pairIntro levelHead formation first second => match subject, type with
      | .pair a b, .sigma A B => decide (R.isUniverse levelHead) &&
          check context (.sigma A B) (.head levelHead) formation &&
          check context a A first && check context b (inst0 a B) second
      | _, _ => false
  | .fstElim B pair => match subject with
      | .fst p => check context p (.sigma type B) pair
      | _ => false
  | .sndElim A B pair => match subject with
      | .snd p => check context p (.sigma A B) pair &&
          decide (type = inst0 (.fst p) B)
      | _ => false
  | .idForm levelHead formation left right => match subject, type with
      | .id A a b, .head u => decide (R.isUniverse levelHead) &&
          check context A (.head levelHead) formation && check context a A left &&
          check context b A right && decide (u = levelHead)
      | _, _ => false
  | .reflIntro A term => match subject with
      | .refl a => check context a A term && decide (type = .id A a a)
      | _ => false
  | .cumul u term => match type with
      | .head v => check context subject (.head u) term && decide (R.cumulative u v)
      | _ => false
  | .convert sourceType levelHead source formation conversion =>
      decide (R.isUniverse levelHead) && check context subject sourceType source &&
        check context type (.head levelHead) formation &&
        conversionCheck conversion sourceType type

/-- A conversion encoding comparison gives exact checker agreement, on
rejection as well as acceptance, throughout the whole recursive tree. -/
theorem check_mapConversion {OtherCode : Nat → Type}
    (otherCheck : {n : Nat} → OtherCode n → Tm Head n → Tm Head n → Bool)
    (mapCode : {n : Nat} → ConversionCode n → OtherCode n)
    (compatible : ∀ {n : Nat} (code : ConversionCode n) (left right : Tm Head n),
      otherCheck (mapCode code) left right = conversionCheck code left right)
    {n : Nat} (code : Code Head ConversionCode n) :
    ∀ (context : Ctx Head n) (subject type : Tm Head n),
      check R otherCheck context subject type (code.mapConversion mapCode) =
        check R conversionCheck context subject type code := by
  induction code <;> intros <;> simp_all only [Code.mapConversion, check]

variable (conversionSound : ∀ {n : Nat} {code : ConversionCode n} {left right : Tm Head n},
  conversionCheck code left right = true → Conv R.headEq left right R.computation)

include conversionSound

/-- Every accepted tree constructs the existing typing judgment, including
its independently checked formation and actual dependent substitution. -/
theorem check_sound {n : Nat} (code : Code Head ConversionCode n) :
    ∀ {context : Ctx Head n} {subject type : Tm Head n},
      check R conversionCheck context subject type code = true → Typing R context subject type := by
  induction code with
  | headType =>
      intro context subject type accepted
      cases subject <;> cases type <;>
        simp only [check, decide_eq_true_eq, Bool.false_eq_true] at accepted
      exact .headType accepted
  | var =>
      intro context subject type accepted
      cases subject <;> simp only [check, decide_eq_true_eq, Bool.false_eq_true] at accepted
      subst type
      exact .var _
  | const levelHead formation ih =>
      intro context subject type accepted
      cases subject <;> simp only [check, Bool.false_eq_true] at accepted
      rename_i name
      cases known : R.constantType name with
      | none => simp only [known, Bool.false_eq_true] at accepted
      | some declared =>
          simp only [known, Bool.and_eq_true, decide_eq_true_eq] at accepted
          obtain ⟨⟨isUniverse, formed⟩, same⟩ := accepted
          subst type
          exact .const known (ih formed) isUniverse
  | piForm u v domain body ihDomain ihBody =>
      intro context subject type accepted
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨⟨⟨isU, isV⟩, joined⟩, domainAccepted⟩, bodyAccepted⟩ := accepted
      exact .piForm (ihDomain domainAccepted) isU (ihBody bodyAccepted) isV joined
  | sigmaForm u v domain body ihDomain ihBody =>
      intro context subject type accepted
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨⟨⟨isU, isV⟩, joined⟩, domainAccepted⟩, bodyAccepted⟩ := accepted
      exact .sigmaForm (ihDomain domainAccepted) isU (ihBody bodyAccepted) isV joined
  | lamIntro levelHead formation body ihFormation ihBody =>
      intro context subject type accepted
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨isUniverse, formed⟩, bodyAccepted⟩ := accepted
      exact .lamIntro (ihFormation formed) isUniverse (ihBody bodyAccepted)
  | appElim A B function argument ihFunction ihArgument =>
      intro context subject type accepted
      cases subject <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨functionAccepted, argumentAccepted⟩, same⟩ := accepted
      subst type
      exact .appElim (ihFunction functionAccepted) (ihArgument argumentAccepted)
  | pairIntro levelHead formation first second ihFormation ihFirst ihSecond =>
      intro context subject type accepted
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨⟨isUniverse, formed⟩, firstAccepted⟩, secondAccepted⟩ := accepted
      exact .pairIntro (ihFormation formed) isUniverse
        (ihFirst firstAccepted) (ihSecond secondAccepted)
  | fstElim B pair ihPair =>
      intro context subject type accepted
      cases subject <;> simp only [check, Bool.false_eq_true] at accepted
      exact .fstElim (ihPair accepted)
  | sndElim A B pair ihPair =>
      intro context subject type accepted
      cases subject <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨pairAccepted, same⟩ := accepted
      subst type
      exact .sndElim (ihPair pairAccepted)
  | idForm levelHead formation left right ihFormation ihLeft ihRight =>
      intro context subject type accepted
      cases subject <;> cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨⟨⟨⟨isUniverse, formed⟩, leftAccepted⟩, rightAccepted⟩, same⟩ := accepted
      subst_vars
      exact .idForm (ihFormation formed) isUniverse (ihLeft leftAccepted) (ihRight rightAccepted)
  | reflIntro A term ihTerm =>
      intro context subject type accepted
      cases subject <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      obtain ⟨termAccepted, same⟩ := accepted
      subst type
      exact .reflIntro (ihTerm termAccepted)
  | cumul levelHead term ihTerm =>
      intro context subject type accepted
      cases type <;>
        simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at accepted
      exact .cumul (ihTerm accepted.1) accepted.2
  | convert sourceType levelHead source formation conversion ihSource ihFormation =>
      intro context subject type accepted
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at accepted
      obtain ⟨⟨⟨isUniverse, sourceAccepted⟩, targetAccepted⟩, converted⟩ := accepted
      exact .conv (ihSource sourceAccepted) (ihFormation targetAccepted) isUniverse
        (conversionSound converted)

/-- Replay earns the existing dependent context morphism. It is not another
substitution relation or a declaration admission procedure. -/
theorem checked_substitution {n m : Nat} {context : Ctx Head n} {target : Ctx Head m}
    {sigma : Sub Head n m} {evidence : Fin n → Code Head ConversionCode m}
    (accepted : checkArguments (check R conversionCheck target) context sigma evidence = true) :
    FormationSensitive.CtxMor R context target sigma :=
  FormationCheckedTelescopePrograms.checked_substitution (check R conversionCheck target)
    (fun _ _ code accepted => check_sound R conversionCheck conversionSound code accepted) accepted

/-- Formed programs consume this actual checked argument assignment and
execute to its simultaneous substitution, without a head-equality step. -/
theorem checked_program
    (universes : UniverseRegularity R)
    (joins : ∀ {u v}, R.isUniverse u → R.isUniverse v →
      ∃ w, R.isUniverse w ∧ R.join u v w)
    {n m : Nat} {context : Ctx Head n} {target : Ctx Head m}
    (targetFormation : ContextFormation R target)
    {sigma : Sub Head n m} {evidence : Fin n → Code Head ConversionCode m}
    {body type : Tm Head n} (source : Judgment R context body type)
    (accepted : checkArguments (check R conversionCheck target) context sigma evidence = true) :
    Judgment R target
        (TelescopeAbstraction.applyClosed context sigma
          (liftClosed (TelescopeAbstraction.closeTerm context body)))
        (subst sigma type) ∧
      Judgment R target (subst sigma body) (subst sigma type) ∧
      TelescopeAbstraction.BetaSteps
        (TelescopeAbstraction.applyClosed context sigma
          (liftClosed (TelescopeAbstraction.closeTerm context body)))
        (subst sigma body) :=
  FormationCheckedTelescopePrograms.checked_program universes joins targetFormation
    (check R conversionCheck target) (fun _ _ code accepted => check_sound R conversionCheck conversionSound code accepted) source accepted

/-- Missing declarations cannot be supplied by structural evidence, even
through a chain of cumulative-universe certificates. -/
theorem missing_constant_rejected {n : Nat} (context : Ctx Head n)
    (name : DeclName) (missing : R.constantType name = none) (code : Code Head ConversionCode n) :
    ∀ type, check R conversionCheck context (.const name) type code = false := by
  intro type
  cases accepted : check R conversionCheck context (.const name) type code with
  | false => rfl
  | true =>
      obtain ⟨declared, level, known, _, _⟩ :=
        (check_sound R conversionCheck conversionSound code accepted).constFormation
      rw [missing] at known
      cases known

#print axioms check_sound
#print axioms check_mapConversion
#print axioms checked_substitution
#print axioms checked_program
#print axioms missing_constant_rejected

end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
