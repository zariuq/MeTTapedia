import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveJudgmentReplay
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCodeDependencies

/-!
# Declaration-local reuse of dependent judgment certificates

The finite dependency collector follows the existing supplied typing tree,
including closed declaration formation and the ambient telescope. It records
missing lookups as well as present declarations. Agreement on these lookups
and on the conversion requests preserves the existing checker's exact verdict.

The universe policy is fixed across the comparison. Computation packages may
change; qualification of the target conversion decoder remains necessary to
interpret a successful replay as a target judgment. The collector is sufficient
support, not a minimal dynamic read trace, and does not reconstruct certificates.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay

variable {Head : Type} {ConversionCode : Nat → Type}

/-- The universe discipline is unchanged; declarations and computation need
not agree globally. -/
structure PolicyAgreement (source target : Rules Head) : Prop where
  headTyping : source.headTyping = target.headTyping
  isUniverse : source.isUniverse = target.isUniverse
  join : source.join = target.join
  cumulative : source.cumulative = target.cumulative

def DeclarationAgreement (source target : Rules Head) (names : List DeclName) : Prop :=
  ∀ name ∈ names, source.constantType name = target.constantType name

@[simp] theorem declarationAgreement_nil (source target : Rules Head) :
    DeclarationAgreement source target [] := by simp [DeclarationAgreement]

@[simp] theorem declarationAgreement_cons (source target : Rules Head)
    (name : DeclName) (names : List DeclName) :
    DeclarationAgreement source target (name :: names) ↔
      source.constantType name = target.constantType name ∧
        DeclarationAgreement source target names := by
  simp [DeclarationAgreement]

@[simp] theorem declarationAgreement_append (source target : Rules Head)
    (left right : List DeclName) :
    DeclarationAgreement source target (left ++ right) ↔
      DeclarationAgreement source target left ∧ DeclarationAgreement source target right := by
  simp [DeclarationAgreement, or_imp, forall_and]

/-- Declaration queries made by the entire supplied tree. Traversal terminates
on the certificate, even when declaration types contain cyclic references. -/
def Code.declarationRequests (source : Rules Head) : {n : Nat} →
    Tm Head n → Tm Head n → Code Head ConversionCode n → List DeclName
  | _, _, _, .headType => []
  | _, _, _, .var => []
  | _, subject, _, .const u formation => match subject with
      | .const name => name :: (match source.constantType name with
          | none => []
          | some declared => formation.declarationRequests source declared (.head u))
      | _ => []
  | _, .pi A B, .head _, .piForm u v domain body =>
      domain.declarationRequests source A (.head u) ++
        body.declarationRequests source B (.head v)
  | _, .sigma A B, .head _, .sigmaForm u v domain body =>
      domain.declarationRequests source A (.head u) ++
        body.declarationRequests source B (.head v)
  | _, .lam term, .pi A B, .lamIntro u formation body =>
      formation.declarationRequests source (.pi A B) (.head u) ++
        body.declarationRequests source term B
  | _, .app g a, _, .appElim A B function argument =>
      function.declarationRequests source g (.pi A B) ++
        argument.declarationRequests source a A
  | _, .pair a b, .sigma A B, .pairIntro u formation first second =>
      formation.declarationRequests source (.sigma A B) (.head u) ++
        first.declarationRequests source a A ++
          second.declarationRequests source b (inst0 a B)
  | _, .fst p, type, .fstElim B pair =>
      pair.declarationRequests source p (.sigma type B)
  | _, .snd p, _, .sndElim A B pair =>
      pair.declarationRequests source p (.sigma A B)
  | _, .id A a b, .head _, .idForm u formation left right =>
      formation.declarationRequests source A (.head u) ++
        left.declarationRequests source a A ++ right.declarationRequests source b A
  | _, .refl a, _, .reflIntro A term => term.declarationRequests source a A
  | _, subject, .head _, .cumul u term =>
      term.declarationRequests source subject (.head u)
  | _, subject, type, .convert A u sourceCode formation _ =>
      sourceCode.declarationRequests source subject A ++
        formation.declarationRequests source type (.head u)
  | _, _, _, _ => []

/-- Conversion requests retain their binder scopes. Endpoints are supplied by
the existing checker, not guessed by this collector. -/
def Code.conversionRequests : {n : Nat} → Code Head ConversionCode n →
    List (Σ n, ConversionCode n)
  | _, .headType | _, .var => []
  | _, .const _ formation => formation.conversionRequests
  | _, .piForm _ _ domain body | _, .sigmaForm _ _ domain body =>
      domain.conversionRequests ++ body.conversionRequests
  | _, .lamIntro _ formation body => formation.conversionRequests ++ body.conversionRequests
  | _, .appElim _ _ function argument => function.conversionRequests ++ argument.conversionRequests
  | _, .pairIntro _ formation first second | _, .idForm _ formation first second =>
      formation.conversionRequests ++ first.conversionRequests ++ second.conversionRequests
  | _, .fstElim _ pair | _, .sndElim _ _ pair => pair.conversionRequests
  | _, .reflIntro _ term | _, .cumul _ term => term.conversionRequests
  | n, .convert _ _ source formation conversion =>
      ⟨n, conversion⟩ :: (source.conversionRequests ++ formation.conversionRequests)

def ConversionAgreement
    (first second : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)
    (requests : List (Σ n, ConversionCode n)) : Prop :=
  ∀ request ∈ requests, ∀ left right, first request.2 left right = second request.2 left right

@[simp] theorem conversionAgreement_nil
    (first second : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool) :
    ConversionAgreement first second [] := by simp [ConversionAgreement]

@[simp] theorem conversionAgreement_cons
    (first second : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)
    (request : Σ n, ConversionCode n) (requests : List (Σ n, ConversionCode n)) :
    ConversionAgreement first second (request :: requests) ↔
      (∀ left right, first request.2 left right = second request.2 left right) ∧
        ConversionAgreement first second requests := by
  simp [ConversionAgreement]

@[simp] theorem conversionAgreement_append
    (first second : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)
    (left right : List (Σ n, ConversionCode n)) :
    ConversionAgreement first second (left ++ right) ↔
      ConversionAgreement first second left ∧ ConversionAgreement first second right := by
  simp [ConversionAgreement, or_imp, forall_and]

variable (source target : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (source.headTyping h u)] [∀ h, Decidable (source.isUniverse h)]
variable [∀ u v w, Decidable (source.join u v w)] [∀ u v, Decidable (source.cumulative u v)]
variable [∀ h u, Decidable (target.headTyping h u)] [∀ h, Decidable (target.isUniverse h)]
variable [∀ u v w, Decidable (target.join u v w)] [∀ u v, Decidable (target.cumulative u v)]
variable (first second : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)

set_option maxHeartbeats 1600000 in
/-- A complete typing replay has the same Boolean result under locally
agreeing declarations and conversion requests. No acceptance premise is used. -/
theorem check_eq_of_agreement (policy : PolicyAgreement source target)
    {n : Nat} (code : Code Head ConversionCode n) :
    ∀ (context : Ctx Head n) (subject type : Tm Head n),
      DeclarationAgreement source target (code.declarationRequests source subject type) →
      ConversionAgreement first second code.conversionRequests →
      check source first context subject type code = check target second context subject type code := by
  induction code with
  | const u formation ih =>
      intro context subject type declarations conversions
      cases subject <;> simp only [check]
      rename_i name
      simp only [Code.declarationRequests, declarationAgreement_cons] at declarations
      rw [← declarations.1]
      cases known : source.constantType name with
      | none => rfl
      | some declared =>
          simp only [known] at declarations
          simp only [policy.isUniverse, ih .nil declared (.head u) declarations.2 conversions]
  | convert A u sourceCode formation conversion ihSource ihFormation =>
      intro context subject type declarations conversions
      simp only [Code.declarationRequests, declarationAgreement_append] at declarations
      simp only [Code.conversionRequests, conversionAgreement_cons,
        conversionAgreement_append] at conversions
      simp only [check, policy.isUniverse,
        ihSource context subject A declarations.1 conversions.2.1,
        ihFormation context type (.head u) declarations.2 conversions.2.2, conversions.1]
  | cumul u term ih =>
      intros context subject type declarations conversions
      cases type <;>
        simp_all [check, Code.declarationRequests, Code.conversionRequests, policy.cumulative]
  | _ =>
      intros context subject type declarations conversions
      cases subject <;> simp only [check]
      all_goals cases type <;>
        simp_all [Code.declarationRequests, Code.conversionRequests,
          policy.headTyping, policy.isUniverse, policy.join]

def ContextCode.declarationRequests (source : Rules Head) : {n : Nat} →
    Ctx Head n → ContextCode Head ConversionCode n → List DeclName
  | _, .nil, .nil => []
  | _, .snoc context type, .snoc prior u formation =>
      prior.declarationRequests source context ++ formation.declarationRequests source type (.head u)

def ContextCode.conversionRequests : {n : Nat} → ContextCode Head ConversionCode n →
    List (Σ n, ConversionCode n)
  | _, .nil => []
  | _, .snoc prior _ formation => prior.conversionRequests ++ formation.conversionRequests

theorem checkContext_eq_of_agreement (policy : PolicyAgreement source target)
    {n : Nat} (code : ContextCode Head ConversionCode n) :
    ∀ (context : Ctx Head n),
      DeclarationAgreement source target (code.declarationRequests source context) →
      ConversionAgreement first second code.conversionRequests →
      checkContext source first context code = checkContext target second context code := by
  induction code with
  | nil => intro context _ _; cases context; rfl
  | snoc prior u formation ih =>
      intro context declarations conversions
      cases context with
      | snoc context type =>
          simp only [ContextCode.declarationRequests, declarationAgreement_append] at declarations
          simp only [ContextCode.conversionRequests, conversionAgreement_append] at conversions
          simp only [checkContext, policy.isUniverse,
            ih context declarations.1 conversions.1,
            check_eq_of_agreement source target first second policy formation
              context type (.head u) declarations.2 conversions.2]

/-- The support of the displayed term alone is insufficient: dependencies of
ambient assumption formation are retained too. -/
theorem checkJudgment_eq_of_agreement (policy : PolicyAgreement source target)
    {n : Nat} (context : Ctx Head n) (subject type : Tm Head n)
    (contextCode : ContextCode Head ConversionCode n) (termCode : Code Head ConversionCode n)
    (declarations : DeclarationAgreement source target
      (contextCode.declarationRequests source context ++ termCode.declarationRequests source subject type))
    (conversions : ConversionAgreement first second
      (contextCode.conversionRequests ++ termCode.conversionRequests)) :
    checkJudgment source first context subject type contextCode termCode =
      checkJudgment target second context subject type contextCode termCode := by
  rw [declarationAgreement_append] at declarations
  rw [conversionAgreement_append] at conversions
  simp only [checkJudgment,
    checkContext_eq_of_agreement source target first second policy contextCode
      context declarations.1 conversions.1,
    check_eq_of_agreement source target first second policy termCode
      context subject type declarations.2 conversions.2]

def declarationAgreementCheck (source target : Rules Head)
    (names : List DeclName) : Bool :=
  names.all fun name => decide (source.constantType name = target.constantType name)

@[simp] theorem declarationAgreementCheck_iff (source target : Rules Head)
    (names : List DeclName) :
    declarationAgreementCheck source target names = true ↔ DeclarationAgreement source target names := by
  simp [declarationAgreementCheck, DeclarationAgreement]

section StructuralConversion

variable {RootCode : Nat → Type}

/-- Flatten only the finitely many root-decoder requests present in the
conversion certificates. All intermediate binder scopes remain attached. -/
def conversionRootRequests
    (requests : List (Σ n, StructuralConversionCode.Code Head RootCode n)) :
    List (StructuralConversionCode.RootRequest RootCode) :=
  requests.flatMap fun request => request.2.rootRequests

variable (headEq : Head → Head → Prop) [DecidableRel headEq]
variable (decodeSource decodeTarget : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))

theorem conversionAgreement_of_rootAgreement
    (requests : List (Σ n, StructuralConversionCode.Code Head RootCode n))
    (agree : StructuralConversionCode.AgreeOn (conversionRootRequests requests) decodeSource decodeTarget) :
    ConversionAgreement (StructuralConversionCode.Code.check headEq decodeSource)
      (StructuralConversionCode.Code.check headEq decodeTarget) requests := by
  intro request member left right
  apply StructuralConversionCode.Code.check_eq_of_agreeOn headEq
  intro root rootMember
  exact agree root (List.mem_flatMap.mpr ⟨request, member, rootMember⟩)

/-- Executable comparison of the complete judgment's finite support. It
compares declaration types and full root-decoder outputs, including failure. -/
def judgmentDependencyCheck {n : Nat} (context : Ctx Head n) (subject type : Tm Head n)
    (contextCode : ContextCode Head (StructuralConversionCode.Code Head RootCode) n)
    (termCode : Code Head (StructuralConversionCode.Code Head RootCode) n) : Bool :=
  declarationAgreementCheck source target
    (contextCode.declarationRequests source context ++ termCode.declarationRequests source subject type) &&
  StructuralConversionCode.agreeOnCheck
    (conversionRootRequests (contextCode.conversionRequests ++ termCode.conversionRequests))
      decodeSource decodeTarget

/-- A successful finite comparison preserves the actual full checker, not
merely the existence of another derivation or another certificate. -/
theorem checkJudgment_eq_of_dependencyCheck (policy : PolicyAgreement source target)
    {n : Nat} (context : Ctx Head n) (subject type : Tm Head n)
    (contextCode : ContextCode Head (StructuralConversionCode.Code Head RootCode) n)
    (termCode : Code Head (StructuralConversionCode.Code Head RootCode) n)
    (compared : judgmentDependencyCheck source target decodeSource decodeTarget
      context subject type contextCode termCode = true) :
    checkJudgment source (StructuralConversionCode.Code.check headEq decodeSource)
        context subject type contextCode termCode =
      checkJudgment target (StructuralConversionCode.Code.check headEq decodeTarget)
        context subject type contextCode termCode := by
  simp only [judgmentDependencyCheck, Bool.and_eq_true, declarationAgreementCheck_iff,
    StructuralConversionCode.agreeOnCheck_iff] at compared
  exact checkJudgment_eq_of_agreement source target _ _ policy context subject type
    contextCode termCode compared.1
    (conversionAgreement_of_rootAgreement headEq decodeSource decodeTarget _ compared.2)

end StructuralConversion

#print axioms check_eq_of_agreement
#print axioms checkContext_eq_of_agreement
#print axioms checkJudgment_eq_of_agreement
#print axioms checkJudgment_eq_of_dependencyCheck

end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
