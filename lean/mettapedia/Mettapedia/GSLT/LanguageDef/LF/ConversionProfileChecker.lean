import Mettapedia.GSLT.LanguageDef.LF.BetaEtaConversion
import Mettapedia.GSLT.LanguageDef.LF.Profiles

/-!
# Conversion-capable profile-parametric LF checker

This is the executable reference for the indexed LF product profile combined
with beta-delta-eta conversion.  The checker first establishes that a claimed
type itself has a sort, then compares inferred and claimed types through the
proved conversion normalizer.  Its soundness theorem targets an independently
stated declarative typing relation.

The implementation is generic in the PTS profile and finite LF signature.  It
contains no DTTBench-specific rule or term.
-/

namespace Mettapedia.GSLT.LanguageDef.LFConversionProfileChecker

open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping
open Mettapedia.GSLT.LanguageDef.LFProfile
open Mettapedia.GSLT.LanguageDef.LFBetaEta

/-- Select the first product rule for a pair of premise sorts. -/
def productResult? : List ProductRule → Srt → Srt → Option Srt
  | [], _, _ => none
  | rule :: rules, domain, codomain =>
      if rule.domain = domain ∧ rule.codomain = codomain then
        some rule.result
      else
        productResult? rules domain codomain

theorem productResult?_mem {rules : List ProductRule}
    {domain codomain result : Srt}
    (hresult : productResult? rules domain codomain = some result) :
    (⟨domain, codomain, result⟩ : ProductRule) ∈ rules := by
  induction rules with
  | nil => simp [productResult?] at hresult
  | cons rule rules ih =>
      simp only [productResult?] at hresult
      split at hresult
      · rename_i hmatch
        rcases hmatch with ⟨hdomain, hcodomain⟩
        cases hdomain
        cases hcodomain
        simp only [Option.some.injEq] at hresult
        cases hresult
        simp
      · exact List.mem_cons_of_mem _ (ih hresult)

/-- Declarative profile-parametric LF typing with explicit conversion. -/
inductive Deriv (profile : Profile) (signature : Sig) :
    Ctx → Term → Term → Prop where
  | sort {context source target} :
      profile.sortAxiom source = some target →
      Deriv profile signature context (.srt source) (.srt target)
  | var {context index type} :
      ctxLookup context index = some type →
      Deriv profile signature context (.var index) type
  | con {context name type} :
      sigT signature name = some type →
      Deriv profile signature context (.con name) type
  | pi {context domain body domainSort codomainSort resultSort} :
      Deriv profile signature context domain (.srt domainSort) →
      Deriv profile signature (domain :: context) body (.srt codomainSort) →
      (⟨domainSort, codomainSort, resultSort⟩ : ProductRule) ∈
        profile.products →
      Deriv profile signature context (.pi domain body) (.srt resultSort)
  | lam {context domain body bodyType domainSort codomainSort resultSort} :
      Deriv profile signature context domain (.srt domainSort) →
      Deriv profile signature (domain :: context) body bodyType →
      Deriv profile signature (domain :: context) bodyType
        (.srt codomainSort) →
      (⟨domainSort, codomainSort, resultSort⟩ : ProductRule) ∈
        profile.products →
      Deriv profile signature context (.lam domain body)
        (.pi domain bodyType)
  | app {context function argument domain bodyType} :
      Deriv profile signature context function (.pi domain bodyType) →
      Deriv profile signature context argument domain →
      Deriv profile signature context (.app function argument)
        (subst0 argument bodyType)
  | conv {context term source target} :
      Deriv profile signature context term source →
      LFBetaEta.Conv signature source target →
      Deriv profile signature context term target

/-- Normalize an inferred type and expose its sort, if it is one. -/
def normalizedSort? (signature : Sig) (fuel : Nat) (type : Term) : Option Srt :=
  match normalForm signature fuel type with
  | .srt sort => some sort
  | _ => none

theorem normalizedSort?_eq_some_iff {signature : Sig} {fuel : Nat}
    {type : Term} {sort : Srt} :
    normalizedSort? signature fuel type = some sort ↔
      normalForm signature fuel type = .srt sort := by
  cases hnormal : normalForm signature fuel type <;>
    simp [normalizedSort?, hnormal]

mutual

/-- Fuel-bounded inference over a selectable product profile. -/
def infer : Nat → Profile → Sig → Ctx → Term → Option Term
  | 0, _, _, _, _ => none
  | remaining + 1, profile, signature, context, term =>
      match term with
          | .srt source => (profile.sortAxiom source).map .srt
          | .con name => sigT signature name
          | .var index => ctxLookup context index
          | .pi domain body =>
              match infer remaining profile signature context domain with
              | some domainType =>
                  match normalizedSort? signature remaining domainType with
                  | some domainSort =>
                      match infer remaining profile signature
                          (domain :: context) body with
                      | some bodyType =>
                          match normalizedSort? signature remaining bodyType with
                          | some codomainSort =>
                              (productResult? profile.products domainSort
                                codomainSort).map .srt
                          | none => none
                      | none => none
                  | none => none
              | none => none
          | .lam domain body =>
              match infer remaining profile signature context domain with
              | some domainType =>
                  match normalizedSort? signature remaining domainType with
                  | some domainSort =>
                      match infer remaining profile signature
                          (domain :: context) body with
                      | some bodyType =>
                          match infer remaining profile signature
                              (domain :: context) bodyType with
                          | some bodyTypeType =>
                              match normalizedSort? signature remaining
                                  bodyTypeType with
                              | some codomainSort =>
                                  match productResult? profile.products
                                      domainSort codomainSort with
                                  | some _ => some (.pi domain bodyType)
                                  | none => none
                              | none => none
                          | none => none
                      | none => none
                  | none => none
              | none => none
          | .app function argument =>
              match infer remaining profile signature context function with
              | some functionType =>
                  match normalForm signature remaining functionType with
                  | .pi domain bodyType =>
                      if check remaining profile signature context argument
                          domain then
                        some (subst0 argument bodyType)
                      else
                        none
                  | _ => none
              | none => none

/-- Checking additionally rejects a claimed type that does not itself have a
sort. -/
def check : Nat → Profile → Sig → Ctx → Term → Term → Bool
  | 0, _, _, _, _, _ => false
  | remaining + 1, profile, signature, context, term, type =>
      match infer remaining profile signature context type with
      | some typeType =>
          match normalizedSort? signature remaining typeType with
          | none => false
          | some _ =>
              match infer remaining profile signature context term with
              | none => false
              | some inferred =>
                  LFBetaEta.convBool signature remaining inferred type
      | none => false

end

private theorem Deriv.convert_normalForm {profile : Profile}
    {signature : Sig} {context : Ctx} {term type : Term} {fuel : Nat}
    (derivation : Deriv profile signature context term type) :
    Deriv profile signature context term
      (normalForm signature fuel type) :=
  .conv derivation
    (.common (normalForm_sound signature fuel type) .refl)

/-- Mutual soundness of inference and checking. -/
theorem infer_check_sound : ∀ fuel,
    (∀ profile signature context term type,
      infer fuel profile signature context term = some type →
      Deriv profile signature context term type) ∧
    (∀ profile signature context term type,
      check fuel profile signature context term type = true →
      Deriv profile signature context term type) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro profile signature context term type h
        simp [infer] at h
      · intro profile signature context term type h
        simp [check] at h
  | succ fuel ih =>
      constructor
      · intro profile signature context term type h
        cases term with
        | srt source =>
            simp only [infer] at h
            cases haxiom : profile.sortAxiom source with
            | none => simp [haxiom] at h
            | some target =>
                simp [haxiom] at h
                cases h
                exact .sort haxiom
        | con name =>
            simp [infer] at h
            exact .con h
        | var index =>
            simp [infer] at h
            exact .var h
        | pi domain body =>
            simp only [infer] at h
            split at h <;> try contradiction
            rename_i domainType hdomain
            split at h <;> try contradiction
            rename_i domainSort hdomainSort
            split at h <;> try contradiction
            rename_i bodyType hbody
            split at h <;> try contradiction
            rename_i codomainSort hcodomainSort
            cases hproduct :
                productResult? profile.products domainSort codomainSort with
            | none => simp [hproduct] at h
            | some resultSort =>
                simp [hproduct] at h
                cases h
                have domainDerivation :=
                  (ih.1 profile signature context domain domainType) hdomain
                have bodyDerivation :=
                  (ih.1 profile signature (domain :: context) body bodyType)
                    hbody
                have domainNormalized :=
                  domainDerivation.convert_normalForm (fuel := fuel)
                have bodyNormalized :=
                  bodyDerivation.convert_normalForm (fuel := fuel)
                rw [normalizedSort?_eq_some_iff.mp hdomainSort] at domainNormalized
                rw [normalizedSort?_eq_some_iff.mp hcodomainSort] at bodyNormalized
                exact .pi domainNormalized bodyNormalized
                  (productResult?_mem hproduct)
        | lam domain body =>
            simp only [infer] at h
            split at h <;> try contradiction
            rename_i domainType hdomain
            split at h <;> try contradiction
            rename_i domainSort hdomainSort
            split at h <;> try contradiction
            rename_i bodyType hbody
            split at h <;> try contradiction
            rename_i bodyTypeType hbodyType
            split at h <;> try contradiction
            rename_i codomainSort hcodomainSort
            cases hproduct :
                productResult? profile.products domainSort codomainSort with
            | none => simp [hproduct] at h
            | some resultSort =>
                simp [hproduct] at h
                cases h
                have domainDerivation :=
                  (ih.1 profile signature context domain domainType) hdomain
                have bodyDerivation :=
                  (ih.1 profile signature (domain :: context) body bodyType)
                    hbody
                have bodyTypeDerivation :=
                  (ih.1 profile signature (domain :: context) bodyType
                    bodyTypeType) hbodyType
                have domainNormalized :=
                  domainDerivation.convert_normalForm (fuel := fuel)
                have bodyTypeNormalized :=
                  bodyTypeDerivation.convert_normalForm (fuel := fuel)
                rw [normalizedSort?_eq_some_iff.mp hdomainSort] at domainNormalized
                rw [normalizedSort?_eq_some_iff.mp hcodomainSort] at bodyTypeNormalized
                exact .lam domainNormalized bodyDerivation bodyTypeNormalized
                  (productResult?_mem hproduct)
        | app function argument =>
            simp only [infer] at h
            split at h <;> try contradiction
            rename_i functionType hfunction
            split at h <;> try contradiction
            rename_i domain bodyType hfunctionNormal
            split at h <;> try contradiction
            rename_i hargument
            cases h
            have functionDerivation :=
              (ih.1 profile signature context function functionType) hfunction
            have functionNormalized :=
              functionDerivation.convert_normalForm (fuel := fuel)
            rw [hfunctionNormal] at functionNormalized
            exact .app functionNormalized
              ((ih.2 profile signature context argument domain) hargument)
      · intro profile signature context term type h
        simp only [check] at h
        split at h <;> try contradiction
        rename_i typeType htype
        split at h <;> try contradiction
        rename_i typeSort htypeSort
        split at h <;> try contradiction
        rename_i inferred hinfer
        exact .conv
          ((ih.1 profile signature context term inferred) hinfer)
          (convBool_sound h)

/-- Soundness crown for the conversion-capable checker. -/
theorem S1 {fuel : Nat} {profile : Profile} {signature : Sig}
    {context : Ctx} {term type : Term}
    (hcheck : check fuel profile signature context term type = true) :
    Deriv profile signature context term type :=
  (infer_check_sound fuel).2 profile signature context term type hcheck

/-! ## Positive and negative executable fixtures -/

private def typeTerm : Term := .srt .type
private def typeIdentity : Term := .lam typeTerm (.var 0)
private def typeIdentityType : Term := .pi typeTerm typeTerm

theorem indexed_accepts_type_identity :
    check 64 indexed [] [] typeIdentity typeIdentityType = true := by
  decide

theorem basic_rejects_type_identity :
    check 64 basic [] [] typeIdentity typeIdentityType = false := by
  decide

private def etaConstructorType : Term := .pi typeTerm typeTerm
private def etaPredicateType : Term :=
  .pi etaConstructorType typeTerm
private def etaExpandedConstructor : Term :=
  .lam typeTerm (.app (.con "F") (.var 0))
private def etaActualType : Term := .app (.con "P") (.con "F")
private def etaExpectedType : Term :=
  .app (.con "P") etaExpandedConstructor
private def etaSignature : Sig :=
  [.const "F" etaConstructorType,
   .const "P" etaPredicateType,
   .const "x" etaActualType]

/-- The typing checker uses eta conversion in a type argument, not merely in an
isolated Boolean fixture. -/
theorem indexed_accepts_eta_equivalent_type :
    check 128 indexed etaSignature [] (.con "x") etaExpectedType = true := by
  decide

private def unrelatedExpectedType : Term :=
  .app (.con "P") (.lam typeTerm typeTerm)

theorem indexed_rejects_nonconvertible_type :
    check 128 indexed etaSignature [] (.con "x") unrelatedExpectedType =
      false := by
  decide

theorem indexed_eta_fixture_sound :
    Deriv indexed etaSignature [] (.con "x") etaExpectedType :=
  S1 indexed_accepts_eta_equivalent_type

#print axioms productResult?_mem
#print axioms infer_check_sound
#print axioms S1
#print axioms indexed_eta_fixture_sound

end Mettapedia.GSLT.LanguageDef.LFConversionProfileChecker
