/-
# Profile-parametric LF proof checker

This is the Lean reference for the open obligation recorded at
`MettaKernel/OBLIGATIONS.md:55`: one structurally total checker generated from
the statics, with `checkProof = accept ↔ Deriv`.  It is parameterized by the
PTS profile from `Profiles.lean`; no kernel profile is hidden in the rules.

The checker is deliberately conversion-free.  Types in Var, Con, Lam, and App
premises must agree syntactically.  Real DTTBench therefore does not route
through this checker: it requires a separately proved conversion-capable
LF/MIK frontend.  `Canonical.lean` supplies the simple-erasure canonical-action
substrate; it does not normalize or authenticate the existing DTTBench traces.
-/

import Mettapedia.GSLT.LanguageDef.LF.Canonical
import Mettapedia.GSLT.LanguageDef.LFTyping

namespace Mettapedia.GSLT.LanguageDef.LFProfileChecker

open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFProfile

abbrev Signature := Mettapedia.GSLT.LanguageDef.LFTyping.Sig
abbrev Context := Mettapedia.GSLT.LanguageDef.LFTyping.Ctx

def signatureType := Mettapedia.GSLT.LanguageDef.LFTyping.sigT
def contextType := Mettapedia.GSLT.LanguageDef.LFTyping.ctxLookup
def subst0 := Mettapedia.GSLT.LanguageDef.LFTyping.subst0

/-- Conversion-free declarative PTS statics, stated once over profile data. -/
inductive Deriv (profile : Profile) (signature : Signature) :
    Context → Term → Term → Prop where
  | sort {context source target} :
      profile.sortAxiom source = some target →
      Deriv profile signature context (.srt source) (.srt target)
  | var {context index type} :
      contextType context index = some type →
      Deriv profile signature context (.var index) type
  | con {context name type} :
      signatureType signature name = some type →
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
      Deriv profile signature (domain :: context) bodyType (.srt codomainSort) →
      (⟨domainSort, codomainSort, resultSort⟩ : ProductRule) ∈
        profile.products →
      Deriv profile signature context (.lam domain body) (.pi domain bodyType)
  | app {context function argument domain bodyType} :
      Deriv profile signature context function (.pi domain bodyType) →
      Deriv profile signature context argument domain →
      Deriv profile signature context (.app function argument)
        (subst0 argument bodyType)

/-- Declarative statics are monotone in the profile lattice. -/
theorem Deriv.mono {first second : Profile} (hprofiles : first ⊑ second)
    {signature : Signature} {context : Context} {term type : Term}
    (derivation : Deriv first signature context term type) :
    Deriv second signature context term type := by
  induction derivation with
  | sort haxiom => exact .sort (hprofiles.1 _ _ haxiom)
  | var hlookup => exact .var hlookup
  | con hlookup => exact .con hlookup
  | pi _ _ hrule ihDomain ihBody =>
      exact .pi ihDomain ihBody (hprofiles.2 _ hrule)
  | lam _ _ _ hrule ihDomain ihBody ihBodyType =>
      exact .lam ihDomain ihBody ihBodyType (hprofiles.2 _ hrule)
  | app _ _ ihFunction ihArgument =>
      exact .app ihFunction ihArgument

/-- T1 transport for complete typing derivations, not just formations. -/
theorem basic_deriv_embed {signature : Signature} {context : Context}
    {term type : Term} (derivation : Deriv basic signature context term type) :
    Deriv indexed signature context term type :=
  derivation.mono basic_subsumed_indexed

/-- Explicit proof trees consumed by the executable checker. -/
inductive Proof where
  | sort
  | var
  | con
  | pi (domainSort codomainSort resultSort : Srt)
      (domain body : Proof)
  | lam (domainSort codomainSort resultSort : Srt)
      (domain body bodyType : Proof)
  | app (domain bodyType : Term) (function argument : Proof)
  deriving Repr

/-- Structurally total proof checker.  Every recursive call consumes a proper
subtree of the producer-supplied proof. -/
def checkProof (profile : Profile) (signature : Signature)
    (context : Context) : Proof → Term → Term → Bool
  | .sort, .srt source, .srt target =>
      decide (profile.sortAxiom source = some target)
  | .var, .var index, type =>
      decide (contextType context index = some type)
  | .con, .con name, type =>
      decide (signatureType signature name = some type)
  | .pi domainSort codomainSort resultSort domainProof bodyProof,
      .pi domain body, .srt claimedSort =>
      decide (claimedSort = resultSort) &&
      decide ((⟨domainSort, codomainSort, resultSort⟩ : ProductRule) ∈
        profile.products) &&
      checkProof profile signature context domainProof domain (.srt domainSort) &&
      checkProof profile signature (domain :: context) bodyProof body
        (.srt codomainSort)
  | .lam domainSort codomainSort resultSort domainProof bodyProof typeProof,
      .lam domain body, .pi claimedDomain bodyType =>
      decide (claimedDomain = domain) &&
      decide ((⟨domainSort, codomainSort, resultSort⟩ : ProductRule) ∈
        profile.products) &&
      checkProof profile signature context domainProof domain (.srt domainSort) &&
      checkProof profile signature (domain :: context) bodyProof body bodyType &&
      checkProof profile signature (domain :: context) typeProof bodyType
        (.srt codomainSort)
  | .app domain bodyType functionProof argumentProof,
      .app function argument, claimedType =>
      decide (claimedType = subst0 argument bodyType) &&
      checkProof profile signature context functionProof function
        (.pi domain bodyType) &&
      checkProof profile signature context argumentProof argument domain
  | _, _, _ => false

/-- Soundness half of the checker contract. -/
theorem checkProof_sound {profile : Profile} {signature : Signature}
    {context : Context} {proof : Proof} {term type : Term}
    (hcheck : checkProof profile signature context proof term type = true) :
    Deriv profile signature context term type := by
  induction proof generalizing context term type with
  | sort =>
      cases term <;> cases type <;> simp [checkProof] at hcheck
      exact .sort hcheck
  | var =>
      cases term <;> simp [checkProof] at hcheck
      exact .var hcheck
  | con =>
      cases term <;> simp [checkProof] at hcheck
      exact .con hcheck
  | pi domainSort codomainSort resultSort domainProof bodyProof
      ihDomain ihBody =>
      cases term <;> cases type <;> simp [checkProof] at hcheck
      obtain ⟨⟨⟨hsort, hrule⟩, hdomain⟩, hbody⟩ := hcheck
      cases hsort
      exact .pi (ihDomain hdomain) (ihBody hbody) hrule
  | lam domainSort codomainSort resultSort domainProof bodyProof typeProof
      ihDomain ihBody ihType =>
      cases term <;> cases type <;> simp [checkProof] at hcheck
      obtain ⟨⟨⟨⟨hdomainEq, hrule⟩, hdomain⟩, hbody⟩, htype⟩ := hcheck
      cases hdomainEq
      exact .lam (ihDomain hdomain) (ihBody hbody) (ihType htype) hrule
  | app domain bodyType functionProof argumentProof ihFunction ihArgument =>
      cases term <;> simp [checkProof] at hcheck
      obtain ⟨⟨htype, hfunction⟩, hargument⟩ := hcheck
      cases htype
      exact .app (ihFunction hfunction) (ihArgument hargument)

/-- Completeness half: every declarative derivation has an accepted proof tree. -/
theorem exists_checkProof_of_deriv {profile : Profile} {signature : Signature}
    {context : Context} {term type : Term}
    (derivation : Deriv profile signature context term type) :
    ∃ proof, checkProof profile signature context proof term type = true := by
  induction derivation with
  | sort haxiom =>
      exact ⟨.sort, by simp [checkProof, haxiom]⟩
  | var hlookup =>
      exact ⟨.var, by simp [checkProof, hlookup]⟩
  | con hlookup =>
      exact ⟨.con, by simp [checkProof, hlookup]⟩
  | @pi context domain body domainSort codomainSort resultSort
      hdomain hbody hrule ihDomain ihBody =>
      obtain ⟨domainProof, hdomainProof⟩ := ihDomain
      obtain ⟨bodyProof, hbodyProof⟩ := ihBody
      exact ⟨.pi domainSort codomainSort resultSort domainProof bodyProof,
        by simp [checkProof, hrule, hdomainProof, hbodyProof]⟩
  | @lam context domain body bodyType domainSort codomainSort resultSort
      hdomain hbody htype hrule ihDomain ihBody ihType =>
      obtain ⟨domainProof, hdomainProof⟩ := ihDomain
      obtain ⟨bodyProof, hbodyProof⟩ := ihBody
      obtain ⟨typeProof, htypeProof⟩ := ihType
      exact ⟨.lam domainSort codomainSort resultSort
        domainProof bodyProof typeProof,
        by simp [checkProof, hrule, hdomainProof, hbodyProof, htypeProof]⟩
  | @app context function argument domain bodyType
      hfunction hargument ihFunction ihArgument =>
      obtain ⟨functionProof, hfunctionProof⟩ := ihFunction
      obtain ⟨argumentProof, hargumentProof⟩ := ihArgument
      exact ⟨.app domain bodyType functionProof argumentProof,
        by simp [checkProof, hfunctionProof, hargumentProof]⟩

/-- Profile-parametric checker crown in the exact obligation shape. -/
theorem exists_checkProof_iff_deriv {profile : Profile} {signature : Signature}
    {context : Context} {term type : Term} :
    (∃ proof, checkProof profile signature context proof term type = true) ↔
      Deriv profile signature context term type := by
  constructor
  · rintro ⟨proof, hcheck⟩
    exact checkProof_sound hcheck
  · exact exists_checkProof_of_deriv

/-- T4 indexed-instance crown. -/
theorem indexed_check_accept_iff_deriv {signature : Signature}
    {context : Context} {term type : Term} :
    (∃ proof, checkProof indexed signature context proof term type = true) ↔
      Deriv indexed signature context term type :=
  exists_checkProof_iff_deriv

/-! ## Positive and negative profile/boundary fixtures -/

def typeParameterProof : Proof :=
  .pi .kind .kind .kind .sort .sort

theorem indexed_accepts_typeParameterProduct :
    checkProof indexed [] [] typeParameterProof
      (.pi (.srt .type) (.srt .type)) (.srt .kind) = true := by
  decide

theorem basic_rejects_typeParameterProduct :
    checkProof basic [] [] typeParameterProof
      (.pi (.srt .type) (.srt .type)) (.srt .kind) = false := by
  decide

def betaRedexType : Term :=
  .app (.lam (.srt .type) (.var 0)) (.srt .type)

def exactTypeSignature : Signature :=
  [.const "betaTyped" betaRedexType]

theorem exact_type_accepts :
    checkProof indexed exactTypeSignature [] .con (.con "betaTyped")
      betaRedexType = true := by
  decide

/-- Boundary fixture matching the Eq_symm diagnostic in miniature: a
beta-equivalent but syntactically different expected type is rejected. -/
theorem beta_equivalent_type_is_not_syntactically_accepted :
    checkProof indexed exactTypeSignature [] .con (.con "betaTyped")
      (.srt .type) = false := by
  decide

#print axioms Deriv.mono
#print axioms checkProof_sound
#print axioms exists_checkProof_of_deriv
#print axioms exists_checkProof_iff_deriv
#print axioms indexed_check_accept_iff_deriv
#print axioms beta_equivalent_type_is_not_syntactically_accepted

end Mettapedia.GSLT.LanguageDef.LFProfileChecker
