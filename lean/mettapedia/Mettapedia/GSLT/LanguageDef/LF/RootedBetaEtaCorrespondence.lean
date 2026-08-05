import Mettapedia.GSLT.LanguageDef.LF.BetaEtaConversion
import Mettapedia.GSLT.LanguageDef.LF.RootedBetaEtaConversion

/-!
# Runtime LF to rooted beta-eta correspondence

The executable LF checker uses `LF.Term`, while the generic GSLT inference
checker consumes locally nameless `Pattern`s.  This module defines one total
encoding between those carriers and proves that their binding operations
agree:

* LF lifting is `Pattern` bound-variable lifting;
* LF beta substitution is generic binder elimination;
* LF eta freshness is generic unused-binder elimination;
* well-scoped LF terms become ground patterns at the same depth.

These results bind the runtime beta-eta operations to the rooted language
without replacing either implementation by the other.
-/

namespace Mettapedia.GSLT.LanguageDef.LFRootedBetaEtaCorrespondence

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping
open Mettapedia.GSLT.LanguageDef.LFBetaEta
open Mettapedia.GSLT.LanguageDef.LFRootedBetaEtaConversion
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CheckedSource
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

/-- A collision-free atom representation for an LF constant name. -/
def encodeName (name : String) : Pattern :=
  .apply "LFNameLiteral" [.apply name []]

/-- Encode the executable LF carrier into the rooted GSLT carrier. -/
def encodeTerm : LF.Term → Pattern
  | .srt .type => typeTerm
  | .srt .kind => kindTerm
  | .con name => con (encodeName name)
  | .var index => .bvar index
  | .pi domain body => pi (encodeTerm domain) (encodeTerm body)
  | .lam domain body => lam (encodeTerm domain) (encodeTerm body)
  | .app function argument => app (encodeTerm function) (encodeTerm argument)

/-- Partial inverse of the tagged LF-name encoding. -/
def decodeName? : Pattern → Option String
  | .apply "LFNameLiteral" [.apply name []] => some name
  | _ => none

/-- Partial inverse of `encodeTerm` on rooted LF patterns. -/
def decodeTerm? : Pattern → Option LF.Term
  | .apply "Srt" [.apply "SortType" []] => some (.srt .type)
  | .apply "Srt" [.apply "SortKind" []] => some (.srt .kind)
  | .apply "Con" [name] => do
      pure (.con (← decodeName? name))
  | .bvar index => some (.var index)
  | .apply "Pi" [domain, .lambda none body] => do
      pure (.pi (← decodeTerm? domain) (← decodeTerm? body))
  | .apply "Lam" [domain, .lambda none body] => do
      pure (.lam (← decodeTerm? domain) (← decodeTerm? body))
  | .apply "App" [function, argument] => do
      pure (.app (← decodeTerm? function) (← decodeTerm? argument))
  | _ => none

theorem decodeName?_encodeName (name : String) :
    decodeName? (encodeName name) = some name := by
  simp [decodeName?, encodeName]

/-- The carrier encoding is lossless on every executable LF term. -/
theorem decodeTerm?_encodeTerm (term : LF.Term) :
    decodeTerm? (encodeTerm term) = some term := by
  induction term with
  | srt sort =>
      cases sort <;>
        simp [decodeTerm?, encodeTerm, typeTerm, kindTerm, srt, sortType,
          sortKind]
  | con name =>
      simp [decodeTerm?, encodeTerm, con, decodeName?_encodeName]
  | var index =>
      simp [decodeTerm?, encodeTerm]
  | pi domain body domainIH bodyIH =>
      simp [decodeTerm?, encodeTerm, pi, domainIH, bodyIH]
  | lam domain body domainIH bodyIH =>
      simp [decodeTerm?, encodeTerm, lam, domainIH, bodyIH]
  | app function argument functionIH argumentIH =>
      simp [decodeTerm?, encodeTerm, app, functionIH, argumentIH]

/-- Distinct runtime LF terms remain distinct at the rooted carrier. -/
theorem encodeTerm_injective : Function.Injective encodeTerm := by
  intro first second hequal
  apply Option.some.inj
  calc
    some first = decodeTerm? (encodeTerm first) :=
      (decodeTerm?_encodeTerm first).symm
    _ = decodeTerm? (encodeTerm second) := congrArg decodeTerm? hequal
    _ = some second := decodeTerm?_encodeTerm second

/-- General LF lifting is exactly the generic locally nameless lifting
operation after encoding. -/
theorem encodeTerm_lift (distance cutoff : Nat) (term : LF.Term) :
    encodeTerm (LFTyping.lift distance cutoff term) =
      liftBVars cutoff distance (encodeTerm term) := by
  induction term generalizing cutoff with
  | srt sort =>
      cases sort <;>
        simp [encodeTerm, LFTyping.lift, liftBVars, typeTerm, kindTerm, srt,
          sortType, sortKind]
  | con name =>
      simp [encodeTerm, LFTyping.lift, liftBVars, con, encodeName]
  | var index =>
      by_cases hindex : index < cutoff
      · simp [encodeTerm, LFTyping.lift, liftBVars, hindex,
          Nat.not_le.mpr hindex]
      · have hcutoff : cutoff ≤ index := Nat.le_of_not_gt hindex
        simp [encodeTerm, LFTyping.lift, liftBVars, hindex, hcutoff]
  | pi domain body domainIH bodyIH =>
      simp [encodeTerm, LFTyping.lift, liftBVars, pi, domainIH, bodyIH]
  | lam domain body domainIH bodyIH =>
      simp [encodeTerm, LFTyping.lift, liftBVars, lam, domainIH, bodyIH]
  | app function argument functionIH argumentIH =>
      simp [encodeTerm, LFTyping.lift, liftBVars, app, functionIH,
        argumentIH]

/-- Lifts at one cutoff compose by adding their distances. -/
theorem lift_lift_same_cutoff (first second cutoff : Nat) (term : LF.Term) :
    LFTyping.lift second cutoff (LFTyping.lift first cutoff term) =
      LFTyping.lift (first + second) cutoff term := by
  induction term generalizing cutoff with
  | srt sort => cases sort <;> simp [LFTyping.lift]
  | con name => simp [LFTyping.lift]
  | var index =>
      by_cases hindex : index < cutoff
      · simp [LFTyping.lift, hindex]
      · have hcutoff : cutoff ≤ index := Nat.le_of_not_gt hindex
        have hshifted : ¬index + first < cutoff := by omega
        simp [LFTyping.lift, hindex, hshifted, Nat.add_assoc]
  | pi domain body domainIH bodyIH =>
      simp [LFTyping.lift, domainIH, bodyIH]
  | lam domain body domainIH bodyIH =>
      simp [LFTyping.lift, domainIH, bodyIH]
  | app function argument functionIH argumentIH =>
      simp [LFTyping.lift, functionIH, argumentIH]

/-- A zero-distance LF lift is the identity. -/
theorem lift_zero_distance (cutoff : Nat) (term : LF.Term) :
    LFTyping.lift 0 cutoff term = term := by
  induction term generalizing cutoff with
  | srt sort => cases sort <;> simp [LFTyping.lift]
  | con name => simp [LFTyping.lift]
  | var index =>
      by_cases hindex : index < cutoff <;>
        simp [LFTyping.lift, hindex]
  | pi domain body domainIH bodyIH =>
      simp [LFTyping.lift, domainIH, bodyIH]
  | lam domain body domainIH bodyIH =>
      simp [LFTyping.lift, domainIH, bodyIH]
  | app function argument functionIH argumentIH =>
      simp [LFTyping.lift, functionIH, argumentIH]

/-- Substituting the replacement lifted through `depth` surrounding binders
matches generic binder elimination at that depth. -/
theorem encodeTerm_subst_lifted
    (depth : Nat) (replacement term : LF.Term) :
    encodeTerm
        (LFTyping.subst depth (LFTyping.lift depth 0 replacement) term) =
      instantiateBVarAt depth (encodeTerm replacement) (encodeTerm term) := by
  induction term generalizing depth with
  | srt sort =>
      cases sort <;>
        simp [encodeTerm, LFTyping.subst, instantiateBVarAt, typeTerm,
          kindTerm, srt, sortType, sortKind]
  | con name =>
      simp [encodeTerm, LFTyping.subst, instantiateBVarAt, con, encodeName]
  | var index =>
      by_cases hequal : index = depth
      · subst index
        simp [encodeTerm, LFTyping.subst, instantiateBVarAt,
          encodeTerm_lift]
      · by_cases habove : depth < index
        · have hnotBelow : ¬index < depth := by omega
          simp [encodeTerm, LFTyping.subst, instantiateBVarAt, hequal,
            habove, hnotBelow]
        · have hbelow : index < depth := by omega
          simp [encodeTerm, LFTyping.subst, instantiateBVarAt, hequal,
            habove, hbelow]
  | pi domain body domainIH bodyIH =>
      simp only [LFTyping.subst, encodeTerm, pi, instantiateBVarAt]
      rw [domainIH]
      have hlift :
          LFTyping.lift 1 0 (LFTyping.lift depth 0 replacement) =
            LFTyping.lift (depth + 1) 0 replacement := by
        simpa using lift_lift_same_cutoff depth 1 0 replacement
      rw [hlift, bodyIH]
      simp [instantiateBVarAt]
  | lam domain body domainIH bodyIH =>
      simp only [LFTyping.subst, encodeTerm, lam, instantiateBVarAt]
      rw [domainIH]
      have hlift :
          LFTyping.lift 1 0 (LFTyping.lift depth 0 replacement) =
            LFTyping.lift (depth + 1) 0 replacement := by
        simpa using lift_lift_same_cutoff depth 1 0 replacement
      rw [hlift, bodyIH]
      simp [instantiateBVarAt]
  | app function argument functionIH argumentIH =>
      simp [LFTyping.subst, encodeTerm, app, instantiateBVarAt,
        functionIH, argumentIH]

/-- Runtime beta substitution is exactly the rooted beta rule's checked
binder elimination. -/
theorem encodeTerm_subst0 (replacement body : LF.Term) :
    encodeTerm (LFTyping.subst0 replacement body) =
      instantiateBVar (encodeTerm replacement) (encodeTerm body) := by
  simpa [LFTyping.subst0, instantiateBVar, lift_zero_distance] using
    (encodeTerm_subst_lifted 0 replacement body)

/-- Runtime eta freshness is exactly the rooted eta rule's checked
unused-binder elimination. -/
theorem encodeTerm_unbind (cutoff : Nat) (term : LF.Term) :
    Option.map encodeTerm (LFBetaEta.unbind cutoff term) =
      dropBVarAt? cutoff (encodeTerm term) := by
  induction term generalizing cutoff with
  | srt sort =>
      cases sort <;>
        simp [LFBetaEta.unbind, encodeTerm, dropBVarAt?, typeTerm, kindTerm,
          srt, sortType, sortKind]
  | con name =>
      simp [LFBetaEta.unbind, encodeTerm, dropBVarAt?, con, encodeName]
  | var index =>
      by_cases hbelow : index < cutoff
      · simp [LFBetaEta.unbind, encodeTerm, dropBVarAt?, hbelow]
      · by_cases hequal : index = cutoff
        · simp [LFBetaEta.unbind, encodeTerm, dropBVarAt?, hequal]
        · simp [LFBetaEta.unbind, encodeTerm, dropBVarAt?, hbelow, hequal]
  | pi domain body domainIH bodyIH =>
      cases hdomain : LFBetaEta.unbind cutoff domain <;>
        cases hbody : LFBetaEta.unbind (cutoff + 1) body
      all_goals
        have hdomainDrop := (domainIH cutoff).symm
        have hbodyDrop := (bodyIH (cutoff + 1)).symm
        rw [hdomain] at hdomainDrop
        rw [hbody] at hbodyDrop
        simp at hdomainDrop hbodyDrop
        simp [LFBetaEta.unbind, hdomain, hbody, encodeTerm, dropBVarAt?, pi,
          hdomainDrop, hbodyDrop]
  | lam domain body domainIH bodyIH =>
      cases hdomain : LFBetaEta.unbind cutoff domain <;>
        cases hbody : LFBetaEta.unbind (cutoff + 1) body
      all_goals
        have hdomainDrop := (domainIH cutoff).symm
        have hbodyDrop := (bodyIH (cutoff + 1)).symm
        rw [hdomain] at hdomainDrop
        rw [hbody] at hbodyDrop
        simp at hdomainDrop hbodyDrop
        simp [LFBetaEta.unbind, hdomain, hbody, encodeTerm, dropBVarAt?, lam,
          hdomainDrop, hbodyDrop]
  | app function argument functionIH argumentIH =>
      cases hfunction : LFBetaEta.unbind cutoff function <;>
        cases hargument : LFBetaEta.unbind cutoff argument
      all_goals
        have hfunctionDrop := (functionIH cutoff).symm
        have hargumentDrop := (argumentIH cutoff).symm
        rw [hfunction] at hfunctionDrop
        rw [hargument] at hargumentDrop
        simp at hfunctionDrop hargumentDrop
        simp [LFBetaEta.unbind, hfunction, hargument, encodeTerm,
          dropBVarAt?, app, hfunctionDrop, hargumentDrop]

/-- The executable LF scope judgment and the generic rooted groundness check
agree in the sound direction needed by proof-certificate arguments. -/
theorem encodeTerm_isGroundAt {depth : Nat} {term : LF.Term}
    (hscoped : LF.WellScoped depth term) :
    (encodeTerm term).isGroundAt depth = true := by
  induction hscoped with
  | srt =>
      cases ‹Srt› <;>
        simp [encodeTerm, Pattern.isGroundAt, Pattern.isGroundListAt,
          typeTerm, kindTerm, srt, sortType, sortKind]
  | con =>
      simp [encodeTerm, Pattern.isGroundAt, Pattern.isGroundListAt, con,
        encodeName]
  | var hindex =>
      simp [encodeTerm, Pattern.isGroundAt, hindex]
  | pi _ _ domainIH bodyIH =>
      simp [encodeTerm, pi, Pattern.isGroundAt, Pattern.isGroundListAt,
        domainIH, bodyIH]
  | lam _ _ domainIH bodyIH =>
      simp [encodeTerm, lam, Pattern.isGroundAt, Pattern.isGroundListAt,
        domainIH, bodyIH]
  | app _ _ functionIH argumentIH =>
      simp [encodeTerm, app, Pattern.isGroundAt, Pattern.isGroundListAt,
        functionIH, argumentIH]

/-- Every encoded LF term uses canonical anonymous binder metadata. -/
theorem encodeTerm_hasCanonicalBinderMetadata (term : LF.Term) :
    (encodeTerm term).hasCanonicalBinderMetadata = true := by
  induction term with
  | srt sort =>
      cases sort <;>
        simp [encodeTerm, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList, typeTerm, kindTerm, srt,
          sortType, sortKind]
  | con name =>
      simp [encodeTerm, con, encodeName, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | var index =>
      simp [encodeTerm, Pattern.hasCanonicalBinderMetadata]
  | pi domain body domainIH bodyIH =>
      simp [encodeTerm, pi, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, domainIH, bodyIH]
  | lam domain body domainIH bodyIH =>
      simp [encodeTerm, lam, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, domainIH, bodyIH]
  | app function argument functionIH argumentIH =>
      simp [encodeTerm, app, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, functionIH, argumentIH]

/-- A runtime scope derivation supplies the exact argument-validity premise
required by a rooted rule instance. -/
theorem encodeTerm_argumentValidAt {depth : Nat} {term : LF.Term}
    (hscoped : LF.WellScoped depth term) :
    argumentValidAt depth (encodeTerm term) = true := by
  simp [argumentValidAt, encodeTerm_isGroundAt hscoped,
    encodeTerm_hasCanonicalBinderMetadata]

/-- The beta side condition accepts every runtime substitution result. -/
theorem beta_side_condition_accepts
    (domain body argument result : LF.Term)
    (hresult : LFTyping.subst0 argument body = result) :
    RuleSideCondition.holds
        [encodeTerm domain, encodeTerm body, encodeTerm argument,
          encodeTerm result]
        (.explicitSubstitution 0 1 2 3) = true := by
  subst result
  simp [RuleSideCondition.holds, encodeTerm_subst0]

/-- If the rooted beta side condition accepts an encoded result, that result
is the runtime substitution result. -/
theorem beta_side_condition_reflects
    (domain body argument result : LF.Term)
    (hcheck :
      RuleSideCondition.holds
          [encodeTerm domain, encodeTerm body, encodeTerm argument,
            encodeTerm result]
          (.explicitSubstitution 0 1 2 3) = true) :
    LFTyping.subst0 argument body = result := by
  simp [RuleSideCondition.holds] at hcheck
  apply encodeTerm_injective
  simpa [encodeTerm_subst0] using hcheck

/-- The eta side condition accepts every runtime unused-binder result. -/
theorem eta_side_condition_accepts
    (domain function result : LF.Term)
    (hresult : LFBetaEta.unbind 0 function = some result) :
    RuleSideCondition.holds
        [encodeTerm domain, encodeTerm function, encodeTerm result]
        (.unusedBinderElimination 0 1 2) = true := by
  have hencoded := encodeTerm_unbind 0 function
  rw [hresult] at hencoded
  simp only [Option.map_some] at hencoded
  simp [RuleSideCondition.holds, dropBVar?, ← hencoded]

/-- Rooted eta acceptance of encoded terms reflects the runtime freshness
test and its exact decremented result. -/
theorem eta_side_condition_reflects
    (domain function result : LF.Term)
    (hcheck :
      RuleSideCondition.holds
          [encodeTerm domain, encodeTerm function, encodeTerm result]
          (.unusedBinderElimination 0 1 2) = true) :
    LFBetaEta.unbind 0 function = some result := by
  simp [RuleSideCondition.holds] at hcheck
  have hencoded := encodeTerm_unbind 0 function
  simp only [dropBVar?] at hcheck
  rw [hcheck] at hencoded
  cases hunbind : LFBetaEta.unbind 0 function with
  | none => simp [hunbind] at hencoded
  | some reduced =>
      simp only [hunbind, Option.map_some, Option.some.injEq] at hencoded
      have : reduced = result := encodeTerm_injective hencoded
      subst result
      rfl

/-! ## Runtime-produced raw rule certificates -/

/-- Raw rooted beta proof emitted from executable LF terms. -/
def betaRawProof
    (domain body argument result : LF.Term) : RawProof :=
  .node
    { ruleId := ruleId "lf-conv-beta"
      arguments :=
        [encodeTerm domain, encodeTerm body, encodeTerm argument,
          encodeTerm result] }
    []

/-- Raw rooted eta proof emitted from executable LF terms. -/
def etaRawProof (domain function result : LF.Term) : RawProof :=
  .node
    { ruleId := ruleId "lf-conv-eta"
      arguments := [encodeTerm domain, encodeTerm function, encodeTerm result] }
    []

/-- A well-scoped runtime beta contraction is accepted by the generic rooted
checker, with no LF-specific checker branch. -/
theorem betaRawProof_accepts
    {domain body argument result : LF.Term}
    (hdomain : LF.WellScoped 0 domain)
    (hbody : LF.WellScoped 1 body)
    (hargument : LF.WellScoped 0 argument)
    (hresultScoped : LF.WellScoped 0 result)
    (hresult : LFTyping.subst0 argument body = result) :
    checked.checkRaw
        (converts
          (app (lam (encodeTerm domain) (encodeTerm body))
            (encodeTerm argument))
          (encodeTerm result))
        (betaRawProof domain body argument result) = true := by
  have hdomainGround := encodeTerm_isGroundAt hdomain
  have hbodyGround := encodeTerm_isGroundAt hbody
  have hargumentGround := encodeTerm_isGroundAt hargument
  have hresultGround := encodeTerm_isGroundAt hresultScoped
  have hsubstitution :
      instantiateBVar (encodeTerm argument) (encodeTerm body) =
        encodeTerm result := by
    rw [← encodeTerm_subst0, hresult]
  simp [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
    InferenceChecker.checkRawChildren,
    CheckedGSLT.presentation, checked,
    source, presentation, language, betaRawProof, betaRule, etaRule,
    appCongruenceRule, piCongruenceRule, lamCongruenceRule,
    conversionDeclaration, instantiateRule?, Presentation.lookupRule?,
    argumentsValidAt, argumentValidAt, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, RuleSchema.sideConditionsHold,
    RuleSideCondition.holds, hdomainGround, hbodyGround, hargumentGround,
    hresultGround, hsubstitution, encodeTerm_hasCanonicalBinderMetadata,
    converts, app, lam, ruleId]

/-- A well-scoped runtime eta contraction is accepted by the generic rooted
checker after the executable freshness test succeeds. -/
theorem etaRawProof_accepts
    {domain function result : LF.Term}
    (hdomain : LF.WellScoped 0 domain)
    (hfunction : LF.WellScoped 1 function)
    (hresultScoped : LF.WellScoped 0 result)
    (hresult : LFBetaEta.unbind 0 function = some result) :
    checked.checkRaw
        (converts
          (lam (encodeTerm domain)
            (app (encodeTerm function) (.bvar 0)))
          (encodeTerm result))
        (etaRawProof domain function result) = true := by
  have hdrop := encodeTerm_unbind 0 function
  rw [hresult] at hdrop
  simp only [Option.map_some] at hdrop
  have hdomainGround := encodeTerm_isGroundAt hdomain
  have hfunctionGround := encodeTerm_isGroundAt hfunction
  have hresultGround := encodeTerm_isGroundAt hresultScoped
  simp [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
    InferenceChecker.checkRawChildren,
    CheckedGSLT.presentation, checked,
    source, presentation, language, etaRawProof, betaRule, etaRule,
    appCongruenceRule, piCongruenceRule, lamCongruenceRule,
    conversionDeclaration, instantiateRule?, Presentation.lookupRule?,
    argumentsValidAt, argumentValidAt, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, RuleSchema.sideConditionsHold,
    RuleSideCondition.holds, hdomainGround, hfunctionGround, hresultGround,
    encodeTerm_hasCanonicalBinderMetadata, dropBVar?, ← hdrop,
    converts, app, lam, ruleId]

/-! ## Executable positive and negative correspondence fixtures -/

private def runtimeType : LF.Term := .srt .type
private def runtimeIdentity : LF.Term := .lam runtimeType (.var 0)

theorem beta_fixture_corresponds :
    encodeTerm (LFTyping.subst0 runtimeType (.var 0)) =
      instantiateBVar (encodeTerm runtimeType) (encodeTerm (.var 0)) := by
  exact encodeTerm_subst0 _ _

theorem eta_fixture_corresponds :
    Option.map encodeTerm (LFBetaEta.unbind 0 (.var 1)) =
      dropBVarAt? 0 (encodeTerm (.var 1)) := by
  exact encodeTerm_unbind _ _

/-- Captured eta is rejected by both representations. -/
theorem captured_eta_rejected_on_both_sides :
    LFBetaEta.unbind 0 (.var 0) = none ∧
      dropBVarAt? 0 (encodeTerm (.var 0)) = none := by
  simp [LFBetaEta.unbind, encodeTerm, dropBVarAt?]

#print axioms encodeTerm_lift
#print axioms decodeTerm?_encodeTerm
#print axioms encodeTerm_injective
#print axioms lift_lift_same_cutoff
#print axioms lift_zero_distance
#print axioms encodeTerm_subst_lifted
#print axioms encodeTerm_subst0
#print axioms encodeTerm_unbind
#print axioms encodeTerm_isGroundAt
#print axioms encodeTerm_argumentValidAt
#print axioms beta_side_condition_reflects
#print axioms eta_side_condition_reflects
#print axioms betaRawProof_accepts
#print axioms etaRawProof_accepts
#print axioms captured_eta_rejected_on_both_sides

end Mettapedia.GSLT.LanguageDef.LFRootedBetaEtaCorrespondence
