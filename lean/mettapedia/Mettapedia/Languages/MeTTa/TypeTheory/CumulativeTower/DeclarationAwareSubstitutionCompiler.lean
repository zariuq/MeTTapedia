import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionSemantics

/-!
# Proof-producing compiler for authored Prime substitution

This module compiles the independent first-order weakening and substitution
functions to raw proof trees accepted by the generic declaration-aware
checker.  The compiler is not trusted: its output is ordinary data, and each
universal acceptance theorem is proved against the validated authored rule
inventory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionCompiler

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwarePatternCodec
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionLanguage
open Mettapedia.OSLF.MeTTaIL.Syntax

namespace Sem

abbrev encode {Head : Type} (headCodec : PartialCodec Head Pattern)
    (term : DeclarationAwareSubstitutionSemantics.RawTm Head) : Pattern :=
  DeclarationAwareSubstitutionSemantics.encode headCodec term

abbrev weakenAt {Head : Type} (cutoff : Nat)
    (term : DeclarationAwareSubstitutionSemantics.RawTm Head) :
    DeclarationAwareSubstitutionSemantics.RawTm Head :=
  DeclarationAwareSubstitutionSemantics.weakenAt cutoff term

end Sem

abbrev RawTerm :=
  DeclarationAwareSubstitutionSemantics.RawTm Presentation.Tower.Head

def encodeRaw (term : RawTerm) : Pattern :=
  DeclarationAwareSubstitutionSemantics.encode towerHeadCodec term

def weakenRaw (cutoff : Nat) (term : RawTerm) : RawTerm :=
  DeclarationAwareSubstitutionSemantics.weakenAt cutoff term

def substituteRaw (index : Nat) (replacement term : RawTerm) : RawTerm :=
  DeclarationAwareSubstitutionSemantics.substituteAt index replacement term

/-! These equations deliberately expose only the public first-order boundary.
They keep generic-checker proofs independent of the implementation details of
the intrinsic scoped syntax. -/

@[simp] theorem encodeRaw_var (index : Nat) :
    encodeRaw (.var index) = tmVar (encodeNat index) := rfl

@[simp] theorem encodeRaw_const (name : Lean.Name) :
    encodeRaw (.const name) = tmConst (encodeDeclName name) := rfl

@[simp] theorem encodeRaw_head (head : Presentation.Tower.Head) :
    encodeRaw (.head head) = tmHead (towerHeadCodec.encode head) := rfl

@[simp] theorem encodeRaw_pi (domain body : RawTerm) :
    encodeRaw (.pi domain body) = tmPi (encodeRaw domain) (encodeRaw body) := rfl

@[simp] theorem encodeRaw_sigma (domain body : RawTerm) :
    encodeRaw (.sigma domain body) =
      tmSigma (encodeRaw domain) (encodeRaw body) := rfl

@[simp] theorem encodeRaw_id (type left right : RawTerm) :
    encodeRaw (.id type left right) =
      tmId (encodeRaw type) (encodeRaw left) (encodeRaw right) := rfl

@[simp] theorem encodeRaw_lam (body : RawTerm) :
    encodeRaw (.lam body) = tmLam (encodeRaw body) := rfl

@[simp] theorem encodeRaw_app (function argument : RawTerm) :
    encodeRaw (.app function argument) =
      tmApp (encodeRaw function) (encodeRaw argument) := rfl

@[simp] theorem encodeRaw_pair (first second : RawTerm) :
    encodeRaw (.pair first second) =
      tmPair (encodeRaw first) (encodeRaw second) := rfl

@[simp] theorem encodeRaw_fst (pair : RawTerm) :
    encodeRaw (.fst pair) = tmFst (encodeRaw pair) := rfl

@[simp] theorem encodeRaw_snd (pair : RawTerm) :
    encodeRaw (.snd pair) = tmSnd (encodeRaw pair) := rfl

@[simp] theorem encodeRaw_refl (term : RawTerm) :
    encodeRaw (.refl term) = tmRefl (encodeRaw term) := rfl

@[simp] theorem weakenRaw_var_below {index cutoff : Nat}
    (below : index < cutoff) :
    weakenRaw cutoff (.var index) = .var index := by
  simp [weakenRaw, DeclarationAwareSubstitutionSemantics.weakenAt, below]

@[simp] theorem weakenRaw_var_atOrAbove {index cutoff : Nat}
    (notBelow : ¬ index < cutoff) :
    weakenRaw cutoff (.var index) = .var (index + 1) := by
  simp [weakenRaw, DeclarationAwareSubstitutionSemantics.weakenAt, notBelow]

@[simp] theorem weakenRaw_const (cutoff : Nat) (name : Lean.Name) :
    weakenRaw cutoff (.const name) = .const name := rfl

@[simp] theorem weakenRaw_head (cutoff : Nat)
    (head : Presentation.Tower.Head) :
    weakenRaw cutoff (.head head) = .head head := rfl

@[simp] theorem weakenRaw_pi (cutoff : Nat) (domain body : RawTerm) :
    weakenRaw cutoff (.pi domain body) =
      .pi (weakenRaw cutoff domain) (weakenRaw (cutoff + 1) body) := rfl

@[simp] theorem weakenRaw_sigma (cutoff : Nat) (domain body : RawTerm) :
    weakenRaw cutoff (.sigma domain body) =
      .sigma (weakenRaw cutoff domain) (weakenRaw (cutoff + 1) body) := rfl

@[simp] theorem weakenRaw_id (cutoff : Nat) (type left right : RawTerm) :
    weakenRaw cutoff (.id type left right) =
      .id (weakenRaw cutoff type) (weakenRaw cutoff left)
        (weakenRaw cutoff right) := rfl

@[simp] theorem weakenRaw_lam (cutoff : Nat) (body : RawTerm) :
    weakenRaw cutoff (.lam body) = .lam (weakenRaw (cutoff + 1) body) := rfl

@[simp] theorem weakenRaw_app (cutoff : Nat) (function argument : RawTerm) :
    weakenRaw cutoff (.app function argument) =
      .app (weakenRaw cutoff function) (weakenRaw cutoff argument) := rfl

@[simp] theorem weakenRaw_pair (cutoff : Nat) (first second : RawTerm) :
    weakenRaw cutoff (.pair first second) =
      .pair (weakenRaw cutoff first) (weakenRaw cutoff second) := rfl

@[simp] theorem weakenRaw_fst (cutoff : Nat) (pair : RawTerm) :
    weakenRaw cutoff (.fst pair) = .fst (weakenRaw cutoff pair) := rfl

@[simp] theorem weakenRaw_snd (cutoff : Nat) (pair : RawTerm) :
    weakenRaw cutoff (.snd pair) = .snd (weakenRaw cutoff pair) := rfl

@[simp] theorem weakenRaw_refl (cutoff : Nat) (term : RawTerm) :
    weakenRaw cutoff (.refl term) = .refl (weakenRaw cutoff term) := rfl

@[simp] theorem substituteRaw_var_equal (index : Nat) (replacement : RawTerm) :
    substituteRaw index replacement (.var index) = replacement := by
  simp [substituteRaw, DeclarationAwareSubstitutionSemantics.substituteAt]

@[simp] theorem substituteRaw_var_below {variableIndex index : Nat}
    (replacement : RawTerm) (notEqual : variableIndex ≠ index)
    (below : variableIndex < index) :
    substituteRaw index replacement (.var variableIndex) =
      .var variableIndex := by
  simp [substituteRaw, DeclarationAwareSubstitutionSemantics.substituteAt,
    notEqual, below]

@[simp] theorem substituteRaw_var_above {variableIndex index : Nat}
    (replacement : RawTerm) (notEqual : variableIndex ≠ index)
    (notBelow : ¬ variableIndex < index) :
    substituteRaw index replacement (.var variableIndex) =
      .var (variableIndex - 1) := by
  simp [substituteRaw, DeclarationAwareSubstitutionSemantics.substituteAt,
    notEqual, notBelow]

@[simp] theorem substituteRaw_const (index : Nat) (replacement : RawTerm)
    (name : Lean.Name) :
    substituteRaw index replacement (.const name) = .const name := rfl

@[simp] theorem substituteRaw_head (index : Nat) (replacement : RawTerm)
    (head : Presentation.Tower.Head) :
    substituteRaw index replacement (.head head) = .head head := rfl

@[simp] theorem substituteRaw_pi (index : Nat) (replacement domain body : RawTerm) :
    substituteRaw index replacement (.pi domain body) =
      .pi (substituteRaw index replacement domain)
        (substituteRaw (index + 1) (weakenRaw 0 replacement) body) := rfl

@[simp] theorem substituteRaw_sigma
    (index : Nat) (replacement domain body : RawTerm) :
    substituteRaw index replacement (.sigma domain body) =
      .sigma (substituteRaw index replacement domain)
        (substituteRaw (index + 1) (weakenRaw 0 replacement) body) := rfl

@[simp] theorem substituteRaw_id
    (index : Nat) (replacement type left right : RawTerm) :
    substituteRaw index replacement (.id type left right) =
      .id (substituteRaw index replacement type)
        (substituteRaw index replacement left)
        (substituteRaw index replacement right) := rfl

@[simp] theorem substituteRaw_lam (index : Nat)
    (replacement body : RawTerm) :
    substituteRaw index replacement (.lam body) =
      .lam (substituteRaw (index + 1) (weakenRaw 0 replacement) body) := rfl

@[simp] theorem substituteRaw_app (index : Nat)
    (replacement function argument : RawTerm) :
    substituteRaw index replacement (.app function argument) =
      .app (substituteRaw index replacement function)
        (substituteRaw index replacement argument) := rfl

@[simp] theorem substituteRaw_pair (index : Nat)
    (replacement first second : RawTerm) :
    substituteRaw index replacement (.pair first second) =
      .pair (substituteRaw index replacement first)
        (substituteRaw index replacement second) := rfl

@[simp] theorem substituteRaw_fst (index : Nat)
    (replacement pair : RawTerm) :
    substituteRaw index replacement (.fst pair) =
      .fst (substituteRaw index replacement pair) := rfl

@[simp] theorem substituteRaw_snd (index : Nat)
    (replacement pair : RawTerm) :
    substituteRaw index replacement (.snd pair) =
      .snd (substituteRaw index replacement pair) := rfl

@[simp] theorem substituteRaw_refl (index : Nat)
    (replacement term : RawTerm) :
    substituteRaw index replacement (.refl term) =
      .refl (substituteRaw index replacement term) := rfl

@[simp] theorem encodeRaw_argumentValid (term : RawTerm) :
    argumentValidAt 0 (encodeRaw term) = true := by
  exact DeclarationAwareSubstitutionSemantics.encode_argumentValid term

@[simp] theorem encodeDeclName_argumentValid_local (name : Lean.Name) :
    argumentValidAt 0 (encodeDeclName name) = true := by
  simp [argumentValidAt, encodeDeclName_ground, encodeDeclName_canonical]

@[simp] theorem towerHeadCodec_argumentValid
    (head : Presentation.Tower.Head) :
    argumentValidAt 0 (towerHeadCodec.encode head) = true := by
  simpa [towerHeadCodec] using encodeTowerHead_argumentValid head

/-! ## Peano order certificates -/

/-- Compile the unique proof of a true Peano inequality.  False comparisons
land on an invalid rule identifier and therefore cannot be accepted. -/
def ltRawProof : Nat → Nat → RawProof
  | 0, right + 1 =>
      rawProof "prime-index-lt-zero-succ" [encodeNat right] []
  | left + 1, right + 1 =>
      rawProof "prime-index-lt-succ-succ" [encodeNat left, encodeNat right]
        [ltRawProof left right]
  | _, _ => rawProof "prime-invalid-index-lt" [] []

/-- Every true comparison compiles to a proof accepted by the generic
checker. -/
theorem ltRawProof_accepts {left right : Nat} (less : left < right) :
    checkRaw definition (indexLt (encodeNat left) (encodeNat right))
      (ltRawProof left right) = true := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero => omega
      | succ right =>
          simp (config := { maxSteps := 1000000, decide := true })
            [definition, substitutionExtension,
             ValidatedCalculusLanguageExtension.target,
             substitutionDelta, CalculusLanguageExtension.apply, allRules,
             ltRawProof, rawProof, ltZeroSuccRule, rule, formal, m,
             InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
             instantiateRule?, CalculusLanguageDef.lookupRule?,
             instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
             instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
             encodeNat_argumentValid, indexLt, encodeNat, zero, succ, ruleId,
             DeclarationAwareDataLanguage.checked,
             DeclarationAwareDataLanguage.definition]
  | succ left leftIH =>
      cases right with
      | zero => omega
      | succ right =>
          have previous : left < right := by omega
          have child := leftIH previous
          simp (config := { maxSteps := 1000000, decide := true })
            [definition, substitutionExtension,
             ValidatedCalculusLanguageExtension.target,
             substitutionDelta, CalculusLanguageExtension.apply, allRules,
             ltRawProof, rawProof, ltSuccSuccRule, rule, formal, m,
             InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
             instantiateRule?, CalculusLanguageDef.lookupRule?,
             instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
             instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
             encodeNat_argumentValid, indexLt, encodeNat, succ, ruleId,
             DeclarationAwareDataLanguage.checked,
             DeclarationAwareDataLanguage.definition]
          simpa [definition, substitutionExtension,
            ValidatedCalculusLanguageExtension.target,
            substitutionDelta, CalculusLanguageExtension.apply, allRules,
            ltSuccSuccRule, rule, formal, m, indexLt, succ, ruleId,
            DeclarationAwareDataLanguage.checked,
            DeclarationAwareDataLanguage.definition] using child

/-! ## Weakening certificates -/

/-- Compile first-order weakening by one at an arbitrary cutoff. -/
def weakenRawProof (cutoff : Nat) : RawTerm → RawProof
  | .var index =>
      if index < cutoff then
        rawProof "prime-weaken-var-below" [encodeNat cutoff, encodeNat index]
          [ltRawProof index cutoff]
      else
        rawProof "prime-weaken-var-at-or-above"
          [encodeNat cutoff, encodeNat index]
          [ltRawProof cutoff (index + 1)]
  | .const name =>
      rawProof "prime-weaken-const" [encodeNat cutoff, encodeDeclName name] []
  | .head head =>
      rawProof "prime-weaken-head"
        [encodeNat cutoff, towerHeadCodec.encode head] []
  | .pi domain body =>
      rawProof "prime-weaken-pi"
        [encodeNat cutoff, encodeRaw domain, encodeRaw body,
          encodeRaw (weakenRaw cutoff domain),
          encodeRaw (weakenRaw (cutoff + 1) body)]
        [weakenRawProof cutoff domain, weakenRawProof (cutoff + 1) body]
  | .sigma domain body =>
      rawProof "prime-weaken-sigma"
        [encodeNat cutoff, encodeRaw domain, encodeRaw body,
          encodeRaw (weakenRaw cutoff domain),
          encodeRaw (weakenRaw (cutoff + 1) body)]
        [weakenRawProof cutoff domain, weakenRawProof (cutoff + 1) body]
  | .id type left right =>
      rawProof "prime-weaken-id"
        [encodeNat cutoff, encodeRaw type, encodeRaw left, encodeRaw right,
          encodeRaw (weakenRaw cutoff type),
          encodeRaw (weakenRaw cutoff left),
          encodeRaw (weakenRaw cutoff right)]
        [weakenRawProof cutoff type, weakenRawProof cutoff left,
          weakenRawProof cutoff right]
  | .lam body =>
      rawProof "prime-weaken-lam"
        [encodeNat cutoff, encodeRaw body,
          encodeRaw (weakenRaw (cutoff + 1) body)]
        [weakenRawProof (cutoff + 1) body]
  | .app function argument =>
      rawProof "prime-weaken-app"
        [encodeNat cutoff, encodeRaw function, encodeRaw argument,
          encodeRaw (weakenRaw cutoff function),
          encodeRaw (weakenRaw cutoff argument)]
        [weakenRawProof cutoff function, weakenRawProof cutoff argument]
  | .pair first second =>
      rawProof "prime-weaken-pair"
        [encodeNat cutoff, encodeRaw first, encodeRaw second,
          encodeRaw (weakenRaw cutoff first),
          encodeRaw (weakenRaw cutoff second)]
        [weakenRawProof cutoff first, weakenRawProof cutoff second]
  | .fst pair =>
      rawProof "prime-weaken-fst"
        [encodeNat cutoff, encodeRaw pair, encodeRaw (weakenRaw cutoff pair)]
        [weakenRawProof cutoff pair]
  | .snd pair =>
      rawProof "prime-weaken-snd"
        [encodeNat cutoff, encodeRaw pair, encodeRaw (weakenRaw cutoff pair)]
        [weakenRawProof cutoff pair]
  | .refl term =>
      rawProof "prime-weaken-refl"
        [encodeNat cutoff, encodeRaw term, encodeRaw (weakenRaw cutoff term)]
        [weakenRawProof cutoff term]

/-- Every independently computed weakening compiles to a certificate accepted
by the actual generic checker. -/
theorem weakenRawProof_accepts (cutoff : Nat) (term : RawTerm) :
    checkRaw definition
      (weakensAt (encodeNat cutoff) (encodeRaw term)
        (encodeRaw (weakenRaw cutoff term)))
      (weakenRawProof cutoff term) = true := by
  induction term generalizing cutoff with
  | var index =>
      by_cases below : index < cutoff
      · have child := ltRawProof_accepts below
        simp (config := { maxSteps := 1000000, decide := true })
          [definition, substitutionExtension,
           ValidatedCalculusLanguageExtension.target,
           substitutionDelta, CalculusLanguageExtension.apply, allRules,
           weakenRawProof,
           rawProof, weakenVarBelowRule, rule, formal, m,
           InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
           instantiateRule?, CalculusLanguageDef.lookupRule?,
           instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
           instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
           encodeNat_argumentValid, weakensAt, indexLt, tmVar, encodeNat,
           zero, succ, ruleId, below,
           DeclarationAwareDataLanguage.checked,
           DeclarationAwareDataLanguage.definition]
        simpa [definition, substitutionExtension,
          ValidatedCalculusLanguageExtension.target,
          substitutionDelta, CalculusLanguageExtension.apply, allRules,
          weakenVarBelowRule, rule, formal, m, weakensAt, indexLt, tmVar,
          ruleId, DeclarationAwareDataLanguage.checked,
          DeclarationAwareDataLanguage.definition] using child
      · have above : cutoff < index + 1 := by omega
        have child := ltRawProof_accepts above
        simp (config := { maxSteps := 1000000, decide := true })
          [definition, substitutionExtension,
           ValidatedCalculusLanguageExtension.target,
           substitutionDelta, CalculusLanguageExtension.apply, allRules,
           weakenRawProof,
           rawProof, weakenVarAtOrAboveRule, rule, formal, m,
           InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
           instantiateRule?, CalculusLanguageDef.lookupRule?,
           instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
           instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
           encodeNat_argumentValid, weakensAt, indexLt, tmVar, encodeNat,
           zero, succ, ruleId, below,
           DeclarationAwareDataLanguage.checked,
           DeclarationAwareDataLanguage.definition]
        simpa [definition, substitutionExtension,
          ValidatedCalculusLanguageExtension.target,
          substitutionDelta, CalculusLanguageExtension.apply, allRules,
          weakenVarAtOrAboveRule, rule, formal, m, weakensAt, indexLt,
          tmVar, encodeNat, succ, ruleId,
          DeclarationAwareDataLanguage.checked,
          DeclarationAwareDataLanguage.definition] using child
  | const name =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
           weakenRawProof,
         rawProof, weakenConstRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?,
         instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
         instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
         encodeNat_argumentValid, encodeDeclName_ground,
         encodeDeclName_canonical, weakensAt, tmConst, ruleId,
         DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
  | head head =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
           weakenRawProof,
         rawProof, weakenHeadRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?,
         instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
         instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
         encodeNat_argumentValid, encodeTowerHead_argumentValid,
         weakensAt, tmHead, ruleId,
         DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
  | pi domain body domainIH bodyIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
           weakenRawProof,
         rawProof, weakenPiRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?,
         instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
         instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
         encodeNat_argumentValid, encodeRaw_argumentValid,
         weakensAt, tmPi, succ, encodeNat, ruleId,
         DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
      exact ⟨domainIH cutoff, bodyIH (cutoff + 1)⟩
  | sigma domain body domainIH bodyIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
           weakenRawProof,
         rawProof, weakenSigmaRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?,
         instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
         instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
         encodeNat_argumentValid, encodeRaw_argumentValid,
         weakensAt, tmSigma, succ, encodeNat, ruleId,
         DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
      exact ⟨domainIH cutoff, bodyIH (cutoff + 1)⟩
  | id type left right typeIH leftIH rightIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
           weakenRawProof,
         rawProof, weakenIdRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?,
         instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
         instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
         encodeNat_argumentValid, encodeRaw_argumentValid,
         weakensAt, tmId, ruleId,
         DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
      exact ⟨typeIH cutoff, leftIH cutoff, rightIH cutoff⟩
  | lam body bodyIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
           weakenRawProof,
         rawProof, weakenLamRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?,
         instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
         instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
         encodeNat_argumentValid, encodeRaw_argumentValid,
         weakensAt, tmLam, succ, encodeNat, ruleId,
         DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
      exact bodyIH (cutoff + 1)
  | app function argument functionIH argumentIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
           weakenRawProof,
         rawProof, weakenAppRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?,
         instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
         instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
         encodeNat_argumentValid, encodeRaw_argumentValid,
         weakensAt, tmApp, ruleId,
         DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
      exact ⟨functionIH cutoff, argumentIH cutoff⟩
  | pair first second firstIH secondIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
           weakenRawProof,
         rawProof, weakenPairRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?,
         instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
         instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
         encodeNat_argumentValid, encodeRaw_argumentValid,
         weakensAt, tmPair, ruleId,
         DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
      exact ⟨firstIH cutoff, secondIH cutoff⟩
  | fst pair pairIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
           weakenRawProof,
         rawProof, weakenFstRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?,
         instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
         instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
         encodeNat_argumentValid, encodeRaw_argumentValid,
         weakensAt, tmFst, ruleId,
         DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
      exact pairIH cutoff
  | snd pair pairIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
           weakenRawProof,
         rawProof, weakenSndRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?,
         instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
         instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
         encodeNat_argumentValid, encodeRaw_argumentValid,
         weakensAt, tmSnd, ruleId,
         DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
      exact pairIH cutoff
  | refl term termIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
         weakenRawProof,
         rawProof, weakenReflRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?,
         instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
         instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
         encodeNat_argumentValid, encodeRaw_argumentValid,
         weakensAt, tmRefl, ruleId,
         DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
      exact termIH cutoff

/-! ## Substitution certificates -/

/-- Compile capture-avoiding substitution at an arbitrary de Bruijn index. -/
def substituteRawProof (index : Nat) (replacement : RawTerm) :
    RawTerm → RawProof
  | .var variableIndex =>
      if variableIndex = index then
        rawProof "prime-subst-var-equal"
          [encodeNat index, encodeRaw replacement] []
      else if variableIndex < index then
        rawProof "prime-subst-var-below"
          [encodeNat index, encodeRaw replacement, encodeNat variableIndex]
          [ltRawProof variableIndex index]
      else
        rawProof "prime-subst-var-above"
          [encodeNat index, encodeRaw replacement,
            encodeNat (variableIndex - 1)]
          [ltRawProof index variableIndex]
  | .const name =>
      rawProof "prime-subst-const"
        [encodeNat index, encodeRaw replacement, encodeDeclName name] []
  | .head head =>
      rawProof "prime-subst-head"
        [encodeNat index, encodeRaw replacement, towerHeadCodec.encode head] []
  | .pi domain body =>
      let liftedReplacement := weakenRaw 0 replacement
      rawProof "prime-subst-pi"
        [encodeNat index, encodeRaw replacement, encodeRaw domain,
          encodeRaw body, encodeRaw (substituteRaw index replacement domain),
          encodeRaw liftedReplacement,
          encodeRaw (substituteRaw (index + 1) liftedReplacement body)]
        [substituteRawProof index replacement domain,
          weakenRawProof 0 replacement,
          substituteRawProof (index + 1) liftedReplacement body]
  | .sigma domain body =>
      let liftedReplacement := weakenRaw 0 replacement
      rawProof "prime-subst-sigma"
        [encodeNat index, encodeRaw replacement, encodeRaw domain,
          encodeRaw body, encodeRaw (substituteRaw index replacement domain),
          encodeRaw liftedReplacement,
          encodeRaw (substituteRaw (index + 1) liftedReplacement body)]
        [substituteRawProof index replacement domain,
          weakenRawProof 0 replacement,
          substituteRawProof (index + 1) liftedReplacement body]
  | .id type left right =>
      rawProof "prime-subst-id"
        [encodeNat index, encodeRaw replacement, encodeRaw type,
          encodeRaw left, encodeRaw right,
          encodeRaw (substituteRaw index replacement type),
          encodeRaw (substituteRaw index replacement left),
          encodeRaw (substituteRaw index replacement right)]
        [substituteRawProof index replacement type,
          substituteRawProof index replacement left,
          substituteRawProof index replacement right]
  | .lam body =>
      let liftedReplacement := weakenRaw 0 replacement
      rawProof "prime-subst-lam"
        [encodeNat index, encodeRaw replacement, encodeRaw body,
          encodeRaw liftedReplacement,
          encodeRaw (substituteRaw (index + 1) liftedReplacement body)]
        [weakenRawProof 0 replacement,
          substituteRawProof (index + 1) liftedReplacement body]
  | .app function argument =>
      rawProof "prime-subst-app"
        [encodeNat index, encodeRaw replacement, encodeRaw function,
          encodeRaw argument,
          encodeRaw (substituteRaw index replacement function),
          encodeRaw (substituteRaw index replacement argument)]
        [substituteRawProof index replacement function,
          substituteRawProof index replacement argument]
  | .pair first second =>
      rawProof "prime-subst-pair"
        [encodeNat index, encodeRaw replacement, encodeRaw first,
          encodeRaw second, encodeRaw (substituteRaw index replacement first),
          encodeRaw (substituteRaw index replacement second)]
        [substituteRawProof index replacement first,
          substituteRawProof index replacement second]
  | .fst pair =>
      rawProof "prime-subst-fst"
        [encodeNat index, encodeRaw replacement, encodeRaw pair,
          encodeRaw (substituteRaw index replacement pair)]
        [substituteRawProof index replacement pair]
  | .snd pair =>
      rawProof "prime-subst-snd"
        [encodeNat index, encodeRaw replacement, encodeRaw pair,
          encodeRaw (substituteRaw index replacement pair)]
        [substituteRawProof index replacement pair]
  | .refl term =>
      rawProof "prime-subst-refl"
        [encodeNat index, encodeRaw replacement, encodeRaw term,
          encodeRaw (substituteRaw index replacement term)]
        [substituteRawProof index replacement term]

private theorem encodeNat_pred_succ {value : Nat} (positive : 0 < value) :
    succ (encodeNat (value - 1)) = encodeNat value := by
  have value_eq : value = (value - 1) + 1 := by omega
  rw [value_eq]
  rfl

/-- Every independently computed capture-avoiding substitution compiles to a
certificate accepted by the actual generic checker. -/
theorem substituteRawProof_accepts
    (index : Nat) (replacement term : RawTerm) :
    checkRaw definition
      (substitutesAt (encodeNat index) (encodeRaw replacement)
        (encodeRaw term) (encodeRaw (substituteRaw index replacement term)))
      (substituteRawProof index replacement term) = true := by
  induction term generalizing index replacement with
  | var variableIndex =>
      by_cases equal : variableIndex = index
      · subst variableIndex
        simp (config := { maxSteps := 1000000, decide := true })
          [definition, substitutionExtension,
           ValidatedCalculusLanguageExtension.target,
           substitutionDelta, CalculusLanguageExtension.apply, allRules,
           substituteRawProof, rawProof, substVarEqualRule, rule, formal, m,
           InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
           instantiateRule?, CalculusLanguageDef.lookupRule?,
           instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
           instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
           encodeNat_argumentValid, encodeRaw_argumentValid,
           substitutesAt, tmVar, ruleId,
           DeclarationAwareDataLanguage.checked,
           DeclarationAwareDataLanguage.definition]
      · by_cases below : variableIndex < index
        · have child := ltRawProof_accepts below
          simp (config := { maxSteps := 1000000, decide := true })
            [definition, substitutionExtension,
             ValidatedCalculusLanguageExtension.target,
             substitutionDelta, CalculusLanguageExtension.apply, allRules,
             substituteRawProof, rawProof, substVarBelowRule, rule, formal, m,
             InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
             instantiateRule?, CalculusLanguageDef.lookupRule?,
             instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
             instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
             encodeNat_argumentValid, encodeRaw_argumentValid,
             substitutesAt, indexLt, tmVar, equal, below, ruleId,
             DeclarationAwareDataLanguage.checked,
             DeclarationAwareDataLanguage.definition]
          simpa [definition, substitutionExtension,
            ValidatedCalculusLanguageExtension.target,
            substitutionDelta, CalculusLanguageExtension.apply, allRules,
            substVarBelowRule, rule, formal, m, substitutesAt, indexLt, tmVar,
            ruleId, DeclarationAwareDataLanguage.checked,
            DeclarationAwareDataLanguage.definition] using child
        · have above : index < variableIndex := by omega
          have positive : 0 < variableIndex := by omega
          have encoded := encodeNat_pred_succ positive
          have child := ltRawProof_accepts above
          have predecessorChild :
              checkRaw definition
                (indexLt (encodeNat index)
                  (succ (encodeNat (variableIndex - 1))))
                (ltRawProof index variableIndex) = true := by
            rw [encoded]
            exact child
          simp (config := { maxSteps := 1000000, decide := true })
            [definition, substitutionExtension,
             ValidatedCalculusLanguageExtension.target,
             substitutionDelta, CalculusLanguageExtension.apply, allRules,
             substituteRawProof, rawProof, substVarAboveRule, rule, formal, m,
             InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
             instantiateRule?, CalculusLanguageDef.lookupRule?,
             instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
             instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
             encodeNat_argumentValid, encodeRaw_argumentValid,
             substitutesAt, indexLt, tmVar, succ, encodeNat, equal, below,
             above, ruleId,
             DeclarationAwareDataLanguage.checked,
             DeclarationAwareDataLanguage.definition]
          constructor
          · exact encoded
          · simpa [definition, substitutionExtension,
              ValidatedCalculusLanguageExtension.target,
              substitutionDelta, CalculusLanguageExtension.apply, allRules,
              substVarAboveRule, rule, formal, m, substitutesAt, indexLt, tmVar,
              succ, ruleId, DeclarationAwareDataLanguage.checked,
              DeclarationAwareDataLanguage.definition] using predecessorChild
  | const name =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
         substituteRawProof, rawProof, substConstRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?, instantiateSchema?,
         instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
         lookupArgumentAt?, argumentsValidAt, encodeNat_argumentValid,
         encodeRaw_argumentValid, substitutesAt, tmConst, ruleId,
         DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
  | head head =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
         substituteRawProof, rawProof, substHeadRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?, instantiateSchema?,
         instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
         lookupArgumentAt?, argumentsValidAt, encodeNat_argumentValid,
         encodeRaw_argumentValid, substitutesAt, tmHead, ruleId,
         DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
  | pi domain body domainIH bodyIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
         substituteRawProof, rawProof, substPiRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?, instantiateSchema?,
         instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
         lookupArgumentAt?, argumentsValidAt, encodeNat_argumentValid,
         encodeRaw_argumentValid, substitutesAt, weakensAt, zero, succ,
         tmPi, ruleId, DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
      exact ⟨domainIH index replacement, weakenRawProof_accepts 0 replacement,
        bodyIH (index + 1) (weakenRaw 0 replacement)⟩
  | sigma domain body domainIH bodyIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
         substituteRawProof, rawProof, substSigmaRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?, instantiateSchema?,
         instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
         lookupArgumentAt?, argumentsValidAt, encodeNat_argumentValid,
         encodeRaw_argumentValid, substitutesAt, weakensAt, zero, succ,
         tmSigma, ruleId, DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
      exact ⟨domainIH index replacement, weakenRawProof_accepts 0 replacement,
        bodyIH (index + 1) (weakenRaw 0 replacement)⟩
  | id type left right typeIH leftIH rightIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
         substituteRawProof, rawProof, substIdRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?, instantiateSchema?,
         instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
         lookupArgumentAt?, argumentsValidAt, encodeNat_argumentValid,
         encodeRaw_argumentValid, substitutesAt, tmId, ruleId,
         DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
      exact ⟨typeIH index replacement, leftIH index replacement,
        rightIH index replacement⟩
  | lam body bodyIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
         substituteRawProof, rawProof, substLamRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?, instantiateSchema?,
         instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
         lookupArgumentAt?, argumentsValidAt, encodeNat_argumentValid,
         encodeRaw_argumentValid, substitutesAt, weakensAt, zero, succ,
         tmLam, ruleId, DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
      exact ⟨weakenRawProof_accepts 0 replacement,
        bodyIH (index + 1) (weakenRaw 0 replacement)⟩
  | app function argument functionIH argumentIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
         substituteRawProof, rawProof, substAppRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?, instantiateSchema?,
         instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
         lookupArgumentAt?, argumentsValidAt, encodeNat_argumentValid,
         encodeRaw_argumentValid, substitutesAt, tmApp, ruleId,
         DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
      exact ⟨functionIH index replacement, argumentIH index replacement⟩
  | pair first second firstIH secondIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
         substituteRawProof, rawProof, substPairRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?, instantiateSchema?,
         instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
         lookupArgumentAt?, argumentsValidAt, encodeNat_argumentValid,
         encodeRaw_argumentValid, substitutesAt, tmPair, ruleId,
         DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
      exact ⟨firstIH index replacement, secondIH index replacement⟩
  | fst pair pairIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
         substituteRawProof, rawProof, substFstRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?, instantiateSchema?,
         instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
         lookupArgumentAt?, argumentsValidAt, encodeNat_argumentValid,
         encodeRaw_argumentValid, substitutesAt, tmFst, ruleId,
         DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
      exact pairIH index replacement
  | snd pair pairIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
         substituteRawProof, rawProof, substSndRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?, instantiateSchema?,
         instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
         lookupArgumentAt?, argumentsValidAt, encodeNat_argumentValid,
         encodeRaw_argumentValid, substitutesAt, tmSnd, ruleId,
         DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
      exact pairIH index replacement
  | refl term termIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [definition, substitutionExtension,
         ValidatedCalculusLanguageExtension.target,
         substitutionDelta, CalculusLanguageExtension.apply, allRules,
         substituteRawProof, rawProof, substReflRule, rule, formal, m,
         InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
         instantiateRule?, CalculusLanguageDef.lookupRule?, instantiateSchema?,
         instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
         lookupArgumentAt?, argumentsValidAt, encodeNat_argumentValid,
         encodeRaw_argumentValid, substitutesAt, tmRefl, ruleId,
         DeclarationAwareDataLanguage.checked,
         DeclarationAwareDataLanguage.definition]
      exact termIH index replacement

/-- Compile one root beta contraction from the same independently computed
substitution target. -/
def betaRawProof (body argument : RawTerm) : RawProof :=
  rawProof "prime-root-beta"
    [encodeRaw body, encodeRaw argument,
      encodeRaw (substituteRaw 0 argument body)]
    [substituteRawProof 0 argument body]

/-- Every independently computed root-beta contraction is accepted by the
generic checker through the authored substitution judgment. -/
theorem betaRawProof_accepts (body argument : RawTerm) :
    checkRaw definition
      (rootBeta (tmApp (tmLam (encodeRaw body)) (encodeRaw argument))
        (encodeRaw (substituteRaw 0 argument body)))
      (betaRawProof body argument) = true := by
  have child := substituteRawProof_accepts 0 argument body
  simp (config := { maxSteps := 1000000, decide := true })
    [definition, substitutionExtension,
     ValidatedCalculusLanguageExtension.target,
     substitutionDelta, CalculusLanguageExtension.apply, allRules,
     betaRawProof, rawProof, rootBetaRule, rule, formal, m,
     InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
     instantiateRule?, CalculusLanguageDef.lookupRule?, instantiateSchema?,
     instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
     lookupArgumentAt?, argumentsValidAt, encodeRaw_argumentValid,
     rootBeta, substitutesAt, zero, tmApp, tmLam, ruleId,
     DeclarationAwareDataLanguage.checked,
     DeclarationAwareDataLanguage.definition]
  simpa [definition, substitutionExtension,
    ValidatedCalculusLanguageExtension.target,
    substitutionDelta, CalculusLanguageExtension.apply, allRules,
    rootBetaRule, rule, formal, m, rootBeta, substitutesAt, zero, encodeNat,
    tmApp, tmLam, ruleId, DeclarationAwareDataLanguage.checked,
    DeclarationAwareDataLanguage.definition] using child

/-! ## Arbitrary-target no-invention for generated artifacts -/

/-- A generated weakening tree cannot be replayed against any other target. -/
theorem weakenRawProof_no_invention (cutoff : Nat) (term : RawTerm)
    {target : Pattern}
    (accepted : checkRaw definition
      (weakensAt (encodeNat cutoff) (encodeRaw term) target)
      (weakenRawProof cutoff term) = true) :
    target = encodeRaw (weakenRaw cutoff term) := by
  have canonical := weakenRawProof_accepts cutoff term
  have sameGoal := checkRaw_goal_unique accepted canonical
  simpa [weakensAt] using sameGoal

/-- A generated substitution tree cannot be replayed against any other
target. -/
theorem substituteRawProof_no_invention
    (index : Nat) (replacement term : RawTerm) {target : Pattern}
    (accepted : checkRaw definition
      (substitutesAt (encodeNat index) (encodeRaw replacement)
        (encodeRaw term) target)
      (substituteRawProof index replacement term) = true) :
    target = encodeRaw (substituteRaw index replacement term) := by
  have canonical := substituteRawProof_accepts index replacement term
  have sameGoal := checkRaw_goal_unique accepted canonical
  simpa [substitutesAt] using sameGoal

/-- A generated root-beta tree cannot be replayed against any other result. -/
theorem betaRawProof_no_invention (body argument : RawTerm) {target : Pattern}
    (accepted : checkRaw definition
      (rootBeta (tmApp (tmLam (encodeRaw body)) (encodeRaw argument)) target)
      (betaRawProof body argument) = true) :
    target = encodeRaw (substituteRaw 0 argument body) := by
  have canonical := betaRawProof_accepts body argument
  have sameGoal := checkRaw_goal_unique accepted canonical
  simpa [rootBeta] using sameGoal

/-! ## Initial executable boundaries -/

theorem two_lt_five_accepts :
    checkRaw definition (indexLt (encodeNat 2) (encodeNat 5))
      (ltRawProof 2 5) = true := by
  exact ltRawProof_accepts (by decide)

/-- The false comparison branch remains rejected. -/
theorem two_lt_two_rejects :
    checkRaw definition (indexLt (encodeNat 2) (encodeNat 2))
      (ltRawProof 2 2) = false := by
  simp (config := { maxSteps := 1000000, decide := true })
    [definition, substitutionExtension,
     ValidatedCalculusLanguageExtension.target,
     substitutionDelta, CalculusLanguageExtension.apply, allRules,
     ltRawProof, rawProof, ltSuccSuccRule, rule, formal, m,
     InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
     instantiateRule?, CalculusLanguageDef.lookupRule?, instantiateSchema?,
     instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
     lookupArgumentAt?, indexLt, encodeNat, succ, ruleId,
     DeclarationAwareDataLanguage.checked,
     DeclarationAwareDataLanguage.definition]

/-! ## Axiom audit -/

#print axioms ltRawProof_accepts
#print axioms weakenRawProof_accepts
#print axioms substituteRawProof_accepts
#print axioms betaRawProof_accepts
#print axioms weakenRawProof_no_invention
#print axioms substituteRawProof_no_invention
#print axioms betaRawProof_no_invention
#print axioms two_lt_five_accepts
#print axioms two_lt_two_rejects

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionCompiler
