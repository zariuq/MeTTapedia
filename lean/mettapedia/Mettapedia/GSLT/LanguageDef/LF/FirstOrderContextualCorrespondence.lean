import Mettapedia.GSLT.LanguageDef.LF.ContextualBetaEtaClosure
import Mettapedia.GSLT.LanguageDef.LF.FirstOrderContextualConversion

/-!
# Runtime LF correspondence for the first-order contextual source

The contextual conversion language uses ordinary first-order data rather
than locally nameless `Pattern.lambda` binders.  This module supplies a total,
injective encoding of runtime LF terms and one-hole contexts into that carrier.
Names are represented by finite lists of Unicode scalar codepoints, each
codepoint written in the source's Peano representation.

The central executable result in this tranche is context adequacy:
for every runtime one-hole context and every runtime term, a recursively
generated raw proof of the corresponding `Plugs` judgment is accepted by the
source-neutral inference checker.  This binds the semantic context operation
to the actual validated calculus definition without defining either side in terms of
the other.
-/

namespace Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualCorrespondence

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta
open Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CheckedSource
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Total first-order carrier encoding -/

def encodeNat : Nat → Pattern
  | 0 => zero
  | n + 1 => succ (encodeNat n)

def decodeNat? : Pattern → Option Nat
  | .apply "Zero" [] => some 0
  | .apply "Succ" [predecessor] => do
      pure ((← decodeNat? predecessor) + 1)
  | _ => none

theorem decodeNat?_encodeNat (value : Nat) :
    decodeNat? (encodeNat value) = some value := by
  induction value with
  | zero => rfl
  | succ value ih => simp [encodeNat, decodeNat?, succ, ih]

theorem encodeNat_injective : Function.Injective encodeNat := by
  intro first second hequal
  apply Option.some.inj
  calc
    some first = decodeNat? (encodeNat first) :=
      (decodeNat?_encodeNat first).symm
    _ = decodeNat? (encodeNat second) := congrArg decodeNat? hequal
    _ = some second := decodeNat?_encodeNat second

def encodeNameChars : List Char → Pattern
  | [] => nameNil
  | character :: rest =>
      nameCons (encodeNat character.toNat) (encodeNameChars rest)

def decodeNameChars? : Pattern → Option (List Char)
  | .apply "NameNil" [] => some []
  | .apply "NameCons" [codepoint, rest] => do
      pure (Char.ofNat (← decodeNat? codepoint) :: (← decodeNameChars? rest))
  | _ => none

private theorem char_ofNat_toNat (character : Char) :
    Char.ofNat character.toNat = character := by
  cases character with
  | mk value valid =>
      simp [Char.ofNat, Char.toNat, Char.ofNatAux, valid]

theorem decodeNameChars?_encodeNameChars (characters : List Char) :
    decodeNameChars? (encodeNameChars characters) = some characters := by
  induction characters with
  | nil => rfl
  | cons character rest ih =>
      simp [encodeNameChars, decodeNameChars?, nameCons,
        decodeNat?_encodeNat, ih]

def encodeName (name : String) : Pattern := encodeNameChars name.toList

def decodeName? (encoded : Pattern) : Option String := do
  pure (String.ofList (← decodeNameChars? encoded))

theorem decodeName?_encodeName (name : String) :
    decodeName? (encodeName name) = some name := by
  have hmk : String.ofList name.toList = name := by
    apply String.toList_injective
    simp
  simp [decodeName?, encodeName, decodeNameChars?_encodeNameChars, hmk]

theorem encodeName_injective : Function.Injective encodeName := by
  intro first second hequal
  apply Option.some.inj
  calc
    some first = decodeName? (encodeName first) :=
      (decodeName?_encodeName first).symm
    _ = decodeName? (encodeName second) := congrArg decodeName? hequal
    _ = some second := decodeName?_encodeName second

def encodeTerm : Term → Pattern
  | .srt .type => srt typeSort
  | .srt .kind => srt kindSort
  | .con name => con (encodeName name)
  | .var index => var (encodeNat index)
  | .pi domain body => pi (encodeTerm domain) (encodeTerm body)
  | .lam domain body => lam (encodeTerm domain) (encodeTerm body)
  | .app function argument => app (encodeTerm function) (encodeTerm argument)

def decodeTerm? : Pattern → Option Term
  | .apply "Srt" [.apply "TypeSort" []] => some (.srt .type)
  | .apply "Srt" [.apply "KindSort" []] => some (.srt .kind)
  | .apply "Con" [name] => do
      pure (.con (← decodeName? name))
  | .apply "Var" [index] => do
      pure (.var (← decodeNat? index))
  | .apply "Pi" [domain, body] => do
      pure (.pi (← decodeTerm? domain) (← decodeTerm? body))
  | .apply "Lam" [domain, body] => do
      pure (.lam (← decodeTerm? domain) (← decodeTerm? body))
  | .apply "App" [function, argument] => do
      pure (.app (← decodeTerm? function) (← decodeTerm? argument))
  | _ => none

theorem decodeTerm?_encodeTerm (term : Term) :
    decodeTerm? (encodeTerm term) = some term := by
  induction term with
  | srt sort =>
      cases sort <;>
        simp [encodeTerm, decodeTerm?, srt, typeSort, kindSort]
  | con name =>
      simp [encodeTerm, decodeTerm?, con, decodeName?_encodeName]
  | var index =>
      simp [encodeTerm, decodeTerm?, var, decodeNat?_encodeNat]
  | pi domain body domainIH bodyIH =>
      simp [encodeTerm, decodeTerm?, pi, domainIH, bodyIH]
  | lam domain body domainIH bodyIH =>
      simp [encodeTerm, decodeTerm?, lam, domainIH, bodyIH]
  | app function argument functionIH argumentIH =>
      simp [encodeTerm, decodeTerm?, app, functionIH, argumentIH]

theorem encodeTerm_injective : Function.Injective encodeTerm := by
  intro first second hequal
  apply Option.some.inj
  calc
    some first = decodeTerm? (encodeTerm first) :=
      (decodeTerm?_encodeTerm first).symm
    _ = decodeTerm? (encodeTerm second) := congrArg decodeTerm? hequal
    _ = some second := decodeTerm?_encodeTerm second

def encodeContext : LFContextualBetaEta.Context → Pattern
  | .hole => hole
  | .piDomain rest body =>
      piDomainContext (encodeContext rest) (encodeTerm body)
  | .piBody domain rest =>
      piBodyContext (encodeTerm domain) (encodeContext rest)
  | .lamDomain rest body =>
      lamDomainContext (encodeContext rest) (encodeTerm body)
  | .lamBody domain rest =>
      lamBodyContext (encodeTerm domain) (encodeContext rest)
  | .appFunction rest argument =>
      appFunctionContext (encodeContext rest) (encodeTerm argument)
  | .appArgument function rest =>
      appArgumentContext (encodeTerm function) (encodeContext rest)

def decodeContext? : Pattern → Option LFContextualBetaEta.Context
  | .apply "Hole" [] => some .hole
  | .apply "PiDomainContext" [rest, body] => do
      pure (.piDomain (← decodeContext? rest) (← decodeTerm? body))
  | .apply "PiBodyContext" [domain, rest] => do
      pure (.piBody (← decodeTerm? domain) (← decodeContext? rest))
  | .apply "LamDomainContext" [rest, body] => do
      pure (.lamDomain (← decodeContext? rest) (← decodeTerm? body))
  | .apply "LamBodyContext" [domain, rest] => do
      pure (.lamBody (← decodeTerm? domain) (← decodeContext? rest))
  | .apply "AppFunctionContext" [rest, argument] => do
      pure (.appFunction (← decodeContext? rest) (← decodeTerm? argument))
  | .apply "AppArgumentContext" [function, rest] => do
      pure (.appArgument (← decodeTerm? function) (← decodeContext? rest))
  | _ => none

theorem decodeContext?_encodeContext
    (context : LFContextualBetaEta.Context) :
    decodeContext? (encodeContext context) = some context := by
  induction context with
  | hole => rfl
  | piDomain rest body restIH =>
      simp [encodeContext, decodeContext?, piDomainContext, restIH,
        decodeTerm?_encodeTerm]
  | piBody domain rest restIH =>
      simp [encodeContext, decodeContext?, piBodyContext, restIH,
        decodeTerm?_encodeTerm]
  | lamDomain rest body restIH =>
      simp [encodeContext, decodeContext?, lamDomainContext, restIH,
        decodeTerm?_encodeTerm]
  | lamBody domain rest restIH =>
      simp [encodeContext, decodeContext?, lamBodyContext, restIH,
        decodeTerm?_encodeTerm]
  | appFunction rest argument restIH =>
      simp [encodeContext, decodeContext?, appFunctionContext, restIH,
        decodeTerm?_encodeTerm]
  | appArgument function rest restIH =>
      simp [encodeContext, decodeContext?, appArgumentContext, restIH,
        decodeTerm?_encodeTerm]

theorem encodeContext_injective : Function.Injective encodeContext := by
  intro first second hequal
  apply Option.some.inj
  calc
    some first = decodeContext? (encodeContext first) :=
      (decodeContext?_encodeContext first).symm
    _ = decodeContext? (encodeContext second) :=
      congrArg decodeContext? hequal
    _ = some second := decodeContext?_encodeContext second

/-- Encoding commutes exactly with filling the distinguished hole. -/
theorem encodeContext_plug
    (context : LFContextualBetaEta.Context) (inner : Term) :
    encodeTerm (context.plug inner) =
      match context with
      | .hole => encodeTerm inner
      | .piDomain rest body =>
          pi (encodeTerm (rest.plug inner)) (encodeTerm body)
      | .piBody domain rest =>
          pi (encodeTerm domain) (encodeTerm (rest.plug inner))
      | .lamDomain rest body =>
          lam (encodeTerm (rest.plug inner)) (encodeTerm body)
      | .lamBody domain rest =>
          lam (encodeTerm domain) (encodeTerm (rest.plug inner))
      | .appFunction rest argument =>
          app (encodeTerm (rest.plug inner)) (encodeTerm argument)
      | .appArgument function rest =>
          app (encodeTerm function) (encodeTerm (rest.plug inner)) := by
  cases context <;> rfl

/-! ## Proof-producing context adequacy -/

def plugRawProof
    (context : LFContextualBetaEta.Context) (inner : Term) : RawProof :=
  match context with
  | .hole =>
      rawProof "lf-fo-plug-hole" [encodeTerm inner] []
  | .piDomain rest body =>
      rawProof "lf-fo-plug-pi-domain"
        [encodeContext rest, encodeTerm body, encodeTerm inner,
          encodeTerm (rest.plug inner)]
        [plugRawProof rest inner]
  | .piBody domain rest =>
      rawProof "lf-fo-plug-pi-body"
        [encodeTerm domain, encodeContext rest, encodeTerm inner,
          encodeTerm (rest.plug inner)]
        [plugRawProof rest inner]
  | .lamDomain rest body =>
      rawProof "lf-fo-plug-lam-domain"
        [encodeContext rest, encodeTerm body, encodeTerm inner,
          encodeTerm (rest.plug inner)]
        [plugRawProof rest inner]
  | .lamBody domain rest =>
      rawProof "lf-fo-plug-lam-body"
        [encodeTerm domain, encodeContext rest, encodeTerm inner,
          encodeTerm (rest.plug inner)]
        [plugRawProof rest inner]
  | .appFunction rest argument =>
      rawProof "lf-fo-plug-app-function"
        [encodeContext rest, encodeTerm argument, encodeTerm inner,
          encodeTerm (rest.plug inner)]
        [plugRawProof rest inner]
  | .appArgument function rest =>
      rawProof "lf-fo-plug-app-argument"
        [encodeTerm function, encodeContext rest, encodeTerm inner,
          encodeTerm (rest.plug inner)]
        [plugRawProof rest inner]
termination_by context

theorem encodeNat_ground (value : Nat) :
    (encodeNat value).isGroundAt 0 = true := by
  induction value with
  | zero =>
      simp [encodeNat, zero, Pattern.isGroundAt, Pattern.isGroundListAt]
  | succ value ih =>
      simp [encodeNat, succ, Pattern.isGroundAt, Pattern.isGroundListAt, ih]

theorem encodeNat_canonical (value : Nat) :
    (encodeNat value).hasCanonicalBinderMetadata = true := by
  induction value with
  | zero =>
      simp [encodeNat, zero, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | succ value ih =>
      simp [encodeNat, succ, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, ih]

theorem encodeNat_argumentValid (value : Nat) :
    argumentValidAt 0 (encodeNat value) = true := by
  simp [argumentValidAt, encodeNat_ground, encodeNat_canonical]

private theorem encodeNameChars_ground (characters : List Char) :
    (encodeNameChars characters).isGroundAt 0 = true := by
  induction characters with
  | nil =>
      simp [encodeNameChars, nameNil, Pattern.isGroundAt,
        Pattern.isGroundListAt]
  | cons character rest ih =>
      simp [encodeNameChars, nameCons, Pattern.isGroundAt,
        Pattern.isGroundListAt, encodeNat_ground, ih]

private theorem encodeNameChars_canonical (characters : List Char) :
    (encodeNameChars characters).hasCanonicalBinderMetadata = true := by
  induction characters with
  | nil =>
      simp [encodeNameChars, nameNil, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | cons character rest ih =>
      simp [encodeNameChars, nameCons, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, encodeNat_canonical, ih]

theorem encodeName_ground (name : String) :
    (encodeName name).isGroundAt 0 = true := by
  simp [encodeName, encodeNameChars_ground]

theorem encodeName_canonical (name : String) :
    (encodeName name).hasCanonicalBinderMetadata = true := by
  simp [encodeName, encodeNameChars_canonical]

theorem encodeName_argumentValid (name : String) :
    argumentValidAt 0 (encodeName name) = true := by
  simp [argumentValidAt, encodeName_ground, encodeName_canonical]

theorem encodeTerm_ground (term : Term) :
    (encodeTerm term).isGroundAt 0 = true := by
  induction term with
  | srt sort =>
      cases sort <;>
        simp [encodeTerm, srt, typeSort, kindSort, Pattern.isGroundAt,
          Pattern.isGroundListAt]
  | con name =>
      simp [encodeTerm, encodeName, con, Pattern.isGroundAt,
        Pattern.isGroundListAt, encodeNameChars_ground]
  | var index =>
      simp [encodeTerm, var, Pattern.isGroundAt, Pattern.isGroundListAt,
        encodeNat_ground]
  | pi domain body domainIH bodyIH =>
      simp [encodeTerm, pi, Pattern.isGroundAt, Pattern.isGroundListAt,
        domainIH, bodyIH]
  | lam domain body domainIH bodyIH =>
      simp [encodeTerm, lam, Pattern.isGroundAt, Pattern.isGroundListAt,
        domainIH, bodyIH]
  | app function argument functionIH argumentIH =>
      simp [encodeTerm, app, Pattern.isGroundAt, Pattern.isGroundListAt,
        functionIH, argumentIH]

theorem encodeTerm_canonical (term : Term) :
    (encodeTerm term).hasCanonicalBinderMetadata = true := by
  induction term with
  | srt sort =>
      cases sort <;>
        simp [encodeTerm, srt, typeSort, kindSort,
          Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList]
  | con name =>
      simp [encodeTerm, encodeName, con, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, encodeNameChars_canonical]
  | var index =>
      simp [encodeTerm, var, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, encodeNat_canonical]
  | pi domain body domainIH bodyIH =>
      simp [encodeTerm, pi, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, domainIH, bodyIH]
  | lam domain body domainIH bodyIH =>
      simp [encodeTerm, lam, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, domainIH, bodyIH]
  | app function argument functionIH argumentIH =>
      simp [encodeTerm, app, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, functionIH, argumentIH]

theorem encodeContext_ground
    (context : LFContextualBetaEta.Context) :
    (encodeContext context).isGroundAt 0 = true := by
  induction context with
  | hole =>
      simp [encodeContext, hole, Pattern.isGroundAt, Pattern.isGroundListAt]
  | piDomain rest body restIH =>
      simp [encodeContext, piDomainContext, Pattern.isGroundAt,
        Pattern.isGroundListAt, restIH, encodeTerm_ground]
  | piBody domain rest restIH =>
      simp [encodeContext, piBodyContext, Pattern.isGroundAt,
        Pattern.isGroundListAt, restIH, encodeTerm_ground]
  | lamDomain rest body restIH =>
      simp [encodeContext, lamDomainContext, Pattern.isGroundAt,
        Pattern.isGroundListAt, restIH, encodeTerm_ground]
  | lamBody domain rest restIH =>
      simp [encodeContext, lamBodyContext, Pattern.isGroundAt,
        Pattern.isGroundListAt, restIH, encodeTerm_ground]
  | appFunction rest argument restIH =>
      simp [encodeContext, appFunctionContext, Pattern.isGroundAt,
        Pattern.isGroundListAt, restIH, encodeTerm_ground]
  | appArgument function rest restIH =>
      simp [encodeContext, appArgumentContext, Pattern.isGroundAt,
        Pattern.isGroundListAt, restIH, encodeTerm_ground]

theorem encodeContext_canonical
    (context : LFContextualBetaEta.Context) :
    (encodeContext context).hasCanonicalBinderMetadata = true := by
  induction context with
  | hole =>
      simp [encodeContext, hole, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | piDomain rest body restIH =>
      simp [encodeContext, piDomainContext,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, restIH, encodeTerm_canonical]
  | piBody domain rest restIH =>
      simp [encodeContext, piBodyContext,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, restIH, encodeTerm_canonical]
  | lamDomain rest body restIH =>
      simp [encodeContext, lamDomainContext,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, restIH, encodeTerm_canonical]
  | lamBody domain rest restIH =>
      simp [encodeContext, lamBodyContext,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, restIH, encodeTerm_canonical]
  | appFunction rest argument restIH =>
      simp [encodeContext, appFunctionContext,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, restIH, encodeTerm_canonical]
  | appArgument function rest restIH =>
      simp [encodeContext, appArgumentContext,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, restIH, encodeTerm_canonical]

theorem encodeTerm_argumentValid (term : Term) :
    argumentValidAt 0 (encodeTerm term) = true := by
  simp [argumentValidAt, encodeTerm_ground, encodeTerm_canonical]

theorem encodeContext_argumentValid
    (context : LFContextualBetaEta.Context) :
    argumentValidAt 0 (encodeContext context) = true := by
  simp [argumentValidAt, encodeContext_ground, encodeContext_canonical]

/-- The recursive runtime context proof is accepted by the actual generic
checker for every context and every inserted term. -/
theorem plugRawProof_accepts
    (context : LFContextualBetaEta.Context) (inner : Term) :
    checked.checkRaw
      (plugs (encodeContext context) (encodeTerm inner)
        (encodeTerm (context.plug inner)))
      (plugRawProof context inner) = true := by
  induction context with
  | hole =>
      simp (config := { maxSteps := 1000000, decide := true })
        [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
         InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
         source, plugRawProof, rawProof, allRules,
         plugHoleRule, rule,
         Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.formal,
         Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.m,
         instantiateRule?,
         CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
         instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
         argumentsValidAt, encodeTerm_argumentValid,
         plugs, encodeContext,
         LFContextualBetaEta.Context.plug, hole, ruleId]
  | piDomain rest body restIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
         InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
         source, plugRawProof, rawProof, allRules,
         plugPiDomainRule, rule,
         Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.formal,
         Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.m,
         instantiateRule?,
         CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
         instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
         argumentsValidAt, encodeTerm_argumentValid,
         encodeContext_argumentValid,
         plugs, encodeContext, encodeTerm,
         LFContextualBetaEta.Context.plug, piDomainContext, pi, ruleId]
      simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
        allRules, plugPiDomainRule, rule,
        Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.formal,
        Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.m,
        plugs, piDomainContext, pi, ruleId]
        using restIH
  | piBody domain rest restIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
         InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
         source, plugRawProof, rawProof, allRules,
         plugPiBodyRule, rule,
         Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.formal,
         Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.m,
         instantiateRule?,
         CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
         instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
         argumentsValidAt, encodeTerm_argumentValid,
         encodeContext_argumentValid,
         plugs, encodeContext, encodeTerm,
         LFContextualBetaEta.Context.plug, piBodyContext, pi, ruleId]
      simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
        allRules, plugPiBodyRule, rule,
        Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.formal,
        Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.m,
        plugs, piBodyContext, pi, ruleId]
        using restIH
  | lamDomain rest body restIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
         InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
         source, plugRawProof, rawProof, allRules,
         plugLamDomainRule, rule,
         Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.formal,
         Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.m,
         instantiateRule?,
         CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
         instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
         argumentsValidAt, encodeTerm_argumentValid,
         encodeContext_argumentValid,
         plugs, encodeContext, encodeTerm,
         LFContextualBetaEta.Context.plug, lamDomainContext, lam, ruleId]
      simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
        allRules, plugLamDomainRule, rule,
        Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.formal,
        Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.m,
        plugs, lamDomainContext, lam, ruleId]
        using restIH
  | lamBody domain rest restIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
         InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
         source, plugRawProof, rawProof, allRules,
         plugLamBodyRule, rule,
         Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.formal,
         Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.m,
         instantiateRule?,
         CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
         instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
         argumentsValidAt, encodeTerm_argumentValid,
         encodeContext_argumentValid,
         plugs, encodeContext, encodeTerm,
         LFContextualBetaEta.Context.plug, lamBodyContext, lam, ruleId]
      simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
        allRules, plugLamBodyRule, rule,
        Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.formal,
        Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.m,
        plugs, lamBodyContext, lam, ruleId]
        using restIH
  | appFunction rest argument restIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
         InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
         source, plugRawProof, rawProof, allRules,
         plugAppFunctionRule, rule,
         Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.formal,
         Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.m,
         instantiateRule?,
         CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
         instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
         argumentsValidAt, encodeTerm_argumentValid,
         encodeContext_argumentValid,
         plugs, encodeContext, encodeTerm,
         LFContextualBetaEta.Context.plug, appFunctionContext, app, ruleId]
      simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
        allRules, plugAppFunctionRule, rule,
        Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.formal,
        Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.m,
        plugs, appFunctionContext, app, ruleId]
        using restIH
  | appArgument function rest restIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
         InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
         source, plugRawProof, rawProof, allRules,
         plugAppArgumentRule, rule,
         Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.formal,
         Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.m,
         instantiateRule?,
         CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
         instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
         argumentsValidAt, encodeTerm_argumentValid,
         encodeContext_argumentValid,
         plugs, encodeContext, encodeTerm,
         LFContextualBetaEta.Context.plug, appArgumentContext, app, ruleId]
      simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
        allRules, plugAppArgumentRule, rule,
        Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.formal,
        Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.m,
        plugs, appArgumentContext, app, ruleId]
        using restIH

/-! ## Positive and negative boundaries -/

private def runtimeType : Term := .srt .type
private def runtimeIdentity : Term := .lam runtimeType (.var 0)
private def nestedContext : LFContextualBetaEta.Context :=
  .piBody runtimeType (.lamBody runtimeType .hole)

theorem nested_context_proof_accepts :
    checked.checkRaw
      (plugs (encodeContext nestedContext) (encodeTerm (.var 0))
        (encodeTerm (nestedContext.plug (.var 0))))
      (plugRawProof nestedContext (.var 0)) = true :=
  plugRawProof_accepts nestedContext (.var 0)

/-- A context proof cannot be reused for a different inserted endpoint. -/
theorem changed_inner_rejects :
    checked.checkRaw
      (plugs (encodeContext nestedContext) (encodeTerm runtimeType)
        (encodeTerm (nestedContext.plug runtimeType)))
      (plugRawProof nestedContext runtimeIdentity) = false := by
  simp (config := { maxSteps := 1000000, decide := true })
    [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
     CheckedGSLT.definition, checked, source,
     nestedContext, runtimeType, runtimeIdentity, plugRawProof, rawProof,
     allRules, plugPiBodyRule, plugLamBodyRule, plugHoleRule, rule,
     Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.formal,
     Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion.m,
     instantiateRule?,
     CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
     instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
     InferenceChecker.checkRawChildren, plugs,
     encodeContext, encodeTerm, LFContextualBetaEta.Context.plug,
     piBodyContext, lamBodyContext, pi, lam, var, encodeNat, zero, srt,
     typeSort, ruleId]

#print axioms decodeNat?_encodeNat
#print axioms encodeNat_argumentValid
#print axioms decodeName?_encodeName
#print axioms decodeTerm?_encodeTerm
#print axioms encodeTerm_injective
#print axioms decodeContext?_encodeContext
#print axioms encodeContext_injective
#print axioms encodeContext_plug
#print axioms plugRawProof_accepts
#print axioms nested_context_proof_accepts
#print axioms changed_inner_rejects

end Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualCorrespondence
