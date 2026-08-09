import Mettapedia.GSLT.LanguageDef.Extension
import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Runtime profiles as a coGSLT-authored extension

Runtime strategy, backend selection, and diagnostic controls do not identify
the mathematical language being executed.  They therefore live in a separate
dependent layer rather than in `LanguageDef`.  A setting that changes the
language's denotation is intentionally absent: such a parameter must elaborate
to a different five-field language definition.
-/

namespace Mettapedia.GSLT.LanguageDef.RuntimeProfileExtension

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The three non-semantic authorities a runtime profile may exercise. -/
inductive RuntimeSettingClass where
  | operational
  | backend
  | diagnostic
deriving Repr, DecidableEq

/-- Backend-neutral values admitted by the profile language. -/
inductive RuntimeSettingValue where
  | bool (value : Bool)
  | int (value : Int)
  | decimal (value : Float)
  | keyword (value : String)
  | text (value : String)
deriving Repr

/-- One named runtime setting. -/
structure RuntimeSetting where
  key : String
  value : RuntimeSettingValue
  scope : RuntimeSettingClass
deriving Repr

/-- Structural authored syntax for runtime profiles. -/
inductive RuntimeSettingSyntax where
  | setting (key : String) (value : RuntimeSettingValue)
      (scope : RuntimeSettingClass)
deriving Repr

def encodeSetting (setting : RuntimeSetting) : RuntimeSettingSyntax :=
  .setting setting.key setting.value setting.scope

def decodeSetting : RuntimeSettingSyntax → RuntimeSetting
  | .setting key value scope => { key, value, scope }

@[simp] theorem decodeSetting_encodeSetting (setting : RuntimeSetting) :
    decodeSetting (encodeSetting setting) = setting := by
  cases setting
  rfl

@[simp] theorem encodeSetting_decodeSetting (source : RuntimeSettingSyntax) :
    encodeSetting (decodeSetting source) = source := by
  cases source
  rfl

def settingCodec :
    ExactDeclarationCodec RuntimeSettingSyntax RuntimeSetting where
  encode := encodeSetting
  decode := decodeSetting
  decode_encode := decodeSetting_encodeSetting
  encode_decode := encodeSetting_decodeSetting

def ProfileAdmissible (profile : List RuntimeSetting) : Bool :=
  decide (profile.map (fun setting => setting.key)).Nodup &&
    profile.all fun setting => !setting.key.isEmpty

abbrev AdmittedProfile (_language : LanguageDef) :=
  { profile : List RuntimeSetting // ProfileAdmissible profile = true }

/-- The law-bearing authored GSLT for runtime-setting sequences. -/
def runtimeProfileAuthoringGSLT : DeclarationAuthoringGSLT RuntimeSetting :=
  settingCodec.compositionalElaboration

def runtimeProfileDocumentGSLT : GSLT :=
  runtimeProfileAuthoringGSLT.authoring.theory

private def elaborateProfile? (language : LanguageDef)
    (source : DeclarationDocument RuntimeSettingSyntax) :
    Option (AdmittedProfile language) :=
  let profile := settingCodec.elaborate source
  if admitted : ProfileAdmissible profile = true then
    some ⟨profile, admitted⟩
  else
    none

private def quoteProfile (language : LanguageDef)
    (profile : AdmittedProfile language) :
    DeclarationDocument RuntimeSettingSyntax :=
  settingCodec.quote profile.1

def layer : CoGSLTLayer LanguageDef where
  Fiber := AdmittedProfile
  sourceGSLT := fun _ => runtimeProfileDocumentGSLT
  elaborate := elaborateProfile?
  quote := quoteProfile
  elaborate_quote := by
    intro language profile
    simp [quoteProfile, elaborateProfile?,
      ExactDeclarationCodec.elaborate_quote, profile.2]
  elaborate_equation := by
    intro language source target equal
    unfold elaborateProfile?
    rw [settingCodec.elaborate_equation equal]
  elaborate_rewrite := by
    intro language source target impossible
    exact False.elim impossible

@[simp] theorem erase_attach (language : LanguageDef)
    (profile : AdmittedProfile language) :
    layer.erase (layer.attach language profile) = language :=
  rfl

private def exampleLanguage : LanguageDef :=
  LanguageDef.empty "runtime-profile-example"

private def deterministicSetting : RuntimeSetting :=
  { key := "scheduler"
    value := .keyword "deterministic"
    scope := .operational }

private def deterministicProfile : AdmittedProfile exampleLanguage :=
  ⟨[deterministicSetting], by decide⟩

example :
    layer.elaborate exampleLanguage
        (layer.quote exampleLanguage deterministicProfile) =
      some deterministicProfile :=
  layer.elaborate_quote exampleLanguage deterministicProfile

example :
    ProfileAdmissible
      [deterministicSetting, deterministicSetting] = false := by
  decide

example :
    ProfileAdmissible
      [{ key := "", value := .bool true, scope := .diagnostic }] = false := by
  decide

private def emptyProfile : AdmittedProfile exampleLanguage :=
  ⟨[], by decide⟩

def runtimeProfileNonTrivialFiber :
    NonTrivialFiber layer.erase (fun attached => attached.2.1) where
  left := layer.attach exampleLanguage emptyProfile
  right := layer.attach exampleLanguage deterministicProfile
  sameShadow := rfl
  differentValue := by
    change ([] : List RuntimeSetting) ≠ [deterministicSetting]
    simp

theorem runtime_profile_not_determined_by_language :
    ¬ Factors layer.erase (fun attached => attached.2.1) :=
  runtimeProfileNonTrivialFiber.not_factors

end Mettapedia.GSLT.LanguageDef.RuntimeProfileExtension
