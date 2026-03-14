import Mettapedia.OSLF.MeTTaIL.PremiseDatalog
import Mettapedia.Languages.MeTTa.Pure.Core
import Mettapedia.Languages.MeTTa.HE.HELanguageDef
import Mettapedia.Languages.MeTTa.HE.HEPremises
import Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef
import Mettapedia.Languages.MeTTa.OSLFCore.FullPremises

/-!
# MeTTa Core Profile Interface

Canonical profile interface for MeTTa-family languages over the shared
`LanguageDef` + `PremiseProgram` substrate.

This keeps Pure/HE/Full comparable without collapsing them into one semantics.
-/

namespace Mettapedia.Languages.MeTTa.CoreProfile

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PremiseDatalog

abbrev ProfileName := String

/-- Canonical interface for a MeTTa runtime/theory profile. -/
structure MeTTaCoreProfile where
  name : ProfileName
  lang : LanguageDef
  premises : PremiseProgram
  /-- Principal state constructor (if stateful runtime profile). -/
  stateConstructor : Option String := premises.stateConstructor

/-- Empty premise program for kernel-style profiles. -/
def emptyPremiseProgram : PremiseProgram where
  relations := []
  rules := []
  builtins := []
  backendHints := []
  coreGroundEvalRelation := none
  stateConstructor := none

def MeTTaCoreProfile.wellFormed (p : MeTTaCoreProfile) : Bool :=
  p.premises.wellFormed

def MeTTaCoreProfile.stratified (p : MeTTaCoreProfile) : Bool :=
  p.premises.isStratified

/-- Minimal, trusted DTT kernel profile presented as MeTTa language. -/
def pureProfile : MeTTaCoreProfile where
  name := "Pure"
  lang := Mettapedia.Languages.MeTTa.Pure.Core.mettaPure
  premises := emptyPremiseProgram
  stateConstructor := none

/-- Hyperon Experimental profile. -/
def heProfile : MeTTaCoreProfile where
  name := "HE"
  lang := Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE
  premises := Mettapedia.Languages.MeTTa.HE.Premises.mettaHEPremises
  stateConstructor := some "State"

/-- Legacy full/core state-machine profile. -/
def fullLegacyProfile : MeTTaCoreProfile where
  name := "FullLegacy"
  lang := Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef.mettaFullLegacy
  premises := Mettapedia.Languages.MeTTa.OSLFCore.FullPremises.mettaFullPremises
  stateConstructor := some "State"

/-- Compatibility alias retained for downstream imports during migration. -/
abbrev fullProfile : MeTTaCoreProfile := fullLegacyProfile

def coreProfiles : List MeTTaCoreProfile :=
  [pureProfile, heProfile, fullLegacyProfile]

def findProfile (name : ProfileName) : Option MeTTaCoreProfile :=
  coreProfiles.find? (fun p => p.name == name)

theorem pureProfile_no_premise_rules :
    pureProfile.premises.rules = [] := rfl

theorem pureProfile_wellFormed : pureProfile.wellFormed = true := by
  decide

theorem pureProfile_stratified : pureProfile.stratified = true := by
  native_decide

theorem pureProfile_eight_rewrites :
    pureProfile.lang.rewrites.length = 3 := by
  change Mettapedia.Languages.MeTTa.Pure.Core.mettaPure.rewrites.length = 3
  decide

theorem pureProfile_intensional :
    pureProfile.lang.equations = [] := by
  rfl

end Mettapedia.Languages.MeTTa.CoreProfile
