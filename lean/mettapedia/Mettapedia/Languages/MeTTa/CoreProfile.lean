import Mettapedia.OSLF.MeTTaIL.PremiseDatalog
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core
import Mettapedia.Languages.MeTTa.HE.HELanguageDef
import Mettapedia.Languages.MeTTa.HE.HEPremises
import Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef
import Mettapedia.Languages.MeTTa.OSLFCore.FullPremises

/-!
# MeTTa Core Profile Interface

Canonical profile interface for MeTTa-family languages over the shared
`LanguageDef` + `PremiseProgram` substrate.

This compares the two-sort experiment, HE and the legacy Full model without
identifying their semantics or selecting any of them as Prime.
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

/-- Concrete two-sort experiment presented as a MeTTa language profile. -/
def twoSortProfile : MeTTaCoreProfile where
  name := "TwoSortPiSigmaId"
  lang := Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.twoSortDependent
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
  [twoSortProfile, heProfile, fullLegacyProfile]

def findProfile (name : ProfileName) : Option MeTTaCoreProfile :=
  coreProfiles.find? (fun p => p.name == name)

theorem twoSortProfile_no_premise_rules :
    twoSortProfile.premises.rules = [] := rfl

theorem twoSortProfile_wellFormed : twoSortProfile.wellFormed = true := by
  decide

theorem twoSortProfile_stratified : twoSortProfile.stratified = true := by
  cbv

theorem twoSortProfile_three_rewrites :
    twoSortProfile.lang.rewrites.length = 3 := by
  change Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.twoSortDependent.rewrites.length = 3
  decide

theorem twoSortProfile_intensional :
    twoSortProfile.lang.equations = [] := by
  rfl

end Mettapedia.Languages.MeTTa.CoreProfile
