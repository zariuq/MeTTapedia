import Mettapedia.Languages.MeTTa.CoreProfile

/-!
# MeTTa Dialect Profiles

`MeTTaCoreProfile` is intentionally exact: one concrete `LanguageDef` plus one
`PremiseProgram`.  That is too narrow to carry the identity of an entire MeTTa
dialect when some dialects export program-specific artifacts from a richer
semantic carrier.

This file adds a small, auditable layer above `MeTTaCoreProfile`:

- fixed dialect identity (`Pure`, `HE`, `PeTTa`, `FullLegacy`)
- runtime-shape classification
- artifact-boundary classification
- principal semantic carrier name used by the dialect

The point is not to erase differences among dialects.  It is to make those
differences explicit while keeping the exact/core profile object unchanged.
-/

namespace Mettapedia.Languages.MeTTa.DialectProfile

open Mettapedia.Languages.MeTTa.CoreProfile

/-- Coarse operational shape of a MeTTa-family dialect. -/
inductive RuntimeShape where
  /-- Closed kernel-style reduction on typed terms. -/
  | kernelClosed
  /-- Explicit interpreter/state-machine state. -/
  | interpreterState
  /-- Relational atomspace semantics over a program/space object. -/
  | relationalAtomspace
  /-- Spec-facing legacy state machine. -/
  | legacyStateMachine
  deriving DecidableEq, Repr

/-- Where executable/runtime-facing artifacts are honestly derived from. -/
inductive ArtifactBoundary where
  /-- One fixed dialect-level `LanguageDef` / premise interface. -/
  | dialectStatic
  /-- Artifacts are exported from a concrete program/space within the dialect. -/
  | programParametric
  deriving DecidableEq, Repr

/-- Fixed dialect-level profile for a MeTTa family member.

`referenceCoreProfile?` is populated when the dialect has a canonical concrete
`MeTTaCoreProfile` already present in the current library.  It is left empty
when the dialect's formal core is program-parametric at the artifact boundary,
as with the current PeTTa formalization.
-/
structure MeTTaDialectProfile where
  name : ProfileName
  referenceCoreProfile? : Option MeTTaCoreProfile := none
  runtimeShape : RuntimeShape
  artifactBoundary : ArtifactBoundary
  /-- Principal semantic carrier used by the dialect-facing formalization. -/
  principalCarrier : String
  /-- Optional named source of lowered `LanguageDef` artifacts for the dialect. -/
  artifactLanguageSource? : Option String := none

/-- Dialect profile for the trusted intensional kernel. -/
def pureDialectProfile : MeTTaDialectProfile where
  name := "Pure"
  referenceCoreProfile? := some pureProfile
  runtimeShape := .kernelClosed
  artifactBoundary := .dialectStatic
  principalCarrier := "PureTm 0"
  artifactLanguageSource? := none

/-- Dialect profile for Hyperon Experimental MeTTa. -/
def heDialectProfile : MeTTaDialectProfile where
  name := "HE"
  referenceCoreProfile? := some heProfile
  runtimeShape := .interpreterState
  artifactBoundary := .dialectStatic
  principalCarrier := "State"
  artifactLanguageSource? := some "mettaHE"

/-- Dialect profile for PeTTa.

PeTTa is a fixed dialect/implementation in the MeTTa family, but its exported
transition/rewrite artifacts are derived from a concrete `PeTTaSpace`, not from
one fixed global `LanguageDef`.
-/
def pettaDialectProfile : MeTTaDialectProfile where
  name := "PeTTa"
  referenceCoreProfile? := none
  runtimeShape := .relationalAtomspace
  artifactBoundary := .programParametric
  principalCarrier := "PeTTaSpace"
  artifactLanguageSource? := some "pettaSpaceToLangDef"

/-- Dialect profile for the legacy full/core state-machine slice. -/
def fullLegacyDialectProfile : MeTTaDialectProfile where
  name := "FullLegacy"
  referenceCoreProfile? := some fullLegacyProfile
  runtimeShape := .legacyStateMachine
  artifactBoundary := .dialectStatic
  principalCarrier := "State"
  artifactLanguageSource? := some "mettaFullLegacy"

/-- Fixed dialect inventory for the current library. -/
def dialectProfiles : List MeTTaDialectProfile :=
  [pureDialectProfile, heDialectProfile, pettaDialectProfile, fullLegacyDialectProfile]

/-- Lookup by fixed dialect name. -/
def findDialectProfile (name : ProfileName) : Option MeTTaDialectProfile :=
  dialectProfiles.find? (fun p => p.name == name)

@[simp] theorem pureDialectProfile_name :
    pureDialectProfile.name = "Pure" := rfl

@[simp] theorem pureDialectProfile_reference :
    pureDialectProfile.referenceCoreProfile? = some pureProfile := rfl

@[simp] theorem heDialectProfile_reference :
    heDialectProfile.referenceCoreProfile? = some heProfile := rfl

@[simp] theorem pettaDialectProfile_programParametric :
    pettaDialectProfile.artifactBoundary = .programParametric := rfl

@[simp] theorem pettaDialectProfile_languageSource :
    pettaDialectProfile.artifactLanguageSource? = some "pettaSpaceToLangDef" := rfl

@[simp] theorem fullLegacyDialectProfile_reference :
    fullLegacyDialectProfile.referenceCoreProfile? = some fullLegacyProfile := rfl

end Mettapedia.Languages.MeTTa.DialectProfile
