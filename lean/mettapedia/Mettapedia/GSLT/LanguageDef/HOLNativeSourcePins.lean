import Mettapedia.GSLT.LanguageDef.CheckedSource
import Mettapedia.GSLT.LanguageDef.HOLSourceKernel

/-!
# Pinned native HOL kernel sources

This module binds the source-scale HOL `LanguageDef` rule tables to exact
upstream kernel artifacts.  The pins are source identities, not adequacy
proofs: the latter must still relate generated generic derivations to an
independent semantics of the selected primitive rules.
-/

namespace Mettapedia.GSLT.LanguageDef.HOLNativeSourcePins

open Mettapedia.GSLT.LanguageDef.CheckedSource
open Mettapedia.GSLT.LanguageDef.HOLSourceKernel

structure SourceFilePin where
  repository : String
  revision : String
  path : String
  sha256 : String
deriving Repr, DecidableEq

structure PrimitiveRulePin where
  sourceName : String
  generatedRuleId : String
  firstLine : Nat
  lastLine : Nat
deriving Repr, DecidableEq

def holLightFusion : SourceFilePin :=
  { repository := "https://github.com/jrh13/hol-light.git"
    revision := "924faf0c3471a04174ffdeb8576ce7cabcb92d64"
    path := "fusion.ml"
    sha256 := "29544be92d9cc1e6b3b59ba5b210604b9a748366a68b3bcdc2619717d68fd98a" }

def hol4FinalThmSignature : SourceFilePin :=
  { repository := "https://github.com/HOL-Theorem-Prover/HOL.git"
    revision := "f428faeb0b7112675d53f51a9e3a2fcaf27278c3"
    path := "src/prekernel/FinalThm-sig.sml"
    sha256 := "12f5e757c56dd0d13b1a5f8f09abdb96eedc1d80ce9800aec5abebb011d8629c" }

def hol4StandardTheoremKernel : SourceFilePin :=
  { repository := "https://github.com/HOL-Theorem-Prover/HOL.git"
    revision := "f428faeb0b7112675d53f51a9e3a2fcaf27278c3"
    path := "src/thm/std-thm.ML"
    sha256 := "6f559a177e8c59d0c92702b5a8fcecfc4b48f7672c743855c904c3bb126fb25a" }

def holLightIdentity : SourceIdentity :=
  { systemId := "HOL-Light-fusion"
    revision := holLightFusion.revision
    artifactDigest := "sha256:" ++ holLightFusion.sha256 }

def hol4Identity : SourceIdentity :=
  { systemId := "HOL4-standard-theorem-kernel"
    revision := hol4StandardTheoremKernel.revision
    artifactDigest := "sha256:" ++ hol4StandardTheoremKernel.sha256 }

def holLightPrimitiveRules : List PrimitiveRulePin :=
  [ { sourceName := "REFL", generatedRuleId := "HL_REFL",
      firstLine := 498, lastLine := 499 }
  , { sourceName := "TRANS", generatedRuleId := "HL_TRANS",
      firstLine := 501, lastLine := 505 }
  , { sourceName := "MK_COMB", generatedRuleId := "HL_MK_COMB",
      firstLine := 511, lastLine := 519 }
  , { sourceName := "ABS", generatedRuleId := "HL_ABS",
      firstLine := 521, lastLine := 525 }
  , { sourceName := "BETA", generatedRuleId := "HL_BETA",
      firstLine := 531, lastLine := 535 }
  , { sourceName := "ASSUME", generatedRuleId := "HL_ASSUME",
      firstLine := 541, lastLine := 543 }
  , { sourceName := "EQ_MP", generatedRuleId := "HL_EQ_MP",
      firstLine := 545, lastLine := 549 }
  , { sourceName := "DEDUCT_ANTISYM_RULE",
      generatedRuleId := "HL_DEDUCT_ANTISYM",
      firstLine := 551, lastLine := 553 }
  , { sourceName := "INST", generatedRuleId := "HL_INST",
      firstLine := 563, lastLine := 565 }
  , { sourceName := "INST_TYPE", generatedRuleId := "HL_INST_TYPE",
      firstLine := 559, lastLine := 561 }
  , { sourceName := "new_axiom", generatedRuleId := "HL_AXIOM",
      firstLine := 575, lastLine := 579 }
  , { sourceName := "new_basic_definition",
      generatedRuleId := "HL_DEFINITION",
      firstLine := 589, lastLine := 602 }
  , { sourceName := "new_basic_type_definition",
      generatedRuleId := "HL_TYPE_DEFINITION",
      firstLine := 617, lastLine := 639 } ]

def hol4PrimitiveRules : List PrimitiveRulePin :=
  [ { sourceName := "ASSUME", generatedRuleId := "H4_ASSUME",
      firstLine := 314, lastLine := 316 }
  , { sourceName := "REFL", generatedRuleId := "H4_REFL",
      firstLine := 330, lastLine := 330 }
  , { sourceName := "BETA_CONV", generatedRuleId := "H4_BETA_CONV",
      firstLine := 339, lastLine := 342 }
  , { sourceName := "ABS", generatedRuleId := "H4_ABS",
      firstLine := 379, lastLine := 390 }
  , { sourceName := "DISCH", generatedRuleId := "H4_DISCH",
      firstLine := 433, lastLine := 438 }
  , { sourceName := "MP", generatedRuleId := "H4_MP",
      firstLine := 449, lastLine := 454 }
  , { sourceName := "SUBST", generatedRuleId := "H4_SUBST",
      firstLine := 353, lastLine := 371 }
  , { sourceName := "INST_TYPE", generatedRuleId := "H4_INST_TYPE",
      firstLine := 420, lastLine := 422 } ]

def generatedRuleIds (pins : List PrimitiveRulePin) : List String :=
  pins.map (·.generatedRuleId)

theorem holLightRuleTable_is_pinned :
    holLightSourceKernel.rewrites.map (·.name) =
      generatedRuleIds holLightPrimitiveRules := by
  rfl

theorem hol4RuleTable_is_pinned :
    hol4SourceKernel.rewrites.map (·.name) =
      generatedRuleIds hol4PrimitiveRules := by
  rfl

theorem holLightIdentity_valid : holLightIdentity.isValid = true := by
  rfl

theorem hol4Identity_valid : hol4Identity.isValid = true := by
  rfl

#guard holLightPrimitiveRules.all fun pin =>
  pin.sourceName != "" && pin.generatedRuleId != "" &&
    pin.firstLine > 0 && pin.firstLine <= pin.lastLine

#guard hol4PrimitiveRules.all fun pin =>
  pin.sourceName != "" && pin.generatedRuleId != "" &&
    pin.firstLine > 0 && pin.firstLine <= pin.lastLine

#guard (generatedRuleIds holLightPrimitiveRules).eraseDups.length ==
  holLightPrimitiveRules.length

#guard (generatedRuleIds hol4PrimitiveRules).eraseDups.length ==
  hol4PrimitiveRules.length

end Mettapedia.GSLT.LanguageDef.HOLNativeSourcePins
