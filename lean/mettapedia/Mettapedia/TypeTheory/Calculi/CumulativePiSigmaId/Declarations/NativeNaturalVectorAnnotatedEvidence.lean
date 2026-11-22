import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorAnnotated
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.InductivePackage

/-! Generated annotated proof source; each theorem is checked by Lean. -/

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.Programs.Annotated.Evidence

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Annotated

variable (enabled : ComputationProfiles.Selection)

local instance : DecidableRel (ComputationProfiles.rules enabled).headTyping := fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred (ComputationProfiles.rules enabled).isUniverse := fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable ((ComputationProfiles.rules enabled).join u v w) := fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel (ComputationProfiles.rules enabled).cumulative := fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))

private def e0 : Tower.Ctx 0 :=
.nil

private theorem e3 : CTyped (church enabled) (liftCtx e0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e8abf992014c6a64d384) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6bbe1c48b2bd1700632c) :=
.headType (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e5 : CTyped (church enabled) (liftCtx e0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4a27bce6d6d25fd1b645) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e8abf992014c6a64d384) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e3 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e6 : Tower.Ctx 1 :=
.snoc e0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4a27bce6d6d25fd1b645

private theorem e9 : CTyped (church enabled) (liftCtx e6) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_335242b771a931d18c5a) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_83ee15629b1bf92f199d) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e3 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e12 : CTyped (church enabled) (liftCtx e0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b3898b5267cea17e248e) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a60a9e3309f85030c85e) :=
.piForm (e5 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e9 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e15 : CTyped (church enabled) (liftCtx e6) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2f8b8cf81879f5cb13bd) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c879f19b4c38cb8314ab) :=
.headType (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e18 : CTyped (church enabled) (liftCtx e0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9448d2a97ae51aeb04c8) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_94325ab39bb665304311) :=
.piForm (e5 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e15 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e19 : Tower.Ctx 1 :=
.snoc e0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9448d2a97ae51aeb04c8

private theorem e22 : CTyped (church enabled) (liftCtx e19) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6779083e6f4ae6a4b575) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbb718a2ed46d9d43e83) :=
by
  change CTyped (church enabled) (liftCtx e19) (.var 0) (liftTm (Ctx.lookup e19 0))
  rw [← liftCtx_lookup]
  exact .var 0

private theorem e24 : CTyped (church enabled) (liftCtx e19) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a29f58d1c6dc0ad93027) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_335242b771a931d18c5a) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e5 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e27 : CTyped (church enabled) (liftCtx e19) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4797eda3ab17e14f5071) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2f8b8cf81879f5cb13bd) :=
by
  change CTyped (church enabled) (liftCtx e19) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6779083e6f4ae6a4b575) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a29f58d1c6dc0ad93027)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a29f58d1c6dc0ad93027 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8f0c544fe181823a37fb))
  rw [liftTm_inst0]
  exact .appElim (e22 enabled) (e24 enabled)

private def e28 : Tower.Ctx 2 :=
.snoc e19 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4797eda3ab17e14f5071

private theorem e31 : CTyped (church enabled) (liftCtx e28) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e7afc61b162c474cee28) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_83e953797e881bc716be) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e3 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e32 : Tower.Ctx 3 :=
.snoc e28 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e7afc61b162c474cee28

private theorem e35 : CTyped (church enabled) (liftCtx e32) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_00835ccb59a9bb61fd8d) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_afca4aeb33a2d481c79f) :=
by
  change CTyped (church enabled) (liftCtx e32) (.var 2) (liftTm (Ctx.lookup e32 2))
  rw [← liftCtx_lookup]
  exact .var 2

private theorem e38 : CTyped (church enabled) (liftCtx e32) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8f4340c66c9982da566d) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_91ed245f3db3b637097a) :=
by
  change CTyped (church enabled) (liftCtx e32) (.var 0) (liftTm (Ctx.lookup e32 0))
  rw [← liftCtx_lookup]
  exact .var 0

private theorem e42 : CTyped (church enabled) (liftCtx e32) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a99b4baac3e727fa86a1) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_672f9e7d2edea644a135) :=
by
  change CTyped (church enabled) (liftCtx e32) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_00835ccb59a9bb61fd8d) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8f4340c66c9982da566d)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8f4340c66c9982da566d Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_590b9d34857438c4b1f6))
  rw [liftTm_inst0]
  exact .appElim (e35 enabled) (e38 enabled)

private def e43 : Tower.Ctx 4 :=
.snoc e32 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a99b4baac3e727fa86a1

private theorem e46 : CTyped (church enabled) (liftCtx e43) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_79e72e1cc2f009b67130) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_52958d2f7f9cac1b69b6) :=
by
  change CTyped (church enabled) (liftCtx e43) (.var 3) (liftTm (Ctx.lookup e43 3))
  rw [← liftCtx_lookup]
  exact .var 3

private theorem e49 : CTyped (church enabled) (liftCtx e43) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_87761e7a89c36c978f0c) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b1ec2ecc3564f4f6bd3b) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e12 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e52 : CTyped (church enabled) (liftCtx e43) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_41ed62600d0ff298be98) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7090374f1485408a1741) :=
by
  change CTyped (church enabled) (liftCtx e43) (.var 1) (liftTm (Ctx.lookup e43 1))
  rw [← liftCtx_lookup]
  exact .var 1

private theorem e55 : CTyped (church enabled) (liftCtx e43) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eb3d3c7785cd6e0ac515) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7090374f1485408a1741) :=
by
  change CTyped (church enabled) (liftCtx e43) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_87761e7a89c36c978f0c) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_41ed62600d0ff298be98)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_41ed62600d0ff298be98 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_02c898a5fa9dca7e390e))
  rw [liftTm_inst0]
  exact .appElim (e49 enabled) (e52 enabled)

private theorem e58 : CTyped (church enabled) (liftCtx e43) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6f54549db32bd724af34) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_590b9d34857438c4b1f6) :=
by
  change CTyped (church enabled) (liftCtx e43) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_79e72e1cc2f009b67130) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eb3d3c7785cd6e0ac515)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eb3d3c7785cd6e0ac515 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cb3e2cc4e841f82b5b17))
  rw [liftTm_inst0]
  exact .appElim (e46 enabled) (e55 enabled)

private theorem e61 : CTyped (church enabled) (liftCtx e32) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_260b08d4427c593f9feb) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f80c04d130be5f029cc1) :=
.piForm (e42 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e58 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e64 : CTyped (church enabled) (liftCtx e28) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ab99f6fe674f4f292d16) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5da75a8e88a2f5549b00) :=
.piForm (e31 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e61 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e65 : Tower.Ctx 3 :=
.snoc e28 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ab99f6fe674f4f292d16

private theorem e67 : CTyped (church enabled) (liftCtx e65) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_91ed245f3db3b637097a) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ddda40490d45a084fc70) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e3 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e68 : Tower.Ctx 4 :=
.snoc e65 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_91ed245f3db3b637097a

private theorem e69 : CTyped (church enabled) (liftCtx e68) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_79e72e1cc2f009b67130) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_52958d2f7f9cac1b69b6) :=
by
  change CTyped (church enabled) (liftCtx e68) (.var 3) (liftTm (Ctx.lookup e68 3))
  rw [← liftCtx_lookup]
  exact .var 3

private theorem e71 : CTyped (church enabled) (liftCtx e68) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_877d4c7461ca80be7a82) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7090374f1485408a1741) :=
by
  change CTyped (church enabled) (liftCtx e68) (.var 0) (liftTm (Ctx.lookup e68 0))
  rw [← liftCtx_lookup]
  exact .var 0

private theorem e73 : CTyped (church enabled) (liftCtx e68) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_14088f7e0dedd6f8aa6b) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_590b9d34857438c4b1f6) :=
by
  change CTyped (church enabled) (liftCtx e68) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_79e72e1cc2f009b67130) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_877d4c7461ca80be7a82)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_877d4c7461ca80be7a82 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cb3e2cc4e841f82b5b17))
  rw [liftTm_inst0]
  exact .appElim (e69 enabled) (e71 enabled)

private theorem e76 : CTyped (church enabled) (liftCtx e65) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_60181b733197c405ba48) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d5afc8ebaed355341274) :=
.piForm (e67 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e73 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e79 : CTyped (church enabled) (liftCtx e28) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8c449da761cb6792c60c) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_31da6eba7e6ca22fe90f) :=
.piForm (e64 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e76 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e82 : CTyped (church enabled) (liftCtx e19) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d322aab848780adb9932) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3ccd1d96c391128574ce) :=
.piForm (e27 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e79 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e85 : CTyped (church enabled) (liftCtx e0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4d851166eb550ac34558) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d153546ae9ecba0b018a) :=
.piForm (e18 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e82 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e88 : CTyped (church enabled) (liftCtx e0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_003f1c1bfee893c3d4f3) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f0bc4adfaad6685e03eb) :=
.headType (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e89 : Tower.Ctx 1 :=
.snoc e0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_003f1c1bfee893c3d4f3

private theorem e90 : CTyped (church enabled) (liftCtx e89) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_335242b771a931d18c5a) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_83ee15629b1bf92f199d) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e3 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e91 : Tower.Ctx 2 :=
.snoc e89 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_335242b771a931d18c5a

private theorem e94 : CTyped (church enabled) (liftCtx e91) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_393305a5fb0280dd5557) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0ba6f27680f92f5a8c8c) :=
.headType (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e97 : CTyped (church enabled) (liftCtx e89) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_62988b57faa6db64607a) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a94c48294f2423bdf2bb) :=
.piForm (e90 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e94 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e100 : CTyped (church enabled) (liftCtx e0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6a3560c23b32d57d2e66) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ca0a9ad298fa7d1c75f7) :=
.piForm (e88 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e97 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e103 : CTyped (church enabled) (liftCtx e89) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4256c5ecdc6b1d7cf564) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08f3eba25b44608a5443) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e100 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e105 : CTyped (church enabled) (liftCtx e89) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6779083e6f4ae6a4b575) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_51057c62b6697d24bc8b) :=
by
  change CTyped (church enabled) (liftCtx e89) (.var 0) (liftTm (Ctx.lookup e89 0))
  rw [← liftCtx_lookup]
  exact .var 0

private theorem e108 : CTyped (church enabled) (liftCtx e89) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f0e472aad6a638ddda87) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_62988b57faa6db64607a) :=
by
  change CTyped (church enabled) (liftCtx e89) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4256c5ecdc6b1d7cf564) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6779083e6f4ae6a4b575)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6779083e6f4ae6a4b575 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d7877835337389544bbc))
  rw [liftTm_inst0]
  exact .appElim (e103 enabled) (e105 enabled)

private theorem e109 : CTyped (church enabled) (liftCtx e89) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a29f58d1c6dc0ad93027) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_335242b771a931d18c5a) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e5 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e111 : CTyped (church enabled) (liftCtx e89) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_14f733fb9b6c7873512f) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_51057c62b6697d24bc8b) :=
by
  change CTyped (church enabled) (liftCtx e89) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f0e472aad6a638ddda87) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a29f58d1c6dc0ad93027)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a29f58d1c6dc0ad93027 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_393305a5fb0280dd5557))
  rw [liftTm_inst0]
  exact .appElim (e108 enabled) (e109 enabled)

private theorem e114 : CTyped (church enabled) (liftCtx e0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_54609e6eb2e841e41460) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6c2481ab8e3ca18e1ef4) :=
.piForm (e88 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e111 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e116 : CTyped (church enabled) (liftCtx e91) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_93a26ce10f67e5996c83) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_393305a5fb0280dd5557) :=
by
  change CTyped (church enabled) (liftCtx e91) (.var 1) (liftTm (Ctx.lookup e91 1))
  rw [← liftCtx_lookup]
  exact .var 1

private def e117 : Tower.Ctx 3 :=
.snoc e91 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_93a26ce10f67e5996c83

private theorem e120 : CTyped (church enabled) (liftCtx e117) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c886c9ead3da053ca3a2) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db449e01802c56231743) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e100 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e122 : CTyped (church enabled) (liftCtx e117) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_00835ccb59a9bb61fd8d) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_04aeab44f3773c0fe12b) :=
by
  change CTyped (church enabled) (liftCtx e117) (.var 2) (liftTm (Ctx.lookup e117 2))
  rw [← liftCtx_lookup]
  exact .var 2

private theorem e126 : CTyped (church enabled) (liftCtx e117) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e4635eda7cb8212819e1) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b7772273e98bbeb426e5) :=
by
  change CTyped (church enabled) (liftCtx e117) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c886c9ead3da053ca3a2) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_00835ccb59a9bb61fd8d)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_00835ccb59a9bb61fd8d Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5f9d3007e7f9f1651c30))
  rw [liftTm_inst0]
  exact .appElim (e120 enabled) (e122 enabled)

private theorem e128 : CTyped (church enabled) (liftCtx e117) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81bcbe5936e626d62919) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_91ed245f3db3b637097a) :=
by
  change CTyped (church enabled) (liftCtx e117) (.var 1) (liftTm (Ctx.lookup e117 1))
  rw [← liftCtx_lookup]
  exact .var 1

private theorem e131 : CTyped (church enabled) (liftCtx e117) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_78c9c0837f2eefdbd277) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_04aeab44f3773c0fe12b) :=
by
  change CTyped (church enabled) (liftCtx e117) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e4635eda7cb8212819e1) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81bcbe5936e626d62919)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81bcbe5936e626d62919 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c7cb76ff373981f8647))
  rw [liftTm_inst0]
  exact .appElim (e126 enabled) (e128 enabled)

private def e132 : Tower.Ctx 4 :=
.snoc e117 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_78c9c0837f2eefdbd277

private theorem e135 : CTyped (church enabled) (liftCtx e132) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ce757f42c940be45450c) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5346373ce7d68868316a) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e100 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e136 : CTyped (church enabled) (liftCtx e132) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_79e72e1cc2f009b67130) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c7cb76ff373981f8647) :=
by
  change CTyped (church enabled) (liftCtx e132) (.var 3) (liftTm (Ctx.lookup e132 3))
  rw [← liftCtx_lookup]
  exact .var 3

private theorem e139 : CTyped (church enabled) (liftCtx e132) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_73f5f0576b3f51cce921) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5f9d3007e7f9f1651c30) :=
by
  change CTyped (church enabled) (liftCtx e132) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ce757f42c940be45450c) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_79e72e1cc2f009b67130)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_79e72e1cc2f009b67130 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9980f8597757656a7bcd))
  rw [liftTm_inst0]
  exact .appElim (e135 enabled) (e136 enabled)

private theorem e140 : CTyped (church enabled) (liftCtx e132) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_87761e7a89c36c978f0c) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b1ec2ecc3564f4f6bd3b) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e12 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e142 : CTyped (church enabled) (liftCtx e132) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f8b9519d7a5926320085) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7090374f1485408a1741) :=
by
  change CTyped (church enabled) (liftCtx e132) (.var 2) (liftTm (Ctx.lookup e132 2))
  rw [← liftCtx_lookup]
  exact .var 2

private theorem e144 : CTyped (church enabled) (liftCtx e132) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6a79aec368302f82c2e0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7090374f1485408a1741) :=
by
  change CTyped (church enabled) (liftCtx e132) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_87761e7a89c36c978f0c) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f8b9519d7a5926320085)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f8b9519d7a5926320085 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_02c898a5fa9dca7e390e))
  rw [liftTm_inst0]
  exact .appElim (e140 enabled) (e142 enabled)

private theorem e147 : CTyped (church enabled) (liftCtx e132) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5f93e6bd2acc9f024104) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c7cb76ff373981f8647) :=
by
  change CTyped (church enabled) (liftCtx e132) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_73f5f0576b3f51cce921) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6a79aec368302f82c2e0)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6a79aec368302f82c2e0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5978e1f6d4b31cb31598))
  rw [liftTm_inst0]
  exact .appElim (e139 enabled) (e144 enabled)

private theorem e150 : CTyped (church enabled) (liftCtx e117) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7f8c82888ad049db7a0c) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_48d4e24aec7cce841d18) :=
.piForm (e131 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e147 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e153 : CTyped (church enabled) (liftCtx e91) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3c053fa64fb8083d2c20) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ce1b5323898906efc731) :=
.piForm (e116 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e150 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e156 : CTyped (church enabled) (liftCtx e89) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_950dcac2621bf1635915) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a643898f03630ead198b) :=
.piForm (e90 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e153 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e159 : CTyped (church enabled) (liftCtx e0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_39bdea5f8a10d483f750) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d5d8d09ae2bab04fcd7e) :=
.piForm (e88 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e156 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e162 : CTyped (church enabled) (liftCtx e91) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0dbc1dc9b45f07cea224) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c68aa4f30b07c2a5898a) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e100 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e164 : CTyped (church enabled) (liftCtx e91) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_870ad693fefbdfa41c88) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d7877835337389544bbc) :=
by
  change CTyped (church enabled) (liftCtx e91) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0dbc1dc9b45f07cea224) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_93a26ce10f67e5996c83)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_93a26ce10f67e5996c83 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b7772273e98bbeb426e5))
  rw [liftTm_inst0]
  exact .appElim (e162 enabled) (e116 enabled)

private theorem e166 : CTyped (church enabled) (liftCtx e91) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a9cc3400692fcc694d7b) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e7afc61b162c474cee28) :=
by
  change CTyped (church enabled) (liftCtx e91) (.var 0) (liftTm (Ctx.lookup e91 0))
  rw [← liftCtx_lookup]
  exact .var 0

private theorem e168 : CTyped (church enabled) (liftCtx e91) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b8ef9cc570cee757f8ce) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_393305a5fb0280dd5557) :=
by
  change CTyped (church enabled) (liftCtx e91) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_870ad693fefbdfa41c88) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a9cc3400692fcc694d7b)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a9cc3400692fcc694d7b Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_04aeab44f3773c0fe12b))
  rw [liftTm_inst0]
  exact .appElim (e164 enabled) (e166 enabled)

private def e169 : Tower.Ctx 3 :=
.snoc e91 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b8ef9cc570cee757f8ce

private theorem e171 : CTyped (church enabled) (liftCtx e169) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_672f9e7d2edea644a135) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_314d326d853bb42dbe05) :=
.headType (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e174 : CTyped (church enabled) (liftCtx e91) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9b826281c2b765f17ca3) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cc200f68be6b441b5792) :=
.piForm (e168 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e171 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e177 : CTyped (church enabled) (liftCtx e89) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1846a14eb6f6b7530ad5) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a24a37211dc860869f7d) :=
.piForm (e90 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e174 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e178 : Tower.Ctx 2 :=
.snoc e89 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1846a14eb6f6b7530ad5

private theorem e180 : CTyped (church enabled) (liftCtx e178) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a9cc3400692fcc694d7b) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_92849bda1e175dcc9898) :=
by
  change CTyped (church enabled) (liftCtx e178) (.var 0) (liftTm (Ctx.lookup e178 0))
  rw [← liftCtx_lookup]
  exact .var 0

private theorem e182 : CTyped (church enabled) (liftCtx e178) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2972f002d28935dcfd3d) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e7afc61b162c474cee28) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e5 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e186 : CTyped (church enabled) (liftCtx e178) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_487ca439182b88af3c61) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_286d07078c44a76e3a7d) :=
by
  change CTyped (church enabled) (liftCtx e178) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a9cc3400692fcc694d7b) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2972f002d28935dcfd3d)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2972f002d28935dcfd3d Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08cbdb93fef460d728ac))
  rw [liftTm_inst0]
  exact .appElim (e180 enabled) (e182 enabled)

private theorem e189 : CTyped (church enabled) (liftCtx e178) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bdff103ce269e817c3db) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6922b74c5549cfba5db0) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e114 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e190 : CTyped (church enabled) (liftCtx e178) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_93a26ce10f67e5996c83) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_393305a5fb0280dd5557) :=
by
  change CTyped (church enabled) (liftCtx e178) (.var 1) (liftTm (Ctx.lookup e178 1))
  rw [← liftCtx_lookup]
  exact .var 1

private theorem e194 : CTyped (church enabled) (liftCtx e178) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c1710b32edd792beb1fb) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e12ca69c4e9e56abe06b) :=
by
  change CTyped (church enabled) (liftCtx e178) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bdff103ce269e817c3db) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_93a26ce10f67e5996c83)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_93a26ce10f67e5996c83 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_919cc98a3d9e483f7cc8))
  rw [liftTm_inst0]
  exact .appElim (e189 enabled) (e190 enabled)

private theorem e196 : CTyped (church enabled) (liftCtx e178) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d8847226a92f6a315e45) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8f0c544fe181823a37fb) :=
by
  change CTyped (church enabled) (liftCtx e178) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_487ca439182b88af3c61) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c1710b32edd792beb1fb)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c1710b32edd792beb1fb Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_672f9e7d2edea644a135))
  rw [liftTm_inst0]
  exact .appElim (e186 enabled) (e194 enabled)

private def e197 : Tower.Ctx 3 :=
.snoc e178 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d8847226a92f6a315e45

private theorem e198 : CTyped (church enabled) (liftCtx e197) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_91ed245f3db3b637097a) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ddda40490d45a084fc70) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e3 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e199 : Tower.Ctx 4 :=
.snoc e197 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_91ed245f3db3b637097a

private theorem e200 : CTyped (church enabled) (liftCtx e199) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_79e72e1cc2f009b67130) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c7cb76ff373981f8647) :=
by
  change CTyped (church enabled) (liftCtx e199) (.var 3) (liftTm (Ctx.lookup e199 3))
  rw [← liftCtx_lookup]
  exact .var 3

private def e201 : Tower.Ctx 5 :=
.snoc e199 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_79e72e1cc2f009b67130

private theorem e204 : CTyped (church enabled) (liftCtx e201) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_65d9d95480dbc2f1ded2) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bb72eb520d44887deca2) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e100 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e206 : CTyped (church enabled) (liftCtx e201) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f76f44da44e23bb59ec9) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5978e1f6d4b31cb31598) :=
by
  change CTyped (church enabled) (liftCtx e201) (.var 4) (liftTm (Ctx.lookup e201 4))
  rw [← liftCtx_lookup]
  exact .var 4

private theorem e209 : CTyped (church enabled) (liftCtx e201) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7d4fd3f2250d203d59f3) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9980f8597757656a7bcd) :=
by
  change CTyped (church enabled) (liftCtx e201) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_65d9d95480dbc2f1ded2) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f76f44da44e23bb59ec9)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f76f44da44e23bb59ec9 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_29a7d6b9bc23429813f3))
  rw [liftTm_inst0]
  exact .appElim (e204 enabled) (e206 enabled)

private theorem e211 : CTyped (church enabled) (liftCtx e201) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8c02109425bbbb3ea1bf) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_02c898a5fa9dca7e390e) :=
by
  change CTyped (church enabled) (liftCtx e201) (.var 1) (liftTm (Ctx.lookup e201 1))
  rw [← liftCtx_lookup]
  exact .var 1

private theorem e214 : CTyped (church enabled) (liftCtx e201) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_954c51aacad4d5852c3a) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5978e1f6d4b31cb31598) :=
by
  change CTyped (church enabled) (liftCtx e201) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7d4fd3f2250d203d59f3) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8c02109425bbbb3ea1bf)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8c02109425bbbb3ea1bf Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_39e100ccd2d3487475a1))
  rw [liftTm_inst0]
  exact .appElim (e209 enabled) (e211 enabled)

private def e215 : Tower.Ctx 6 :=
.snoc e201 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_954c51aacad4d5852c3a

private theorem e218 : CTyped (church enabled) (liftCtx e215) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_056b5dfa78050fcc66c2) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3af7ab1d8b7b077b59eb) :=
by
  change CTyped (church enabled) (liftCtx e215) (.var 4) (liftTm (Ctx.lookup e215 4))
  rw [← liftCtx_lookup]
  exact .var 4

private theorem e221 : CTyped (church enabled) (liftCtx e215) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_273b38f3b5e65eba2867) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_545fb4a3c03c82a175c1) :=
by
  change CTyped (church enabled) (liftCtx e215) (.var 2) (liftTm (Ctx.lookup e215 2))
  rw [← liftCtx_lookup]
  exact .var 2

private theorem e225 : CTyped (church enabled) (liftCtx e215) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a69ad8f8a2e727f9d398) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c3e34a3f753ef4943c63) :=
by
  change CTyped (church enabled) (liftCtx e215) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_056b5dfa78050fcc66c2) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_273b38f3b5e65eba2867)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_273b38f3b5e65eba2867 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_76415f19ac300cd36e5e))
  rw [liftTm_inst0]
  exact .appElim (e218 enabled) (e221 enabled)

private theorem e228 : CTyped (church enabled) (liftCtx e215) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_56ec059523fbc107fa64) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5b5fbd485bc823ecfe93) :=
by
  change CTyped (church enabled) (liftCtx e215) (.var 0) (liftTm (Ctx.lookup e215 0))
  rw [← liftCtx_lookup]
  exact .var 0

private theorem e232 : CTyped (church enabled) (liftCtx e215) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9fa4b2482385b000b181) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8cfdc317de8010022515) :=
by
  change CTyped (church enabled) (liftCtx e215) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a69ad8f8a2e727f9d398) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_56ec059523fbc107fa64)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_56ec059523fbc107fa64 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_31075591d3aa7302b989))
  rw [liftTm_inst0]
  exact .appElim (e225 enabled) (e228 enabled)

private def e233 : Tower.Ctx 7 :=
.snoc e215 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9fa4b2482385b000b181

private theorem e236 : CTyped (church enabled) (liftCtx e233) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe9d218f641fcefd695) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_99dadea86f0de0dceb88) :=
by
  change CTyped (church enabled) (liftCtx e233) (.var 5) (liftTm (Ctx.lookup e233 5))
  rw [← liftCtx_lookup]
  exact .var 5

private theorem e239 : CTyped (church enabled) (liftCtx e233) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_312107dd2e68ad3ddd2f) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d5183b284fe9ad320f74) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e12 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e242 : CTyped (church enabled) (liftCtx e233) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b7ce038d373481fd5fe4) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) :=
by
  change CTyped (church enabled) (liftCtx e233) (.var 3) (liftTm (Ctx.lookup e233 3))
  rw [← liftCtx_lookup]
  exact .var 3

private theorem e245 : CTyped (church enabled) (liftCtx e233) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6bbc8075f0c8052e50fc) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) :=
by
  change CTyped (church enabled) (liftCtx e233) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_312107dd2e68ad3ddd2f) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b7ce038d373481fd5fe4)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b7ce038d373481fd5fe4 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_56760c9c60918cbf3d6f))
  rw [liftTm_inst0]
  exact .appElim (e239 enabled) (e242 enabled)

private theorem e249 : CTyped (church enabled) (liftCtx e233) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8326c26551056504cb0d) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f93db85810eb711d8da7) :=
by
  change CTyped (church enabled) (liftCtx e233) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe9d218f641fcefd695) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6bbc8075f0c8052e50fc)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6bbc8075f0c8052e50fc Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a6979d08019301405ee5))
  rw [liftTm_inst0]
  exact .appElim (e236 enabled) (e245 enabled)

private theorem e252 : CTyped (church enabled) (liftCtx e233) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eb43856947939657cceb) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6460a0b05b820bfbc879) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e159 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e255 : CTyped (church enabled) (liftCtx e233) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3531df46ccfd426e0cca) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d064c25dd26291905510) :=
by
  change CTyped (church enabled) (liftCtx e233) (.var 6) (liftTm (Ctx.lookup e233 6))
  rw [← liftCtx_lookup]
  exact .var 6

private theorem e259 : CTyped (church enabled) (liftCtx e233) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_62e22fbc88f1307cad24) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_47f226860841a7f9ac0c) :=
by
  change CTyped (church enabled) (liftCtx e233) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eb43856947939657cceb) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3531df46ccfd426e0cca)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3531df46ccfd426e0cca Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4cbe43a0a127e9394a51))
  rw [liftTm_inst0]
  exact .appElim (e252 enabled) (e255 enabled)

private theorem e263 : CTyped (church enabled) (liftCtx e233) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f7ff4db1a312046e7e19) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c05c8dd88fdde5ec2cec) :=
by
  change CTyped (church enabled) (liftCtx e233) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_62e22fbc88f1307cad24) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b7ce038d373481fd5fe4)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b7ce038d373481fd5fe4 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c44731ad96e2746277d2))
  rw [liftTm_inst0]
  exact .appElim (e259 enabled) (e242 enabled)

private theorem e265 : CTyped (church enabled) (liftCtx e233) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_098d0b75ed5b79ff51b3) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3531df46ccfd426e0cca) :=
by
  change CTyped (church enabled) (liftCtx e233) (.var 2) (liftTm (Ctx.lookup e233 2))
  rw [← liftCtx_lookup]
  exact .var 2

private theorem e269 : CTyped (church enabled) (liftCtx e233) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7f02c01378ede7bac2ae) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d84da24277ee8f52bb84) :=
by
  change CTyped (church enabled) (liftCtx e233) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f7ff4db1a312046e7e19) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_098d0b75ed5b79ff51b3)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_098d0b75ed5b79ff51b3 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3e55b1ff9532df185a5e))
  rw [liftTm_inst0]
  exact .appElim (e263 enabled) (e265 enabled)

private theorem e272 : CTyped (church enabled) (liftCtx e233) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3e722ce8c62222c102c3) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c8e19a09c3d5fbe75654) :=
by
  change CTyped (church enabled) (liftCtx e233) (.var 1) (liftTm (Ctx.lookup e233 1))
  rw [← liftCtx_lookup]
  exact .var 1

private theorem e276 : CTyped (church enabled) (liftCtx e233) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4007c4d2b9c1718548c2) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_02622304141c4f3f2ef4) :=
by
  change CTyped (church enabled) (liftCtx e233) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7f02c01378ede7bac2ae) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3e722ce8c62222c102c3)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3e722ce8c62222c102c3 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d7fa212ebc80f7fe757a))
  rw [liftTm_inst0]
  exact .appElim (e269 enabled) (e272 enabled)

private theorem e279 : CTyped (church enabled) (liftCtx e233) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_49cdfe56a84976e06ec2) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_31075591d3aa7302b989) :=
by
  change CTyped (church enabled) (liftCtx e233) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8326c26551056504cb0d) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4007c4d2b9c1718548c2)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4007c4d2b9c1718548c2 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8e62d06b6eb6233cc66d))
  rw [liftTm_inst0]
  exact .appElim (e249 enabled) (e276 enabled)

private theorem e282 : CTyped (church enabled) (liftCtx e215) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3121b3b490bfda80da4e) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c9816b2bf85b23e29655) :=
.piForm (e232 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e279 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e285 : CTyped (church enabled) (liftCtx e201) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_23f845487ad7a6b3f234) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a5511a4a5ddad9890fe2) :=
.piForm (e214 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e282 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e288 : CTyped (church enabled) (liftCtx e199) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d05718d9e815dabd9eca) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f42c4bcfd49f006ab6) :=
.piForm (e200 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e285 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e291 : CTyped (church enabled) (liftCtx e197) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ab74def4828ff76361d5) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_537dce148b0d61baf659) :=
.piForm (e198 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e288 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e292 : Tower.Ctx 4 :=
.snoc e197 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ab74def4828ff76361d5

private theorem e294 : CTyped (church enabled) (liftCtx e292) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7090374f1485408a1741) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2e394dc7764de11694e2) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e3 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private def e295 : Tower.Ctx 5 :=
.snoc e292 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7090374f1485408a1741

private theorem e296 : CTyped (church enabled) (liftCtx e295) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_65d9d95480dbc2f1ded2) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bb72eb520d44887deca2) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e100 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e297 : CTyped (church enabled) (liftCtx e295) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f76f44da44e23bb59ec9) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5978e1f6d4b31cb31598) :=
by
  change CTyped (church enabled) (liftCtx e295) (.var 4) (liftTm (Ctx.lookup e295 4))
  rw [← liftCtx_lookup]
  exact .var 4

private theorem e298 : CTyped (church enabled) (liftCtx e295) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7d4fd3f2250d203d59f3) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9980f8597757656a7bcd) :=
by
  change CTyped (church enabled) (liftCtx e295) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_65d9d95480dbc2f1ded2) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f76f44da44e23bb59ec9)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f76f44da44e23bb59ec9 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_29a7d6b9bc23429813f3))
  rw [liftTm_inst0]
  exact .appElim (e296 enabled) (e297 enabled)

private theorem e300 : CTyped (church enabled) (liftCtx e295) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5828ffe8fb218f9a07e9) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_02c898a5fa9dca7e390e) :=
by
  change CTyped (church enabled) (liftCtx e295) (.var 0) (liftTm (Ctx.lookup e295 0))
  rw [← liftCtx_lookup]
  exact .var 0

private theorem e302 : CTyped (church enabled) (liftCtx e295) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e7181f063d09c15d1fe3) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5978e1f6d4b31cb31598) :=
by
  change CTyped (church enabled) (liftCtx e295) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7d4fd3f2250d203d59f3) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5828ffe8fb218f9a07e9)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5828ffe8fb218f9a07e9 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_39e100ccd2d3487475a1))
  rw [liftTm_inst0]
  exact .appElim (e298 enabled) (e300 enabled)

private def e303 : Tower.Ctx 6 :=
.snoc e295 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e7181f063d09c15d1fe3

private theorem e304 : CTyped (church enabled) (liftCtx e303) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_056b5dfa78050fcc66c2) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3af7ab1d8b7b077b59eb) :=
by
  change CTyped (church enabled) (liftCtx e303) (.var 4) (liftTm (Ctx.lookup e303 4))
  rw [← liftCtx_lookup]
  exact .var 4

private theorem e306 : CTyped (church enabled) (liftCtx e303) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eb5c1c7ee9c99a04c1f0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_545fb4a3c03c82a175c1) :=
by
  change CTyped (church enabled) (liftCtx e303) (.var 1) (liftTm (Ctx.lookup e303 1))
  rw [← liftCtx_lookup]
  exact .var 1

private theorem e309 : CTyped (church enabled) (liftCtx e303) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0f4c81da9dba6d3baa85) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_69dd07658deab3ac3d62) :=
by
  change CTyped (church enabled) (liftCtx e303) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_056b5dfa78050fcc66c2) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eb5c1c7ee9c99a04c1f0)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eb5c1c7ee9c99a04c1f0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_76415f19ac300cd36e5e))
  rw [liftTm_inst0]
  exact .appElim (e304 enabled) (e306 enabled)

private theorem e311 : CTyped (church enabled) (liftCtx e303) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_56ec059523fbc107fa64) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ea1e125d0ec89812d6af) :=
by
  change CTyped (church enabled) (liftCtx e303) (.var 0) (liftTm (Ctx.lookup e303 0))
  rw [← liftCtx_lookup]
  exact .var 0

private theorem e313 : CTyped (church enabled) (liftCtx e303) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fce25c4b681e82857208) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8cfdc317de8010022515) :=
by
  change CTyped (church enabled) (liftCtx e303) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0f4c81da9dba6d3baa85) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_56ec059523fbc107fa64)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_56ec059523fbc107fa64 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_31075591d3aa7302b989))
  rw [liftTm_inst0]
  exact .appElim (e309 enabled) (e311 enabled)

private theorem e316 : CTyped (church enabled) (liftCtx e295) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b87ec2dd9fe2ea6ce633) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b655c0b04ba425b2c21) :=
.piForm (e302 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e313 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e319 : CTyped (church enabled) (liftCtx e292) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2c5c6302e0b16c7f6f25) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ba8eaa3f3272434871c6) :=
.piForm (e294 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e316 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e322 : CTyped (church enabled) (liftCtx e197) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a28b5af9302eb82e8662) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eab0bb335da65c004569) :=
.piForm (e291 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e319 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e325 : CTyped (church enabled) (liftCtx e178) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_425229d4431e2dde830c) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_186725e85eeabbfa936b) :=
.piForm (e196 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e322 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e328 : CTyped (church enabled) (liftCtx e89) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8bc9c67405b5122335a7) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7671e1fa7ac2a6ff2148) :=
.piForm (e177 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e325 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e331 : CTyped (church enabled) (liftCtx e0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c8254397a208bf80bef4) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5fa383beac0f294d28d0) :=
.piForm (e88 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (e328 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e334 : CTyped (church enabled) (liftCtx e65) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_74ee832e717092ebdc5b) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_398b34734648160d836c) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e85 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e335 : CTyped (church enabled) (liftCtx e65) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_00835ccb59a9bb61fd8d) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_afca4aeb33a2d481c79f) :=
by
  change CTyped (church enabled) (liftCtx e65) (.var 2) (liftTm (Ctx.lookup e65 2))
  rw [← liftCtx_lookup]
  exact .var 2

private theorem e339 : CTyped (church enabled) (liftCtx e65) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0d4bd9e9413f821dd433) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_801695c718aede18f34b) :=
by
  change CTyped (church enabled) (liftCtx e65) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_74ee832e717092ebdc5b) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_00835ccb59a9bb61fd8d)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_00835ccb59a9bb61fd8d Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ee7f2a78358f6b8e123e))
  rw [liftTm_inst0]
  exact .appElim (e334 enabled) (e335 enabled)

private theorem e341 : CTyped (church enabled) (liftCtx e65) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81bcbe5936e626d62919) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b7266f290fc09f9049a) :=
by
  change CTyped (church enabled) (liftCtx e65) (.var 1) (liftTm (Ctx.lookup e65 1))
  rw [← liftCtx_lookup]
  exact .var 1

private theorem e345 : CTyped (church enabled) (liftCtx e65) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_10800778a3565ace6049) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9a05ff9976e6403ec89b) :=
by
  change CTyped (church enabled) (liftCtx e65) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0d4bd9e9413f821dd433) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81bcbe5936e626d62919)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81bcbe5936e626d62919 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b23daa9c18673f14951))
  rw [liftTm_inst0]
  exact .appElim (e339 enabled) (e341 enabled)

private theorem e347 : CTyped (church enabled) (liftCtx e65) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8f4340c66c9982da566d) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_45c52fcde3a98dd8a247) :=
by
  change CTyped (church enabled) (liftCtx e65) (.var 0) (liftTm (Ctx.lookup e65 0))
  rw [← liftCtx_lookup]
  exact .var 0

private theorem e350 : CTyped (church enabled) (liftCtx e65) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dff9a0c0550a4cceeb82) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_60181b733197c405ba48) :=
by
  change CTyped (church enabled) (liftCtx e65) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_10800778a3565ace6049) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8f4340c66c9982da566d)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8f4340c66c9982da566d Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_75666c1059a36f174163))
  rw [liftTm_inst0]
  exact .appElim (e345 enabled) (e347 enabled)

private theorem e352 : CTyped (church enabled) (liftCtx e65) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8e31ce79969183a1b368) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_91ed245f3db3b637097a) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e5 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e354 : CTyped (church enabled) (liftCtx e65) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e295460ba68756d48615) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b7266f290fc09f9049a) :=
by
  change CTyped (church enabled) (liftCtx e65) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dff9a0c0550a4cceeb82) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8e31ce79969183a1b368)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8e31ce79969183a1b368 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_14088f7e0dedd6f8aa6b))
  rw [liftTm_inst0]
  exact .appElim (e350 enabled) (e352 enabled)

private theorem e355 : CCtxFormed (church enabled) (liftCtx e0) :=
.nil

private theorem e356 : CCtxFormed (church enabled) (liftCtx e19) :=
.snoc (e355 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e18 enabled)⟩

private theorem e357 : CCtxFormed (church enabled) (liftCtx e28) :=
.snoc (e356 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e27 enabled)⟩

private theorem e358 : CCtxFormed (church enabled) (liftCtx e65) :=
.snoc (e357 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e64 enabled)⟩

private theorem e361 : CTyped (church enabled) (liftCtx e68) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_839ce6daa2f5e6f5a95d) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dc7e7ef9576ba472fc21) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e85 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e365 : CTyped (church enabled) (liftCtx e68) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d927dfb4a8a449e358ac) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2c9d60a0266e06dcd009) :=
by
  change CTyped (church enabled) (liftCtx e68) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_839ce6daa2f5e6f5a95d) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_79e72e1cc2f009b67130)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_79e72e1cc2f009b67130 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4dddad40cf020d387a7d))
  rw [liftTm_inst0]
  exact .appElim (e361 enabled) (e69 enabled)

private theorem e367 : CTyped (church enabled) (liftCtx e68) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f8b9519d7a5926320085) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ee9e008e17f176df3ffb) :=
by
  change CTyped (church enabled) (liftCtx e68) (.var 2) (liftTm (Ctx.lookup e68 2))
  rw [← liftCtx_lookup]
  exact .var 2

private theorem e370 : CTyped (church enabled) (liftCtx e68) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d80f839636a9d9bf9dd) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b23daa9c18673f14951) :=
by
  change CTyped (church enabled) (liftCtx e68) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d927dfb4a8a449e358ac) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f8b9519d7a5926320085)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f8b9519d7a5926320085 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_441e2aacef30e4a47d46))
  rw [liftTm_inst0]
  exact .appElim (e365 enabled) (e367 enabled)

private theorem e372 : CTyped (church enabled) (liftCtx e68) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_41ed62600d0ff298be98) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_166834bf3186e2ee7aa4) :=
by
  change CTyped (church enabled) (liftCtx e68) (.var 1) (liftTm (Ctx.lookup e68 1))
  rw [← liftCtx_lookup]
  exact .var 1

private theorem e375 : CTyped (church enabled) (liftCtx e68) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_282e2340037ee6790723) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_75666c1059a36f174163) :=
by
  change CTyped (church enabled) (liftCtx e68) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d80f839636a9d9bf9dd) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_41ed62600d0ff298be98)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_41ed62600d0ff298be98 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_50ac2f7a76a2a6dd0297))
  rw [liftTm_inst0]
  exact .appElim (e370 enabled) (e372 enabled)

private theorem e376 : CTyped (church enabled) (liftCtx e68) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_87761e7a89c36c978f0c) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b1ec2ecc3564f4f6bd3b) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e12 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e378 : CTyped (church enabled) (liftCtx e68) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7dee8f8436a9d48c18e3) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7090374f1485408a1741) :=
by
  change CTyped (church enabled) (liftCtx e68) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_87761e7a89c36c978f0c) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_877d4c7461ca80be7a82)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_877d4c7461ca80be7a82 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_02c898a5fa9dca7e390e))
  rw [liftTm_inst0]
  exact .appElim (e376 enabled) (e71 enabled)

private theorem e382 : CTyped (church enabled) (liftCtx e68) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_16c7a3fa1db62f112967) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e152fe0a2dfd7c6b505e) :=
by
  change CTyped (church enabled) (liftCtx e68) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_282e2340037ee6790723) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7dee8f8436a9d48c18e3)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7dee8f8436a9d48c18e3 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4a08c60cf142597f53fe))
  rw [liftTm_inst0]
  exact .appElim (e375 enabled) (e378 enabled)

private theorem e383 : CCtxFormed (church enabled) (liftCtx e68) :=
.snoc (e358 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e67 enabled)⟩

private theorem e387 : CTyped (church enabled) (liftCtx e68) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_194077df2735130bf727) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f213ed00fa2f7efe4303) :=
by
  change CTyped (church enabled) (liftCtx e68) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_41ed62600d0ff298be98) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_877d4c7461ca80be7a82)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_877d4c7461ca80be7a82 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0ec22c84418a652e68af))
  rw [liftTm_inst0]
  exact .appElim (e372 enabled) (e71 enabled)

private theorem e389 : CTyped (church enabled) (liftCtx e68) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_301072ca6951a1dc38a0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_14088f7e0dedd6f8aa6b) :=
by
  change CTyped (church enabled) (liftCtx e68) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_282e2340037ee6790723) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_877d4c7461ca80be7a82)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_877d4c7461ca80be7a82 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4a08c60cf142597f53fe))
  rw [liftTm_inst0]
  exact .appElim (e375 enabled) (e71 enabled)

private theorem e392 : CTyped (church enabled) (liftCtx e68) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b354b97afb3f3d6ffe8) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e152fe0a2dfd7c6b505e) :=
by
  change CTyped (church enabled) (liftCtx e68) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_194077df2735130bf727) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_301072ca6951a1dc38a0)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_301072ca6951a1dc38a0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4bc742a088159ba4e21b))
  rw [liftTm_inst0]
  exact .appElim (e387 enabled) (e389 enabled)

private theorem e395 : CTyped (church enabled) (liftCtx e292) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_75dcbb05889ecac59f71) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d495ba21dcad56b28250) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e331 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e396 : CTyped (church enabled) (liftCtx e292) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_79e72e1cc2f009b67130) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c7cb76ff373981f8647) :=
by
  change CTyped (church enabled) (liftCtx e292) (.var 3) (liftTm (Ctx.lookup e292 3))
  rw [← liftCtx_lookup]
  exact .var 3

private theorem e400 : CTyped (church enabled) (liftCtx e292) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_16a82ed3189fddafc0ab) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c50572e96944e5c83241) :=
by
  change CTyped (church enabled) (liftCtx e292) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_75dcbb05889ecac59f71) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_79e72e1cc2f009b67130)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_79e72e1cc2f009b67130 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e96f5fe34fa22af3dbb5))
  rw [liftTm_inst0]
  exact .appElim (e395 enabled) (e396 enabled)

private theorem e402 : CTyped (church enabled) (liftCtx e292) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f8b9519d7a5926320085) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1169d18eae342af08198) :=
by
  change CTyped (church enabled) (liftCtx e292) (.var 2) (liftTm (Ctx.lookup e292 2))
  rw [← liftCtx_lookup]
  exact .var 2

private theorem e406 : CTyped (church enabled) (liftCtx e292) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ab28739712c3f2747af1) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ab0eaf7d3ed0178d5194) :=
by
  change CTyped (church enabled) (liftCtx e292) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_16a82ed3189fddafc0ab) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f8b9519d7a5926320085)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f8b9519d7a5926320085 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_76dc3e2382c3319235d6))
  rw [liftTm_inst0]
  exact .appElim (e400 enabled) (e402 enabled)

private theorem e408 : CTyped (church enabled) (liftCtx e292) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_41ed62600d0ff298be98) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_535c1fa4cbed718fb795) :=
by
  change CTyped (church enabled) (liftCtx e292) (.var 1) (liftTm (Ctx.lookup e292 1))
  rw [← liftCtx_lookup]
  exact .var 1

private theorem e412 : CTyped (church enabled) (liftCtx e292) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e28feded39ae82cb69af) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_35ab4314dce05e89502a) :=
by
  change CTyped (church enabled) (liftCtx e292) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ab28739712c3f2747af1) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_41ed62600d0ff298be98)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_41ed62600d0ff298be98 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ccd4255ef92d1ea760fa))
  rw [liftTm_inst0]
  exact .appElim (e406 enabled) (e408 enabled)

private theorem e414 : CTyped (church enabled) (liftCtx e292) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_877d4c7461ca80be7a82) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_17bad4374f46794e7168) :=
by
  change CTyped (church enabled) (liftCtx e292) (.var 0) (liftTm (Ctx.lookup e292 0))
  rw [← liftCtx_lookup]
  exact .var 0

private theorem e417 : CTyped (church enabled) (liftCtx e292) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_09626c7ea276b1d33d20) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2c5c6302e0b16c7f6f25) :=
by
  change CTyped (church enabled) (liftCtx e292) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e28feded39ae82cb69af) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_877d4c7461ca80be7a82)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_877d4c7461ca80be7a82 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f7e7eec83df6466b6bad))
  rw [liftTm_inst0]
  exact .appElim (e412 enabled) (e414 enabled)

private theorem e419 : CTyped (church enabled) (liftCtx e292) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_82a2893d012540d0191a) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7090374f1485408a1741) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e5 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e422 : CTyped (church enabled) (liftCtx e292) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d99db99468d9b4ec7c0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_59ea7ff8d8649dc036e3) :=
by
  change CTyped (church enabled) (liftCtx e292) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_09626c7ea276b1d33d20) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_82a2893d012540d0191a)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_82a2893d012540d0191a Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b87ec2dd9fe2ea6ce633))
  rw [liftTm_inst0]
  exact .appElim (e417 enabled) (e419 enabled)

private theorem e425 : CTyped (church enabled) (liftCtx e292) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_12d0f5840d19e180dc26) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_640c67ba991b5e522625) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e114 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e429 : CTyped (church enabled) (liftCtx e292) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9c85be851750b97e18c4) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebc60f68bc765c922ad5) :=
by
  change CTyped (church enabled) (liftCtx e292) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_12d0f5840d19e180dc26) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_79e72e1cc2f009b67130)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_79e72e1cc2f009b67130 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b40b85244ea02d420f44))
  rw [liftTm_inst0]
  exact .appElim (e425 enabled) (e396 enabled)

private theorem e432 : CTyped (church enabled) (liftCtx e292) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_23a053da08baeb355cfa) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_535c1fa4cbed718fb795) :=
by
  change CTyped (church enabled) (liftCtx e292) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d99db99468d9b4ec7c0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9c85be851750b97e18c4)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9c85be851750b97e18c4 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2834b09b80479d70aac1))
  rw [liftTm_inst0]
  exact .appElim (e422 enabled) (e429 enabled)

private theorem e433 : CCtxFormed (church enabled) (liftCtx e89) :=
.snoc (e355 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e88 enabled)⟩

private theorem e434 : CCtxFormed (church enabled) (liftCtx e178) :=
.snoc (e433 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.succ
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))))), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e177 enabled)⟩

private theorem e435 : CCtxFormed (church enabled) (liftCtx e197) :=
.snoc (e434 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e196 enabled)⟩

private theorem e436 : CCtxFormed (church enabled) (liftCtx e292) :=
.snoc (e435 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0)
    (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
      (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
        (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1))
          (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
            (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 1)))))), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e291 enabled)⟩

private def e437 : Tower.Ctx 6 :=
.snoc e295 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f76f44da44e23bb59ec9

private def e438 : Tower.Ctx 7 :=
.snoc e437 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ea1e125d0ec89812d6af

private theorem e441 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8588e0785a1ffecc1a5c) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_248700eebbaf433dfe6d) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e331 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e442 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3531df46ccfd426e0cca) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d064c25dd26291905510) :=
by
  change CTyped (church enabled) (liftCtx e438) (.var 6) (liftTm (Ctx.lookup e438 6))
  rw [← liftCtx_lookup]
  exact .var 6

private theorem e446 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_255ae76a99d1e1af3486) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3d3c199cd54356f62996) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8588e0785a1ffecc1a5c) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3531df46ccfd426e0cca)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3531df46ccfd426e0cca Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_28d1c82697969c284dfa))
  rw [liftTm_inst0]
  exact .appElim (e441 enabled) (e442 enabled)

private theorem e447 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe9d218f641fcefd695) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_99dadea86f0de0dceb88) :=
by
  change CTyped (church enabled) (liftCtx e438) (.var 5) (liftTm (Ctx.lookup e438 5))
  rw [← liftCtx_lookup]
  exact .var 5

private theorem e451 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f751bc335250fee695cb) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_26f6cd5f26fc921e9c80) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_255ae76a99d1e1af3486) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe9d218f641fcefd695)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe9d218f641fcefd695 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6063f25f00d066965c89))
  rw [liftTm_inst0]
  exact .appElim (e446 enabled) (e447 enabled)

private theorem e454 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e02de3a8b35112303820) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e953da9b964163c4db16) :=
by
  change CTyped (church enabled) (liftCtx e438) (.var 4) (liftTm (Ctx.lookup e438 4))
  rw [← liftCtx_lookup]
  exact .var 4

private theorem e458 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_90a2835d4c8329c41260) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c1362f5fd48ab7188368) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f751bc335250fee695cb) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e02de3a8b35112303820)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e02de3a8b35112303820 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_925b79b01f24cdb4620c))
  rw [liftTm_inst0]
  exact .appElim (e451 enabled) (e454 enabled)

private theorem e460 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b7ce038d373481fd5fe4) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1643e1d51795c7075b2d) :=
by
  change CTyped (church enabled) (liftCtx e438) (.var 3) (liftTm (Ctx.lookup e438 3))
  rw [← liftCtx_lookup]
  exact .var 3

private theorem e464 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dfb5470855ec7ca09c11) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fc40dfee771950024b3d) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_90a2835d4c8329c41260) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b7ce038d373481fd5fe4)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b7ce038d373481fd5fe4 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_64652693ea2fd4d930a7))
  rw [liftTm_inst0]
  exact .appElim (e458 enabled) (e460 enabled)

private theorem e465 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_312107dd2e68ad3ddd2f) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d5183b284fe9ad320f74) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e12 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e466 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_098d0b75ed5b79ff51b3) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) :=
by
  change CTyped (church enabled) (liftCtx e438) (.var 2) (liftTm (Ctx.lookup e438 2))
  rw [← liftCtx_lookup]
  exact .var 2

private theorem e468 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1e80b7b7c4b9d5e121ea) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_312107dd2e68ad3ddd2f) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_098d0b75ed5b79ff51b3)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_098d0b75ed5b79ff51b3 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_56760c9c60918cbf3d6f))
  rw [liftTm_inst0]
  exact .appElim (e465 enabled) (e466 enabled)

private theorem e472 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2590903eb288c7e47ad1) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_df83855ed49c8d6f57f2) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dfb5470855ec7ca09c11) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1e80b7b7c4b9d5e121ea)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1e80b7b7c4b9d5e121ea Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e7ebc1c653adcd52b504))
  rw [liftTm_inst0]
  exact .appElim (e464 enabled) (e468 enabled)

private theorem e473 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eb43856947939657cceb) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6460a0b05b820bfbc879) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e159 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e474 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_62e22fbc88f1307cad24) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_47f226860841a7f9ac0c) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eb43856947939657cceb) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3531df46ccfd426e0cca)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3531df46ccfd426e0cca Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4cbe43a0a127e9394a51))
  rw [liftTm_inst0]
  exact .appElim (e473 enabled) (e442 enabled)

private theorem e477 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cb44e7782e701a059aa8) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4016cade1cb50f6a4bcc) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_62e22fbc88f1307cad24) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_098d0b75ed5b79ff51b3)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_098d0b75ed5b79ff51b3 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c44731ad96e2746277d2))
  rw [liftTm_inst0]
  exact .appElim (e474 enabled) (e466 enabled)

private theorem e478 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3e722ce8c62222c102c3) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3531df46ccfd426e0cca) :=
by
  change CTyped (church enabled) (liftCtx e438) (.var 1) (liftTm (Ctx.lookup e438 1))
  rw [← liftCtx_lookup]
  exact .var 1

private theorem e482 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0b7b09bb347bb5ac9775) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_83daf1cf80dfc84e0a7c) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cb44e7782e701a059aa8) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3e722ce8c62222c102c3)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3e722ce8c62222c102c3 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c967c2e46acc18c19adf))
  rw [liftTm_inst0]
  exact .appElim (e477 enabled) (e478 enabled)

private theorem e485 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0a6554b81c57291f8b68) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_61babc0a06ef8aba8578) :=
by
  change CTyped (church enabled) (liftCtx e438) (.var 0) (liftTm (Ctx.lookup e438 0))
  rw [← liftCtx_lookup]
  exact .var 0

private theorem e489 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3d29438bf5b4a777fe20) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_efdd10704b5b2d96bc64) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0b7b09bb347bb5ac9775) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0a6554b81c57291f8b68)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0a6554b81c57291f8b68 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9c79454855099a8ab17f))
  rw [liftTm_inst0]
  exact .appElim (e482 enabled) (e485 enabled)

private theorem e493 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2213c4e84bb59d18b927) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b6394a8cb40ae44d5ed5) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2590903eb288c7e47ad1) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3d29438bf5b4a777fe20)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3d29438bf5b4a777fe20 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b8e96bb6d6e1db4ca932))
  rw [liftTm_inst0]
  exact .appElim (e472 enabled) (e489 enabled)

private theorem e494 : CCtxFormed (church enabled) (liftCtx e295) :=
.snoc (e436 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const 0), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e294 enabled)⟩

private theorem e495 : CCtxFormed (church enabled) (liftCtx e437) :=
.snoc (e494 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e297 enabled)⟩

private theorem e498 : CTyped (church enabled) (liftCtx e437) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7b6af36df4bf3369255d) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1c510f3650f24731a931) :=
.const (by rw [constantType_eq enabled]; clear! enabled; decide +kernel) (e100 enabled) (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel)

private theorem e500 : CTyped (church enabled) (liftCtx e437) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_987df36b061ff751f22f) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_39e100ccd2d3487475a1) :=
by
  change CTyped (church enabled) (liftCtx e437) (.var 5) (liftTm (Ctx.lookup e437 5))
  rw [← liftCtx_lookup]
  exact .var 5

private theorem e503 : CTyped (church enabled) (liftCtx e437) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2f4903672a78731c7f9b) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_29a7d6b9bc23429813f3) :=
by
  change CTyped (church enabled) (liftCtx e437) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7b6af36df4bf3369255d) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_987df36b061ff751f22f)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_987df36b061ff751f22f Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a106cca66cedc9381f50))
  rw [liftTm_inst0]
  exact .appElim (e498 enabled) (e500 enabled)

private theorem e504 : CTyped (church enabled) (liftCtx e437) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eb5c1c7ee9c99a04c1f0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_545fb4a3c03c82a175c1) :=
by
  change CTyped (church enabled) (liftCtx e437) (.var 1) (liftTm (Ctx.lookup e437 1))
  rw [← liftCtx_lookup]
  exact .var 1

private theorem e505 : CTyped (church enabled) (liftCtx e437) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ea1e125d0ec89812d6af) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_39e100ccd2d3487475a1) :=
by
  change CTyped (church enabled) (liftCtx e437) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2f4903672a78731c7f9b) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eb5c1c7ee9c99a04c1f0)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eb5c1c7ee9c99a04c1f0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d064c25dd26291905510))
  rw [liftTm_inst0]
  exact .appElim (e503 enabled) (e504 enabled)

private theorem e506 : CCtxFormed (church enabled) (liftCtx e438) :=
.snoc (e495 enabled) ⟨Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
  (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0), (by dsimp only [church, ChurchRules.ofSchemas, ComputationProfiles.rules, ComputationProfiles.signature, Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?]; clear! enabled; decide +kernel), (e505 enabled)⟩

private theorem e510 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5889962b7b6bbc477455) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d84f4639f5e3207041e4) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b7ce038d373481fd5fe4) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_098d0b75ed5b79ff51b3)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_098d0b75ed5b79ff51b3 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e23ecaa821a25d9a5829))
  rw [liftTm_inst0]
  exact .appElim (e460 enabled) (e466 enabled)

private theorem e514 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a3396ae46268d5efa5c3) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a33ba5a9db06e26e3b59) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5889962b7b6bbc477455) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3e722ce8c62222c102c3)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3e722ce8c62222c102c3 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0a096ab8f1b71a5ad776))
  rw [liftTm_inst0]
  exact .appElim (e510 enabled) (e478 enabled)

private theorem e518 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9b92141a452211f14bca) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_697defed3ebe166bc563) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a3396ae46268d5efa5c3) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0a6554b81c57291f8b68)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0a6554b81c57291f8b68 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0acc26c4bb5cc7527c08))
  rw [liftTm_inst0]
  exact .appElim (e514 enabled) (e485 enabled)

private theorem e521 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1e6f515f9f597e819769) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a1f32ea193968438465b) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dfb5470855ec7ca09c11) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_098d0b75ed5b79ff51b3)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_098d0b75ed5b79ff51b3 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e7ebc1c653adcd52b504))
  rw [liftTm_inst0]
  exact .appElim (e464 enabled) (e466 enabled)

private theorem e525 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f60e194ed63f0683f5a2) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a168f88a6228dd7a3a8c) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1e6f515f9f597e819769) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0a6554b81c57291f8b68)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0a6554b81c57291f8b68 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_98dd1faebfdd2f71e1e1))
  rw [liftTm_inst0]
  exact .appElim (e521 enabled) (e485 enabled)

private theorem e528 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_75386fddd4eb13447bb7) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b6394a8cb40ae44d5ed5) :=
by
  change CTyped (church enabled) (liftCtx e438) (.app (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9b92141a452211f14bca) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f60e194ed63f0683f5a2)) (liftTm (inst0 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f60e194ed63f0683f5a2 Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ace4dbcbd47d9f00b042))
  rw [liftTm_inst0]
  exact .appElim (e518 enabled) (e525 enabled)

theorem declaration_0 : CTyped (church enabled) (liftCtx e0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e8abf992014c6a64d384) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6bbe1c48b2bd1700632c) := (e3 enabled)

theorem declaration_1 : CTyped (church enabled) (liftCtx e0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4a27bce6d6d25fd1b645) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e8abf992014c6a64d384) := (e5 enabled)

theorem declaration_2 : CTyped (church enabled) (liftCtx e0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b3898b5267cea17e248e) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a60a9e3309f85030c85e) := (e12 enabled)

theorem declaration_3 : CTyped (church enabled) (liftCtx e0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4d851166eb550ac34558) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d153546ae9ecba0b018a) := (e85 enabled)

theorem declaration_4 : CTyped (church enabled) (liftCtx e0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6a3560c23b32d57d2e66) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ca0a9ad298fa7d1c75f7) := (e100 enabled)

theorem declaration_5 : CTyped (church enabled) (liftCtx e0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_54609e6eb2e841e41460) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6c2481ab8e3ca18e1ef4) := (e114 enabled)

theorem declaration_6 : CTyped (church enabled) (liftCtx e0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_39bdea5f8a10d483f750) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d5d8d09ae2bab04fcd7e) := (e159 enabled)

theorem declaration_7 : CTyped (church enabled) (liftCtx e0) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c8254397a208bf80bef4) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5fa383beac0f294d28d0) := (e331 enabled)

theorem left_0 : CTyped (church enabled) (liftCtx e65) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e295460ba68756d48615) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b7266f290fc09f9049a) := (e354 enabled)

theorem context_0 : CCtxFormed (church enabled) (liftCtx e65) := (e358 enabled)

theorem right_0 : CTyped (church enabled) (liftCtx e65) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81bcbe5936e626d62919) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b7266f290fc09f9049a) := (e341 enabled)

theorem left_1 : CTyped (church enabled) (liftCtx e68) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_16c7a3fa1db62f112967) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e152fe0a2dfd7c6b505e) := (e382 enabled)

theorem context_1 : CCtxFormed (church enabled) (liftCtx e68) := (e383 enabled)

theorem right_1 : CTyped (church enabled) (liftCtx e68) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b354b97afb3f3d6ffe8) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e152fe0a2dfd7c6b505e) := (e392 enabled)

theorem left_2 : CTyped (church enabled) (liftCtx e292) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_23a053da08baeb355cfa) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_535c1fa4cbed718fb795) := (e432 enabled)

theorem context_2 : CCtxFormed (church enabled) (liftCtx e292) := (e436 enabled)

theorem right_2 : CTyped (church enabled) (liftCtx e292) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_41ed62600d0ff298be98) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_535c1fa4cbed718fb795) := (e408 enabled)

theorem left_3 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2213c4e84bb59d18b927) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b6394a8cb40ae44d5ed5) := (e493 enabled)

theorem context_3 : CCtxFormed (church enabled) (liftCtx e438) := (e506 enabled)

theorem right_3 : CTyped (church enabled) (liftCtx e438) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_75386fddd4eb13447bb7) (liftTm Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b6394a8cb40ae44d5ed5) := (e528 enabled)

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.Programs.Annotated.Evidence
