import Mettapedia.Languages.GF.GFCoreNTTDiagnostics
import Mettapedia.Languages.GF.PaperAmbiguityPGFBridge

/-!
# Grounded GF Witness Demo

This file is the grounded replacement for the old scope/modal demo. It stays
strictly on the real `GFCore.check` / PGF-witness lane:

- generated English and Czech `PaperAmbiguity` witnesses recover the same
  abstract trees;
- those witnesses check to the same Lean patterns;
- the syntax-only OSLF lane distinguishes the real VP/NP attachment readings
  at the native-type level;
- the syntax-only modal boundary is honest: `□` is vacuous and there is no
  positive `◇` witness because there are no rewrites.

This means the current grounded coverage boundary is exactly the actual
generated English/Czech `PaperAmbiguity` slice. If we want more GF here, the
right next move is more generated Czech/GF material, not more authored
semantics.
-/

namespace Mettapedia.Languages.GF.Examples.EmbeddedScopeDemo

open Mettapedia.Languages.GF.GFCoreNTTDiagnostics
open Mettapedia.Languages.GF.PaperAmbiguityPGFBridge
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- Grounded cross-language recovery: the generated English and Czech telescope
    witness sets recover the same abstract trees. -/
theorem telescope_recovery_aligns_across_english_czech :
    Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses.englishTelescopeRecovered =
      Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses.czechTelescopeRecovered :=
  english_czech_telescope_recovered_equal

/-- Grounded cross-language recovery: the generated English and Czech Anna
    witness sets recover the same abstract trees. -/
theorem anna_recovery_aligns_across_english_czech :
    Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses.englishAnnaRecovered =
      Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses.czechAnnaRecovered :=
  english_czech_anna_recovered_equal

/-- The real telescope readings remain structurally distinct after the
    witness/check bridge. The VP-attached reading satisfies the VP native type
    and fails the NP one; the NP-attached reading does the converse. -/
theorem telescope_attachment_distinction :
    (langOSLF paperLangKR "S").satisfies telescopeVPPattern vpAttachmentType.pred ∧
    ¬ (langOSLF paperLangKR "S").satisfies telescopeVPPattern npAttachmentType.pred ∧
    (langOSLF paperLangKR "S").satisfies telescopeNPPattern npAttachmentType.pred ∧
    ¬ (langOSLF paperLangKR "S").satisfies telescopeNPPattern vpAttachmentType.pred := by
  exact ⟨ telescopeVP_satisfies_vpAttachmentType
        , telescopeVP_not_npAttachmentType
        , telescopeNP_satisfies_npAttachmentType
        , telescopeNP_not_vpAttachmentType
        ⟩

/-- The grounded modal boundary for the syntax-only lane:
    `□` is available on the checked present sentence, while a positive `◇`
    witness toward the temporal target is absent because the real syntax lane
    has no rewrites. -/
theorem present_sentence_modal_boundary :
    langBox paperLangKR (fun q => q = presentSentencePattern) presentSentencePattern ∧
    ¬ langDiamond paperLangKR (fun q => q = temporalPresentPattern) presentSentencePattern := by
  exact ⟨presentSentence_box_self, presentSentence_not_diamond_temporal⟩

/-- Summary theorem for the grounded English/Czech boundary currently present
    in-tree. -/
theorem grounded_paper_ambiguity_summary :
    Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses.englishTelescopeRecovered =
      Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses.czechTelescopeRecovered ∧
    Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses.englishAnnaRecovered =
      Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses.czechAnnaRecovered ∧
    ((langOSLF paperLangKR "S").satisfies telescopeVPPattern vpAttachmentType.pred) ∧
    ((langOSLF paperLangKR "S").satisfies telescopeNPPattern npAttachmentType.pred) ∧
    langBox paperLangKR (fun q => q = presentSentencePattern) presentSentencePattern := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact telescope_recovery_aligns_across_english_czech
  · exact anna_recovery_aligns_across_english_czech
  · exact telescopeVP_satisfies_vpAttachmentType
  · exact telescopeNP_satisfies_npAttachmentType
  · exact presentSentence_box_self

end Mettapedia.Languages.GF.Examples.EmbeddedScopeDemo
