import Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses
import Mettapedia.Languages.GF.PaperAmbiguityPGFBridge
import Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation

namespace Mettapedia.Languages.GF.PaperAmbiguitySemanticBridge

open Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses
open Mettapedia.Languages.GF.PaperAmbiguityPGFBridge
open Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation
open Mettapedia.Languages.GF.WorldModelSemantics

theorem english_telescope_recovered_contextual :
    englishTelescopeRecovered = [telescopeVPAttachmentTree, telescopeNPAttachmentTree] := by
  simpa [telescopeVPAttachmentTree, telescopeNPAttachmentTree] using english_telescope_recovered

theorem english_anna_recovered_contextual :
    englishAnnaRecovered = [annaVPAttachmentTree, annaNPAttachmentTree] := by
  simpa [annaVPAttachmentTree, annaNPAttachmentTree] using english_anna_recovered

theorem czech_telescope_recovered_contextual :
    czechTelescopeRecovered = [telescopeVPAttachmentTree, telescopeNPAttachmentTree] := by
  simpa [telescopeVPAttachmentTree, telescopeNPAttachmentTree] using czech_telescope_recovered

theorem czech_anna_recovered_contextual :
    czechAnnaRecovered = [annaVPAttachmentTree, annaNPAttachmentTree] := by
  simpa [annaVPAttachmentTree, annaNPAttachmentTree] using czech_anna_recovered

theorem english_telescope_instrument_scene_values :
    @gfEvidenceDenote TelescopeState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeTelescopeState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelTelescopeStateGFPattern
      telescopeInstrumentScene englishTelescopeAbstractNode2 = ev 1 2 ∧
    @gfEvidenceDenote TelescopeState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeTelescopeState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelTelescopeStateGFPattern
      telescopeInstrumentScene englishTelescopeAbstractNode1 = ev 3 0 := by
  simpa [telescopeNPAttachmentTree, telescopeVPAttachmentTree] using telescope_instrument_scene_values

theorem english_telescope_modifier_scene_values :
    @gfEvidenceDenote TelescopeState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeTelescopeState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelTelescopeStateGFPattern
      telescopeModifierScene englishTelescopeAbstractNode2 = ev 3 0 ∧
    @gfEvidenceDenote TelescopeState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeTelescopeState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelTelescopeStateGFPattern
      telescopeModifierScene englishTelescopeAbstractNode1 = ev 1 2 := by
  simpa [telescopeNPAttachmentTree, telescopeVPAttachmentTree] using telescope_modifier_scene_values

theorem english_anna_baby_in_crib_scene_values :
    @gfEvidenceDenote AnnaState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeAnnaState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelAnnaStateGFPattern
      annaBabyInCribScene englishAnnaAbstractNode2 = ev 3 0 ∧
    @gfEvidenceDenote AnnaState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeAnnaState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelAnnaStateGFPattern
      annaBabyInCribScene englishAnnaAbstractNode1 = ev 1 2 := by
  simpa [annaNPAttachmentTree, annaVPAttachmentTree] using anna_baby_in_crib_scene_values

theorem english_anna_dressing_in_crib_scene_values :
    @gfEvidenceDenote AnnaState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeAnnaState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelAnnaStateGFPattern
      annaDressingInCribScene englishAnnaAbstractNode2 = ev 1 2 ∧
    @gfEvidenceDenote AnnaState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeAnnaState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelAnnaStateGFPattern
      annaDressingInCribScene englishAnnaAbstractNode1 = ev 3 0 := by
  simpa [annaNPAttachmentTree, annaVPAttachmentTree] using anna_dressing_in_crib_scene_values

theorem czech_telescope_instrument_scene_values :
    @gfEvidenceDenote TelescopeState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeTelescopeState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelTelescopeStateGFPattern
      telescopeInstrumentScene czechTelescopeAbstractNode2 = ev 1 2 ∧
    @gfEvidenceDenote TelescopeState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeTelescopeState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelTelescopeStateGFPattern
      telescopeInstrumentScene czechTelescopeAbstractNode1 = ev 3 0 := by
  simpa [englishTelescopeAbstractNode1, englishTelescopeAbstractNode2,
    czechTelescopeAbstractNode1, czechTelescopeAbstractNode2] using english_telescope_instrument_scene_values

theorem czech_telescope_modifier_scene_values :
    @gfEvidenceDenote TelescopeState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeTelescopeState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelTelescopeStateGFPattern
      telescopeModifierScene czechTelescopeAbstractNode2 = ev 3 0 ∧
    @gfEvidenceDenote TelescopeState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeTelescopeState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelTelescopeStateGFPattern
      telescopeModifierScene czechTelescopeAbstractNode1 = ev 1 2 := by
  simpa [englishTelescopeAbstractNode1, englishTelescopeAbstractNode2,
    czechTelescopeAbstractNode1, czechTelescopeAbstractNode2] using english_telescope_modifier_scene_values

theorem czech_anna_baby_in_crib_scene_values :
    @gfEvidenceDenote AnnaState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeAnnaState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelAnnaStateGFPattern
      annaBabyInCribScene czechAnnaAbstractNode2 = ev 3 0 ∧
    @gfEvidenceDenote AnnaState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeAnnaState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelAnnaStateGFPattern
      annaBabyInCribScene czechAnnaAbstractNode1 = ev 1 2 := by
  simpa [englishAnnaAbstractNode1, englishAnnaAbstractNode2,
    czechAnnaAbstractNode1, czechAnnaAbstractNode2] using english_anna_baby_in_crib_scene_values

theorem czech_anna_dressing_in_crib_scene_values :
    @gfEvidenceDenote AnnaState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeAnnaState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelAnnaStateGFPattern
      annaDressingInCribScene czechAnnaAbstractNode2 = ev 1 2 ∧
    @gfEvidenceDenote AnnaState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeAnnaState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelAnnaStateGFPattern
      annaDressingInCribScene czechAnnaAbstractNode1 = ev 3 0 := by
  simpa [englishAnnaAbstractNode1, englishAnnaAbstractNode2,
    czechAnnaAbstractNode1, czechAnnaAbstractNode2] using english_anna_dressing_in_crib_scene_values

theorem czech_telescope_scene_rankings_reverse :
    @gfEvidenceDenote TelescopeState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeTelescopeState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelTelescopeStateGFPattern
      telescopeInstrumentScene czechTelescopeAbstractNode2 =
        @gfEvidenceDenote TelescopeState
          Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeTelescopeState
          Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelTelescopeStateGFPattern
          telescopeModifierScene czechTelescopeAbstractNode1 ∧
    @gfEvidenceDenote TelescopeState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeTelescopeState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelTelescopeStateGFPattern
      telescopeInstrumentScene czechTelescopeAbstractNode1 =
        @gfEvidenceDenote TelescopeState
          Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeTelescopeState
          Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelTelescopeStateGFPattern
          telescopeModifierScene czechTelescopeAbstractNode2 := by
  constructor
  · exact (czech_telescope_instrument_scene_values.1).trans
      (czech_telescope_modifier_scene_values.2).symm
  · exact (czech_telescope_instrument_scene_values.2).trans
      (czech_telescope_modifier_scene_values.1).symm

theorem czech_anna_scene_rankings_reverse :
    @gfEvidenceDenote AnnaState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeAnnaState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelAnnaStateGFPattern
      annaBabyInCribScene czechAnnaAbstractNode2 =
        @gfEvidenceDenote AnnaState
          Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeAnnaState
          Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelAnnaStateGFPattern
          annaDressingInCribScene czechAnnaAbstractNode1 ∧
    @gfEvidenceDenote AnnaState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeAnnaState
      Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelAnnaStateGFPattern
      annaBabyInCribScene czechAnnaAbstractNode1 =
        @gfEvidenceDenote AnnaState
          Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instEvidenceTypeAnnaState
          Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation.instWorldModelAnnaStateGFPattern
          annaDressingInCribScene czechAnnaAbstractNode2 := by
  constructor
  · exact (czech_anna_baby_in_crib_scene_values.1).trans
      (czech_anna_dressing_in_crib_scene_values.2).symm
  · exact (czech_anna_baby_in_crib_scene_values.2).trans
      (czech_anna_dressing_in_crib_scene_values.1).symm

end Mettapedia.Languages.GF.PaperAmbiguitySemanticBridge
