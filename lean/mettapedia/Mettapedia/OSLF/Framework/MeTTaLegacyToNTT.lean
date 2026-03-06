import Mettapedia.OSLF.Framework.MeTTaToNTT

/-!
# MeTTa Full Legacy OSLF -> NTT Bridge Module

Legacy-named module wrapper for the historical full-state MeTTa OSLF->NTT
bridge. This preserves the existing implementation while stabilizing naming
for migration to HE/PeTTa-aligned concrete instances.
-/

namespace Mettapedia.OSLF.Framework.MeTTaLegacyToNTT

open Mettapedia.OSLF.Framework.MeTTaToNTT

noncomputable section

abbrev mettaFullLegacy := Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFullLegacy
abbrev mettaEvidenceToNT := Mettapedia.OSLF.Framework.MeTTaToNTT.mettaEvidenceToNT
abbrev mettaEvidenceToNT_hom := @Mettapedia.OSLF.Framework.MeTTaToNTT.mettaEvidenceToNT_hom
abbrev mettaSemE := @Mettapedia.OSLF.Framework.MeTTaToNTT.mettaSemE
abbrev mettaSemE_atom := @Mettapedia.OSLF.Framework.MeTTaToNTT.mettaSemE_atom
abbrev mettaSemE_atom_revision := @Mettapedia.OSLF.Framework.MeTTaToNTT.mettaSemE_atom_revision
abbrev mettaFormulaToNT := @Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFormulaToNT
abbrev mettaFormulaToNT_snd := @Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFormulaToNT_snd
abbrev mettaFormulaToNT_atom := @Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFormulaToNT_atom
abbrev mettaFormulaToNT_hom := @Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFormulaToNT_hom

end

end Mettapedia.OSLF.Framework.MeTTaLegacyToNTT
