import Mettapedia.OSLF.Framework.MeTTaFullInstance

/-!
# MeTTa Full Legacy Instance Module

Legacy-named module wrapper for the historical full-state MeTTa OSLF instance.
This module intentionally re-exports the existing implementation surface via
aliases, while preserving backward compatibility with `MeTTaFullInstance`.
-/

namespace Mettapedia.OSLF.Framework.MeTTaFullLegacyInstance

abbrev mettaFullLegacy : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef :=
  Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFullLegacy
abbrev mettaFullLegacyOSLF :=
  Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFullLegacyOSLF
abbrev mettaLegacyState :=
  Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaLegacyState
abbrev mettaFullLegacy_pathOrder :=
  @Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFullLegacy_pathOrder
abbrev mettaFullLegacy_checker_sat_to_pathSemClosed_commDi_bc_graph :=
  @Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFullLegacy_checker_sat_to_pathSemClosed_commDi_bc_graph
abbrev mettaFullLegacy_checker_sat_to_pathSemClosed_commDi_bc_graph_auto :=
  @Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFullLegacy_checker_sat_to_pathSemClosed_commDi_bc_graph_auto
abbrev mettaFullLegacySpecAtomCheck :=
  Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFullLegacySpecAtomCheck
abbrev mettaFullLegacySpecAtomSem :=
  Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFullLegacySpecAtomSem
abbrev mettaFullLegacy_checkLangUsing_sat_sound_specAtoms :=
  @Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFullLegacy_checkLangUsing_sat_sound_specAtoms
abbrev mettaFullLegacy_checkLang_sat_sound_specAtoms :=
  @Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFullLegacy_checkLang_sat_sound_specAtoms

end Mettapedia.OSLF.Framework.MeTTaFullLegacyInstance
