import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSelectedMeaning
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketSelectionControls

/-! Selected-source transport retains successful derivations and refuses
grammatical packets excluded by the declared policy. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketSelection.Controls

open Mettapedia.GSLT.Parsing
open SourceSyntaxIO ScalarSyntaxCore

theorem selected_meaning_exists :
    ∃ core, Source (description SourceSyntaxIO.Controls.spec) admitted.parser
      [.rejectWords "Term" ["y"]] [120] "Term" core := by
  obtain ⟨reading, read⟩ := Option.isSome_iff_exists.mp selected_packet_positive
  exact ⟨reading.core, core?_sound (shape := admitted.shape)
    (packet := SourceSyntaxIO.Controls.packet "First") (by simp only [core?, read, Option.map_some])⟩

theorem grammatical_packet_has_no_selected_core :
    SourcePacketSelection.core? (description SourceSyntaxIO.Controls.spec) admitted.parser admitted.shape
      [.rejectWords "Term" ["x"]] [120] "Term" (SourceSyntaxIO.Controls.packet "First") = none := by
  have missing := grammatical_but_unselected_refused
  cases read : SourcePacketSelection.read? (description SourceSyntaxIO.Controls.spec) admitted.parser admitted.shape
      [.rejectWords "Term" ["x"]] [120] "Term" (SourceSyntaxIO.Controls.packet "First") with
  | none => simp only [core?, read, Option.map_none]
  | some reading => simp only [read, Option.isSome_some, Bool.true_eq_false] at missing

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketSelection.Controls
