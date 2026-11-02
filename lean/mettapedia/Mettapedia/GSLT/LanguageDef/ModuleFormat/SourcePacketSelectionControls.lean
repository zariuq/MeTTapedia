import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketSelection
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketCoverageControls

/-! Declared policy controls separate grammar acceptance from retained
selection, including suffix lookahead and composition of policy modules. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketSelection.Controls

open Mettapedia.GSLT.Parsing ClassAwarePackedForest ClassAwareParserPackCertificate
open SourceSyntax SourceSyntaxIO ScalarSyntaxCore

def token : Family := ⟨⟨"Name", 0, 1⟩, .structural 0, []⟩

theorem continuation_refused : allows [.maximalToken "Name" [98] []] [97,98] token = false := by decide_cbv
theorem delimiter_allowed : allows [.maximalToken "Name" [98] []] [97,40] token = true := by decide_cbv
theorem opener_refused : allows [.maximalToken "Name" [] ["/*"]] [97,47,42] token = false := by decide_cbv
theorem reserved_word_refused : allows [.rejectWords "Name" ["a"]] [97] token = false := by decide_cbv
theorem other_sort_unchanged : allows [.rejectWords "Other" ["a"]] [97] token = true := by decide_cbv

def admitted := SourcePacketCoverage.Controls.admitted

def firstCertificate : Certificate := .structural 0 0 1 (.terminal (.char 120) 0 1 (.nil 1))

theorem first_proposed :
    SourcePacketCertificate.propose? admitted.parser.plan [120] "Term" (SourceSyntaxIO.Controls.packet "First") =
      some firstCertificate := by decide_cbv

theorem selected_packet_positive :
    (SourcePacketSelection.read? (description SourceSyntaxIO.Controls.spec) admitted.parser admitted.shape
      [.rejectWords "Term" ["y"]] [120] "Term" (SourceSyntaxIO.Controls.packet "First")).isSome = true := by
  rw [read?_isSome]
  rw [first_proposed]
  change ((readCertificate? _ _ _ _ _ _ _ firstCertificate).isSome &&
    selected (allows [.rejectWords "Term" ["y"]] [120]) "Term" firstCertificate) = true
  rw [show selected (allows [.rejectWords "Term" ["y"]] [120]) "Term" firstCertificate = true by decide_cbv]
  simp only [Bool.and_true]
  rw [readCertificate?_isSome_iff]
  refine ⟨.node "First" 0 1 [], ⟨.structural 0 (by decide_cbv)
    (by simp only [List.get_eq_getElem]; decide_cbv)
    (by simp only [List.get_eq_getElem]; decide_cbv)
    ?_⟩⟩
  rw [show (admitted.parser.plan.structural.get ⟨0, by decide_cbv⟩).items = [.terminal (.char 120)] by
    simp only [List.get_eq_getElem]; decide_cbv]
  exact .terminal (.char rfl) .nil

theorem grammatical_but_unselected_refused :
    (SourcePacketSelection.read? (description SourceSyntaxIO.Controls.spec) admitted.parser admitted.shape
      [.rejectWords "Term" ["x"]] [120] "Term" (SourceSyntaxIO.Controls.packet "First")).isSome = false := by
  rw [read?_isSome]
  rw [first_proposed]
  change ((readCertificate? _ _ _ _ _ _ _ firstCertificate).isSome &&
    selected (allows [.rejectWords "Term" ["x"]] [120]) "Term" firstCertificate) = false
  rw [show selected (allows [.rejectWords "Term" ["x"]] [120]) "Term" firstCertificate = false by decide_cbv]
  exact Bool.and_false _

theorem combined_policy (input : List Nat) (sort : String) (certificate : Certificate) :
    selected (allows [.rejectWords "Name" ["if"], .maximalToken "Name" [97,98] []] input) sort certificate =
      (selected (allows [.rejectWords "Name" ["if"]] input) sort certificate &&
       selected (allows [.maximalToken "Name" [97,98] []] input) sort certificate) :=
  selected_append [.rejectWords "Name" ["if"]] [.maximalToken "Name" [97,98] []] input sort certificate

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketSelection.Controls
