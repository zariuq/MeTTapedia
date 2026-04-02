import Mettapedia.OSLF.MeTTaIL.Export
import Algorithms.GF.Generated.PaperAmbiguitySig
import Mettapedia.Languages.GF.GFRealSyntaxBridge
import Mettapedia.Languages.Metamath.LanguageDefDSL
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefDSL

open Mettapedia.OSLF.MeTTaIL

namespace Mettapedia.Tools.WriteLanguageFixtures

private def fixtureBase :=
  "/home/zar/claude/hyperon/mettail-rust/macros/tests/fixtures/lean_export"

private def gfPaperSyntaxLang :=
  Mettapedia.Languages.GF.GFCoreOSLFBridge.gfSyntaxLanguageDef
    Algorithms.GF.Generated.PaperAmbiguitySig.sig

#eval do
  IO.FS.createDirAll fixtureBase
  let metamathPath := s!"{fixtureBase}/metamath_core.language"
  let rhocalcPath := s!"{fixtureBase}/rhocalc_core.language"
  let gfPaperPath := s!"{fixtureBase}/gf_paper_ambiguity.language"
  IO.FS.writeFile metamathPath
    (Export.renderLanguage
      Mettapedia.Languages.Metamath.LanguageDefDSL.metamathCore ++ "\n")
  IO.FS.writeFile rhocalcPath
    (Export.renderLanguage
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefDSL.rhoCalcProcessCore ++ "\n")
  IO.FS.writeFile gfPaperPath
    (Export.renderLanguage gfPaperSyntaxLang ++ "\n")
  IO.println s!"Wrote fixtures:\n  {metamathPath}\n  {rhocalcPath}\n  {gfPaperPath}"

end Mettapedia.Tools.WriteLanguageFixtures
