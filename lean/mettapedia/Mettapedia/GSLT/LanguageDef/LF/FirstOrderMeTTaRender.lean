import Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
import Mettapedia.GSLT.LanguageDef.LF.FirstOrderOperationalCorrespondence

/-!
# Shared MeTTa rendering for first-order LF certificates

These renderers serialize LF runtime data only.  They do not validate terms,
proofs, or sources; generated artifacts remain subject to the live source and
kernel checks.
-/

namespace Mettapedia.GSLT.LanguageDef.LFFirstOrderMeTTaRender

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFFirstOrderOperationalCorrespondence
open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

def renderSort : Srt → String
  | .type => "type"
  | .kind => "kind"

def renderTerm : Term → String
  | .srt sort => s!"(Srt {renderSort sort})"
  | .con name => s!"(Con {quote name})"
  | .var index => s!"(Var {index})"
  | .pi domain body => s!"(Pi {renderTerm domain} {renderTerm body})"
  | .lam domain body => s!"(Lam {renderTerm domain} {renderTerm body})"
  | .app function argument =>
      s!"(App {renderTerm function} {renderTerm argument})"

def renderConvertedWitness
    (signature : String)
    (termCertificate typeCertificate : ConversionCertificate) : String :=
  "  (KWCheckConverted\n" ++
    s!"    {signature}\n" ++
    s!"    {renderTerm termCertificate.source}\n" ++
    s!"    {renderTerm termCertificate.target}\n" ++
    s!"    {renderRawProof termCertificate.proof}\n" ++
    s!"    {renderTerm typeCertificate.source}\n" ++
    s!"    {renderTerm typeCertificate.target}\n" ++
    s!"    {renderRawProof typeCertificate.proof})"

end Mettapedia.GSLT.LanguageDef.LFFirstOrderMeTTaRender
