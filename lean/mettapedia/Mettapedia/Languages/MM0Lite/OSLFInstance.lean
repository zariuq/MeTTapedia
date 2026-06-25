import Mettapedia.Languages.MM0Lite.LanguageDef
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# MM0-Lite OSLF/GSLT Instance

This connects MM0-Lite to the generic OSLF synthesis pipeline:
`LanguageDef -> langOSLF -> modal/Galois structure`.
-/

namespace Mettapedia.Languages.MM0Lite.OSLFInstance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Languages.MM0Lite.LanguageDef

def mm0LiteOSLF : OSLFTypeSystem (langRewriteSystem mm0Lite "ProofState") :=
  langOSLF mm0Lite "ProofState"

theorem mm0Lite_galois :
    GaloisConnection (langDiamond mm0Lite) (langBox mm0Lite) :=
  langGalois mm0Lite

end Mettapedia.Languages.MM0Lite.OSLFInstance
