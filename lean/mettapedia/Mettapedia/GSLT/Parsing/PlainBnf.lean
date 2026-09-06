import Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
import Mettapedia.GSLT.Parsing.CanonicalSourceHornElaboration
import Mettapedia.GSLT.Parsing.HornCertificateGSLT
import Mettapedia.GSLT.Parsing.CanonicalSourceOperationalGSLT
import Mettapedia.GSLT.Parsing.HornEquationInstantiation
import Mettapedia.GSLT.Parsing.PlainBnfSourceTextAppend
import Mettapedia.GSLT.Parsing.PlainBnfStructuredDenotation
import Mettapedia.GSLT.Parsing.PlainBnfSemanticAdmission
import Mettapedia.GSLT.Parsing.PlainBnfGraphSemantics
import Mettapedia.GSLT.Parsing.PlainBnfDenotationCompilation
import Mettapedia.GSLT.Parsing.PlainBnfStructuredValueCodec
import Mettapedia.GSLT.Parsing.PlainBnfDenotationValueCodec

/-!
# Plain-BNF semantic and compilation boundary

This umbrella collects the typed structured grammar, its total denotation to a
syntax `LanguageDef` and parser profile, the ParserPack semantic compilation,
and the exact physical CeTTa value codecs.  Operational correspondence for the
authored GSLT programs and native parser implementations remains a separate
layer.
-/
