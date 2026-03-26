import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

/-!
# `LanguageDefMacro` Compatibility Alias

`LanguageDefDSL` is the canonical shared authoring layer because it includes both
syntax macros and small language/rule builders. This module exists so callers
that prefer "Macro" naming can import an equivalent surface.
-/

namespace Mettapedia.OSLF.MeTTaIL.LanguageDefMacro

open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

end Mettapedia.OSLF.MeTTaIL.LanguageDefMacro
