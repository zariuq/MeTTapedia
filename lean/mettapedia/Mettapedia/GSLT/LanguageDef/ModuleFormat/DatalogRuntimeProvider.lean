import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogRuntimeCompiler

/-! The D0 provider's initialization hook for a shared in-process Lean
runtime: lazily created closed constants are forced while every provider's
modules are initialized, before request allocations begin. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogRuntimeCompiler

@[export cetta_datalog_force_constants_v1]
def forceConstants (word : UInt64) : String :=
  toString (forceIntegerBounds word) ++ forceDecimalCodec word

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogRuntimeCompiler
