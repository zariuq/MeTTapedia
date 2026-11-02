import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogReferenceReader

/-! Executable reference controls distinguish valid empty input and a real
fact from malformed source. General soundness and completeness are proved
in ReferenceReader; these guards exercise its compiled evaluator. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ReferenceReader

#guard programs [] == [⟨[]⟩]
#guard programs [63] == []
#guard programs ("a().".toList.map Char.toNat) ==
  [⟨[Mettapedia.Languages.Datalog.Statement.fact ⟨["a"],[]⟩]⟩]

theorem terminal_is_not_a_program : program? (.terminal [] 0 0) = none := by
  simp [program?, CSTToCore.lower?, Mettapedia.GSLT.Parsing.DeclaredConstructorReifier.lower?]

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ReferenceReader
