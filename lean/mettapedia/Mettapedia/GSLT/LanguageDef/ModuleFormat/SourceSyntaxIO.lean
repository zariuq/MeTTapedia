import Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketCertificate
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxNativePlan
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxTextInverse

/-! Shared source I/O over a grammar/profile description. Native packets
propose syntax data; independent replay checks input, declarations and spans.
Binding and runtime elaboration compose after this retained source boundary. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxIO

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter (stringScalars)
open ScalarSyntaxCore

def description (spec : Portable.SyntaxDescription) : Description :=
  ⟨spec.grammar,spec.profile,"source-scalar:"⟩

def read? (spec : Portable.SyntaxDescription) (input : String) (packet : SourcePacket.Packet) : Option Pattern := do
  let admitted ← admit? (description spec)
  SourcePacketCertificate.core? (description spec) admitted.parser admitted.shape
    (stringScalars input) spec.profile.startSort packet

def print? (spec : Portable.SyntaxDescription) (core : Pattern) : Option String :=
  printText? (description spec) spec.profile.startSort core

theorem read_print (spec : Portable.SyntaxDescription) (input : String)
    (packet : SourcePacket.Packet) (core : Pattern) (read : read? spec input packet = some core) :
    print? spec core = some input := by
  obtain ⟨admitted,_,accepted⟩ := Option.bind_eq_some_iff.mp read
  have printed := SourcePacketCertificate.core?_prints accepted
  unfold print? printText?
  rw [printed]
  simp [stringScalars,List.map_map,Function.comp_def]

theorem read_has_source (spec : Portable.SyntaxDescription) (input : String)
    (packet : SourcePacket.Packet) (core : Pattern) (read : read? spec input packet = some core) :
    ∃ tree, Nonempty (Mettapedia.GSLT.Parsing.LanguageDefScalarSyntax.DerivesAt SourceSyntaxExport.literalScalars?
      spec.profile spec.grammar (stringScalars input) spec.profile.startSort 0 (stringScalars input).length tree) ∧
      lowerCST? (description spec) spec.profile.startSort tree = some core := by
  obtain ⟨admitted,_,accepted⟩ := Option.bind_eq_some_iff.mp read
  exact SourcePacketCertificate.core?_source accepted

theorem print_has_source (spec : Portable.SyntaxDescription) (shape : Shape (description spec))
    (core : Pattern) (text : String) (printed : print? spec core = some text) :
    ∃ tree, Nonempty (Mettapedia.GSLT.Parsing.LanguageDefScalarSyntax.DerivesAt SourceSyntaxExport.literalScalars?
      spec.profile spec.grammar (stringScalars text) spec.profile.startSort 0 (stringScalars text).length tree) ∧
      lowerCST? (description spec) spec.profile.startSort tree = some core :=
  printed_text_readback (description spec) shape spec.profile.startSort core text printed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxIO
