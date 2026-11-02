import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxIO
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketCoverage

/-! Source syntax, retained cores and selected packets compose in both
directions. Ambiguity is preserved: the inverse constructs a packet for a
specified source tree, not a claim that the text has a unique parse. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxIO

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing LanguageDefScalarPrinter PresentationExprSemantics
open ScalarSyntaxCore

theorem source_read (spec : Portable.SyntaxDescription) (admitted : Admitted (description spec))
    (accepted : admit? (description spec) = some admitted)
    (profile : SourcePacketEncoding.Profile admitted.parser.plan) (text : String) {tree : CST}
    (source : LanguageDefScalarSyntax.DerivesAt SourceSyntaxExport.literalScalars?
      spec.profile spec.grammar (stringScalars text) spec.profile.startSort 0 (stringScalars text).length tree) :
    read? spec text (SourcePacketEncoding.encode tree) = some (reify (description spec) source) := by
  unfold read?
  rw [accepted]
  exact SourcePacketCoverage.core_complete admitted.parser admitted.shape profile source

theorem printed_has_packet (spec : Portable.SyntaxDescription) (admitted : Admitted (description spec))
    (accepted : admit? (description spec) = some admitted)
    (profile : SourcePacketEncoding.Profile admitted.parser.plan) (core : Pattern) (text : String)
    (printed : print? spec core = some text) :
    ∃ packet, read? spec text packet = some core := by
  obtain ⟨tree, ⟨source⟩, lowered⟩ := print_has_source spec admitted.shape core text printed
  have same : reify (description spec) source = core :=
    Option.some.inj ((lowerCST_source (description spec) admitted.shape source).symm.trans lowered)
  exact ⟨SourcePacketEncoding.encode tree, (source_read spec admitted accepted profile text source).trans
    (congrArg some same)⟩

theorem print_iff_packet (spec : Portable.SyntaxDescription) (admitted : Admitted (description spec))
    (accepted : admit? (description spec) = some admitted)
    (profile : SourcePacketEncoding.Profile admitted.parser.plan) (core : Pattern) (text : String) :
    print? spec core = some text ↔ ∃ packet, read? spec text packet = some core :=
  ⟨printed_has_packet spec admitted accepted profile core text,
    fun ⟨packet, read⟩ => read_print spec text packet core read⟩

#print axioms source_read
#print axioms printed_has_packet
#print axioms print_iff_packet

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxIO
